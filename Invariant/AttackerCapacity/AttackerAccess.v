Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineView.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.
Require Import Technique.TechniqueOneStep.

Require Import Machine.MachineAuxFunctions.

Require Import Invariant.AuxLemmas.AuxLemmasMachineUser.
Require Import Invariant.AuxLemmas.AuxLemmasEnviroment.
Require Import Invariant.AuxLemmas.AuxLemmasFile.
Require Import Invariant.AuxLemmas.AuxLemmasSecret.
Require Import Invariant.AttackerCapacity.AttackerReach.
Require Import Invariant.ValidAttacker.ValidAttacker.

Section AttackerAccess.

  (* ===== Predicados de obtenibilidad ===== *)

  (* Una maquina tiene un exploit que el atacante puede usar:
     el exploit esta en la lista de exploits de la maquina
     y tambien en la lista de exploits dominados por el atacante.
     Ambas listas son estaticas durante la campaña de ataque. *)
  Definition has_usable_exploit (mac: Machine) (a: Attacker) : Prop :=
    exists (e: idExploit) (s: idService),
      In (s, e) (machine_exploits mac)
      /\ In (s, e) (mastered_exploits a).

  (* Usuario obtenible via Remote_Services en la red concreta:
     existe en la maquina mid una cuenta para u en algun servicio s con clave
     definida (account_key <> None). Cubre tanto el caso de clave concreta
     `Some (Some k)` como el caso `Some None` (servicio passwordless),
     ambos validos para que la Pre de Remote_Services se satisfaga con un
     k' apropiado. *)
  Definition obtainable_via_remote_services (n: network_map) (mid: idMachine) (u: idUser) : Prop :=
    exists (mac: Machine) (acc: Account) (s: idService),
      n mid = Some mac
      /\ In acc (machine_accounts mac)
      /\ account_user acc = u
      /\ account_service acc = Some s
      /\ account_key acc <> None.

  (* Usuario obtenible via Exploitation_Remote_Services en la red concreta:
     la maquina tiene un exploit aprovechable por el atacante,
     existe un servicio s en la maquina, y u tiene una cuenta
     asociada a ese servicio. No se necesita clave porque la explotacion
     la omite. *)
  Definition obtainable_via_exploitation (n: network_map) (a: Attacker) (mid: idMachine) (u: idUser) : Prop :=
    exists (mac: Machine) (s: idService) (acc: Account) (serv: Service),
      n mid = Some mac
      /\ In serv (machine_services mac)
      /\ service_value serv = s
      /\ has_usable_exploit mac a
      /\ In acc (machine_accounts mac)
      /\ account_user acc = u
      /\ account_service acc = Some s.

  (* Usuario obtenible via Abuse_Elevation_Control_Mechanism (escalada local):
     vulnerabilidad estructural de la maquina, en el sentido de que existe en
     mid una cuenta de alto privilegio para u' (servicio OS, privilegio high)
     y ALGUNA cuenta low_star de OS con clave definida que AECM podria usar
     como pivote. No exige que el atacante ya conozca al usuario low_star: es
     una propiedad estatica de la red concreta. La razon es que si el atacante
     llega a obtener cualquier usuario low_star del par OS por movimiento
     lateral, AECM se vuelve aplicable; entonces u' debe contar como
     potencialmente obtenible desde el inicio. *)
  Definition obtainable_via_local_escalation (n: network_map) (mid: idMachine) (u': idUser) : Prop :=
    exists (mac: Machine) (accHigh: Account),
      n mid = Some mac
      /\ In accHigh (machine_accounts mac)
      /\ account_user accHigh = u'
      /\ account_service accHigh = Some OS
      /\ account_privilege accHigh = Some high
      /\ (exists (u_low: idUser) (accLow: Account),
            In accLow (machine_accounts mac)
            /\ account_user accLow = u_low
            /\ account_service accLow = Some OS
            /\ account_privilege accLow = Some low_star
            /\ account_key accLow <> None).

  (* Un usuario es obtenible en una maquina si:
     - ya esta en known_machines a (caso base),
     - movimiento lateral con credenciales (Remote_Services),
     - explotacion remota de un servicio (Exploitation_Remote_Services), o
     - escalada local de privilegios (Abuse_Elevation_Control_Mechanism).
     Las tres ultimas son propiedades estaticas de la red concreta +
     mastered_exploits a (que es estatico durante la campana); la primera
     es monotona en a. Por tanto el predicado entero es monotono en a:
     si u es obtenible desde a, es obtenible desde todo a' que extienda
     known_machines a. La negacion (~ obtainable_user) es por ende
     anti-monotona y persiste bajo multi_step. *)
  Definition obtainable_user (n: network_map) (a: Attacker) (mid: idMachine) (u: idUser) : Prop :=
    In (mid, u) (known_machines a)
    \/ obtainable_via_remote_services n mid u
    \/ obtainable_via_exploitation n a mid u
    \/ obtainable_via_local_escalation n mid u.

  (* ===== Clasificacion de inaccesibilidad ===== *)

  (* La inaccesibilidad de un secreto puede ser rota:
     existe un objetivo actualmente inaccesible (ningun usuario conocido
     tiene acceso al archivo), pero la maquina es alcanzable y existe
     un usuario con acceso al archivo que es obtenible via movimiento
     lateral. Es un predicado estatico sobre la red concreta:
     si se cumple, existe un multi_step que rompe la inaccesibilidad. *)
  Definition inaccessibility_breakable (a: Attacker) (n: network_map) : Prop :=
    exists (mid: idMachine) (mac: Machine) (f: File),
      n mid = Some mac
      /\ In f (machine_fileSystem mac)
      /\ file_objective f = true
      /\ reachable n a mid
      /\ (forall (u: idUser), In (mid, u) (known_machines a) ->
            ~ In u (file_user_access f))
      /\ (exists (u: idUser),
            In u (file_user_access f)
            /\ obtainable_user n a mid u).

  (* Un secreto es permanentemente inaccesible: la maquina es alcanzable
     pero ningun usuario con acceso al archivo puede ser obtenido
     por ninguna tecnica de movimiento lateral.
     A diferencia de exists_credential_protected_secret (que usa
     has_credentials y es insatisfacible en redes concretas validas),
     este predicado distingue credenciales reales de la ausencia
     de exploits, proporcionando una barrera genuina. *)
  Definition exists_permanently_inaccessible_secret (a: Attacker) (n: network_map) : Prop :=
    exists (mid: idMachine) (mac: Machine) (f: File),
      n mid = Some mac
      /\ In f (machine_fileSystem mac)
      /\ file_objective f = true
      /\ reachable n a mid
      /\ (forall (u: idUser),
            In u (file_user_access f) ->
            ~ obtainable_user n a mid u).

  (* ===== Lema auxiliar clave ===== *)

  (* Cuando one_step agrega un nuevo par (mid, u) a known_machines,
     u debe ser obtainable_user en la red concreta.
     Se prueba por analisis de casos sobre la tecnica t:
     - Remote_Services: Pre da una cuenta para u' en la vista del atacante
       con account_key <> None; via is_networkView se transfiere a la red
       concreta, dando obtainable_via_remote_services.
     - Exploitation_Remote_Services: Post da directamente la cuenta en mac'
       (red concreta) y Pre + is_networkView dan has_usable_exploit, dando
       obtainable_via_exploitation.
     - Abuse_Elevation_Control_Mechanism: Post da accHigh en mac (red concreta)
       con privilegio high; Pre da una cuenta low_star ya conocida que se
       transfiere via is_networkView, dando obtainable_via_local_escalation.
     - Demas tecnicas: Post da known_machines a' = known_machines a,
       contradiciendo la hipotesis de que (mid, u) es nuevo. *)
  Lemma one_step_adds_obtainable_user :
    forall (a a': Attacker) (t: Technique) (n: network_map)
           (mid: idMachine) (u: idUser),
      valid_concrete_network n ->
      valid_attacker a n ->
      one_step a t n a' ->
      In (mid, u) (known_machines a') ->
      ~ In (mid, u) (known_machines a) ->
      obtainable_user n a mid u.
  Proof.
    intros a a' t n mid u _ _ Honestep Hin' Hnotin.
    destruct Honestep.
    destruct t; unfold Pre in H1; unfold Post in H2.
    - (* Remote_Services *)
      destruct H2 as [Hkm _].
      rewrite Hkm in Hin'.
      apply member_add_machine_user in Hin'.
      destruct Hin' as [Heq | Hin].
      + injection Heq as Hmeq Hueq. subst.
        right. left.
        destruct H1 as [_ [_ HaccPre]].
        destruct HaccPre as [acc [mac' [Henv [Hin_acc [Huser [Hservice Hkey]]]]]].
        destruct H0 as [_ [_ [_ Hview]]].
        unfold valid_attacker_iv, is_networkView in Hview.
        destruct (Hview _ _ Henv) as [mac_n [Hn1 Hmv]].
        destruct Hmv as [_ [Hacc_subset _]].
        unfold subset_accounts in Hacc_subset.
        specialize (Hacc_subset acc Hin_acc).
        destruct Hacc_subset as [Hin_n | [acc_n [Hin_n Hview_acc]]].
        * (* acc esta directamente en mac_n *)
          exists mac_n, acc.
          eexists.
          split; [exact Hn1 |].
          split; [exact Hin_n |].
          split; [exact Huser |].
          split; [exact Hservice |].
          rewrite Hkey. discriminate.
        * (* acc tiene una vista acc_n en mac_n *)
          destruct Hview_acc as [Huser_eq [Hsv_disj [Hkey_disj _]]].
          exists mac_n, acc_n.
          eexists.
          split; [exact Hn1 |].
          split; [exact Hin_n |].
          split.
          -- rewrite <- Huser_eq. exact Huser.
          -- split.
             ++ destruct Hsv_disj as [Hsv_none | Hsv_eq].
                ** rewrite Hsv_none in Hservice. discriminate.
                ** rewrite <- Hsv_eq. exact Hservice.
             ++ destruct Hkey_disj as [Hkey_none | Hkey_eq].
                ** rewrite Hkey_none in Hkey. discriminate.
                ** rewrite <- Hkey_eq. rewrite Hkey. discriminate.
      + exfalso. apply Hnotin. exact Hin.

    - (* Exploitation_Remote_Services *)
      destruct H2 as [_ [_ [mac_post [macView_post [_ [acc_post [_ [_ [u_post [Hnet_post [Henv_post [Hin_acc_post [Huser_post [Hservice_post [Hkm _]]]]]]]]]]]]]]].
      rewrite Hkm in Hin'.
      apply member_add_machine_user in Hin'.
      destruct Hin' as [Heq | Hin].
      + injection Heq as Hmeq Hueq.
        rewrite <- Hueq.
        rewrite <- Hmeq.
        right. right. left.
        destruct H1 as [_ [_ HservPre]].
        destruct HservPre as [serv_pre [macView_pre [Henv_pre [Hin_serv_pre [Hsvalue_pre [Hin_exploit_pre Hin_mastered_pre]]]]]].
        assert (Heq_view: macView_pre = macView_post).
        { eapply enviroment_map_image; eassumption. }
        subst macView_pre.
        destruct H0 as [_ [_ [_ Hview]]].
        unfold valid_attacker_iv, is_networkView in Hview.
        destruct (Hview _ _ Henv_post) as [mac_iv [Hn_iv Hmv]].
        assert (Heq_mac: mac_iv = mac_post).
        { eapply enviroment_map_image; eassumption. }
        subst mac_iv.
        destruct Hmv as [Hsvc_sub [_ [_ [_ Hexp_sub]]]].
        unfold subset_services in Hsvc_sub.
        unfold subset_exploits in Hexp_sub.
        exists mac_post.
        eexists.
        exists acc_post, serv_pre.
        split; [exact Hnet_post |].
        split; [apply Hsvc_sub; exact Hin_serv_pre |].
        split; [exact Hsvalue_pre |].
        split.
        * unfold has_usable_exploit.
          eexists. eexists.
          split.
          -- apply Hexp_sub. exact Hin_exploit_pre.
          -- exact Hin_mastered_pre.
        * split; [exact Hin_acc_post |].
          split; [exact Huser_post | exact Hservice_post].
      + exfalso. apply Hnotin. exact Hin.

    - (* Unsecured_Credentials *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'. contradiction.

    - (* Brute_Force *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'. contradiction.

    - (* Abuse_Elevation_Control_Mechanism *)
      destruct H2 as [_ [_ [mac_post [macView_post [_ [u_post [_ [accHigh_post [_ [Hnet_post [Henv_post [Hin_accH [HaccH_user [HaccH_service [HaccH_priv [_ [_ [_ [Hkm _]]]]]]]]]]]]]]]]]]].
      rewrite Hkm in Hin'.
      apply member_add_machine_user in Hin'.
      destruct Hin' as [Heq | Hin].
      + injection Heq as Hmeq Hueq.
        rewrite <- Hueq.
        rewrite <- Hmeq.
        right. right. right.
        destruct H1 as [_ HaccLow_pre].
        destruct HaccLow_pre as [accLow [macView_pre [k_pre [Henv_pre [Hin_accLow [HaccLow_user [HaccLow_service [HaccLow_key HaccLow_priv]]]]]]]].
        assert (Heq_view: macView_pre = macView_post).
        { eapply enviroment_map_image; eassumption. }
        subst macView_pre.
        destruct H0 as [_ [_ [_ Hview]]].
        unfold valid_attacker_iv, is_networkView in Hview.
        destruct (Hview _ _ Henv_post) as [mac_iv [Hn_iv Hmv]].
        assert (Heq_mac: mac_iv = mac_post).
        { eapply enviroment_map_image; eassumption. }
        subst mac_iv.
        destruct Hmv as [_ [Hacc_subset _]].
        unfold subset_accounts in Hacc_subset.
        specialize (Hacc_subset accLow Hin_accLow).
        exists mac_post, accHigh_post.
        split; [exact Hnet_post |].
        split; [exact Hin_accH |].
        split; [exact HaccH_user |].
        split; [exact HaccH_service |].
        split; [exact HaccH_priv |].
        destruct Hacc_subset as [Hin_n | [accLow_n [Hin_n Hview_acc]]].
        * (* accLow esta directamente en mac_post *)
          exists (account_user accLow), accLow.
          split; [exact Hin_n |].
          split; [reflexivity |].
          split; [exact HaccLow_service |].
          split; [exact HaccLow_priv |].
          rewrite HaccLow_key. discriminate.
        * (* accLow tiene una vista accLow_n en mac_post *)
          destruct Hview_acc as [Huser_eq [Hsv_disj [Hkey_disj Hpriv_disj]]].
          exists (account_user accLow), accLow_n.
          split; [exact Hin_n |].
          split; [symmetry; exact Huser_eq |].
          split.
          -- destruct Hsv_disj as [Hsv_none | Hsv_eq].
             ++ rewrite Hsv_none in HaccLow_service. discriminate.
             ++ rewrite <- Hsv_eq. exact HaccLow_service.
          -- split.
             ++ destruct Hpriv_disj as [Hpriv_none | Hpriv_eq].
                ** rewrite Hpriv_none in HaccLow_priv. discriminate.
                ** rewrite <- Hpriv_eq. exact HaccLow_priv.
             ++ destruct Hkey_disj as [Hkey_none | Hkey_eq].
                ** rewrite Hkey_none in HaccLow_key. discriminate.
                ** rewrite <- Hkey_eq. rewrite HaccLow_key. discriminate.
      + exfalso. apply Hnotin. exact Hin.

    - (* File_Directory_Discovery_Local *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'. contradiction.

    - (* File_Directory_Discovery_Remote *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'. contradiction.

    - (* Network_Service_Scanning *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'. contradiction.

    - (* Remote_System_Discovery *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'. contradiction.

    - (* Account_Discovery_Local *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'. contradiction.

    - (* Account_Discovery_Remote *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'. contradiction.

    - (* System_Service_Discovery *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'. contradiction.
  Qed.

  (* ===== Lemas auxiliares de invarianza/inversa ===== *)

  (* one_step preserva mastered_exploits (estatico durante la campana).
     Caso por tecnica; todas las Post lo conservan, BF con orden invertido. *)
  Lemma one_step_preserves_mastered_exploits :
    forall (a a': Attacker) (t: Technique) (n: network_map),
      one_step a t n a' ->
      mastered_exploits a' = mastered_exploits a.
  Proof.
    intros a a' t n Honestep.
    destruct Honestep.
    destruct t; unfold Post in H2.
    - destruct H2 as [_ [_ [_ Hme]]]. exact Hme.
    - destruct H2 as [_ [Hme _]]. exact Hme.
    - destruct H2 as [_ [_ [Hme _]]]. exact Hme.
    - destruct H2 as [_ [_ [Hme _]]]. symmetry. exact Hme.
    - destruct H2 as [_ [Hme _]]. exact Hme.
    - destruct H2 as [_ [Hme _]]. exact Hme.
    - destruct H2 as [_ [Hme _]]. exact Hme.
    - destruct H2 as [_ [_ [Hme _]]]. exact Hme.
    - destruct H2 as [_ [_ [Hme _]]]. exact Hme.
    - destruct H2 as [_ [_ [Hme _]]]. exact Hme.
    - destruct H2 as [_ [_ [Hme _]]]. exact Hme.
    - destruct H2 as [_ [_ [Hme _]]]. exact Hme.
  Qed.

  (* obtainable_via_exploitation depende de mastered_exploits, invariante via one_step *)
  Lemma obtainable_via_exploitation_mastered_eq :
    forall (a a': Attacker) (n: network_map) (mid: idMachine) (u: idUser),
      mastered_exploits a = mastered_exploits a' ->
      obtainable_via_exploitation n a' mid u ->
      obtainable_via_exploitation n a mid u.
  Proof.
    intros a a' n mid u Heq Hexp.
    unfold obtainable_via_exploitation, has_usable_exploit in *.
    destruct Hexp as [mac [s [acc [serv [Hn [Hin_serv [Hsv [Hexp [Hin_acc [Huser Hsvc]]]]]]]]]].
    exists mac, s, acc, serv.
    split; [exact Hn |].
    split; [exact Hin_serv |].
    split; [exact Hsv |].
    split.
    - destruct Hexp as [e [s' [Hin_e Hin_me]]].
      exists e, s'. split; [exact Hin_e |]. rewrite Heq. exact Hin_me.
    - split; [exact Hin_acc |].
      split; [exact Huser | exact Hsvc].
  Qed.

  (* Version sin Hnotin: cualquier usuario en known_machines a' es obtenible desde a *)
  Lemma one_step_known_machines_obtainable :
    forall (a a': Attacker) (t: Technique) (n: network_map) (mid: idMachine) (u: idUser),
      valid_concrete_network n ->
      valid_attacker a n ->
      one_step a t n a' ->
      In (mid, u) (known_machines a') ->
      obtainable_user n a mid u.
  Proof.
    intros a a' t n mid u Hcn Hva Honestep Hin'.
    destruct (classic (In (mid, u) (known_machines a))) as [Hin_a | Hnotin_a].
    - left. exact Hin_a.
    - apply (one_step_adds_obtainable_user a a' t n mid u); auto.
  Qed.

  (* Inversa de la monotonia: si u es obtenible desde a', es obtenible desde a *)
  Lemma one_step_obtainable_inverse :
    forall (a a': Attacker) (t: Technique) (n: network_map) (mid: idMachine) (u: idUser),
      valid_concrete_network n ->
      valid_attacker a n ->
      one_step a t n a' ->
      obtainable_user n a' mid u ->
      obtainable_user n a mid u.
  Proof.
    intros a a' t n mid u Hcn Hva Honestep Hobt'.
    destruct Hobt' as [Hin' | [Hrs | [Hexp | Hloc]]].
    - eapply one_step_known_machines_obtainable; eassumption.
    - right. left. exact Hrs.
    - right. right. left.
      eapply obtainable_via_exploitation_mastered_eq; [|exact Hexp].
      symmetry. eapply one_step_preserves_mastered_exploits. exact Honestep.
    - right. right. right. exact Hloc.
  Qed.

  (* Inversa via multi_step *)
  Lemma multi_step_obtainable_inverse :
    forall (a a': Attacker) (n: network_map) (mid: idMachine) (u: idUser),
      valid_concrete_network n ->
      valid_attacker a n ->
      multi_step a n a' ->
      obtainable_user n a' mid u ->
      obtainable_user n a mid u.
  Proof.
    intros a a' n mid u Hcn Hva Hmulti.
    induction Hmulti as [a0 n0 | a0 a0' a0'' t n0 Hone Hmulti' IH]; intro Hobt'.
    - exact Hobt'.
    - assert (Hva' : valid_attacker a0' n0).
      { eapply one_step_preserves_valid_attacker. exact Hone. }
      eapply one_step_obtainable_inverse; try eassumption.
      apply IH; assumption.
  Qed.

  (* Multi-step: cualquier usuario en known_machines a' es obtenible desde a *)
  Lemma multi_step_known_machines_obtainable :
    forall (a a': Attacker) (n: network_map) (mid: idMachine) (u: idUser),
      valid_concrete_network n ->
      valid_attacker a n ->
      multi_step a n a' ->
      In (mid, u) (known_machines a') ->
      obtainable_user n a mid u.
  Proof.
    intros a a' n mid u Hcn Hva Hmulti Hin'.
    eapply multi_step_obtainable_inverse; try eassumption.
    left. exact Hin'.
  Qed.

  (* ===== Teoremas de persistencia ===== *)

  (* Si un secreto es permanentemente inaccesible,
     la propiedad exists_inaccessible_secret se preserva tras multi_step.
     Para todo u en known_machines a' (que tiene acceso al archivo),
     u es obtenible desde a (por multi_step_known_machines_obtainable),
     contradiciendo que ningun u con acceso es obtenible (Hnotobt). *)
  Theorem permanently_inaccessible_secret_persists :
    forall (a a': Attacker) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      multi_step a n a' ->
      exists_permanently_inaccessible_secret a n ->
      exists_inaccessible_secret a' n.
  Proof.
    intros a a' n Hcn Hva Hmulti Hperm.
    destruct Hperm as [mid [mac [f [Hn [Hin [Hobj [_ Hnotobt]]]]]]].
    exists mid, mac, f.
    split; [exact Hn |].
    split; [exact Hin |].
    split; [exact Hobj |].
    intros u Huk Huaccess.
    apply (Hnotobt u Huaccess).
    eapply multi_step_known_machines_obtainable; eassumption.
  Qed.

  (* La estructura de inaccesibilidad permanente tambien persiste:
     reachable se preserva via multi_step_preserves_reachable;
     "no obtenible" se transfiere via multi_step_obtainable_inverse. *)
  Theorem permanently_inaccessible_persists_strong :
    forall (a a': Attacker) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      multi_step a n a' ->
      exists_permanently_inaccessible_secret a n ->
      exists_permanently_inaccessible_secret a' n.
  Proof.
    intros a a' n Hcn Hva Hmulti Hperm.
    destruct Hperm as [mid [mac [f [Hn [Hin [Hobj [Hreach Hnotobt]]]]]]].
    exists mid, mac, f.
    split; [exact Hn |].
    split; [exact Hin |].
    split; [exact Hobj |].
    split.
    - eapply multi_step_preserves_reachable; eassumption.
    - intros u Huaccess Hobt'.
      apply (Hnotobt u Huaccess).
      eapply multi_step_obtainable_inverse; eassumption.
  Qed.

  (* ===== Invariante: secretos implican usuarios obtenibles con acceso =====

     Si una ruta objetivo aparece en secrets a, existe un usuario obtenible
     desde a con acceso al archivo. La conclusion usa obtainable_user (no solo
     known_machines) porque FDDR puede agregar un secreto sin que el usuario
     con acceso entre a known_machines: el atacante autentica como u' con
     credenciales validas pero u' no se incorpora a known_machines. La forma
     correcta de capturar la traza es entonces "u es obtenible_via_remote_services"
     (un disjunto estatico de obtainable_user). *)
  Definition secrets_have_obtainable_users (a: Attacker) (n: network_map) : Prop :=
    forall (mid: idMachine) (mac: Machine) (f: File),
      n mid = Some mac ->
      In f (machine_fileSystem mac) ->
      file_objective f = true ->
      In (mid, file_path f) (secrets a) ->
      exists (u: idUser), obtainable_user n a mid u /\ In u (file_user_access f).

  (* ===== Monotonia hacia adelante ===== *)

  (* one_step preserva known_machines hacia adelante (caso por tecnica) *)
  Lemma one_step_known_machines_monotone :
    forall (a a': Attacker) (t: Technique) (n: network_map) (mid: idMachine) (u: idUser),
      one_step a t n a' ->
      In (mid, u) (known_machines a) ->
      In (mid, u) (known_machines a').
  Proof.
    intros a a' t n mid u Honestep Hin.
    destruct Honestep.
    destruct t; unfold Post in H2.
    - destruct H2 as [Hkm _]. rewrite Hkm. apply member_add_machine_user. right. exact Hin.
    - destruct H2 as [_ [_ Hex]].
      destruct Hex as [? [? [? [? [? [? [? [_ [_ [_ [_ [_ [Hkm _]]]]]]]]]]]]].
      rewrite Hkm. apply member_add_machine_user. right. exact Hin.
    - destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
    - destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
    - destruct H2 as [_ [_ Hex]].
      destruct Hex as [? [? [? [? [? [? [? [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hkm _]]]]]]]]]]]]]]]]].
      rewrite Hkm. apply member_add_machine_user. right. exact Hin.
    - destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
    - destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
    - destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
    - destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
    - destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
    - destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
    - destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
  Qed.

  (* obtainable_user es monotono hacia adelante via one_step *)
  Lemma obtainable_user_monotone_one_step :
    forall (a a': Attacker) (t: Technique) (n: network_map) (mid: idMachine) (u: idUser),
      one_step a t n a' ->
      obtainable_user n a mid u ->
      obtainable_user n a' mid u.
  Proof.
    intros a a' t n mid u Honestep Hobt.
    destruct Hobt as [Hin | [Hrs | [Hexp | Hloc]]].
    - left. eapply one_step_known_machines_monotone; eassumption.
    - right. left. exact Hrs.
    - right. right. left.
      eapply (obtainable_via_exploitation_mastered_eq a' a n mid u).
      + eapply one_step_preserves_mastered_exploits. exact Honestep.
      + exact Hexp.
    - right. right. right. exact Hloc.
  Qed.

  Lemma obtainable_user_monotone_multi_step :
    forall (a a': Attacker) (n: network_map) (mid: idMachine) (u: idUser),
      multi_step a n a' ->
      obtainable_user n a mid u ->
      obtainable_user n a' mid u.
  Proof.
    intros a a' n mid u Hmulti Hobt.
    induction Hmulti.
    - exact Hobt.
    - apply IHHmulti. eapply obtainable_user_monotone_one_step; eassumption.
  Qed.

  (* ===== Preservacion del invariante ===== *)

  (* one_step preserva secrets_have_obtainable_users.
     - Tecnicas que preservan secrets: aplicar Hinv directamente y monotonia.
     - FDDL: nuevo secreto se justifica con el usuario u_p de Pre,
       que esta en known_machines a (disjunto 1 de obtainable_user).
     - FDDR: nuevo secreto se justifica con el usuario u_p' de Pre,
       que tiene credenciales validas en mac' (disjunto 2,
       obtainable_via_remote_services). *)
  Lemma one_step_preserves_secrets_have_obtainable_users :
    forall (a a': Attacker) (t: Technique) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      secrets_have_obtainable_users a n ->
      one_step a t n a' ->
      secrets_have_obtainable_users a' n.
  Proof.
    intros a a' t n Hcn Hva Hinv Honestep.
    intros mid mac f Hn Hin Hobj Hsec'.
    assert (Hgeneric: In (mid, file_path f) (secrets a) ->
                      exists u, obtainable_user n a' mid u /\ In u (file_user_access f)).
    { intros Hsec_a.
      destruct (Hinv mid mac f Hn Hin Hobj Hsec_a) as [u' [Hobt Hua]].
      exists u'. split; [|exact Hua].
      eapply obtainable_user_monotone_one_step; eassumption. }
    destruct Honestep.
    destruct t as
      [m_p u_p m_p' u_p' k_p' s_p
      | m_p u_p m_p' s_p' e_p
      | m_p u_p s_p
      | m_p u_p m_p' u_p' s_p'
      | m_p u_p
      | m_p u_p p_p
      | m_p u_p m_p' u_p' k_p' p_p' s_p'
      | m_p u_p m_p' l_p
      | m_p u_p
      | m_p u_p s_p
      | m_p u_p m_p' u_p' k_p' s_p'
      | m_p u_p];
    unfold Pre in H1; unfold Post in H2.

    - (* Remote_Services *)
      destruct H2 as [_ [Hsec_eq _]]. apply Hgeneric. rewrite <- Hsec_eq. exact Hsec'.

    - (* Exploitation_Remote_Services *)
      destruct H2 as [Hsec_eq _]. apply Hgeneric. rewrite <- Hsec_eq. exact Hsec'.

    - (* Unsecured_Credentials *)
      destruct H2 as [_ [Hsec_eq _]]. apply Hgeneric. rewrite <- Hsec_eq. exact Hsec'.

    - (* Brute_Force *)
      destruct H2 as [_ [Hsec_eq _]]. apply Hgeneric. rewrite <- Hsec_eq. exact Hsec'.

    - (* Abuse_Elevation_Control_Mechanism *)
      destruct H2 as [Hsec_eq _]. apply Hgeneric. rewrite <- Hsec_eq. exact Hsec'.

    - (* File_Directory_Discovery_Local *)
      destruct H2 as [Hkm_eq [_ [mac_post [_ [_ [filesMac [_ [newSecrets [_ [Hnet_post [HfilesMac_eq [HnewSec_eq [Hsec_eq _]]]]]]]]]]]]].
      rewrite Hsec_eq in Hsec'.
      apply oplusSecrets_membership in Hsec'.
      destruct Hsec' as [Hold | Hnew].
      + apply Hgeneric. exact Hold.
      + rewrite HnewSec_eq in Hnew.
        apply getPaths_objectives_membership in Hnew.
        destruct Hnew as [Hmid_eq [f' [Hin_f' Hpath_f']]].
        rewrite Hmid_eq in Hn.
        assert (Heq_mac: mac = mac_post).
        { eapply enviroment_map_image; eassumption. }
        subst mac.
        rewrite HfilesMac_eq in Hin_f'.
        destruct H1 as [Hkn_pre _].
        destruct Hcn as [_ Hvm].
        rewrite <- Hmid_eq in Hn.
        destruct (Hvm mid mac_post Hn) as [Hvalid_mac _].
        unfold valid_machine in Hvalid_mac.
        destruct Hvalid_mac as [_ [_ [_ Hvfs]]].
        unfold valid_fileSystem in Hvfs.
        destruct Hvfs as [_ [Hnodup _]].
        apply NoDup_map_file_path_unique_paths in Hnodup.
        assert (Hu_acc_f': In u_p (file_user_access f')).
        { eapply getFiles_user_access. exact Hin_f'. }
        assert (Hsubset: subset_files (getFiles (machine_fileSystem mac_post) p_p u_p)
                                       (machine_fileSystem mac_post)).
        { apply getFiles_subset_files_mac. }
        unfold subset_files in Hsubset.
        destruct (Hsubset f' Hin_f') as [Hf'_in | [g [Hin_g Hview_g]]].
        * assert (Heq_f: f' = f).
          { apply (Hnodup f' f Hf'_in Hin Hpath_f'). }
          rewrite Heq_f in Hu_acc_f'.
          exists u_p. split; [|exact Hu_acc_f'].
          left. rewrite Hkm_eq. rewrite Hmid_eq. exact Hkn_pre.
        * destruct Hview_g as [Hpath_g [_ [_ Husers_g]]].
          assert (Heq_g: g = f).
          { apply (Hnodup g f Hin_g Hin). rewrite <- Hpath_g. exact Hpath_f'. }
          rewrite Heq_g in Husers_g.
          exists u_p. split; [|apply Husers_g; exact Hu_acc_f'].
          left. rewrite Hkm_eq. rewrite Hmid_eq. exact Hkn_pre.

    - (* File_Directory_Discovery_Remote *)
      destruct H2 as [Hkm_eq [_ [mac_post [macView_post [_ [filesMac [_ [newSecrets [Henv_post [Hnet_post [HfilesMac_eq [HnewSec_eq [Hsec_eq _]]]]]]]]]]]]].
      rewrite Hsec_eq in Hsec'.
      apply oplusSecrets_membership in Hsec'.
      destruct Hsec' as [Hold | Hnew].
      + apply Hgeneric. exact Hold.
      + rewrite HnewSec_eq in Hnew.
        apply getPaths_objectives_membership in Hnew.
        destruct Hnew as [Hmid_eq [f' [Hin_f' Hpath_f']]].
        rewrite Hmid_eq in Hn.
        assert (Heq_mac: mac = mac_post).
        { eapply enviroment_map_image; eassumption. }
        subst mac.
        rewrite HfilesMac_eq in Hin_f'.
        destruct H1 as [_ [_ [macView_pre [_ [_ [acc_pre [Henv_pre [_ [_ [_ [Hin_acc [Huser [Hsvc [Hkey _]]]]]]]]]]]]]].
        assert (Heq_view: macView_pre = macView_post).
        { eapply enviroment_map_image; eassumption. }
        subst macView_pre.
        destruct H0 as [_ [_ [_ Hview]]].
        unfold valid_attacker_iv, is_networkView in Hview.
        destruct (Hview _ _ Henv_post) as [mac_iv [Hn_iv Hmv]].
        assert (Heq_mac_iv: mac_iv = mac_post).
        { eapply enviroment_map_image; eassumption. }
        subst mac_iv.
        destruct Hmv as [_ [Hacc_subset _]].
        unfold subset_accounts in Hacc_subset.
        specialize (Hacc_subset acc_pre Hin_acc).
        destruct Hcn as [_ Hvm].
        rewrite <- Hmid_eq in Hn.
        destruct (Hvm mid mac_post Hn) as [Hvalid_mac _].
        unfold valid_machine in Hvalid_mac.
        destruct Hvalid_mac as [_ [_ [_ Hvfs]]].
        unfold valid_fileSystem in Hvfs.
        destruct Hvfs as [_ [Hnodup _]].
        apply NoDup_map_file_path_unique_paths in Hnodup.
        assert (Hu_acc_f': In u_p' (file_user_access f')).
        { eapply getFiles_user_access. exact Hin_f'. }
        assert (Hsubset: subset_files (getFiles (machine_fileSystem mac_post) p_p' u_p')
                                       (machine_fileSystem mac_post)).
        { apply getFiles_subset_files_mac. }
        unfold subset_files in Hsubset.
        assert (Hu_in_f: In u_p' (file_user_access f)).
        { destruct (Hsubset f' Hin_f') as [Hf'_in | [g [Hin_g Hview_g]]].
          - assert (Heq_f: f' = f) by (apply (Hnodup f' f Hf'_in Hin Hpath_f')).
            rewrite Heq_f in Hu_acc_f'. exact Hu_acc_f'.
          - destruct Hview_g as [Hpath_g [_ [_ Husers_g]]].
            assert (Heq_g: g = f).
            { apply (Hnodup g f Hin_g Hin). rewrite <- Hpath_g. exact Hpath_f'. }
            rewrite Heq_g in Husers_g. apply Husers_g. exact Hu_acc_f'. }
        exists u_p'. split; [|exact Hu_in_f].
        right. left. unfold obtainable_via_remote_services.
        destruct Hacc_subset as [Hacc_in | [acc_n [Hacc_in Hview_acc]]].
        * exists mac_post, acc_pre. eexists.
          split; [exact Hn |].
          split; [exact Hacc_in |].
          split; [exact Huser |].
          split; [exact Hsvc |].
          exact Hkey.
        * destruct Hview_acc as [Huser_eq [Hsvc_disj [Hkey_disj _]]].
          exists mac_post, acc_n. eexists.
          split; [exact Hn |].
          split; [exact Hacc_in |].
          split; [rewrite <- Huser_eq; exact Huser |].
          split.
          -- destruct Hsvc_disj as [Hnone | Heq].
             ++ rewrite Hnone in Hsvc. discriminate.
             ++ rewrite <- Heq. exact Hsvc.
          -- destruct Hkey_disj as [Hnone | Heq].
             ++ intro Habs. apply Hkey. exact Hnone.
             ++ rewrite <- Heq. exact Hkey.

    - (* Network_Service_Scanning *)
      destruct H2 as [_ [Hsec_eq _]]. apply Hgeneric. rewrite <- Hsec_eq. exact Hsec'.

    - (* Remote_System_Discovery *)
      destruct H2 as [_ [Hsec_eq _]]. apply Hgeneric. rewrite <- Hsec_eq. exact Hsec'.

    - (* Account_Discovery_Local *)
      destruct H2 as [_ [Hsec_eq _]]. apply Hgeneric. rewrite <- Hsec_eq. exact Hsec'.

    - (* Account_Discovery_Remote *)
      destruct H2 as [_ [Hsec_eq _]]. apply Hgeneric. rewrite <- Hsec_eq. exact Hsec'.

    - (* System_Service_Discovery *)
      destruct H2 as [_ [Hsec_eq _]]. apply Hgeneric. rewrite <- Hsec_eq. exact Hsec'.
  Qed.

  (* multi_step preserva el invariante por induccion *)
  Lemma multi_step_preserves_secrets_have_obtainable_users :
    forall (a a': Attacker) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      secrets_have_obtainable_users a n ->
      multi_step a n a' ->
      secrets_have_obtainable_users a' n.
  Proof.
    intros a a' n Hcn Hva Hinv Hmulti.
    induction Hmulti as [a0 n0 | a0 a0' a0'' t n0 Hone Hmulti' IH].
    - exact Hinv.
    - apply IH.
      + exact Hcn.
      + eapply one_step_preserves_valid_attacker. exact Hone.
      + eapply one_step_preserves_secrets_have_obtainable_users; eassumption.
  Qed.

  (* ===== Puente y teoremas de imposibilidad ===== *)

  (* Si una ruta objetivo aparece en secrets a' tras multi_step, existe un
     usuario obtenible desde a' con acceso al archivo. Corolario directo
     del invariante preservado. *)
  Lemma multi_step_secret_implies_obtainable_with_access :
    forall (a a': Attacker) (n: network_map) (mid: idMachine) (mac: Machine) (f: File),
      valid_concrete_network n ->
      valid_attacker a n ->
      secrets_have_obtainable_users a n ->
      multi_step a n a' ->
      n mid = Some mac ->
      In f (machine_fileSystem mac) ->
      file_objective f = true ->
      In (mid, file_path f) (secrets a') ->
      exists (u: idUser), obtainable_user n a' mid u /\ In u (file_user_access f).
  Proof.
    intros a a' n mid mac f Hcn Hva Hinv Hmulti Hn Hin Hobj Hsec'.
    pose proof (multi_step_preserves_secrets_have_obtainable_users
                  a a' n Hcn Hva Hinv Hmulti) as Hinv'.
    apply (Hinv' mid mac f Hn Hin Hobj Hsec').
  Qed.

  (* Si hay un secreto permanentemente inaccesible, el atacante nunca puede
     conocer todos los secretos de la red. La hipotesis adicional
     secrets_have_obtainable_users a n se cumple trivialmente cuando secrets a
     es vacio (atacante inicial sin secretos previos). *)
  Theorem permanently_inaccessible_blocks_all_secrets :
    forall (a a': Attacker) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      secrets_have_obtainable_users a n ->
      multi_step a n a' ->
      exists_permanently_inaccessible_secret a n ->
      ~ all_secrets_known a' n.
  Proof.
    intros a a' n Hcn Hva Hinv Hmulti Hperm Hall.
    destruct Hperm as [mid [mac [f [Hn [Hin [Hobj [_ Hnotobt]]]]]]].
    specialize (Hall mid mac f Hn Hin Hobj).
    destruct (multi_step_secret_implies_obtainable_with_access
                a a' n mid mac f Hcn Hva Hinv Hmulti Hn Hin Hobj Hall)
      as [u [Hobt' Huaccess]].
    apply (Hnotobt u Huaccess).
    eapply multi_step_obtainable_inverse; eassumption.
  Qed.

  (* Cualquiera de las dos barreras permanentes impide conocer todos los secretos.
     Composicion directa de los dos teoremas de imposibilidad.
     Toma ambos invariantes (secrets_have_reachable_machines y
     secrets_have_obtainable_users) como hipotesis; ambos son trivialmente
     verdaderos cuando secrets a = nil (atacante inicial). *)
  Theorem any_barrier_blocks_all_secrets :
    forall (a a': Attacker) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      secrets_have_reachable_machines a n ->
      secrets_have_obtainable_users a n ->
      multi_step a n a' ->
      (exists_unreachable_secret a n
       \/ exists_permanently_inaccessible_secret a n) ->
      ~ all_secrets_known a' n.
  Proof.
    intros a a' n Hcn Hva Hinv_reach Hinv_obt Hmulti [Hunr | Hperm].
    - eapply unreachable_secret_blocks_all_secrets; eassumption.
    - eapply permanently_inaccessible_blocks_all_secrets; eassumption.
  Qed.

  (* ===== Teorema de alcanzabilidad (existencial) ===== *)

  (* Si inaccessibility_breakable se cumple, existe un multi_step
     tras el cual el atacante gana un usuario con acceso al archivo
     objetivo. Este es el teorema mas dificil de probar porque requiere
     construir la traza de descubrimiento completa:
     Remote_System_Discovery -> System_Service_Discovery ->
     Unsecured_Credentials -> Remote_Services/Exploitation. *)
  Theorem breakable_inaccessibility_can_be_broken :
    forall (a: Attacker) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      inaccessibility_breakable a n ->
      exists (a': Attacker),
        multi_step a n a'
        /\ exists (mid: idMachine) (mac: Machine) (f: File) (u: idUser),
             n mid = Some mac
             /\ In f (machine_fileSystem mac)
             /\ file_objective f = true
             /\ In (mid, u) (known_machines a')
             /\ In u (file_user_access f).
  Proof.
  Admitted.

End AttackerAccess.
