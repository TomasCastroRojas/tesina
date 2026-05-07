Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineView.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniqueOneStep.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.
Require Import Invariant.AuxLemmas.AuxLemmasMachineUser.
Require Import Invariant.AuxLemmas.AuxLemmasFile.
Require Import Invariant.AuxLemmas.AuxLemmasSecret.
Require Import Invariant.ValidAttacker.ValidAttacker.

Section AttackerReachability.

  (* ===== Lemas auxiliares sobre monotonia de reachable ===== *)

  (* Si known_machines a es subconjunto de known_machines a',
     entonces toda maquina alcanzable desde a tambien lo es desde a'.
     Esto es clave porque las tecnicas solo agregan a known_machines. *)
  Lemma reachable_monotone : forall (n: network_map) (a a': Attacker) (mid: idMachine),
    (forall (m: idMachine) (u: idUser), In (m, u) (known_machines a) -> In (m, u) (known_machines a')) ->
    reachable n a mid ->
    reachable n a' mid.
  Proof.
    intros n a a' mid H_subset H_reach.
    induction H_reach as [m u Hin | m m' mac Hreach IH Hmac Hneigh].
    - apply (reachable_known n a' m u).
      apply H_subset. exact Hin.
    - apply (reachable_step n a' m m' mac).
      + exact IH.
      + exact Hmac.
      + exact Hneigh.
  Qed.

  (* ===== Preservacion de alcanzabilidad tras one_step ===== *)

  (* Tras un paso de ejecucion, toda maquina previamente alcanzable sigue siendolo.
     one_step solo agrega a known_machines maquinas que ya eran vecinas de maquinas
     conocidas (via add_machine_user), y por tanto ya eran reachable. *)
  Lemma one_step_preserves_reachable : forall (a a': Attacker) (t: Technique) (n: network_map) (mid: idMachine),
    one_step a t n a' ->
    reachable n a mid ->
    reachable n a' mid.
  Proof.
    intros a a' t n mid Honestep Hreach.
    destruct Honestep.
    apply (reachable_monotone network a a' mid).
    - intros m0 u0 Hin.
      destruct t; unfold Post in H2.
      + (* Remote_Services *)
        destruct H2 as [Hkm _]. rewrite Hkm.
        apply member_add_machine_user. right. exact Hin.
      + (* Exploitation_Remote_Services *)
        destruct H2 as [_ [_ Hex]].
        destruct Hex as [? [? [? [? [? [? [? [_ [_ [_ [_ [_ [Hkm _]]]]]]]]]]]]].
        rewrite Hkm. apply member_add_machine_user. right. exact Hin.
      + (* Unsecured_Credentials *)
        destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
      + (* Brute_Force *)
        destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
      + (* Abuse_Elevation_Control_Mechanism *)
        destruct H2 as [_ [_ Hex]].
        destruct Hex as [? [? [? [? [? [? [? [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hkm _]]]]]]]]]]]]]]]]].
        rewrite Hkm. apply member_add_machine_user. right. exact Hin.
      + (* File_Directory_Discovery_Local *)
        destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
      + (* File_Directory_Discovery_Remote *)
        destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
      + (* Network_Service_Scanning *)
        destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
      + (* Remote_System_Discovery *)
        destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
      + (* Account_Discovery_Local *)
        destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
      + (* Account_Discovery_Remote *)
        destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
      + (* System_Service_Discovery *)
        destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
    - exact Hreach.
  Qed.

  (* ===== Preservacion de alcanzabilidad tras multi_step ===== *)

  (* Generalizacion por induccion sobre multi_step:
     la alcanzabilidad se preserva tras cualquier cantidad de pasos. *)
  Lemma multi_step_preserves_reachable : forall (a a': Attacker) (n: network_map) (mid: idMachine),
    multi_step a n a' ->
    reachable n a mid ->
    reachable n a' mid.
  Proof.
    intros a a' n mid Hmulti Hreach.
    induction Hmulti.
    - exact Hreach.
    - apply IHHmulti. eapply one_step_preserves_reachable; eassumption.
  Qed.

  (* ===== Cobertura del entorno sobre la red concreta =====

     Toda maquina conocida por el atacante existe tambien en la red concreta.
     Se sigue de valid_attacker_i (todo (m, u) en known_machines tiene entrada
     en enviroment a) compuesto con la nueva definicion de is_networkView
     (toda entrada de enviroment a tiene contraparte en la red concreta). *)
  Lemma env_known_in_network : forall (a: Attacker) (n: network_map),
    valid_attacker a n ->
    forall (m: idMachine) (u: idUser),
      In (m, u) (known_machines a) ->
      exists (mac: Machine), n m = Some mac.
  Proof.
    intros a n Hva m u Hin.
    destruct Hva as [Hi [_ [_ Hiv]]].
    unfold valid_attacker_i in Hi.
    unfold valid_attacker_iv, is_networkView in Hiv.
    destruct (Hi m u Hin) as [mac [Henv _]].
    destruct (Hiv m mac Henv) as [mac' [Hn _]].
    exists mac'. exact Hn.
  Qed.

  (* ===== Inversa de la monotonia de reachable ===== *)

  (* Para todo par (m, u) en known_machines a', m ya era alcanzable desde a.
     Caso por tecnica:
     - Tecnicas que preservan known_machines: (m, u) ya estaba en a, aplica
       reachable_known.
     - Remote_Services / Exploitation_Remote_Services: el nuevo m' es vecino
       de un m_pre ya conocido en la vista del atacante. Via env_known_in_network
       se obtiene la imagen de m_pre en n, y is_networkView transfiere el
       vecindario al n concreto, dando reachable_step.
     - Abuse_Elevation_Control_Mechanism: agrega (m, u') con m ya conocido,
       aplica reachable_known directo. *)
  Lemma one_step_known_machines_was_reachable :
    forall (a a': Attacker) (t: Technique) (n: network_map) (m: idMachine) (u: idUser),
      one_step a t n a' ->
      In (m, u) (known_machines a') ->
      reachable n a m.
  Proof.
    intros a a' t n m u Honestep Hin'.
    destruct Honestep.
    destruct t; unfold Pre in H1; unfold Post in H2.
    - (* Remote_Services *)
      destruct H2 as [Hkm _].
      rewrite Hkm in Hin'.
      apply member_add_machine_user in Hin'.
      destruct Hin' as [Heq | Hin].
      + injection Heq as Hmeq Hueq.
        rewrite <- Hmeq.
        destruct H1 as [Hkn [HenvNeigh _]].
        destruct HenvNeigh as [mac [Henv Hneigh]].
        destruct H0 as [_ [_ [_ Hview]]].
        unfold valid_attacker_iv, is_networkView in Hview.
        destruct (Hview _ _ Henv) as [mac_n [Hn1 Hmv]].
        destruct Hmv as [_ [_ [_ [Hsn _]]]].
        unfold subset_neighbours in Hsn.
        eapply reachable_step.
        * eapply reachable_known. exact Hkn.
        * exact Hn1.
        * apply Hsn. exact Hneigh.
      + eapply reachable_known. exact Hin.
    - (* Exploitation_Remote_Services *)
      destruct H2 as [_ [_ Hex]].
      destruct Hex as [? [? [? [? [? [? [? [_ [_ [_ [_ [_ [Hkm _]]]]]]]]]]]]].
      rewrite Hkm in Hin'.
      apply member_add_machine_user in Hin'.
      destruct Hin' as [Heq | Hin].
      + injection Heq as Hmeq Hueq.
        rewrite <- Hmeq.
        destruct H1 as [Hkn [HenvNeigh _]].
        destruct HenvNeigh as [mac [Henv Hneigh]].
        destruct H0 as [_ [_ [_ Hview]]].
        unfold valid_attacker_iv, is_networkView in Hview.
        destruct (Hview _ _ Henv) as [mac_n [Hn1 Hmv]].
        destruct Hmv as [_ [_ [_ [Hsn _]]]].
        unfold subset_neighbours in Hsn.
        eapply reachable_step.
        * eapply reachable_known. exact Hkn.
        * exact Hn1.
        * apply Hsn. exact Hneigh.
      + eapply reachable_known. exact Hin.
    - (* Unsecured_Credentials *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'.
      eapply reachable_known. exact Hin'.
    - (* Brute_Force *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'.
      eapply reachable_known. exact Hin'.
    - (* Abuse_Elevation_Control_Mechanism *)
      destruct H2 as [_ [_ Hex]].
      destruct Hex as [? [? [? [? [? [? [? [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hkm _]]]]]]]]]]]]]]]]].
      rewrite Hkm in Hin'.
      apply member_add_machine_user in Hin'.
      destruct Hin' as [Heq | Hin].
      + injection Heq as Hmeq Hueq.
        rewrite <- Hmeq.
        destruct H1 as [Hkn _].
        eapply reachable_known. exact Hkn.
      + eapply reachable_known. exact Hin.
    - (* File_Directory_Discovery_Local *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'.
      eapply reachable_known. exact Hin'.
    - (* File_Directory_Discovery_Remote *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'.
      eapply reachable_known. exact Hin'.
    - (* Network_Service_Scanning *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'.
      eapply reachable_known. exact Hin'.
    - (* Remote_System_Discovery *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'.
      eapply reachable_known. exact Hin'.
    - (* Account_Discovery_Local *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'.
      eapply reachable_known. exact Hin'.
    - (* Account_Discovery_Remote *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'.
      eapply reachable_known. exact Hin'.
    - (* System_Service_Discovery *)
      destruct H2 as [Hkm _]. rewrite Hkm in Hin'.
      eapply reachable_known. exact Hin'.
  Qed.

  (* Inversa de one_step_preserves_reachable: una maquina alcanzable desde a'
     tambien era alcanzable desde a. La induccion sobre la derivacion de
     reachable n a' mid reduce el caso base (reachable_known) al lema
     one_step_known_machines_was_reachable; el paso inductivo se cierra con
     reachable_step (que solo depende de la red concreta n, fija). *)
  Lemma one_step_reachable_inverse :
    forall (a a': Attacker) (t: Technique) (n: network_map) (mid: idMachine),
      one_step a t n a' ->
      reachable n a' mid ->
      reachable n a mid.
  Proof.
    intros a a' t n mid Honestep Hreach'.
    induction Hreach' as [m u Hin' | m m' mac _ IH Hmac Hneigh'].
    - eapply one_step_known_machines_was_reachable; eassumption.
    - eapply reachable_step; eassumption.
  Qed.

  (* ===== Persistencia de inalcanzabilidad ===== *)

  (* Si una maquina es inalcanzable antes de un paso, sigue siendolo despues.
     Por contraposicion de one_step_reachable_inverse. *)
  Lemma unreachable_persists_after_one_step : forall (a a': Attacker) (t: Technique) (n: network_map) (mid: idMachine),
    one_step a t n a' ->
    ~ reachable n a mid ->
    ~ reachable n a' mid.
  Proof.
    intros a a' t n mid Honestep Hunreach Hreach'.
    apply Hunreach.
    eapply one_step_reachable_inverse; eassumption.
  Qed.

  (* Si una maquina es inalcanzable antes de multi_step, sigue siendolo despues.
     Induccion sobre multi_step usando unreachable_persists_after_one_step. *)
  Lemma unreachable_persists_after_multi_step : forall (a a': Attacker) (n: network_map) (mid: idMachine),
    multi_step a n a' ->
    ~ reachable n a mid ->
    ~ reachable n a' mid.
  Proof.
    intros a a' n mid Hmulti.
    induction Hmulti as [a0 n0 | a0 a0' a0'' t n0 Hone Hmulti' IH]; intro Hunreach.
    - exact Hunreach.
    - apply IH.
      eapply unreachable_persists_after_one_step; eassumption.
  Qed.

  (* ===== Persistencia de exists_unreachable_secret ===== *)

  (* Si al inicio existe un objetivo en una maquina inalcanzable,
     esa maquina sigue siendo inalcanzable tras multi_step.
     El testigo (mid, mac, f) es el mismo: las primeras tres conjunciones
     (n mid = Some mac, In f, file_objective) no dependen del atacante;
     la inalcanzabilidad se transfiere via unreachable_persists_after_multi_step. *)
  Lemma exists_unreachable_secret_persists : forall (a a': Attacker) (n: network_map),
    multi_step a n a' ->
    exists_unreachable_secret a n ->
    exists_unreachable_secret a' n.
  Proof.
    intros a a' n Hmulti Hexists.
    destruct Hexists as [mid [mac [f [Hn [Hin [Hobj Hunreach]]]]]].
    exists mid, mac, f.
    repeat split; try assumption.
    eapply unreachable_persists_after_multi_step; eassumption.
  Qed.

  (* ===== Invariante: secretos implican maquinas alcanzables =====

     Si una ruta aparece en secrets a, su maquina es alcanzable desde a.
     Se preserva via one_step:
     - Tecnicas que preservan secrets: Hinv + monotonia de reachable.
     - FDDL: nuevo secreto en m_p donde (m_p, u_p) en known_machines a (Pre);
       reachable_known da reachable n a m_p.
     - FDDR: nuevo secreto en m_p' que es vecino de m_p en env a m_p;
       (m_p, u_p) en known_machines a, is_networkView transfiere el vecindario
       a la red concreta, reachable_step da reachable n a m_p'. *)
  Definition secrets_have_reachable_machines (a: Attacker) (n: network_map) : Prop :=
    forall (mid: idMachine) (p: path),
      In (mid, p) (secrets a) -> reachable n a mid.

  (* one_step preserva el invariante *)
  Lemma one_step_preserves_secrets_have_reachable_machines :
    forall (a a': Attacker) (t: Technique) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      secrets_have_reachable_machines a n ->
      one_step a t n a' ->
      secrets_have_reachable_machines a' n.
  Proof.
    intros a a' t n Hcn Hva Hinv Honestep.
    intros mid p Hsec'.
    assert (Hlift: forall m, reachable n a m -> reachable n a' m).
    { intros m Hr. eapply one_step_preserves_reachable; eassumption. }
    assert (Hgeneric: In (mid, p) (secrets a) -> reachable n a' mid).
    { intros Hsec_a. apply Hlift. apply (Hinv mid p Hsec_a). }
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
      destruct H2 as [_ [_ [_ [_ [_ [filesMac [_ [newSecrets [_ [_ [_ [HnewSec_eq [Hsec_eq _]]]]]]]]]]]]].
      rewrite Hsec_eq in Hsec'.
      apply oplusSecrets_membership in Hsec'.
      destruct Hsec' as [Hold | Hnew].
      + apply Hgeneric. exact Hold.
      + rewrite HnewSec_eq in Hnew.
        apply getPaths_objectives_membership in Hnew.
        destruct Hnew as [Hmid_eq _].
        destruct H1 as [Hkn_pre _].
        rewrite Hmid_eq.
        apply Hlift.
        eapply reachable_known. exact Hkn_pre.

    - (* File_Directory_Discovery_Remote *)
      destruct H2 as [_ [_ [_ [_ [_ [filesMac [_ [newSecrets [_ [_ [_ [HnewSec_eq [Hsec_eq _]]]]]]]]]]]]].
      rewrite Hsec_eq in Hsec'.
      apply oplusSecrets_membership in Hsec'.
      destruct Hsec' as [Hold | Hnew].
      + apply Hgeneric. exact Hold.
      + rewrite HnewSec_eq in Hnew.
        apply getPaths_objectives_membership in Hnew.
        destruct Hnew as [Hmid_eq _].
        destruct H1 as [Hkn_pre [HenvNeigh _]].
        destruct HenvNeigh as [mac_pre [Henv Hneigh_pre]].
        rewrite Hmid_eq.
        apply Hlift.
        destruct H0 as [_ [_ [_ Hview]]].
        unfold valid_attacker_iv, is_networkView in Hview.
        destruct (Hview _ _ Henv) as [mac_n [Hn_eq Hmv]].
        destruct Hmv as [_ [_ [_ [Hsn _]]]].
        unfold subset_neighbours in Hsn.
        eapply reachable_step.
        * eapply reachable_known. exact Hkn_pre.
        * exact Hn_eq.
        * apply Hsn. exact Hneigh_pre.

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

  (* multi_step preserva el invariante *)
  Lemma multi_step_preserves_secrets_have_reachable_machines :
    forall (a a': Attacker) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      secrets_have_reachable_machines a n ->
      multi_step a n a' ->
      secrets_have_reachable_machines a' n.
  Proof.
    intros a a' n Hcn Hva Hinv Hmulti.
    induction Hmulti as [a0 n0 | a0 a0' a0'' t n0 Hone Hmulti' IH].
    - exact Hinv.
    - apply IH.
      + exact Hcn.
      + eapply one_step_preserves_valid_attacker. exact Hone.
      + eapply one_step_preserves_secrets_have_reachable_machines; eassumption.
  Qed.

  (* Corolario directo: si (mid, p) en secrets, entonces mid es alcanzable *)
  Lemma secret_implies_reachable :
    forall (a: Attacker) (n: network_map) (mid: idMachine) (p: path),
      secrets_have_reachable_machines a n ->
      In (mid, p) (secrets a) ->
      reachable n a mid.
  Proof.
    intros a n mid p Hinv Hsec.
    apply (Hinv mid p Hsec).
  Qed.

  (* ===== Teoremas de imposibilidad ===== *)

  (* Resultado directo: si existe un objetivo en una maquina inalcanzable,
     el atacante no puede conocer todos los secretos en su estado actual.
     Si el atacante conociera todos los secretos, en particular conoceria
     (mid, file_path f); por el invariante, mid seria alcanzable; pero
     exists_unreachable_secret asegura ~ reachable. Contradiccion. *)
  Theorem unreachable_secret_prevents_all_secrets_known :
    forall (a: Attacker) (n: network_map),
      secrets_have_reachable_machines a n ->
      exists_unreachable_secret a n ->
      ~ all_secrets_known a n.
  Proof.
    intros a n Hinv Hexists Hall.
    destruct Hexists as [mid [mac [f [Hn [Hin [Hobj Hunreach]]]]]].
    specialize (Hall mid mac f Hn Hin Hobj).
    apply Hunreach.
    eapply secret_implies_reachable; eassumption.
  Qed.

  (* Resultado principal: si al inicio existe un secreto inalcanzable,
     entonces sin importar cuantos pasos ejecute el atacante, nunca podra
     conocer todos los secretos de la red. La hipotesis adicional
     secrets_have_reachable_machines a n se cumple trivialmente cuando
     secrets a = nil (atacante inicial sin secretos previos). *)
  Theorem unreachable_secret_blocks_all_secrets :
    forall (a a': Attacker) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      secrets_have_reachable_machines a n ->
      multi_step a n a' ->
      exists_unreachable_secret a n ->
      ~ all_secrets_known a' n.
  Proof.
    intros a a' n Hcn Hva Hinv Hmulti Hexists.
    apply unreachable_secret_prevents_all_secrets_known.
    - eapply multi_step_preserves_secrets_have_reachable_machines; eassumption.
    - eapply exists_unreachable_secret_persists; eassumption.
  Qed.

End AttackerReachability.
