Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniqueOneStep.
Require Import Technique.TechniquePostCondition.
Require Import Invariant.AuxLemmas.AuxLemmasMachineUser.

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
      + (* Brute_Force *) admit.
      + (* Abuse_Elevation_Control_Mechanism *) admit.
      + (* File_Directory_Discovery_Local *)
        destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
      + (* File_Directory_Discovery_Remote *) admit.
      + (* Network_Service_Scanning *) admit.
      + (* Remote_System_Discovery *)
        destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
      + (* Account_Discovery_Local *) admit.
      + (* Account_Discovery_Remote *) admit.
      + (* System_Service_Discovery *)
        destruct H2 as [Hkm _]. rewrite Hkm. exact Hin.
    - exact Hreach.
  Admitted.

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

  (* ===== Persistencia de inalcanzabilidad ===== *)

  (* Si una maquina es inalcanzable antes de un paso, sigue siendolo despues.
     Contrapositivo de one_step_preserves_reachable. *)
  Lemma unreachable_persists_after_one_step : forall (a a': Attacker) (t: Technique) (n: network_map) (mid: idMachine),
    one_step a t n a' ->
    ~ reachable n a mid ->
    ~ reachable n a' mid.
  Proof.
  Admitted.

  (* Si una maquina es inalcanzable antes de multi_step, sigue siendolo despues.
     Generalizacion de unreachable_persists_after_one_step por induccion. *)
  Lemma unreachable_persists_after_multi_step : forall (a a': Attacker) (n: network_map) (mid: idMachine),
    multi_step a n a' ->
    ~ reachable n a mid ->
    ~ reachable n a' mid.
  Proof.
  Admitted.

  (* ===== Persistencia de exists_unreachable_secret ===== *)

  (* Si al inicio existe un objetivo en una maquina inalcanzable,
     esa maquina sigue siendo inalcanzable tras multi_step. *)
  Lemma exists_unreachable_secret_persists : forall (a a': Attacker) (n: network_map),
    multi_step a n a' ->
    exists_unreachable_secret a n ->
    exists_unreachable_secret a' n.
  Proof.
  Admitted.

  (* ===== Teoremas de imposibilidad ===== *)

  (* Resultado directo: si existe un objetivo en una maquina inalcanzable,
     el atacante no puede conocer todos los secretos en su estado actual. *)
  Theorem unreachable_secret_prevents_all_secrets_known : forall (a: Attacker) (n: network_map),
    exists_unreachable_secret a n ->
    ~ all_secrets_known a n.
  Proof.
  Admitted.

  (* Resultado principal: si al inicio existe un secreto inalcanzable,
     entonces sin importar cuantos pasos ejecute el atacante,
     nunca podra conocer todos los secretos de la red. *)
  Theorem unreachable_secret_blocks_all_secrets : forall (a a': Attacker) (n: network_map),
    valid_concrete_network n ->
    valid_attacker a n ->
    multi_step a n a' ->
    exists_unreachable_secret a n ->
    ~ all_secrets_known a' n.
  Proof.
  Admitted.

End AttackerReachability.
