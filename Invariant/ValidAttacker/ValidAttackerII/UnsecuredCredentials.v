Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmasEnviroment.
Require Import Invariant.AuxTactics.

Lemma one_step_unsecured_credentials_preserves_valid_attacker_ii : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m : idMachine) (u : idUser) (s: idService),
      valid_concrete_network n -> Pre a (Unsecured_Credentials m u s) -> Post a (Unsecured_Credentials m u s) n a' -> valid_attacker_ii a'.
  Proof.
    intros a a' network validAttacker m u s validNetwork pre post.
    unfold valid_attacker_ii.
    intros m0 p0 H_secrets_a'.
    unfold valid_attacker in validAttacker.
    elim validAttacker.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    unfold Pre in pre; destruct post.

    elim_intro_clear H0 Hsecrets H0'.
    elim_intro_clear H0' mac H0.
    elim_intro_clear H0 macView H0'.
    elim_intro_clear H0' newMacView H0.
    elim_intro_clear H0 accs H0'.
    elim_intro_clear H0' accsView H0.
    elim_intro_clear H0 accsLinkedToUser H0'.
    elim_intro_clear H0' accsNewView H0.
    elim_intro_clear H0 accView H1.

    elim_intro_clear H1 env_m H1'.
    elim_intro_clear H1' network_m H1.
    elim_intro_clear H1 accsView_eq H1'.
    elim_intro_clear H1' accView_in H1.
    elim_intro_clear H1 accView_user H1'.
    elim_intro_clear H1' accView_service H1.
    elim_intro_clear H1 accs_mac H1'.
    elim_intro_clear H1' accsLinked_eq H1.
    elim_intro_clear H1 accsNewView_eq H1'.
    elim_intro_clear H1' newMacView_eq env_a'.

    unfold valid_attacker_ii in validAttackerII.
    elim (validAttackerII m0 p0).
    intros MAC IH.
    elim_intro_clear IH env_MAC path_MAC.
    - case (idMachine_eq m0 m); intro eq_m0.
      -- exists newMacView.
         split.
         --- rewrite env_a'.
             unfold modify_machine.
             case (idMachine_eq m0 m); intros.
             ---- reflexivity.
             ---- contradiction.
         --- unfold registered_paths.
             rewrite newMacView_eq.
             simpl.
             assert (macView = MAC).
             ---- apply (enviroment_map_image (enviroment a) m macView MAC).
                  ----- exact env_m.
                  ----- rewrite <- eq_m0. exact env_MAC.
             ---- unfold registered_paths in path_MAC.
                  rewrite <- H2 in path_MAC.
                  exact path_MAC.
      -- exists MAC.
         rewrite (enviroment_eq (enviroment a) (enviroment a') m0 m newMacView).
         --- split.
             ---- exact env_MAC.
             ---- exact path_MAC.
         --- exact eq_m0.
         --- exact env_a'.
    - rewrite Hsecrets in H_secrets_a'.
      exact H_secrets_a'.
  Qed.