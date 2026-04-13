Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmasEnviroment.
Require Import Invariant.AuxLemmas.AuxLemmasAccount.
Require Import Invariant.AuxTactics.

Lemma one_step_unsecured_credentials_preserves_valid_attacker_i : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m : idMachine) (u : idUser) (s: idService),
      valid_concrete_network n -> Pre a (Unsecured_Credentials m u s) -> Post a (Unsecured_Credentials m u s) n a' -> valid_attacker_i a'.
  Proof.
    intros a a' network validAttacker m u s validNetwork pre post.
    unfold valid_attacker_i.
    intros m0 u0 H_known_machines_a'.
    unfold valid_attacker in validAttacker.
    elim validAttacker.
    intros validAttackerI validAttackerII_III.
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


    unfold valid_attacker_i in validAttackerI.
    rewrite H in H_known_machines_a'.

    elim (validAttackerI m0 u0).
    intros MAC IH.
    elim_intro_clear IH env_MAC users_MAC.
    - case (idMachine_eq m0 m); intro eq_m0.
      -- exists newMacView.
         split.
         --- rewrite env_a'.
             unfold modify_machine.
             case (idMachine_eq m0 m); intros.
             ---- reflexivity.
             ---- contradiction.
         --- unfold registered_users.
             rewrite newMacView_eq.
             simpl.
             assert (macView = MAC).
             ---- apply (enviroment_map_image (enviroment a) m macView MAC).
                  ----- exact env_m.
                  ----- rewrite <- eq_m0. exact env_MAC.
             ---- rewrite <- H0 in users_MAC.
                  unfold registered_users in users_MAC.
                  rewrite accsNewView_eq.
                  apply oplusAccounts_preserves_registered_user.
                  rewrite <- accsView_eq.
                  exact users_MAC.
      -- exists MAC.
         rewrite (enviroment_eq (enviroment a) (enviroment a') m0 m newMacView).
         --- split.
             ---- exact env_MAC.
             ---- exact users_MAC.
         --- exact eq_m0.
         --- exact env_a'.
    - exact H_known_machines_a'.
  Qed.