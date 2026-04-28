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

Lemma one_step_account_discovery_remote_preserves_valid_attacker_i : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m m': idMachine) (u u': idUser) (k' : option key) (s': idService),
      valid_concrete_network n -> Pre a (Account_Discovery_Remote m u m' u' k' s') -> Post a (Account_Discovery_Remote m u m' u' k' s') n a' -> valid_attacker_i a'.
  Proof.
    intros a a' network validAttacker m m' u u' k' s' validNetwork pre post.
    unfold valid_attacker_i.
    intros m0 u0 H_known_machines_a'.
    unfold valid_attacker in validAttacker.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    unfold Pre in pre; unfold Post in post.

    elim_intro_clear post known_machines_eq post'.
    elim_intro_clear post' secrets_eq post.
    elim_intro_clear post mastered_exploits_eq post'.
    elim_intro_clear post' mac post.
    elim_intro_clear post macView post'.
    elim_intro_clear post' newMacView post.
    elim_intro_clear post newAccountsView post'.
    elim_intro_clear post' accsLinkedToService post.
    elim_intro_clear post env_m post'.
    elim_intro_clear post' network_m post.
    elim_intro_clear post accsLinkedToService_eq post'.
    elim_intro_clear post' newAccountsView_eq post.
    elim_intro_clear post newMacView_eq env_a'.


    unfold valid_attacker_i in validAttackerI.
    rewrite known_machines_eq in H_known_machines_a'.

    elim (validAttackerI m0 u0).
    intros MAC IH.
    elim_intro_clear IH env_MAC users_MAC.
    - case (idMachine_eq m0 m'); intro eq_m0.
      -- exists newMacView.
         split.
         --- rewrite env_a'.
             unfold modify_machine.
             case (idMachine_eq m0 m'); intros.
             ---- reflexivity.
             ---- contradiction.
         --- unfold registered_users.
             rewrite newMacView_eq.
             simpl.
             assert (macView = MAC).
             ---- apply (enviroment_map_image (enviroment a) m' macView MAC).
                  ----- exact env_m.
                  ----- rewrite <- eq_m0. exact env_MAC.
             ---- rewrite <- H in users_MAC.
                  unfold registered_users in users_MAC.
                  rewrite newAccountsView_eq.
                  apply oplusAccounts_preserves_registered_user.
                  exact users_MAC.
      -- exists MAC.
         rewrite (enviroment_eq (enviroment a) (enviroment a') m0 m' newMacView).
         --- split.
             ---- exact env_MAC.
             ---- exact users_MAC.
         --- exact eq_m0.
         --- exact env_a'.
    - exact H_known_machines_a'.
  Qed.