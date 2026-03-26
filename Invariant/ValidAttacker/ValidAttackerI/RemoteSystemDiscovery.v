Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmas.
Require Import Invariant.AuxTactics.

Lemma one_step_remote_system_discovery_preserves_valid_attacker_i : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m : idMachine) (u : idUser),
      valid_concrete_network n -> Pre a (Remote_System_Discovery m u) -> Post a (Remote_System_Discovery m u) n a' -> valid_attacker_i a'.
  Proof.
    intros a a' network validAttacker m u validNetwork pre post.
    unfold valid_attacker_i.
    intros m0 u0 H_known_machines_a'.
    unfold valid_attacker in validAttacker.
    elim validAttacker.
    intros validAttackerI validAttackerII_III.
    unfold Pre in pre; destruct post.

    elim_intro_clear H0 Hsecrets H0'.
    elim_intro_clear H0' macView H0''.
    elim_intro_clear H0'' newMacView H0'''.
    elim_intro_clear H0''' mac H0''''.
    elim_intro_clear H0'''' newNeighbours H0'''''.
    elim_intro_clear H0''''' macNeighbours H1.

    elim_intro_clear H1 env_m H1'.
    elim_intro_clear H1' network_m H1''.
    elim_intro_clear H1'' macNeighbours_eq H1'''.
    elim_intro_clear H1''' macNeighbours_closure H1''''.
    elim_intro_clear H1'''' newNeighbours_eq H1'''''.
    elim_intro_clear H1''''' newMacView_eq env_a'.

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