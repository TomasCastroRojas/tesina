Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.
Require Import Technique.TechniqueOneStep.

Require Import Invariant.AuxLemmas.AuxLemmas.
Require Import Invariant.AuxTactics.

Require Import Invariant.ValidAttacker.ValidAttackerI.RemoteServices.
Require Import Invariant.ValidAttacker.ValidAttackerI.ExploitationRemoteServices.

Theorem one_step_preserves_valid_attacker_i : forall (a a' : Attacker) (t : Technique) (n: network_map),
      one_step a t n a' -> valid_attacker_i a'.
  Proof.
    intros a a' t n onestep.
    destruct onestep.
    induction t; unfold valid_attacker in H0; unfold valid_concrete_network in H;
    unfold Pre in H1; unfold Post in H2; unfold valid_attacker_i; intros m' u' known_machines_a'.
    - apply (one_step_remote_services_preserves_valid_attacker_i a a' network H0 i i1 i0 i2 k i3); auto.
    - apply (one_step_exploitation_remote_services_preserves_valid_attacker_i a a' network H0 i i1 i0 i2 i3); auto.
  Admitted.