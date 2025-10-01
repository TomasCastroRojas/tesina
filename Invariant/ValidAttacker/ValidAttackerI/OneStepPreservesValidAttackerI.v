Require Import Coq.Lists.List.

Require Import Tesina.Machine.Machine.
Require Import Tesina.Machine.MachineAuxFunctions.
Require Import Tesina.Attacker.Attacker.
Require Import Tesina.Technique.Technique.
Require Import Tesina.Technique.TechniquePreCondition.
Require Import Tesina.Technique.TechniquePostCondition.
Require Import Tesina.Technique.TechniqueOneStep.

Require Import Tesina.Invariant.AuxLemmas.AuxLemmas.
Require Import Tesina.Invariant.AuxTactics.

Require Import Tesina.Invariant.ValidAttacker.ValidAttackerI.RemoteServices.

Theorem one_step_preserves_valid_attacker_i : forall (a a' : Attacker) (t : Technique) (n: network_map),
      one_step a t n a' -> valid_attacker_i a' n.
  Proof.
    intros a a' t n onestep.
    destruct onestep.
    induction t; unfold valid_attacker in H0; unfold valid_network in H;
    unfold Pre in H1; unfold Post in H2; unfold valid_attacker_i; intros m' u' known_machines_a'.
    - apply (one_step_remote_services_preserves_valid_attacker_i a a' network H0 i i1 i0 i2 k i3); auto.
    
  Admitted.