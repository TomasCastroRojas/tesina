Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.
Require Import Technique.TechniqueOneStep.

Require Import Invariant.AuxLemmas.AuxLemmas.
Require Import Invariant.AuxTactics.


Section AttackerInvariant.
  
  Theorem one_step_preserves_valid_attacker_i : forall (a a' : Attacker) (t : Technique) (n: network_map),
      one_step a t n a' -> valid_attacker_i a'.
  Proof.
    admit.
  Admitted.
      
  Theorem one_step_preserves_prop_ii : forall (a a' : Attacker) (t : Technique) (n: network_map),
      one_step a t n a' -> valid_attacker_ii a'.
  Proof.
    admit.
  Admitted.
  Theorem one_step_preserves_prop_iii : forall (a a' : Attacker) (t : Technique) (n: network_map),
      one_step a t n a' -> valid_attacker_iii a'.
  Proof.
    admit.
  Admitted.
  Theorem one_step_preserves_valid_attacker : forall (a a' : Attacker) (t : Technique) (n: network_map),
      one_step a t n a' -> valid_attacker a' n.
  Proof.
    admit.
  Admitted.
End AttackerInvariant.