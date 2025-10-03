Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.
Require Import Technique.TechniqueOneStep.

Require Import Invariant.ValidAttacker.ValidAttackerI.OneStepPreservesValidAttackerI.
Require Import Invariant.ValidAttacker.ValidAttackerII.OneStepPreservesValidAttackerII.
Require Import Invariant.ValidAttacker.ValidAttackerIII.OneStepPreservesValidAttackerIII.
Require Import Invariant.ValidAttacker.ValidAttackerIV.OneStepPreservesValidAttackerIV.

Theorem one_step_preserves_valid_attacker : forall (a a' : Attacker) (t : Technique) (n: network_map),
      one_step a t n a' -> valid_attacker a' n.
  Proof.
    intros a a' t n onestep.
    unfold valid_attacker.
    split; [  | split]; [ | | split].
    - apply (one_step_preserves_valid_attacker_i a a' t n); auto.
    - apply (one_step_preserves_valid_attacker_ii a a' t n); auto.
    - apply (one_step_preserves_valid_attacker_iii a a' t n); auto.
    - apply (one_step_preserves_valid_attacker_iv a a' t n); auto.
  Qed.