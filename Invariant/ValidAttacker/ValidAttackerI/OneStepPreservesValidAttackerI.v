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

Theorem one_step_preserves_valid_attacker_i : forall (a a' : Attacker) (t : Technique) (n: network_map),
      one_step a t n a' -> valid_attacker_i a' n.
  Proof.
    admit.
  Admitted.