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

Lemma one_step_remote_services_preserves_valid_attacker_i : forall (m m': idMachine) (u u': idUser) (k: key) (s: idService) (a a' : Attacker) (n: network_map),
      one_step a (Remote_Services m u m' u' k s) n a' -> valid_attacker_i a' n.
  Proof.
    intros.
    admit.
  Admitted.