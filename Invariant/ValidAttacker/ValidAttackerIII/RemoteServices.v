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

Lemma one_step_remote_services_preserves_valid_attacker_iii : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m m': idMachine) (u u': idUser) (k': key) (s': idService),
      valid_concrete_network n -> Pre a (Remote_Services m u m' u' k' s') -> Post a (Remote_Services m u m' u' k' s') n a' -> valid_attacker_iii a'.
  Proof.
    intros a a' network validAttacker m m' u u' k' s' validNetwork pre post.
    unfold valid_attacker_iii.
    unfold valid_network.
    unfold valid_attacker in validAttacker.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttacker'''.
    destruct pre; destruct post.
    elim H2; intros secrets env; clear H2.
    unfold valid_attacker_iii in validAttackerIII.
    unfold valid_network in validAttackerIII.
    rewrite env.
    exact validAttackerIII.
  Qed.