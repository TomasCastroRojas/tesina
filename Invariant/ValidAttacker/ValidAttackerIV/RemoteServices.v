Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxTactics.

Lemma one_step_remote_services_preserves_valid_attacker_iv : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m m': idMachine) (u u': idUser) (k': key) (s': idService),
      valid_concrete_network n -> Pre a (Remote_Services m u m' u' k' s') -> Post a (Remote_Services m u m' u' k' s') n a' -> valid_attacker_iv a' n.
  Proof.
    intros a a' network validAttacker m m' u u' k' s' validNetwork pre post.
    unfold valid_attacker_iv.
    unfold valid_attacker in validAttacker.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttackerIV.
    destruct pre; destruct post.
    elim H2; intros secrets H3; clear H2.
    elim H3; intros env mastered; clear H3.
    unfold valid_attacker_iv in validAttackerIV.
    rewrite env.
    exact validAttackerIV.
  Qed.