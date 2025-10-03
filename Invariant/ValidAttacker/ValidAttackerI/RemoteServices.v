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

Lemma one_step_remote_services_preserves_valid_attacker_i : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m m': idMachine) (u u': idUser) (k': key) (s': idService),
      valid_network n -> Pre a (Remote_Services m u m' u' k' s') -> Post a (Remote_Services m u m' u' k' s') n a' -> valid_attacker_i a'.
  Proof.
    intros a a' network validAttacker m m' u u' k' s' validNetwork pre post.
    unfold valid_attacker_i.
    intros m0 u0 known_machines_a'.
    unfold valid_attacker in validAttacker.
    elim validAttacker.
    intros validAttackerI validAttackerII_III.
    destruct pre; destruct post.
    elim H2; intros secrets env; clear H2.
    rewrite H1 in known_machines_a'.
    rewrite env.
    apply member_add_machine_user in known_machines_a'.
    elim known_machines_a'.
    - intro eq.
      elim_intro_clear H0 H4 H0'.
      elim_intro_clear H0' accs H0''.
      elim_intro_clear H0'' acc H0'''.
      elim_intro_clear H0''' mac' H6.
      elim_intro_clear H6 env_mac' H7.
      elim_intro_clear H7 accs_mac' H8.
      exists mac'.
      injection eq.
      intros equ' eqm'.
      split.
      -- rewrite <- eqm'. exact env_mac'.
      -- rewrite <- equ'. unfold registered_users. exists accs. exact accs_mac'.
    - intro known_machines_a.
      unfold valid_attacker_i in validAttackerI.
      apply validAttackerI.
      exact known_machines_a.
  Qed.