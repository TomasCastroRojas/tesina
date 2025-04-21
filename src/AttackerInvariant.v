Require Import Coq.Lists.List.

Require Import Machine.
Require Import MachineAuxFunctions.
Require Import Attacker.
Require Import Technique.

Section AttackerInvariant.
  
  (* add_machine_user se 'comporta' como cons *)
  Lemma add_element_preserves_list : forall (a b: (idMachine * idUser)) (l: list (idMachine * idUser)),
    In a l -> In a (add_machine_user b l).
  Proof.
    intros a b l H.
    induction l.
    - simpl. auto.
    - destruct a as [m u].
      destruct b as [m' u'].
      destruct a0 as [m0 u0].
      simpl in |- *.
      case (idMachine_eq m' m0).
      -- case (idUser_eq u' u0).
         --- intro eq_u.
             intro eq_m.
             exact H.
         --- simpl in |- *.
             intros neq_u' eq_m'.
             simpl in H.
             elim H.
             ---- intro eq_a0_a.
                  left.
                  exact eq_a0_a.
             ---- intro HIn.
                  right.
                  apply IHl.
                  exact HIn.
     -- intro eq_m'.
        simpl.
        elim H.
        --- intro eq_m.
            left.
            exact eq_m.
        --- intro HIn.
            right.
            apply IHl.
            exact HIn.
  Qed.
  
  Theorem one_step_preserves_prop_i : forall (a a' : Attacker) (t : Technique) (n: network_map),
      one_step a t n a' -> valid_attacker_i a'.
  Proof.
    intros a a' t n onestep.
    destruct onestep.
    induction t; unfold valid_attacker in H0; unfold valid_network in H;
    unfold Pre in H1; unfold Post in H2; unfold valid_attacker_i.
    - clear H network.
      intros m' u' mac' known_machines_a'.
      elim H2; intros know_machines_a H2'; clear H2.
      elim H2'; intros secrets env; clear H2' secrets.
      elim H0; intros PropI H0'; clear H0 H0'.
      unfold valid_attacker_i in PropI.
      rewrite env.
      apply PropI.
      rewrite know_machines_a in known_machines_a'.
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
      one_step a t n a' -> valid_attacker a'.
  Proof.
    admit.
  Admitted.
End AttackerInvariant.