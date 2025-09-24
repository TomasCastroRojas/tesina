Require Import Coq.Lists.List.

Require Import Tesina.Machine.Machine.
Require Import Tesina.Machine.MachineAuxFunctions.
Require Import Tesina.Attacker.Attacker.


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
  
  Lemma disjuction_commutative : forall (A B C: Prop), (A \/ B \/ C) <-> (B \/ A \/ C).
  Proof.
    intros.
    split; intro H; elim H; intro H'.
    - right. left. exact H'.
    - elim H'; intro H''.
      -- left. exact H''.
      -- right. right. exact H''.
    - right. left. exact H'.
    - elim H'; intro H''.
      -- left. exact H''.
      -- right. right. exact H''.
  Qed.
  
  Lemma member_add_machine_user : forall (m m': idMachine) (u u':idUser) (l: list (idMachine * idUser)),
    In (m,u) (add_machine_user (m', u') l) <-> ((m', u') = (m, u) \/ In (m, u) l).
  Proof.
    induction l.
    - simpl. reflexivity.
    - destruct a as [m0 u0].
      simpl.
      case (idMachine_eq m' m0).
      -- case (idUser_eq u' u0); intros Heq_u Heq_m; simpl; split; intro H; elim H; intro H'.
         --- left. rewrite Heq_u. rewrite Heq_m. exact H'.
         --- right. right. exact H'.
         --- left. rewrite <- Heq_u. rewrite <- Heq_m. exact H'.
         --- exact H'.
         --- right. left. exact H'.
         --- apply disjuction_commutative. right. apply IHl. exact H'.
         --- right. apply IHl. left. exact H'.
         --- elim H'; intros H''.
             ---- left. exact H''.
             ---- right. apply IHl. right. exact H''.
     -- intro neq_m.
        simpl.
        split; intro H; [  | apply disjuction_commutative in H]; elim H; intro H'.
        --- right. left. exact H'.
        --- apply disjuction_commutative. right. apply IHl. exact H'.
        --- left. exact H'.
        --- right. apply IHl. exact H'.
  Qed.