Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.

Require Import Machine.Machine.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.


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

  Lemma and_cortocircuito : forall (A B: Prop), A \/ (B /\ False) <-> A \/ False.
  Proof.
    intros.
    split.
    - intro H.
      elim H.
      -- intro H1. left. exact H1.
      -- intro H1. elim H1. intros H2 H3. right. exact H3.
    - intro H.
      elim H.
      -- intro H1. left. exact H1.
      -- intro H1. contradiction.
  Qed.
  

  
  Lemma neq_tuple_first : forall (A B: Type) (a c: A) (b d: B),
   a <> c -> (a, b) <> (c, d).
  Proof.
    intros.
    unfold not.
    unfold not in H.
    intro eq_tuple.
    apply H.
    injection eq_tuple.
    intros.
    exact H1.
  Qed.

  Lemma neq_tuple_second : forall (A B: Type) (a c: A) (b d: B),
   b <> d -> (a, b) <> (c, d).
  Proof.
    intros.
    unfold not.
    unfold not in H.
    intro eq_tuple.
    apply H.
    injection eq_tuple.
    intros.
    exact H0.
  Qed.

  Lemma neq_tuple1 : forall (A B: Type) (a c: A) (b d: B),
   a <> c \/ b <> d -> (a, b) <> (c, d).
  Proof.
    intros.
    elim H.
    - apply neq_tuple_first.
    - apply neq_tuple_second.
  Qed.
  
  Lemma neq_tuple_discard : forall (A B: Type) (a c: A) (b d: B),
   (a, b) <> (c, d) -> a = c -> b <> d.
  Proof.
  Admitted.

  Lemma neq_tuple2 : forall (A B: Type) (a c: A) (b d: B),
   (a, b) <> (c, d) -> a <> c \/ b <> d.
  Proof.
    intros.
    elim (classic (a<>c)).
    - intro. left. assumption.
    - intro. right. unfold not in H0. apply (neq_tuple_discard A B a c b d). exact H. apply NNPP in H0. exact H0.
  Qed.

  Lemma neq_tuple : forall (A B: Type) (a c: A) (b d: B),
   (a, b) <> (c, d) <-> a <> c \/ b <> d.
  Proof.
    intros.
    split.
    - apply neq_tuple2.
    - apply neq_tuple1.
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

  Lemma member_addAccount : forall (a: Account) (l: list Account),
      In a (addAccount a l) <-> True.
  Proof.
    intros.
    induction l; simpl; split.
    - auto.
    - auto.
    - destruct a as [u s k p].
      destruct a0 as [u0 s0 k0 p0].
      simpl.
      case (idUser_eq u u0); case (idService_eq s s0); intros; auto.
    - intro.
      destruct a as [u s k p].
      destruct a0 as [u0 s0 k0 p0].
      simpl.
      case (idUser_eq u u0); intro.
      -- case (idService_eq s s0); intros.
         --- simpl.
             left.
             reflexivity.
         --- simpl.
             right.
             apply IHl. auto.
      -- simpl.
         right.
         apply IHl. auto.
  Qed.

  Lemma member_addAccount_simpl : forall (a a': Account) (l: list Account),
      In a (addAccount a' l) <-> a' = a \/ In a l.
  Proof.
    (* TODO *)
  Admitted.

  Lemma enviroment_eq : forall (env env': network_map) (m m': idMachine) (mac: Machine),
    m <> m' -> env' = modify_machine m' mac env -> env' m = env m.
  Proof.
    intros.
    rewrite H0.
    unfold modify_machine.
    case (idMachine_eq m m').
    - intro. contradiction.
    - intro. reflexivity.
  Qed.

  Lemma option_eq : forall (A: Type) (a a': A), Some a = Some a' -> a = a'.
  Proof.
    intros.
    congruence.
  Qed.
  
  Lemma enviroment_map_image : forall (env: network_map) (m: idMachine) (mac1 mac2: Machine),
    env m = Some mac1 -> env m = Some mac2 -> mac1 = mac2.
  Proof.
    intros.
    apply (option_eq Machine).
    rewrite H in H0.
    exact H0.
  Qed.

  
      

       