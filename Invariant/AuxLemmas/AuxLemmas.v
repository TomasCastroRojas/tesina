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
      In a (addAccount a' l) -> a' = a \/ In a l.
  Proof.
    intros a a'.
  induction l as [| acc' accs IH].

  - simpl.
    intros [H | []].
    left.  exact H.

  - destruct a'   as [u' s' k' p'].
    destruct acc' as [u0 s0 k0 p0].
    simpl.
    destruct (idUser_eq u' u0) as [Heq_u | Hneq_u];
    destruct (idService_eq s' s0) as [Heq_s | Hneq_s]; simpl.

    + intros [H | H].
      * left. exact H.
      * right. right. exact H. 

    + intros [H | H].
      * right. left. exact H.
      * apply IH in H.
        destruct H as [H | H].
        -- left. exact H.
        -- right. right. exact H.

    + intros [H | H].
      * right. left. exact H.
      * apply IH in H.
        destruct H as [H | H].
        -- left. exact H.
        -- right. right. exact H.

    + intros [H | H].
      * right. left. exact H.
      * apply IH in H.
        destruct H as [H | H].
        -- left. exact H.
        -- right. right. exact H.
  Qed.

  Lemma addAccount_preserves_membership_when_neq : forall (a a': Account) (l: list Account),
    (account_user a <> account_user a') -> In a l -> In a (addAccount a' l).
  Proof.
    intros a a'.
    induction l as [| acc accs IH].
    - intros. simpl. auto.
    - intros Hneq Hin.
      simpl in *.
      destruct (idUser_eq (account_user a') (account_user acc)) as [ Heq_u | Hneq_u];
      destruct (idService_eq (account_service a') (account_service acc)) as [ Heq_s | Hneq_s];
      simpl; destruct Hin as [ Heq | Hin'].
      -- exfalso. apply Hneq. rewrite <- Heq. symmetry. exact Heq_u.
      -- right. exact Hin'.
      -- left. exact Heq.
      -- right. apply IH; assumption.
      -- left. exact Heq.
      -- right. apply IH; assumption.
      -- left. exact Heq.
      -- right. apply IH; assumption.
  Qed.

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

  Lemma enviroment_simpl : forall (env env': network_map) (m m': idMachine) (m0 mac: Machine),
    m = m' -> env' = (modify_machine m' mac env) -> env' m = Some m0 -> m0 = mac.
  Proof.
    intros.
    assert (env' m = Some mac).
    rewrite H0.
    unfold modify_machine.
    case (idMachine_eq m m'); intro eq_m.
    - reflexivity.
    - contradiction.
    - rewrite H1 in H2.
    apply option_eq.
    exact H2.
  Qed.


  Lemma addService_preserves_membership : forall (a b: Service) (l: list Service),
    In a l -> In a (addService b l).
  Proof.
    intros.
    induction l; simpl.
    - auto.
    - case (idService_eq (service_value b) (service_value a0)); intros eq_serv.
      -- exact H.
      -- simpl in *.
         elim H; intro H'.
         --- left. exact H'.
         --- right. apply IHl. exact H'.
  Qed.

  
  Lemma oplusServices_preserves_membership : forall (s: Service) (l1 l2: list Service),
    In s l1 -> In s (oplusServices l1 l2).
  Proof.
    intros s l1 l2.
    revert l1.
    induction l2 as [| a l2' IH].
    - auto.
    - intros l H.
      simpl.
      apply IH.
      apply addService_preserves_membership.
      exact H.
  Qed.

  Lemma addNeighbour_membership : forall (n1 n2: idMachine) (l: list idMachine),
    In n1 (addNeighbour n2 l) -> n1 = n2 \/ In n1 l.
  Proof.
    intros n1 n2 l.
    induction l as [| n0 l' IH]; simpl.
    - intros [H | []]. left. symmetry. exact H.
    - case (idMachine_eq n2 n0); intros eq_n0 H; simpl in H.
      -- right. exact H.
      -- destruct H as [ Heq | Hin].
         --- right. left. exact Heq.
         --- destruct (IH Hin) as [ Heq | Hin'].
             ---- left. exact Heq.
             ---- right. right. exact Hin'.
  Qed.
  
  Lemma oplusNeighbours_membership : forall (m: idMachine) (l1 l2: list idMachine),
    In m (oplusNeighbours l1 l2) -> In m l1 \/ In m l2.
  Proof.
    intros m l1.
    induction l1 as [| m' l1' IH]; simpl in *; intros l2 H.
    - right. exact H.
    - apply IH in H.
      destruct H as [Hin | Hin_add].
      -- left. right. exact Hin.
      -- apply addNeighbour_membership in Hin_add.
         destruct Hin_add as [ Heq | Hin'].
         --- left. left. symmetry. exact Heq.
         --- right. exact Hin'.
  Qed.
  
      

       