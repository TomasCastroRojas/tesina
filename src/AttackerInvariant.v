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
  
  Theorem one_step_preserves_prop_i : forall (a a' : Attacker) (t : Technique) (n: network_map),
      one_step a t n a' -> valid_attacker_i a'.
  Proof.
    intros a a' t n onestep.
    destruct onestep.
    induction t; unfold valid_attacker in H0; unfold valid_network in H;
    unfold Pre in H1; unfold Post in H2; unfold valid_attacker_i; intros m' u' known_machines_a'.
    - elim H0.
      intros valid_a H0'.
      unfold valid_attacker_i in valid_a.
      elim H2.
      intros new_machines H2'.
      elim H2'.
      intros secrets env.
      clear H H2 H2' H0 H0'.
      rewrite env.
      rewrite new_machines in known_machines_a'.
      apply member_add_machine_user in known_machines_a'.
      elim known_machines_a'.
      -- intro eq.
         elim H1; intros H4 H1'; clear H1.
         elim H1'; intros H5 H1''; clear H1'.
         elim H1''; intros accs H1'''; clear H1''.
         elim H1'''; intros acc H1''''; clear H1'''.
         elim H1''''; intros mac' H6; clear H1''''.
         elim H6; intros env_mac' H7.
         elim H7; intros accs_mac' H8.
         clear H4 H5 H6 H7 H8.
         exists mac'.
         injection eq.
         intros equ' eqm'.
         split.
         --- rewrite <- eqm'. exact env_mac'.
         --- rewrite <- equ'. unfold registered_users. exists accs. exact accs_mac'.
      -- intro known_machines_a.
         apply valid_a.
         exact known_machines_a.
    - elim H0; intros valid_a H0'; clear H0 H0'.
      unfold valid_attacker_i in valid_a.
      
      elim H1; intros H3 H1'; clear H1.
      elim H1'; intros H4 H1''; clear H1'.
      elim H1''; intros serv H1'''; clear H1''.
      elim H1'''; intros mac' H5; clear H1'''.
      elim H5; intros exists_mac H5'; clear H3 H4 H5 H5'.
      
      elim H2; intros secrets H2'; clear H2.
      elim H2'; intros env H2''; clear H2'.
      elim H2''; intros mac'' H2'''; clear H2''.
      elim H2'''; intros serv' H2''''; clear H2'''.
      elim H2''''; intros acss H2'''''; clear H2''''.
      elim H2'''''; intros acc H2''''''; clear H2'''''.
      elim H2''''''; intros user H3; clear H2''''''.
      elim H3; intros net_i1 H3'; clear H3.
      elim H3'; intros H4 H3''; clear H3'.
      (* 
      TODO: Esta técnica no cumple la propiedad porque el usuario agregado
      es de la maquina física y no la vista parcial. Tampoco es agregado a la vista parcial.
      Caso extraño porque las demas técnicas requieren conocer una Account para ejecutarse
      *)
      admit.
    - elim H0; intros valid_a H0'; clear H0 H0'.
      unfold valid_attacker_i in valid_a.
      
      elim H2; intros eq_known_machines H2'; clear H2.
      elim H2'; intros secrets H2''; clear H2'.
      elim H2''; intros macView H2'''; clear H2''.
      elim H2'''; intros mac H2''''; clear H2'''.
      elim H2''''; intros accs H2'''''; clear H2''''.
      elim H2'''''; intros accsView H3; clear H2'''''.
      elim H3; intros exists_macView H3'; clear H3.
      elim H3'; intros exists_net H3''; clear H3'.
      elim H3''; intros exists_user H3'''; clear H3''.
      elim H3'''; intros exists_net_user env; clear H3'''.
      clear H secrets exists_net exists_net_user.
      
      rewrite env.
      unfold modify_machine.
      case (idMachine_eq m' i).
      -- case (idUser_eq u' i0).
         --- intros.
             unfold registered_users.
             exists (machine (machine_services macView)
                             (modify_accounts i0 (oplusAccounts (get_accounts_linked_service_with_key i1 accs) accsView) (machine_accounts macView))
                             (machine_fileSystem macView)
                             (machine_neighbours macView)).
             simpl.
             split.
             ---- reflexivity.
             ---- exists (oplusAccounts (get_accounts_linked_service_with_key i1 accs) accsView).
                  unfold modify_accounts.
                  case (idUser_eq u' i0).
                  ----- intro; reflexivity.
                  ----- intro. contradiction.
         --- intros.
             exists (machine (machine_services macView)
                         (modify_accounts i0 (oplusAccounts (get_accounts_linked_service_with_key i1 accs) accsView) (machine_accounts macView))
                         (machine_fileSystem macView)
                         (machine_neighbours macView)).
             unfold registered_users.
             simpl.
             split.
             ---- reflexivity.
             ---- unfold modify_accounts.
                  case (idUser_eq u' i0).
                  ----- intro. contradiction.
                  ----- intro. admit.
      -- intro.
         apply valid_a.
         rewrite <- eq_known_machines.
         exact known_machines_a'.
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