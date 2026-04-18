Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineAuxFunctions.
Require Import Machine.MachineView.
Require Import Machine.MachineValid.

(* ===== Lemas sobre cuentas (addAccount / oplusAccounts) ===== *)

  (* addAccount siempre incluye la cuenta agregada en el resultado *)
  Lemma member_addAccount : forall (a: Account) (l: list Account),
      In a (addAccount a l) <-> True.
  Proof.
    intros.
    induction l; simpl; split.
    - auto.
    - auto.
    - auto.
    - intro.
      destruct a as [u s k p].
      destruct a0 as [u0 s0 k0 p0].
      simpl.
      case (idUser_eq u u0); intro.
      + destruct s0 as [s0' |].
        * destruct s as [s_val |].
          { case (idService_eq s_val s0'); intro.
            - simpl. left. reflexivity.
            - simpl. right. apply IHl. auto.
          }
          { simpl. right. apply IHl. auto. }
        * simpl. left. reflexivity.
      + simpl. right. apply IHl. auto.
  Qed.

  (* Si a pertenece a addAccount a' l, entonces a' = a o a ya estaba en l *)
  Lemma member_addAccount_simpl : forall (a a': Account) (l: list Account),
      In a (addAccount a' l) -> a' = a \/ In a l.
  Proof.
    intros a a'.
    induction l as [| acc' accs IH].

    - simpl.
      intros [H | []].
      left. exact H.

    - destruct a' as [u' s' k' p'].
      destruct acc' as [u0 s0 k0 p0].
      simpl.
      destruct (idUser_eq u' u0) as [Heq_u | Hneq_u].

      + destruct s0 as [s0' |].
        * destruct s' as [s_val |].
          { destruct (idService_eq s_val s0') as [Heq_s | Hneq_s]; simpl.
            - intros [H | H].
              ++ left. exact H.
              ++ right. right. exact H.
            - intros [H | H].
              ++ right. left. exact H.
              ++ apply IH in H. destruct H as [H | H].
                 ** left. exact H.
                 ** right. right. exact H.
          }
          { simpl. intros [H | H].
            - right. left. exact H.
            - apply IH in H. destruct H as [H | H].
              ++ left. exact H.
              ++ right. right. exact H.
          }
        * simpl. intros [H | H].
          { left. exact H. }
          { right. right. exact H. }

      + simpl. intros [H | H].
        * right. left. exact H.
        * apply IH in H. destruct H as [H | H].
          { left. exact H. }
          { right. right. exact H. }
  Qed.

  (* Si los usuarios de a y a' son distintos, addAccount preserva la pertenencia de a *)
  Lemma addAccount_preserves_membership_when_neq : forall (a a': Account) (l: list Account),
    (account_user a <> account_user a') -> In a l -> In a (addAccount a' l).
  Proof.
    intros a a'.
    induction l as [| acc accs IH].
    - intros. simpl. auto.
    - intros Hneq Hin.
      simpl in *.
      destruct (idUser_eq (account_user a') (account_user acc)) as [Heq_u | Hneq_u].
      + destruct Hin as [Heq | Hin'].
        * exfalso. apply Hneq. rewrite <- Heq. symmetry. exact Heq_u.
        * destruct (account_service acc) as [s0' |].
          { destruct (account_service a') as [s_val |].
            - destruct (idService_eq s_val s0') as [Heq_s | Hneq_s]; simpl.
              ++ right. exact Hin'.
              ++ right. apply IH; assumption.
            - simpl. right. apply IH; assumption.
          }
          { simpl. right. exact Hin'. }
      + simpl. destruct Hin as [Heq | Hin'].
        * left. exact Heq.
        * right. apply IH; assumption.
  Qed.

  (* addAccount preserva la existencia de una cuenta con usuario u en la lista *)
  Lemma addAccount_preserves_registered_user : forall (acc: Account) (u: idUser) (accs: list Account),
    (exists a, account_user a = u /\ In a accs) -> (exists a, account_user a = u /\ In a (addAccount acc accs)).
  Proof.
    intros acc u accs [a [Huser Hin]].
    destruct (idUser_eq (account_user acc) u) as [Heq_u | Hneq_u].
    - exists acc. split.
      + exact Heq_u.
      + apply member_addAccount. exact I.
    - exists a. split.
      + exact Huser.
      + apply addAccount_preserves_membership_when_neq.
        * intro Hcontra. apply Hneq_u. rewrite <- Hcontra. exact Huser.
        * exact Hin.
  Qed.

  (* oplusAccounts preserva la existencia de una cuenta con usuario u en el destino *)
  Lemma oplusAccounts_preserves_registered_user : forall (source dest: list Account) (u: idUser),
    (exists a, account_user a = u /\ In a dest) -> (exists a, account_user a = u /\ In a (oplusAccounts source dest)).
  Proof.
    intros source.
    induction source as [| acc source' IH].
    - intros dest u H. simpl. exact H.
    - intros dest u H. simpl. apply IH. apply addAccount_preserves_registered_user. exact H.
  Qed.

  (* Todo elemento de oplusAccounts proviene de source o de dest *)
  Lemma member_oplusAccounts_simpl : forall (a: Account) (source dest: list Account),
      In a (oplusAccounts source dest) -> In a source \/ In a dest.
  Proof.
    intros a source.
    induction source as [| acc source' IH].
    - intros dest H. simpl in H. right. exact H.
    - intros dest H. simpl in H.
      apply IH in H. destruct H as [H | H].
      + left. right. exact H.
      + apply member_addAccount_simpl in H. destruct H as [H | H].
        * left. left. exact H.
        * right. exact H.
  Qed.

   (* ===== Lemas sobre consultas de cuentas (get_accounts_linked_service_with_key) ===== *)

  (* Toda cuenta devuelta por get_accounts_linked_service_with_key pertenece a la lista original *)
  Lemma get_accounts_linked_service_with_key_in : forall (u: idUser) (s: idService) (l: list Account) (a: Account),
      In a (get_accounts_linked_service_with_key u s l) -> In a l.
  Proof.
    intros u s.
    induction l as [| acc l' IH].
    - intros a H. simpl in H. contradiction.
    - intros a H. simpl in H.
      destruct (account_service acc) eqn:Hserv.
      + destruct (idUser_eq u (account_user acc)) as [Heq_u | Hneq_u];
        destruct (idService_eq s i) as [Heq_s | Hneq_s].
        * simpl in H. destruct H as [H | H].
          { left. exact H. }
          { right. apply IH. exact H. }
        * right. apply IH. exact H.
        * right. apply IH. exact H.
        * right. apply IH. exact H.
      + right. apply IH. exact H.
  Qed.

  (* Toda cuenta devuelta por get_accounts_linked_service_with_key tiene account_service = Some s *)
  Lemma get_accounts_linked_service_with_key_service : forall (u: idUser) (s: idService) (l: list Account) (a: Account),
      In a (get_accounts_linked_service_with_key u s l) -> account_service a = Some s.
  Proof.
    intros u s.
    induction l as [| acc l' IH].
    - intros a H. simpl in H. contradiction.
    - intros a H. simpl in H.
      destruct (account_service acc) eqn:Hserv.
      + destruct (idUser_eq u (account_user acc)) as [Heq_u | Hneq_u];
        destruct (idService_eq s i) as [Heq_s | Hneq_s].
        * simpl in H. destruct H as [H | H].
          { rewrite <- H. rewrite Heq_s. exact Hserv. }
          { apply IH. exact H. }
        * apply IH. exact H.
        * apply IH. exact H.
        * apply IH. exact H.
      + apply IH. exact H.
  Qed.

  (* Toda cuenta devuelta por get_accounts_linked_service_without_key es una vista parcial
     (account_view) de alguna cuenta original en la lista. Las cuentas devueltas son sinteticas
     (account_key = None), por lo que no pertenecen a la lista original, pero comparten usuario,
     servicio y privilegio con una cuenta de la lista. *)
  Lemma get_accounts_linked_service_without_key_view : forall (u: idUser) (s: idService) (l: list Account) (b: Account),
      In b (get_accounts_linked_service_without_key u s l) ->
      exists a, In a l /\ account_view b a.
  Proof.
    intros u s.
    induction l as [| acc l' IH].
    - intros b H. simpl in H. contradiction.
    - intros b H. simpl in H.
      destruct (account_service acc) as [s_acc |] eqn:Hserv.
      + destruct (idUser_eq u (account_user acc)) as [Heq_u | Hneq_u];
        destruct (idService_eq s s_acc) as [Heq_s | Hneq_s].
        * apply IH in H. destruct H as [a [Hin Hview]].
          exists a. split; [right; exact Hin | exact Hview].
        * apply IH in H. destruct H as [a [Hin Hview]].
          exists a. split; [right; exact Hin | exact Hview].
        * simpl in H. destruct H as [Heq_b | Hin_rec].
          -- exists acc. split.
             ++ left. reflexivity.
             ++ unfold account_view. rewrite <- Heq_b. simpl.
                split; [reflexivity |].
                split; [right; rewrite Hserv; rewrite Heq_s; reflexivity |].
                split; [left; reflexivity | right; reflexivity].
          -- apply IH in Hin_rec. destruct Hin_rec as [a [Hin Hview]].
             exists a. split; [right; exact Hin | exact Hview].
        * apply IH in H. destruct H as [a [Hin Hview]].
          exists a. split; [right; exact Hin | exact Hview].
      + apply IH in H. destruct H as [a [Hin Hview]].
        exists a. split; [right; exact Hin | exact Hview].
  Qed.

  (* Toda cuenta devuelta por get_accounts_linked_service_without_key tiene account_service = Some s.
     Las cuentas devueltas son sinteticas: se construyen con service = Some s explicitamente. *)
  Lemma get_accounts_linked_service_without_key_service : forall (u: idUser) (s: idService) (l: list Account) (a: Account),
      In a (get_accounts_linked_service_without_key u s l) -> account_service a = Some s.
  Proof.
    intros u s.
    induction l as [| acc l' IH].
    - intros a H. simpl in H. contradiction.
    - intros a H. simpl in H.
      destruct (account_service acc) as [s_acc |] eqn:Hserv.
      + destruct (idUser_eq u (account_user acc)) as [Heq_u | Hneq_u];
        destruct (idService_eq s s_acc) as [Heq_s | Hneq_s].
        * apply IH. exact H.
        * apply IH. exact H.
        * simpl in H. destruct H as [Heq_a | Hin_rec].
          -- rewrite <- Heq_a. simpl. reflexivity.
          -- apply IH. exact Hin_rec.
        * apply IH. exact H.
      + apply IH. exact H.
  Qed.