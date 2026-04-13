Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineAuxFunctions.
Require Import Invariant.AuxLemmas.AuxLemmasLogic.

(* ===== Lemas sobre servicios (addService / oplusServices) ===== *)

  (* addService preserva todos los servicios ya presentes en la lista *)
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

  (* Si s pertenece a addService s' l, entonces s' = s o s ya estaba en l *)
  Lemma addService_membership : forall (s s': Service) (l: list Service),
    In s (addService s' l) -> s' = s \/ In s l.
  Proof.
    intros s s' l.
    induction l as [| s0 l' IH]; simpl.
    - auto.
    - case (idService_eq (service_value s') (service_value s0)); intros eq_s0 H; simpl in *.
      -- right. exact H.
      -- apply disjuction_commutative.
         destruct H as [ Heq | Hin].
         --- left. exact Heq.
         --- right. apply IH. exact Hin.
  Qed.

  (* oplusServices preserva todos los servicios del primer argumento en el resultado *)
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

  (* Todo elemento de oplusServices proviene de l1 o de l2 *)
  Lemma oplusServices_membership : forall (s: Service) (l1 l2: list Service),
      In s (oplusServices l1 l2) -> In s l1 \/ In s l2.
  Proof.
    intros s l1 l2.
    revert l1.
    induction l2 as [| s' l2' IH]; intros l1 H.
    - auto.
    - apply IH in H.
      simpl.
      apply disjuction_commutative.
      apply or_assoc.
      destruct H as [ Hin_add | Hin_l2 ].
      -- left. apply addService_membership. exact Hin_add.
      -- right. exact Hin_l2.
  Qed.