Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineAuxFunctions.

(* ===== Lemas sobre vecinos (addNeighbour / oplusNeighbours) ===== *)

  (* Si n1 pertenece a addNeighbour n2 l, entonces n1 = n2 o n1 ya estaba en l *)
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

  (* Todo elemento de oplusNeighbours proviene de l1 o de l2 *)
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