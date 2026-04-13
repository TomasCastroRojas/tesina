Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineAuxFunctions.
Require Import Machine.MachineView.
Require Import Machine.MachineValid.

(* ===== Lemas sobre secretos (addSecret / oplusSecrets) ===== *)

  (* Si (m0,p0) pertenece a addSecret m p s, entonces (m0,p0) = (m,p) o ya estaba en s *)
  Lemma addSecret_membership : forall (m m0: idMachine) (p p0: path)
                                      (s: list (idMachine * path)),
    In (m0, p0) (addSecret m p s) -> (m0, p0) = (m, p) \/ In (m0, p0) s.
  Proof.
    intros m m0 p p0 s.
    induction s as [| [m' p'] s' IH].
    - simpl. intros [H | []]. left. symmetry. exact H.
    - simpl.
      case (idMachine_eq m m'); intro eq_m.
      + case (path_eq p p'); intro eq_p.
        * (* left, left: addSecret devuelve (m',p')::s' sin cambios *)
          intros H. right. exact H.
        * (* left, right: (m',p') :: addSecret m p s' *)
          simpl. intros [H | H].
          -- right. left. exact H.
          -- apply IH in H. destruct H as [H | H].
             ++ left. exact H.
             ++ right. right. exact H.
      + (* right, _: (m',p') :: addSecret m p s' *)
        simpl. intros [H | H].
        * right. left. exact H.
        * apply IH in H. destruct H as [H | H].
          -- left. exact H.
          -- right. right. exact H.
  Qed.

  (* Todo elemento de oplusSecrets proviene de s1 o de s2 *)
  Lemma oplusSecrets_membership : forall (m0: idMachine) (p0: path)
                                         (s1 s2: list (idMachine * path)),
    In (m0, p0) (oplusSecrets s1 s2) -> In (m0, p0) s1 \/ In (m0, p0) s2.
  Proof.
    intros m0 p0 s1 s2.
    revert s1.
    induction s2 as [| [m p] s2' IH]; intros s1 H.
    - left. exact H.
    - simpl in H.
      apply IH in H.
      destruct H as [H | H].
      + apply addSecret_membership in H.
        destruct H as [H | H].
        * right. left. rewrite <- H. reflexivity.
        * left. exact H.
      + right. right. exact H.
  Qed.