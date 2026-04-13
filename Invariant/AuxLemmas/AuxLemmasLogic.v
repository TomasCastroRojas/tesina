Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineAuxFunctions.
Require Import Machine.MachineView.
Require Import Machine.MachineValid.
Require Import Attacker.Attacker.


  (* ===== Lemas logicos generales ===== *)

  (* Conmutatividad parcial de la disyuncion: reorganiza los dos primeros terminos de (A \/ B \/ C) *)
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

  (* Asociatividad de la disyuncion: reordena los parentesis de una triple disyuncion *)
  Lemma or_assoc : forall A B C : Prop, (A \/ (B \/ C)) <-> ((A \/ B) \/ C).
  Proof.
    intros.
    split; intro H.
    - destruct H as [ H | H].
      -- left. left. exact H.
      -- destruct H as [ H | H ].
         --- left. right. exact H.
         --- right. exact H.
    - destruct H as [ H | H].
      -- destruct H as [ H | H ].
         --- left. exact H.
         --- right. left. exact H.
      -- right. right. exact H.
  Qed.

  (* Inyectividad de Some: si Some a = Some a' entonces a = a' *)
  Lemma option_eq : forall (A: Type) (a a': A), Some a = Some a' -> a = a'.
  Proof.
    intros.
    congruence.
  Qed.
