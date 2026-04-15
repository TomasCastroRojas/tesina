Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Inductive one_step : Attacker -> Technique -> (network_map) -> Attacker -> Prop :=
      | onestep : forall (a: Attacker) (t: Technique) (network: network_map) (a': Attacker),
                    valid_concrete_network network -> valid_attacker a network -> Pre a t -> Post a t network a' -> one_step a t network a'.

(* Clausura transitiva de one_step: el atacante puede llegar de estado a a estado a'
   en cero o mas pasos de ejecucion de tecnicas *)
Inductive multi_step : Attacker -> network_map -> Attacker -> Prop :=
  | multi_step_refl : forall (a: Attacker) (n: network_map),
      multi_step a n a
  | multi_step_trans : forall (a a' a'': Attacker) (t: Technique) (n: network_map),
      one_step a t n a' ->
      multi_step a' n a'' ->
      multi_step a n a''.