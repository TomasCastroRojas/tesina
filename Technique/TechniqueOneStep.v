Require Import Coq.Lists.List.

Require Import Tesina.Machine.Machine.
Require Import Tesina.Attacker.Attacker.
Require Import Tesina.Technique.Technique.
Require Import Tesina.Technique.TechniquePreCondition.
Require Import Tesina.Technique.TechniquePostCondition.

Inductive one_step : Attacker -> Technique -> (idMachine -> option Machine) -> Attacker -> Prop :=
      | onestep : forall (a: Attacker) (t: Technique) (network: idMachine -> option Machine) (a': Attacker),
                    valid_network network -> valid_attacker a network -> Pre a t -> Post a t network a' -> one_step a t network a'.
                    