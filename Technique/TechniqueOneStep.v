Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Inductive one_step : Attacker -> Technique -> (idMachine -> option Machine) -> Attacker -> Prop :=
      | onestep : forall (a: Attacker) (t: Technique) (network: idMachine -> option Machine) (a': Attacker),
                    valid_network network -> valid_attacker a network -> Pre a t -> Post a t network a' -> one_step a t network a'.
                    