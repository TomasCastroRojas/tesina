Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineAuxFunctions.
Require Import Invariant.AuxLemmas.AuxLemmasLogic.


(* ===== Lemas sobre el entorno (modify_machine) ===== *)

  (* Si m <> m', modificar el entorno en m' no afecta la entrada de m *)
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

  (* El entorno es una funcion determinista: el mismo identificador siempre devuelve la misma maquina *)
  Lemma enviroment_map_image : forall (env: network_map) (m: idMachine) (mac1 mac2: Machine),
    env m = Some mac1 -> env m = Some mac2 -> mac1 = mac2.
  Proof.
    intros.
    apply (option_eq Machine).
    rewrite H in H0.
    exact H0.
  Qed.

  (* Si m = m', el entorno modificado en m' devuelve exactamente mac *)
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