Require Import Coq.Lists.List.
Require Import Machine.

Section muSE.

  Record Attacker : Set :=
    attacker {
      known_machines : list (idMachine * idUser); (* Conjunto de acceso a máquinas *)
      secrets : list (idMachine * path); (* Conjunto de secretos obtenidos *)
      enviroment : idMachine -> option Machine (* Vista parcial *) (* Puede diferir entre atacantes *)
    }.
  
  Definition valid_attacker_i (a: Attacker) : Prop :=
    forall (m:idMachine) (u:idUser), (In (m,u) (known_machines a)) -> (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                                              /\ (registered_users mac) u).
  Definition valid_attacker_ii (a: Attacker) : Prop :=
    forall (m:idMachine) (p:path), (In (m,p) (secrets a)) -> (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                                     /\ (registered_paths mac) p).                                                                     
End muSE.