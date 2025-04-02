Require Import Coq.Lists.List.
Require Import Machine.

Section muSE.

  Record Attacker : Set :=
    attacker {
      known_machines : list (idMachine * idUser); (* Conjunto de acceso a máquinas *)
      secrets : list (idMachine * path); (* Conjunto de secretos obtenidos *)
      enviroment : idMachine -> option Machine (* Vista parcial *) (* Puede diferir entre atacantes *)
    }.
    
  Definition register_users (m:Machine) : idUser -> Prop := 
    fun u => exists (l: list Account), (machine_accounts m) u = Some l.
  Definition register_paths (m:Machine) : path -> Prop := 
    fun p => exists (files: list path) (users: list idUser) (o: objective), (machine_fileSystem m) p = Some (files, users, o).
  
  Definition valid_attacker_i (a: Attacker) : Prop :=
    forall (m:idMachine) (u:idUser), (In (m,u) (known_machines a)) -> (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                                              /\ (register_users mac) u).
  Definition valid_attacker_ii (a: Attacker) : Prop :=
    forall (m:idMachine) (p:path), (In (m,p) (secrets a)) -> (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                                     /\ (register_paths mac) p).                                                                     
End muSE.