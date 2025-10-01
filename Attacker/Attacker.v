Require Import Coq.Lists.List.

Require Import Machine.Machine.

Section muSE.

  Record Attacker : Set :=
    attacker {
      known_machines : list (idMachine * idUser); (* Conjunto de acceso a máquinas *)
      secrets : list (idMachine * path); (* Conjunto de secretos obtenidos *)
      enviroment : idMachine -> option Machine (* Vista parcial *) (* Puede diferir entre atacantes *)
    }.
  
  
  (* Relaciona known_machines con enviroment de un Attacker *)
  (* Para cada par de identificador de máquina y usuario que esta en el area de propagación del atacante (known_machines),
     entonces ese identificador esta definido en las vistas parciales *)
  Definition valid_attacker_i (a: Attacker) (network: network_map) : Prop :=
    forall (m:idMachine) (u:idUser), 
      (In (m,u) (known_machines a)) -> 
        (exists (mac:Machine), (enviroment a) m = Some mac /\ registered_users mac u).

  (* Relaciona secrets con enviroment de un Attacker *)
  (* Para cada par de identificador de máquina y path que el atacante obtuvo como secreto (secrets),
     entonces ese identificador esta definido en las vistas parciales y el path es una ruta registrada/válida en esa máquina *)
  Definition valid_attacker_ii (a: Attacker) : Prop :=
    forall (m:idMachine) (p:path), 
      (In (m,p) (secrets a)) -> 
        (exists (mac:Machine), (enviroment a) m = Some mac /\ (registered_paths mac) p).
                                                                                     
  (* Enviroment válido de un atacante *)
  (* Topología válida y además para toda máquina que tiene una vista parcial definida, entonces esa máquina es válida*)
  Definition valid_attacker_iii (a: Attacker) : Prop :=
    valid_network (enviroment a).
    
  (* Relaciona la vista parcial del atacante con la red concreta objetivo *)
  (* Toda máquina con una vista parcial definida tambien esta definida en la red concreta 
     y además las máquinas estan relacionadas (una es 'subconjunto' de la otra)*)
  Definition valid_attacker_iv (a: Attacker) (network: network_map) : Prop := True.
  
  Definition valid_attacker (a: Attacker) (network: network_map) : Prop :=
    valid_attacker_i a network /\ valid_attacker_iii a /\ valid_attacker_iii a.
End muSE.