Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

Require Import Machine.Machine.

Section Predicados.

  Definition registered_users (m:Machine) (u: idUser) : Prop := 
    exists (a: Account), account_user a = u /\ In a (machine_accounts m).
    
  Definition registered_paths (m:Machine) (p: path) : Prop := 
    exists (f: File), file_path f = p /\ In f (machine_fileSystem m).

  Definition registered_service (m: Machine) (s: idService) : Prop :=
    exists (serv: Service), service_value serv = s /\ In serv (machine_services m).
    
  (* Todo usuario con acceso a un archivo es un usuario registrado en la maquina *) 
  Definition users_access_to_files (m: Machine) : Prop :=
    forall (u: idUser) (f: File), (In f (machine_fileSystem m) /\ In u (file_user_access f)) -> registered_users m u.
              
  (* Para todo path en la maquina sus subarchivos estan registrados en la maquina *)
  (* Para todo path que es un directorio, los archivos que contiene estan registrados en la maquina *)
  Definition subfiles_in_machine (m: Machine) : Prop :=
    forall (f: File), In f (machine_fileSystem m) -> (forall (p':path), In p' (file_subfiles f) -> registered_paths m p').

  Definition is_neighbour (m: Machine) (mid: idMachine) :=
    In mid (machine_neighbours m).
    
  (* Para todo servicio asociado a una cuenta, es un servicio registrado en la maquina *)
  Definition users_access_to_services (m: Machine) : Prop :=
    forall (a: Account), In a (machine_accounts m) -> registered_service m (account_service a).
  
  (* Para toda maquina que pertenece a la red, todos sus vecinos tambien pertenecen a la red y ella es vecina de ellos *)
  Definition network_topology (network: network_map) : Prop :=
    forall (mid: idMachine)(m: Machine), network mid = Some m -> 
        forall (neighbour: idMachine), is_neighbour m neighbour 
          -> (exists (m':Machine), network neighbour = Some m' /\ is_neighbour m' mid).
          
  Definition valid_machine (m: Machine) : Prop :=
    users_access_to_files m /\ subfiles_in_machine m /\ users_access_to_services m.
    
  Definition valid_network (network: network_map) : Prop :=
    network_topology network /\ (forall (mid: idMachine)(m: Machine), network mid = Some m -> valid_machine m).

  Definition accounts_complete (m: Machine) : Prop :=
    forall (acc: Account), In acc (machine_accounts m) -> (account_key acc <> None /\ account_privilege acc <> None).

  Definition valid_concrete_network (network: network_map) : Prop :=
    network_topology network /\ (forall (mid: idMachine)(m: Machine), network mid = Some m -> valid_machine m /\ accounts_complete m).
End Predicados.