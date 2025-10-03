Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

Require Import Machine.Machine.

Section Predicados.

  Definition registered_users (m:Machine) (u: idUser) : Prop := 
    exists (l: list Account), (machine_accounts m) u = Some l.
    
  Definition registered_paths (m:Machine) (p: path) : Prop := 
    exists (files: list path) (users: list idUser) (o: objective), (machine_fileSystem m) p = Some (files, users, o).
    
  (* Todo usuario con acceso a un archivo es un usuario registrado en la maquina *) 
  Definition users_access_to_files (m: Machine) : Prop :=
    forall (u: idUser), 
      (exists (p: path)
              (files: list path)
              (auth: list idUser)
              (o: objective), (machine_fileSystem m) p = Some (files, auth, o) /\ (In u auth)) -> registered_users m u.
              
  (* Para todo path en la maquina sus subarchivos estan registrados en la maquina *)
  (* Para todo path que es un directorio, los archivos que contiene estan registrados en la maquina *)
  Definition subfiles_in_machine (m: Machine) : Prop :=
    forall (p: path)
           (files: list path)
           (auth: list idUser)
           (o: objective), (machine_fileSystem m) p = Some (files, auth, o) -> (forall (p':path), (In p' files) -> registered_paths m p').

  Definition is_neighbour (m: Machine) (mid: idMachine) :=
    In mid (machine_neighbours m).
    
  (* Para todo servicio asociado a una cuenta, es un servicio registrado en la maquina *)
  Definition users_access_to_services (m: Machine) : Prop :=
    forall (s: idService),
      (exists (u: idUser)
              (l: list Account)
              (acc: Account), (machine_accounts m) u = Some l 
                              /\ (In acc l) 
                              /\ (account_service acc) = s) -> (exists (serv: Service), (machine_services m) s = Some serv).
  
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
    forall (u: idUser) (l: list Account) (acc: Account), (machine_accounts m) u = Some l -> In acc l -> (account_key acc <> None /\ account_privilege acc <> None).

  Definition valid_concrete_network (network: network_map) : Prop :=
    network_topology network /\ (forall (mid: idMachine)(m: Machine), network mid = Some m -> valid_machine m /\ accounts_complete m).
End Predicados.