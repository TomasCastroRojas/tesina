Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

Section Machine.

  (* Nivel de privilegios *)
  Inductive privilege : Set := 
    | low
    | low_star
    | high.
  
  (* Claves de cuentas en la maquina (contraseñas, tokens, etc)*)
  Parameter key : Set.
  Parameter key_eq : forall k1 k2 : key, {k1 = k2} + {k1 <> k2}.

  (* Identificadores de Usuarios *)
  Parameter idUser : Set.
  Parameter idUser_eq : forall u1 u2 : idUser, {u1 = u2} + {u1 <> u2}.

  (* Identificadores de Servicios *)
  Parameter idService : Set.
  Parameter idService_eq : forall s1 s2: idService, {s1 = s2} + {s1 <> s2}.
  Parameter OS: idService.

  (* Cuentas *)
      
  Record Account : Set :=
      account {
        account_service  : idService; 
        account_key : option (option key); 
        account_privilege : option privilege
      }.
      
  (* Identificador del recurso de un servicio *)
  Inductive logical_identifier : Set := 
    | service_port
    | service_process
    | service_file.

  Definition logical_identifier_eq (l1 l2: logical_identifier) : bool :=
    match l1, l2 with
      | service_port, service_port => true
      | service_port, _ => false
      | _, service_port => false
      | service_process, service_process => true
      | service_process, _ => false
      | _, service_process => false
      | service_file, service_file => true
    end. 
    
  (* Valor asociado del recurso de un servicio (Numero de puerto, numero de proceso o un archivo)*)
  Parameter serviceValue : Set.
  Parameter serviceValue_eq : forall val1 val2 : serviceValue, {val1 = val2} + {val1 <> val2}.

  (* Servicios *)
  Record Service : Set :=
    service {
      logical_ident : logical_identifier;
      value_s : nat (* Deberia ser serviceValue *) 
      (* El experimento PWNJUTSU modela principalmente la etapa de propagacion en red del atacante 
      por lo que en las Techniques siempre se utiliza como logical_ident a un puerto *)
    }.
  
  Definition is_network_service (s: Service) : Prop := (logical_ident s) = service_port.
  (* Rutas del sistema de archivos *)
  Parameter path : Set.
  Parameter path_eq : forall p1 p2 : path, {p1 = p2} + {p1 <> p2}.
  (* Definir un orden parcial, jerarquía de archivos*)
  
  (* Flag que marca los objetivos del atacante *)
  Definition objective := bool.
    
  (* Identificadores de máquinas *)
  Parameter idMachine : Set.
  Parameter idMachine_eq : forall m1 m2 : idMachine, {m1 = m2} + {m1 <> m2}.
  
  (* Exploits conocidos*)
  Parameter idExploit : Set.
  Parameter idExploit_eq : forall e1 e2 : idExploit, {e1 = e2} + {e1 <> e2}.
  
  Parameter Exploits : idService -> list idExploit.
  
  Record Machine : Set :=
    machine {
      machine_services : idService -> option Service; (* Servicios registrados *)
      machine_accounts : idUser -> option (list Account); (* Usuarios registrado. Un usuario puede estar suscrito a más de un servicio *)
      machine_fileSystem : path -> option (list path * list idUser * objective); (* Archivos y directorios de la máquina *)
      machine_neighbours : list idMachine; (* Vecinos *)
    }.
    
  (* Red de máquinas en un sistema *)
  Definition network_map := idMachine -> option Machine. 
  
End Machine.

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
End Predicados.