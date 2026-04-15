Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

Require Import Machine.Machine.

Section Predicados.

  (* Un usuario esta registrado en una maquina si existe alguna cuenta asociada a ese usuario en la lista de cuentas de la maquina *)
  Definition registered_users (m:Machine) (u: idUser) : Prop :=
    exists (a: Account), account_user a = u /\ In a (machine_accounts m).
    
  (* Una ruta esta registrada en una maquina si existe algun archivo con esa ruta en el sistema de archivos de la maquina *)
  Definition registered_paths (m:Machine) (p: path) : Prop :=
    exists (f: File), file_path f = p /\ In f (machine_fileSystem m).

  (* Un servicio esta registrado en una maquina si existe algun registro de servicio con ese identificador en la lista de servicios de la maquina *)
  Definition registered_service (m: Machine) (s: idService) : Prop :=
    exists (serv: Service), service_value serv = s /\ In serv (machine_services m).
    
  (* Todo archivo en la maquina tiene al menos un usuario registrado con acceso a el *)
  Definition users_access_to_files (m: Machine) : Prop :=
    forall (f: File), In f (machine_fileSystem m) -> (exists (u:idUser), registered_users m u /\ In u (file_user_access f)).
              
  (* Para todo archivo en la maquina, cada una de sus subrutas esta registrada como ruta en la maquina *)
  Definition subfiles_in_machine (m: Machine) : Prop :=
    forall (f: File), In f (machine_fileSystem m) -> (forall (p':path), In p' (file_subfiles f) -> registered_paths m p').

  (* En una lista de archivos, no existen dos archivos distintos con la misma ruta *)
  Definition unique_paths_to_file (files: list File) : Prop :=
    forall (f g: File), In f files -> In g files -> file_path f = file_path g -> f = g.

  (* Ningun archivo se contiene a si mismo como subarchivo *)
  Definition files_without_cycles (files: list File) : Prop :=
    forall (f: File), In f files -> (~ In (file_path f) (file_subfiles f)).
  
  (* Un sistema de archivos es valido si los subarchivos estan registrados, las rutas son unicas y no hay ciclos directos *)
  Definition valid_fileSystem (m: Machine) : Prop :=
    subfiles_in_machine m /\ NoDup (map file_path (machine_fileSystem m)) /\ files_without_cycles (machine_fileSystem m).

  (* Un identificador de maquina es vecino de una maquina dada *)
  Definition is_neighbour (m: Machine) (mid: idMachine) :=
    In mid (machine_neighbours m).
    
  (* Para toda cuenta en la maquina, si tiene un servicio asociado entonces ese servicio esta registrado en la maquina *)
  Definition users_access_to_services (m: Machine) : Prop :=
    forall (a: Account), In a (machine_accounts m) -> (account_service a = None \/ (exists (s: idService), account_service a = Some s /\ registered_service m s)).
  
  (* Todo vecino de toda maquina definida en la red esta tambien definido en la red *)
  Definition network_topology (network: network_map) : Prop :=
    forall (mid neighbour: idMachine)(m: Machine), mid <> neighbour -> network mid = Some m -> is_neighbour m neighbour 
          -> exists (m':Machine), network neighbour = Some m'.
  
  Definition exploits_services (m: Machine) : Prop :=
    forall (s: idService)(e: idExploit), In (s, e) (machine_exploits m) -> registered_service m s.
          
  (* Una maquina es valida si cumple las propiedades de acceso a archivos, acceso a servicios y sistema de archivos valido *)
  Definition valid_machine (m: Machine) : Prop :=
    users_access_to_files m /\ users_access_to_services m /\ exploits_services m /\ valid_fileSystem m.
    
  (* Una red es valida si su topologia es valida y todas sus maquinas son validas *)
  Definition valid_network (network: network_map) : Prop :=
    network_topology network /\ (forall (mid: idMachine)(m: Machine), network mid = Some m -> valid_machine m).

  (* Toda cuenta en la maquina tiene definidos todos sus campos opcionales (servicio, clave y privilegio) *)
  Definition accounts_complete (m: Machine) : Prop :=
    forall (acc: Account), In acc (machine_accounts m) -> (account_service acc <> None /\ account_key acc <> None /\ account_privilege acc <> None).

  (* Una red concreta es valida si su topologia es valida, todas sus maquinas son validas y todas las cuentas son completas *)
  Definition valid_concrete_network (network: network_map) : Prop :=
    network_topology network /\ (forall (mid: idMachine)(m: Machine), network mid = Some m -> valid_machine m /\ accounts_complete m).
    
End Predicados.