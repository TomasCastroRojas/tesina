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
  Parameter os: idService.
  Definition is_network_service (s: idService) : Prop := True.

  (* Vista de Cuentas *)
  Record AccountView : Set :=
      account_view {
        account_view_service  : option idService; (* | bottom *)
        account_view_key : option (option key); (* | bottom *)
        account_view_privilege : option privilege (* | bottom *)
      }.
      
  Record Account : Set :=
      account {
        account_service  : idService; 
        account_key : option key; 
        account_privilege : privilege
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
      service_ident: idService;
      logical_ident : logical_identifier;
      value_s : nat
    }.
  
  (* Rutas del sistema de archivos *)
  Parameter path : Set.
  Parameter path_eq : forall p1 p2 : path, {p1 = p2} + {p1 <> p2}.
  (* Definir un orden parcial, jerarquía de archivos*)
    
  (* Identificadores de máquinas *)
  Parameter idMachine : Set.
  Parameter idMachine_eq : forall m1 m2 : idMachine, {m1 = m2} + {m1 <> m2}.
  
  (* Exploits conocidos*)
  Parameter idExploit : Set.
  Parameter idExploit_eq : forall e1 e2 : idExploit, {e1 = e2} + {e1 <> e2}.
  
  Record MachineView : Set :=
    machine_view {
      machine_view_ident : idMachine;
      machine_view_services : list Service;
      machine_view_accounts : idUser -> option (list AccountView);
      machine_view_fileSystem : path -> option (list idUser);
      machine_view_neighbours : list idMachine;
      (* exploits : idService -> option (list idExploit) (* Exploits asociados a un servicio en esta máquina*) *)
    }.
  Record Machine : Set :=
    machine {
      machine_ident : idMachine;
      machine_services : list Service;
      machine_accounts : idUser -> option (list Account);
      machine_fileSystem : path -> option (list idUser);
      machine_neighbours : list idMachine;
      (* exploits : idService -> option (list idExploit) (* Exploits asociados a un servicio en esta máquina*) *)
    }.
    
  Definition network_map := idMachine -> option Machine. 
  
End Machine.

Section muSE.

  Record Attacker : Set :=
    attacker {
      known_machines : list (idMachine * idUser); (* Conjunto de acceso a máquinas *)
      secrets : list (idMachine * path); (* Conjunto de secretos obtenidos *)
      enviroment : idMachine -> option MachineView (* Vista parcial *) (* Puede diferir entre atacantes *)
    }.
    
  Definition register_users (m:MachineView) : idUser -> Prop := 
    fun u => exists (l: list AccountView), (machine_view_accounts m) u = Some l.
  Definition register_paths (m:MachineView) : path -> Prop := 
    fun p => exists (l: list idUser), (machine_view_fileSystem m) p = Some l.
  
  Definition valid_attacker_i (a: Attacker) : Prop :=
    forall (m:idMachine) (u:idUser), (In (m,u) (known_machines a)) -> (exists (mac: MachineView), (enviroment a) m = Some mac 
                                                                                                  /\ (register_users mac) u).
  Definition valid_attacker_ii (a: Attacker) : Prop :=
    forall (m:idMachine) (p:path), (In (m,p) (secrets a)) -> (exists (mac: MachineView), (enviroment a) m = Some mac 
                                                                                         /\ (register_paths mac) p).                                                                     
End muSE.

Section Techniques.

  Inductive Technique : Set :=
    (* Lateral Movement *)
    | Remote_Services : idMachine -> idUser -> idMachine -> idUser -> key -> idService -> Technique
    | Exploitation_Remote_Services : idMachine -> idUser -> idMachine -> idService -> idExploit -> Technique
    (* Credential Access *)
    | Unsecured_Credentials : idMachine -> idUser -> idService -> Technique
    | Brute_Force : idMachine -> idUser -> idMachine -> idUser -> idService -> Technique
    (* Privilege Escalation *)
    | Abuse_Elevation_Control_Mechanism : idMachine -> idUser -> Technique
    (* Discovery *)
    | File_Directory_Discovery_Local : idMachine -> idUser -> path -> Technique
    | File_Directory_Discovery_Remote : idMachine -> idUser -> idMachine -> idUser -> key -> path -> idService -> Technique
    | Network_Service_Scanning : idMachine -> idUser -> idMachine -> list nat -> Technique
    | Remote_System_Discovery : idMachine -> idUser -> Technique
    | Account_Discovery_Local : idMachine -> idUser -> idService -> Technique
    | Account_Discovery_Remote : idMachine -> idUser -> idMachine -> idUser -> key -> idService -> Technique
    | System_Service_Discovery : idMachine -> idUser -> Technique
    (* Persistence *)
    | Create_Account : idMachine -> idUser -> idUser -> key -> privilege -> idService -> Technique. 


  Definition Pre (a : Attacker) (t: Technique) : Prop :=
    match t with
      | Remote_Services m u m' u' k' s => (In (m,u) (known_machines a)) 
                                          /\ (exists (mac: MachineView), (enviroment a) m = Some mac 
                                                                         /\ In  m' (machine_view_neighbours mac))
                                          /\ (exists (accs: list AccountView)
                                                     (acc : AccountView) 
                                                     (mac': MachineView), (enviroment a) m' = Some mac'
                                                                          /\ (machine_view_accounts mac') u' = Some accs
                                                                          /\ In acc accs
                                                                          /\ account_view_service acc = Some s
                                                                          /\ account_view_key acc = Some (Some k'))
      | Exploitation_Remote_Services m u m' s' e => (In (m,u) (known_machines a))
                                                    /\ (exists (mac: MachineView), (enviroment a) m = Some mac 
                                                                                   /\ In  m' (machine_view_neighbours mac))
                                                    /\ (exists (serv : Service) 
                                                               (mac': MachineView),(enviroment a) m' = Some mac' 
                                                                                   /\ service_ident serv = s'
                                                                                   /\ In serv (machine_view_services mac'))
                                                                                                     (* (In e Exploits(s))
                                                                                                        Cómo asociar el exploit con el servicio y la máquina? 
                                                                                                        Cómo puede saber el atacante que el exploit va a funcionar?*)
      | Unsecured_Credentials m u s => (In (m,u) (known_machines a))
                                       /\ (exists (accs: list AccountView) 
                                                  (acc : AccountView) 
                                                  (mac: MachineView), (enviroment a) m = Some mac
                                                                      /\ (machine_view_accounts mac) u = Some accs
                                                                      /\ In acc accs
                                                                      /\ account_view_service acc = Some s)
      | Brute_Force m u m' u' s' => (In (m,u) (known_machines a))
                                    /\ (exists (mac: MachineView), (enviroment a) m = Some mac 
                                                                   /\ In  m' (machine_view_neighbours mac))
                                    /\ (exists (accs: list AccountView)
                                               (acc : AccountView) 
                                               (mac': MachineView) 
                                               (l: privilege), (enviroment a) m' = Some mac'
                                                               /\ (machine_view_accounts mac') u' = Some accs
                                                               /\ In acc accs
                                                               /\ account_view_service acc = Some s'
                                                               /\ account_view_key acc = None
                                                               /\ account_view_privilege acc = Some l)
 
      | Abuse_Elevation_Control_Mechanism m u => (In (m,u) (known_machines a))
                                                 /\ (exists (accs: list AccountView)
                                                            (acc : AccountView) 
                                                            (mac: MachineView)
                                                            (k : key), (enviroment a) m = Some mac
                                                                       /\ (machine_view_accounts mac) u = Some accs
                                                                       /\ In acc accs
                                                                       /\ account_view_service acc = Some os
                                                                       /\ account_view_key acc = Some (Some k)
                                                                       /\ account_view_privilege acc = Some low_star)
      | File_Directory_Discovery_Local m u p => (In (m,u) (known_machines a))
                                                /\ (exists (mac: MachineView) 
                                                           (users: list idUser), (enviroment a) m = Some mac
                                                                                 /\ (machine_view_fileSystem mac) p = Some users
                                                                                 /\ In u users)
      | File_Directory_Discovery_Remote m u m' u' k' p' s' => (In (m,u) (known_machines a))
                                                              /\ (exists (mac: MachineView), (enviroment a) m = Some mac 
                                                                                             /\ In  m' (machine_view_neighbours mac))
                                                              /\ (exists (mac': MachineView) 
                                                                         (serv': Service)
                                                                         (accs: list AccountView)
                                                                         (acc : AccountView)
                                                                         (users': list idUser), (enviroment a) m' = Some mac'
                                                                                                /\ In serv' (machine_view_services mac')
                                                                                                /\ service_ident serv' = s'
                                                                                                /\ is_network_service s'
                                                                                                /\ (machine_view_accounts mac') u' = Some accs
                                                                                                /\ In acc accs
                                                                                                /\ account_view_service acc = Some s'
                                                                                                /\ account_view_key acc <> None
                                                                                                /\ (machine_view_fileSystem mac') p' = Some users'
                                                                                                /\ In u' users')
      | Network_Service_Scanning m u m' l => (In (m,u) (known_machines a))
                                             /\ (exists (mac: MachineView), (enviroment a) m = Some mac 
                                                                            /\ In  m' (machine_view_neighbours mac))
      | Remote_System_Discovery m u => In (m,u) (known_machines a)
      | Account_Discovery_Local m u s => In (m,u) (known_machines a)
                                         /\ (exists (mac: MachineView)
                                            (serv: Service)
                                            (accs: list AccountView)
                                            (acc : AccountView), (enviroment a) m = Some mac
                                                                 /\ In serv (machine_view_services mac)
                                                                 /\ service_ident serv = s
                                                                 /\ (machine_view_accounts mac) u = Some accs
                                                                 /\ In acc accs
                                                                 /\ account_view_service acc = Some s)
      | Account_Discovery_Remote m u m' u' k' s' => (In (m,u) (known_machines a))
                                                    /\ (exists (mac: MachineView), (enviroment a) m = Some mac 
                                                                                   /\ In  m' (machine_view_neighbours mac))
                                                    /\ (exists (mac': MachineView) 
                                                               (serv': Service)
                                                               (accs': list AccountView)
                                                               (acc' : AccountView), (enviroment a) m' = Some mac'
                                                                                     /\ In serv' (machine_view_services mac')
                                                                                     /\ service_ident serv' = s'
                                                                                     /\ is_network_service s'
                                                                                     /\ (machine_view_accounts mac') u' = Some accs'
                                                                                     /\ In acc' accs'
                                                                                     /\ account_view_service acc' = Some s'
                                                                                     /\ account_view_key acc' <> None)
      | System_Service_Discovery m u => In (m,u) (known_machines a)
      | Create_Account m u u' k' l' s => In (m,u) (known_machines a)
                                         /\ (exists (mac: MachineView)
                                                    (accs: list AccountView)
                                                    (acc : AccountView), (enviroment a) m = Some mac
                                                                         /\ (machine_view_accounts mac) u = Some accs
                                                                         /\ In acc accs
                                                                         /\ account_view_service acc = Some s
                                                                         /\ account_view_privilege acc = Some high)
    end.
    
    
    Fixpoint add_machine_user (mu: (idMachine * idUser)) (l: list (idMachine * idUser)) : list (idMachine * idUser) :=
      match l with
        | nil => mu::nil
        | (m', u')::l' => let (m,u) := mu in
                          match idMachine_eq m m', idUser_eq u u' with
                            | left _, left _ => l
                            | _, _ => add_machine_user mu l'
                          end
      end.
      
    Fixpoint add_secret (s: (idMachine * path)) (l: list (idMachine * path)) : list (idMachine * path) :=
      match l with
        | nil => s::nil
        | (m', p')::l' => let (m,p) := s in
                          match idMachine_eq m m', path_eq p p' with
                            | left _, left _ => l
                            | _, _ => add_secret s l'
                          end
      end.
    
    Definition modify_machine (m: idMachine) (mac: MachineView) (env: idMachine -> option MachineView) : idMachine -> option MachineView :=
      fun id => match idMachine_eq m id with
                  | left _ => Some mac
                  | right _ => env id
                end.
    
    Fixpoint get_accounts_linked_service_with_key (s: idService) (l: list Account) : list AccountView :=
      match l with
        | nil => nil
        | acc::l' => match idService_eq s (account_service acc) with
                       | left _ => account_view (Some s) (Some (account_key acc)) (Some (account_privilege acc)) :: get_accounts_linked_service_with_key s l'
                       | right _ => get_accounts_linked_service_with_key s l'
                     end
      end.
      
    Fixpoint get_accounts_linked_service_without_key (s: idService) (l: list Account) : list AccountView :=
      match l with
        | nil => nil
        | acc::l' => match idService_eq s (account_service acc) with
                       | left _ => account_view (Some s) None (Some (account_privilege acc)) :: get_accounts_linked_service_without_key s l'
                       | right _ => get_accounts_linked_service_without_key s l'
                     end
      end.
      
    Definition modify_accounts (u: idUser) (l: list AccountView) (accounts: idUser -> option (list AccountView)) : idUser -> option (list AccountView) :=
      fun id => match idUser_eq u id with
                  | left _ => Some l
                  | right _ => accounts id
                end.
    Definition addAccountView (u: idUser) (acc: AccountView) (accounts: idUser -> option (list AccountView)) : idUser -> option (list AccountView) :=           
      fun id => match idUser_eq u id with
                  | left _ => match accounts u with
                                | None => Some (cons acc nil)
                                | Some l => Some (cons acc l)
                              end
                  | right _ => accounts id
                end.
    Fixpoint get_service_in_port (port: nat) (services: list Service) : option Service :=
      match services with
        | nil => None
        | s::ss => if logical_identifier_eq (logical_ident s) service_port && Nat.eqb (value_s s) port then Some s else get_service_in_port port ss
      end.
    
    Fixpoint get_services_ports (services: list Service) (ports: list nat) : list Service :=
      match ports with
        | nil => nil
        | p::ps => match get_service_in_port p services with
                    | None => get_services_ports services ps
                    | Some s => s :: get_services_ports services ps
                   end
      end.
    
    Definition Post (a: Attacker) (t: Technique) (network: network_map) (a': Attacker): Prop :=
      match t with
      | Remote_Services m u m' u' k' s => known_machines a' = add_machine_user (m', u') (known_machines a)
                                          /\ secrets a' = secrets a
                                          /\ enviroment a' = enviroment a
      | Exploitation_Remote_Services m u m' s' e => secrets a' = secrets a
                                                    /\ enviroment a' = enviroment a
                                                    /\ (exists (mac:Machine) 
                                                               (serv: Service)
                                                               (accs: list Account)
                                                               (acc: Account)
                                                               (u': idUser), network m' = Some mac
                                                                               /\ In serv (machine_services mac)
                                                                               /\ service_ident serv = s'
                                                                               /\ (machine_accounts mac) u' = Some accs
                                                                               /\ In acc accs
                                                                               /\ account_service acc = s'
                                                                               /\ known_machines a' = add_machine_user (m,u') (known_machines a))
                                                                                              
      | Unsecured_Credentials m u s => known_machines a' = known_machines a
                                       /\ secrets a' = secrets a
                                       /\ (exists (macView:MachineView)
                                                  (mac: Machine)
                                                  (accs: list Account)
                                                  (accsView: list AccountView), (enviroment a) m = Some macView
                                                                  /\ network m = Some mac
                                                                  /\ (machine_view_accounts macView) u = Some accsView
                                                                  /\ (machine_accounts mac) u = Some accs
                                                                  /\ enviroment a' = modify_machine m 
                                                                                                    (machine_view (machine_view_ident macView)
                                                                                                                  (machine_view_services macView)
                                                                                                                  (* TODO: implementar Oplus para evitar repetidos *)
                                                                                                                  (modify_accounts u (accsView ++ get_accounts_linked_service_with_key s accs) (machine_view_accounts macView))
                                                                                                                  (machine_view_fileSystem macView)
                                                                                                                  (machine_view_neighbours macView))
                                                                                                    (enviroment a))
      | Brute_Force m u m' u' s' => known_machines a' = known_machines a
                                    /\ secrets a' = secrets a
                                    /\ (exists (macView':MachineView)
                                                (mac': Machine)
                                                (accs': list Account)
                                                  (accsView': list AccountView), (enviroment a) m' = Some macView'
                                                                                /\ network m' = Some mac'
                                                                                /\ (machine_view_accounts macView') u' = Some accsView'
                                                                                /\ (machine_accounts mac') u' = Some accs'
                                                                                /\ enviroment a' = modify_machine m' 
                                                                                                    (machine_view (machine_view_ident macView')
                                                                                                                  (machine_view_services macView')
                                                                                                                  (* TODO: implementar Oplus para evitar repetidos *)
                                                                                                                  (modify_accounts u' (accsView' ++ get_accounts_linked_service_with_key s' accs') (machine_view_accounts macView'))
                                                                                                                  (machine_view_fileSystem macView')
                                                                                                                  (machine_view_neighbours macView'))
                                                                                                    (enviroment a))
 
      | Abuse_Elevation_Control_Mechanism m u => secrets a' = secrets a
                                                 /\ enviroment a' = enviroment a
                                                 /\ (exists (mac: Machine)
                                                            (u': idUser)
                                                            (accs: list Account)
                                                            (acc: Account), network m = Some mac
                                                                                  /\ (machine_accounts mac) u' = Some accs
                                                                                  /\ (In acc accs)
                                                                                  /\ account_service acc = os
                                                                                  /\ account_privilege acc = high
                                                                                  /\ known_machines a' = add_machine_user (m, u') (known_machines a))
      | Network_Service_Scanning m u m' l => known_machines a' = known_machines a
                                             /\ secrets a' = secrets a
                                             /\ (exists (macView':MachineView)
                                                        (mac': Machine), (enviroment a) m' = Some macView'
                                                                         /\ enviroment a' = modify_machine m'
                                                                                                            (machine_view (machine_view_ident macView')
                                                                                                                          (machine_view_services macView')
                                                                                                                          (machine_view_accounts macView')
                                                                                                                          (machine_view_fileSystem macView')
                                                                                                                          (machine_view_neighbours macView'))
                                                                                                            (enviroment a))
      | Remote_System_Discovery m u => known_machines a' = known_machines a
                                       /\ secrets a' = secrets a
                                       /\ (exists (macView:MachineView)
                                                  (mac: Machine), (enviroment a) m = Some macView
                                                                  /\ enviroment a' = modify_machine m
                                                                                                    (machine_view (machine_view_ident macView)
                                                                                                                  (machine_view_services macView)
                                                                                                                  (machine_view_accounts macView)
                                                                                                                  (machine_view_fileSystem macView)
                                                                                                                  ((machine_view_neighbours macView) ++ (machine_neighbours mac)))
                                                                                                    (enviroment a))
      | Account_Discovery_Local m u s => known_machines a' = known_machines a
                                         /\ secrets a' = secrets a
                                         /\ (exists (macView:MachineView)
                                                    (mac: Machine)
                                                    (accs: list Account)
                                                    (accsView: list AccountView), (enviroment a) m = Some macView
                                                                    /\ network m = Some mac
                                                                    /\ (machine_view_accounts macView) u = Some accsView
                                                                    /\ (machine_accounts mac) u = Some accs
                                                                    /\ enviroment a' = modify_machine m 
                                                                                                      (machine_view (machine_view_ident macView)
                                                                                                                    (machine_view_services macView)
                                                                                                                    (* TODO: implementar Oplus para evitar repetidos *)
                                                                                                                    (modify_accounts u (accsView ++ get_accounts_linked_service_without_key s accs) (machine_view_accounts macView))
                                                                                                                    (machine_view_fileSystem macView)
                                                                                                                    (machine_view_neighbours macView))
                                                                                                      (enviroment a))
      | Account_Discovery_Remote m u m' u' k' s' => known_machines a' = known_machines a
                                                    /\ secrets a' = secrets a
                                                    /\ (exists (mac': Machine)
                                                               (macView': MachineView)
                                                               (accs': list Account)
                                                               (accsView': list AccountView), (enviroment a) m' = Some macView'
                                                                                              /\ network m' = Some mac'
                                                                                              /\ (machine_view_accounts macView') u = Some accsView'
                                                                                              /\ (machine_accounts mac') u = Some accs'
                                                                                              /\ enviroment a' = modify_machine m 
                                                                                                                                (machine_view (machine_view_ident macView')
                                                                                                                                              (machine_view_services macView')
                                                                                                                                              (* TODO: implementar Oplus para evitar repetidos *)
                                                                                                                                              (modify_accounts u' (accsView' ++ get_accounts_linked_service_without_key s' accs') (machine_view_accounts macView'))
                                                                                                                                              (machine_view_fileSystem macView')
                                                                                                                                              (machine_view_neighbours macView'))
                                                                                                                                (enviroment a))
      | System_Service_Discovery m u => known_machines a' = known_machines a
                                        /\ secrets a' = secrets a
                                        /\ (exists (mac: Machine)
                                                   (macView: MachineView), (enviroment a) m = Some macView
                                                                           /\ network m = Some mac
                                                                           /\ enviroment a' = modify_machine m 
                                                                                                             (machine_view (machine_view_ident macView)
                                                                                                                           ((machine_view_services macView) ++ (machine_services mac))
                                                                                                                           (machine_view_accounts macView)
                                                                                                                           (machine_view_fileSystem macView)
                                                                                                                           (machine_view_neighbours macView))
                                                                                                             (enviroment a))
      | Create_Account m u u' k' l' s => known_machines a' = known_machines a
                                         /\ secrets a' = secrets a
                                         /\ (exists (macView: MachineView), (enviroment a) m = Some macView
                                                                              /\ enviroment a' = modify_machine m
                                                                                                              (machine_view (machine_view_ident macView)
                                                                                                                             (machine_view_services macView)
                                                                                                                             (addAccountView u' (account_view (Some s) (Some (Some k')) (Some l')) (machine_view_accounts macView))
                                                                                                                             (machine_view_fileSystem macView)
                                                                                                                             (machine_view_neighbours macView))
                                                                                                              (enviroment a))
      (*
      | File_Directory_Discovery_Local m u p => known_machines a' = known_machines a
                                                /\ (exists (macView: MachineView)
                                                           (mac: Machine)
                                                           (users: list idUser), (enviroment a) m = Some macView
                                                                                /\ network m = Some mac
                                                                                /\ 
      | File_Directory_Discovery_Remote m u m' u' k' p' s' => *)
      | _ => True
    end.
End Techniques.




















