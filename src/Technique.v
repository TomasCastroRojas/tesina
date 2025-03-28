Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

Require Import Machine.
Require Import Attacker.

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
                                          /\ (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                     /\ In  m' (machine_neighbours mac))
                                          /\ (exists (accs: list Account)
                                                     (acc : Account) 
                                                     (mac': Machine), (enviroment a) m' = Some mac'
                                                                      /\ (machine_accounts mac') u' = Some accs
                                                                      /\ In acc accs
                                                                      /\ account_service acc = s
                                                                      /\ account_key acc = Some (Some k'))
      | Exploitation_Remote_Services m u m' s' e => (In (m,u) (known_machines a))
                                                    /\ (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                               /\ In  m' (machine_neighbours mac))
                                                    /\ (exists (serv : Service) 
                                                               (mac': Machine),(enviroment a) m' = Some mac' 
                                                                               /\ (machine_services mac') s' = Some serv
                                                                               /\ (In e (Exploits s'))) (* Exploits conocido asociados a un servicio *)
      | Unsecured_Credentials m u s => (In (m,u) (known_machines a))
                                       /\ (exists (accs: list Account) 
                                                  (acc : Account) 
                                                  (mac: Machine), (enviroment a) m = Some mac
                                                                  /\ (machine_accounts mac) u = Some accs
                                                                  /\ In acc accs
                                                                  /\ account_service acc = s)
      | Brute_Force m u m' u' s' => (In (m,u) (known_machines a))
                                    /\ (exists (mac: Machine), (enviroment a) m = Some mac 
                                                               /\ In  m' (machine_neighbours mac))
                                    /\ (exists (accs: list Account)
                                               (acc : Account) 
                                               (mac': Machine) 
                                               (l: privilege), (enviroment a) m' = Some mac'
                                                               /\ (machine_accounts mac') u' = Some accs
                                                               /\ In acc accs
                                                               /\ account_service acc = s'
                                                               /\ account_key acc = None
                                                               /\ account_privilege acc = Some l)
 
      | Abuse_Elevation_Control_Mechanism m u => (In (m,u) (known_machines a))
                                                 /\ (exists (accs: list Account)
                                                            (acc : Account) 
                                                            (mac: Machine)
                                                            (k : key), (enviroment a) m = Some mac
                                                                       /\ (machine_accounts mac) u = Some accs
                                                                       /\ In acc accs
                                                                       /\ account_service acc = OS
                                                                       /\ account_key acc = Some (Some k)
                                                                       /\ account_privilege acc = Some low_star)
      | File_Directory_Discovery_Local m u p => (In (m,u) (known_machines a))
                                                /\ (exists (mac: Machine) 
                                                           (users: list idUser)
                                                           (o: objective), (enviroment a) m = Some mac
                                                                           /\ (machine_fileSystem mac) p = Some (users, o)
                                                                           /\ In u users)
      | File_Directory_Discovery_Remote m u m' u' k' p' s' => (In (m,u) (known_machines a))
                                                              /\ (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                                             /\ In  m' (machine_neighbours mac))
                                                              /\ (exists (mac': Machine) 
                                                                         (serv': Service)
                                                                         (accs: list Account)
                                                                         (acc : Account)
                                                                         (users': list idUser)
                                                                         (o: objective), (enviroment a) m' = Some mac'
                                                                                         /\ (machine_services mac') s' = Some serv'
                                                                                         /\ is_network_service serv'
                                                                                         /\ (machine_accounts mac') u' = Some accs
                                                                                         /\ In acc accs
                                                                                         /\ account_service acc = s'
                                                                                         /\ account_key acc <> None
                                                                                         /\ (machine_fileSystem mac') p' = Some (users', o)
                                                                                         /\ In u' users')
      | Network_Service_Scanning m u m' l => (In (m,u) (known_machines a))
                                             /\ (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                        /\ In  m' (machine_neighbours mac))
      | Remote_System_Discovery m u => In (m,u) (known_machines a)
      | Account_Discovery_Local m u s => In (m,u) (known_machines a)
                                         /\ (exists (mac: Machine)
                                            (serv: Service)
                                            (accs: list Account)
                                            (acc : Account), (enviroment a) m = Some mac
                                                             /\ (machine_services mac) s = Some serv
                                                             /\ (machine_accounts mac) u = Some accs
                                                             /\ In acc accs
                                                             /\ account_service acc = s)
      | Account_Discovery_Remote m u m' u' k' s' => (In (m,u) (known_machines a))
                                                    /\ (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                                   /\ In  m' (machine_neighbours mac))
                                                    /\ (exists (mac': Machine) 
                                                               (serv': Service)
                                                               (accs': list Account)
                                                               (acc' : Account), (enviroment a) m' = Some mac'
                                                                                 /\ (machine_services mac') s' = Some serv'
                                                                                 /\ is_network_service serv'
                                                                                 /\ (machine_accounts mac') u' = Some accs'
                                                                                 /\ In acc' accs'
                                                                                 /\ account_service acc' = s'
                                                                                 /\ account_key acc' <> None)
      | System_Service_Discovery m u => In (m,u) (known_machines a)
      | Create_Account m u u' k' l' s => In (m,u) (known_machines a)
                                         /\ (exists (mac: Machine)
                                                    (accs: list Account)
                                                    (acc : Account), (enviroment a) m = Some mac
                                                                     /\ (machine_accounts mac) u = Some accs
                                                                     /\ In acc accs
                                                                     /\ account_service acc = s
                                                                     /\ account_privilege acc = Some high)
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
    
    Definition modify_machine (m: idMachine) (mac: Machine) (env: idMachine -> option Machine) : idMachine -> option Machine :=
      fun id => match idMachine_eq m id with
                  | left _ => Some mac
                  | right _ => env id
                end.
    
    Fixpoint get_accounts_linked_service_with_key (s: idService) (l: list Account) : list Account :=
      match l with
        | nil => nil
        | acc::l' => match idService_eq s (account_service acc) with
                       | left _ => account s (account_key acc) (account_privilege acc) :: get_accounts_linked_service_with_key s l'
                       | right _ => get_accounts_linked_service_with_key s l'
                     end
      end.
      
    Fixpoint get_accounts_linked_service_without_key (s: idService) (l: list Account) : list Account :=
      match l with
        | nil => nil
        | acc::l' => match idService_eq s (account_service acc) with
                       | left _ => account s None (account_privilege acc) :: get_accounts_linked_service_without_key s l'
                       | right _ => get_accounts_linked_service_without_key s l'
                     end
      end.
      
    Definition modify_accounts (u: idUser) (l: list Account) (accounts: idUser -> option (list Account)) : idUser -> option (list Account) :=
      fun id => match idUser_eq u id with
                  | left _ => Some l
                  | right _ => accounts id
                end.
    Definition updateAccountKey (k1 k2: option (option key)) : option (option key) :=
      match k1, k2 with
        | None, None => None
        | None, Some _ => k2
        | _, _ => k1
      end.
    
    Definition updateAccountPrivilege (l1 l2: option privilege) : option privilege :=
      match l1, l2 with
        | None, None => None
        | None, Some _ => l2
        | _, _ => l1
      end.
    
    Fixpoint oplusAccount (acc: Account) (accounts: list Account) : list Account :=
      match accounts with
        | nil => cons acc nil
        | acc':: accs => match idService_eq (account_service acc) (account_service acc') with
                          | left _ => cons (account (account_service acc)
                                                    (updateAccountKey (account_key acc') (account_key acc))
                                                    (updateAccountPrivilege (account_privilege acc') (account_privilege acc)))
                                           accs
                          | right _ => oplusAccount acc accs
                         end
      end.
    
    Definition addAccount (u: idUser) (acc: Account) (accounts: idUser -> option (list Account)) : idUser -> option (list Account) :=           
      fun id => match idUser_eq u id with
                  | left _ => match accounts u with
                                | None => Some (cons acc nil)
                                | Some l => Some (oplusAccount acc l)
                              end
                  | right _ => accounts id
                end.
    
    Fixpoint oplusAccounts (source dest: list Account) : list Account :=
      match source with
        | nil => dest
        | acc::accs => oplusAccounts accs (oplusAccount acc dest)
      end.
      
    Fixpoint addNeighbour (mac : idMachine) (neighbours: list idMachine) : list idMachine :=
      match neighbours with
        | nil => cons mac nil
        | mac'::macs => match idMachine_eq mac mac' with
                          | left _ => neighbours
                          | right _ => addNeighbour mac macs
                        end
      end.
    
    Fixpoint oplusNeighbours (source dest: list idMachine) : list idMachine :=
      match source with
        | nil => dest
        | mac::macs => oplusNeighbours macs (addNeighbour mac dest)
      end.
      
    Definition unionServices (s1 s2: idService -> option Service) : idService -> option Service :=
      fun s => match s1 s with
                | None => s2 s
                | Some serv => Some serv
               end.
    
    Fixpoint elem_mem_nat (n: nat) (l: list nat) : bool :=
      match l with
        | nil => false
        | x::xs => if Nat.eqb n x then true else elem_mem_nat n xs
      end.
    
    Definition scanServices (services: idService -> option Service) (ports: list nat) : idService -> option Service :=
      fun s => match services s with
                | None => None
                | Some serv => if logical_identifier_eq (logical_ident serv) service_port && (elem_mem_nat (value_s serv) ports) 
                               then Some serv 
                               else None
               end.
    (*
    Fixpoint get_service_in_port (port: nat) (services: list Service) : option Service :=
      match services with
        | nil => None
        | s::ss => if logical_identifier_eq (logical_ident s) service_port && Nat.eqb (value_s s) port then Some s else get_service_in_port port ss
      end.
    
    Fixpoint get_services_ports (services: idService -> option Service) (ports: list nat) : idService -> option Service :=
      match ports with
        | nil => nil
        | p::ps => match get_service_in_port p services with
                    | None => get_services_ports services ps
                    | Some s => s :: get_services_ports services ps
                   end
      end.
    *)
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
                                                                             /\ (machine_services mac) s' = Some serv
                                                                             /\ (machine_accounts mac) u' = Some accs
                                                                             /\ In acc accs
                                                                             /\ account_service acc = s'
                                                                             /\ known_machines a' = add_machine_user (m,u') (known_machines a))
                                                                                              
      | Unsecured_Credentials m u s => known_machines a' = known_machines a
                                       /\ secrets a' = secrets a
                                       /\ (exists (macView: Machine)
                                                  (mac: Machine)
                                                  (accs: list Account)
                                                  (accsView: list Account), (enviroment a) m = Some macView
                                                                            /\ network m = Some mac
                                                                            /\ (machine_accounts macView) u = Some accsView
                                                                            /\ (machine_accounts mac) u = Some accs
                                                                            /\ enviroment a' = modify_machine m 
                                                                                                              (machine (machine_services macView)
                                                                                                                       (modify_accounts u (oplusAccounts (get_accounts_linked_service_with_key s accs) accsView) (machine_accounts macView))
                                                                                                                       (machine_fileSystem macView)
                                                                                                                       (machine_neighbours macView))
                                                                                                              (enviroment a))
      | Brute_Force m u m' u' s' => known_machines a' = known_machines a
                                    /\ secrets a' = secrets a
                                    /\ (exists (macView':Machine)
                                               (mac': Machine)
                                               (accs': list Account)
                                               (accsView': list Account), (enviroment a) m' = Some macView'
                                                                          /\ network m' = Some mac'
                                                                          /\ (machine_accounts macView') u' = Some accsView'
                                                                          /\ (machine_accounts mac') u' = Some accs'
                                                                          /\ enviroment a' = modify_machine m' 
                                                                                                            (machine (machine_services macView')
                                                                                                                     (modify_accounts u' (oplusAccounts (get_accounts_linked_service_with_key s' accs') accsView') (machine_accounts macView'))
                                                                                                                     (machine_fileSystem macView')
                                                                                                                     (machine_neighbours macView'))
                                                                                                            (enviroment a))
 
      | Abuse_Elevation_Control_Mechanism m u => secrets a' = secrets a
                                                 /\ enviroment a' = enviroment a
                                                 /\ (exists (mac: Machine)
                                                            (u': idUser)
                                                            (accs: list Account)
                                                            (acc: Account), network m = Some mac
                                                                            /\ (machine_accounts mac) u' = Some accs
                                                                            /\ (In acc accs)
                                                                            /\ account_service acc = OS
                                                                            /\ account_privilege acc = Some high
                                                                            /\ known_machines a' = add_machine_user (m, u') (known_machines a))
      | Remote_System_Discovery m u => known_machines a' = known_machines a
                                       /\ secrets a' = secrets a
                                       /\ (exists (macView: Machine)
                                                  (mac: Machine), (enviroment a) m = Some macView
                                                                  /\ enviroment a' = modify_machine m
                                                                                                    (machine (machine_services macView)
                                                                                                             (machine_accounts macView)
                                                                                                             (machine_fileSystem macView)
                                                                                                             (oplusNeighbours (machine_neighbours macView) (machine_neighbours mac)))
                                                                                                    (enviroment a))
      | Account_Discovery_Local m u s => known_machines a' = known_machines a
                                         /\ secrets a' = secrets a
                                         /\ (exists (macView: Machine)
                                                    (mac: Machine)
                                                    (accs: list Account)
                                                    (accsView: list Account), (enviroment a) m = Some macView
                                                                              /\ network m = Some mac
                                                                              /\ (machine_accounts macView) u = Some accsView
                                                                              /\ (machine_accounts mac) u = Some accs
                                                                              /\ enviroment a' = modify_machine m 
                                                                                                                (machine (machine_services macView)
                                                                                                                         (modify_accounts u (oplusAccounts (get_accounts_linked_service_without_key s accs) accsView) (machine_accounts macView))
                                                                                                                         (machine_fileSystem macView)
                                                                                                                         (machine_neighbours macView))
                                                                                                                (enviroment a))
      | Account_Discovery_Remote m u m' u' k' s' => known_machines a' = known_machines a
                                                    /\ secrets a' = secrets a
                                                    /\ (exists (mac': Machine)
                                                               (macView': Machine)
                                                               (accs': list Account)
                                                               (accsView': list Account), (enviroment a) m' = Some macView'
                                                                                          /\ network m' = Some mac'
                                                                                          /\ (machine_accounts macView') u = Some accsView'
                                                                                          /\ (machine_accounts mac') u = Some accs'
                                                                                          /\ enviroment a' = modify_machine m 
                                                                                                                            (machine (machine_services macView')
                                                                                                                                     (modify_accounts u' (oplusAccounts (get_accounts_linked_service_without_key s' accs') accsView') (machine_accounts macView'))
                                                                                                                                     (machine_fileSystem macView')
                                                                                                                                     (machine_neighbours macView'))
                                                                                                                            (enviroment a))
      | System_Service_Discovery m u => known_machines a' = known_machines a
                                        /\ secrets a' = secrets a
                                        /\ (exists (mac: Machine)
                                                   (macView: Machine), (enviroment a) m = Some macView
                                                                           /\ network m = Some mac
                                                                           /\ enviroment a' = modify_machine m 
                                                                                                             (machine (unionServices (machine_services macView) (machine_services mac))
                                                                                                                      (machine_accounts macView)
                                                                                                                      (machine_fileSystem macView)
                                                                                                                      (machine_neighbours macView))
                                                                                                             (enviroment a))
      | Network_Service_Scanning m u m' l => known_machines a' = known_machines a
                                             /\ secrets a' = secrets a
                                             /\ (exists (macView': Machine)
                                                        (mac': Machine), (enviroment a) m' = Some macView'
                                                                         /\ enviroment a' = modify_machine m'
                                                                                                            (machine (unionServices (machine_services macView') (scanServices (machine_services mac') l))
                                                                                                                     (machine_accounts macView')
                                                                                                                     (machine_fileSystem macView')
                                                                                                                     (machine_neighbours macView'))
                                                                                                            (enviroment a))
      (*
      | Create_Account m u u' k' l' s => known_machines a' = known_machines a
                                         /\ secrets a' = secrets a
                                         /\ (exists (macView: MachineView), (enviroment a) m = Some macView
                                                                              /\ enviroment a' = modify_machine m
                                                                                                              (machine_view (machine_view_services macView)
                                                                                                                             (addAccountView u' (account_view (Some s) (Some (Some k')) (Some l')) (machine_view_accounts macView))
                                                                                                                             (machine_view_fileSystem macView)
                                                                                                                             (machine_view_neighbours macView))
                                                                                                              (enviroment a))

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