Require Import Coq.Lists.List.

Require Import Machine.
Require Import MachineAuxFunctions.
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
                                                           (files: list path)
                                                           (users: list idUser)
                                                           (o: objective), (enviroment a) m = Some mac
                                                                           /\ (machine_fileSystem mac) p = Some (files, users, o)
                                                                           /\ In u users)
      | File_Directory_Discovery_Remote m u m' u' k' p' s' => (In (m,u) (known_machines a))
                                                              /\ (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                                             /\ In  m' (machine_neighbours mac))
                                                              /\ (exists (mac': Machine) 
                                                                         (serv': Service)
                                                                         (accs: list Account)
                                                                         (acc : Account)
                                                                         (files': list path)
                                                                         (users': list idUser)
                                                                         (o: objective), (enviroment a) m' = Some mac'
                                                                                         /\ (machine_services mac') s' = Some serv'
                                                                                         /\ is_network_service serv'
                                                                                         /\ (machine_accounts mac') u' = Some accs
                                                                                         /\ In acc accs
                                                                                         /\ account_service acc = s'
                                                                                         /\ account_key acc <> None
                                                                                         /\ (machine_fileSystem mac') p' = Some (files', users', o)
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
                                                                             /\ known_machines a' = add_machine_user (m',u') (known_machines a))
                                                                                              
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
      | File_Directory_Discovery_Local m u p => known_machines a' = known_machines a
                                                /\ (exists (macView: Machine)
                                                           (mac: Machine), (enviroment a) m = Some macView
                                                                                /\ network m = Some mac
                                                                                /\ secrets a' = addSecrets (secrets a) (machine_fileSystem mac) p m u
                                                                                /\ enviroment a' = modify_machine m
                                                                                                                  (machine (machine_services macView)
                                                                                                                           (machine_accounts macView)
                                                                                                                           (updatePaths (machine_fileSystem macView) (machine_fileSystem mac) (getPaths (machine_fileSystem mac) p u))
                                                                                                                           (machine_neighbours macView))
                                                                                                                  (enviroment a))
      | File_Directory_Discovery_Remote m u m' u' k' p' s' => known_machines a' = known_machines a
                                                              /\ (exists (macView': Machine)
                                                                         (mac': Machine), (enviroment a) m' = Some macView'
                                                                                          /\ network m' = Some mac'
                                                                                          /\ secrets a' = addSecrets (secrets a) (machine_fileSystem mac') p' m' u'
                                                                                          /\ enviroment a' = modify_machine m'
                                                                                                                            (machine (machine_services macView')
                                                                                                                                     (machine_accounts macView')
                                                                                                                                     (updatePaths (machine_fileSystem macView') (machine_fileSystem mac') (getPaths (machine_fileSystem mac') p' u'))
                                                                                                                                     (machine_neighbours macView'))
                                                                                                                            (enviroment a))
      | Create_Account m u u' k' l' s => known_machines a' = known_machines a
                                         /\ secrets a' = secrets a
                                         /\ (exists (macView: Machine), (enviroment a) m = Some macView
                                                                        /\ enviroment a' = modify_machine m
                                                                                                          (machine (machine_services macView)
                                                                                                                   (addAccount u' (account s (Some (Some k')) (Some l')) (machine_accounts macView))
                                                                                                                   (machine_fileSystem macView)
                                                                                                                   (machine_neighbours macView))
                                                                                                          (enviroment a))

    end.
    
    Inductive one_step : Attacker -> Technique -> (idMachine -> option Machine) -> Attacker -> Prop :=
      | onestep : forall (a: Attacker) (t: Technique) (network: idMachine -> option Machine) (a': Attacker),
                    valid_network network -> valid_attacker a -> Pre a t -> Post a t network a' -> one_step a t network a'.
                    
    Notation "t ⇒ a ↪ n ↪ a'" := (one_step a t n a') (at level 50).
End Techniques.