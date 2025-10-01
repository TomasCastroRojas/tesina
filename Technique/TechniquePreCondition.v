Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.

Section TechniquePreCondition.

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

End TechniquePreCondition.