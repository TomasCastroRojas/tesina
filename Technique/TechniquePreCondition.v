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
                                          /\ (exists (acc : Account) 
                                                     (mac': Machine), (enviroment a) m' = Some mac'
                                                                      /\ In acc (machine_accounts mac')
                                                                      /\ account_user acc = u'
                                                                      /\ account_service acc = s
                                                                      /\ account_key acc = Some (Some k'))
      | Exploitation_Remote_Services m u m' s' e => (In (m,u) (known_machines a))
                                                    /\ (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                               /\ In  m' (machine_neighbours mac))
                                                    /\ (exists (serv : Service) 
                                                               (mac': Machine), (enviroment a) m' = Some mac' 
                                                                                /\ In serv (machine_services mac')
                                                                                /\ service_value serv = s'
                                                                                /\ (In e (Exploits s'))) (* Exploits conocido asociados a un servicio *)
      | Unsecured_Credentials m u s => (In (m,u) (known_machines a))
                                       /\ (exists (mac: Machine)
                                                  (acc : Account)
                                                  (k : key)
                                                  (l: privilege), (enviroment a) m = Some mac
                                                                  /\ In acc (machine_accounts mac)
                                                                  /\ account_user acc = u
                                                                  /\ account_service acc = s
                                                                  /\ account_privilege acc = Some l
                                                                  /\ account_key acc = Some (Some k))
      | Brute_Force m u m' u' s' => (In (m,u) (known_machines a))
                                    /\ (exists (mac: Machine), (enviroment a) m = Some mac 
                                                               /\ In  m' (machine_neighbours mac))
                                    /\ (exists (acc : Account) 
                                               (mac': Machine) 
                                               (l: privilege), (enviroment a) m' = Some mac'
                                                               /\ In acc (machine_accounts mac')
                                                               /\ account_user acc = u
                                                               /\ account_service acc = s'
                                                               /\ account_key acc = None
                                                               /\ account_privilege acc = Some l)
 
      | Abuse_Elevation_Control_Mechanism m u => (In (m,u) (known_machines a))
                                                 /\ (exists (acc : Account) 
                                                            (mac: Machine)
                                                            (k : key), (enviroment a) m = Some mac
                                                                       /\ In acc (machine_accounts mac)
                                                                       /\ account_user acc = u
                                                                       /\ account_service acc = OS
                                                                       /\ account_key acc = Some (Some k)
                                                                       /\ account_privilege acc = Some low_star)
      | File_Directory_Discovery_Local m u p => (In (m,u) (known_machines a))
                                                /\ (exists (mac: Machine)
                                                           (f: File)
                                                           (acc: Account), (enviroment a) m = Some mac
                                                                      /\ In f (machine_fileSystem mac)
                                                                      /\ file_path f = p
                                                                      /\ In u (file_user_access f)
                                                                      /\ In acc (machine_accounts mac)
                                                                      /\ account_user acc = u)
      | File_Directory_Discovery_Remote m u m' u' k' p' s' => (In (m,u) (known_machines a))
                                                              /\ (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                                         /\ In m' (machine_neighbours mac))
                                                              /\ (exists (mac': Machine) 
                                                                         (serv': Service)
                                                                         (f: File)
                                                                         (acc : Account), (enviroment a) m' = Some mac'
                                                                                          /\ In serv' (machine_services mac') 
                                                                                          /\ service_value serv' = s'
                                                                                          /\ In acc (machine_accounts mac')
                                                                                          /\ account_user acc = u'
                                                                                          /\ account_service acc = s'
                                                                                          /\ account_key acc <> None
                                                                                          /\ In f (machine_fileSystem mac')
                                                                                          /\ file_path f = p'
                                                                                          /\ In u' (file_user_access f))
      | Network_Service_Scanning m u m' l => (In (m,u) (known_machines a))
                                             /\ (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                        /\ In m' (machine_neighbours mac))
      | Remote_System_Discovery m u => In (m,u) (known_machines a)
      | Account_Discovery_Local m u s => In (m,u) (known_machines a)
                                         /\ (exists (mac: Machine)
                                                    (serv: Service)
                                                    (acc : Account)
                                                    (k: key)
                                                    (l: privilege), (enviroment a) m = Some mac
                                                                    /\ In serv (machine_services mac)
                                                                    /\ service_value serv = s
                                                                    /\ In acc (machine_accounts mac)
                                                                    /\ account_user acc = u
                                                                    /\ account_service acc = s
                                                                    /\ account_key acc = Some (Some k)
                                                                    /\ account_privilege acc = Some l)
      | Account_Discovery_Remote m u m' u' k' s' => (In (m,u) (known_machines a))
                                                    /\ (exists (mac: Machine), (enviroment a) m = Some mac 
                                                                               /\ In m' (machine_neighbours mac))
                                                    /\ (exists (mac': Machine) 
                                                               (serv': Service)
                                                               (acc' : Account)
                                                               (l: privilege), (enviroment a) m' = Some mac'
                                                                               /\ In serv' (machine_services mac')
                                                                               /\ service_value serv' = s'
                                                                               /\ In acc' (machine_accounts mac')
                                                                               /\ account_user acc' = u'
                                                                               /\ account_service acc' = s'
                                                                               /\ account_key acc' <> None
                                                                               /\ account_privilege acc' = Some l)
      | System_Service_Discovery m u => In (m,u) (known_machines a)
    end.

End TechniquePreCondition.