Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.

Section TechniquePostCondition.

    Definition Post (a: Attacker) (t: Technique) (network: network_map) (a': Attacker): Prop :=
      match t with
      | Remote_Services m u m' u' k' s => known_machines a' = add_machine_user (m', u') (known_machines a)
                                          /\ secrets a' = secrets a
                                          /\ enviroment a' = enviroment a
      | Exploitation_Remote_Services m u m' s' e => secrets a' = secrets a
                                                    /\ (exists (mac' macView' newMacView':Machine) 
                                                               (acc' newAcc': Account)
                                                               (newAccountsView: list Account)
                                                               (u': idUser), network m' = Some mac'
                                                                             /\ enviroment a m' = Some macView'
                                                                             /\ In acc' (machine_accounts mac')
                                                                             /\ account_user acc' = u'
                                                                             /\ account_service acc' = s'
                                                                             /\ known_machines a' = add_machine_user (m',u') (known_machines a)
                                                                             /\ newAcc' = account u' s' None None
                                                                             /\ newAccountsView = addAccount newAcc' (machine_accounts macView')
                                                                             /\ newMacView' = machine (machine_services macView')
                                                                                                      newAccountsView
                                                                                                      (machine_fileSystem macView')
                                                                                                      (machine_neighbours macView')
                                                                             /\ enviroment a' = modify_machine m'
                                                                                                               newMacView'
                                                                                                               (enviroment a))
(*                                                                                    
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
*)
      | Remote_System_Discovery m u => known_machines a' = known_machines a
                                       /\ secrets a' = secrets a
                                       /\ (exists (macView newMacView mac: Machine)
                                                  (newNeighbours macNeighbours: list idMachine), (enviroment a) m = Some macView
                                                                                    /\ network m = Some mac
                                                                                    /\ macNeighbours = (machine_neighbours mac)
                                                                                    /\ (forall (n: idMachine), In n macNeighbours -> (exists (mac0: Machine), (enviroment a) n = Some mac0))
                                                                                    (* TODO: Agregar condicion que los identificadores agregados deben estar previamente definidos en el mapping de la vista parcial *)
                                                                                    /\ newNeighbours = oplusNeighbours (machine_neighbours macView) macNeighbours
                                                                                    /\ newMacView = machine (machine_services macView)
                                                                                                            (machine_accounts macView)
                                                                                                            (machine_fileSystem macView)
                                                                                                            newNeighbours
                                                                                    /\ enviroment a' = modify_machine m
                                                                                                                        newMacView
                                                                                                                        (enviroment a))
(*
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
*)
      | System_Service_Discovery m u => known_machines a' = known_machines a
                                        /\ secrets a' = secrets a
                                        /\ (exists (mac macView newMacView: Machine)
                                                   (services servicesView servicesNewView: list Service), (enviroment a) m = Some macView
                                                                                                            /\ network m = Some mac
                                                                                                            /\ servicesView = machine_services macView
                                                                                                            /\ services = machine_services mac
                                                                                                            /\ servicesNewView = oplusServices servicesView services
                                                                                                            /\ newMacView = machine servicesNewView
                                                                                                                                    (machine_accounts macView)
                                                                                                                                    (machine_fileSystem macView)
                                                                                                                                    (machine_neighbours macView)
                                                                                                            /\ enviroment a' = modify_machine m newMacView (enviroment a))
(*

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

*)  
    | _ => True                                                                                                        
    end.
    
End TechniquePostCondition.