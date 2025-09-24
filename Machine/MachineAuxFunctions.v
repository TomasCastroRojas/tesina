Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

Require Import Tesina.Machine.Machine.

Section MachineAuxOperations.

    Fixpoint add_machine_user (mu: (idMachine * idUser)) (l: list (idMachine * idUser)) : list (idMachine * idUser) :=
      match l with
        | nil => mu::nil
        | (m', u')::l' => let (m,u) := mu in
                          match idMachine_eq m m', idUser_eq u u' with
                            | left _, left _ => l
                            | _, _ => (m', u') :: add_machine_user mu l'
                          end
      end.
    
    Definition modify_machine (m: idMachine) (mac: Machine) (env: idMachine -> option Machine) : idMachine -> option Machine :=
      fun id => match idMachine_eq id m with
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
      fun id => match idUser_eq id u with
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
                          | right _ => cons acc' (oplusAccount acc accs)
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
                          | right _ => cons mac' (addNeighbour mac macs)
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
    
    Fixpoint mem_user (u: idUser) (users: list idUser) : bool :=
      match users with
        | nil => false
        | u'::us => match idUser_eq u u' with
                      | left _ => true
                      | right _ => mem_user u us
                    end
      end.
    
    Fixpoint addSecret (m: idMachine) (p: path) (secrets: list (idMachine * path)) : list (idMachine * path) :=
      match secrets with
        | nil => cons (m, p) nil
        | (m', p'):: secrets' => match idMachine_eq m m', path_eq p p' with
                                  | left _, left _ => secrets
                                  | _, _ => (m', p')::(addSecret m p secrets')
                                 end
      end.
    
    Fixpoint addSecrets' (secrets: list (idMachine * path)) 
                           (secrets_new: list (idMachine * path)) : list (idMachine * path) :=
      match secrets_new with
        | nil => secrets
        | (m, p):: secrets' => addSecrets' (addSecret m p secrets) secrets'
      end.
    
    Fixpoint getSecrets (files: path -> option (list path * list idUser * objective))
                        (subfiles: list path) (m: idMachine) (u: idUser): list (idMachine * path):=
      match subfiles with
        | nil => nil
        | p'::ps => match files p' with
                      | None => getSecrets files ps m u
                      | Some (_, _, false) => getSecrets files ps m u
                      | Some (_, users, true) => if mem_user u users then cons (m, p') (getSecrets files ps m u) else getSecrets files ps m u
                    end
      end.
    
    Definition addSecrets (secrets: list (idMachine * path)) 
                          (files: path -> option (list path * list idUser * objective)) 
                          (p: path) (m: idMachine) (u: idUser): list (idMachine * path):=
      match files p with
        | None => secrets
        | Some (nil, _, _) => secrets
        | Some (subfiles, _, _) => addSecrets' secrets (getSecrets files subfiles m u)
      end.
      
    Fixpoint getPaths' (files: path -> option (list path * list idUser * objective))
                       (subfiles: list path) (u: idUser): list path :=
      match subfiles with
        | nil => nil
        | f::fs => match files f with
                    | None => getPaths' files fs u
                    | Some (_, users, _) => if mem_user u users then cons f (getPaths' files fs u) else getPaths' files fs u
                   end
      end.
    
    Definition getPaths (files: path -> option (list path * list idUser * objective))
                        (p: path) (u: idUser) : list path :=
      match files p with
        | None => nil
        | Some (nil, _, _) => nil
        | Some (subfiles, _, _) => getPaths' files subfiles u
      end.
    
    Fixpoint mem_path (p: path) (paths: list path) : bool :=
      match paths with
        | nil => false
        | p'::ps => match path_eq p p' with
                      | left _ => true
                      | right _ => mem_path p ps
                    end
      end.
    
    Fixpoint addUser (u: idUser) (l: list idUser) : list idUser :=
      match l with
        | nil => cons u nil
        | u'::us => match idUser_eq u u' with
                      | left _ => l
                      | right _ => u'::(addUser u us)
                    end
      end.
    
    Fixpoint mergeUsers (source dest: list idUser) : list idUser :=
      match source with
        | nil => dest
        | u::us => mergeUsers us (addUser u dest)
      end.
      
    Fixpoint addPath (p: path) (l: list path) : list path :=
      match l with
        | nil => cons p nil
        | p'::ps => match path_eq p p' with
                      | left _ => l
                      | right _ => p'::(addPath p ps)
                    end
      end.
    
    Fixpoint mergePaths (source dest: list path) : list path :=
      match source with
        | nil => dest
        | p::ps => mergePaths ps (addPath p dest)
      end.
    
    Definition pathInfo (filesView: path -> option (list path * list idUser * objective))
                        (files: path -> option (list path * list idUser * objective))
                        (p: path) : option (list path * list idUser * objective) :=
      match filesView p, files p with
        | None, None => None
        | None, Some info => Some info
        | Some (ps, us, o), Some (ps', us', o') => Some (mergePaths ps' ps, mergeUsers us' us, o')
        | Some info, None => Some info (* Este caso nunca deberia ocurrir. No es posible que la view tenga mas informacion que la maquina real *)
      end.
    
    Definition updatePaths (filesView: path -> option (list path * list idUser * objective))
                           (files: path -> option (list path * list idUser * objective))
                           (new_paths: list path) : path -> option (list path * list idUser * objective) :=
      fun p' => if mem_path p' new_paths
                then pathInfo filesView files p'
                else filesView p'.
                
End MachineAuxOperations.