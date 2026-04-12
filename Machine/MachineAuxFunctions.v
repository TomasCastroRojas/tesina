Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

Require Import Machine.Machine.

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
    
    Fixpoint addAccount (acc: Account) (accounts: list Account) : list Account :=
      match accounts with
        | nil => cons acc nil
        | acc':: accs =>
          match idUser_eq (account_user acc) (account_user acc') with
            | left _ =>
              match account_service acc' with
                | None => cons (account (account_user acc)
                                        (account_service acc)
                                        (account_key acc)
                                        (account_privilege acc))
                               accs
                | Some s' =>
                  match account_service acc with
                    | Some s =>
                      match idService_eq s s' with
                        | left _ => cons (account (account_user acc)
                                                   (account_service acc)
                                                   (account_key acc)
                                                   (account_privilege acc))
                                          accs
                        | right _ => cons acc' (addAccount acc accs)
                      end
                    | None => cons acc' (addAccount acc accs)
                  end
              end
            | right _ => cons acc' (addAccount acc accs)
          end
      end.
    
    Fixpoint oplusAccounts (source dest: list Account) : list Account :=
      match source with
        | nil => dest
        | acc::accs => oplusAccounts accs (addAccount acc dest)
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
 
    Fixpoint addService (s: Service) (l: list Service) : list Service :=
      match l with
        | nil => cons s l
        | s'::l' => match idService_eq (service_value s) (service_value s') with
                      | left _ => l
                      | right _ => cons s' (addService s l')
                    end
      end.

    Fixpoint oplusServices (dest source: list Service) : list Service :=
      match source with
        | nil => dest
        | s::ss => oplusServices (addService s dest) ss
      end.

    Fixpoint addSecret (m: idMachine) (p: path) (secrets: list (idMachine * path)) : list (idMachine * path) :=
      match secrets with
        | nil => cons (m, p) nil
        | (m', p'):: secrets' => match idMachine_eq m m', path_eq p p' with
                                  | left _, left _ => secrets
                                  | _, _ => (m', p')::(addSecret m p secrets')
                                 end
      end.
    
    Fixpoint oplusSecrets (secrets: list (idMachine * path)) 
                           (secrets_new: list (idMachine * path)) : list (idMachine * path) :=
      match secrets_new with
        | nil => secrets
        | (m, p):: secrets' => oplusSecrets (addSecret m p secrets) secrets'
      end.
    
    Fixpoint lookupFile (files: list File) (p: path) (u: idUser) : option File :=
      match files with
        | nil => None
        | f::files' => match path_eq p (file_path f), in_dec idUser_eq u (file_user_access f) with
                        | left _, left _ => Some f
                        | _, _ => lookupFile files' p u
                       end
    end.


    Definition getFiles (files: list File) (p: path) (u: idUser) : list File :=
      match lookupFile files p u with
      | None => nil
      | Some root =>
          let acc_sub_paths :=
            filter (fun p' => match lookupFile files p' u with
                              | Some _ => true
                              | None   => false
                              end)
                   (file_subfiles root) in
          let acc_subs :=
            flat_map (fun p' => match lookupFile files p' u with
                                | None   => nil
                                | Some g => ((file (file_path g) nil
                                                  (file_user_access g)
                                                  (file_objective g))::nil)
                                end)
                     (file_subfiles root) in
          (file (file_path root) acc_sub_paths
                (file_user_access root) (file_objective root))
          :: acc_subs
      end.
    
    Fixpoint getPaths_objectives (files : list File) (m : idMachine) : list (idMachine * path) :=
      match files with
        | nil => nil
        | f :: files' => if (file_objective f) 
                         then cons (m, (file_path f)) (getPaths_objectives files' m)
                         else (getPaths_objectives files' m)
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

    Fixpoint addFile (f: File) (files: list File) : list File :=
      match files with
        | nil => cons f nil
        | f'::files' => match path_eq (file_path f) (file_path f') with
                          | left _ => cons (file (file_path f)
                                                 (mergePaths (file_subfiles f) (file_subfiles f'))
                                                 (mergeUsers (file_user_access f) (file_user_access f'))
                                                 (file_objective f))
                                                 files'
                          | right _ => cons f' (addFile f files')
                        end
      end.

    Fixpoint oplusFiles (source dest: list File) : list File :=
      match source with
        | nil => dest
        | f::source' => oplusFiles source' (addFile f dest)
      end.

    Fixpoint get_accounts_linked_service_with_key (u: idUser) (s: idService) (l: list Account) : list Account :=
      match l with
        | nil => nil
        | a::l' => match (account_service a) with
                    | None => get_accounts_linked_service_with_key u s l'
                    | Some s' => match (idUser_eq u (account_user a)), (idService_eq s s') with
                                  | left _, left _ => cons a (get_accounts_linked_service_with_key u s l')
                                  | _, _ => get_accounts_linked_service_with_key u s l'
                                  end
                  end
      end.
                    
End MachineAuxOperations.