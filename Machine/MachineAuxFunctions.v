Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

Require Import Machine.Machine.

Section MachineAuxOperations.

  (* ===== Operaciones sobre known_machines (pares idMachine * idUser) ===== *)

    (* Agrega el par (idMachine, idUser) a la lista si no existe ya un par identico.
       Si el par ya esta presente, la lista no se modifica. *)
    Fixpoint add_machine_user (mu: (idMachine * idUser)) (l: list (idMachine * idUser)) : list (idMachine * idUser) :=
      match l with
        | nil => mu::nil
        | (m', u')::l' => let (m,u) := mu in
                          match idMachine_eq m m', idUser_eq u u' with
                            | left _, left _ => l
                            | _, _ => (m', u') :: add_machine_user mu l'
                          end
      end.
    
  (* ===== Operaciones sobre el entorno (network_map) ===== *)

    (* Actualiza el entorno sobreescribiendo la entrada del identificador m con la maquina mac.
       Para cualquier otro identificador, el entorno permanece sin cambios. *)
    Definition modify_machine (m: idMachine) (mac: Machine) (env: idMachine -> option Machine) : idMachine -> option Machine :=
      fun id => match idMachine_eq id m with
                  | left _ => Some mac
                  | right _ => env id
                end.
    
  (* ===== Operaciones sobre cuentas (Account) ===== *)

    (* Agrega una cuenta a la lista. Si ya existe una cuenta del mismo usuario y servicio,
       la reemplaza. Si el usuario existe pero con distinto servicio, agrega la nueva cuenta
       sin eliminar las existentes. *)
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
    
    (* Fusiona dos listas de cuentas incorporando cada cuenta de source en dest
       mediante addAccount. El resultado contiene todas las cuentas de ambas listas,
       con las de source sobreescribiendo las de dest en caso de conflicto. *)
    Fixpoint oplusAccounts (source dest: list Account) : list Account :=
      match source with
        | nil => dest
        | acc::accs => oplusAccounts accs (addAccount acc dest)
      end.
      
  (* ===== Operaciones sobre vecinos (idMachine) ===== *)

    (* Agrega un identificador de maquina a la lista de vecinos si no esta ya presente.
       Si ya existe, la lista no se modifica. *)
    Fixpoint addNeighbour (mac : idMachine) (neighbours: list idMachine) : list idMachine :=
      match neighbours with
        | nil => cons mac nil
        | mac'::macs => match idMachine_eq mac mac' with
                          | left _ => neighbours
                          | right _ => cons mac' (addNeighbour mac macs)
                        end
      end.
    
    (* Fusiona dos listas de vecinos incorporando cada elemento de source en dest
       mediante addNeighbour. El resultado es la union de ambas listas sin duplicados. *)
    Fixpoint oplusNeighbours (source dest: list idMachine) : list idMachine :=
      match source with
        | nil => dest
        | mac::macs => oplusNeighbours macs (addNeighbour mac dest)
      end.
 
  (* ===== Operaciones sobre servicios (Service) ===== *)

    (* Agrega un servicio a la lista si no existe ya uno con el mismo idService.
       Si ya existe un servicio con ese identificador, la lista no se modifica. *)
    Fixpoint addService (s: Service) (l: list Service) : list Service :=
      match l with
        | nil => cons s l
        | s'::l' => match idService_eq (service_value s) (service_value s') with
                      | left _ => l
                      | right _ => cons s' (addService s l')
                    end
      end.

    (* Fusiona dos listas de servicios incorporando cada elemento de source en dest
       mediante addService. El resultado es la union de ambas listas sin duplicados de idService. *)
    Fixpoint oplusServices (dest source: list Service) : list Service :=
      match source with
        | nil => dest
        | s::ss => oplusServices (addService s dest) ss
      end.

    Definition is_network_service (s: Service) : Prop :=
      match (service_exposure s) with
        | ExpPort _ => True
        | _ => False
      end.
  
  (* ===== Operaciones sobre secretos (idMachine * path) ===== *)

    (* Agrega el par (idMachine, path) a la lista de secretos si no existe ya un par identico.
       Si el par ya esta presente, la lista no se modifica. *)
    Fixpoint addSecret (m: idMachine) (p: path) (secrets: list (idMachine * path)) : list (idMachine * path) :=
      match secrets with
        | nil => cons (m, p) nil
        | (m', p'):: secrets' => match idMachine_eq m m', path_eq p p' with
                                  | left _, left _ => secrets
                                  | _, _ => (m', p')::(addSecret m p secrets')
                                 end
      end.
    
    (* Fusiona dos listas de secretos incorporando cada par de secrets_new en secrets
       mediante addSecret. El resultado es la union de ambas listas sin duplicados. *)
    Fixpoint oplusSecrets (secrets: list (idMachine * path))
                           (secrets_new: list (idMachine * path)) : list (idMachine * path) :=
      match secrets_new with
        | nil => secrets
        | (m, p):: secrets' => oplusSecrets (addSecret m p secrets) secrets'
      end.
    
  (* ===== Operaciones sobre archivos (File) ===== *)

    (* Busca en la lista el primer archivo con ruta p al que el usuario u tiene acceso.
       Devuelve Some f si lo encuentra, o None si no existe tal archivo. *)
    Fixpoint lookupFile (files: list File) (p: path) (u: idUser) : option File :=
      match files with
        | nil => None
        | f::files' => match path_eq p (file_path f), in_dec idUser_eq u (file_user_access f) with
                        | left _, left _ => Some f
                        | _, _ => lookupFile files' p u
                       end
    end.


    (* Dado un archivo raiz en la ruta p accesible por u, devuelve ese archivo junto con
       los subarchivos a los que u tambien tiene acceso. Los subarchivos se devuelven sin
       sus propias subrutas (file_subfiles = nil) para representar solo la entrada del directorio. *)
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
    
    (* Recorre la lista de archivos y devuelve los pares (m, path) correspondientes
       a los archivos marcados como objetivo (file_objective = true). *)
    Fixpoint getPaths_objectives (files : list File) (m : idMachine) : list (idMachine * path) :=
      match files with
        | nil => nil
        | f :: files' => if (file_objective f) 
                         then cons (m, (file_path f)) (getPaths_objectives files' m)
                         else (getPaths_objectives files' m)
      end.

  (* ===== Funciones auxiliares para addFile (listas de usuarios y rutas) ===== *)

    (* Agrega un usuario a la lista si no esta ya presente. *)
    Fixpoint addUser (u: idUser) (l: list idUser) : list idUser :=
      match l with
        | nil => cons u nil
        | u'::us => match idUser_eq u u' with
                      | left _ => l
                      | right _ => u'::(addUser u us)
                    end
      end.
    (* Fusiona dos listas de usuarios produciendo la union sin duplicados. *)
    Fixpoint mergeUsers (source dest: list idUser) : list idUser :=
      match source with
        | nil => dest
        | u::us => mergeUsers us (addUser u dest)
      end.
      
    (* Agrega una ruta a la lista si no esta ya presente. *)
    Fixpoint addPath (p: path) (l: list path) : list path :=
      match l with
        | nil => cons p nil
        | p'::ps => match path_eq p p' with
                      | left _ => l
                      | right _ => p'::(addPath p ps)
                    end
      end.
    
    (* Fusiona dos listas de rutas produciendo la union sin duplicados. *)
    Fixpoint mergePaths (source dest: list path) : list path :=
      match source with
        | nil => dest
        | p::ps => mergePaths ps (addPath p dest)
      end.

  (* addFile y oplusFiles usan addUser/mergeUsers y addPath/mergePaths para fusionar archivos con la misma ruta *)

    (* Agrega un archivo a la lista. Si ya existe un archivo con la misma ruta, fusiona
       sus subrutas y usuarios de acceso mediante mergePaths y mergeUsers respectivamente,
       conservando el flag objetivo del archivo entrante. *)
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

    (* Fusiona dos listas de archivos incorporando cada archivo de source en dest
       mediante addFile. Archivos con la misma ruta quedan fusionados en el resultado. *)
    Fixpoint oplusFiles (source dest: list File) : list File :=
      match source with
        | nil => dest
        | f::source' => oplusFiles source' (addFile f dest)
      end.

  (* ===== Consultas sobre cuentas ===== *)

    (* Devuelve todas las cuentas de la lista que pertenecen al usuario u y estan vinculadas
       al servicio s. Se usan para obtener las credenciales del atacante para un servicio dado. *)
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

    Fixpoint get_accounts_linked_service_without_key (u: idUser) (s: idService) (l: list Account) : list Account :=
      match l with
        | nil => nil
        | a::l' => match (account_service a) with
                    | None => get_accounts_linked_service_without_key u s l'
                    | Some s' => match (idUser_eq u (account_user a)), (idService_eq s s') with
                                  | left _, left _ => get_accounts_linked_service_without_key u s l'
                                  | right _, left _ => cons (account (account_user a) (Some s) None (account_privilege a)) (get_accounts_linked_service_without_key u s l')
                                  | _, _ => get_accounts_linked_service_without_key u s l'
                                  end
                  end
      end.
                    
End MachineAuxOperations.