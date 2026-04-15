Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineView.

Section muSE.

  Record Attacker : Set :=
    attacker {
      known_machines : list (idMachine * idUser); (* Conjunto de acceso a máquinas *)
      secrets : list (idMachine * path); (* Conjunto de secretos obtenidos *)
      enviroment : idMachine -> option Machine; (* Vista parcial *) (* Puede diferir entre atacantes *)
      mastered_exploits : list (idService * idExploit) (* Exploits que el atacante conoce y puede aplicar, estatico durante la campana *)
    }.
  
  
  (* Relaciona known_machines con enviroment de un Attacker *)
  (* Para cada par de identificador de máquina y usuario que esta en el area de propagación del atacante (known_machines),
     entonces ese identificador esta definido en la vista parcial y además hay una cuenta registrada con ese usuario *)
  Definition valid_attacker_i (a: Attacker) : Prop :=
    forall (m:idMachine) (u:idUser), 
      (In (m,u) (known_machines a)) -> 
        (exists (mac:Machine), (enviroment a) m = Some mac /\ registered_users mac u).

  (* Relaciona secrets con enviroment de un Attacker *)
  (* Para cada par de identificador de máquina y path que el atacante obtuvo como secreto (secrets),
     entonces ese identificador esta definido en las vistas parciales y el path es una ruta registrada/válida en esa máquina *)
  Definition valid_attacker_ii (a: Attacker) : Prop :=
    forall (m:idMachine) (p:path), 
      (In (m,p) (secrets a)) -> 
        (exists (mac:Machine), (enviroment a) m = Some mac /\ (registered_paths mac) p).
                                                                                     
  (* Enviroment válido de un atacante *)
  (* Topología válida y además para toda máquina que tiene una vista parcial definida, entonces esa máquina es válida *)
  Definition valid_attacker_iii (a: Attacker) : Prop :=
    valid_network (enviroment a).
    
  (* Relaciona la vista parcial del atacante con la red concreta objetivo *)
  (* Toda máquina con una vista parcial definida tambien esta definida en la red concreta 
     y además las máquinas estan relacionadas (una es 'subconjunto' de la otra)*)
  Definition valid_attacker_iv (a: Attacker) (network: network_map) : Prop :=
    is_networkView (enviroment a) (network).
  
  Definition valid_attacker (a: Attacker) (network: network_map) : Prop :=
    valid_attacker_i a /\ valid_attacker_ii a /\ valid_attacker_iii a /\ valid_attacker_iv a network.

  (* ===== Predicados de completitud de secretos ===== *)

  (* Un archivo en la ruta p de la maquina mid es un objetivo del atacante en la red n *)
  Definition is_objective (n: network_map) (mid: idMachine) (p: path) : Prop :=
    exists (mac: Machine) (f: File),
      n mid = Some mac
      /\ In f (machine_fileSystem mac)
      /\ file_path f = p
      /\ file_objective f = true.

  (* La red contiene al menos un archivo marcado como objetivo *)
  Definition network_has_objectives (n: network_map) : Prop :=
    exists (mid: idMachine) (p: path), is_objective n mid p.

  (* El atacante conoce todos los secretos de la red:
     para toda maquina y todo archivo objetivo, el par (maquina, ruta) esta en secrets *)
  Definition all_secrets_known (a: Attacker) (n: network_map) : Prop :=
    forall (mid: idMachine) (mac: Machine) (f: File),
      n mid = Some mac ->
      In f (machine_fileSystem mac) ->
      file_objective f = true ->
      In (mid, file_path f) (secrets a).

  (* ===== Alcanzabilidad topologica ===== *)

  (* Una maquina mid es alcanzable desde el atacante si:
     - el atacante conoce algun usuario en esa maquina, o
     - existe una maquina alcanzable que tiene a mid como vecino *)
  Inductive reachable (n: network_map) (a: Attacker) : idMachine -> Prop :=
    | reachable_known : forall (mid: idMachine) (u: idUser),
        In (mid, u) (known_machines a) ->
        reachable n a mid
    | reachable_step : forall (mid mid': idMachine) (mac: Machine),
        reachable n a mid ->
        n mid = Some mac ->
        In mid' (machine_neighbours mac) ->
        reachable n a mid'.

  (* ===== Condiciones necesarias para descubrir todos los secretos ===== *)

  (* Para todo objetivo en la red, la maquina que lo aloja es alcanzable
     y existe un usuario con acceso al archivo y cuenta registrada en la maquina *)
  Definition can_discover_all_secrets (a: Attacker) (n: network_map) : Prop :=
    forall (mid: idMachine) (mac: Machine) (f: File),
      n mid = Some mac ->
      In f (machine_fileSystem mac) ->
      file_objective f = true ->
      reachable n a mid
      /\ (exists (u: idUser),
            In u (file_user_access f)
            /\ registered_users mac u).

  (* ===== Predicados de imposibilidad ===== *)

  (* Existe un objetivo cuya maquina es inalcanzable desde el atacante (barrera topologica) *)
  Definition exists_unreachable_secret (a: Attacker) (n: network_map) : Prop :=
    exists (mid: idMachine) (mac: Machine) (f: File),
      n mid = Some mac
      /\ In f (machine_fileSystem mac)
      /\ file_objective f = true
      /\ ~ reachable n a mid.

  (* Existe un objetivo al que ningun usuario conocido por el atacante tiene acceso (barrera de permisos).
     Nota: este predicado depende del estado actual del atacante y puede dejar de cumplirse
     si el atacante gana nuevos usuarios en la maquina via tecnicas de movimiento lateral. *)
  Definition exists_inaccessible_secret (a: Attacker) (n: network_map) : Prop :=
    exists (mid: idMachine) (mac: Machine) (f: File),
      n mid = Some mac
      /\ In f (machine_fileSystem mac)
      /\ file_objective f = true
      /\ (forall (u: idUser), In (mid, u) (known_machines a) ->
            ~ In u (file_user_access f)).

  (* Un usuario tiene credenciales utilizables en una maquina si tiene al menos
     una cuenta con servicio y clave definidos en esa maquina.
     NOTA: bajo valid_concrete_network, accounts_complete garantiza
     account_service <> None y account_key <> None para TODA cuenta,
     por lo que este predicado es trivialmente verdadero para todo usuario registrado.
     Para un analisis mas preciso de las barreras de acceso, usar
     obtainable_user de AttackerCapacity/AttackerAccess.v, que distingue
     clave real (Some (Some k)) de clave indefinida (Some None). *)
  Definition has_credentials (mac: Machine) (u: idUser) : Prop :=
    exists (acc: Account),
      In acc (machine_accounts mac)
      /\ account_user acc = u
      /\ account_service acc <> None
      /\ account_key acc <> None.

  (* Existe un objetivo en una maquina alcanzable tal que ningun usuario con acceso
     al archivo tiene credenciales en la red concreta (barrera de credenciales).
     A diferencia de exists_inaccessible_secret, este predicado es una propiedad
     estatica de la red concreta: no depende del estado actual del atacante sino
     de la ausencia estructural de credenciales para los usuarios con acceso al archivo.
     NOTA: este predicado es insatisfacible bajo valid_concrete_network + valid_machine
     porque has_credentials es trivialmente verdadero (ver nota en has_credentials).
     El predicado exists_permanently_inaccessible_secret de
     AttackerCapacity/AttackerAccess.v lo reemplaza con un analisis mas preciso
     que distingue credenciales reales de la ausencia de exploits. *)
  Definition exists_credential_protected_secret (a: Attacker) (n: network_map) : Prop :=
    exists (mid: idMachine) (mac: Machine) (f: File),
      n mid = Some mac
      /\ In f (machine_fileSystem mac)
      /\ file_objective f = true
      /\ reachable n a mid
      /\ (forall (u: idUser), In u (file_user_access f) -> ~ has_credentials mac u).

End muSE.