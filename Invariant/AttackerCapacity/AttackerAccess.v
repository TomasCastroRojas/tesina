Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineView.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniqueOneStep.

Section AttackerAccess.

  (* ===== Predicados de credenciales refinados ===== *)

  (* Credencial con clave real: requiere account_key = Some (Some k),
     estrictamente mas fuerte que has_credentials (que solo pide <> None).
     Esto es lo que Remote_Services realmente necesita como precondicion.
     El parametro s indica el servicio asociado a la cuenta. *)
  Definition has_real_key_credentials (mac: Machine) (u: idUser) (s: idService) : Prop :=
    exists (acc: Account) (k: key),
      In acc (machine_accounts mac)
      /\ account_user acc = u
      /\ account_service acc = Some s
      /\ account_key acc = Some (Some k).

  (* ===== Predicados de obtenibilidad ===== *)

  (* Una maquina tiene un exploit que el atacante puede usar:
     el exploit esta en la lista de exploits de la maquina
     y tambien en la lista de exploits dominados por el atacante.
     Ambas listas son estaticas durante la campaña de ataque. *)
  Definition has_usable_exploit (mac: Machine) (a: Attacker) : Prop :=
    exists (e: idExploit) (s: idService),
      In (s, e) (machine_exploits mac)
      /\ In (s, e) (mastered_exploits a).

  (* Usuario obtenible via Remote_Services en la red concreta:
     existe una cuenta para u en la maquina mid con un servicio
     y una clave real (Some (Some k)). *)
  Definition obtainable_via_remote_services (n: network_map) (mid: idMachine) (u: idUser) : Prop :=
    exists (mac: Machine) (s: idService),
      n mid = Some mac
      /\ has_real_key_credentials mac u s.

  (* Usuario obtenible via Exploitation_Remote_Services en la red concreta:
     la maquina tiene un exploit aprovechable por el atacante,
     existe un servicio s en la maquina, y u tiene una cuenta
     asociada a ese servicio. No se necesita clave porque la explotacion
     la omite. *)
  Definition obtainable_via_exploitation (n: network_map) (a: Attacker) (mid: idMachine) (u: idUser) : Prop :=
    exists (mac: Machine) (s: idService) (acc: Account) (serv: Service),
      n mid = Some mac
      /\ In serv (machine_services mac)
      /\ service_value serv = s
      /\ has_usable_exploit mac a
      /\ In acc (machine_accounts mac)
      /\ account_user acc = u
      /\ account_service acc = Some s.

  (* Un usuario es obtenible en una maquina por alguna tecnica
     de movimiento lateral: ya sea por credenciales reales
     (Remote_Services) o por explotacion de servicios
     (Exploitation_Remote_Services).
     Nota: obtainable_via_exploitation depende de mastered_exploits a,
     pero como es estatico durante la campana, el predicado es
     efectivamente una propiedad de la red concreta + atacante inicial. *)
  Definition obtainable_user (n: network_map) (a: Attacker) (mid: idMachine) (u: idUser) : Prop :=
    obtainable_via_remote_services n mid u
    \/ obtainable_via_exploitation n a mid u.

  (* ===== Clasificacion de inaccesibilidad ===== *)

  (* La inaccesibilidad de un secreto puede ser rota:
     existe un objetivo actualmente inaccesible (ningun usuario conocido
     tiene acceso al archivo), pero la maquina es alcanzable y existe
     un usuario con acceso al archivo que es obtenible via movimiento
     lateral. Es un predicado estatico sobre la red concreta:
     si se cumple, existe un multi_step que rompe la inaccesibilidad. *)
  Definition inaccessibility_breakable (a: Attacker) (n: network_map) : Prop :=
    exists (mid: idMachine) (mac: Machine) (f: File),
      n mid = Some mac
      /\ In f (machine_fileSystem mac)
      /\ file_objective f = true
      /\ reachable n a mid
      /\ (forall (u: idUser), In (mid, u) (known_machines a) ->
            ~ In u (file_user_access f))
      /\ (exists (u: idUser),
            In u (file_user_access f)
            /\ obtainable_user n a mid u).

  (* Un secreto es permanentemente inaccesible: la maquina es alcanzable
     pero ningun usuario con acceso al archivo puede ser obtenido
     por ninguna tecnica de movimiento lateral.
     A diferencia de exists_credential_protected_secret (que usa
     has_credentials y es insatisfacible en redes concretas validas),
     este predicado distingue credenciales reales de la ausencia
     de exploits, proporcionando una barrera genuina. *)
  Definition exists_permanently_inaccessible_secret (a: Attacker) (n: network_map) : Prop :=
    exists (mid: idMachine) (mac: Machine) (f: File),
      n mid = Some mac
      /\ In f (machine_fileSystem mac)
      /\ file_objective f = true
      /\ reachable n a mid
      /\ (forall (u: idUser),
            In u (file_user_access f) ->
            ~ obtainable_user n a mid u).

  (* ===== Lema auxiliar clave ===== *)

  (* Cuando one_step agrega un nuevo par (mid, u) a known_machines,
     u debe ser obtainable_user en la red concreta.
     Se prueba por analisis de casos sobre la tecnica t:
     - Remote_Services/Exploitation_Remote_Services: Post da
       add_machine_user (m', u') y Pre conecta con la red concreta
       via valid_attacker_iv.
     - Demas tecnicas activas: Post da known_machines a' = known_machines a,
       contradiciendo la hipotesis de que (mid, u) es nuevo. *)
  Lemma one_step_adds_obtainable_user :
    forall (a a': Attacker) (t: Technique) (n: network_map)
           (mid: idMachine) (u: idUser),
      valid_concrete_network n ->
      valid_attacker a n ->
      one_step a t n a' ->
      In (mid, u) (known_machines a') ->
      ~ In (mid, u) (known_machines a) ->
      obtainable_user n a mid u.
  Proof.
  Admitted.

  (* ===== Teoremas de persistencia ===== *)

  (* Si un secreto es permanentemente inaccesible,
     la propiedad exists_inaccessible_secret se preserva tras multi_step.
     Prueba por induccion sobre multi_step:
     - Base: trivial (a = a').
     - Paso: por one_step_adds_obtainable_user, todo nuevo (mid, u)
       satisface obtainable_user. Pero la hipotesis dice que ningun
       usuario con acceso al archivo es obtenible. Ergo el nuevo
       usuario no tiene acceso al archivo y la inaccesibilidad se preserva. *)
  Theorem permanently_inaccessible_secret_persists :
    forall (a a': Attacker) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      multi_step a n a' ->
      exists_permanently_inaccessible_secret a n ->
      exists_inaccessible_secret a' n.
  Proof.
  Admitted.

  (* La estructura de inaccesibilidad permanente tambien persiste:
     el predicado exists_permanently_inaccessible_secret se preserva
     porque obtainable_user es una propiedad de la red concreta
     y mastered_exploits (estatico), y reachable persiste
     bajo multi_step (probado en AttackerReach.v). *)
  Theorem permanently_inaccessible_persists_strong :
    forall (a a': Attacker) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      multi_step a n a' ->
      exists_permanently_inaccessible_secret a n ->
      exists_permanently_inaccessible_secret a' n.
  Proof.
  Admitted.

  (* ===== Teoremas de imposibilidad ===== *)

  (* Si hay un secreto permanentemente inaccesible, el atacante
     nunca puede conocer todos los secretos de la red.
     El atacante necesita ejecutar File_Directory_Discovery_Local
     para agregar secretos, pero esa tecnica requiere un usuario
     con acceso al archivo en known_machines. Si tal usuario
     no es obtenible, el secreto queda fuera de alcance. *)
  Theorem permanently_inaccessible_blocks_all_secrets :
    forall (a a': Attacker) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      multi_step a n a' ->
      exists_permanently_inaccessible_secret a n ->
      ~ all_secrets_known a' n.
  Proof.
  Admitted.

  (* Cualquiera de las dos barreras permanentes impide conocer
     todos los secretos:
     - Barrera topologica (exists_unreachable_secret): la maquina
       es inalcanzable, persistente bajo multi_step.
     - Barrera de credenciales/exploits (exists_permanently_inaccessible_secret):
       la maquina es alcanzable pero ningun usuario con acceso
       al archivo es obtenible.
     Se compone con los teoremas de AttackerReach.v y los de arriba. *)
  Theorem any_barrier_blocks_all_secrets :
    forall (a a': Attacker) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      multi_step a n a' ->
      (exists_unreachable_secret a n
       \/ exists_permanently_inaccessible_secret a n) ->
      ~ all_secrets_known a' n.
  Proof.
  Admitted.

  (* ===== Teorema de alcanzabilidad (existencial) ===== *)

  (* Si inaccessibility_breakable se cumple, existe un multi_step
     tras el cual el atacante gana un usuario con acceso al archivo
     objetivo. Este es el teorema mas dificil de probar porque requiere
     construir la traza de descubrimiento completa:
     Remote_System_Discovery -> System_Service_Discovery ->
     Unsecured_Credentials -> Remote_Services/Exploitation. *)
  Theorem breakable_inaccessibility_can_be_broken :
    forall (a: Attacker) (n: network_map),
      valid_concrete_network n ->
      valid_attacker a n ->
      inaccessibility_breakable a n ->
      exists (a': Attacker),
        multi_step a n a'
        /\ exists (mid: idMachine) (mac: Machine) (f: File) (u: idUser),
             n mid = Some mac
             /\ In f (machine_fileSystem mac)
             /\ file_objective f = true
             /\ In (mid, u) (known_machines a')
             /\ In u (file_user_access f).
  Proof.
  Admitted.

End AttackerAccess.
