Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

Section Machine.

  (* Nivel de privilegios *)
  Inductive privilege : Set := 
    | low
    | low_star
    | high.
  
  (* Claves de cuentas en la maquina (contraseñas, tokens, etc)*)
  Parameter key : Set.
  Parameter key_eq : forall k1 k2 : key, {k1 = k2} + {k1 <> k2}.

  (* Identificadores de Usuarios *)
  Parameter idUser : Set.
  Parameter idUser_eq : forall u1 u2 : idUser, {u1 = u2} + {u1 <> u2}.

  (* Identificadores de Servicios *)
  Parameter idService : Set.
  Parameter idService_eq : forall s1 s2: idService, {s1 = s2} + {s1 <> s2}.
  Parameter OS: idService.

  (* Cuentas *)
      
  Record Account : Set :=
      account {
        account_user      : idUser;
        account_service   : option idService;
        account_key       : option (option key); 
        account_privilege : option privilege;
      }.
    
  (* Valor asociado del recurso de un servicio (Numero de puerto, numero de proceso o un archivo)*)
  Parameter serviceValue : Set.
  Parameter serviceValue_eq : forall val1 val2 : serviceValue, {val1 = val2} + {val1 <> val2}.

  (* Servicios *)
  Record Service : Set :=
    service {
      service_value : idService;
      service_port : nat;
    }.

  (* Rutas del sistema de archivos *)
  Parameter path : Set.
  Parameter path_eq : forall p1 p2 : path, {p1 = p2} + {p1 <> p2}.

  (* Flag que marca los objetivos del atacante *)
  Definition objective := bool.

  (* Servicios *)
  Record File : Set :=
    file {
      file_path : path;
      file_subfiles : list path;
      file_user_access : list idUser;
      file_objective: objective;
    }.
    
  (* Identificadores de máquinas *)
  Parameter idMachine : Set.
  Parameter idMachine_eq : forall m1 m2 : idMachine, {m1 = m2} + {m1 <> m2}.
  
  (* Exploits conocidos*)
  Parameter idExploit : Set.
  Parameter idExploit_eq : forall e1 e2 : idExploit, {e1 = e2} + {e1 <> e2}.
  
  Parameter Exploits : idService -> list idExploit.
  
  Record Machine : Set :=
    machine {
      machine_services : list Service; (* Servicios registrados *)
      machine_accounts : list Account; (* Usuarios registrado. Un usuario puede estar suscrito a más de un servicio *)
      machine_fileSystem : list File; (* Archivos y directorios de la máquina *)
      machine_neighbours : list idMachine; (* Vecinos *)
    }.
    
  (* Red de máquinas en un sistema *)
  Definition network_map := idMachine -> option Machine. 
  
End Machine.