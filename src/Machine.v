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
        account_service  : idService; 
        account_key : option (option key); 
        account_privilege : option privilege
      }.
      
  (* Identificador del recurso de un servicio *)
  Inductive logical_identifier : Set := 
    | service_port
    | service_process
    | service_file.

  Definition logical_identifier_eq (l1 l2: logical_identifier) : bool :=
    match l1, l2 with
      | service_port, service_port => true
      | service_port, _ => false
      | _, service_port => false
      | service_process, service_process => true
      | service_process, _ => false
      | _, service_process => false
      | service_file, service_file => true
    end. 
    
  (* Valor asociado del recurso de un servicio (Numero de puerto, numero de proceso o un archivo)*)
  Parameter serviceValue : Set.
  Parameter serviceValue_eq : forall val1 val2 : serviceValue, {val1 = val2} + {val1 <> val2}.

  (* Servicios *)
  Record Service : Set :=
    service {
      logical_ident : logical_identifier;
      value_s : nat (* Deberia ser serviceValue *)
    }.
  
  Definition is_network_service (s: Service) : Prop := (logical_ident s) = service_port.
  (* Rutas del sistema de archivos *)
  Parameter path : Set.
  Parameter path_eq : forall p1 p2 : path, {p1 = p2} + {p1 <> p2}.
  (* Definir un orden parcial, jerarquía de archivos*)
  
  (* Flag que marca los objetivos del atacante *)
  Definition objective := bool.
    
  (* Identificadores de máquinas *)
  Parameter idMachine : Set.
  Parameter idMachine_eq : forall m1 m2 : idMachine, {m1 = m2} + {m1 <> m2}.
  
  (* Exploits conocidos*)
  Parameter idExploit : Set.
  Parameter idExploit_eq : forall e1 e2 : idExploit, {e1 = e2} + {e1 <> e2}.
  
  Parameter Exploits : idService -> list idExploit.
  
  Record Machine : Set :=
    machine {
      machine_services : idService -> option Service;
      machine_accounts : idUser -> option (list Account);
      machine_fileSystem : path -> option (list idUser * objective);
      machine_neighbours : list idMachine;
    }.
    
  Definition network_map := idMachine -> option Machine. 
  
End Machine.