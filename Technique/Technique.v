Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.

Section Techniques.

  Inductive Technique : Set :=
    (* Lateral Movement *)
    | Remote_Services : idMachine -> idUser -> idMachine -> idUser -> key -> idService -> Technique
    | Exploitation_Remote_Services : idMachine -> idUser -> idMachine -> idService -> idExploit -> Technique
    (* Credential Access *)
    | Unsecured_Credentials : idMachine -> idUser -> idService -> Technique
    | Brute_Force : idMachine -> idUser -> idMachine -> idUser -> idService -> Technique
    (* Privilege Escalation *)
    | Abuse_Elevation_Control_Mechanism : idMachine -> idUser -> Technique
    (* Discovery *)
    | File_Directory_Discovery_Local : idMachine -> idUser -> path -> Technique
    | File_Directory_Discovery_Remote : idMachine -> idUser -> idMachine -> idUser -> key -> path -> idService -> Technique
    | Network_Service_Scanning : idMachine -> idUser -> idMachine -> list nat -> Technique
    | Remote_System_Discovery : idMachine -> idUser -> Technique
    | Account_Discovery_Local : idMachine -> idUser -> idService -> Technique
    | Account_Discovery_Remote : idMachine -> idUser -> idMachine -> idUser -> key -> idService -> Technique
    | System_Service_Discovery : idMachine -> idUser -> Technique
    (* Persistence *)
    | Create_Account : idMachine -> idUser -> idUser -> key -> privilege -> idService -> Technique. 
    
    
End Techniques.