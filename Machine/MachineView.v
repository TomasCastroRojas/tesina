Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

Require Import Machine.Machine.

Section MachineView.

  (* Una lista de servicios es subconjunto de otra si todo servicio de la primera esta en la segunda *)
  Definition subset_services (services1 services2: list Service) : Prop :=
    forall (s: Service), In s services1-> In s services2.

  (* Una cuenta es vista parcial de otra si comparten usuario y sus campos opcionales coinciden o son None en la vista *)
  Definition account_view (acc1 acc2: Account) : Prop :=
    account_user acc1 = account_user acc2
    /\ (account_service acc1 = None \/ account_service acc1 = account_service acc2)
    /\ (account_key acc1 = None \/ account_key acc1 = account_key acc2)
    /\ (account_privilege acc1 = None \/ account_privilege acc1 = account_privilege acc2).

  (* Un archivo es vista parcial de otro si comparten ruta y objetivo, y sus subarchivos y usuarios de acceso son subconjuntos *)
  Definition file_view (file1 file2: File) : Prop :=
    file_path file1 = file_path file2
    /\ file_objective file1 = file_objective file2
    /\ (forall (p: path), In p (file_subfiles file1) -> In p (file_subfiles file2))
    /\ (forall (u: idUser), In u (file_user_access file1) -> In u (file_user_access file2)).
  
  (* Una lista de cuentas es subconjunto de otra si toda cuenta de la primera esta en la segunda o tiene una vista parcial en ella *)
  Definition subset_accounts (l1 l2: list Account) : Prop :=
    forall (acc: Account), In acc l1 -> (In acc l2 \/ (exists (acc': Account), In acc' l2 /\ account_view acc acc')).

  (* Una lista de archivos es subconjunto de otra si todo archivo de la primera esta en la segunda o tiene una vista parcial en ella *)
  Definition subset_files (files1 files2: list File) : Prop :=
    forall (f: File), In f files1 -> (In f files2 \/ (exists (f': File), In f' files2 /\ file_view f f')).

  (* Una lista de vecinos es subconjunto de otra si todo identificador de maquina de la primera esta en la segunda *)
  Definition subset_neighbours (l1 l2: list idMachine) : Prop :=
    forall (m: idMachine), In m l1 -> In m l2.

  (* Una lista de exploits es subconjunto de otra si todo exploit de la primera esta en la segunda *)
  Definition subset_exploits (l1 l2: list (idService * idExploit)) : Prop :=
    forall (s: idService) (e: idExploit), In (s, e) l1 -> In (s, e) l2.

  (* Una maquina es vista parcial de otra si sus servicios, cuentas, archivos, vecinos y exploits son subconjuntos de los de la otra *)
  Definition is_machineView (m1 m2: Machine) : Prop :=
    subset_services (machine_services m1) (machine_services m2)
    /\ subset_accounts (machine_accounts m1) (machine_accounts m2)
    /\ subset_files (machine_fileSystem m1) (machine_fileSystem m2)
    /\ subset_neighbours (machine_neighbours m1) (machine_neighbours m2)
    /\ subset_exploits (machine_exploits m1) (machine_exploits m2).

  (* Una red es vista parcial de otra si toda maquina definida en la primera tambien lo esta
     en la segunda y la primera es vista parcial de la segunda en ese identificador.
     Esto expresa la inclusion de dominio enviroment ⊆ network ademas de la relacion punto a punto:
     el atacante no tiene vistas de maquinas inexistentes en la red concreta. *)
  Definition is_networkView (net1 net2: network_map) : Prop :=
    forall (m: idMachine) (mac1: Machine),
      net1 m = Some mac1 ->
      exists (mac2: Machine),
        net2 m = Some mac2
        /\ is_machineView mac1 mac2.


End MachineView.