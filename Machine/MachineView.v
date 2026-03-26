Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.EqNat.

Require Import Machine.Machine.

Section MachineView.

  Definition subset_services (services1 services2: list Service) : Prop :=
    forall (s: Service), In s services1-> In s services2.

  Definition account_view (acc1 acc2: Account) : Prop :=
    account_user acc1 = account_user acc2
    /\ (account_service acc1 = None \/ account_service acc1 = account_service acc2)
    /\ (account_key acc1 = None \/ account_key acc1 = account_key acc2)
    /\ (account_privilege acc1 = None \/ account_privilege acc1 = account_privilege acc2).

  Definition file_view (file1 file2: File) : Prop :=
    file_path file1 = file_path file2
    /\ file_objective file1 = file_objective file2
    /\ (forall (p: path), In p (file_subfiles file1) -> In p (file_subfiles file2))
    /\ (forall (u: idUser), In u (file_user_access file1) -> In u (file_user_access file2)).
  
  Definition subset_accounts (l1 l2: list Account) : Prop :=
    forall (acc: Account), In acc l1 -> (In acc l2 \/ (exists (acc': Account), In acc' l2 /\ account_view acc acc')).

  Definition subset_files (files1 files2: list File) : Prop :=
    forall (f: File), In f files1 -> (In f files2 \/ (exists (f': File), In f' files2 /\ file_view f f')).

  Definition subset_neighbours (l1 l2: list idMachine) : Prop :=
    forall (m: idMachine), In m l1 -> In m l2.
  
  Definition is_machineView (m1 m2: Machine) : Prop :=
    subset_services (machine_services m1) (machine_services m2)
    /\ subset_accounts (machine_accounts m1) (machine_accounts m2)
    /\ subset_files (machine_fileSystem m1) (machine_fileSystem m2)
    /\ subset_neighbours (machine_neighbours m1) (machine_neighbours m2).

  Definition is_networkView (net1 net2: network_map) : Prop :=
    forall (m: idMachine) (mac1 mac2: Machine), net1 m = Some mac1 -> net2 m = Some mac2 -> is_machineView mac1 mac2.


End MachineView.