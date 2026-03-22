Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Machine.MachineView.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmas.
Require Import Invariant.AuxTactics.

Lemma one_step_file_directory_discovery_local_preserves_valid_attacker_iv :
    forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n)
           (m: idMachine) (u: idUser) (p: path),
      valid_concrete_network n ->
      Pre a (File_Directory_Discovery_Local m u p) ->
      Post a (File_Directory_Discovery_Local m u p) n a' ->
      valid_attacker_iv a' n.
  Proof.
    intros a a' network validAttacker m u p validNetwork pre post.
    unfold valid_attacker in validAttacker.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttackerIV.
    clear validAttackerI validAttackerII validAttackerIII.
    unfold Pre in pre; destruct post.

    (* Descomposicion de los 6 existenciales del Post *)
    elim_intro_clear H0 mac H0'.
    elim_intro_clear H0' macView H0''.
    elim_intro_clear H0'' newMacView H0'''.
    elim_intro_clear H0''' filesMac H0''''.
    elim_intro_clear H0'''' filesNewMacView H0'''''.
    elim_intro_clear H0''''' newSecrets H1.

    (* Descomposicion de la conjuncion de 8 partes *)
    elim_intro_clear H1 env_m H1'.
    elim_intro_clear H1' network_m H1''.
    elim_intro_clear H1'' filesMac_eq H1'''.
    elim_intro_clear H1''' newSecrets_eq H1''''.
    elim_intro_clear H1'''' secrets_eq H1'''''.
    elim_intro_clear H1''''' filesNewMacView_eq H1''''''.
    elim_intro_clear H1'''''' newMacView_eq env_a'.

    unfold valid_attacker_iv in *.
    unfold is_networkView in *.
    intros m0 mac1 mac2 env_a'_m0 network_m0.
    unfold is_machineView.

    case (idMachine_eq m0 m); intros eq_m0.
    elim (validAttackerIV m0 macView mac).
    intros Hserv. intro Hserv'.
    destruct Hserv' as [Haccs Hserv'']. 
    destruct Hserv'' as [Hfiles Hneighs].
    assert (Heq_mac1: mac1 = newMacView).
    {
      apply (enviroment_simpl (enviroment a) (enviroment a') m0 m mac1 newMacView).
      - exact eq_m0.
      - exact env_a'.
      - exact env_a'_m0.
    }
    assert (Heq_mac2: mac2 = mac).
    {
      apply (enviroment_map_image network m mac2 mac).
      - rewrite eq_m0 in network_m0. exact network_m0.
      - exact network_m.
    }
    rewrite Heq_mac1.
    rewrite Heq_mac2.
    split; [|split]; try split.
    - unfold subset_services in *.
      rewrite newMacView_eq.
      simpl.
      exact Hserv.
    - unfold subset_accounts in *.
      rewrite newMacView_eq.
      simpl.
      exact Haccs.
    - unfold subset_files in *.
      rewrite newMacView_eq.
      simpl.
      rewrite filesNewMacView_eq.
      apply (oplusFiles_subset_files filesMac (machine_fileSystem macView) (machine_fileSystem mac)).
      + destruct validNetwork as [_ Hvalid_concrete].
        destruct (Hvalid_concrete m mac network_m) as [Hvm _].
        unfold valid_machine in Hvm.
        destruct Hvm as [_ [_ Hvfs_mac]].
        unfold valid_fileSystem in Hvfs_mac.
        destruct Hvfs_mac as [_ [Hnodup_map_mac _]].
        apply NoDup_map_file_path_unique_paths. exact Hnodup_map_mac.
      + rewrite filesMac_eq. apply (getFiles_subset_files_mac (machine_fileSystem mac) p u). 
      + exact Hfiles.
    - unfold subset_neighbours in *.
      rewrite newMacView_eq.
      simpl.
      exact Hneighs.
    - rewrite <- eq_m0 in env_m. exact env_m.
    - rewrite <- eq_m0 in network_m. exact network_m.
    - elim (validAttackerIV m0 mac1 mac2).
      intros Hserv. intro Hserv'.
      destruct Hserv' as [Haccs Hserv''].
      destruct Hserv'' as [Hfiles Hneighs].
      split; [|split]; try split.
      -- exact Hserv.
      -- exact Haccs.
      -- exact Hfiles.
      -- exact Hneighs.
      -- rewrite <- (enviroment_eq (enviroment a) (enviroment a') m0 m newMacView).
         --- exact env_a'_m0.
         --- exact eq_m0.
         --- exact env_a'.
      -- exact network_m0.
  Qed.