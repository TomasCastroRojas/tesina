Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Machine.MachineView.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmasEnviroment.
Require Import Invariant.AuxLemmas.AuxLemmasFile.
Require Import Invariant.AuxTactics.

Lemma one_step_file_directory_discovery_remote_preserves_valid_attacker_iv : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m m': idMachine) (u u': idUser) (k': option key) (p':path) (s': idService),
      valid_concrete_network n -> Pre a (File_Directory_Discovery_Remote m u m' u' k' p' s') -> Post a (File_Directory_Discovery_Remote m u m' u' k' p' s') n a' -> valid_attacker_iv a' n.
  Proof.
    intros a a' network validAttacker m m' u u' k' p' s' validNetwork pre post.
    unfold valid_attacker in validAttacker.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttackerIV.
    clear validAttackerI validAttackerII validAttackerIII.
    unfold Pre in pre; unfold Post in post.

    elim_intro_clear pre known_machines_a pre'.
    elim_intro_clear pre' mac_local pre.
    destruct pre as [macPre [serv_pre [fPre [accPre preBody]]]].
    destruct preBody as [enva_macPre [Hin_servPre [Hserv_value [Hserv_network preAcc]]]].
    destruct preAcc as [Hin_accPre [Heq_accPre [HaccPre_serv [HaccPre_key preFile]]]].
    destruct preFile as [Hin_fPre [Heq_fPre_path Hin_file_access]].

    elim_intro_clear post known_machines_a' post'.
    elim_intro_clear post' Hmastered post.
    elim_intro_clear post mac post'.
    elim_intro_clear post' macView post.
    elim_intro_clear post newMacView post'.
    elim_intro_clear post' filesMac post.
    elim_intro_clear post filesNewMacView post'.
    elim_intro_clear post' newSecrets post.
    elim_intro_clear post env_m post'.
    elim_intro_clear post' network_m post.
    elim_intro_clear post filesMac_eq post'.
    elim_intro_clear post' newSecrets_eq post.
    elim_intro_clear post secrets_eq post'.
    elim_intro_clear post' filesNewMacView_eq post.
    elim_intro_clear post newMacView_eq env_a'.

    unfold valid_attacker_iv in *.
    unfold is_networkView in *.
    intros m0 mac1 env_a'_m0.

    case (idMachine_eq m0 m'); intros eq_m0.
    - (* m0 = m' *)
      exists mac.
      split.
      + rewrite eq_m0. exact network_m.
      + assert (Heq_mac1: mac1 = newMacView).
        {
          apply (enviroment_simpl (enviroment a) (enviroment a') m0 m' mac1 newMacView).
          - exact eq_m0.
          - exact env_a'.
          - exact env_a'_m0.
        }
        rewrite Heq_mac1.
        destruct (validAttackerIV m0 macView) as [mac'' [Hnetwork' Hmv]].
        { rewrite <- eq_m0 in env_m. exact env_m. }
        assert (Heq_mac': mac'' = mac).
        {
          apply (enviroment_map_image network m' mac'' mac).
          - rewrite <- eq_m0. exact Hnetwork'.
          - exact network_m.
        }
        rewrite Heq_mac' in Hmv.
        destruct Hmv as [Hserv [Haccs [Hfiles [Hneighs Hexploits]]]].
        unfold is_machineView.
        split; [|split; [|split]]; try split.
        -- unfold subset_services in *.
           rewrite newMacView_eq.
           simpl.
           exact Hserv.
        -- unfold subset_accounts in *.
           rewrite newMacView_eq.
           simpl.
           exact Haccs.
        -- unfold subset_files in *.
           rewrite newMacView_eq.
           simpl.
           rewrite filesNewMacView_eq.
           apply (oplusFiles_subset_files filesMac (machine_fileSystem macView) (machine_fileSystem mac)).
           --- destruct validNetwork as [_ Hvalid_concrete].
               destruct (Hvalid_concrete m' mac network_m) as [Hvm _].
               unfold valid_machine in Hvm.
               destruct Hvm as [_ [_ Hvfs_mac]].
               unfold valid_fileSystem in Hvfs_mac.
               destruct Hvfs_mac as [_ [_ [Hnodup_map_mac _]]].
               apply NoDup_map_file_path_unique_paths. exact Hnodup_map_mac.
           --- rewrite filesMac_eq. apply (getFiles_subset_files_mac (machine_fileSystem mac) p' u').
           --- exact Hfiles.
        -- unfold subset_neighbours in *.
           rewrite newMacView_eq.
           simpl.
           exact Hneighs.
        -- unfold subset_exploits in *.
           rewrite newMacView_eq.
           simpl.
           exact Hexploits.
    - (* m0 <> m' *)
      destruct (validAttackerIV m0 mac1) as [mac2 [Hn2 Hmv]].
      { rewrite <- (enviroment_eq (enviroment a) (enviroment a') m0 m' newMacView).
        - exact env_a'_m0.
        - exact eq_m0.
        - exact env_a'.
      }
      exists mac2.
      split; assumption.
  Qed.