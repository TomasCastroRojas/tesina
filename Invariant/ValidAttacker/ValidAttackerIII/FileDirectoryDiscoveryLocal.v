Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmas.
Require Import Invariant.AuxTactics.

Lemma one_step_file_directory_discovery_local_preserves_valid_attacker_iii :
    forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n)
           (m: idMachine) (u: idUser) (p: path),
      valid_concrete_network n ->
      Pre a (File_Directory_Discovery_Local m u p) ->
      Post a (File_Directory_Discovery_Local m u p) n a' ->
      valid_attacker_iii a'.
  Proof.
    intros a a' network validAttacker m u p validNetwork pre post.
    unfold valid_attacker in validAttacker.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttackerIV.
    clear validAttackerI validAttackerII.
    unfold Pre in pre; destruct post.

    elim_intro_clear pre known_machines_a pre'.
    elim_intro_clear pre' macPre pre''.
    elim_intro_clear pre'' fPre pre'''.
    elim_intro_clear pre''' accPre pre''''.
    elim_intro_clear pre'''' enva_macPre pre0.
    elim_intro_clear pre0 Hin_fPre pre1.
    elim_intro_clear pre1 Heq_fPre_path pre2.
    elim_intro_clear pre2 Hin_file_access pre3.
    elim_intro_clear pre3 Hin_accPre Heq_accPre.

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

    unfold valid_attacker_iii in *.
    unfold valid_network in *.
    unfold network_topology in *.
    elim_intro_clear validAttackerIII network_top_enva valid_machine_enva.

    split.
    - intros.
      rewrite env_a'.
      unfold modify_machine.
      case (idMachine_eq neighbour m); case (idMachine_eq mid m); intros eq_mid eq_neigh.
      -- exists newMacView; auto.
      -- exists newMacView; auto.
      -- apply (network_top_enva m neighbour macView).
         --- intro contra. symmetry in contra. exact (eq_neigh contra).
         --- exact env_m.
         --- assert (m0 = newMacView).
             ---- apply (enviroment_simpl (enviroment a) (enviroment a') mid m).
                  ----- exact eq_mid.
                  ----- exact env_a'.
                  ----- exact H1.
             ---- rewrite H3 in H2.
                  rewrite newMacView_eq in H2.
                  unfold is_neighbour in *.
                  simpl in H2.
                  exact H2.
      -- apply (network_top_enva mid neighbour m0).
         --- exact H0.
         --- rewrite <- (enviroment_eq (enviroment a) (enviroment a') mid m newMacView).
             ---- exact H1.
             ---- exact eq_mid.
             ---- exact env_a'.
         --- exact H2.
    - intros m' mac' enva'_m'.
      case (idMachine_eq m' m); intros eq_m'.
      -- assert (mac' = newMacView).
         apply (enviroment_simpl (enviroment a) (enviroment a') m' m mac' newMacView).
         --- exact eq_m'.
         --- exact env_a'.
         --- exact enva'_m'.
         --- rewrite H0.
             elim (valid_machine_enva m macView).
             ---- intros users_macView HI.
                  elim_intro_clear HI subfiles_macView HI'.
                  elim_intro_clear HI' users_services_macView unique_macView.
                  unfold valid_machine.
                  rewrite newMacView_eq.
                  split.
                  ------ unfold users_access_to_files in *.
                         unfold registered_users in *.
                         simpl.
                         rewrite filesNewMacView_eq.
                         intros f Hin_oplus.
                         assert (Heq_macPre: macPre = macView).
                         {
                            apply (enviroment_map_image (enviroment a) m macPre macView).
                            - exact enva_macPre.
                            - exact env_m.
                         }
                         assert (Hforall_u : forall f_src, In f_src filesMac ->
                                                 In u (file_user_access f_src)).
                         { intros f_src Hin_src.
                           apply (getFiles_user_access (machine_fileSystem mac) p u f_src).
                           rewrite <- filesMac_eq. exact Hin_src. }
                         destruct (oplusFiles_source_user_or_in_dest filesMac
                                       (machine_fileSystem macView) f u Hforall_u Hin_oplus)
                           as [Hu_f | Hf_macView].
                         * (* u esta en file_user_access f: usar accPre *)
                           exists u. split.
                           + exists accPre. split.
                             ------- exact Heq_accPre.
                             ------- rewrite <- Heq_macPre. exact Hin_accPre.
                           + exact Hu_f.
                         * (* f proviene de machine_fileSystem macView: usar users_macView *)
                           apply users_macView. exact Hf_macView.
                  ------ split.
                         ------- unfold users_access_to_services in *.
                                 unfold registered_service in *.
                                 simpl.
                                 exact subfiles_macView.
                         ------- unfold valid_fileSystem.
                                 simpl.
                                 rewrite filesNewMacView_eq.
                                 split.
                                 -------- unfold subfiles_in_machine in *.
                                          unfold registered_paths in *.
                                          simpl.
                                          apply (oplusFiles_subfiles_closed filesMac
                                                     (machine_fileSystem macView)).
                                          * intros f_src Hin_src p' Hp'.
                                            rewrite filesMac_eq in *.
                                            apply (getFiles_subfiles_closed
                                                     (machine_fileSystem mac) p u f_src p').
                                            --------- exact Hin_src.
                                            --------- exact Hp'.
                                          * intros f_dst Hin_dst p' Hp'.
                                            exact (users_services_macView f_dst Hin_dst p' Hp').
                                 -------- destruct unique_macView as [nodup_map_macView fwc_macView].
                                          destruct validNetwork as [_ Hvalid_concrete].
                                          destruct (Hvalid_concrete m mac network_m) as [Hvm _].
                                          unfold valid_machine in Hvm.
                                          destruct Hvm as [_ [_ Hvfs_mac]].
                                          unfold valid_fileSystem in Hvfs_mac.
                                          destruct Hvfs_mac as [_ [_ Hfwc_mac]].
                                          split.
                                          --------- apply oplusFiles_preserves_NoDup_map_file_path.
                                                    exact nodup_map_macView.
                                          --------- apply oplusFiles_preserves_files_without_cycles.
                                                    ---------- rewrite filesMac_eq.
                                                               apply getFiles_preserves_files_without_cycles.
                                                               exact Hfwc_mac.
                                                    ---------- exact fwc_macView.
                                                    
             ---- exact env_m.
      -- elim (valid_machine_enva m' mac').
         --- intros users_mac' HI.
            elim_intro_clear HI subfiles_mac' HI'.
            elim_intro_clear HI' users_services_mac' unique_mac'.
            unfold valid_machine.
            split.
            ---- exact users_mac'.
            ---- split.
                 ------ exact subfiles_mac'.
                 ------ unfold valid_fileSystem.
                        split.
                        -------- exact users_services_mac'.
                        -------- exact unique_mac'.
         --- rewrite <- (enviroment_eq (enviroment a) (enviroment a') m' m newMacView).
             ---- exact enva'_m'.
             ---- exact eq_m'.
             ---- exact env_a'.
  Qed.