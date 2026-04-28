Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmasEnviroment.
Require Import Invariant.AuxLemmas.AuxLemmasFile.
Require Import Invariant.AuxTactics.

Lemma one_step_file_directory_discovery_remote_preserves_valid_attacker_iii : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m m': idMachine) (u u': idUser) (k': option key) (p':path) (s': idService),
      valid_concrete_network n -> Pre a (File_Directory_Discovery_Remote m u m' u' k' p' s') -> Post a (File_Directory_Discovery_Remote m u m' u' k' p' s') n a' -> valid_attacker_iii a'.
  Proof.
    intros a a' network validAttacker m m' u u' k' p' s' validNetwork pre post.
    unfold valid_attacker in validAttacker.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttackerIV.
    clear validAttackerI validAttackerII.
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

    unfold valid_attacker_iii in *.
    unfold valid_network in *.
    unfold network_topology in *.
    elim_intro_clear validAttackerIII network_top_enva valid_machine_enva.

    split.
    - intros.
      rewrite env_a'.
      unfold modify_machine.
      case (idMachine_eq neighbour m'); case (idMachine_eq mid m'); intros eq_mid eq_neigh.
      -- exists newMacView; auto.
      -- exists newMacView; auto.
      -- apply (network_top_enva m' neighbour macView).
         --- intro contra. symmetry in contra. exact (eq_neigh contra).
         --- exact env_m.
         --- assert (m0 = newMacView).
             ---- apply (enviroment_simpl (enviroment a) (enviroment a') mid m').
                  ----- exact eq_mid.
                  ----- exact env_a'.
                  ----- exact H0.
             ---- rewrite H2 in H1.
                  rewrite newMacView_eq in H1.
                  unfold is_neighbour in *.
                  simpl in H1.
                  exact H1.
      -- apply (network_top_enva mid neighbour m0).
         --- exact H.
         --- rewrite <- (enviroment_eq (enviroment a) (enviroment a') mid m' newMacView).
             ---- exact H0.
             ---- exact eq_mid.
             ---- exact env_a'.
         --- exact H1.
    - intros m0 mac' enva'_m0.
      case (idMachine_eq m0 m'); intros eq_m'.
      -- assert (mac' = newMacView).
         apply (enviroment_simpl (enviroment a) (enviroment a') m0 m' mac' newMacView).
         --- exact eq_m'.
         --- exact env_a'.
         --- exact enva'_m0.
         --- rewrite H.
             elim (valid_machine_enva m' macView).
             ---- intros users_macView HI.
                  elim_intro_clear HI users_services_macView HI'.
                  elim_intro_clear HI' exploits_macView fileSystem_macView.
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
                            apply (enviroment_map_image (enviroment a) m' macPre macView).
                            - exact enva_macPre.
                            - exact env_m.
                         }
                         assert (Hforall_u : forall f_src, In f_src filesMac ->
                                                 In u' (file_user_access f_src)).
                         { intros f_src Hin_src.
                           apply (getFiles_user_access (machine_fileSystem mac) p' u' f_src).
                           rewrite <- filesMac_eq. exact Hin_src. }
                         destruct (oplusFiles_source_user_or_in_dest filesMac
                                       (machine_fileSystem macView) f u' Hforall_u Hin_oplus)
                           as [Hu_f | Hf_macView].
                         * (* u esta en file_user_access f: usar accPre *)
                           exists u'. split.
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
                                 exact users_services_macView.
                         ------- split.
                                 -------- unfold exploits_services in *.
                                          unfold registered_service in *.
                                          simpl.
                                          exact exploits_macView.
                                 -------- unfold valid_fileSystem in *.
                                          elim_intro_clear fileSystem_macView subfiles_macView fileSystem'_macView.
                                          simpl.
                                          rewrite filesNewMacView_eq.
                                          split.
                                          --------- unfold subfiles_in_machine in *.
                                                    unfold registered_paths in *.
                                                    simpl.
                                                    apply (oplusFiles_subfiles_closed filesMac
                                                              (machine_fileSystem macView)).
                                                    * intros f_src Hin_src p0' Hp'.
                                                      rewrite filesMac_eq in *.
                                                      apply (getFiles_subfiles_closed
                                                              (machine_fileSystem mac) p' u' f_src p0').
                                                      ---------- exact Hin_src.
                                                      ---------- exact Hp'.
                                                    * intros f_dst Hin_dst p0' Hp'.
                                                      exact (subfiles_macView f_dst Hin_dst p0' Hp').
                                          --------- destruct fileSystem'_macView as [nodup_map_macView fwc_macView].
                                                    destruct validNetwork as [_ Hvalid_concrete].
                                                    destruct (Hvalid_concrete m' mac network_m) as [Hvm _].
                                                    unfold valid_machine in Hvm.
                                                    destruct Hvm as [_ [_ Hvfs_mac]].
                                                    unfold valid_fileSystem in Hvfs_mac.
                                                    destruct Hvfs_mac as [_ [_ [_ Hfwc_mac]]].
                                                    split.
                                                    ---------- apply oplusFiles_preserves_NoDup_map_file_path.
                                                              exact nodup_map_macView.
                                                    ---------- apply oplusFiles_preserves_files_without_cycles.
                                                              ----------- rewrite filesMac_eq.
                                                                        apply getFiles_preserves_files_without_cycles.
                                                                        exact Hfwc_mac.
                                                              ----------- exact fwc_macView.
                                                    
             ---- exact env_m.
      -- elim (valid_machine_enva m0 mac').
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
         --- rewrite <- (enviroment_eq (enviroment a) (enviroment a') m0 m' newMacView).
             ---- exact enva'_m0.
             ---- exact eq_m'.
             ---- exact env_a'.
  Qed.