Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmasEnviroment.
Require Import Invariant.AuxLemmas.AuxLemmasService.
Require Import Invariant.AuxTactics.

Lemma one_step_network_service_scanning_preserves_valid_attacker_iii : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m m': idMachine) (u : idUser) (l: list nat),
      valid_concrete_network n -> Pre a (Network_Service_Scanning m u m' l) -> Post a (Network_Service_Scanning m u m' l) n a' -> valid_attacker_iii a'.
  Proof.
    intros a a' network validAttacker m m' u l validNetwork pre post.
    unfold valid_attacker_iii; unfold valid_network.
    unfold Pre in pre; unfold Post in post.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttacker'''.
    clear validAttackerI validAttackerII validAttacker'''.

    elim_intro_clear post Hknown_machines post'.
    elim_intro_clear post' Hsecrets post.
    elim_intro_clear post Hmastered post'.
    elim_intro_clear post' mac post.
    elim_intro_clear post macView' post'.
    elim_intro_clear post' newMacView' post.
    elim_intro_clear post portsServices post'.
    elim_intro_clear post' servicesNewView post.
    elim_intro_clear post env_m post'.
    elim_intro_clear post' network_m post.
    elim_intro_clear post portsServices_eq post'.
    elim_intro_clear post' servicesNewView_eq post.
    elim_intro_clear post newMacView_eq env_a'.


        unfold valid_attacker_iii in validAttackerIII.
    unfold valid_network in validAttackerIII.
    elim_intro_clear validAttackerIII network_top_enva valid_machine_enva.
    unfold network_topology in *.

    split.
    - intros.
      rewrite env_a'.
      unfold modify_machine.
      case (idMachine_eq neighbour m'); case (idMachine_eq mid m'); intros eq_mid eq_neigh.
      -- exists newMacView'; auto.
      -- exists newMacView'; auto.
      -- apply (network_top_enva m' neighbour macView').
         --- intro contra. symmetry in contra. exact (eq_neigh contra).
         --- exact env_m.
         --- assert (Hm0: m0 = newMacView').
             ---- apply (enviroment_simpl (enviroment a) (enviroment a') mid m').
                  ----- exact eq_mid.
                  ----- exact env_a'.
                  ----- exact H0.
             ---- rewrite Hm0 in H1.
                  rewrite newMacView_eq in H1.
                  unfold is_neighbour in *.
                  simpl in H1.
                  exact H1.
      -- apply (network_top_enva mid neighbour m0).
         --- exact H.
         --- rewrite <- (enviroment_eq (enviroment a) (enviroment a') mid m' newMacView').
             ---- exact H0.
             ---- exact eq_mid.
             ---- exact env_a'.
         --- exact H1.
    - intros m0 mac' enva'_m'.
      case (idMachine_eq m0 m'); intros eq_m0.
      -- assert (mac' = newMacView').
         apply (enviroment_simpl (enviroment a) (enviroment a') m0 m' mac' newMacView').
         --- exact eq_m0.
         --- exact env_a'.
         --- exact enva'_m'.
         --- rewrite H.
             elim (valid_machine_enva m' macView').
             ---- intros users_macView HI.
                  elim_intro_clear HI users_services_macView HI'.
                  elim_intro_clear HI' exploits_macView fileSystem_macView.
                  unfold valid_machine.
                  rewrite newMacView_eq.
                  split.
                  ------ unfold users_access_to_files in *.
                         unfold registered_users in *.
                         simpl.
                         exact users_macView.
                  ------ split.
                         ------- unfold users_access_to_services in *.
                                 unfold registered_service in *.
                                 simpl.
                                 rewrite servicesNewView_eq.
                                 intros acc Hinacc.
                                 elim (users_services_macView acc).
                                 -------- intro Hnone. left. exact Hnone.
                                 -------- intros [s [Heq_s [service [Heq_service H_in_service]]]].
                                          right. exists s. split.
                                          --------- exact Heq_s.
                                          --------- exists service. split.
                                                    ---------- exact Heq_service.
                                                    ---------- rewrite portsServices_eq.
                                                               apply oplusServices_preserves_membership.
                                                               exact H_in_service.
                                 -------- exact Hinacc.
                         ------- split.
                                 -------- unfold exploits_services in *.
                                          unfold registered_service in *.
                                          simpl.
                                          intros s0 e0 Hin_exploits.
                                          rewrite servicesNewView_eq.
                                          elim (exploits_macView s0 e0).
                                          --------- intros serv HI.
                                                    elim_intro_clear HI serv_value_eq H_in_service.
                                                    exists serv.
                                                    split.
                                                    ---------- exact serv_value_eq.
                                                    ---------- rewrite portsServices_eq.
                                                               apply oplusServices_preserves_membership.
                                                               exact H_in_service.
                                          --------- exact Hin_exploits.
                                 -------- unfold valid_fileSystem in *.
                                          simpl.
                                          elim_intro_clear fileSystem_macView subfiles_macView fileSystem'_macView.
                                          split.
                                          --------- unfold subfiles_in_machine in *.
                                                    unfold registered_paths in *.
                                                    simpl.
                                                    exact subfiles_macView.
                                          --------- exact fileSystem'_macView.
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
         --- rewrite <- (enviroment_eq (enviroment a) (enviroment a') m0 m' newMacView').
             ---- exact enva'_m'.
             ---- exact eq_m0.
             ---- exact env_a'.
  Qed.