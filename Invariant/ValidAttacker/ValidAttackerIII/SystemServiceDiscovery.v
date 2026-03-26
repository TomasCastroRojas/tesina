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

Lemma one_step_system_service_discovery_preserves_valid_attacker_iii : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m : idMachine) (u : idUser),
      valid_concrete_network n -> Pre a (System_Service_Discovery m u) -> Post a (System_Service_Discovery m u) n a' -> valid_attacker_iii a'.
  Proof.
    intros a a' network validAttacker m u validNetwork pre post.
    unfold valid_attacker_iii; unfold valid_network.
    unfold Pre in pre; destruct post.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttacker'''.
    clear validAttackerI validAttackerII validAttacker'''.

    elim_intro_clear H0 Hsecrets H0'.
    elim_intro_clear H0' mac H0''.
    elim_intro_clear H0'' macView H0'''.
    elim_intro_clear H0''' newMacView H0''''.
    elim_intro_clear H0'''' services H0'''''.
    elim_intro_clear H0''''' servicesView H0''''''.
    elim_intro_clear H0'''''' servicesNewView H1.

    elim_intro_clear H1 env_m H1'.
    elim_intro_clear H1' network_m H1''.
    elim_intro_clear H1'' servicesView_eq H1'''.
    elim_intro_clear H1''' services_eq H1''''.
    elim_intro_clear H1'''' servicesNewView_eq H1'''''.
    elim_intro_clear H1''''' newMacView_eq env_a'.

    unfold valid_attacker_iii in validAttackerIII.
    unfold valid_network in validAttackerIII.
    elim_intro_clear validAttackerIII network_top_enva valid_machine_enva.
    unfold network_topology in *.

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
                         exact users_macView.
                  ------ split.
                         ------- unfold users_access_to_services in *.
                                 unfold registered_service in *.
                                 simpl.
                                 rewrite servicesNewView_eq.
                                 intros acc Hinacc.
                                 elim (subfiles_macView acc).
                                 -------- intro Hnone. left. exact Hnone.
                                 -------- intros [s [Heq_s [service [Heq_service H_in_service]]]].
                                          right. exists s. split.
                                          --------- exact Heq_s.
                                          --------- exists service. split.
                                                    ---------- exact Heq_service.
                                                    ---------- rewrite servicesView_eq.
                                                               apply oplusServices_preserves_membership.
                                                               exact H_in_service.
                                 -------- exact Hinacc.
                         ------- unfold valid_fileSystem.
                                 simpl.
                                 split.
                                 -------- exact users_services_macView.
                                 -------- exact unique_macView.
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