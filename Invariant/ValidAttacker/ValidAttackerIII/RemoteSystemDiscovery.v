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

Lemma one_step_remote_system_discovery_preserves_valid_attacker_iii : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m: idMachine) (u: idUser),
      valid_concrete_network n -> Pre a (Remote_System_Discovery m u) -> Post a (Remote_System_Discovery m u) n a' -> valid_attacker_iii a'.
  Proof.
    intros a a' network validAttacker m u validNetwork pre post.
    unfold valid_attacker_iii; unfold valid_network.
    unfold Pre in pre; destruct post.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttacker'''.
    clear validAttackerI validAttackerII validAttacker'''.

    elim_intro_clear H0 Hsecrets H0'.
    elim_intro_clear H0' macView H0''.
    elim_intro_clear H0'' newMacView H0'''.
    elim_intro_clear H0''' mac H0''''.
    elim_intro_clear H0'''' newNeighbours H0'''''.
    elim_intro_clear H0''''' macNeighbours H1.

    elim_intro_clear H1 env_m H1'.
    elim_intro_clear H1' network_m H1''.
    elim_intro_clear H1'' macNeighbours_eq H1'''.
    elim_intro_clear H1''' macNeighbours_closure H1''''.
    elim_intro_clear H1'''' newNeighbours_eq H1'''''.
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
      -- assert (Hm0: m0 = newMacView).
         --- apply (enviroment_simpl (enviroment a) (enviroment a') mid m).
             ---- exact eq_mid.
             ---- exact env_a'.
             ---- exact H1.
         --- rewrite Hm0 in H2.
             rewrite newMacView_eq in H2.
             unfold is_neighbour in H2.
             simpl in H2.
             rewrite newNeighbours_eq in H2.
             apply oplusNeighbours_membership in H2.
             destruct H2 as [ H2_view | H2_mac ].
             ---- apply (network_top_enva m neighbour macView).
                  ----- intro contra. symmetry in contra. exact (eq_neigh contra).
                  ----- exact env_m.
                  ----- unfold is_neighbour. exact H2_view.
             ---- exact (macNeighbours_closure neighbour H2_mac).
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
                                 exact subfiles_macView.
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