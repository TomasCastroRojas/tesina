Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmasEnviroment.
Require Import Invariant.AuxLemmas.AuxLemmasAccount.
Require Import Invariant.AuxTactics.

Lemma one_step_unsecured_credentials_preserves_valid_attacker_iii : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m : idMachine) (u : idUser) (s: idService),
      valid_concrete_network n -> Pre a (Unsecured_Credentials m u s) -> Post a (Unsecured_Credentials m u s) n a' -> valid_attacker_iii a'.
  Proof.
    intros a a' network validAttacker m u s validNetwork pre post.
    unfold valid_attacker_iii.
    unfold valid_network.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttackerIV.
    unfold Pre in pre; destruct post.
    clear validNetwork validAttackerI validAttackerII validAttackerIV.

    elim_intro_clear H0 Hsecrets H0'.
    elim_intro_clear H0' Hmastered H0'a.
    elim_intro_clear H0'a mac H0.
    elim_intro_clear H0 macView H0'.
    elim_intro_clear H0' newMacView H0.
    elim_intro_clear H0 accs H0'.
    elim_intro_clear H0' accsView H0.
    elim_intro_clear H0 accsLinkedToUser H0'.
    elim_intro_clear H0' accsNewView H0.
    elim_intro_clear H0 accView H1.

    elim_intro_clear H1 env_m H1'.
    elim_intro_clear H1' network_m H1.
    elim_intro_clear H1 accsView_eq H1'.
    elim_intro_clear H1' accView_in H1.
    elim_intro_clear H1 accView_user H1'.
    elim_intro_clear H1' accView_service H1.
    elim_intro_clear H1 accs_mac H1'.
    elim_intro_clear H1' accsLinked_eq H1.
    elim_intro_clear H1 accsNewView_eq H1'.
    elim_intro_clear H1' newMacView_eq env_a'.

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
         --- assert (Heq_m0: m0 = newMacView).
             ---- apply (enviroment_simpl (enviroment a) (enviroment a') mid m).
                  ----- exact eq_mid.
                  ----- exact env_a'.
                  ----- exact H1.
             ---- rewrite Heq_m0 in H2.
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
    - intros.
      case (idMachine_eq mid m); intros eq_m.
      -- assert (m0 = newMacView).
         apply (enviroment_simpl (enviroment a) (enviroment a') mid m).
         --- exact eq_m.
         --- exact env_a'.
         --- exact H0.
         --- rewrite H1.
             elim (valid_machine_enva m macView).
             intros.
             elim_intro_clear H3 H6 H5.
             elim_intro_clear H5 H7 H8.
             unfold valid_machine.
             rewrite newMacView_eq.
             split.
             ---- unfold users_access_to_files in *.
                  unfold registered_users in *.
                  simpl.
                  rewrite accsNewView_eq.
                  rewrite <- accsView_eq.
                  intros f Hinf.
                  destruct (H2 f Hinf) as [Hacc_user H5].
                  destruct H5 as [ Hacc Hin_f].
                  destruct Hacc as [acc Hacc'].
                  destruct Hacc' as [ Heq_acc Hin_acc ].
                  ----- exists Hacc_user.
                        split.
                        ------ apply oplusAccounts_preserves_registered_user.
                               exists acc.
                               split.
                               ------- exact Heq_acc.
                               ------- exact Hin_acc.
                        ------ exact Hin_f.
             ---- split.
                  ----- unfold users_access_to_services in *.
                        unfold registered_service in *.
                        simpl.
                        intros acc0 HIP.
                        rewrite accsNewView_eq in HIP.
                        apply member_oplusAccounts_simpl in HIP.
                        destruct HIP as [HIP | HIP].
                        ------ (* acc0 proviene de accsLinkedToUser *)
                               right.
                               assert (Hservice: account_service acc0 = Some s).
                               { rewrite accsLinked_eq in HIP.
                                 apply (get_accounts_linked_service_with_key_service u s accs).
                                 exact HIP. }
                               exists s.
                               split.
                               ------- exact Hservice.
                               ------- assert (Hin_accView: In accView (machine_accounts macView)).
                                       { rewrite accsView_eq. exact accView_in. }
                                       destruct (H6 accView Hin_accView) as [Habs | [s0 [Hs0 Hserv]]].
                                       -------- rewrite accView_service in Habs. discriminate.
                                       -------- rewrite accView_service in Hs0.
                                                injection Hs0 as Hs0.
                                                rewrite <- Hs0 in Hserv.
                                                exact Hserv.
                        ------ (* acc0 proviene de accsView *)
                               rewrite <- accsView_eq in HIP.
                               apply H6. exact HIP.
                  ----- unfold valid_fileSystem.
                        simpl.
                        split.
                        ------ unfold subfiles_in_machine in *. 
                               unfold registered_paths in *.
                               simpl in *.
                               exact H7.
                        ------ exact H8.
             ---- exact env_m.
      -- assert (enviroment a' mid = enviroment a mid).
         apply (enviroment_eq (enviroment a) (enviroment a') mid m newMacView).
         --- exact eq_m.
         --- exact env_a'.
         --- rewrite H1 in H0.
             apply (valid_machine_enva mid m0).
             exact H0.
  Qed.