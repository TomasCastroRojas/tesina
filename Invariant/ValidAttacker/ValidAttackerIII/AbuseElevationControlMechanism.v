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

Lemma one_step_abuse_elevation_control_mechanism_preserves_valid_attacker_iii : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m : idMachine) (u: idUser),
      valid_concrete_network n -> Pre a (Abuse_Elevation_Control_Mechanism m u) -> Post a (Abuse_Elevation_Control_Mechanism m u) n a' -> valid_attacker_iii a'.
  Proof.
    intros a a' network validAttacker m u validNetwork pre post.
    unfold valid_attacker_iii.
    unfold valid_network.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttackerIV.
    unfold Pre in pre; unfold Post in post.
    clear validNetwork validAttackerI validAttackerII validAttackerIV.

    elim_intro_clear post Hsecrets post'.
    elim_intro_clear post' Hmastered post.
    elim_intro_clear post mac post'.
    elim_intro_clear post' macView post.
    elim_intro_clear post newMacView post'.
    elim_intro_clear post' u' post.
    elim_intro_clear post newAccountsView post'.
    elim_intro_clear post' accHigh post.
    elim_intro_clear post accHighView post'.

    elim_intro_clear post' network_m post.
    elim_intro_clear post env_macView post'.
    elim_intro_clear post' Hin_accs post.
    elim_intro_clear post HaccHigh_user post'.
    elim_intro_clear post' HaccHigh_service post.
    elim_intro_clear post HaccHigh_priv post'.
    elim_intro_clear post' HaccHighView_eq post.
    elim_intro_clear post newAccountsView_eq post'.
    elim_intro_clear post' newMacView_eq post.
    elim_intro_clear post known_machines_a' env_a'.

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
         --- exact env_macView.
         --- assert (Hmacm0_eq: m0 = newMacView).
             ---- apply (enviroment_simpl (enviroment a) (enviroment a') mid m).
                  ----- exact eq_mid.
                  ----- exact env_a'.
                  ----- exact H0.
             ---- rewrite Hmacm0_eq in H1.
                  rewrite newMacView_eq in H1.
                  unfold is_neighbour in *.
                  simpl in H1.
                  exact H1.
      -- apply (network_top_enva mid neighbour m0).
         --- exact H.
         --- rewrite <- (enviroment_eq (enviroment a) (enviroment a') mid m newMacView).
             ---- exact H0.
             ---- exact eq_mid.
             ---- exact env_a'.
         --- exact H1.
    - intros.
      case (idMachine_eq mid m); intros eq_m.
      -- assert (Hmacm0_eq: m0 = newMacView).
         apply (enviroment_simpl (enviroment a) (enviroment a') mid m).
         --- exact eq_m.
         --- exact env_a'.
         --- exact H.
         --- rewrite Hmacm0_eq.
             elim (valid_machine_enva m macView).
             intros.
             elim_intro_clear H1 Husers_services_macView H1'.
             elim_intro_clear H1' Hexploits_macView HvalidfileSystem_macView.
             unfold valid_machine.
             rewrite newMacView_eq.
             split.
             ---- unfold users_access_to_files in *.
                  unfold registered_users in *.
                  simpl.
                  rewrite newAccountsView_eq.
                  intros f Hinf.
                  destruct (H0 f Hinf) as [Hacc_user H5].
                  destruct H5 as [ Hacc Hin_f].
                  destruct Hacc as [acc Hacc'].
                  destruct Hacc' as [ Heq_acc Hin_acc ].
                  case (idUser_eq Hacc_user u'); intros Heq_u0.
                  ----- exists Hacc_user.
                        split.
                        ------ exists accHighView.
                              split.
                              ------- rewrite HaccHighView_eq. simpl. symmetry. exact Heq_u0.
                              ------- apply member_addAccount. auto.
                        ------ exact Hin_f.
                  ----- exists Hacc_user.
                        split.
                        ------ exists acc.
                              split.
                              ------- exact Heq_acc.
                              ------- apply addAccount_preserves_membership_when_neq.
                                    -------- rewrite Heq_acc. rewrite HaccHighView_eq. simpl. exact Heq_u0.
                                    -------- exact Hin_acc.
                        ------ exact Hin_f.
             ---- split.
                  ----- unfold users_access_to_services in *.
                        unfold registered_service in *.
                        rewrite newAccountsView_eq.
                        simpl.
                        intros acc0 HIP.
                        apply member_addAccount_simpl in HIP.
                        destruct HIP as [HIP_eq | HIP_in].
                        ------ rewrite <- HIP_eq.
                               rewrite HaccHighView_eq.
                               simpl.
                               right.
                               exists OS.
                               split. reflexivity.
                               destruct pre as [_ [accPre [macPre [kPre [HenvPre [HinPre_acc [_ [HservPre _]]]]]]]].
                               rewrite (enviroment_map_image _ _ _ _ HenvPre env_macView) in HinPre_acc.
                               destruct (Husers_services_macView accPre HinPre_acc) as [Hno_serv | [s [Hs_eq Hreg]]].
                               ------- rewrite HservPre in Hno_serv. discriminate.
                               ------- rewrite HservPre in Hs_eq.
                                       injection Hs_eq as Hs_eq'.
                                       rewrite Hs_eq'.
                                       exact Hreg.
                        ------ apply Husers_services_macView. exact HIP_in.
                  ----- unfold valid_fileSystem in *.
                        unfold exploits_services in *.
                        unfold registered_service in *.
                        unfold subfiles_in_machine in *.
                        unfold registered_paths in *.
                        simpl.
                        split.
                        ------ exact Hexploits_macView.
                        ------ exact HvalidfileSystem_macView.
             ---- exact env_macView.
      -- assert (Henv_eq: enviroment a' mid = enviroment a mid).
         apply (enviroment_eq (enviroment a) (enviroment a') mid m newMacView).
         --- exact eq_m.
         --- exact env_a'.
         --- rewrite Henv_eq in H.
             apply (valid_machine_enva mid m0).
             exact H.
  Qed.