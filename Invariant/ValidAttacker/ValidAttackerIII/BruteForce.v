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

Lemma one_step_brute_force_preserves_valid_attacker_iii : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m m': idMachine) (u u': idUser) (s': idService),
      valid_concrete_network n -> Pre a (Brute_Force m u m' u' s') -> Post a (Brute_Force m u m' u' s') n a' -> valid_attacker_iii a'.
  Proof.
    intros a a' network validAttacker m m' u u' s' validNetwork pre post.
    unfold valid_attacker_iii.
    unfold valid_network.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttackerIV.
    unfold Pre in pre; unfold Post in post.

    elim_intro_clear post known_machines_eq post'.
    elim_intro_clear post' secrets_eq post.
    elim_intro_clear post exploits_eq post'.
    elim_intro_clear post' mac post.
    elim_intro_clear post macView' post'.
    elim_intro_clear post' newMacView post.
    elim_intro_clear post accs post'.
    elim_intro_clear post' accsView' post.
    elim_intro_clear post newAccountsView post'.
    elim_intro_clear post' acc post.
    elim_intro_clear post k post'.
    elim_intro_clear post' l post.
    elim_intro_clear post env_m' post'.
    elim_intro_clear post' network_m' post.
    elim_intro_clear post accsView'_eq post'.
    elim_intro_clear post' accs_eq post.
    elim_intro_clear post acc_in post'.
    elim_intro_clear post' acc_user post.
    elim_intro_clear post acc_service post'.
    elim_intro_clear post' acc_key post.
    elim_intro_clear post acc_priv post'.
    elim_intro_clear post' newAccountsView_eq post.
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
      -- exists newMacView; auto.
      -- exists newMacView; auto.
      -- apply (network_top_enva m' neighbour macView').
         --- intro contra. symmetry in contra. exact (eq_neigh contra).
         --- exact env_m'.
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
    - intros.
      case (idMachine_eq mid m'); intros eq_m.
      -- assert (m0 = newMacView).
         apply (enviroment_simpl (enviroment a) (enviroment a') mid m').
         --- exact eq_m.
         --- exact env_a'.
         --- exact H.
         --- rewrite H0.
             elim (valid_machine_enva m' macView').
             intros.
             elim_intro_clear H2 H3 H2'.
             elim_intro_clear H2' H4 H5.
             unfold valid_machine.
             rewrite newMacView_eq.
             split.
             ---- unfold users_access_to_files in *.
                  unfold registered_users in *.
                  simpl.
                  rewrite newAccountsView_eq.
                  intros f Hinf.
                  destruct (H1 f Hinf) as [Hacc_user H6].
                  destruct H6 as [ Hacc Hin_f].
                  destruct Hacc as [acc0 Hacc'].
                  destruct Hacc' as [ Heq_acc Hin_acc ].
                  case (idUser_eq Hacc_user u'); intros Heq_u0.
                  ----- exists Hacc_user.
                        split.
                        ------ exists acc.
                              split.
                              ------- rewrite acc_user. symmetry. exact Heq_u0.
                              ------- apply member_addAccount. auto.
                        ------ exact Hin_f.
                  ----- exists Hacc_user.
                        split.
                        ------ exists acc0.
                              split.
                              ------- exact Heq_acc.
                              ------- apply addAccount_preserves_membership_when_neq.
                                    -------- rewrite Heq_acc. rewrite acc_user. exact Heq_u0.
                                    -------- rewrite <- accsView'_eq. exact Hin_acc.
                        ------ exact Hin_f.
             ---- split.
                  ----- unfold users_access_to_services in *.
                        unfold registered_service in *.
                        rewrite newAccountsView_eq.
                        simpl.
                        intros acc0 HIP.
                        apply member_addAccount_simpl in HIP.
                        elim HIP; intro HIP'.
                        ------ (* HIP' : acc = acc0 *)
                               right.
                               rewrite <- HIP'.
                               exists s'.
                               split.
                               ------- exact acc_service.
                               ------- destruct pre as [_ [_ [accP [macP [lP [env_m'_pre [accP_in [_ [accP_service [_ _]]]]]]]]]].
                                       assert (Hmac_eq: macP = macView').
                                       { 
                                          apply (enviroment_map_image (enviroment a) m' macP macView').
                                          - exact env_m'_pre.
                                          - exact env_m'. 
                                       }
                                       rewrite Hmac_eq in accP_in.
                                       destruct (H3 accP accP_in) as [Hnone | [s0 [Hs0 Hserv]]].
                                       -------- rewrite accP_service in Hnone. discriminate.
                                       -------- rewrite accP_service in Hs0.
                                                injection Hs0 as Hs0.
                                                rewrite <- Hs0 in Hserv.
                                                exact Hserv.
                        ------ apply H3.
                               rewrite <- accsView'_eq in HIP'.
                               exact HIP'.
                  ----- unfold valid_fileSystem.
                        simpl.
                        split.
                        ------ exact H4.
                        ------ exact H5.
             ---- exact env_m'.
      -- assert (enviroment a' mid = enviroment a mid).
         apply (enviroment_eq (enviroment a) (enviroment a') mid m' newMacView).
         --- exact eq_m.
         --- exact env_a'.
         --- rewrite H0 in H.
             apply (valid_machine_enva mid m0).
             exact H.
  Qed.