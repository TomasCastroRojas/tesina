Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmasMachineUser.
Require Import Invariant.AuxLemmas.AuxLemmasEnviroment.
Require Import Invariant.AuxLemmas.AuxLemmasAccount.
Require Import Invariant.AuxTactics.

Lemma one_step_abuse_elevation_control_mechanism_preserves_valid_attacker_i : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m : idMachine) (u: idUser),
      valid_concrete_network n -> Pre a (Abuse_Elevation_Control_Mechanism m u) -> Post a (Abuse_Elevation_Control_Mechanism m u) n a' -> valid_attacker_i a'.
  Proof.
    intros a a' network validAttacker m u validNetwork pre post.
    unfold valid_attacker_i.
    intros m0 u0 H_known_machines_a'.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    unfold Pre in pre; unfold Post in post.
    clear validNetwork validAttacker'.

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

    unfold valid_attacker_i in validAttackerI.
    rewrite known_machines_a' in H_known_machines_a'.
    apply member_add_machine_user in H_known_machines_a'.
    case (idMachine_eq m0 m); case (idUser_eq u0 u'); intros.
    - unfold modify_machine in env_a'.
      rewrite env_a'.
      case (idMachine_eq m0 m); intro.
      -- exists newMacView.
         split.
         --- reflexivity.
         --- unfold registered_users.
             exists accHighView.
             split.
             ---- rewrite HaccHighView_eq.
                  simpl.
                  symmetry.
                  exact e.
             ---- rewrite newMacView_eq.
                  simpl.
                  rewrite newAccountsView_eq.
                  apply member_addAccount.
                  auto.
      -- contradiction.
    - elim (validAttackerI m0 u0).
      intros MAC IH.
      elim_intro_clear IH env_MAC users_MAC.
      -- exists newMacView.
         split.
         --- rewrite env_a'.
             unfold modify_machine.
             case (idMachine_eq m0 m); intro eq_m.
             ---- reflexivity.
             ---- contradiction.
         --- unfold registered_users.
             rewrite newMacView_eq.
             simpl.
             rewrite newAccountsView_eq.
             rewrite e in env_MAC.
             assert (macView = MAC).
             ---- apply (enviroment_map_image (enviroment a) m macView MAC).
                  ----- exact env_macView.
                  ----- exact env_MAC.
             ---- unfold registered_users in users_MAC.
                  rewrite <- H in users_MAC.
                  elim_intro_clear users_MAC acc_u0 users_MAC'.
                  elim_intro_clear users_MAC' acc_u0_eq acc_In_accounts.
                  exists acc_u0.
                  split.
                  ----- exact acc_u0_eq.
                  ----- apply addAccount_preserves_membership_when_neq.
                        ------- rewrite acc_u0_eq.
                                rewrite HaccHighView_eq.
                                simpl.
                                exact n.
                        ------- exact acc_In_accounts.
      -- elim H_known_machines_a'.
         --- intro eq_tuple.
             injection eq_tuple.
             intros.
             symmetry in H.
             contradiction.
         --- intro. exact H.
    - elim (validAttackerI m0 u0).
      intros MAC IH.
      elim_intro_clear IH env_MAC users_MAC.
      exists MAC.
      split.
      -- rewrite (enviroment_eq (enviroment a) (enviroment a') m0 m newMacView).
         --- exact env_MAC.
         --- exact n.
         --- exact env_a'.
      -- exact users_MAC.
      -- elim H_known_machines_a'.
         --- intro eq_tuple.
             injection eq_tuple.
             intros.
             symmetry in H0.
             contradiction.
         --- intro. exact H.
    - elim (validAttackerI m0 u0).
      intros MAC IH.
      elim_intro_clear IH env_MAC users_MAC.
      exists MAC.
      split.
      -- rewrite (enviroment_eq (enviroment a) (enviroment a') m0 m newMacView).
         --- exact env_MAC.
         --- exact n0.
         --- exact env_a'.
      -- exact users_MAC.
      -- elim H_known_machines_a'.
         --- intro eq_tuple.
             injection eq_tuple.
             intros.
             symmetry in H0.
             contradiction.
         --- intro. exact H.
  Qed.