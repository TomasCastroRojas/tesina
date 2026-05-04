Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmasEnviroment.
Require Import Invariant.AuxTactics.

Lemma one_step_abuse_elevation_control_mechanism_preserves_valid_attacker_ii : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m : idMachine) (u: idUser),
      valid_concrete_network n -> Pre a (Abuse_Elevation_Control_Mechanism m u) -> Post a (Abuse_Elevation_Control_Mechanism m u) n a' -> valid_attacker_ii a'.
  Proof.
    intros a a' network validAttacker m u validNetwork pre post.
    unfold valid_attacker_ii.
    intros m0 p0 H_secrets_a'.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    unfold Pre in pre; unfold Post in post.
    clear validNetwork validAttacker''.

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

    unfold valid_attacker_ii in validAttackerII.
    elim (validAttackerII m0 p0).
    intros MAC IH.
    elim_intro_clear IH env_MAC path_MAC.
    - case (idMachine_eq m0 m); intro eq_m0.
      -- exists newMacView.
         split.
         --- rewrite env_a'.
             unfold modify_machine.
             case (idMachine_eq m0 m); intros.
             ---- reflexivity.
             ---- contradiction.
         --- unfold registered_paths.
             rewrite newMacView_eq.
             simpl.
             assert (macView = MAC).
             ---- apply (enviroment_map_image (enviroment a) m macView MAC).
                  ----- exact env_macView.
                  ----- rewrite <- eq_m0. exact env_MAC.
             ---- rewrite <- H in path_MAC.
                  unfold registered_paths in path_MAC.
                  exact path_MAC.
      -- exists MAC.
         rewrite (enviroment_eq (enviroment a) (enviroment a') m0 m newMacView).
         --- split.
             ---- exact env_MAC.
             ---- exact path_MAC.
         --- exact eq_m0.
         --- exact env_a'.
    - rewrite Hsecrets in H_secrets_a'.
      exact H_secrets_a'.
  Qed.