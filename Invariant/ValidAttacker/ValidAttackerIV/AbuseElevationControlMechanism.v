Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Machine.MachineView.

Require Import Attacker.Attacker.

Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmasEnviroment.
Require Import Invariant.AuxLemmas.AuxLemmasAccount.
Require Import Invariant.AuxTactics.

Lemma one_step_abuse_elevation_control_mechanism_preserves_valid_attacker_iv : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m : idMachine) (u: idUser),
      valid_concrete_network n -> Pre a (Abuse_Elevation_Control_Mechanism m u) -> Post a (Abuse_Elevation_Control_Mechanism m u) n a' -> valid_attacker_iv a' n.
  Proof.
    intros a a' network validAttacker m u validNetwork pre post.
    unfold valid_attacker_iv.
    unfold is_networkView.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttackerIV.
    unfold Pre in pre; unfold Post in post.
    clear validAttackerI validAttackerII validAttackerIII.

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

    unfold valid_attacker_iv in validAttackerIV.
    unfold is_networkView in validAttackerIV.
    intros m0 mac1 mac2 env_a'_m0 network_m0.
    unfold is_machineView.
    case (idMachine_eq m0 m); intros eq_m0.
    elim (validAttackerIV m0 macView mac).
    intros Hserv. intro Hserv'.
    destruct Hserv' as [Haccs Hserv''].
    destruct Hserv'' as [Hfiles Hserv'''].
    destruct Hserv''' as [Hneighs Hexploits].
    assert (Heq_mac1: mac1 = newMacView).
    {
      apply (enviroment_simpl (enviroment a) (enviroment a') m0 m mac1 newMacView).
      - exact eq_m0.
      - exact env_a'.
      - exact env_a'_m0.
    }
    assert (Heq_mac2: mac2 = mac).
    {
      apply (enviroment_map_image network m mac2 mac).
      - rewrite eq_m0 in network_m0. exact network_m0.
      - exact network_m.
    }
    rewrite Heq_mac1.
    rewrite Heq_mac2.   
    split; [|split; [|split]]; try split.
    - unfold subset_services in *.
      rewrite newMacView_eq.
      simpl.
      exact Hserv.
    - unfold subset_accounts in *.
      rewrite newMacView_eq.
      simpl.
      rewrite newAccountsView_eq.
      intros Hacc Hin_addAccount.
      assert (Hin_Hacc: accHighView = Hacc \/ In Hacc (machine_accounts macView)).
      {
        apply (member_addAccount_simpl Hacc accHighView (machine_accounts macView)).
        exact Hin_addAccount.
      }
      destruct Hin_Hacc as [Heq_Hacc | Hin_macView].
      -- right.
         rewrite <- Heq_Hacc.
         exists accHigh.
         split.
         --- exact Hin_accs.
         --- unfold account_view.
             rewrite HaccHighView_eq.
             simpl.
             split; [ |split]; try split.
             ---- symmetry. exact HaccHigh_user.
             ---- right. symmetry. exact HaccHigh_service.
             ---- left. reflexivity.
             ---- right. symmetry. exact HaccHigh_priv.
      -- apply (Haccs Hacc).
         exact Hin_macView.
    - unfold subset_files in *.
      rewrite newMacView_eq.
      simpl.
      exact Hfiles.
    - unfold subset_neighbours in *.
      rewrite newMacView_eq.
      simpl.
      exact Hneighs.
    - unfold subset_exploits in *.
      rewrite newMacView_eq.
      simpl.
      exact Hexploits.
    - rewrite <- eq_m0 in env_macView. exact env_macView.
    - rewrite <- eq_m0 in network_m. exact network_m.
    - elim (validAttackerIV m0 mac1 mac2).
      intros Hserv. intro Hserv'.
      destruct Hserv' as [Haccs Hserv''].
      destruct Hserv'' as [Hfiles Hserv'''].
      destruct Hserv''' as [Hneighs Hexploits].
      split; [|split; [|split]]; try split.
      -- exact Hserv.
      -- exact Haccs.
      -- exact Hfiles.
      -- exact Hneighs.
      -- exact Hexploits.
      -- rewrite <- (enviroment_eq (enviroment a) (enviroment a') m0 m newMacView).
         --- exact env_a'_m0.
         --- exact eq_m0.
         --- exact env_a'.
      -- exact network_m0.
  Qed.