Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Machine.MachineView.

Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmas.
Require Import Invariant.AuxTactics.

Lemma one_step_remote_system_discovery_preserves_valid_attacker_iv : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m : idMachine) (u: idUser),
      valid_concrete_network n -> Pre a (Remote_System_Discovery m u) -> Post a (Remote_System_Discovery m u) n a' -> valid_attacker_iv a' n.
  Proof.
    intros a a' network validAttacker m u validNetwork pre post.
    unfold valid_attacker_iv.
    unfold is_networkView.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttackerIV.
    unfold Pre in pre; destruct post.
    clear validAttackerI validAttackerII validAttackerIII.

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

    unfold valid_attacker_iv in validAttackerIV.
    unfold is_networkView in validAttackerIV.
    intros m0 mac1 mac2 env_a'_m0 network_m0.
    unfold is_machineView.

    case (idMachine_eq m0 m); intros eq_m0.
    elim (validAttackerIV m0 macView mac).
    intros Hserv. intro Hserv'.
    destruct Hserv' as [Haccs Hserv'']. 
    destruct Hserv'' as [Hfiles Hneighs].
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
    split; [|split]; try split.
    - unfold subset_services in *.
      rewrite newMacView_eq.
      simpl.
      exact Hserv.
    - unfold subset_accounts in *.
      rewrite newMacView_eq.
      simpl.
      exact Haccs.
    - unfold subset_files in *.
      rewrite newMacView_eq.
      simpl.
      exact Hfiles.
    - unfold subset_neighbours in *.
      rewrite newMacView_eq.
      simpl.
      rewrite newNeighbours_eq.
      intros m' Hin_oplus.
      apply oplusNeighbours_membership in Hin_oplus.
      destruct Hin_oplus as [ Hin_macView | Hin_mac ].
      -- apply Hneighs.
         exact Hin_macView.
      -- rewrite macNeighbours_eq in Hin_mac.
         exact Hin_mac.
    - rewrite <- eq_m0 in env_m. exact env_m.
    - rewrite <- eq_m0 in network_m. exact network_m.
    - elim (validAttackerIV m0 mac1 mac2).
      intros Hserv. intro Hserv'.
      destruct Hserv' as [Haccs Hserv''].
      destruct Hserv'' as [Hfiles Hneighs].
      split; [|split]; try split.
      -- exact Hserv.
      -- exact Haccs.
      -- exact Hfiles.
      -- exact Hneighs.
      -- rewrite <- (enviroment_eq (enviroment a) (enviroment a') m0 m newMacView).
         --- exact env_a'_m0.
         --- exact eq_m0.
         --- exact env_a'.
      -- exact network_m0.
  Qed.