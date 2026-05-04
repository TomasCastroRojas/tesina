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
Require Import Invariant.AuxLemmas.AuxLemmasService.
Require Import Invariant.AuxTactics.

Lemma one_step_network_service_scanning_preserves_valid_attacker_iv : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m m': idMachine) (u : idUser) (l: list nat),
      valid_concrete_network n -> Pre a (Network_Service_Scanning m u m' l) -> Post a (Network_Service_Scanning m u m' l) n a' -> valid_attacker_iv a' n.
  Proof.
    intros a a' network validAttacker m m' u l validNetwork pre post.
    unfold valid_attacker_iv.
    unfold is_networkView.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttackerIV.
    unfold Pre in pre; unfold Post in post.
    clear validAttackerI validAttackerII validAttackerIII.

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

    unfold valid_attacker_iv in validAttackerIV.
    unfold is_networkView in validAttackerIV.
    intros m0 mac1 mac2 env_a'_m0 network_m0.
    unfold is_machineView.

    case (idMachine_eq m0 m'); intros eq_m0.
    elim (validAttackerIV m0 macView' mac).
    intros Hserv. intro Hserv'.
    destruct Hserv' as [Haccs Hserv''].
    destruct Hserv'' as [Hfiles Hserv'''].
    destruct Hserv''' as [Hneighs Hexploits].
    assert (Heq_mac1: mac1 = newMacView').
    {
      apply (enviroment_simpl (enviroment a) (enviroment a') m0 m' mac1 newMacView').
      - exact eq_m0.
      - exact env_a'.
      - exact env_a'_m0.
    }
    assert (Heq_mac2: mac2 = mac).
    {
      apply (enviroment_map_image network m' mac2 mac).
      - rewrite eq_m0 in network_m0. exact network_m0.
      - exact network_m.
    }
    rewrite Heq_mac1.
    rewrite Heq_mac2.
    split; [|split; [|split]]; try split.
    - unfold subset_services in *.
      rewrite newMacView_eq.
      simpl.
      rewrite servicesNewView_eq.
      rewrite portsServices_eq.
      intros s' Hin_oplus.
      apply oplusServices_membership in Hin_oplus.
      destruct Hin_oplus as [ Hin_macView | Hin_mac ].
      -- apply Hserv. exact Hin_macView.
      -- apply (scanServices_subset s' (machine_services mac) l). exact Hin_mac.
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
      exact Hneighs.
    - unfold subset_exploits in *.
      rewrite newMacView_eq.
      simpl.
      exact Hexploits.
    - rewrite <- eq_m0 in env_m. exact env_m.
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
      -- rewrite <- (enviroment_eq (enviroment a) (enviroment a') m0 m' newMacView').
         --- exact env_a'_m0.
         --- exact eq_m0.
         --- exact env_a'.
      -- exact network_m0.
  Qed.