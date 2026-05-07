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
    intros m0 mac1 env_a'_m0.

    case (idMachine_eq m0 m'); intros eq_m0.
    - (* m0 = m' *)
      exists mac.
      split.
      + rewrite eq_m0. exact network_m.
      + assert (Heq_mac1: mac1 = newMacView').
        {
          apply (enviroment_simpl (enviroment a) (enviroment a') m0 m' mac1 newMacView').
          - exact eq_m0.
          - exact env_a'.
          - exact env_a'_m0.
        }
        rewrite Heq_mac1.
        destruct (validAttackerIV m0 macView') as [mac'' [Hnetwork' Hmv]].
        { rewrite <- eq_m0 in env_m. exact env_m. }
        assert (Heq_mac': mac'' = mac).
        {
          apply (enviroment_map_image network m' mac'' mac).
          - rewrite <- eq_m0. exact Hnetwork'.
          - exact network_m.
        }
        rewrite Heq_mac' in Hmv.
        destruct Hmv as [Hserv [Haccs [Hfiles [Hneighs Hexploits]]]].
        unfold is_machineView.
        split; [|split; [|split]]; try split.
        -- unfold subset_services in *.
           rewrite newMacView_eq.
           simpl.
           rewrite servicesNewView_eq.
           rewrite portsServices_eq.
           intros s' Hin_oplus.
           apply oplusServices_membership in Hin_oplus.
           destruct Hin_oplus as [ Hin_macView | Hin_mac ].
           --- apply Hserv. exact Hin_macView.
           --- apply (scanServices_subset s' (machine_services mac) l). exact Hin_mac.
        -- unfold subset_accounts in *.
           rewrite newMacView_eq.
           simpl.
           exact Haccs.
        -- unfold subset_files in *.
           rewrite newMacView_eq.
           simpl.
           exact Hfiles.
        -- unfold subset_neighbours in *.
           rewrite newMacView_eq.
           simpl.
           exact Hneighs.
        -- unfold subset_exploits in *.
           rewrite newMacView_eq.
           simpl.
           exact Hexploits.
    - (* m0 <> m' *)
      destruct (validAttackerIV m0 mac1) as [mac2 [Hn2 Hmv]].
      { rewrite <- (enviroment_eq (enviroment a) (enviroment a') m0 m' newMacView').
        - exact env_a'_m0.
        - exact eq_m0.
        - exact env_a'.
      }
      exists mac2.
      split; assumption.
  Qed.