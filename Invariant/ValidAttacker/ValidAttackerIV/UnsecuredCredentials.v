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

Lemma one_step_unsecured_credentials_preserves_valid_attacker_iv : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m : idMachine) (u : idUser) (s: idService),
      valid_concrete_network n -> Pre a (Unsecured_Credentials m u s) -> Post a (Unsecured_Credentials m u s) n a' -> valid_attacker_iv a' n.
  Proof.
    intros a a' network validAttacker m u s validNetwork pre post.
    unfold valid_attacker_iv.
    unfold is_networkView.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    elim_intro_clear validAttacker'' validAttackerIII validAttackerIV.
    unfold Pre in pre; destruct post.
    clear validAttackerI validAttackerII validAttackerIII.

    elim_intro_clear H0 Hsecrets H0'.
    elim_intro_clear H0' mac H0.
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
      rewrite accsNewView_eq.
      intros Hacc Hin_oplus.
      apply member_oplusAccounts_simpl in Hin_oplus.
      destruct Hin_oplus as [Hin_linked | Hin_accsView].
      -- (* Hacc proviene de accsLinkedToUser: esta en machine_accounts mac *)
         left.
         rewrite accsLinked_eq in Hin_linked.
         rewrite accs_mac.
         apply (get_accounts_linked_service_with_key_in u s accs).
         exact Hin_linked.
      -- (* Hacc proviene de accsView: usar hipotesis Haccs *)
         rewrite <- accsView_eq in Hin_accsView.
         apply Haccs. exact Hin_accsView.
    - unfold subset_files in *.
      rewrite newMacView_eq.
      simpl.
      exact Hfiles.
    - unfold subset_neighbours in *.
      rewrite newMacView_eq.
      simpl.
      exact Hneighs.
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