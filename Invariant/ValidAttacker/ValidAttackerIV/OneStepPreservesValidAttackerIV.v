Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.
Require Import Technique.TechniqueOneStep.

Require Import Invariant.AuxTactics.

Require Import Invariant.ValidAttacker.ValidAttackerIV.RemoteServices.
Require Import Invariant.ValidAttacker.ValidAttackerIV.ExploitationRemoteServices.
Require Import Invariant.ValidAttacker.ValidAttackerIV.RemoteSystemDiscovery.
Require Import Invariant.ValidAttacker.ValidAttackerIV.SystemServiceDiscovery.
Require Import Invariant.ValidAttacker.ValidAttackerIV.FileDirectoryDiscoveryLocal.
Require Import Invariant.ValidAttacker.ValidAttackerIV.FileDirectoryDiscoveryRemote.
Require Import Invariant.ValidAttacker.ValidAttackerIV.UnsecuredCredentials.
Require Import Invariant.ValidAttacker.ValidAttackerIV.BruteForce.
Require Import Invariant.ValidAttacker.ValidAttackerIV.AccountDiscoveryLocal.
Require Import Invariant.ValidAttacker.ValidAttackerIV.AccountDiscoveryRemote.
Require Import Invariant.ValidAttacker.ValidAttackerIV.AbuseElevationControlMechanism.
Require Import Invariant.ValidAttacker.ValidAttackerIV.NetworkServiceScanning.

Theorem one_step_preserves_valid_attacker_iv : forall (a a' : Attacker) (t : Technique) (n: network_map),
      one_step a t n a' -> valid_attacker_iv a' n.
  Proof.
    intros a a' t n onestep.
    destruct onestep.
    induction t; unfold valid_attacker in H0; unfold valid_concrete_network in H;
    unfold Pre in H1; unfold Post in H2; unfold valid_attacker_iv.
    - apply (one_step_remote_services_preserves_valid_attacker_iv a a' network H0 i i1 i0 i2 o i3); auto.
    - apply (one_step_exploitation_remote_services_preserves_valid_attacker_iv a a' network H0 i i1 i0 i2 i3); auto.
    - apply (one_step_unsecured_credentials_preserves_valid_attacker_iv a a' network H0 i i0 i1); auto.
    - apply (one_step_brute_force_preserves_valid_attacker_iv a a' network H0 i i1 i0 i2 i3); auto.
    - apply (one_step_abuse_elevation_control_mechanism_preserves_valid_attacker_iv a a' network H0 i i0); auto.
    - apply (one_step_file_directory_discovery_local_preserves_valid_attacker_iv a a' network H0 i i0 p); auto.
    - apply (one_step_file_directory_discovery_remote_preserves_valid_attacker_iv a a' network H0 i i1 i0 i2 o p i3); auto.
    - apply (one_step_network_service_scanning_preserves_valid_attacker_iv a a' network H0 i i1 i0 l); auto.
    - apply (one_step_remote_system_discovery_preserves_valid_attacker_iv a a' network H0 i i0); auto.
    - apply (one_step_account_discovery_local_preserves_valid_attacker_iv a a' network H0 i i0 i1); auto.
    - apply (one_step_account_discovery_remote_preserves_valid_attacker_iv a a' network H0 i i1 i0 i2 o i3); auto.
    - apply (one_step_system_service_discovery_preserves_valid_attacker_iv a a' network H0 i i0); auto.
  Qed.