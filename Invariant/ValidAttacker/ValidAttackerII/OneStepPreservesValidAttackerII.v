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

Require Import Invariant.ValidAttacker.ValidAttackerII.RemoteServices.
Require Import Invariant.ValidAttacker.ValidAttackerII.ExploitationRemoteServices.
Require Import Invariant.ValidAttacker.ValidAttackerII.RemoteSystemDiscovery.
Require Import Invariant.ValidAttacker.ValidAttackerII.SystemServiceDiscovery.
Require Import Invariant.ValidAttacker.ValidAttackerII.FileDirectoryDiscoveryLocal.
Require Import Invariant.ValidAttacker.ValidAttackerII.FileDirectoryDiscoveryRemote.
Require Import Invariant.ValidAttacker.ValidAttackerII.UnsecuredCredentials.
Require Import Invariant.ValidAttacker.ValidAttackerII.BruteForce.
Require Import Invariant.ValidAttacker.ValidAttackerII.AccountDiscoveryLocal.
Require Import Invariant.ValidAttacker.ValidAttackerII.AccountDiscoveryRemote.

Theorem one_step_preserves_valid_attacker_ii : forall (a a' : Attacker) (t : Technique) (n: network_map),
      one_step a t n a' -> valid_attacker_ii a'.
  Proof.
    intros a a' t n onestep.
    destruct onestep.
    induction t; unfold valid_attacker in H0; unfold valid_concrete_network in H;
    unfold Pre in H1; unfold Post in H2; unfold valid_attacker_ii.
    - apply (one_step_remote_services_preserves_valid_attacker_ii a a' network H0 i i1 i0 i2 o i3); auto.
    - apply (one_step_exploitation_remote_services_preserves_valid_attacker_ii a a' network H0 i i1 i0 i2 i3); auto.
    - apply (one_step_unsecured_credentials_preserves_valid_attacker_ii a a' network H0 i i0 i1); auto.
    - apply (one_step_brute_force_preserves_valid_attacker_ii a a' network H0 i i1 i0 i2 i3); auto.
    - admit. (* Abuse_Elevation_Control_Mechanism *)
    - apply (one_step_file_directory_discovery_local_preserves_valid_attacker_ii a a' network H0 i i0 p); auto.
    - apply (one_step_file_directory_discovery_remote_preserves_valid_attacker_ii a a' network H0 i i1 i0 i2 o p i3); auto.
    - admit. (* Network_Service_Scanning *)
    - apply (one_step_remote_system_discovery_preserves_valid_attacker_ii a a' network H0 i i0); auto.
    - apply (one_step_account_discovery_local_preserves_valid_attacker_ii a a' network H0 i i0 i1); auto.
    - apply (one_step_account_discovery_remote_preserves_valid_attacker_ii a a' network H0 i i1 i0 i2 o i3); auto.
    - apply (one_step_system_service_discovery_preserves_valid_attacker_ii a a' network H0 i i0); auto.
  Admitted.