Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.
Require Import Technique.TechniqueOneStep.

Require Import Invariant.AuxLemmas.AuxLemmas.
Require Import Invariant.AuxTactics.

Require Import Invariant.ValidAttacker.ValidAttackerIII.RemoteServices.
Require Import Invariant.ValidAttacker.ValidAttackerIII.ExploitationRemoteServices.
Require Import Invariant.ValidAttacker.ValidAttackerIII.RemoteSystemDiscovery.
Require Import Invariant.ValidAttacker.ValidAttackerIII.SystemServiceDiscovery.
Require Import Invariant.ValidAttacker.ValidAttackerIII.FileDirectoryDiscoveryLocal.

Theorem one_step_preserves_valid_attacker_iii : forall (a a' : Attacker) (t : Technique) (n: network_map),
      one_step a t n a' -> valid_attacker_iii a'.
  Proof.
    intros a a' t n onestep.
    destruct onestep.
    induction t; unfold valid_attacker in H0; unfold valid_concrete_network in H;
    unfold Pre in H1; unfold Post in H2; unfold valid_attacker_iii.
    - apply (one_step_remote_services_preserves_valid_attacker_iii a a' network H0 i i1 i0 i2 k i3); auto.
    - apply (one_step_exploitation_remote_services_preserves_valid_attacker_iii a a' network H0 i i1 i0 i2 i3); auto.
    - admit. (* Unsecured_Credentials *)
    - admit. (* Brute_Force *)
    - admit. (* Abuse_Elevation_Control_Mechanism *)
    - apply (one_step_file_directory_discovery_local_preserves_valid_attacker_iii a a' network H0 i i0 p); auto.
    - admit. (* File_Directory_Discovery_Remote *)
    - admit. (* Network_Service_Scanning *)
    - apply (one_step_remote_system_discovery_preserves_valid_attacker_iii a a' network H0 i i0); auto.
    - admit. (* Account_Discovery_Local *)
    - admit. (* Account_Discovery_Remote *)
    - apply (one_step_system_service_discovery_preserves_valid_attacker_iii a a' network H0 i i0); auto.
  Admitted.