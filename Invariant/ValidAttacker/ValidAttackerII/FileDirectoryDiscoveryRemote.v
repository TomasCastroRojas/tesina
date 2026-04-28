Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmasEnviroment.
Require Import Invariant.AuxLemmas.AuxLemmasSecret.
Require Import Invariant.AuxLemmas.AuxLemmasFile.
Require Import Invariant.AuxTactics.

Lemma one_step_file_directory_discovery_remote_preserves_valid_attacker_ii : forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n) (m m': idMachine) (u u': idUser) (k': option key) (p':path) (s': idService),
      valid_concrete_network n -> Pre a (File_Directory_Discovery_Remote m u m' u' k' p' s') -> Post a (File_Directory_Discovery_Remote m u m' u' k' p' s') n a' -> valid_attacker_ii a'.
  Proof.
    intros a a' network validAttacker m m' u u' k' p' s' validNetwork pre post.
    unfold valid_attacker_ii.
    intros m0 p0 H_secrets_a'.
    unfold valid_attacker in validAttacker.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    clear validAttackerI validAttacker''.
    unfold Pre in pre; unfold Post in post.

    elim_intro_clear post known_machines_a' post'.
    elim_intro_clear post' Hmastered post.
    elim_intro_clear post mac post'.
    elim_intro_clear post' macView post.
    elim_intro_clear post newMacView post'.
    elim_intro_clear post' filesMac post.
    elim_intro_clear post filesNewMacView post'.
    elim_intro_clear post' newSecrets post.
    elim_intro_clear post env_m post'.
    elim_intro_clear post' network_m post.
    elim_intro_clear post filesMac_eq post'.
    elim_intro_clear post' newSecrets_eq post.
    elim_intro_clear post secrets_eq post'.
    elim_intro_clear post' filesNewMacView_eq post.
    elim_intro_clear post newMacView_eq env_a'.

    unfold valid_attacker_ii in validAttackerII.

    rewrite secrets_eq in H_secrets_a'.
    apply oplusSecrets_membership in H_secrets_a'.
    destruct H_secrets_a' as [Hin_old | Hin_new].

    - elim (validAttackerII m0 p0 Hin_old).
      intros MAC IH.
      elim_intro_clear IH env_MAC paths_MAC.
      case (idMachine_eq m0 m'); intro eq_m0.
      -- exists newMacView.
         split.
         --- rewrite env_a'.
             unfold modify_machine.
             case (idMachine_eq m0 m'); intros.
             ---- reflexivity.
             ---- contradiction.
         --- unfold registered_paths.
             rewrite newMacView_eq.
             simpl.
             rewrite filesNewMacView_eq.
             assert (macView = MAC) as Hmac.
             ---- apply (enviroment_map_image (enviroment a) m' macView MAC).
                  ----- exact env_m.
                  ----- rewrite <- eq_m0. exact env_MAC.
             ---- rewrite <- Hmac in paths_MAC.
                  unfold registered_paths in paths_MAC.
                  destruct paths_MAC as [f' [Hpath' Hin_f']].
                  apply (oplusFiles_dest_path_preserved p0 filesMac
                                                        (machine_fileSystem macView)).
                  exists f'. split. exact Hpath'. exact Hin_f'.

      -- exists MAC.
         rewrite (enviroment_eq (enviroment a) (enviroment a') m0 m' newMacView).
         --- split.
             ---- exact env_MAC.
             ---- exact paths_MAC.
         --- exact eq_m0.
         --- exact env_a'.

    - rewrite newSecrets_eq in Hin_new.
      apply getPaths_objectives_membership in Hin_new.
      destruct Hin_new as [Hm0 [f [Hin_f Hpath_f]]].
      exists newMacView.
      split.
      -- rewrite Hm0.
         rewrite env_a'.
         unfold modify_machine.
         case (idMachine_eq m' m'); intro.
         --- reflexivity.
         --- contradiction.
      -- unfold registered_paths.
         rewrite newMacView_eq.
         simpl.
         rewrite filesNewMacView_eq.
         destruct (oplusFiles_source_path_in f filesMac
                                             (machine_fileSystem macView) Hin_f)
           as [f' [Hpath' Hin_f']].
         exists f'. split.
         --- rewrite Hpath'. exact Hpath_f.
         --- exact Hin_f'.
  Qed.