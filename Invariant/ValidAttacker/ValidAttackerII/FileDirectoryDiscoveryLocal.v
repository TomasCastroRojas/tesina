Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineValid.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.
Require Import Technique.Technique.
Require Import Technique.TechniquePreCondition.
Require Import Technique.TechniquePostCondition.

Require Import Invariant.AuxLemmas.AuxLemmas.
Require Import Invariant.AuxTactics.

Lemma one_step_file_directory_discovery_local_preserves_valid_attacker_ii :
    forall (a a' : Attacker) (n: network_map) (aValid: valid_attacker a n)
           (m: idMachine) (u: idUser) (p: path),
      valid_concrete_network n ->
      Pre a (File_Directory_Discovery_Local m u p) ->
      Post a (File_Directory_Discovery_Local m u p) n a' ->
      valid_attacker_ii a'.
  Proof.
    intros a a' network validAttacker m u p validNetwork pre post.
    unfold valid_attacker_ii.
    intros m0 p0 H_secrets_a'.
    unfold valid_attacker in validAttacker.
    elim_intro_clear validAttacker validAttackerI validAttacker'.
    elim_intro_clear validAttacker' validAttackerII validAttacker''.
    clear validAttackerI validAttacker''.
    unfold Pre in pre; destruct post.

    (* Descomposicion de los 6 existenciales del Post *)
    elim_intro_clear H0 mac H0'.
    elim_intro_clear H0' macView H0''.
    elim_intro_clear H0'' newMacView H0'''.
    elim_intro_clear H0''' filesMac H0''''.
    elim_intro_clear H0'''' filesNewMacView H0'''''.
    elim_intro_clear H0''''' newSecrets H1.

    (* Descomposicion de la conjuncion de 8 partes *)
    elim_intro_clear H1 env_m H1'.
    elim_intro_clear H1' network_m H1''.
    elim_intro_clear H1'' filesMac_eq H1'''.
    elim_intro_clear H1''' newSecrets_eq H1''''.
    elim_intro_clear H1'''' secrets_eq H1'''''.
    elim_intro_clear H1''''' filesNewMacView_eq H1''''''.
    elim_intro_clear H1'''''' newMacView_eq env_a'.

    unfold valid_attacker_ii in validAttackerII.

    (* Dividir: el secreto viene de secrets a o de newSecrets *)
    rewrite secrets_eq in H_secrets_a'.
    apply oplusSecrets_membership in H_secrets_a'.
    destruct H_secrets_a' as [Hin_old | Hin_new].

    (* Caso 1: (m0, p0) estaba en secrets a *)
    - elim (validAttackerII m0 p0 Hin_old).
      intros MAC IH.
      elim_intro_clear IH env_MAC paths_MAC.
      case (idMachine_eq m0 m); intro eq_m0.

      (* m0 = m: la maquina fue modificada, testigo newMacView *)
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
             rewrite filesNewMacView_eq.
             (* registered_paths macView p0 => existe f en macView con path p0
                Necesitamos ese f siga estando en oplusFiles filesMac (machine_fileSystem macView)
                Requiere oplusFiles_dest_path_preserved (admitido por bug en addFile) *)
             assert (macView = MAC) as Hmac.
             ---- apply (enviroment_map_image (enviroment a) m macView MAC).
                  ----- exact env_m.
                  ----- rewrite <- eq_m0. exact env_MAC.
             ---- rewrite <- Hmac in paths_MAC.
                  unfold registered_paths in paths_MAC.
                  destruct paths_MAC as [f' [Hpath' Hin_f']].
                  apply (oplusFiles_dest_path_preserved p0 filesMac
                                                        (machine_fileSystem macView)).
                  exists f'. split. exact Hpath'. exact Hin_f'.

      (* m0 ≠ m: modify_machine no toca m0, testigo MAC *)
      -- exists MAC.
         rewrite (enviroment_eq (enviroment a) (enviroment a') m0 m newMacView).
         --- split.
             ---- exact env_MAC.
             ---- exact paths_MAC.
         --- exact eq_m0.
         --- exact env_a'.

    (* Caso 2: (m0, p0) es un secreto nuevo de getPaths_objectives *)
    - rewrite newSecrets_eq in Hin_new.
      apply getPaths_objectives_membership in Hin_new.
      destruct Hin_new as [Hm0 [f [Hin_f Hpath_f]]].
      exists newMacView.
      split.
      -- (* (enviroment a') m0 = Some newMacView *)
         rewrite Hm0.
         rewrite env_a'.
         unfold modify_machine.
         case (idMachine_eq m m); intro.
         --- reflexivity.
         --- contradiction.
      -- (* registered_paths newMacView p0 *)
         unfold registered_paths.
         rewrite newMacView_eq.
         simpl.
         rewrite filesNewMacView_eq.
         (* f esta en filesMac con file_path f = p0.
            Necesitamos que siga en oplusFiles filesMac (machine_fileSystem macView).
            Requiere oplusFiles_source_path_in (admitido por bug en addFile) *)
         destruct (oplusFiles_source_path_in f filesMac
                                             (machine_fileSystem macView) Hin_f)
           as [f' [Hpath' Hin_f']].
         exists f'. split.
         --- rewrite Hpath'. exact Hpath_f.
         --- exact Hin_f'.
  Qed.