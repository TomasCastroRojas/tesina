Require Import Coq.Lists.List.

Require Import Machine.Machine.
Require Import Machine.MachineAuxFunctions.
Require Import Machine.MachineView.
Require Import Machine.MachineValid.

(* ===== Lemas sobre getPaths_objectives ===== *)

  (* Si (m0,p0) pertenece al resultado de getPaths_objectives, entonces m0 = m
     y existe un archivo en la lista con path p0 marcado como objetivo *)
  Lemma getPaths_objectives_membership : forall (m0: idMachine) (p0: path)
                                                (files: list File) (m: idMachine),
    In (m0, p0) (getPaths_objectives files m) ->
    m0 = m /\ exists f, In f files /\ file_path f = p0.
  Proof.
    intros m0 p0 files m.
    induction files as [| f files' IH].
    - simpl. intros [].
    - simpl.
      destruct (file_objective f) eqn:Hobj.
      + simpl. intros [Heq | Hrest].
        * injection Heq as Hm Hp.
          split. symmetry. exact Hm.
          exists f. split. left. reflexivity. exact Hp.
        * apply IH in Hrest.
          destruct Hrest as [Hm [f' [Hin Hpath]]].
          split. exact Hm. exists f'. split. right. exact Hin. exact Hpath.
      + intros H. apply IH in H.
        destruct H as [Hm [f' [Hin Hpath]]].
        split. exact Hm. exists f'. split. right. exact Hin. exact Hpath.
  Qed.


  (* ===== Lemas sobre funciones auxiliares de archivos (addUser, mergeUsers, addPath, mergePaths) ===== *)

  (* Si u pertenece a addUser u' l, entonces u = u' o u ya estaba en l *)
  Lemma addUser_membership : forall (u u': idUser) (l: list idUser),
    In u (addUser u' l) -> u = u' \/ In u l.
  Proof.
    intros u u' l. induction l as [| v vs IH]; simpl.
    - intros [H | []]. left. symmetry. exact H.
    - destruct (idUser_eq u' v) as [Heq | Hneq].
      + intro H. right. exact H.
      + simpl. intros [H | H].
        * right. left. exact H.
        * destruct (IH H) as [Heq | Hin].
          -- left. exact Heq.
          -- right. right. exact Hin.
  Qed.

  (* addUser u l siempre contiene u en el resultado *)
  Lemma addUser_self : forall (u : idUser) (l : list idUser),
    In u (addUser u l).
  Proof.
    intros u l. induction l as [| v vs IH]; simpl.
    - left. reflexivity.
    - destruct (idUser_eq u v) as [Heq | Hneq].
      + rewrite Heq. left. reflexivity.
      + simpl. right. exact IH.
  Qed.

  (* addUser preserva todos los usuarios ya presentes en la lista *)
  Lemma addUser_preserves_membership : forall (u u' : idUser) (l : list idUser),
    In u l -> In u (addUser u' l).
  Proof.
    intros u u' l. induction l as [| v vs IH]; intros Hin; simpl in *.
    - contradiction.
    - destruct (idUser_eq u' v) as [Heq | Hneq].
      + exact Hin.
      + simpl. destruct Hin as [Heq_v | Hin_vs].
        * left. exact Heq_v.
        * right. exact (IH Hin_vs).
  Qed.

  (* Todo elemento de mergeUsers proviene de source o de dest *)
  Lemma mergeUsers_membership : forall (u: idUser) (source dest: list idUser),
    In u (mergeUsers source dest) -> In u source \/ In u dest.
  Proof.
    intros u source. induction source as [| u' us IH]; intros dest H; simpl in *.
    - right. exact H.
    - apply IH in H. destruct H as [H | H].
      + left. right. exact H.
      + apply addUser_membership in H. destruct H as [Heq | Hin].
        * left. left. symmetry. exact Heq.
        * right. exact Hin.
  Qed.

  (* Los elementos del destino se preservan en mergeUsers *)
  Lemma mergeUsers_dest_preserved : forall (u : idUser) (source dest : list idUser),
    In u dest -> In u (mergeUsers source dest).
  Proof.
    intros u source. induction source as [| u' us IH]; intros dest Hin; simpl.
    - exact Hin.
    - apply IH. apply addUser_preserves_membership. exact Hin.
  Qed.

  (* Los elementos del source se preservan en mergeUsers *)
  Lemma mergeUsers_source_preserved : forall (u : idUser) (source dest : list idUser),
    In u source -> In u (mergeUsers source dest).
  Proof.
    intros u source. induction source as [| u' us IH]; intros dest Hin; simpl in *.
    - contradiction.
    - destruct Hin as [Heq | Hin_us].
      + rewrite Heq. apply mergeUsers_dest_preserved. apply addUser_self.
      + apply IH. exact Hin_us.
  Qed.

  (* Si p pertenece a addPath p' l, entonces p = p' o p ya estaba en l *)
  Lemma addPath_membership : forall (p p': path) (l: list path),
    In p (addPath p' l) -> p = p' \/ In p l.
  Proof.
    intros p p' l. induction l as [| q qs IH]; simpl.
    - intros [H | []]. left. symmetry. exact H.
    - destruct (path_eq p' q) as [Heq | Hneq].
      + intro H. right. exact H.
      + simpl. intros [H | H].
        * right. left. exact H.
        * destruct (IH H) as [Heq | Hin].
          -- left. exact Heq.
          -- right. right. exact Hin.
  Qed.

  (* Todo elemento de mergePaths proviene de source o de dest *)
  Lemma mergePaths_membership : forall (p: path) (source dest: list path),
    In p (mergePaths source dest) -> In p source \/ In p dest.
  Proof.
    intros p source. induction source as [| p' ps IH]; intros dest H; simpl in *.
    - right. exact H.
    - apply IH in H. destruct H as [H | H].
      + left. right. exact H.
      + apply addPath_membership in H. destruct H as [Heq | Hin].
        * left. left. symmetry. exact Heq.
        * right. exact Hin.
  Qed.


  (* ===== Lemas sobre archivos (addFile / oplusFiles) ===== *)

  (* addFile siempre produce un archivo con el mismo path que f en el resultado *)
  Lemma addFile_source_path_in : forall (f: File) (files: list File),
    exists f', file_path f' = file_path f /\ In f' (addFile f files).
  Proof.
    intros f files.
    induction files as [| f0 files' IH].
    - simpl. exists f. split. reflexivity. left. reflexivity.
    - simpl.
      case (path_eq (file_path f) (file_path f0)); intro eq_path.
      + (* paths coinciden: resultado es merged :: files' *)
        exists (file (file_path f)
                     (mergePaths (file_subfiles f) (file_subfiles f0))
                     (mergeUsers (file_user_access f) (file_user_access f0))
                     (file_objective f)).
        split. simpl. reflexivity. left. reflexivity.
      + (* paths distintos: resultado es f0 :: addFile f files' *)
        destruct IH as [f' [Hpath' Hin']].
        exists f'. split. exact Hpath'. right. exact Hin'.
  Qed.

  (* Si un path estaba registrado en dest, sigue estando en addFile f_add dest *)
  Lemma addFile_dest_path_preserved : forall (p: path) (f_add: File) (dest: list File),
    (exists g, file_path g = p /\ In g dest) ->
    exists g', file_path g' = p /\ In g' (addFile f_add dest).
  Proof.
    intros p f_add dest.
    induction dest as [| f0 dest' IH].
    - intros [g [_ []]].
    - intros [g [Hpath_g Hin_g]].
      simpl.
      case (path_eq (file_path f_add) (file_path f0)); intro eq_path.
      + (* paths coinciden: resultado es merged :: dest' *)
        simpl in Hin_g.
        destruct Hin_g as [Heq_g | Hin_g'].
        * (* f0 = g: el path de g coincide con file_path f_add = file_path f0 *)
          exists (file (file_path f_add)
                       (mergePaths (file_subfiles f_add) (file_subfiles f0))
                       (mergeUsers (file_user_access f_add) (file_user_access f0))
                       (file_objective f_add)).
          split.
          -- simpl. rewrite eq_path. rewrite Heq_g. exact Hpath_g.
          -- left. reflexivity.
        * (* In g dest': g sigue en merged :: dest' via right *)
          exists g. split.
          -- exact Hpath_g.
          -- right. exact Hin_g'.
      + (* paths distintos: resultado es f0 :: addFile f_add dest' *)
        simpl in Hin_g.
        destruct Hin_g as [Heq_g | Hin_g'].
        * (* f0 = g *)
          exists f0. split.
          -- rewrite Heq_g. exact Hpath_g.
          -- left. reflexivity.
        * (* In g dest': por IH *)
          destruct (IH (ex_intro _ g (conj Hpath_g Hin_g'))) as [g' [Hpath_g' Hin_g'']].
          exists g'. split.
          -- exact Hpath_g'.
          -- right. exact Hin_g''.
  Qed.

  (* Si un path estaba registrado en dest, sigue estando en oplusFiles source dest *)
  Lemma oplusFiles_dest_path_preserved : forall (p: path) (source dest: list File),
    (exists f, file_path f = p /\ In f dest) ->
    exists f', file_path f' = p /\ In f' (oplusFiles source dest).
  Proof.
    intros p source.
    induction source as [| f_add source' IH]; intros dest Hexists.
    - simpl. exact Hexists.
    - simpl.
      apply IH.
      apply addFile_dest_path_preserved.
      exact Hexists.
  Qed.

  (* Si f_src esta en source, su path aparece en oplusFiles source dest *)
  Lemma oplusFiles_source_path_in : forall (f_src: File) (source dest: list File),
    In f_src source ->
    exists f', file_path f' = file_path f_src /\ In f' (oplusFiles source dest).
  Proof.
    intros f_src source.
    induction source as [| f source' IH]; intros dest Hin_src.
    - simpl in Hin_src. contradiction.
    - simpl in Hin_src. simpl.
      destruct Hin_src as [Heq | Hin_src'].
      + (* f_src es la cabeza: f = f_src *)
        rewrite <- Heq.
        destruct (addFile_source_path_in f_src dest) as [f'' [Hpath'' Hin'']].
        rewrite Heq.
        apply (oplusFiles_dest_path_preserved (file_path f_src) source' (addFile f_src dest)).
        exists f''. split. exact Hpath''. exact Hin''.
      + (* f_src esta en la cola source' *)
        apply IH.
        exact Hin_src'.
  Qed.

  (* Los usuarios de un archivo resultado de addFile provienen del source o de algun archivo en dest *)
  Lemma addFile_user_in_source_or_dest :
    forall (f_src f_result : File) (dest : list File) (u0 : idUser),
      In f_result (addFile f_src dest) ->
      In u0 (file_user_access f_result) ->
      In u0 (file_user_access f_src) \/
      exists f_dst, In f_dst dest /\ In u0 (file_user_access f_dst).
  Proof.
    intros f_src f_result dest. revert f_result.
    induction dest as [| f0 dest' IH]; intros f_result u0 Hin Hu0.
    - simpl in Hin. destruct Hin as [Heq | []].
      left. rewrite Heq. exact Hu0.
    - simpl in Hin.
      destruct (path_eq (file_path f_src) (file_path f0)) as [Hpath | Hpath];
      simpl in Hin; destruct Hin as [Heq | Hin_rest].
      + rewrite <- Heq in Hu0. simpl in Hu0.
        apply mergeUsers_membership in Hu0.
        destruct Hu0 as [Hu_src | Hu_dst].
        * left. exact Hu_src.
        * right. exists f0. split. left. reflexivity. exact Hu_dst.
      + right. exists f_result. split. right. exact Hin_rest. exact Hu0.
      + right. exists f0. split. left. reflexivity. rewrite Heq. exact Hu0.
      + destruct (IH f_result u0 Hin_rest Hu0) as [Hu_src | [f_dst [Hin_dst Hu_dst]]].
        * left. exact Hu_src.
        * right. exists f_dst. split. right. exact Hin_dst. exact Hu_dst.
  Qed.

  (* Las subrutas de un archivo resultado de addFile provienen del source o de algun archivo en dest *)
  Lemma addFile_subfile_in_source_or_dest :
    forall (f_src f_result : File) (dest : list File) (p' : path),
      In f_result (addFile f_src dest) ->
      In p' (file_subfiles f_result) ->
      In p' (file_subfiles f_src) \/
      exists f_dst, In f_dst dest /\ In p' (file_subfiles f_dst).
  Proof.
    intros f_src f_result dest. revert f_result.
    induction dest as [| f0 dest' IH]; intros f_result p' Hin Hp'.
    - simpl in Hin. destruct Hin as [Heq | []].
      left. rewrite Heq. exact Hp'.
    - simpl in Hin.
      destruct (path_eq (file_path f_src) (file_path f0)) as [Hpath | Hpath];
      simpl in Hin; destruct Hin as [Heq | Hin_rest].
      + rewrite <- Heq in Hp'. simpl in Hp'.
        apply mergePaths_membership in Hp'.
        destruct Hp' as [Hp_src | Hp_dst].
        * left. exact Hp_src.
        * right. exists f0. split. left. reflexivity. exact Hp_dst.
      + right. exists f_result. split. right. exact Hin_rest. exact Hp'.
      + right. exists f0. split. left. reflexivity. rewrite Heq. exact Hp'.
      + destruct (IH f_result p' Hin_rest Hp') as [Hp_src | [f_dst [Hin_dst Hp_dst]]].
        * left. exact Hp_src.
        * right. exists f_dst. split. right. exact Hin_dst. exact Hp_dst.
  Qed.

  (* Las subrutas de un archivo en oplusFiles provienen de algun archivo en source o en dest *)
  Lemma oplusFiles_subfile_in_source_or_dest :
    forall (source dest : list File) (f : File) (p' : path),
      In f (oplusFiles source dest) ->
      In p' (file_subfiles f) ->
      (exists f_src, In f_src source /\ In p' (file_subfiles f_src)) \/
      (exists f_dst, In f_dst dest   /\ In p' (file_subfiles f_dst)).
  Proof.
    intros source. induction source as [| f_src source' IH]; intros dest f p' Hin Hp'.
    - simpl in Hin. right. exists f. split. exact Hin. exact Hp'.
    - simpl in Hin.
      destruct (IH (addFile f_src dest) f p' Hin Hp')
        as [[f_src' [Hin_src' Hp_src']] | [f_add [Hin_add Hp_add]]].
      + left. exists f_src'. split. right. exact Hin_src'. exact Hp_src'.
      + destruct (addFile_subfile_in_source_or_dest f_src f_add dest p' Hin_add Hp_add)
          as [Hp_fsrc | [f_dst [Hin_dst Hp_dst]]].
        * left. exists f_src. split. left. reflexivity. exact Hp_fsrc.
        * right. exists f_dst. split. exact Hin_dst. exact Hp_dst.
  Qed.

  (* Si f_src tiene usuario u en su acceso, entonces en addFile f_src dest
     el archivo resultado tambien tendra u, o bien el resultado ya estaba en dest sin modificar *)
  Lemma addFile_source_user_or_in_dest :
    forall (f_src f_res : File) (dest : list File) (u : idUser),
      In u (file_user_access f_src) ->
      In f_res (addFile f_src dest) ->
      In u (file_user_access f_res) \/ In f_res dest.
  Proof.
    intros f_src f_res dest. revert f_res.
    induction dest as [| f_elem rest IH]; intros f_res u Hu Hin; simpl in *.
    - destruct Hin as [Heq | []].
      left. rewrite <- Heq. exact Hu.
    - destruct (path_eq (file_path f_src) (file_path f_elem)) as [Hpath | Hpath];
      simpl in Hin; destruct Hin as [Heq | Hin_rest].
      + left. rewrite <- Heq. simpl.
        apply mergeUsers_source_preserved. exact Hu.
      + right. right. exact Hin_rest.
      + right. left. exact Heq.
      + destruct (IH f_res u Hu Hin_rest) as [Hleft | Hright].
        * left. exact Hleft.
        * right. right. exact Hright.
  Qed.

  (* Para todo archivo en oplusFiles source dest: si todos los archivos de source tienen usuario u,
     entonces el archivo resultado tambien tendra u, o bien proviene de dest sin modificar *)
  Lemma oplusFiles_source_user_or_in_dest :
    forall (source dest : list File) (f : File) (u : idUser),
      (forall f_src, In f_src source -> In u (file_user_access f_src)) ->
      In f (oplusFiles source dest) ->
      In u (file_user_access f) \/ In f dest.
  Proof.
    intros source. induction source as [| f_head rest IH]; intros dest f u Hforall Hin; simpl in *.
    - right. exact Hin.
    - assert (Hrest : forall f_src, In f_src rest -> In u (file_user_access f_src)).
      { intros f_src Hin_src. apply Hforall. right. exact Hin_src. }
      destruct (IH (addFile f_head dest) f u Hrest Hin) as [Hu_f | Hf_add].
      + left. exact Hu_f.
      + assert (Hu_head : In u (file_user_access f_head)).
        { apply Hforall. left. reflexivity. }
        exact (addFile_source_user_or_in_dest f_head f dest u Hu_head Hf_add).
  Qed.

  (* Si L1 y L2 son cerradas bajo subarchivos individualmente,
     entonces oplusFiles L1 L2 tambien lo es *)
  Lemma oplusFiles_subfiles_closed :
    forall (L1 L2 : list File),
      (forall f, In f L1 -> forall p', In p' (file_subfiles f) ->
        exists g, file_path g = p' /\ In g L1) ->
      (forall f, In f L2 -> forall p', In p' (file_subfiles f) ->
        exists g, file_path g = p' /\ In g L2) ->
      forall f, In f (oplusFiles L1 L2) -> forall p', In p' (file_subfiles f) ->
        exists g, file_path g = p' /\ In g (oplusFiles L1 L2).
  Proof.
    intros L1 L2 H1 H2 f Hin p' Hp'.
    destruct (oplusFiles_subfile_in_source_or_dest L1 L2 f p' Hin Hp')
      as [[f_src [Hin_src Hp_src]] | [f_dst [Hin_dst Hp_dst]]].
    - destruct (H1 f_src Hin_src p' Hp_src) as [g [Hpath_g Hin_g]].
      destruct (oplusFiles_source_path_in g L1 L2 Hin_g) as [g' [Hpath_g' Hin_g']].
      exists g'. split.
      + rewrite Hpath_g'. exact Hpath_g.
      + exact Hin_g'.
    - destruct (H2 f_dst Hin_dst p' Hp_dst) as [g [Hpath_g Hin_g]].
      apply (oplusFiles_dest_path_preserved p' L1 L2).
      exists g. split. exact Hpath_g. exact Hin_g.
  Qed.

  (* file_view es reflexiva: todo archivo es vista parcial de si mismo *)
  Lemma file_view_refl : forall (f : File), file_view f f.
  Proof.
    intro f. unfold file_view.
    split; [reflexivity | split; [reflexivity | split; auto]].
  Qed.

  (* addFile sobre dest preserva subset_files hacia L3,
     siempre que f_src tenga un testigo en L3 y L3 tenga paths unicos *)
  Lemma addFile_subset_files : forall (f_src : File) (dest L3 : list File),
    unique_paths_to_file L3 ->
    (In f_src L3 \/ (exists h : File, In h L3 /\ file_view f_src h)) ->
    subset_files dest L3 ->
    subset_files (addFile f_src dest) L3.
  Proof.
    intros f_src dest. revert f_src.
    induction dest as [| f_head rest IH]; intros f_src L3 Huniq Hview_src Hsubset_dest.
    - (* dest = [] *)
      unfold subset_files. intros f Hin.
      simpl in Hin. destruct Hin as [Heq | []].
      rewrite <- Heq. exact Hview_src.
    - (* dest = f_head :: rest *)
      unfold subset_files. intros f_result Hin.
      simpl in Hin.
      destruct (path_eq (file_path f_src) (file_path f_head)) as [Hpath | Hpath];
      simpl in Hin; destruct Hin as [Heq | Hin_rest].
      + (* Mismo path, f_result = archivo fusionado *)
        (* Obtener testigo para f_src *)
        assert (Hview_src_ex : exists h, In h L3 /\ file_view f_src h).
        { destruct Hview_src as [Hin_src | Hex].
          - exists f_src. split. exact Hin_src. apply file_view_refl.
          - exact Hex. }
        (* Obtener testigo para f_head *)
        assert (Hview_head_ex : exists h, In h L3 /\ file_view f_head h).
        { destruct (Hsubset_dest f_head (or_introl eq_refl)) as [Hin_head | Hex].
          - exists f_head. split. exact Hin_head. apply file_view_refl.
          - exact Hex. }
        destruct Hview_src_ex as [h_src [Hh_src_in Hh_src_view]].
        destruct Hview_head_ex as [h_head [Hh_head_in Hh_head_view]].
        (* Por unique_paths_to_file: h_src = h_head *)
        assert (Heq_h : h_src = h_head).
        { apply (Huniq h_src h_head Hh_src_in Hh_head_in).
          destruct Hh_src_view as [Hp_s _].
          destruct Hh_head_view as [Hp_h _].
          congruence. }
        subst h_head.
        (* file_view del archivo fusionado hacia h_src *)
        right. exists h_src. split.
        * exact Hh_src_in.
        * rewrite <- Heq. unfold file_view. simpl.
          destruct Hh_src_view as [Hp_s [Ho_s [Hpsub_s Huser_s]]].
          destruct Hh_head_view as [_ [_ [Hpsub_h Huser_h]]].
          split; [exact Hp_s | split; [exact Ho_s | split]].
          -- intros p' Hp'. apply mergePaths_membership in Hp'.
             destruct Hp'; [apply Hpsub_s | apply Hpsub_h]; assumption.
          -- intros u Hu. apply mergeUsers_membership in Hu.
             destruct Hu; [apply Huser_s | apply Huser_h]; assumption.
      + (* Mismo path, f_result en rest *)
        apply Hsubset_dest. right. exact Hin_rest.
      + (* Distinto path, f_result = f_head *)
        apply Hsubset_dest. left. exact Heq.
      + (* Distinto path, f_result en addFile f_src rest *)
        assert (Hsubset_rest : subset_files rest L3).
        { unfold subset_files. intros f Hf. apply Hsubset_dest. right. exact Hf. }
        exact (IH f_src L3 Huniq Hview_src Hsubset_rest f_result Hin_rest).
  Qed.

  (* Si L1 y L2 son ambas subset_files de L3 (con paths unicos), entonces oplusFiles L1 L2 tambien lo es *)
  Lemma oplusFiles_subset_files : forall (L1 L2 L3 : list File),
    unique_paths_to_file L3 ->
    subset_files L1 L3 ->
    subset_files L2 L3 ->
    subset_files (oplusFiles L1 L2) L3.
  Proof.
    intros L1. induction L1 as [| f L1' IH]; intros L2 L3 Huniq H1 H2.
    - simpl. exact H2.
    - simpl. apply IH.
      + exact Huniq.
      + unfold subset_files in *. intros f' Hf'. apply H1. right. exact Hf'.
      + apply addFile_subset_files.
        * exact Huniq.
        * apply H1. left. reflexivity.
        * exact H2.
  Qed.

  (* addFile preserva la propiedad files_without_cycles:
     si f no se contiene a si mismo y dest es acíclico, entonces addFile f dest tambien lo es *)
  Lemma addFile_preserves_files_without_cycles : forall (f : File) (dest : list File),
    ~ In (file_path f) (file_subfiles f) ->
    files_without_cycles dest ->
    files_without_cycles (addFile f dest).
  Proof.
    unfold files_without_cycles.
    intros f dest Hf.
    induction dest as [| f' dest' IH]; intros Hdest g Hin.
    - simpl in Hin. destruct Hin as [Heq | []].
      rewrite <- Heq. simpl. exact Hf.
    - simpl in Hin.
      destruct (path_eq (file_path f) (file_path f')) as [Heq_path | Hneq_path];
      simpl in Hin; destruct Hin as [Heq | Hin].
      + rewrite <- Heq. simpl.
        intro Habs. apply mergePaths_membership in Habs.
        destruct Habs as [Hs | Hd].
        * exact (Hf Hs).
        * apply (Hdest f' (or_introl eq_refl)). rewrite <- Heq_path. exact Hd.
      + apply Hdest. right. exact Hin.
      + rewrite <- Heq. apply Hdest. left. reflexivity.
      + apply IH.
        * intros g' Hg'. apply Hdest. right. exact Hg'.
        * exact Hin.
  Qed.

  (* oplusFiles preserva la propiedad files_without_cycles en ambas listas *)
  Lemma oplusFiles_preserves_files_without_cycles : forall (source dest : list File),
    files_without_cycles source ->
    files_without_cycles dest ->
    files_without_cycles (oplusFiles source dest).
  Proof.
    intros source.
    induction source as [| f source' IH]; intros dest Hsource Hdest.
    - simpl. exact Hdest.
    - simpl. apply IH.
      + unfold files_without_cycles in *. intros g Hg. apply Hsource. right. exact Hg.
      + apply addFile_preserves_files_without_cycles.
        * apply Hsource. left. reflexivity.
        * exact Hdest.
  Qed.

  (* Si g pertenece a addFile f dest y su path difiere del de f, entonces g ya estaba en dest *)
  Lemma addFile_In_dest : forall (f g : File) (dest : list File),
    In g (addFile f dest) -> file_path g <> file_path f -> In g dest.
  Proof.
    intros f g dest.
    induction dest as [| f' dest' IH]; intros Hin Hneq.
    - simpl in Hin. destruct Hin as [Heq | []].
      subst g. exfalso. apply Hneq. simpl. reflexivity.
    - simpl in Hin.
      destruct (path_eq (file_path f) (file_path f')) as [Heq_path | Hneq_path];
      simpl in Hin; destruct Hin as [Heq | Hin].
      + subst g. exfalso. apply Hneq. simpl. reflexivity.
      + right. exact Hin.
      + left. exact Heq.
      + right. apply IH. exact Hin. exact Hneq.
  Qed.

  (* NoDup sobre map file_path implica unique_paths_to_file:
     si no hay paths duplicados, entonces no hay dos archivos distintos con el mismo path *)
  Lemma NoDup_map_file_path_unique_paths : forall (dest : list File),
    NoDup (map file_path dest) -> unique_paths_to_file dest.
  Proof.
    intros dest.
    induction dest as [| f' dest' IH]; intros Hnodup.
    - unfold unique_paths_to_file. intros a b Ha. simpl in Ha. contradiction.
    - simpl in Hnodup. inversion Hnodup as [| ? ? Hnotin Hnodup']. subst.
      unfold unique_paths_to_file.
      intros a b Ha Hb Hpath.
      destruct Ha as [Ha_eq | Ha_in]; destruct Hb as [Hb_eq | Hb_in].
      + rewrite <- Ha_eq, <- Hb_eq. reflexivity.
      + exfalso. apply Hnotin. subst a. rewrite Hpath. apply in_map. exact Hb_in.
      + exfalso. apply Hnotin. subst b. rewrite <- Hpath. apply in_map. exact Ha_in.
      + apply (IH Hnodup' a b Ha_in Hb_in Hpath).
  Qed.

  (* addFile preserva NoDup sobre map file_path:
     si dest no tiene paths duplicados, tampoco los tiene addFile f dest *)
  Lemma addFile_preserves_NoDup_map_file_path : forall (f : File) (dest : list File),
    NoDup (map file_path dest) -> NoDup (map file_path (addFile f dest)).
  Proof.
    intros f dest.
    induction dest as [| f' dest' IH]; intros Hnodup.
    - simpl. constructor.
      + simpl. auto.
      + constructor.
    - simpl.
      destruct (path_eq (file_path f) (file_path f')) as [Heq_path | Hneq_path]; simpl.
      + (* Match: merged :: dest' *)
        simpl in Hnodup. rewrite Heq_path. exact Hnodup.
      + (* No match: f' :: addFile f dest' *)
        simpl in Hnodup. inversion Hnodup as [| ? ? Hnotin Hnodup']. subst.
        constructor.
        * intro Habs.
          apply in_map_iff in Habs.
          destruct Habs as [g [Hpath_g Hin_g]].
          assert (Hneq_g : file_path g <> file_path f).
          { intro Heq. apply Hneq_path. rewrite <- Heq. exact Hpath_g. }
          apply addFile_In_dest in Hin_g; [|exact Hneq_g].
          apply Hnotin. rewrite <- Hpath_g. apply in_map. exact Hin_g.
        * apply IH. exact Hnodup'.
  Qed.

  (* oplusFiles preserva NoDup sobre map file_path *)
  Lemma oplusFiles_preserves_NoDup_map_file_path : forall (source dest : list File),
    NoDup (map file_path dest) -> NoDup (map file_path (oplusFiles source dest)).
  Proof.
    intros source. induction source as [| f source' IH]; intros dest H.
    - simpl. exact H.
    - simpl. apply IH. apply addFile_preserves_NoDup_map_file_path. exact H.
  Qed.


  (* ===== Lemas sobre lookupFile y getFiles ===== *)

  (* El archivo devuelto por lookupFile tiene al usuario u en su lista de acceso *)
  Lemma lookupFile_user_access : forall (files : list File) (p : path) (u : idUser) (f : File),
    lookupFile files p u = Some f -> In u (file_user_access f).
  Proof.
    intros files p u. induction files as [| f0 files' IH]; intros f H; simpl in H.
    - discriminate.
    - destruct (path_eq p (file_path f0)) as [Heq_p | Hneq_p];
      destruct (in_dec idUser_eq u (file_user_access f0)) as [Hin_u | Hnin_u];
      simpl in H; try (apply IH; exact H).
      injection H as Heq. rewrite <- Heq. exact Hin_u.
  Qed.

  (* El archivo devuelto por lookupFile tiene exactamente el path buscado *)
  Lemma lookupFile_path : forall (files : list File) (p : path) (u : idUser) (f : File),
    lookupFile files p u = Some f -> file_path f = p.
  Proof.
    intros files p u. induction files as [| f0 files' IH]; intros f H; simpl in H.
    - discriminate.
    - destruct (path_eq p (file_path f0)) as [Heq_p | Hneq_p];
      destruct (in_dec idUser_eq u (file_user_access f0)) as [Hin_u | Hnin_u];
      simpl in H; try (apply IH; exact H).
      injection H as Heq. rewrite <- Heq. symmetry. exact Heq_p.
  Qed.

  (* El archivo devuelto por lookupFile pertenece a la lista original *)
  Lemma lookupFile_in : forall (files : list File) (p : path) (u : idUser) (f : File),
    lookupFile files p u = Some f -> In f files.
  Proof.
    intros files p u. induction files as [| f0 files' IH]; intros f H; simpl in H.
    - discriminate.
    - destruct (path_eq p (file_path f0)) as [Heq_p | Hneq_p];
      destruct (in_dec idUser_eq u (file_user_access f0)) as [Hin_u | Hnin_u];
      simpl in H; try (right; apply IH; exact H).
      injection H as Heq. left. exact Heq.
  Qed.

  (* Todo archivo en getFiles files p u tiene al usuario u en su lista de acceso *)
  Lemma getFiles_user_access : forall (files : list File) (p : path) (u : idUser) (f : File),
    In f (getFiles files p u) -> In u (file_user_access f).
  Proof.
    intros files p u f H. unfold getFiles in H.
    destruct (lookupFile files p u) as [root|] eqn:Hlookup.
    - simpl in H. destruct H as [Heq | Hin_subs].
      + rewrite <- Heq. simpl.
        apply (lookupFile_user_access files p u). exact Hlookup.
      + apply in_flat_map in Hin_subs.
        destruct Hin_subs as [p' [_ Hin_f]].
        destruct (lookupFile files p' u) as [g|] eqn:Hlookup'.
        * simpl in Hin_f. destruct Hin_f as [Heq_g | []].
          rewrite <- Heq_g. simpl.
          apply (lookupFile_user_access files p' u). exact Hlookup'.
        * simpl in Hin_f. contradiction.
    - simpl in H. contradiction.
  Qed.

  (* getFiles devuelve una lista cerrada bajo subarchivos accesibles por u:
     si f esta en el resultado y p' es subarchivo de f, existe algun g en el resultado con path p' *)
  Lemma getFiles_subfiles_closed :
    forall (files : list File) (p : path) (u : idUser) (f : File) (p' : path),
      In f (getFiles files p u) ->
      In p' (file_subfiles f) ->
      exists g, file_path g = p' /\ In g (getFiles files p u).
  Proof.
    intros files p u f p' Hin_f Hin_p'.
    unfold getFiles in *.
    destruct (lookupFile files p u) as [root|] eqn:Hlookup.
    - simpl in Hin_f. destruct Hin_f as [Heq_f | Hin_subs].
      + (* f es la raiz modificada: file_subfiles f = acc_sub_paths *)
        rewrite <- Heq_f in Hin_p'. simpl in Hin_p'.
        apply filter_In in Hin_p'.
        destruct Hin_p' as [Hin_p'_root Hlookup_p'].
        destruct (lookupFile files p' u) as [g|] eqn:Hlookup'.
        * exists (file (file_path g) nil (file_user_access g) (file_objective g)).
          split.
          -- simpl. apply (lookupFile_path files p' u g). exact Hlookup'.
          -- right. apply in_flat_map.
             exists p'. split.
             ++ exact Hin_p'_root.
             ++ rewrite Hlookup'. left. reflexivity.
        * simpl in Hlookup_p'. discriminate.
      + (* f es un subarchivo directo: file_subfiles f = [] *)
        apply in_flat_map in Hin_subs.
        destruct Hin_subs as [p'' [_ Hin_f']].
        destruct (lookupFile files p'' u) as [g|] eqn:Hlookup''.
        * simpl in Hin_f'. destruct Hin_f' as [Heq_g | []].
          rewrite <- Heq_g in Hin_p'. simpl in Hin_p'. contradiction.
        * simpl in Hin_f'. contradiction.
    - simpl in Hin_f. contradiction.
  Qed.

  (* Cada archivo devuelto por getFiles es una vista parcial de algun archivo en la lista original *)
  Lemma getFiles_subset_files_mac : forall (files : list File) (p : path) (u : idUser),
    subset_files (getFiles files p u) files.
  Proof.
    intros files p u. unfold subset_files. intros f Hin_f.
    unfold getFiles in Hin_f.
    destruct (lookupFile files p u) as [root|] eqn:Hlookup.
    - simpl in Hin_f. destruct Hin_f as [Heq_f | Hin_subs].
      + (* f es la raiz modificada: file_subfiles reducido a subarchivos accesibles *)
        right. exists root. split.
        * exact (lookupFile_in files p u root Hlookup).
        * rewrite <- Heq_f. unfold file_view. simpl.
          split; [reflexivity | split; [reflexivity | split]].
          -- intros p' Hin_p'. apply filter_In in Hin_p'. exact (proj1 Hin_p').
          -- intros u' Hu'. exact Hu'.
      + (* f es un subarchivo directo: file_subfiles = [] *)
        apply in_flat_map in Hin_subs.
        destruct Hin_subs as [p' [_ Hin_f']].
        destruct (lookupFile files p' u) as [g|] eqn:Hlookup'.
        * simpl in Hin_f'. destruct Hin_f' as [Heq_g | []].
          right. exists g. split.
          -- exact (lookupFile_in files p' u g Hlookup').
          -- rewrite <- Heq_g. unfold file_view. simpl.
             split; [reflexivity | split; [reflexivity | split]].
             ++ intros p'' Hp''. contradiction.
             ++ intros u' Hu'. exact Hu'.
        * simpl in Hin_f'. contradiction.
    - simpl in Hin_f. contradiction.
  Qed.

  (* getFiles preserva la propiedad files_without_cycles:
     si la lista original es aciclica, la vista filtrada tambien lo es *)
  Lemma getFiles_preserves_files_without_cycles : forall (files : list File) (p : path) (u : idUser),
    files_without_cycles files ->
    files_without_cycles (getFiles files p u).
  Proof.
    intros files p u Hfwc.
    unfold files_without_cycles. intros f Hf.
    unfold getFiles in Hf.
    destruct (lookupFile files p u) as [root|] eqn:Hlookup.
    - simpl in Hf. destruct Hf as [Hf_eq | Hf_in].
      + rewrite <- Hf_eq. simpl.
        intro Habs. apply filter_In in Habs. destruct Habs as [Hin_sub _].
        exact (Hfwc root (lookupFile_in _ _ _ _ Hlookup) Hin_sub).
      + apply in_flat_map in Hf_in.
        destruct Hf_in as [p' [_ Hf_in']].
        destruct (lookupFile files p' u) as [g|] eqn:Hlookup'.
        * simpl in Hf_in'. destruct Hf_in' as [Heq | []].
          rewrite <- Heq. simpl. auto.
        * simpl in Hf_in'. contradiction.
    - simpl in Hf. contradiction.
  Qed.