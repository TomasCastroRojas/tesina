Require Import Coq.Lists.List.
Require Import Coq.Logic.Classical_Prop.

Require Import Machine.Machine.
Require Import Machine.MachineAuxFunctions.
Require Import Attacker.Attacker.


(* add_machine_user se 'comporta' como cons *)
  Lemma add_element_preserves_list : forall (a b: (idMachine * idUser)) (l: list (idMachine * idUser)),
    In a l -> In a (add_machine_user b l).
  Proof.
    intros a b l H.
    induction l.
    - simpl. auto.
    - destruct a as [m u].
      destruct b as [m' u'].
      destruct a0 as [m0 u0].
      simpl in |- *.
      case (idMachine_eq m' m0).
      -- case (idUser_eq u' u0).
         --- intro eq_u.
             intro eq_m.
             exact H.
         --- simpl in |- *.
             intros neq_u' eq_m'.
             simpl in H.
             elim H.
             ---- intro eq_a0_a.
                  left.
                  exact eq_a0_a.
             ---- intro HIn.
                  right.
                  apply IHl.
                  exact HIn.
     -- intro eq_m'.
        simpl.
        elim H.
        --- intro eq_m.
            left.
            exact eq_m.
        --- intro HIn.
            right.
            apply IHl.
            exact HIn.
  Qed.
  
  Lemma disjuction_commutative : forall (A B C: Prop), (A \/ B \/ C) <-> (B \/ A \/ C).
  Proof.
    intros.
    split; intro H; elim H; intro H'.
    - right. left. exact H'.
    - elim H'; intro H''.
      -- left. exact H''.
      -- right. right. exact H''.
    - right. left. exact H'.
    - elim H'; intro H''.
      -- left. exact H''.
      -- right. right. exact H''.
  Qed.

  Lemma and_cortocircuito : forall (A B: Prop), A \/ (B /\ False) <-> A \/ False.
  Proof.
    intros.
    split.
    - intro H.
      elim H.
      -- intro H1. left. exact H1.
      -- intro H1. elim H1. intros H2 H3. right. exact H3.
    - intro H.
      elim H.
      -- intro H1. left. exact H1.
      -- intro H1. contradiction.
  Qed.

  Lemma member_add_machine_user : forall (m m': idMachine) (u u':idUser) (l: list (idMachine * idUser)),
    In (m,u) (add_machine_user (m', u') l) <-> ((m', u') = (m, u) \/ In (m, u) l).
  Proof.
    induction l.
    - simpl. reflexivity.
    - destruct a as [m0 u0].
      simpl.
      case (idMachine_eq m' m0).
      -- case (idUser_eq u' u0); intros Heq_u Heq_m; simpl; split; intro H; elim H; intro H'.
         --- left. rewrite Heq_u. rewrite Heq_m. exact H'.
         --- right. right. exact H'.
         --- left. rewrite <- Heq_u. rewrite <- Heq_m. exact H'.
         --- exact H'.
         --- right. left. exact H'.
         --- apply disjuction_commutative. right. apply IHl. exact H'.
         --- right. apply IHl. left. exact H'.
         --- elim H'; intros H''.
             ---- left. exact H''.
             ---- right. apply IHl. right. exact H''.
     -- intro neq_m.
        simpl.
        split; intro H; [  | apply disjuction_commutative in H]; elim H; intro H'.
        --- right. left. exact H'.
        --- apply disjuction_commutative. right. apply IHl. exact H'.
        --- left. exact H'.
        --- right. apply IHl. exact H'.
  Qed.

  Lemma member_addAccount : forall (a: Account) (l: list Account),
      In a (addAccount a l) <-> True.
  Proof.
    intros.
    induction l; simpl; split.
    - auto.
    - auto.
    - destruct a as [u s k p].
      destruct a0 as [u0 s0 k0 p0].
      simpl.
      case (idUser_eq u u0); case (idService_eq s s0); intros; auto.
    - intro.
      destruct a as [u s k p].
      destruct a0 as [u0 s0 k0 p0].
      simpl.
      case (idUser_eq u u0); intro.
      -- case (idService_eq s s0); intros.
         --- simpl.
             left.
             reflexivity.
         --- simpl.
             right.
             apply IHl. auto.
      -- simpl.
         right.
         apply IHl. auto.
  Qed.

  Lemma member_addAccount_simpl : forall (a a': Account) (l: list Account),
      In a (addAccount a' l) -> a' = a \/ In a l.
  Proof.
    intros a a'.
  induction l as [| acc' accs IH].

  - simpl.
    intros [H | []].
    left.  exact H.

  - destruct a'   as [u' s' k' p'].
    destruct acc' as [u0 s0 k0 p0].
    simpl.
    destruct (idUser_eq u' u0) as [Heq_u | Hneq_u];
    destruct (idService_eq s' s0) as [Heq_s | Hneq_s]; simpl.

    + intros [H | H].
      * left. exact H.
      * right. right. exact H. 

    + intros [H | H].
      * right. left. exact H.
      * apply IH in H.
        destruct H as [H | H].
        -- left. exact H.
        -- right. right. exact H.

    + intros [H | H].
      * right. left. exact H.
      * apply IH in H.
        destruct H as [H | H].
        -- left. exact H.
        -- right. right. exact H.

    + intros [H | H].
      * right. left. exact H.
      * apply IH in H.
        destruct H as [H | H].
        -- left. exact H.
        -- right. right. exact H.
  Qed.

  Lemma addAccount_preserves_membership_when_neq : forall (a a': Account) (l: list Account),
    (account_user a <> account_user a') -> In a l -> In a (addAccount a' l).
  Proof.
    intros a a'.
    induction l as [| acc accs IH].
    - intros. simpl. auto.
    - intros Hneq Hin.
      simpl in *.
      destruct (idUser_eq (account_user a') (account_user acc)) as [ Heq_u | Hneq_u];
      destruct (idService_eq (account_service a') (account_service acc)) as [ Heq_s | Hneq_s];
      simpl; destruct Hin as [ Heq | Hin'].
      -- exfalso. apply Hneq. rewrite <- Heq. symmetry. exact Heq_u.
      -- right. exact Hin'.
      -- left. exact Heq.
      -- right. apply IH; assumption.
      -- left. exact Heq.
      -- right. apply IH; assumption.
      -- left. exact Heq.
      -- right. apply IH; assumption.
  Qed.

  Lemma enviroment_eq : forall (env env': network_map) (m m': idMachine) (mac: Machine),
    m <> m' -> env' = modify_machine m' mac env -> env' m = env m.
  Proof.
    intros.
    rewrite H0.
    unfold modify_machine.
    case (idMachine_eq m m').
    - intro. contradiction.
    - intro. reflexivity.
  Qed.

  Lemma option_eq : forall (A: Type) (a a': A), Some a = Some a' -> a = a'.
  Proof.
    intros.
    congruence.
  Qed.
  
  Lemma enviroment_map_image : forall (env: network_map) (m: idMachine) (mac1 mac2: Machine),
    env m = Some mac1 -> env m = Some mac2 -> mac1 = mac2.
  Proof.
    intros.
    apply (option_eq Machine).
    rewrite H in H0.
    exact H0.
  Qed.

  Lemma enviroment_simpl : forall (env env': network_map) (m m': idMachine) (m0 mac: Machine),
    m = m' -> env' = (modify_machine m' mac env) -> env' m = Some m0 -> m0 = mac.
  Proof.
    intros.
    assert (env' m = Some mac).
    rewrite H0.
    unfold modify_machine.
    case (idMachine_eq m m'); intro eq_m.
    - reflexivity.
    - contradiction.
    - rewrite H1 in H2.
    apply option_eq.
    exact H2.
  Qed.


  Lemma addService_preserves_membership : forall (a b: Service) (l: list Service),
    In a l -> In a (addService b l).
  Proof.
    intros.
    induction l; simpl.
    - auto.
    - case (idService_eq (service_value b) (service_value a0)); intros eq_serv.
      -- exact H.
      -- simpl in *.
         elim H; intro H'.
         --- left. exact H'.
         --- right. apply IHl. exact H'.
  Qed.

  
  Lemma oplusServices_preserves_membership : forall (s: Service) (l1 l2: list Service),
    In s l1 -> In s (oplusServices l1 l2).
  Proof.
    intros s l1 l2.
    revert l1.
    induction l2 as [| a l2' IH].
    - auto.
    - intros l H.
      simpl.
      apply IH.
      apply addService_preserves_membership.
      exact H.
  Qed.

  Lemma or_assoc : forall A B C : Prop, (A \/ (B \/ C)) <-> ((A \/ B) \/ C).
  Proof.
    intros.
    split; intro H.
    - destruct H as [ H | H].
      -- left. left. exact H.
      -- destruct H as [ H | H ].
         --- left. right. exact H.
         --- right. exact H.
    - destruct H as [ H | H].
      -- destruct H as [ H | H ].
         --- left. exact H.
         --- right. left. exact H.
      -- right. right. exact H.
  Qed.
  
  Lemma addService_membership : forall (s s': Service) (l: list Service),
    In s (addService s' l) -> s' = s \/ In s l.
  Proof.
    intros s s' l.
    induction l as [| s0 l' IH]; simpl.
    - auto.
    - case (idService_eq (service_value s') (service_value s0)); intros eq_s0 H; simpl in *.
      -- right. exact H.
      -- apply disjuction_commutative.
         destruct H as [ Heq | Hin].
         --- left. exact Heq.
         --- right. apply IH. exact Hin.
  Qed.

Lemma oplusServices_membership : forall (s: Service) (l1 l2: list Service),
    In s (oplusServices l1 l2) -> In s l1 \/ In s l2.
  Proof.
    intros s l1 l2.
    revert l1.
    induction l2 as [| s' l2' IH]; intros l1 H.
    - auto.
    - apply IH in H.
      simpl.
      apply disjuction_commutative.
      apply or_assoc.
      destruct H as [ Hin_add | Hin_l2 ].
      -- left. apply addService_membership. exact Hin_add.
      -- right. exact Hin_l2.
  Qed.

  Lemma addNeighbour_membership : forall (n1 n2: idMachine) (l: list idMachine),
    In n1 (addNeighbour n2 l) -> n1 = n2 \/ In n1 l.
  Proof.
    intros n1 n2 l.
    induction l as [| n0 l' IH]; simpl.
    - intros [H | []]. left. symmetry. exact H.
    - case (idMachine_eq n2 n0); intros eq_n0 H; simpl in H.
      -- right. exact H.
      -- destruct H as [ Heq | Hin].
         --- right. left. exact Heq.
         --- destruct (IH Hin) as [ Heq | Hin'].
             ---- left. exact Heq.
             ---- right. right. exact Hin'.
  Qed.
  
  Lemma oplusNeighbours_membership : forall (m: idMachine) (l1 l2: list idMachine),
    In m (oplusNeighbours l1 l2) -> In m l1 \/ In m l2.
  Proof.
    intros m l1.
    induction l1 as [| m' l1' IH]; simpl in *; intros l2 H.
    - right. exact H.
    - apply IH in H.
      destruct H as [Hin | Hin_add].
      -- left. right. exact Hin.
      -- apply addNeighbour_membership in Hin_add.
         destruct Hin_add as [ Heq | Hin'].
         --- left. left. symmetry. exact Heq.
         --- right. exact Hin'.
  Qed.
  
      
(* Membership in addSecret: el resultado contiene (m,p) o un elemento de s *)
Lemma addSecret_membership : forall (m m0: idMachine) (p p0: path)
                                    (s: list (idMachine * path)),
  In (m0, p0) (addSecret m p s) -> (m0, p0) = (m, p) \/ In (m0, p0) s.
Proof.
  intros m m0 p p0 s.
  induction s as [| [m' p'] s' IH].
  - simpl. intros [H | []]. left. symmetry. exact H.
  - simpl.
    case (idMachine_eq m m'); intro eq_m.
    + case (path_eq p p'); intro eq_p.
      * (* left, left: addSecret devuelve (m',p')::s' sin cambios *)
        intros H. right. exact H.
      * (* left, right: (m',p') :: addSecret m p s' *)
        simpl. intros [H | H].
        -- right. left. exact H.
        -- apply IH in H. destruct H as [H | H].
           ++ left. exact H.
           ++ right. right. exact H.
    + (* right, _: (m',p') :: addSecret m p s' *)
      simpl. intros [H | H].
      * right. left. exact H.
      * apply IH in H. destruct H as [H | H].
        -- left. exact H.
        -- right. right. exact H.
Qed.

(* Membership in oplusSecrets: el resultado proviene de s1 o de s2 *)
Lemma oplusSecrets_membership : forall (m0: idMachine) (p0: path)
                                       (s1 s2: list (idMachine * path)),
  In (m0, p0) (oplusSecrets s1 s2) -> In (m0, p0) s1 \/ In (m0, p0) s2.
Proof.
  intros m0 p0 s1 s2.
  revert s1.
  induction s2 as [| [m p] s2' IH]; intros s1 H.
  - left. exact H.
  - simpl in H.
    apply IH in H.
    destruct H as [H | H].
    + apply addSecret_membership in H.
      destruct H as [H | H].
      * right. left. rewrite <- H. reflexivity.
      * left. exact H.
    + right. right. exact H.
Qed.

(* Membership in getPaths_objectives: m0 = m y existe el archivo en la lista *)
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

(* addFile siempre incluye en el resultado un archivo con el mismo path que f.
   Nota: en la rama `right` de addFile, la definicion actual dice
         `addFile f files'` en lugar de `cons f' (addFile f files')`.
   Eso no afecta este lema porque la rama `right` recursa y eventualmente
   llega a nil donde agrega f. *)
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

(* addFile preserva todos los elementos de dest: si un path estaba registrado
   en dest, sigue estando en addFile f_add dest *)
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

Lemma oplusFiles_user_in_source_or_dest :
  forall (source dest : list File) (f : File) (u0 : idUser),
    In f (oplusFiles source dest) ->
    In u0 (file_user_access f) ->
    (exists f_src, In f_src source /\ In u0 (file_user_access f_src)) \/
    (exists f_dst, In f_dst dest   /\ In u0 (file_user_access f_dst)).
Proof.
  intros source. induction source as [| f_src source' IH]; intros dest f u0 Hin Hu0.
  - simpl in Hin. right. exists f. split. exact Hin. exact Hu0.
  - simpl in Hin.
    destruct (IH (addFile f_src dest) f u0 Hin Hu0)
      as [[f_src' [Hin_src' Hu_src']] | [f_add [Hin_add Hu_add]]].
    + left. exists f_src'. split. right. exact Hin_src'. exact Hu_src'.
    + destruct (addFile_user_in_source_or_dest f_src f_add dest u0 Hin_add Hu_add)
        as [Hu_fsrc | [f_dst [Hin_dst Hu_dst]]].
      * left. exists f_src. split. left. reflexivity. exact Hu_fsrc.
      * right. exists f_dst. split. exact Hin_dst. exact Hu_dst.
Qed.

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

(* Todo archivo devuelto por lookupFile tiene a u en su lista de acceso *)
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

(* Todo archivo devuelto por getFiles_collect tiene a u en su lista de acceso *)
Lemma getFiles_collect_user_access :
  forall (files filesStatic : list File) (paths : list path) (u : idUser) (f : File),
    In f (getFiles_collect files filesStatic paths u) -> In u (file_user_access f).
Proof.
  intros files. induction files as [| f0 files' IH];
  intros filesStatic paths u f Hin; simpl in Hin.
  - contradiction.
  - destruct paths as [| p paths'].
    + contradiction.
    + destruct (lookupFile filesStatic p u) as [fLooked|] eqn:Hlookup.
      * simpl in Hin. destruct Hin as [Heq | Hin_rest].
        -- rewrite <- Heq.
           apply (lookupFile_user_access filesStatic p u).
           exact Hlookup.
        -- apply (IH filesStatic (file_subfiles fLooked ++ paths') u f). exact Hin_rest.
      * apply (IH filesStatic paths' u f). exact Hin.
Qed.

(* Todo archivo en filesMac = getFiles fs p u tiene a u en su lista de acceso *)
Lemma getFiles_user_access : forall (files : list File) (p : path) (u : idUser) (f : File),
  In f (getFiles files p u) -> In u (file_user_access f).
Proof.
  intros files p u f H. unfold getFiles in H.
  apply (getFiles_collect_user_access files files (p :: nil) u).
  exact H.
Qed.

(* addUser u l siempre contiene u *)
Lemma addUser_self : forall (u : idUser) (l : list idUser),
  In u (addUser u l).
Proof.
  intros u l. induction l as [| v vs IH]; simpl.
  - left. reflexivity.
  - destruct (idUser_eq u v) as [Heq | Hneq].
    + rewrite Heq. left. reflexivity.
    + simpl. right. exact IH.
Qed.

(* addUser preserva los miembros existentes *)
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

(* Si u esta en file_user_access f_src, algun archivo del resultado de addFile
   tiene a u en su user_access; o bien f_res ya estaba en dest *)
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

(* Para todo f en oplusFiles source dest:
   o bien u esta en file_user_access f (si source lo introduce),
   o bien f proviene de dest sin modificacion *)
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