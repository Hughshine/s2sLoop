Add LoadPath "~/formal/s2sLoop/from_compcert".
Add LoadPath "~/formal/PilkiLib".
Add LoadPath "~/formal/s2sLoop/src".
Require Import Libs.
Require Import Errors.
Require Import Polyhedra.
Require Import Loops.
Require Import Memory.
Require Import ArithClasses.
Require Import Permutation.
Require Import Sorted.
Require Import Instructions.
Require Import Bounds.
Require Import BoxedPolyhedra.
Require Import Psatz. (** 提供一些tactics *)
Require Import PolyBase.
Require Import PLang.
Require Import TimeStamp.
Require Import ExtractPoly.
Require Import Do_notation.
Open Scope string_scope.
(*Set Implicit Arguments.*)
Open Scope Z_scope.




Module Tilling (Import M:BASEMEM(ZNum))
  (I:INSTRS(ZNum) with Definition Value := M.Value).
  Module EP := Extract(M)(I).
  Import EP.
  Import P. Import T.
  Module Mem := MEMORY(ZNum)(M).
  Import Mem.

  (* we now move to the potential tilling *)

   Open Scope Z_scope.
  Ltac spec_lia :=
    unfold satisfy_constraint in *; simpl in *; simpl_vect in *; simpl in *;
    unfold Inhab_num, Inhabited_Z, ZNum.Numerical_Num in *; lia.

   Lemma tilling_Z_lemma_1: forall a x i,
     -a * x + i >=0 ->
     a*x - i + (a - 1) >= 0 ->
     x = i / a.
    (** i+1 -a <= ax <= i 
    => i/a + 1/a - 1 <= x <= i/a (a > 0)
        (a是整数，1/a-1在[0, 1)之间)
    *)
   Proof.
     intros.
     assert (a >= 1) by lia.
     assert (a <> 0) by lia.
     apply (Zdiv_unique_full _ _ _ (i - a * x)); try lia.
     unfold Remainder.
     lia.
   Qed.

   Lemma tilling_Z_lemma_2: forall a x,
     -a * x  >=0 ->
     a*x  + (a - 1) >= 0 ->
     x = 0.
    (** 
      1-a <= ax <= 0
    (a=0) => 无解
    (a>0) => 1/a - 1 <= x <= 0
             1/a - 1 在 (-1, 0]，所以x=0
    (a<0) => 1-1/a >= x >= 0
             1 - 1/a 在 [0, 1)，所以x=0
    *)
   Proof.
     intros.
     assert (x = 0/a).
     apply tilling_Z_lemma_1; lia.
     compute in H1.
     assumption.
   Qed.

  (** 生成关于分块维度的约束（根据一个列表的分块信息，pos是这一层的tile size，nat是对应的层数（即某个旧维度））
      这一步会建立分块维度（IT）和旧维度（I）的关系（相关约束）：
       a * IT <= I < a * IT + a 
                   (<= a * IT + a - 1)
      【无关维度都是0】
      注意，这里是domain，维度和循环的层数无关
  *)
  Fixpoint mk_constraints_tile_dims
    {depth nbr_global_parameters nbr_tiles: nat}
    (num_tile : nat)
    (tc: list (positive * nat))
      : Polyhedron ((depth + nbr_tiles) + nbr_global_parameters):=
    match tc with
    | [] => []
    | (a', n) :: tc' =>
      let a := Zpos a' in
        mkConstraint 
          (((Vnth_at_val depth n 1) +++ (Vnth_at_val nbr_tiles num_tile (-a)))
            +++ (V0 nbr_global_parameters))
          GE 0 ::
        mkConstraint
          (((Vnth_at_val depth n (- 1)) +++ (Vnth_at_val nbr_tiles num_tile (a)))
            +++ (V0 nbr_global_parameters))
          GE (1 - a) ::
        mk_constraints_tile_dims (S num_tile) tc'
    end.

  (** Inductive Z : Set :=  Z0 : Z | Zpos : positive -> Z | Zneg : positive -> Z *)
  (** 分块，就是对旧的约束的维度做扩增（但是仍为0），然后加入新的对分块维度的约束*)
   Definition mk_tilled_poly 
     {depth nbr_global_parameters} (tc: list (positive * nat))
     (pol: Polyhedron (depth + nbr_global_parameters)):
     Polyhedron ((depth + length tc) + nbr_global_parameters) :=
     let nbr_tiles := length tc in
     (mk_constraints_tile_dims 0 tc) ∩
     (map (fun c =>
       mkConstraint 
       (V_insert_middle0 c.(constr_vect)) c.(constr_comp)  c.(constr_val)) pol).

   Definition mk_tilled_vect {depth} (tc: list (positive * nat))
     (v: ZVector depth): ZVector (length tc) :=
     exist _ (map (fun p => (Vnth v (snd p)) / (Zpos (fst p))) tc) (map_length _ _).

   Lemma Vnth_mk_tilled_vect depth tc n a m tc' (v : ZVector depth):
     (a, m) :: tc' = list_drop n tc ->
     Vnth (mk_tilled_vect tc v) n = 
     (Vnth v m) / (Zpos a).
   Proof.
     unfold mk_tilled_vect, Vnth. dest_vects.
     simpl. clear Lv depth.
     revert tc a m tc' v.
     induction n as [|n]; intros.
     (* Case "O". *)
       simpl in *. subst.
       simpl. reflexivity.
     (* Case "S n". *)
       destruct tc; simpl in *; clean.
       eauto.
   Qed.
     
   Tactic Notation "Vsplit" constr(v) "as" ident(v1) ident(v2) :=
     let H := fresh in
     let v' := fresh v in
     rename v into v';
     pose proof (Vapp_take_drop _ _ v') as H;
     remember_no_eq (Vtake_p _ v') as v1;
     remember_no_eq (Vdrop_p _ v') as v2;
     rewrite <- H in *;
     clear H; clear v'.

   Program Definition mk_tilled_boxed_poly
     {depth nbr_global_parameters} (tc: list (positive * nat))
     (bpol: Boxed_Polyhedron nbr_global_parameters depth):
     Boxed_Polyhedron nbr_global_parameters (depth + length tc) :=
     {| bp_poly := mk_tilled_poly tc bpol.(bp_poly);
        bp_elts := (fun params =>
          map (fun v => v +++ (mk_tilled_vect tc v)) (bpol.(bp_elts) params))
     |}.
   Next Obligation.
     pose proof (bp_elts_NoDup _ _ bpol params).
     remember_no_eq (bp_elts bpol params) as vs.
     clear -H vs.
     induction vs as [|v vs].
     (* Case "nil". *)
       constructor.
     (* Case "cons v vs". *)
       inv H. constructor; auto.
       intro. apply H2.
       clear - H.
       induction vs as [|v' vs].
       (* SCase "nil". *)
         inv H.
       (* SCase "cons v' vs". *)
         destruct H; auto.
         (* SSCase "or_introl". *)
           left.
           match type of H with
             | ?V1 = ?V2 =>
               assert (Vtake_p depth V1 = Vtake_p depth V2) by congruence
           end.
           simpl_vect in H0. auto.
         (* SSCase "or_intror". *)
           right. apply IHvs. auto.
   Qed.
  Hint Rewrite Vnth_at_val_prod: vect.

   Next Obligation.
     rewrite in_map_iff in H.
     destruct H as [v [? IN]]. subst.
     apply bp_in_elts_in_poly in IN.
     unfold mk_tilled_poly.
     apply Pol_Included_intersertion.
     (* Case "In mk_constraints_tile_dims". *)
       clear.
       assert (forall tc' n,
         tc' = list_drop n tc ->
         (v +++ mk_tilled_vect tc v) +++ params ∈
         mk_constraints_tile_dims n tc') as GENERALIZED.
       (* SCase "Assert: GENERALIZED". *)
         intro. induction tc' as [| [a m] tc']; intros n DROP.
         (* SCase "Assert: GENERALIZED". *)
           simpl. constructor.
         (* SCase "Assert: GENERALIZED". *)
         Opaque Zminus Zplus Zmult.
           (* simpl. constructor;[|constructor];
           [ SSCase "satisfy_constraint1"|
             SSCase "satisfy_constraint2"|
             SSCase "tail"]. *)
           (* SSCase "satisfy_constraint1". *)
           simpl; constructor; [|constructor].
             red. simpl. simpl_vect.
             erewrite Vnth_mk_tilled_vect; eauto.
             replace (Zneg a) with (- Zpos a) by reflexivity.
             remember (Zpos a) as z.
             simpl. rewrite Zopp_mult_distr_l_reverse.
             assert (z > 0) by (subst; reflexivity).
             pose proof (Z_mult_div_ge (Vnth v m) z H).
             unfold ZNum.Numerical_Num in *.
             unfold Inhab_num in *. unfold Inhabited_Z in *. simpl in *. lia.
           (* SSCase "satisfy_constraint2". *)
             red; simpl. simpl_vect.
             erewrite Vnth_mk_tilled_vect; eauto.
             remember (Zpos a) as z.
             simpl.
             assert (z > 0) by (subst; reflexivity).
             pose proof (Z_mult_div_ge (Vnth v m) z H).
             unfold Inhab_num. simpl.
             unfold Inhabited_Z in *.
             match type of H0 with
               | _ * (?X / _) <= _ =>
                 remember_no_eq X as y
             end.
             replace (-1 * y) with (-y) by lia.
             pose proof (Z_div_mod_eq y z H). simpl.
             match goal with
               | |- ?X >= ?Y =>
                 replace X with (-(y mod z)) by lia
             end.
             pose proof (Z_mod_lt y z H). lia.
           (* SSCase "tail". *)
             apply IHtc'.
             remember_no_eq (a,m) as p.
             clear - DROP.
             revert p tc tc' DROP.
             induction n as [|n]; intros; auto.
             (* S3Case "O". *)
               simpl in *.
               subst. reflexivity.
             (* S3Case "S n". *)
               destruct tc; clean.
               simpl in DROP.
               rewrite (IHn _ _ _ DROP). simpl. reflexivity.
       (* End_of_assert GENERALIZED. *)
         apply GENERALIZED. reflexivity.
    (* Case "In map".     *)
      remember_no_eq (bp_poly bpol) as pol.
      induction pol as [|c pol]; constructor.
      (* SCase "cons c pol". *)
      inv IN.
      destruct c. unfold satisfy_constraint in *. simpl in *.
      simpl; simpl_vect.
      rewrite <- (Vapp_take_drop _ _ constr_vect) in *.
      rewrite V_insert_middle0_ok_l. rewrite Vprod_app in H1. apply H1.
      
      apply IHpol. inv IN; auto.
  Qed.
  Next Obligation.
    unfold mk_tilled_poly in H.
    pose proof H as H0.
    apply Pol_intersection_Included_l in H.
    apply Pol_intersection_Included_r in H0.
    pose proof H0 as H1.
    apply Pol_intersection_Included_l in H0.
    apply Pol_intersection_Included_r in H1.
    Vsplit vect as v12 v3.
    Vsplit v12 as v1 v2.

    simpl_vect.

    assert ((v1+++v3) ∈ constrain_params params (bp_poly bpol)) as IN.
    (* Case "Assert: IN". *)
      unfold constrain_params.
      apply Pol_Included_intersertion.
      apply poly_containing_params_drop_1 in H. simpl_vect in H.
      apply poly_containing_params_drop_2. simpl_vect. assumption.
      remember_no_eq (bp_poly bpol) as pol.
      clear - H1.
      induction pol as [|c pol]; constructor.
      (* SCase "constraint". *)
        inv H1. unfold satisfy_constraint in *. destruct c. simpl in *.
        Vsplit constr_vect as v1' v2'.
        rewrite V_insert_middle0_ok_l in H2.
        simpl_vect. simpl. apply H2.
      (* SCase "rest". *)
        inv H1. apply IHpol; auto.
    (* End_of_assert IN. *)
      apply bp_in_poly_in_elts in IN.
      simpl_vect in IN.
      clear H1 H.
      match goal with
        | |- In ?V (map ?F _) =>
          replace V with (F v1);
          apply (in_map F) in IN; auto
      end.
      clear IN.
      f_equal.
      apply Vnth_inj.
      intros n INF.
      assert (Vnth (mk_tilled_vect tc v1) n = Vnth v1 (snd (nth n tc (1%positive, 0%nat))) / Zpos (fst (nth n tc (1%positive, 0%nat))))
        as EQ.
      (* Case "Assert: EQ". *)
        clear - INF.
        unfold mk_tilled_vect.
        unfold Vnth at 1. simpl.
        revert n INF.
        induction tc as [|[p m] tc]; intros; simpl in *.
        (* SCase "nil". *)
          omegaContradiction.
        (* SCase "cons (p, m) tc". *)
          destruct n as [|n].
          simpl. reflexivity.
          apply IHtc. omega.
      (* End_of_assert EQ. *)
      rewrite EQ. clear EQ.

      assert (forall i, (v1 +++ v2) +++ v3 ∈ mk_constraints_tile_dims i (list_drop i tc)).
        induction i as [|i].
        (* SCase "O". *)
        simpl. auto.
        (* SCase "S i". *)
        replace (list_drop (S i) tc) with (tail (list_drop i tc)).
        remember_no_eq (list_drop i tc) as l.
        destruct l; simpl in *; auto. destruct p.
        inv IHi. inv H3. auto.
        clear.
        revert tc.
        induction i as [|i]; intros; auto.
        destruct tc; simpl. reflexivity.
        rewrite IHi. reflexivity.
      (* End_of_assert. *)
      clear H0.
      specialize (H n).
      assert ((list_drop n tc) = (nth n tc (1%positive, 0%nat)) :: (tl (list_drop n tc))).
        clear - INF.
        revert tc INF.
        induction n as [|n]; intros.
        (* SCase "O". *)
          destruct tc; auto. simpl in INF. omegaContradiction.
        (* SCase "S n". *)
          destruct tc; simpl in *. omegaContradiction.
          apply IHn. omega.
      (* End_of_assert. *)
        rewrite H0 in H.
        simpl in H.
        destruct (nth n tc (1%positive, 0%nat)) as [a' m]; simpl in *.
        inv H. inv H4.
        unfold satisfy_constraint in *; simpl in *.
        simpl_vect in *. simpl in *.
        symmetry. apply tilling_Z_lemma_1;
        unfold Inhabited_Z; unfold Inhab_num in *; spec_lia.
  Qed.

  Check Vhd.
  Search ":::".

  Definition mk_tilled_poly_instr {nbr_global_parameters}
    (pi: Polyhedral_Instruction nbr_global_parameters)
    tc
      : Polyhedral_Instruction nbr_global_parameters :=
      {| pi_instr := pi.(pi_instr); (** 原指令本身不变 *)
         pi_depth := pi.(pi_depth) + length tc; (** 维度增加tiling的维度 *)
         pi_poly := mk_tilled_boxed_poly tc pi.(pi_poly); (** 多面体根据tiling info变换；但tc为什么不是跟schedule有关，而是只跟domain有关??*)
         pi_schedule :=
           map (fun v => (** 对于schedule中间（中间指哪里，不清楚）插入一堆0，不知道有什么意义 —— 啊，tiling这些维度，不贡献序，排序不需要它们，所以schedule它们对应0即可*)
             Vhd v ::: (V_insert_middle0 (Vtail v))) pi.(pi_schedule);
         pi_transformation :=
           Vmap (fun v =>
             Vhd v ::: (V_insert_middle0 (Vtail v))) pi.(pi_transformation)|}. 


  Lemma expand_tilled_poly_instr nbr_global_parameters
    (pi: Polyhedral_Instruction nbr_global_parameters)
    tc params:
    expand_poly_instr params pi = expand_poly_instr params (mk_tilled_poly_instr pi tc).
  Proof.
    destruct pi; unfold expand_poly_instr; simpl.
    repeat rewrite map_map.
    apply map_ext.
    intro v.
    f_equal.
    unfold make_context_ext. clear.
    apply PVeq_Veq.
    unfold Mprod_vect. simpl.
    rewrite map_map. apply map_ext.
    intro v'.
    Vdestruct v' as v1 v2. simpl_vect. simpl.
    f_equal. Vsplit v2 as v21 v22. simpl_vect. rewrite V_insert_middle0_ok_l.
    reflexivity.
    unfold apply_schedule.
    rewrite map_map. apply map_ext.
    unfold make_context_ext.
    intro v'.
    Vdestruct v' as v1 v2. simpl_vect. simpl.
    f_equal. Vsplit v2 as v21 v22. simpl_vect. rewrite V_insert_middle0_ok_l.
    reflexivity.
  Qed.


  (** 根据分块信息对某输入的多面体程序进行分块 
    1. 全局信息不变
    2. 根据分块信息，对美各指令进行分块
      safe_map2 就是一个普通的map，对每个指令 mk_tilled_poly_instr instr tcs
      虽然返回值是option，但这个option很朴素. 这个文件的分块，是一定正确的【除非传入的tcs的长度都无法匹配】，它只改变了domain. 
      对不同的指令，可以做不同的分块。不太instr的depth是可以不同的。
      嗯... 这里就是没有考虑依赖。
  *)
  Print safe_map2.
  Definition mk_tilled_poly_prog (prog: Poly_Program) tcs:
    option Poly_Program :=
    do instrs <- safe_map2 mk_tilled_poly_instr prog.(pp_poly_instrs) tcs;
    Some
      {| pp_nbr_global_parameters := prog.(pp_nbr_global_parameters);
         pp_poly_instrs := instrs|}.

  (** 这个函数会判断 分块是否正确*)
  Theorem mk_tilled_poly_prog_ok prog1 prog2 tcs:
    mk_tilled_poly_prog prog1 tcs = Some prog2 ->
    forall params mem1 mem2,
      poly_program_semantics_param instruction_point_lt
        prog1 params mem1 mem2 <->
      poly_program_semantics_param instruction_point_lt
        prog2 params mem1 mem2.
  Proof.
    intros.
    unfold mk_tilled_poly_prog in H.
    (** 
    H: (do instrs <- safe_map2 mk_tilled_poly_instr (pp_poly_instrs prog1) tcs;
     Some
       {|
       pp_nbr_global_parameters := pp_nbr_global_parameters prog1;
       pp_poly_instrs := instrs |}) = Some prog2
    *)
    prog_dos.
    assert
      (forall Vparams,
        flatten (map (expand_poly_instr Vparams) prog1.(pp_poly_instrs)) = 
        flatten (map (expand_poly_instr Vparams) instrs)) as FLATTEQ.
    {
    (* Case "Assert: FLATTEQ". *)
      destruct prog1. simpl in *.
      revert tcs instrs Heq_do.
      clear.
      induction pp_poly_instrs0 as [| instr ppinstrs]; intros; simpl in *;
        destruct tcs as [|tc tcs]; clean.
      (* SCase "cons instr ppinstrs". *)
        prog_dos.
        simpl. f_equal.
        apply expand_tilled_poly_instr.
        eapply IHppinstrs; eauto.
    }
    (* End_of_assert FLATTEQ. *)
    split; intro SEM;
    inv SEM; econstructor; eauto; simpl.
    rewrite <- FLATTEQ. auto.
    rewrite FLATTEQ. auto.
  Qed.
    
End Tilling.

(** 这个Tiling看起来相当于是，只在domain进行了分块，没有动schedule，也没有分析被分块维度是不是可交换的，等等 
—— 这个分块真的有意义吗？在代码生成的时候，会对这种映射到0的维度，如何处理？
*)