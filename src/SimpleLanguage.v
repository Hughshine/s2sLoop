Add LoadPath "~/formal/s2sLoop/from_compcert".
Add LoadPath "~/formal/PilkiLib".
Add LoadPath "~/formal/s2sLoop/src".
Require Import Libs.
(*Require Import Floats.*)
Require Import AST.
Require Import Setoid.
Require Import ArithClasses.
Require Import Memory.
Require Import Instructions.
Require Import Bounds.

Parameter ocaml_string: Type.
Extract Constant ocaml_string =>
  "string".

Set Implicit Arguments.

Module BM := BMem(ZNum).


Module Instructions <:INSTRS(ZNum) with Definition Value := BM.Value.
  Module T := Tools(ZNum).
  Import T.


  (* The values of the language *)
  Definition Value := BM.Value.

  (** 加减乘除 *)

  Inductive Binary_opp:=
  | BO_add
  | BO_mul
  | BO_sub
  | BO_div.

  (** 表达式：常量（写成一个关于context的仿射表达式，如果对context变换，这个表达式的形式其实也会变换），对数组的访问，一元/二元表达式（递归的） *)
  Inductive Expression (n:nat) : Type :=
  | Exp_const: ZVector (S n) -> Expression n
  | Exp_loc: Array_Id * list (ZVector (S n)) -> Expression n
  | Exp_bin: Expression n -> Binary_opp -> Expression n -> Expression n
  | Exp_opp: Expression n -> Expression n.


  (** （某个context下）的写指令：对某个内存地址写；*)
  (** 这里似乎假设每个指令都是 经过一些计算（read）然后写向某个内存地址 *)
  Record Instruction': Type :=
    { context_size: nat;
      write_loc: Array_Id * list (ZVector (S context_size));
      body: Expression context_size;
      (* what follows is here for pretty printing reasons *)
      instr_loop_vars : list ocaml_string;
      instr_body_string: ocaml_string
    }.

  Definition Instruction := Instruction'.

  Fixpoint exp_read_locs {n} (exp: Expression n) :=
    match exp with
      | Exp_const _ => []
      | Exp_loc loc => [loc]
      | Exp_bin l _ r => exp_read_locs l ++ exp_read_locs r
      | Exp_opp e => exp_read_locs e
    end.

  Definition read_locs instr:=
    exp_read_locs (body instr).

  (** evaluation 可能无法求解出值 *)
  Definition eval_bin_opp opp arg1 arg2 :=
    match opp with
    | BO_add => Some (arg1 + arg2)
    | BO_mul => Some (arg1 * arg2)
    | BO_sub => Some (arg1 - arg2)
    | BO_div => if arg2 == 0 then None else Some (arg1 / arg2)
  end.

  (** rvals：读内存部分语义拿到了这个函数外，作为eval_exp的输入，从左至右 *)

  Fixpoint eval_exp {n}  ectxt (exp: Expression n) rvals :
    option (Value * list Value):=
    match exp with
    | Exp_const v => Some (〈v, ectxt〉, rvals)
    | Exp_loc _ =>
      match rvals with
      | [] => None
      | z :: rvals' =>
        Some (z, rvals')
      end
    | Exp_bin l opp r =>
      do{;
        (zl, rvals1) <- eval_exp ectxt l rvals;;
        (zr, rvals2) <- eval_exp ectxt r rvals1;;
        res <- eval_bin_opp opp zl zr;
        Some (res, rvals2)
      }
    | Exp_opp e =>
      do (res, rvals') <- eval_exp ectxt e rvals;
      Some (- res, rvals')
    end.


  (** ctxt的这个1是什么？ 应该要对应常数。
    要求在一个context/准确的内存序列下，计算出对应的值
  *)
  Definition semantics (instr:Instruction) ctxt rvals res : Prop :=
    eval_exp (1:::ctxt) instr.(body) rvals = Some(res, []).

  Lemma semantics_deterministic:
    forall i v lv val1 val2,
      semantics i v lv val1 -> semantics i v lv val2 -> val1 = val2.
  Proof.
    unfold semantics; intros; congruence.
  Qed.
End Instructions.
