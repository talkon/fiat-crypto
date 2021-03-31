Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Crypto.Util.Tuple.
Require Import Util.OptionList.
Require Import Crypto.Util.ErrorT.
Module Import List.
  Section IndexOf.
    Context [A] (f : A -> bool).
    Fixpoint indexof (l : list A) : option nat :=
      match l with
      | nil => None
      | cons a l =>
          if f a then Some 0
          else option_map S (indexof l )
      end.
    Lemma indexof_none l (H : indexof l = None) :
      forall i a, nth_error l i = Some a -> f a = false.
    Admitted.
    Lemma indexof_Some l i (H : indexof l = Some i) :
      exists a, nth_error l i = Some a -> f a = true.
    Admitted.
    Lemma indexof_first l i (H : indexof l = Some i) :
      forall j a, j < i -> nth_error l j = Some a -> f a = false.
    Admitted.
  End IndexOf.


  Section FoldMap. (* map over a list in the state monad *)
    Context [A B S] (f : A -> S -> B * S).
    Fixpoint foldmap (l : list A) (s : S) : list B * S :=
      match l with
      | nil => (nil, s)
      | cons a l =>
          let b_s := f a s in
          let bs_s := foldmap l (snd b_s) in
          (cons (fst b_s) (fst bs_s), snd bs_s)
      end.
  End FoldMap.
End List.

Require Import Crypto.Assembly.Syntax.
Definition idx := Z.
Local Set Boolean Equality Schemes.
Variant opname := old (_:REG*option nat) | const (_ : Z) | add | sub | slice (lo sz : N) | set_slice (lo sz : N)(* | ... *).
Class OperationSize := operation_size : N.
Definition op : Set := opname * OperationSize.

Definition node (A : Set) : Set := op * list A.

Local Unset Elimination Schemes.
Inductive expr : Set :=
| ExprRef (_ : idx)
| ExprApp (_ : node expr).
  (* Note: need custom induction principle *)
Local Unset Elimination Schemes.
Definition invert_ExprRef (e : expr) : option idx :=
  match e with ExprRef i => Some i | _ => None end.

Definition node_eqb [A : Set] (arg_eqb : A -> A -> bool) : node A -> node A -> bool := 
  Prod.prod_beq _ _ (Prod.prod_beq _ _ opname_beq N.eqb) (ListUtil.list_beq _ arg_eqb).

Definition dag := list (node idx).

Section Reveal.
  Context (dag : dag).
  Definition reveal_step reveal (i : idx) : expr :=
    match List.nth_error dag (Z.to_nat i) with
    | None => (* undefined *) ExprRef i
    | Some (op, args) => ExprApp (op, List.map reveal args)
    end.
  Fixpoint reveal (n : nat) (i : idx) :=
    match n with
    | O => ExprRef i
    | S n => reveal_step (reveal n) i
    end.

  Definition reveal_node n '(op, args) :=
    ExprApp (op, List.map (reveal n) args).
End Reveal.

Definition merge_node (n : node idx) (d : dag) : idx * dag :=
  match List.indexof (node_eqb Z.eqb n) d with
  | Some i => (Z.of_nat i, d)
  | None => (Z.of_nat (length d), List.app d (cons n nil))
  end.
Fixpoint merge (e : expr) (d : dag) : idx * dag :=
  match e with
  | ExprRef i => (i, d)
  | ExprApp (op, args) =>
    let idxs_d := List.foldmap merge args d in
    merge_node (op, fst idxs_d) (snd idxs_d)
  end.

Lemma reveal_merge : forall d e, exists n, reveal (snd (merge e d)) n (fst (merge e d)) = e.
Proof.
Admitted.

Require Import Crypto.Util.Option Crypto.Util.Notations.
Import ListNotations.

Definition simplify (dag : dag) (e : node idx) : expr :=
  List.fold_right (fun f e => f e) (reveal_node dag 4 e)
  [fun e => match e with
    ExprApp (((add|sub),s), [a; ExprApp ((const 0, _), []) ]) =>
      if N.eqb s 64 then a else e | _ => e end
  ;fun e => match e with
    ExprApp ((sub,s)as op, [ExprApp ((add, s'), [a; b]); a']) =>
      if N.eqb s s' && expr_beq a a' then b else e | _ => e end
  ;fun e => match e with
    ExprApp ((sub,s), [a; b]) =>
      if expr_beq a b then ExprApp ((const 0, s), []) else e | _ => e end]%bool.


Definition reg_state := Tuple.tuple (option idx) 16.
Definition flag_state := Tuple.tuple (option idx) 6.
Definition mem_state := list (idx * idx).

Definition get_flag (st : flag_state) (f : FLAG) : option idx
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     match f with
     | CF => cfv
     | PF => pfv
     | AF => afv
     | ZF => zfv
     | SF => sfv
     | OF => ofv
     end.
Definition set_flag_internal (st : flag_state) (f : FLAG) (v : option idx) : flag_state
  := let '(cfv, pfv, afv, zfv, sfv, ofv) := st in
     (match f with CF => v | _ => cfv end,
      match f with PF => v | _ => pfv end,
      match f with AF => v | _ => afv end,
      match f with ZF => v | _ => zfv end,
      match f with SF => v | _ => sfv end,
      match f with OF => v | _ => ofv end).
Definition set_flag (st : flag_state) (f : FLAG) (v : idx) : flag_state
  := set_flag_internal st f (Some v).
Definition havoc_flag (st : flag_state) (f : FLAG) : flag_state
  := set_flag_internal st f None.
Definition havoc_flags : flag_state
  := (None, None, None, None, None, None).

Definition get_reg (st : reg_state) (ri : nat) : option idx
  := Tuple.nth_default None ri st.
Definition set_reg (st : reg_state) ri (i : idx) : reg_state
  := Tuple.from_list_default None _ (ListUtil.set_nth
       ri
       (Some i)
       (Tuple.to_list _ st)).

Definition load (a : idx) (s : mem_state) : option idx :=
  option_map snd (find (fun p => fst p =? a)%Z s).
Definition store (a v : idx) (s : mem_state) : option mem_state :=
  n <- indexof (fun p => fst p =? a)%Z s;
  Some (ListUtil.update_nth n (fun ptsto => (fst ptsto, v)) s).

Record symbolic_state := { dag_state :> dag ; symbolic_reg_state :> reg_state ; symbolic_flag_state :> flag_state ; symbolic_mem_state :> mem_state }.
Definition update_dag_with (st : symbolic_state) (f : dag -> dag) : symbolic_state
  := {| dag_state := f st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_reg_with (st : symbolic_state) (f : reg_state -> reg_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := f st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_flag_with (st : symbolic_state) (f : flag_state -> flag_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := f st.(symbolic_flag_state) ; symbolic_mem_state := st.(symbolic_mem_state) |}.
Definition update_mem_with (st : symbolic_state) (f : mem_state -> mem_state) : symbolic_state
  := {| dag_state := st.(dag_state); symbolic_reg_state := st.(symbolic_reg_state) ; symbolic_flag_state := st.(symbolic_flag_state) ; symbolic_mem_state := f st.(symbolic_mem_state) |}.

Module error.
  Variant error :=
  | get_flag (f : FLAG)
  | get_reg (r : REG)
  | load (a : idx)
  | store (a v : idx)
  | set_const (_ : CONST) (_ : idx)

  | unimplemented_instruction (_ : NormalInstruction)
  | ambiguous_operation_size (_ : NormalInstruction).
End error.
Notation error := error.error.

Definition M T := symbolic_state -> ErrorT (error * symbolic_state) (T * symbolic_state).
Definition ret {A} (x : A) : M A :=
  fun s => Success (x, s).
Definition err {A} (e : error) : M A :=
  fun s => Error (e, s).
Definition some_or {A} (f : symbolic_state -> option A) (e : error) : M A :=
  fun st => match f st with Some x => Success (x, st) | None => Error (e, st) end.
Definition bind {A B} (x : M A) (f : A -> M B) : M B :=
  fun s => (x_s <- x s; f (fst x_s) (snd x_s))%error.
Declare Scope x86symex_scope.
Delimit Scope x86symex_scope with x86symex.
Bind Scope x86symex_scope with M.
Notation "x <- y ; f" := (bind y (fun x => f%x86symex)) : x86symex_scope.
Section MapM. (* map over a list in the state monad *)
  Context [A B] (f : A -> M B).
  Fixpoint mapM (l : list A) : M (list B) :=
    match l with
    | nil => ret nil
    | cons a l => b <- f a; bs <- mapM l; ret (cons b bs)
    end%x86symex.
End MapM.
Definition mapM_ [A] (f: A -> M unit) l : M unit := _ <- mapM f l; ret tt.

Definition GetFlag f : M idx :=
  some_or (fun s => get_flag s f) (error.get_flag f).
Definition GetReg ri : M idx :=
  some_or (fun st => get_reg st ri) (error.get_reg (widest_register_of_index ri)).
Definition Load (a : idx) : M idx := some_or (load a) (error.load a).
Definition SetFlag f i : M unit :=
  fun s => Success (tt, update_flag_with s (fun s => set_flag s f i)).
Definition SetReg rn i : M unit :=
  fun s => Success (tt, update_reg_with s (fun s => set_reg s rn i)).
Definition Store (a v : idx) : M unit :=
  ms <- some_or (store a v) (error.store a v);
  fun s => Success (tt, update_mem_with s (fun _ => ms)).
Definition App (n : node idx) : M idx := fun s =>
  let i_dag := merge (simplify s n) s in
  Success (fst i_dag, update_dag_with s (fun _ => snd i_dag)).

Local Unset Elimination Schemes.
Inductive pre_expr : Set :=
| PreFlag (_ : FLAG)
| PreReg (_ : nat) (* 0 <= i < 16 *)
| PreMem (_ : pre_expr)
| PreApp (_:node pre_expr).
(* note: need custom induction principle *)
Local Set Elimination Schemes.
Fixpoint SymevalPre (e : pre_expr) : M idx :=
  match e with
  | PreFlag f => GetFlag f
  | PreReg r => GetReg r
  | PreMem a => a <- SymevalPre a; Load a
  | PreApp (op, args) => args <- mapM SymevalPre args; App (op, args)
  end%x86symex.

Class AddressSize := address_size : N.
Definition PreAddress {sa : AddressSize} (a : MEM) : pre_expr :=
  PreApp (add, sa,
  [PreApp (add, sa,
   [PreReg (reg_index (mem_reg a));
   match mem_extra_reg a with
   | Some _ => PreReg (reg_index (mem_reg a))
   | None => PreApp ((const 0, sa), nil)
   end]);
   PreApp ((const match mem_offset a with Some z => z | _ => 0 end, sa), nil)]).

Section WithOperationSize.
  Context {sa : AddressSize} {s : OperationSize}.
  Definition PreOperand (a : ARG) : pre_expr :=
    match a with
    | reg a =>
        (* note: partial register access should be handled here *)
        PreReg (reg_index a)
    | mem a => PreMem (PreAddress (sa:=sa) a)
    | Syntax.const a => PreApp ((const a, s), nil)
  end.
  Definition Symeval a := SymevalPre (PreOperand a).
  Definition Symaddr a := SymevalPre (PreAddress a).

  Definition SetOperand (a : ARG) (v : idx) : M unit :=
    match a with
    | Syntax.const a => err (error.set_const a v)
    | mem a =>
        addr <- Symaddr a;
        if negb (mem_is_byte a)
        then
          Store addr v
        else
          old <- Load addr;
          v <- App ((set_slice 0 8, 64), [old; v]);
          Store addr v
    | reg a =>
        let '(a, lo, sz) := index_and_shift_and_bitcount_of_reg a in
        if N.eqb sz 64
        then
          SetReg a v
        else
          old <- GetReg a;
          v <- App ((set_slice lo sz, 64), [old; v]);
          SetReg a v
    end%N%x86symex.

End WithOperationSize.

Definition SymexNormalInstruction (instr : NormalInstruction) : M unit :=
  let sa : AddressSize := 64%N in
  match Syntax.operation_size instr with Some (Some s) =>
  let s : OperationSize := s in
  match instr.(Syntax.op), instr.(args) with
  | mov, [dst; src] => (* Note: unbundle when switching from N to Z *)
    e <- Symeval src;
    SetOperand dst e
  | lea, [dst; mem src] => (* Flags Affected: None *)
    e <- Symaddr src;
    SetOperand dst e
  | _, _ => err (error.unimplemented_instruction instr)
 end | _ => err (error.ambiguous_operation_size instr) end%N%x86symex.

Definition SymexNormalInstructions := fun st is => mapM_ SymexNormalInstruction is st.

Definition init
  (arrays : list (REG * nat)) (* full 64-bit registers only *)
  (stack : nat)
  : symbolic_state :=
  let sz := 64%N in
  let dag := List.map (fun i =>
    ((old (widest_register_of_index i,None), 64%N),[])) (seq 0 16) in
  let arrayentries := List.flat_map (fun r_n =>
    List.map (fun i => (fst r_n, i)) (List.seq 0 (snd r_n))) arrays in
  let heap_dag := foldmap (fun r_i dag => let r := fst r_i in
       let p_dag := merge (ExprApp ((add, sz),[ExprRef (Z.of_nat (reg_index r)); ExprApp ((const (8 * Z.of_nat (snd r_i)), sz), [])])) dag in
       let v_dag := merge (ExprApp ((old (r, Some (snd r_i)), sz),[])) (snd p_dag) in
       ((fst p_dag, fst v_dag), snd p_dag)
       ) arrayentries dag in
  let stack_dag := foldmap (fun i dag => let r := rsp in
       let p_dag := merge (ExprApp ((sub, sz),[ExprRef (Z.of_nat (reg_index r)); ExprApp ((const (8*Z.of_nat i), sz), [])])) dag in
       let v_dag := merge (ExprApp ((old (r, Some i), sz),[])) (snd p_dag) in
       ((fst p_dag, fst v_dag), snd p_dag)
       ) (seq 0 stack) (snd heap_dag) in
  let regs := List.map (fun i => Some (Z.of_nat i)) (seq 0 16) in
  {|
    dag_state := snd stack_dag;
    symbolic_reg_state := Tuple.from_list _ regs eq_refl;
    symbolic_mem_state := fst heap_dag ++ fst stack_dag;
    symbolic_flag_state := Tuple.repeat None 6
  |}.

Example test1 : match (
  let st := init [(rsi, 4)] 0 in
  (SymexNormalInstructions st
    [Build_NormalInstruction lea [reg rax; mem (Build_MEM false rsi None (Some 16%Z))]
    ;Build_NormalInstruction mov [reg rbx; mem (Build_MEM false rsi None (Some 16%Z))]
    ;Build_NormalInstruction lea [reg rcx; mem (Build_MEM false rsi (Some rbx) (Some 7%Z))]
    ;Build_NormalInstruction mov [         mem (Build_MEM false rsi None (Some 24%Z)); reg rcx]
    ])
) with Error _ => False | Success st => True end. native_cast_no_check I. Qed.

Definition SymexLines st (lines : list Syntax.Line) :=
  SymexNormalInstructions st (Option.List.map (fun l =>
    match l.(rawline) with INSTR instr => Some instr | _ => None end) lines).

Require Crypto.Assembly.Parse Crypto.Assembly.Parse.Examples.fiat_25519_carry_square_optimised_seed20.
Definition lines' := Eval native_compute in
  Assembly.Parse.parse
  Assembly.Parse.Examples.fiat_25519_carry_square_optimised_seed20.example.
Definition lines := Eval cbv in ErrorT.invert_result lines'.

Import Coq.Strings.String.
Local Open Scope string_scope.

(*
Compute
  let st := init [(rsi, 4); (rdi, 4)] 48 in
  SymexLines st lines.
*)