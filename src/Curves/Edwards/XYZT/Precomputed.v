Require Import Crypto.Util.Decidable Crypto.Util.Notations Crypto.Algebra.Hierarchy.

Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.Curves.Edwards.XYZT.Basic.
Require Import Coq.Classes.Morphisms.

Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Prod.
Require Import Crypto.Algebra.Field.

(* "Niels" coordinates, for twisted Edwards curves with a = -1 *)

Section ExtendedCoordinates.
  Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {char_ge_3 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos BinNat.N.two)}
          {Feq_dec:DecidableRel Feq}.

  Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := Fzero.  Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "*" := Fmul.
  Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
  Local Notation "x ^ 2" := (x*x).

  Context {a d: F}
          {nonzero_a : a <> 0}
          {square_a : exists sqrt_a, sqrt_a^2 = a}
          {nonsquare_d : forall x, x^2 <> d}
          {a_eq_minus1 : a = Fopp 1}.
  Local Notation Epoint := (@E.point F Feq Fone Fadd Fmul a d).
  Local Notation Ppoint := (@point F Feq Fzero Fadd Fmul a d).

  Local Notation "2" := (1 + 1).
  Local Notation "4" := (1 + 1 + 1 + 1).

  Local Notation onCurve x y := (a*x^2 + y^2 = 1 + d*x^2*y^2) (only parsing).

  Lemma nonzero_d : d <> 0.
  Proof. unfold not. intros. destruct nonsquare_d with (x := 0). fsatz. Qed.

  Definition precomputed_point : Type :=
    { P | let '(A, B, C) := P in 
          4 * d * (A*B - 1) = C^2
          /\ d * (A^2 - B^2) = C + C }. 

  Definition precomputed_coordinates (P: precomputed_point) : F*F*F := proj1_sig P.

  Ltac t_step := 
    match goal with
    | _ => progress autounfold with points_as_coordinates in *
    | _ => progress destruct_head' @prod
    | _ => progress destruct_head' @sig
    | _ => progress destruct_head' @and
    | _ => progress destruct_head' @point
    | _ => progress destruct_head' precomputed_point
    | _ => progress destruct_head' @E.point
    | _ => progress cbv [eq CompleteEdwardsCurve.E.eq E.eq E.zero E.add AffineProofs.E.opp fst snd coordinates E.coordinates proj1_sig precomputed_coordinates] in *
    | H: _ = _ :> _ * _ |- _ => inversion H; clear H
    | |- _ /\ _ => split
    end.
  Ltac t := pose proof nonzero_d; repeat t_step; try fsatz.

  Program Definition opp (P: precomputed_point) : precomputed_point :=
    let '(A, B, C) := P in (B, A, Fopp C).
  Next Obligation. t. Qed.    

  Program Definition of_twisted (P: Epoint) : precomputed_point :=
    let '(x, y) := E.coordinates P in
    (y+x, y-x, (let xy := x*y in xy+xy)*d).
  Next Obligation. t. Qed.

  Program Definition to_twisted (P: precomputed_point) : Epoint :=
    let '(A, B, C) := P in ((A - B) / 2, (A + B) / 2).
  Next Obligation. t. Qed.

  Definition basic_to_twisted := @Basic.to_twisted F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec a d nonzero_a.

  Definition basic_opp := @Basic.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec a d nonzero_a.

  Definition of_projective (P: Ppoint) : precomputed_point := of_twisted (basic_to_twisted P).

  Section TwistMinusOne.
    Program Definition m1add_precomputed (P: precomputed_point) (Q: Ppoint) : Ppoint :=
    match precomputed_coordinates P, coordinates Q return F*F*F*F with 
      (ypx2, ymx2, xy2d2), (X1, Y1, Z1, T1) =>
      let YpX1 := Y1+X1 in
      let YmX1 := Y1-X1 in
      let A := YpX1*ypx2 in
      let B := YmX1*ymx2 in
      let C := xy2d2*T1 in
      let D := Z1+Z1 in
      let X3 := A-B in
      let Y3 := A+B in
      let Z3 := D+C in
      let T3 := D-C in
      (* X/Z, Y/T = x, y *)
      let X4 := X3*T3 in
      let Y4 := Y3*Z3 in
      let Z4 := T3*Z3 in
      let T4 := X3*Y3 in
      (X4, Y4, Z4, T4)
    end.
    Next Obligation.
      t.
      assert (onCurve_P: onCurve ((f6-f7)/2) ((f6+f7)/2)) by fsatz.
      assert (onCurve_Q: onCurve (f1/f0) (f2/f0)) by fsatz.
      pose proof AffineProofs.E.denominator_nonzero a nonzero_a square_a d nonsquare_d _ _ onCurve_P _ _ onCurve_Q.
      fsatz.
    Qed.


    Create HintDb points_as_coordinates discriminated.
    Hint Unfold XYZT.Basic.point XYZT.Basic.coordinates XYZT.Basic.from_twisted XYZT.Basic.m1add
         E.point E.coordinates m1add_precomputed of_twisted precomputed_point : points_as_coordinates.
    Local Notation m1add := (Basic.m1add(nonzero_a:=nonzero_a)(square_a:=square_a)(a_eq_minus1:=a_eq_minus1)(nonsquare_d:=nonsquare_d)(k_eq_2d:=reflexivity _)).
    Local Notation XYZT_of_twisted := (Basic.from_twisted(nonzero_a:=nonzero_a)(d:=d)).

    Lemma m1add_precomputed_correct: forall (P Q: Ppoint),
      Basic.eq (m1add_precomputed (of_projective P) Q) (m1add P Q).
    Proof. intros; t; cbv; split; fsatz. Qed.

    Lemma m1add_opp_precomputed_correct: forall (P Q: Ppoint),
      Basic.eq (m1add_precomputed (opp (of_projective P)) Q) (m1add (basic_opp P) Q).
    Proof. intros; t; cbv; split; fsatz. Qed.

  End TwistMinusOne.
End ExtendedCoordinates.
