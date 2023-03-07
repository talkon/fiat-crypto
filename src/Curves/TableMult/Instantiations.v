Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Require Import Coq.Sorting.Permutation.

Require Import Crypto.Curves.Edwards.XYZT.Precomputed.
Require Import Crypto.Curves.Edwards.XYZT.Basic.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Spec.Curve25519. 
Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.Field.
Require Import Spec.ModularArithmetic.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Curves.TableMult.TableMult.

Import ListNotations.

Local Open Scope Z_scope.

Section Instantiations.

  Section Curve25519. 

    Definition p := Curve25519.p.
    Definition F := F ( p ).
    Definition F_field := @F.field_modulo p Curve25519.prime_p.

    Definition a : F := F.of_Z _ (-1).
    Definition d : F := F.of_Z _ 37095705934669439343138083508754565189542113879843219016388785533085940283555.

    Lemma d_spec : d = ((F.of_Z _ (-121665)) / (F.of_Z _ 121666))%F.
    Proof. Admitted.

    Definition twice_d : F := (d + d)%F.

    Lemma nonzero_a : a <> 0%F.
    Proof. Admitted.

    Lemma twice_d_spec: twice_d = (d + d)%F.
    Proof. auto. Qed.
  
    Context (square_a : exists sqrt_a, (sqrt_a * sqrt_a)%F = a)
        (nonsquare_d : forall x, (x * x)%F <> d)
        (a_eq_minus1 : a = F.opp 1)
        (char_ge_3 : @Ring.char_ge F Logic.eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos BinNat.N.two)).

    Definition affP := @E.point F Logic.eq F.one F.add F.mul a d.
    Definition affO := @E.zero F Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div F_field F.eq_dec a d nonzero_a.

    Definition P := @Basic.point F Logic.eq F.zero F.add F.mul a d.
    Definition O := @Basic.zero F Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div F_field F.eq_dec a d nonzero_a.

    Definition addP := @Basic.m1add F Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div F_field char_ge_3 F.eq_dec a d nonzero_a square_a nonsquare_d a_eq_minus1 twice_d twice_d_spec.
    Definition doubleP := @Basic.m1double F Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div F_field char_ge_3 F.eq_dec a d nonzero_a square_a nonsquare_d a_eq_minus1 twice_d twice_d_spec.
    Definition negP := @Basic.opp F Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div F_field F.eq_dec a d nonzero_a.
    Definition eqP := @Basic.eq F Logic.eq F.zero F.add F.mul a d.
    Definition isomorphic_affP_P := @Basic.isomorphic_commutative_group_m1 F Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div F_field char_ge_3 F.eq_dec a d nonzero_a square_a nonsquare_d a_eq_minus1 twice_d twice_d_spec.
    Definition commutative_group_P := @isomorphic_commutative_groups_group_H _ _ _ _ _ _ _ _ _ _ _ _ isomorphic_affP_P.
    Definition group_P := @Hierarchy.commutative_group_group _ _ _ _ _ commutative_group_P.

    Lemma doubleP_addP : forall Q, eqP (doubleP Q) (addP Q Q).
    Proof. apply Basic.m1double_m1add. Qed.

    Context (s : Z) (t : Z) (n : Z) (nt : Z) (D : Z)
            (Hs: 0 <= s) (Ht: 1 <= t) (Hn: 1 <= n)
            (Hnt: nt = n * t) (HD: D = s * nt).

    Definition P' := @Precomputed.precomputed_point F Logic.eq F.one F.add F.sub F.mul d.
  
    Definition basic_to_twisted := @Basic.to_twisted F Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div F_field F.eq_dec a d nonzero_a.
    Definition twisted_to_basic := @Basic.from_twisted F Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div F_field F.eq_dec a d nonzero_a.

    Definition PtoP' : P -> P' := @Precomputed.of_projective F Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div F_field F.eq_dec a d nonzero_a nonsquare_d a_eq_minus1.

    Definition addP' : P' -> P -> P  := @Precomputed.m1add_precomputed F Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div F_field char_ge_3 F.eq_dec a d nonzero_a square_a nonsquare_d a_eq_minus1.
    
    Definition negP' : P' -> P' := @Precomputed.opp F Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div F_field F.eq_dec a d nonzero_a nonsquare_d a_eq_minus1.

    Lemma addP'_addP : forall Q R, eqP (addP' (PtoP' Q) R) (addP Q R).
    Proof. apply Precomputed.m1add_precomputed_correct. Qed.

    Lemma addP'_negP'_negP_addP : forall Q R, eqP (addP' (negP' (PtoP' Q)) R) (addP (negP Q) R).
    Proof. apply Precomputed.m1add_opp_precomputed_correct. Qed.
    
    
    Definition affB_x : F := F.of_Z _ 15112221349535400772501151409588531511454012693041857206046113283949847762202.
    Definition affB_y : F := F.of_Z _ 46316835694926478169428394003475163141307993866256225615783033603165251855960.

    Program Definition affB : affP := (affB_x, affB_y).
    Next Obligation. Admitted.

    Definition B : P := twisted_to_basic affB.

    Definition mulP := TableMult.mulP P addP negP O.

    Context (table' : Z -> Z -> P')
            (table'_spec : forall bnum d : Z, 0 <= d < 2 ^ (t - 1) 
              -> exists Q : P, eqP Q (table s t P addP negP O B bnum d)
                /\ PtoP' Q = table' bnum d).

    Definition q := Curve25519.l.
    Lemma odd_q : Zodd q.
    Proof. compute. trivial. Qed.
    
    Lemma Hq : 0 < q.
    Proof. lia. Qed.

    Context (mulP_q : mulP q B = O) (HDq: q < 2 ^ D).
    
    Opaque q. (* Needed to make definition below go through *)

    Definition Ed25519_table_multicomb_correct :=
      table_multicomb_positify_correct
      s t n nt D Hs Ht Hn Hnt HD
      P eqP addP doubleP negP O group_P doubleP_addP
      B P' PtoP' addP' negP' table'
      table'_spec addP'_addP addP'_negP'_negP_addP
      q odd_q mulP_q Hq HDq.
    Print Ed25519_table_multicomb_correct.

    Check table_multicomb_positify s t n D P addP doubleP O P' addP' negP' table' (Z.pos q).

  End Curve25519.

End Instantiations.
