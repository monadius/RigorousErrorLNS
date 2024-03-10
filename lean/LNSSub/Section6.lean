import LNS.Common
import LNS.Basic
import LNS.Section5
import LNS.Lemma61
import LNS.Lemma65
import LNS.Lemma66
import LNS.Lemma67


noncomputable section

namespace LNS

open Real Filter Topology


def EM Δ := E (-1) Δ

def QR Δ :=  Q_lo Δ (R_opt Δ) - Q_hi Δ (R_opt Δ)

def QI Δ ΔP := 1 - Q_hi Δ (Δ - ΔP)

variable (rnd : ℝ → ℝ)

variable (ε  : ℝ)

variable (hrnd : ∀ x , |x - rnd x| ≤ ε)

variable (rnd_mono: Monotone rnd)

variable (rnd_1:  rnd (1:ℝ) = (1:ℝ))

variable (rnd_0:  rnd (0:ℝ) = (0:ℝ))

noncomputable def EEC (Δ ΔP c i r  : ℝ) := rnd (Φ i) - rnd (r * rnd (deriv Φ i) ) -
                      rnd (rnd (E i Δ) * rnd (Q Δ c (Int.floor (r / ΔP) * ΔP)))

noncomputable def EECfix (Δ ΔP c i r  : ℝ):= |Φ (i - r) - EEC rnd Δ ΔP c i r|

lemma Phi_eq_EC (hi: i ≤ -1) (hr1 : 0 < r) (hr2 : r < Δ):
        Φ (i - r) = Φ i - r * (deriv Φ i) - (E i Δ)*(Q Δ i r) :=by
  have ep : E i Δ > 0 := by apply err_pos; assumption; linarith
  unfold Q; field_simp; unfold E; ring_nf

lemma hrndn :  |rnd x - x| ≤ ε := by
  have : |rnd x - x| = |x - rnd x| :=by apply abs_sub_comm
  rw[this]
  apply hrnd


lemma Q_lt_1 (hc: c ≤ -1) (hr1 : 0 ≤ r) (hr2 : r < Δ): |rnd (Q Δ c r)| ≤ (1:ℝ) :=by
  have i1: Q Δ c r ≥ 0:= by
    unfold Q; apply div_nonneg; apply err_nonneg hc hr1;  apply err_nonneg hc; linarith
  have i2: rnd (Q Δ c r) ≥ 0 :=by
    rw[← rnd_0]; apply rnd_mono; assumption
  have e1: |rnd (Q Δ c r)| = rnd (Q Δ c r):= by apply abs_of_nonneg; assumption;
  rw[e1, ← rnd_1];  apply rnd_mono;
  unfold Q; apply le_of_lt;
  have i3:  E c Δ >0 :=by apply err_pos hc; linarith
  apply (div_lt_one i3).mpr
  apply strictMonoOn_E_r;
  any_goals simp;
  any_goals linarith;



lemma sum_8_abs (a1 a2 a3 a4 a5 a6 a7 a8 :ℝ) :
  |a1+ a2 + a3 - (a4 + a5 + a6 + a7 + a8)| ≤ |a1|+|a2|+|a3|+|a4|+|a5|+|a6|+|a7|+|a8|:=by
  have i1 :  |a1+a2+a3-(a4 + a5 + a6 + a7 + a8)|  ≤  |a1+a2+a3| + |a4+a5+a6+a7+a8|:= by  apply abs_sub
  have i2 :  |a1+a2+a3|  ≤  |a1+a2|+|a3|:= by  apply abs_add
  have i3 :  |a1+a2|  ≤  |a1|+|a2|:= by  apply abs_add
  have i4 :  |a4+a5+a6+a7+a8|  ≤  |a4+a5+a6+a7|+|a8|:= by  apply abs_add
  have i5 :  |a4+a5+a6+a7|  ≤  |a4+a5+a6|+|a7|:= by  apply abs_add
  have i6 :  |a4+a5+a6|  ≤  |a4+a5|+|a6|:= by  apply abs_add
  have i7 :  |a4+a5|  ≤  |a4|+|a5|:= by  apply abs_add
  linarith;



lemma Theorem68 (hi : i ≤ -1)(hc : c ≤ -1) (hr1 : 0 < r) (hr2 : r < Δ) (hΔ:  ΔP < Δ ) (hΔP:  ΔP > 0 ):
    EECfix rnd Δ ΔP c i r ≤ (4+Δ)*ε + (EM Δ) * (QR Δ + QI Δ ΔP + ε) := by
    set rr := (Int.floor (r / ΔP) * ΔP)
    set a1 := Φ i - rnd (Φ i)
    set a2 := rnd (r * rnd (deriv Φ i) ) - r * rnd (deriv Φ i)
    set a3 := r * (rnd (deriv Φ i) -  (deriv Φ i))
    set a4 := (E i Δ)*((Q Δ i r) - (Q Δ c r))
    set a5 := (E i Δ)*((Q Δ c r) - (Q Δ c rr))
    set a6 := (E i Δ)*((Q Δ c rr) - (rnd (Q Δ c rr)))
    set a7 := (rnd (Q Δ c rr)) * ((E i Δ) - (rnd (E i Δ) ) )
    set a8 := (rnd (E i Δ) ) * (rnd (Q Δ c rr)) - rnd (rnd (E i Δ) * rnd (Q Δ c rr))

    have irr0: rr ≥ 0:= by
      apply mul_nonneg; simp; apply Int.floor_nonneg.mpr;
      apply div_nonneg;
      any_goals linarith;

    have irr1: r - rr ≥ 0:= by
      simp;
      have i2: Int.floor (r / ΔP) * ΔP ≤ r / ΔP * ΔP := by
        apply mul_le_mul; apply Int.floor_le; simp; linarith
        apply div_nonneg;
        any_goals linarith;
      have e0: r / ΔP * ΔP = r := by field_simp
      linarith;

    have eq0: Φ (i - r) - EEC rnd Δ ΔP c i r = a1 + a2 + a3 - (a4 + a5 + a6 + a7 + a8) := by
      rw[Phi_eq_EC hi hr1 hr2]; unfold EEC;  ring_nf
    have i0 : |E i Δ| ≤ (EM Δ) := by unfold EM; apply err_bound hi ; linarith; linarith
    have i01 :  (EM Δ) ≥ 0 :=by
      have : |E i Δ| ≥ 0 := by simp;
      linarith
    have i1 : |a1| ≤ ε := by apply hrnd
    have i2 : |a2| ≤ ε := by apply hrndn; apply hrnd;
    have i3 : |a3| ≤ Δ * ε := by
      have e1 : |a3| = |r| * |rnd (deriv Φ i) -  (deriv Φ i)| :=by apply abs_mul
      have e2 : |r| = r := by apply abs_of_pos hr1;
      rw[e1,e2]; apply mul_le_mul; linarith; apply hrndn; apply hrnd; simp; linarith;
    have i4 : |a4| ≤ (EM Δ) * (QR Δ) :=by
      have e1: |a4| = |E i Δ| * |(Q Δ i r) - (Q Δ c r)| := by apply  abs_mul
      have i1: |(Q Δ i r) - (Q Δ c r)| ≤ (QR Δ):= by apply lemma66; any_goals linarith
      rw[e1] ; apply mul_le_mul; assumption;  assumption;  simp; assumption;
    have i5: |a5| ≤ (EM Δ) * (QI Δ ΔP) :=by
      have e1: |a5| = |E i Δ| * |(Q Δ c r) - (Q Δ c rr)| := by apply  abs_mul
      have i1: |(Q Δ c r) - (Q Δ c rr)| ≤ QI Δ ΔP := by apply lemma67; any_goals linarith
      rw[e1] ; apply mul_le_mul; assumption;  assumption;  simp; assumption;
    have i6: |a6| ≤ (EM Δ) * ε :=by
      have e1: |a6| = |E i Δ| * |(Q Δ c rr) - (rnd (Q Δ c rr))| := by apply  abs_mul
      have i1: |(Q Δ c rr) - (rnd (Q Δ c rr))| ≤ ε := by apply hrnd
      rw[e1] ; apply mul_le_mul; assumption;  assumption; simp; assumption;
    have i7: |a7| ≤  ε :=by
      have e1: |a7| = |rnd (Q Δ c rr)| * |(E i Δ) - (rnd (E i Δ) )| := by apply  abs_mul
      have i1: |(E i Δ) - (rnd (E i Δ) )| ≤ ε := by apply hrnd
      have i2: |rnd (Q Δ c rr)| ≤ (1:ℝ) :=by
        apply Q_lt_1; apply rnd_mono; apply rnd_1; apply rnd_0;
        assumption; linarith; linarith
      have e2: ε = (1:ℝ) * ε :=by simp
      rw[e1, e2] ; apply mul_le_mul; assumption;  assumption; simp; linarith;
    have i8: |a8| ≤  ε  := by apply hrnd
    have isum: EECfix rnd Δ ΔP c i r ≤ |a1|+|a2|+|a3|+|a4|+|a5|+|a6|+|a7|+|a8|:=by
      unfold EECfix; rw[eq0]; apply sum_8_abs
    linarith
