import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import LNS.Common

/- Definitions of Φ⁺(x) and E(i, r) -/

noncomputable section

namespace LNS

open Real

/- Φ⁺ from Introduction -/

def Φ (x : ℝ) := logb 2 (1 + (2 : ℝ) ^ x)

/- Iₓ and Rₓ correspond to iₓ and rₓ from Eq (1) -/

def Iₓ (Δ x : ℝ) := Δ * Int.ceil (x / Δ)

def Rₓ (Δ x : ℝ) := Iₓ Δ x - x

/- Φₜ is the first order Taylor approximation of Φ⁺ from Eq (1) -/

def Φₜ (Δ x : ℝ) := Φ (Iₓ Δ x) - Rₓ Δ x * deriv Φ (Iₓ Δ x)

/- E i r is the error of the first order Taylor approximation
   defined for all real i and r -/

def E (i r : ℝ) := Φ (i - r) - Φ i + r * deriv Φ i

def Q (Δ i r : ℝ) := E i r / E i Δ

lemma err_eq_zero : E i 0 = 0 := by simp [E]

lemma i_sub_r_eq_x (Δ x : ℝ) : Iₓ Δ x - Rₓ Δ x = x := by
  simp only [Iₓ, Rₓ, sub_sub_cancel]

lemma Φₜ_error : Φ x - Φₜ Δ x = E (Iₓ Δ x) (Rₓ Δ x) := by
  simp only [Φₜ, E, i_sub_r_eq_x]; ring

lemma x_le_ix {Δ} (hd : 0 < Δ) x : x ≤ Iₓ Δ x :=
  (div_le_iff' hd).mp $ Int.le_ceil $ x / Δ

lemma x_neg_iff_ix_neg {Δ} (hd : 0 < Δ) x : x ≤ 0 ↔ Iₓ Δ x ≤ 0 := by
  constructor
  · intro hx
    apply mul_nonpos_of_nonneg_of_nonpos (le_of_lt hd)
    rw [← Int.cast_zero, Int.cast_le, Int.ceil_le, Int.cast_zero]
    exact div_nonpos_of_nonpos_of_nonneg hx (le_of_lt hd)
  · exact le_trans (x_le_ix hd x)

lemma rx_eq_fract {Δ x : ℝ} (hd : Δ ≠ 0) (ix : Iₓ Δ x ≠ x) :
    Rₓ Δ x = Δ * (1 - Int.fract (x / Δ)) := by
  -- unfold Rₓ Int.fract Iₓ
  -- field_simp
  -- rw [Int.ceil_sub_self_eq]
  sorry

lemma rx_nonneg {Δ} (hd : 0 < Δ) x : 0 ≤ Rₓ Δ x := by
  sorry

lemma rx_lt_delta {Δ} (hd : 0 < Δ) x : Rₓ Δ x < Δ := by
  sorry

/- Derivatives and differentiability of Φ -/

lemma hasDerivAt_two_pow (x : ℝ) : HasDerivAt (fun x => (2 : ℝ) ^ x) ((2 : ℝ) ^ x * log 2) x := by
  rw [(by ring : (2 : ℝ) ^ x * log 2 = 0 * x * (2 : ℝ) ^ (x - 1) + 1 * (2 : ℝ) ^ x * log 2)]
  exact HasDerivAt.rpow (hasDerivAt_const x 2) (hasDerivAt_id' x) two_pos

lemma deriv_two_pow (x : ℝ) : deriv (fun x => (2 : ℝ) ^ x) x = (2 : ℝ) ^ x * log 2 :=
  HasDerivAt.deriv (hasDerivAt_two_pow x)

lemma one_plus_two_pow_pos (x : ℝ) : 0 < 1 + (2 : ℝ) ^ x := by
  linarith [rpow_pos_of_pos two_pos x]

lemma one_plus_two_pow_ne_zero (x : ℝ) : 1 + (2 : ℝ) ^ x ≠ 0 := by
  linarith [rpow_pos_of_pos two_pos x]

lemma diff_aux1 : Differentiable ℝ (fun (x : ℝ) => 1 + (2 : ℝ) ^ x) := by
  apply Differentiable.const_add
  apply Differentiable.rpow <;> simp

lemma diff_aux2 : Differentiable ℝ (fun (x : ℝ) => log (1 + (2 : ℝ) ^ x)) := by
  apply Differentiable.log diff_aux1
  exact one_plus_two_pow_ne_zero

lemma differentiable_phi : Differentiable ℝ Φ :=
  Differentiable.div_const diff_aux2 _

lemma deriv_phi : deriv Φ = fun (x : ℝ) => (2 : ℝ) ^ x / (1 + (2 : ℝ) ^ x) := by
  unfold Φ logb
  ext x; simp
  rw [deriv.log, deriv_const_add, deriv_two_pow]
  · field_simp; ring
  · apply DifferentiableAt.const_add
    apply DifferentiableAt.rpow _ differentiableAt_id' <;> simp
  · exact one_plus_two_pow_ne_zero _

lemma deriv_phi2 {x} : deriv (deriv Φ) x = (2 : ℝ) ^ x * log 2 / (1 + (2 : ℝ) ^ x) ^ 2 := by
  simp [deriv_phi]
  rw [deriv_div]
  · simp [deriv_two_pow]; ring
  · apply (hasDerivAt_two_pow x).differentiableAt
  · simp [(hasDerivAt_two_pow x).differentiableAt]
  · exact one_plus_two_pow_ne_zero x

end LNS
