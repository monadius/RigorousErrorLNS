import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import LNS.Common

/- Definitions of Φ⁺(x) and E(i, r) -/

noncomputable section

namespace LNS

open Real

def Φ (x : ℝ) := logb 2 (1 + (2 : ℝ) ^ x)

def E i r := Φ (i - r) - Φ i + r * deriv Φ i

def Q Δ i r := E i r / E i Δ

lemma err_eq_zero : E i 0 = 0 := by simp [E]

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
