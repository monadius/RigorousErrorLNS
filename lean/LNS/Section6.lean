import Mathlib.Analysis.Calculus.LHopital
import LNS.Common
import LNS.Basic

noncomputable section

namespace LNS

open Real Filter Topology

def Q_lo (Δ r : ℝ) := Q Δ 0 r

def Q_hi (Δ r : ℝ) := (2 ^ (-r) + r * log 2 - 1) / (2 ^ (-Δ) + Δ * log 2 - 1)

def R_opt (Δ : ℝ) :=
  let X := 2 ^ Δ
  logb 2 (-X * (2 * log (X + 1) - log X - 2 * log 2) / (2 * X * (log (X + 1) - log X - log 2) + X - 1))

variable {Δ r : Real}
variable (delta_pos : Δ > 0)

lemma lemma61 : Tendsto (fun i => Q Δ i r) atBot (𝓝 (Q_hi Δ r)) := by
  sorry

lemma lemma62 (hr1 : 0 ≤ r) (hr2 : r < Δ) : AntitoneOn (fun i => Q Δ i r) (Set.Iic 0) := by
  sorry

lemma q_lower_bound (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) : Q_lo Δ r ≤ Q Δ i r :=
  lemma62 hr1 hr2 hi Set.right_mem_Iic hi

lemma q_upper_bound (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) : Q Δ i r ≤ Q_hi Δ r := by
  suffices h : ∀ᶠ (x : ℝ) in atBot, Q Δ i r ≤ Q Δ x r
  · exact ge_of_tendsto (@lemma61 Δ r) h
  · rw [eventually_atBot]
    exact ⟨i, fun j ji => lemma62 hr1 hr2 (le_trans ji hi) hi ji⟩

lemma lemma63 (hi : i ≤ 0) (hc : c ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    |Q Δ i r - Q Δ c r| ≤ Q_hi Δ (R_opt Δ) - Q_lo Δ (R_opt Δ) := by
  sorry

lemma lemma64 {Δₚ} (hc : c ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    |Q Δ c r - Q Δ c (Int.ceil (r / Δₚ) * Δₚ)| ≤ 1 - Q_lo Δ (Δ - Δₚ) := by
  sorry

private def f a r := a * r * log 2 - (a + 1) * log (a + 1) + (a + 1) * log (a * 2 ^ (-r) + 1)

private lemma q_eq : Q Δ i r = f (2 ^ i) r / f (2 ^ i) Δ := by
  simp only [Q, E, deriv_phi, Φ, logb]
  field_simp
  let g := fun r => ((log (1 + 2 ^ (i - r)) - log (1 + 2 ^ i)) * (1 + 2 ^ i) + r * 2 ^ i * log 2)
  suffices h : ∀ r, g r = f (2 ^ i) r
  · rw [← h, ←h]
  intro r; simp only [g, f]
  have eq : (2 : ℝ) ^ (i - r) = 2 ^ i * 2 ^ (-r) := by
    rw [rpow_sub zero_lt_two, rpow_neg zero_le_two]
    exact rfl
  rw [eq]
  ring_nf

private lemma hasDerivAt_f (ha : a + 1 ≠ 0) (har : a * 2 ^ (-r) + 1 ≠ 0) :
    HasDerivAt (fun a => f a r)
      (r * log 2 - (log (a + 1) + 1) +
        (log (a * 2 ^ (-r) + 1) + (a + 1) * (2 ^ (-r) / (a * 2 ^ (-r) + 1)))) a := by
  apply HasDerivAt.add
  · apply HasDerivAt.sub
    · simp only [mul_assoc]
      exact hasDerivAt_mul_const (r * log 2)
    · have : log (a + 1) + 1 = 1 * log (a + 1) + (a + 1) * (1 / (a + 1)) := by
        field_simp
      rw [this]
      apply HasDerivAt.mul
      · exact HasDerivAt.add_const (hasDerivAt_id' _) _
      apply HasDerivAt.log
      · exact HasDerivAt.add_const (hasDerivAt_id' _) _
      · exact ha
  · rw [← one_mul (log (a * 2 ^ (-r) + 1))]
    apply HasDerivAt.mul
    · exact HasDerivAt.add_const (hasDerivAt_id' _) _
    · apply HasDerivAt.log
      · apply HasDerivAt.add_const
        exact hasDerivAt_mul_const _
      · exact har
      -- apply ne_of_gt
      --   apply add_pos_of_nonneg_of_pos _ zero_lt_one
      --   apply mul_nonneg ha
      --   exact rpow_nonneg_of_nonneg zero_le_two _

-- private lemma hasDeriv_f (ha : 0 ≤ a) :
--     deriv (fun a => f a r) 0 = 2 ^ (-r) + r * log 2 - 1 := by

private lemma tendsto_f_0 :
    Tendsto (fun a => f a r) (𝓝 0) (𝓝 0) := by
  have h1 : Tendsto (fun a : ℝ => a + 1) (𝓝 0) (𝓝 1) := by
    rw [(by norm_num : 𝓝 (1 : ℝ) = 𝓝 (0 + 1))]
    exact Tendsto.add_const _ tendsto_id
  rw (config := {occs := .pos [2]}) [(by norm_num : 𝓝 (0 : ℝ) = 𝓝 ((0 * (r * log 2) - 1 * log 1) + 1 * log 1))]
  apply Tendsto.add
  · apply Tendsto.sub
    · simp only [mul_assoc]
      exact Tendsto.mul_const _ tendsto_id
    · exact Tendsto.mul h1 (Tendsto.log h1 one_ne_zero)
  · apply Tendsto.mul h1
    apply Tendsto.log _ one_ne_zero
    rw [(by norm_num : 𝓝 (1 : ℝ) = 𝓝 (0 * 2 ^ (-r) + 1))]
    exact Tendsto.add_const _ (Tendsto.mul_const _ tendsto_id)

private lemma tendsto_deriv_f_0 :
    Tendsto (deriv (fun a => f a r)) (𝓝 0) (𝓝 (2 ^ (-r) + r * log 2 - 1)) := by
  sorry
