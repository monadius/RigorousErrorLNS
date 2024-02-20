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

lemma q_hi_denom_valid : 2 ^ (-Δ) + Δ * log 2 - 1 > 0 := by
  let f x := 2 ^ (-x) + x * log 2 - 1
  have df : ∀ x, HasDerivAt f (log 2 * (1 - 2 ^ (-x))) x := by
    intro x
    rw [(by ring : log 2 * (1 - 2 ^ (-x)) = log 2 * (-1) * 2 ^ (-x) + log 2)]
    apply HasDerivAt.sub_const
    apply HasDerivAt.add _ (hasDerivAt_mul_const _)
    -- have := HasDerivAt.const_rpow zero_lt_two
    exact HasDerivAt.const_rpow zero_lt_two (hasDerivAt_neg _)
  have f0 : f 0 = 0 := by simp
  rw [← f0]
  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici 0)
  · apply ContinuousAt.continuousOn
    exact fun x _ => (df x).differentiableAt.continuousAt
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi, gt_iff_lt]
    intro x hx
    rw [(df x).deriv]
    apply mul_pos (log_pos one_lt_two)
    rw [sub_pos]
    apply rpow_lt_one_of_one_lt_of_neg one_lt_two
    rwa [neg_lt, neg_zero]
  · exact Set.left_mem_Ici
  · exact Set.mem_Ici_of_Ioi delta_pos
  · exact delta_pos

/- Proof of Lemma 6.1 -/

lemma tendsto_f_mul_inv_x : Tendsto (fun a => f a r * a⁻¹) (𝓝[≠] 0) (𝓝 (2 ^ (-r) + r * log 2 - 1)) := by
  simp only [f, add_mul, sub_mul, mul_right_comm]
  rw [(by norm_num; ring : 2 ^ (-r) + r * log 2 - 1 = 1 * (log 2 * r) - (1 * log (0 + 1) + 1) + (1 * log (0 * 2 ^ (-r) + 1) + 2 ^ (-r)))]
  apply Tendsto.add
  · apply Tendsto.sub
    · simp only [mul_right_comm _ r, mul_assoc _ (log 2)]
      exact Tendsto.mul_const _ tendsto_x_mul_inv_x
    · apply Tendsto.add
      · apply Tendsto.mul tendsto_x_mul_inv_x
        apply tendsto_nhdsWithin_of_tendsto_nhds
        apply ContinuousAt.tendsto
        apply ContinuousAt.log _ (by norm_num)
        exact Continuous.continuousAt (continuous_add_right 1)
      · simpa [mul_comm] using tendsto_log_mul_inv_x 1
  · apply Tendsto.add
    · apply Tendsto.mul tendsto_x_mul_inv_x
      apply tendsto_nhdsWithin_of_tendsto_nhds
      apply ContinuousAt.tendsto
      apply ContinuousAt.log _ (by norm_num)
      apply Continuous.continuousAt
      exact Continuous.add (continuous_mul_right _) continuous_const
    · simpa [mul_comm] using tendsto_log_mul_inv_x (2 ^ (-r))

lemma lemma61 : Tendsto (fun i => Q Δ i r) atBot (𝓝 (Q_hi Δ r)) := by
  simp only [q_eq, Q_hi]
  have : ∀ i : ℝ, f (2 ^ i) r / f (2 ^ i) Δ = f (2 ^ i) r * (2 ^ i)⁻¹ / (f (2 ^ i) Δ * (2 ^ i)⁻¹) := by
    intro i; field_simp
  simp only [this]; clear this
  suffices h : ∀ r, Tendsto (fun i : ℝ => f (2 ^ i) r * (2 ^ i)⁻¹) atBot (𝓝 (2 ^ (-r) + r * log 2 - 1))
  · exact Tendsto.div (h _) (h _) (ne_of_gt (q_hi_denom_valid delta_pos))
  · intro r
    apply Tendsto.comp tendsto_f_mul_inv_x
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact tendsto_rpow_atTop_of_base_gt_one _ one_lt_two
    · simp; use 0; intro x _
      exact ne_of_gt (rpow_pos_of_pos zero_lt_two _)

/- Proof of Lemma 6.2 -/

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


lemma lemma62 (hr1 : 0 ≤ r) (hr2 : r < Δ) : AntitoneOn (fun i => Q Δ i r) (Set.Iic 0) := by
  sorry

lemma q_lower_bound (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) : Q_lo Δ r ≤ Q Δ i r :=
  lemma62 hr1 hr2 hi Set.right_mem_Iic hi

lemma q_upper_bound (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) : Q Δ i r ≤ Q_hi Δ r := by
  suffices h : ∀ᶠ (x : ℝ) in atBot, Q Δ i r ≤ Q Δ x r
  · exact ge_of_tendsto (lemma61 delta_pos) h
  · rw [eventually_atBot]
    exact ⟨i, fun j ji => lemma62 hr1 hr2 (le_trans ji hi) hi ji⟩

lemma lemma63 (hi : i ≤ 0) (hc : c ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    |Q Δ i r - Q Δ c r| ≤ Q_hi Δ (R_opt Δ) - Q_lo Δ (R_opt Δ) := by
  sorry

lemma lemma64 {Δₚ} (hc : c ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    |Q Δ c r - Q Δ c (Int.ceil (r / Δₚ) * Δₚ)| ≤ 1 - Q_lo Δ (Δ - Δₚ) := by
  sorry
