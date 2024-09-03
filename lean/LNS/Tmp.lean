import LNS.Common
import LNS.Basic

/- Unused proofs and ideas -/

-- lemma q_upper_bound (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) : Q Δ i r ≤ Q_hi Δ r := by
--   let Q' := (Set.Iic 0).restrict (fun i => Q Δ i r)
--   have : Q Δ i r = Q' ⟨i, hi⟩ := rfl
--   rw [this]
--   apply Antitone.ge_of_tendsto
--   · rw [antitone_restrict]
--     exact lemma62 hr1 hr2
--   · have h := @lemma61 Δ r
--     rw [tendsto_iff_forall_eventually_mem] at h ⊢
--     simp only [eventually_atBot, Set.restrict_apply, Subtype.forall, Set.mem_Iic, Subtype.exists,
--       Subtype.mk_le_mk, exists_prop] at h ⊢
--     intro s sN
--     rcases h s sN with ⟨a, ha⟩
--     use min a 0
--     constructor
--     · exact min_le_right a 0
--     · intro c _ c_le
--       apply ha
--       apply le_trans c_le
--       exact min_le_left a 0

-- Unused
-- private lemma tendsto_f_0 :
--     Tendsto (fun a => f a r) (𝓝 0) (𝓝 0) := by
--   have h1 : Tendsto (fun a : ℝ => a + 1) (𝓝 0) (𝓝 1) := by
--     rw [(by norm_num : 𝓝 (1 : ℝ) = 𝓝 (0 + 1))]
--     exact Tendsto.add_const _ tendsto_id
--   rw (config := {occs := .pos [2]}) [(by norm_num : 𝓝 (0 : ℝ) = 𝓝 ((0 * (r * log 2) - 1 * log 1) + 1 * log 1))]
--   apply Tendsto.add
--   · apply Tendsto.sub
--     · simp only [mul_assoc]
--       exact Tendsto.mul_const _ tendsto_id
--     · exact Tendsto.mul h1 (Tendsto.log h1 one_ne_zero)
--   · apply Tendsto.mul h1
--     apply Tendsto.log _ one_ne_zero
--     rw [(by norm_num : 𝓝 (1 : ℝ) = 𝓝 (0 * 2 ^ (-r) + 1))]
--     exact Tendsto.add_const _ (Tendsto.mul_const _ tendsto_id)

-- lemma deriv_test : Differentiable ℝ (fun (x : ℝ) => 1 + Real.exp x) := by
--   fun_prop
