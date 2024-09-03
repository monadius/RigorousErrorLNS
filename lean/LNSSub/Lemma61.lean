import LNS.Common
import LNS.Basic


noncomputable section

namespace LNS

open Real Filter Topology

variable {i Δ r : Real}
variable (delta_pos : Δ > 0)
variable (hi : i ≤ -1)
variable (hrΔ :=  r < Δ)
variable (hr0 :=  r > 0)



def Q_lo (Δ r : ℝ) := Q Δ (-1:ℝ) r

def Q_hi (Δ r : ℝ) := (2 ^ (-r) + r * log 2 - 1) / (2 ^ (-Δ) + Δ * log 2 - 1)



def f a r := a * r * log 2 + (1-a) * log (1-a) - (1-a) * log (1- a * 2 ^ (-r) )




lemma q_eq : Q Δ i r = f (2 ^ i) r / f (2 ^ i) Δ := by
  have i1: 1 - (2 : ℝ) ^ i > 0 := one_minus_two_pow_pos hi
  have e00 : (2:ℝ) ^ (i - r) = (2^i) * 2^(-r) :=by apply Real.rpow_add; linarith
  have e01 : (2:ℝ) ^ (i - Δ) = (2^i) * 2^(-Δ) :=by apply Real.rpow_add; linarith
  have i3: E i Δ > 0 := by apply err_pos hi; linarith
  have e1 :  (E i r)* (1 - 2^i) * log 2 = (f (2 ^ i) r) := by
    unfold E ; rw[deriv_phi]; unfold dphi Φ logb  f;
    rw[e00]
    field_simp; ring_nf; exact hi
  have e2 :  (E i Δ)* (1 - 2^i) * log 2 = (f (2 ^ i) Δ) := by
    unfold E ; rw[deriv_phi]; unfold dphi Φ logb  f;
    rw[e01]
    field_simp; ring_nf; assumption
  unfold Q
  rw[← e1, ← e2]; field_simp; ring_nf



lemma q_hi_denom_valid : 2 ^ (-Δ) + Δ * log 2 - 1 > 0 := by
  let f x := 2 ^ (-x) + x * log 2 - 1
  have df : ∀ x, HasDerivAt f (log 2 * (1 - 2 ^ (-x))) x := by
    intro x
    rw [(by ring : log 2 * (1 - 2 ^ (-x)) = (-1) * 2 ^ (-x) * log 2 + log 2)]
    apply HasDerivAt.sub_const
    apply HasDerivAt.add _ (hasDerivAt_mul_const _)
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



lemma tendsto_f_mul_inv_x : Tendsto (fun a => f a r * a⁻¹) (𝓝[≠] 0) (𝓝 (2 ^ (-r) + r * log 2 - 1)) := by
  unfold f;
  simp only [f, add_mul, sub_mul, mul_right_comm]; simp;
  have e1: 2 ^ (-r) + r * log 2 - 1 = 1*r * log 2 + (-1-1*log (1-0)) -  (-2 ^ (-r)-1*log (1-0*2^(-r))) :=by
    ring_nf

  rw[e1]
  apply Tendsto.sub; apply Tendsto.add; apply Tendsto.mul_const ;
  have  e2: (fun k ↦ k * r * k⁻¹) = (fun k ↦ k * k⁻¹*r):=by ext k; ring_nf
  rw[e2]; apply Tendsto.mul_const; apply tendsto_x_mul_inv_x
  apply Tendsto.sub;
  have e3: (fun x ↦ x⁻¹ * log (1 - x)) = (fun x ↦ log ((-1)*x + 1) * x⁻¹  ):=by ext x; ring_nf
  rw[e3]; apply tendsto_log_mul_inv_x ;
  apply Tendsto.mul; apply tendsto_x_mul_inv_x
  apply tendsto_nhdsWithin_of_tendsto_nhds; apply ContinuousAt.tendsto
  apply ContinuousAt.log; apply ContinuousAt.sub; apply continuousAt_const; apply continuousAt_id;
  simp; apply Tendsto.sub;
  have e4: (fun x ↦ x⁻¹ * log (1 - x * 2 ^ (-r))) = (fun x ↦ log ((-2 ^ (-r))*x + 1) * x⁻¹  ):=by ext x; ring_nf
  rw[e4]; apply tendsto_log_mul_inv_x ;
  apply Tendsto.mul; apply tendsto_x_mul_inv_x
  apply tendsto_nhdsWithin_of_tendsto_nhds; apply ContinuousAt.tendsto
  apply ContinuousAt.log; apply ContinuousAt.sub; apply continuousAt_const;
  apply ContinuousAt.mul; apply continuousAt_id; apply continuousAt_const; simp




lemma lemma61sub : Tendsto (fun (i:ℝ)=> f (2 ^ i) r / f (2 ^ i) Δ) atBot (𝓝 (Q_hi Δ r)) := by
  unfold Q_hi;
  have : (fun (i:ℝ)=> f (2 ^ i) r / f (2 ^ i) Δ )= (fun i=>f (2 ^ i) r * (2 ^ i)⁻¹ / (f (2 ^ i) Δ * (2 ^ i)⁻¹)) := by
    ext i; field_simp
  simp only [this]; clear this
  suffices h : ∀ r, Tendsto (fun i : ℝ => f (2 ^ i) r * (2 ^ i)⁻¹) atBot (𝓝 (2 ^ (-r) + r * log 2 - 1))
  · exact Tendsto.div (h r) (h Δ) (ne_of_gt (q_hi_denom_valid delta_pos))
  · intro r
    apply Tendsto.comp tendsto_f_mul_inv_x
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact tendsto_rpow_atTop_of_base_gt_one _ one_lt_two
    · simp; use 0; intro x _
      exact ne_of_gt (rpow_pos_of_pos zero_lt_two _)



lemma lemma61 : Tendsto (fun i => Q Δ i r) atBot (𝓝 (Q_hi Δ r)) := by
  have : Tendsto (fun (i:ℝ)=> f (2 ^ i) r / f (2 ^ i) Δ) atBot (𝓝 (Q_hi Δ r)) := by apply lemma61sub ; assumption
  apply Filter.Tendsto.congr' _  this;
  have h: Set.EqOn (fun i ↦ LNS.f (2 ^ i) r / LNS.f (2 ^ i) Δ) (fun i ↦ Q Δ i r) (Set.Iic (-1:ℝ)):=by
    unfold Set.EqOn; simp; intro x hx; rw[← q_eq]; assumption; assumption
  apply Filter.eventuallyEq_of_mem _ h; apply Filter.Iic_mem_atBot;
