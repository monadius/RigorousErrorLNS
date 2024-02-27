import LNS.Common
import LNS.Basic

noncomputable section

namespace LNS

open Real Filter Topology


lemma deriv_ei_pos (hr : r>0) : 0 < deriv (E i) r :=by
    unfold E
    rw [deriv_add]
    · rw [deriv_mul_const (by simp : _), deriv_sub_const, deriv_id'', deriv_comp_const_sub, one_mul]
      simp only [deriv_phi, lt_neg_add_iff_add_lt, add_zero]
      rw [div_lt_div_iff (one_plus_two_pow_pos _) (one_plus_two_pow_pos _)]
      rw [← lt_neg_add_iff_lt]; ring_nf
      rw [lt_neg_add_iff_lt]
      apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num : _)
      linarith
    · apply DifferentiableAt.sub_const
      apply DifferentiableAt.comp_const_sub.mpr
      apply differentiable_phi
    · simp

lemma strictMonoOn_E_r (i:ℝ) : StrictMonoOn (E i) (Set.Ici 0) := by
  have diffE : Differentiable ℝ (E i) := by
    apply Differentiable.add _ (by simp : _)
    apply Differentiable.sub_const
    intro x
    apply DifferentiableAt.comp_const_sub.mpr
    apply differentiable_phi
  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
  · apply Continuous.continuousOn
    exact Differentiable.continuous diffE
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x hx
    apply deriv_ei_pos; assumption


lemma err_pos  (hr : 0 < r) : 0 < E i r := by
  rw [(by simp [E] : 0 = E i 0)]
  apply (strictMonoOn_E_r i) Set.left_mem_Ici;
  simp; linarith; assumption

def dE (i:ℝ) (r:ℝ) := ((2:ℝ)^i)/(2^i +1) - (2^(i-r))/(2^(i-r)+1)

lemma deriv_er :  deriv (E i) r = dE i r  :=by
  unfold dE
  unfold E
  rw[deriv_add, deriv_sub, deriv_mul]; simp;
  rw[deriv_phi, deriv_comp_const_sub, deriv_phi]; simp;
  have i1: (2:ℝ)^i > 0 := by apply rpow_pos_of_pos; linarith
  have i2: (2:ℝ)^(i-r) > 0 := by apply rpow_pos_of_pos; linarith
  have i3: (2:ℝ)^i + 1 ≠ 0 := by linarith
  have i3: (2:ℝ)^(i-r) + 1 ≠ 0 := by linarith
  field_simp; ring_nf;
  simp;simp; apply DifferentiableAt.comp_const_sub.mpr;
  apply differentiable_phi; simp;
  apply DifferentiableAt.sub_const; apply DifferentiableAt.comp_const_sub.mpr;
  apply differentiable_phi; simp;



lemma deriv_de :  deriv (dE i) r = (2^(i-r)*log 2)/(2^(i-r)+1)^2 := by
  have i1: (2:ℝ)^i > 0 := by apply rpow_pos_of_pos; linarith
  have i2: (2:ℝ)^(i-r) > 0 := by apply rpow_pos_of_pos; linarith
  unfold dE
  rw[deriv_sub];simp; rw[deriv_div]; simp; rw[deriv_comp_const_sub, deriv_two_pow];
  field_simp; ring_nf;
  apply DifferentiableAt.rpow; simp; apply DifferentiableAt.const_sub;simp;
  any_goals linarith;
  apply DifferentiableAt.add; apply DifferentiableAt.rpow; simp; apply DifferentiableAt.const_sub;simp;
  linarith; simp; apply DifferentiableAt.div; apply differentiableAt_const; apply differentiableAt_const;
  linarith;
  apply DifferentiableAt.div; apply DifferentiableAt.rpow; simp; apply DifferentiableAt.const_sub; simp;
  any_goals linarith;
  apply DifferentiableAt.add; apply DifferentiableAt.rpow; simp; apply DifferentiableAt.const_sub;simp;
  linarith; simp;



lemma strictMonoOn_derivE (i:ℝ) : StrictMonoOn (dE i) (Set.Ici 0) := by

  have diffE : Differentiable ℝ (dE i) := by
    unfold dE;
    apply Differentiable.sub; simp;
    apply Differentiable.div;
    any_goals apply Differentiable.add;
    any_goals apply Differentiable.rpow;
    any_goals apply Differentiable.const_sub;
    any_goals simp;
    intro x;
    have i2: (2:ℝ)^(i-x) > 0 := by apply rpow_pos_of_pos; linarith
    linarith

  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
  · apply Continuous.continuousOn
    exact Differentiable.continuous diffE
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x hx
    rw[deriv_de];
    apply div_pos; apply mul_pos; apply rpow_pos_of_pos;
    linarith; apply log_pos; linarith;
    apply pow_pos;
    have i2: (2:ℝ)^(i-x) > 0 := by apply rpow_pos_of_pos; linarith
    linarith



def F c Δ r t := (E c r - E c (r-t)) / (E c Δ)

def Ft c Δ t r := F c Δ r t

lemma monoF (h1: r ≥ ΔP) (hr: r > 0) (ht0: 0 ≤ t) (htp: t ≤ ΔP)
       (htr: t ≤ r)  (htd: r ≤ Δ) : (F c Δ) r t ≤  (F c Δ) r ΔP := by
  have diffE : Differentiable ℝ (E c) := by
    apply Differentiable.add _ (by simp : _)
    apply Differentiable.sub_const
    intro x
    apply DifferentiableAt.comp_const_sub.mpr
    apply differentiable_phi
  have ep : E c Δ > 0 := by apply err_pos; linarith
  have ec : (fun y ↦ E c (r - y)) = (fun y=> E c y) ∘ (fun y=>r-y) :=by ext y; simp;
  have ec2 : (fun y ↦ E c (y - t)) = (fun y=> E c y) ∘ (fun y=>y-t) :=by ext y; simp;
  have diffF : DifferentiableOn ℝ (F c Δ r) (Set.Icc 0 r) := by
    unfold F
    apply DifferentiableOn.div; apply DifferentiableOn.sub; apply differentiableOn_const;
    apply Differentiable.differentiableOn
    rw[ec]
    apply Differentiable.comp; assumption;
    apply Differentiable.sub; simp; simp;
    apply differentiableOn_const;
    intro x hx
    linarith
  have monoF : MonotoneOn (F c Δ r) (Set.Icc 0 r) := by
    apply Convex.monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    apply DifferentiableOn.continuousOn diffF
    apply DifferentiableOn.mono diffF; simp;
    apply Set.Ioo_subset_Icc_self
    simp;
    intro x hx1 hx2; unfold F
    rw[deriv_div, deriv_sub]; simp; rw[ec, deriv.comp, deriv_sub]; simp;
    apply div_nonneg; apply mul_nonneg; apply le_of_lt;
    apply deriv_ei_pos; linarith;
    linarith; apply pow_nonneg; linarith;
    simp;simp
    apply Differentiable.differentiableAt diffE;
    apply DifferentiableAt.sub; simp;simp;simp;
    rw[ec];apply DifferentiableAt.comp;
    apply Differentiable.differentiableAt diffE;
    apply DifferentiableAt.sub; simp;simp;
    apply DifferentiableAt.sub; simp;
    rw[ec];apply DifferentiableAt.comp;
    apply Differentiable.differentiableAt diffE;
    apply DifferentiableAt.sub; simp;simp;simp; linarith

  have first : (F c Δ) r t ≤  (F c Δ) r ΔP := by
    apply monoF
    any_goals simp;
    any_goals apply And.intro;
    any_goals linarith;
  assumption


lemma main (hr: r>0) (ht0: 0 ≤ t) (htp: t ≤ ΔP) (htr: t ≤ r)
            (htd: r ≤ Δ) (hΔ:  ΔP ≤ Δ ): (F c Δ) r t ≤  (F c Δ) Δ ΔP:= by
  have diffE : Differentiable ℝ (E c) := by
    apply Differentiable.add _ (by simp : _)
    apply Differentiable.sub_const
    intro x
    apply DifferentiableAt.comp_const_sub.mpr
    apply differentiable_phi
  have ep : E c Δ > 0 := by apply err_pos; linarith
  have ec : (fun y ↦ E c (r - y)) = (fun y=> E c y) ∘ (fun y=>r-y) :=by ext y; simp;
  have ec2 : (fun y ↦ E c (y - t)) = (fun y=> E c y) ∘ (fun y=>y-t) :=by ext y; simp;
  have diffF : DifferentiableOn ℝ (F c Δ r) (Set.Icc 0 r) := by
    unfold F
    apply DifferentiableOn.div; apply DifferentiableOn.sub; apply differentiableOn_const;
    apply Differentiable.differentiableOn
    rw[ec]
    apply Differentiable.comp; assumption;
    apply Differentiable.sub; simp; simp;
    apply differentiableOn_const;
    intro x hx
    linarith


  have diffFt: DifferentiableOn ℝ  (Ft c Δ t)  (Set.Ici t) :=by
    unfold Ft
    unfold F
    apply DifferentiableOn.div; apply DifferentiableOn.sub;
    apply Differentiable.differentiableOn diffE;
    rw[ec2]
    apply Differentiable.differentiableOn
    apply Differentiable.comp; assumption;
    apply Differentiable.sub_const; simp;
    apply differentiableOn_const;
    intro x hx; linarith

  have diffdE: DifferentiableOn ℝ   (dE c) (Set.Ici 0) := by
    unfold dE
    apply DifferentiableOn.sub;
    apply differentiableOn_const;
    apply DifferentiableOn.div; apply DifferentiableOn.rpow;
    apply differentiableOn_const; apply DifferentiableOn.const_sub; apply differentiableOn_id;
    simp; apply DifferentiableOn.add_const; apply DifferentiableOn.rpow;
    apply differentiableOn_const; apply DifferentiableOn.const_sub; apply differentiableOn_id;simp;
    intro x hx;
    have i2: (2:ℝ)^(c-x) > 0 := by apply rpow_pos_of_pos; linarith
    linarith


  have first : (F c Δ) r t ≤ (F c Δ) Δ t :=by
    rw[← Ft, ← Ft]
    apply Convex.monotoneOn_of_deriv_nonneg (convex_Ici t)
    apply DifferentiableOn.continuousOn diffFt
    apply DifferentiableOn.mono diffFt; simp;
    simp; intro x hx
    unfold Ft
    unfold F
    rw[deriv_div, deriv_sub]; simp;
    apply div_nonneg; apply mul_nonneg
    rw[deriv_er, ec2, deriv.comp, deriv_er]; simp;
    apply Convex.monotoneOn_of_deriv_nonneg (convex_Ici 0)
    apply DifferentiableOn.continuousOn diffdE
    apply DifferentiableOn.mono diffdE; simp;
    simp; intro x hx;
    rw[deriv_de];
    apply div_nonneg;
    apply mul_nonneg;
    have i2: (2:ℝ)^(c-x) > 0 := by apply rpow_pos_of_pos; linarith
    linarith;
    apply log_nonneg
    any_goals simp;
    any_goals linarith;
    apply pow_nonneg;
    have i2: (2:ℝ)^(c-x) > 0 := by apply rpow_pos_of_pos; linarith
    linarith;
    apply Differentiable.differentiableAt diffE;
    apply pow_nonneg; linarith;
    apply Differentiable.differentiableAt diffE;
    rw[ec2];apply DifferentiableAt.comp;
    apply Differentiable.differentiableAt diffE;
    apply DifferentiableAt.sub; simp;simp;
    apply DifferentiableAt.sub;apply Differentiable.differentiableAt diffE;
    rw[ec2];apply DifferentiableAt.comp;
    apply Differentiable.differentiableAt diffE;
    apply DifferentiableAt.sub; simp;simp;

  have second : (F c Δ) Δ t ≤ (F c Δ) Δ ΔP := by
    apply monoF;
    any_goals linarith;
  linarith
