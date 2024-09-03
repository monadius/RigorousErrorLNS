import LNS.Common
import LNS.Basic

noncomputable section

namespace LNS

open Real Filter Topology

def Φm (x : ℝ) := logb 2 (1 - (2 : ℝ) ^ x)

lemma denpos (hx: x ≤ (-1:ℝ)) : 1 - (2 : ℝ) ^ x > 0 :=by
  have i1: (2:ℝ)^x <= (2:ℝ)^(-1:ℝ) :=by apply monotone_rpow_of_base_ge_one; linarith; assumption
  have h1: 0 < (2:ℝ):=by simp;
  have e1: (2:ℝ)^(-1:ℝ) < 1 :=by
    apply (Real.rpow_lt_one_iff_of_pos h1).mpr;
    apply Or.intro_left; apply And.intro; linarith; linarith;
  linarith

lemma differentiable_Φm0 : DifferentiableOn ℝ Φm (Set.Iio (0:ℝ)):= by
  unfold Φm
  unfold logb
  apply DifferentiableOn.div;
  apply DifferentiableOn.log; apply DifferentiableOn.const_sub; apply DifferentiableOn.rpow;
  apply differentiableOn_const; apply differentiableOn_id;
  simp; simp; intro x hx;
  have i1: (2 : ℝ) ^ x < 1 := by apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith
  linarith
  apply differentiableOn_const; simp; intro x  _;  linarith


lemma differentiable_Φm : DifferentiableOn ℝ Φm (Set.Iic (-1:ℝ)):= by
  unfold Φm
  unfold logb
  apply DifferentiableOn.div;
  apply DifferentiableOn.log; apply DifferentiableOn.const_sub; apply DifferentiableOn.rpow;
  apply differentiableOn_const; apply differentiableOn_id;
  simp; simp; intro x hx;
  have i1: 1 - (2 : ℝ) ^ x > 0 := denpos hx
  linarith
  apply differentiableOn_const; simp; intro x  _;  linarith



def dphim  (x:ℝ) :=  -(2 : ℝ) ^ x / (1 - (2 : ℝ) ^ x)

lemma differentiable_dphim : DifferentiableOn ℝ dphim (Set.Iic (-1:ℝ)):= by
  unfold dphim
  apply DifferentiableOn.div;
  simp; apply DifferentiableOn.rpow;
  apply differentiableOn_const; apply differentiableOn_id;
  simp
  apply DifferentiableOn.const_sub; apply DifferentiableOn.rpow;
  apply differentiableOn_const; apply differentiableOn_id;
  simp
  intro x hx;
  have i1: 1 - (2 : ℝ) ^ x > 0 := denpos hx
  linarith



lemma deriv_phim (hx: x ≤ -1): deriv Φm x = dphim x := by
  unfold Φm logb dphim
  simp
  have i1: 1 - (2 : ℝ) ^ x > 0 := denpos hx
  rw [deriv.log, deriv_const_sub, deriv_two_pow]
  field_simp; ring_nf
  apply DifferentiableAt.const_sub
  apply DifferentiableAt.rpow _ differentiableAt_id' <;> simp
  linarith

def d2phim  (x:ℝ) :=  -((2 : ℝ) ^ x * log 2) / (1 - (2 : ℝ) ^ x)^2

lemma deriv2_phim (hx: x ≤ -1): deriv dphim x = d2phim x := by
  unfold dphim d2phim
  have i1: 1 - (2 : ℝ) ^ x > 0 := denpos hx
  rw [deriv_div, deriv_sub, deriv_two_pow]; simp;
  rw [deriv_two_pow];
  field_simp; ring_nf
  simp;
  apply DifferentiableAt.rpow _ differentiableAt_id' <;> simp
  simp;
  apply DifferentiableAt.rpow _ differentiableAt_id' <;> simp
  apply DifferentiableAt.const_sub
  apply DifferentiableAt.rpow _ differentiableAt_id' <;> simp
  linarith;

def F x t :=  Φm (x-t)  -  Φm x

def Fx t x := F x t

lemma dphimanti (hx: x ≤ (-1:ℝ)) (ht0: 0 ≤ t): dphim (x-t) ≥  dphim x :=by
  apply antitoneOn_of_deriv_nonpos (convex_Iic (-1:ℝ))
  apply DifferentiableOn.continuousOn differentiable_dphim
  apply DifferentiableOn.mono differentiable_dphim ; simp
  simp; intro x hx;
  rw[deriv2_phim]; unfold d2phim;
  have i1: 1 - (2 : ℝ) ^ x > 0 := by apply denpos; linarith
  have i2: (2 ^ x * log 2) / (1 - 2 ^ x) ^ 2 ≥ 0 :=by
    apply div_nonneg;
    apply mul_nonneg;
    apply le_of_lt; apply rpow_pos_of_pos; simp;
    apply le_of_lt;  apply log_pos ; linarith
    apply pow_nonneg;
    linarith
  have : -(2 ^ x * log 2) / (1 - 2 ^ x) ^ 2 = -(2 ^ x * log 2 / (1 - 2 ^ x) ^ 2) := by ring_nf
  linarith; linarith
  simp; linarith;
  simp; linarith;
  linarith

lemma dphim_neg (hx: x ≤ (-1:ℝ)) : dphim x ≤ 0 :=by
  unfold dphim
  have i1: 1 - (2 : ℝ) ^ x > 0 := by apply denpos; linarith
  have i3: (2:ℝ)^x/(1 - 2^x) >0 :=by apply div_pos; apply rpow_pos_of_pos; linarith; assumption
  have : -2 ^ x / (1 - 2 ^ x) = -((2:ℝ)^x/(1-2^x)) :=by ring_nf;
  linarith


lemma differentiable_Fx (ht0: 0 ≤ t) : DifferentiableOn ℝ (Fx t) (Set.Iic (-1:ℝ)):= by
  unfold Fx  F;
  apply DifferentiableOn.sub;
  intro x; simp; intro hx;
  apply DifferentiableAt.differentiableWithinAt
  have : (fun y ↦ Φm (y - t)) = Φm ∘ (fun y ↦ (y - t)) := by ext x; simp
  rw[this]
  apply DifferentiableAt.comp; apply DifferentiableOn.differentiableAt differentiable_Φm0;
  apply Iio_mem_nhds; linarith
  apply DifferentiableAt.sub_const;
  simp; exact differentiable_Φm




lemma main (hx: x ≤ (-1:ℝ)) (ht0: 0 ≤ t) (htp: t ≤ m): F x t ≤ F (-1) m :=by
  have i1: 1 - (2 : ℝ) ^ x > 0 := denpos hx
  have sub1  :  F x t ≤ F (-1) t :=by
    rw[← Fx, ← Fx]
    apply monotoneOn_of_deriv_nonneg (convex_Iic (-1:ℝ))
    apply DifferentiableOn.continuousOn (differentiable_Fx ht0)
    apply DifferentiableOn.mono (differentiable_Fx ht0) ; simp
    simp; intro x hx;
    unfold Fx F;
    rw[deriv_sub, deriv_phim]
    have : (fun y ↦ Φm (y - t)) = Φm ∘ (fun y ↦ (y - t)) := by ext x; simp
    rw[this]
    rw[deriv.comp, deriv_phim]; simp;
    apply dphimanti; linarith; assumption;
    linarith;
    apply DifferentiableOn.differentiableAt differentiable_Φm
    apply Iic_mem_nhds; linarith
    apply DifferentiableAt.sub_const; simp;
    linarith
    have : (fun y ↦ Φm (y - t)) = Φm ∘ (fun y ↦ (y - t)) := by ext x; simp
    rw[this]
    apply DifferentiableAt.comp; apply DifferentiableOn.differentiableAt differentiable_Φm0;
    apply Iio_mem_nhds; linarith
    apply DifferentiableAt.sub_const; simp; apply DifferentiableOn.differentiableAt differentiable_Φm0;
    apply Iio_mem_nhds; linarith
    simp; linarith; simp; assumption

  have diffF : DifferentiableOn ℝ (F (-1)) (Set.Ici 0) :=by
    unfold F;
    apply DifferentiableOn.sub;
    intro x; simp; intro hx;
    apply DifferentiableAt.differentiableWithinAt
    have : (fun y ↦ Φm (-1-y)) = Φm ∘ (fun y ↦ (-1 - y)) := by ext x; simp
    rw[this]
    apply DifferentiableAt.comp; apply DifferentiableOn.differentiableAt differentiable_Φm0;
    apply Iio_mem_nhds; linarith
    apply DifferentiableAt.const_sub
    simp;
    apply differentiableOn_const;


  have sub3  :  F (-1) t ≤ F (-1) m :=by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    apply DifferentiableOn.continuousOn diffF
    apply DifferentiableOn.mono diffF; simp;
    simp; intro x hx;
    unfold F;
    rw[deriv_sub]; simp;
    have : (fun y ↦ Φm (-1-y)) = Φm ∘ (fun y ↦ (-1 - y)) := by ext x; simp
    rw[this,deriv.comp, deriv_phim, deriv_sub]; simp;
    apply dphim_neg; linarith;
    simp; simp; linarith;
    apply DifferentiableOn.differentiableAt differentiable_Φm0;
    apply Iio_mem_nhds; linarith
    apply DifferentiableAt.const_sub; simp;
    have : (fun y ↦ Φm (-1-y)) = Φm ∘ (fun y ↦ (-1 - y)) := by ext x; simp
    rw[this]
    apply DifferentiableAt.comp; apply DifferentiableOn.differentiableAt differentiable_Φm0;
    apply Iio_mem_nhds; linarith
    apply DifferentiableAt.const_sub; simp;
    apply differentiableAt_const;
    simp; assumption; simp; linarith;assumption
  linarith
