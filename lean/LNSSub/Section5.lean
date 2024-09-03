import LNS.Common
import LNS.Basic

namespace LNS

open Real



/- Auxiliary definitions and lemmas for the proof of the second part of Lemma 5.1 -/

private noncomputable def f (a : ℝ) := a * exp (-a) + exp (-a) - 1

private noncomputable def h a := (a + 2) * exp (-a) + (a - 2)

private lemma differentiable_f : Differentiable ℝ f :=
  let dexp := Differentiable.exp differentiable_neg
  Differentiable.sub_const (Differentiable.add (Differentiable.mul differentiable_id' dexp) dexp) _

private lemma deriv_f (a : ℝ) : deriv f a = -a * exp (-a) := by
  unfold f
  have dexp : DifferentiableAt ℝ (fun a => exp (-a)) a := by
    apply DifferentiableAt.exp
    apply differentiable_neg
  have : deriv (fun a => exp (-a)) a = -exp (-a) := by
    rw [_root_.deriv_exp, deriv_neg, mul_neg, mul_one]
    exact DifferentiableAt.neg differentiableAt_id
  rw [deriv_sub_const, deriv_add, deriv_mul, this, deriv_id'']; ring
  · exact differentiableAt_id'
  · exact dexp
  · exact DifferentiableAt.mul differentiableAt_id' dexp
  · exact dexp

private lemma f_zero : f 0 = 0 := by simp [f]

private lemma f_neg {a} (ha : a ≠ 0) : f a < 0 := by
  rw [← f_zero]
  rcases lt_or_gt_of_ne ha with h | h
  · apply Convex.strictMonoOn_of_deriv_pos (convex_Iic 0) _ _ (Set.mem_Iic_of_Iio h) Set.right_mem_Iic h
    · apply Continuous.continuousOn
      exact Differentiable.continuous differentiable_f
    · simp only [Set.nonempty_Ioi, interior_Iic', Set.mem_Iio, deriv_f]
      intro x x_neg
      exact mul_pos (neg_pos.mpr x_neg) (exp_pos _)
  · apply Convex.strictAntiOn_of_deriv_neg (convex_Ici 0) _ _ Set.left_mem_Ici (Set.mem_Ici_of_Ioi h) h
    · apply Continuous.continuousOn
      exact Differentiable.continuous differentiable_f
    · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi, deriv_f]
      intro x x_pos
      simp only [neg_mul, Left.neg_neg_iff]
      exact mul_pos x_pos (exp_pos _)

private lemma h_nonneg (ha : 0 ≤ a) : 0 ≤ h a := by
  have h0 : h 0 = 0 := by
    simp only [h, zero_add, neg_zero, exp_zero, mul_one, zero_sub, add_right_neg]
  have dh0 : Differentiable ℝ (fun a : ℝ => -a) := Differentiable.neg differentiable_id'
  have dh1 : Differentiable ℝ (fun a => exp (-a)) := Differentiable.exp dh0
  have dh2 : Differentiable ℝ (fun a : ℝ => a + 2) := by simp
  have dh3 : Differentiable ℝ (fun a => (a + 2) * exp (-a)) := Differentiable.mul dh2 dh1
  have dh4 : Differentiable ℝ (fun a : ℝ => a - 2) := by simp
  have dh : Differentiable ℝ h := Differentiable.add dh3 dh4
  rw [← h0]
  apply Convex.monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · apply Continuous.continuousOn
    exact Differentiable.continuous dh
  · exact Differentiable.differentiableOn dh
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x hx; unfold h
    rw [deriv_add (dh3 _) (dh4 _), deriv_sub_const, deriv_mul (dh2 _) (dh1 _), _root_.deriv_exp (dh0 _),
        deriv_add_const, deriv_neg, deriv_id'']
    simp only [one_mul, mul_neg, mul_one]
    calc
      exp (-x) + -((x + 2) * exp (-x)) + 1 = -(f x) := by unfold f; ring
      _ ≥ 0 := le_of_lt $ neg_pos_of_neg $ f_neg $ ne_of_gt hx
  · exact Set.left_mem_Ici
  · exact ha
  · exact ha

-- TODO: simplify




/- Lemma 5.1 -/

lemma err_bound {i r Δ} (hi : i ≤ -1) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ) : |E i r| ≤ E (-1:ℝ) Δ := by
  rw [abs_of_nonneg (err_nonneg hi hr1)]
  have := monotoneOn_E_i hr1 hi Set.right_mem_Iic hi
  apply le_trans this
  unfold Er;
  apply (monotoneOn_E_r); any_goals simp;
  any_goals linarith;

/- Theorem 5.3 -/

variable (rnd : ℝ → ℝ)

variable (ε  : ℝ)

variable (hrnd : ∀ x , |x - rnd x| ≤ ε)

noncomputable def Efix (i r : ℝ) :=  Φ (i - r) -rnd (Φ i) + rnd (r * rnd (deriv Φ i) )

lemma Theorem53 {i r Δ :ℝ} (hi : i ≤ -1) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ) :
    |Efix rnd i r| ≤ (E (-1:ℝ) Δ) + (2+Δ)*ε :=by
  set s1 := (Φ i -  rnd (Φ i))
  set s2 := r*(rnd (deriv Φ i) - deriv Φ i)
  set s3 := (rnd (r * rnd (deriv Φ i)) - r * rnd (deriv Φ i))
  have e1: Efix rnd i r = (-E i r) + s1 + s2 + s3 := by unfold Efix E; ring_nf
  have i1: |s1| ≤ ε := by apply hrnd
  have i3: |s3| ≤ ε := by
    have : |s3| = |r * rnd (deriv Φ i) - rnd (r * rnd (deriv Φ i))| :=by apply abs_sub_comm;
    rw[this]
    apply hrnd
  have i2: |s2| ≤ Δ*ε :=by
    have e1: |s2| = |r| * |(rnd (deriv Φ i) - deriv Φ i)| :=by apply abs_mul
    have e2: |(rnd (deriv Φ i) - deriv Φ i)| = |(deriv Φ i) - rnd (deriv Φ i)|:= by apply abs_sub_comm;
    have e3: |r| = r :=by apply abs_of_nonneg; linarith
    rw[e1,e2,e3]
    have i21: |deriv Φ i - rnd (deriv Φ i)| ≤ ε := by apply hrnd
    apply mul_le_mul hr2 i21; simp; linarith
  have i0:  |Efix rnd i r| ≤ |E i r| + |s1| + |s2| + |s3| :=by
    have i01 : |Efix rnd i r| ≤ |-E i r + s1 + s2| + |s3|:=by rw[e1]; apply abs_add
    have i02 :  |-E i r + s1 + s2|  ≤    |-E i r + s1| + |s2|:=by  apply abs_add
    have i03: |-E i r + s1|  ≤ |-E i r| + |s1| :=by  apply abs_add
    have i04: |-E i r| =|E i r|:=by apply abs_neg
    linarith
  have i01: |E i r|≤ E (-1:ℝ) Δ :=by exact err_bound hi hr1 hr2
  linarith



end LNS
