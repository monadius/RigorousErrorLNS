import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

-- TODO: generalize, simplify and add to Mathlib

lemma DifferentiableAt.comp_linear {a b x : ℝ} {f : ℝ → ℝ} (ha : a ≠ 0) :
    DifferentiableAt ℝ (fun x => f (a * x + b)) x ↔ DifferentiableAt ℝ f (a * x + b) := by
  constructor <;> intro df
  · have : f = (fun x => f (a * x + b)) ∘ (fun x => (x - b) / a) := by
      ext y; congr; field_simp; ring
    rw [this]
    apply DifferentiableAt.comp
    · rw [add_sub_cancel, mul_div_cancel_left _ ha]
      exact df
    · simp only [differentiableAt_id', differentiableAt_const, sub, div_const]
  · rw [← Function.comp]
    apply DifferentiableAt.comp
    · exact df
    · simp only [differentiableAt_add_const_iff]
      exact DifferentiableAt.const_mul differentiableAt_id' _

lemma deriv_comp_linear {a b x : ℝ} {f : ℝ → ℝ} :
    deriv (fun x => f (a * x + b)) x = a * deriv f (a * x + b) := by
  by_cases ha : a = 0; simp [ha]
  by_cases df : DifferentiableAt ℝ f (a * x + b)
  · rw [← Function.comp, deriv.comp, deriv_add_const, deriv_const_mul, deriv_id'', mul_comm, mul_one]
    · exact differentiableAt_id'
    · exact df
    · apply DifferentiableAt.add_const
      exact DifferentiableAt.const_mul differentiableAt_id' _
  · rw [deriv_zero_of_not_differentiableAt df, deriv_zero_of_not_differentiableAt, mul_zero]
    rw [DifferentiableAt.comp_linear ha]
    exact df

lemma DifferentiableAt.comp_const_sub {a x : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun x => f (a - x)) x ↔ DifferentiableAt ℝ f (a - x) := by
  have : ∀ x, a - x = (-1) * x + a := by intro; ring
  simp only [this, DifferentiableAt.comp_linear (by norm_num : -1 ≠ (0 : ℝ))]

lemma deriv_comp_const_sub {a x : ℝ} {f : ℝ → ℝ} :
    deriv (fun x => f (a - x)) x = -(deriv f (a - x)) := by
  have : ∀ x, a - x = (-1) * x + a := by intro; ring
  simp only [this, deriv_comp_linear]
  rw [neg_one_mul]

lemma DifferentiableAt.comp_sub_const {a x : ℝ} {f : ℝ → ℝ} :
    DifferentiableAt ℝ (fun x => f (x - a)) x ↔ DifferentiableAt ℝ f (x - a) := by
  have : ∀ x, x - a = 1 * x + -a := by intro; ring
  simp only [this, DifferentiableAt.comp_linear (by norm_num : 1 ≠ (0 : ℝ))]

lemma deriv_comp_sub_const {a x : ℝ} {f : ℝ → ℝ} :
    deriv (fun x => f (x - a)) x = deriv f (x - a) := by
  have : ∀ x, x - a = 1 * x + -a := by intro; ring
  simp only [this, deriv_comp_linear]
  rw [one_mul]
