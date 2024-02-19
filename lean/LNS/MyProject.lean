import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Order.Module.OrderedSMul
import Mathlib.Analysis.Convex.Star
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace


open Real
noncomputable def Φ (x : ℝ) := logb 2 (1 + (2 : ℝ) ^ x)

lemma hasDerivAt_two_pow (x : ℝ) : HasDerivAt (fun x => (2 : ℝ) ^ x) ((2 : ℝ) ^ x * log 2) x := by
  rw [(by ring : (2 : ℝ) ^ x * log 2 = 0 * x * (2 : ℝ) ^ (x - 1) + 1 * (2 : ℝ) ^ x * log 2)]
  exact HasDerivAt.rpow (hasDerivAt_const x 2) (hasDerivAt_id' x) two_pos

lemma deriv_two_pow (x : ℝ) : deriv (fun x => (2 : ℝ) ^ x) x = (2 : ℝ) ^ x * log 2 :=
  HasDerivAt.deriv (hasDerivAt_two_pow x)

lemma deriv_phi : deriv Φ = fun (x : ℝ) => (2 : ℝ) ^ x / (1 + (2 : ℝ) ^ x) := by
  unfold Φ logb
  ext x; simp
  rw [deriv.log, deriv_const_add, deriv_two_pow]
  . field_simp; ring
  · apply DifferentiableAt.const_add
    apply DifferentiableAt.rpow _ differentiableAt_id'
    simp
    simp
  linarith [rpow_pos_of_pos two_pos x]


noncomputable def phipow (x : ℝ) := x/(1+x)
noncomputable def pow2 (x : ℝ) := (2 : ℝ) ^ x

lemma deriv_pow2 (x : ℝ) : deriv pow2 x = (2 : ℝ) ^ x * log 2 :=
  HasDerivAt.deriv (hasDerivAt_two_pow x)

lemma phipowsub : deriv Φ   = (phipow ∘ pow2)   := by
  have h: deriv Φ = fun (x : ℝ) => (2 : ℝ) ^ x / (1 + (2 : ℝ) ^ x) := by apply deriv_phi
  unfold phipow
  unfold pow2
  funext
  simp
  rw [h]

lemma deriv_phipow (hx: x>0): deriv phipow x =  1 / ((1+x) ^ 2) := by
  have de1: deriv (fun x => 1 + x) x = (1 : ℝ) := by rw [deriv_add]; repeat simp;
  have hx1: 1 + x ≠ 0 := by linarith[hx]
  unfold phipow
  rw [deriv_div]
  . simp; rw [de1]; simp;
  . simp;
  apply DifferentiableAt.const_add
  simp
  assumption

lemma deriv_phi2 : deriv (deriv Φ) x = (2 : ℝ) ^ x * log 2 / (1 + (2 : ℝ) ^ x) ^ 2 := by
  rw [phipowsub]
  rw [deriv.comp]
  unfold pow2
  rw [deriv_two_pow]
  have hp: (2 : ℝ) ^ x >0 := by linarith [rpow_pos_of_pos two_pos x]
  rw [deriv_phipow hp]
  ring
  apply DifferentiableAt.div
  unfold pow2
  simp
  apply DifferentiableAt.const_add
  simp
  unfold pow2
  have hp2: 1+ (2 : ℝ) ^ x ≠ 0  := by linarith [rpow_pos_of_pos two_pos x]
  assumption
  unfold pow2
  apply DifferentiableAt.rpow
  repeat simp



noncomputable def phipow2 (x : ℝ) := log 2 * x/(1+x)^2

lemma phipowsub2 : deriv (deriv Φ)   = (phipow2 ∘ pow2)   := by
  funext
  rw [deriv_phi2]
  unfold phipow2
  unfold pow2
  simp
  ring

noncomputable def sq1 (x : ℝ) := (1+x)^2

lemma ht (x:ℝ): deriv sq1 x = 2 * (x + 1):= by
  have ht1: sq1  = fun x => x^2 + 2*x +1 := by unfold sq1; funext; ring;
  rw [ht1]
  rw[deriv_add, deriv_add, deriv_pow, deriv_const_mul]; simp; ring; repeat simp;
  apply DifferentiableAt.const_mul; simp; apply DifferentiableAt.add
  apply DifferentiableAt.pow; simp; apply DifferentiableAt.const_mul; simp; simp;

lemma sq1dev (x:ℝ): deriv (fun (x:ℝ) => (1+x)^2) x = 2 * (x + 1):= by
  have ht1: (fun (x:ℝ) => (1+x)^2 )  = fun x => x^2 + 2*x +1  := by funext; ring;
  rw [ht1]
  rw[deriv_add, deriv_add, deriv_pow, deriv_const_mul]; simp; ring; repeat simp;
  apply DifferentiableAt.const_mul; simp; apply DifferentiableAt.add
  apply DifferentiableAt.pow; simp; apply DifferentiableAt.const_mul; simp; simp;

lemma deriv_phipow2 (hx: x>0): deriv phipow2 x =  log 2 * (1-x) / ((1+x) ^ 3) := by
  unfold phipow2
  rw [deriv_div]
  rw [deriv_const_mul]
  simp
  rw[sq1dev]
  have ht2: log 2 * (1 + x) ^ 2 - log 2 * x * (2 * (x + 1)) = log 2 * ((1 + x) ^ 2 - x * (2 * (x + 1))):= by
    ring
  have ht3: (1 + x) ^ 2 - x * (2 * (x + 1)) = (1-x)*(x+1) :=by ring;
  rw[ht2]
  rw[ht3]
  have ht4: ((1 + x) ^ 2) ^ 2 = (1 + x) ^ 4 := by ring;
  rw[ht4]
  have ht5: log 2 * ((1 - x) * (x + 1)) = (1 + x) * log 2 * (1 - x)  := by ring;
  rw[ht5]
  field_simp;
  ring
  simp; apply DifferentiableAt.const_mul; simp; apply DifferentiableAt.pow;
  apply DifferentiableAt.const_add; simp;
  simp; linarith;




lemma deriv3_phi_nonneg  (x:ℝ) (hx: x <= 0 ): deriv (deriv (deriv Φ)) x >= 0 := by
  rw [phipowsub2]
  rw [deriv.comp]
  rw [deriv_pow2]
  rw [deriv_phipow2]
  have ht00: (1 : ℝ)<=(2 : ℝ) := by linarith
  have ht0: (2 : ℝ)^x  <= (2 : ℝ)^(0: ℝ)  := rpow_le_rpow_of_exponent_le ht00 hx
  have ht1: (2 : ℝ)^(0: ℝ) = (1 : ℝ) := by simp
  have ht2: (1 : ℝ) - (2 : ℝ)^x >= 0 := by rw[← ht1]; linarith [ht0,  ht1]
  unfold pow2
  simp
  apply mul_nonneg
  apply mul_nonneg; apply mul_nonneg; apply log_nonneg; linarith;
  exact ht2;
  simp; apply inv_nonneg_of_nonneg; apply pow_nonneg; linarith[rpow_pos_of_pos two_pos x];
  apply mul_nonneg; linarith[rpow_pos_of_pos two_pos x]; apply log_nonneg; linarith;
  unfold pow2
  linarith[rpow_pos_of_pos two_pos x]
  unfold pow2
  unfold phipow2
  apply DifferentiableAt.div; apply DifferentiableAt.mul; simp; simp;
  apply DifferentiableAt.pow; apply DifferentiableAt.const_add; simp;
  simp; linarith[rpow_pos_of_pos two_pos x];
  unfold pow2
  apply DifferentiableAt.rpow;
  simp; simp; linarith

noncomputable def taylor_appx_err (f: ℝ → ℝ) (r: ℝ) (x: ℝ) :=  f (x-r) - f (x) + r * (deriv f) x

/-set_option maxRecDepth  5000;-/
lemma pos_taylor_deriv_r (f: ℝ → ℝ)
(r: ℝ)
(hr: r>0)
(hc1 : Continuous (deriv f))
(hf1: Differentiable ℝ f)
(hf2: Differentiable ℝ (deriv f))
(hd1: ∀ x, deriv f x >= 0)
(hd2: ∀ x, deriv (deriv f) x > 0)
  : StrictMonoOn (fun r => taylor_appx_err f r x) (Set.Ici (0:ℝ)) := by
  have hc: Continuous f :=  Differentiable.continuous hf1
  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici (0:ℝ))
  unfold taylor_appx_err
  apply Continuous.continuousOn; apply Continuous.add; apply Continuous.sub;
  apply Continuous.comp; assumption; apply Continuous.sub; exact continuous_const; exact continuous_id;
  exact continuous_const; apply Continuous.mul;  exact continuous_id; exact continuous_const;
  intro x1 hx1
  unfold taylor_appx_err
  rw [deriv_add, deriv_sub, deriv_mul]; simp;
  have ht1: deriv (fun r => f (x - r) ) x1 = - deriv f (x-x1) := by
    have ht11: (fun r=> f (x-r))  = (f ∘ (fun r=>x-r))  := by funext; simp
    rw[ht11]
    rw[deriv.comp];
    rw[deriv_sub]; simp;
    exact differentiableAt_const x;
    exact differentiableAt_id; apply hf1; apply DifferentiableAt.add;
    exact differentiableAt_const x; apply DifferentiableAt.neg; exact differentiableAt_id;
  rw[ht1]
  have monoderiv : StrictMono  (deriv f) := by
    apply strictMono_of_deriv_pos; assumption;
  have k :interior (Set.Ici (0:ℝ)) = (Set.Ioi (0:ℝ)) := by rw[interior_Ici]
  have hx11: x1 ∈ (Set.Ioi (0:ℝ)) := by rw[← k]; assumption;
  have ht2: x1>0 := Set.mem_Ioi.mp hx11
  have ht3: (x-x1)<x := by linarith[ht2]
  linarith [StrictMono.imp monoderiv ht3]

  apply Differentiable.differentiableAt; apply differentiable_id; apply differentiable_const (deriv f x)
  apply Differentiable.differentiableAt; apply Differentiable.comp; assumption;
  apply Differentiable.sub; apply differentiable_const x; apply differentiable_id; apply differentiable_const;
  apply Differentiable.sub; apply Differentiable.comp; assumption;
  apply Differentiable.sub; apply differentiable_const x; apply differentiable_id;
  apply differentiable_const (f x); apply Differentiable.mul; apply differentiable_id;
  apply differentiable_const (deriv f x);



lemma pos_taylor_deriv_x (f: ℝ → ℝ)
(r: ℝ)
(hr: r>0)
(hc : Continuous f )
(hc11 : Continuous (deriv f))
(hc2 : Continuous (deriv (deriv f)))
(hc3 : Continuous (deriv (deriv (deriv f))))
(hf1: Differentiable ℝ f)
(hf2: Differentiable ℝ (deriv f))
(hf3: Differentiable ℝ (deriv (deriv f)))
(hd1: ∀ x, deriv f x >= 0)
(hd2: ∀ x, deriv (deriv f) x >= 0)
(hd3: ∀ x, deriv (deriv (deriv f)) x >=0)
 : Monotone (taylor_appx_err f r)  := by
  have hc1: Continuous (deriv f) :=  Differentiable.continuous hf2
  apply monotone_of_deriv_nonneg
  unfold taylor_appx_err
  apply Differentiable.add
  apply Differentiable.sub
  apply Differentiable.comp
  exact hf1;
  apply Differentiable.sub
  exact differentiable_id
  exact differentiable_const r
  exact hf1
  apply Differentiable.mul
  exact differentiable_const r
  exact hf2
  intro x
  unfold taylor_appx_err
  rw [deriv_add, deriv_sub]; simp
  have ht1: deriv (fun x=> f (x-r) ) x = deriv f (x-r) := by
    have ht11: (fun x=> f (x-r))  = (f ∘ (fun x=>x-r))  := by funext; simp
    rw[ht11]
    rw[deriv.comp]
    rw[deriv_sub]
    rw[deriv_const]; simp;
    exact differentiableAt_id; exact differentiableAt_const r;
    apply hf1
    apply Differentiable.sub; exact differentiable_id; exact differentiable_const r
  rw[ht1]
  have ht2: deriv (fun x=> f x ) x = deriv f x := by simp
  rw[ht2]
  have ht3: deriv (fun x => deriv f x) x = deriv (deriv f) x := by simp
  rw[ht3]

  have existc : ∃ c ∈ Set.Ioo (x-r) x,  deriv (deriv f) c = (deriv f x - deriv f (x-r) )/r := by
    have hab: x-r < x := by linarith[hr]
    have hfc : ContinuousOn (deriv f) (Set.Icc (x-r) x):= Continuous.continuousOn hc1
    have hfd : DifferentiableOn ℝ (deriv f) (Set.Ioo (x-r) x) := Differentiable.differentiableOn hf2
    have exdev := exists_deriv_eq_slope (deriv f) hab hfc hfd
    have eq2: (deriv f x - deriv f (x - r)) / r = (deriv f x - deriv f (x - r)) / (x - (x - r)):=by simp
    rw[eq2]
    exact exdev

  obtain ⟨c, hcc⟩ := existc
  have hcceq: deriv (deriv f) c = (deriv f x - deriv f (x - r)) / r := hcc.right
  have hcceq2 :deriv f (x - r) - deriv f x = -r * ( deriv (deriv f) c )  := by
    rw[hcceq]; field_simp; ring;
  rw[hcceq2]
  simp [hr]
  have monoderiv : Monotone (deriv (deriv f)) := by
    apply monotone_of_deriv_nonneg; exact hf3;  exact hd3;
  have lc : c < x :=  (Set.mem_Ioo.mp hcc.left).right
  have lc2 : c<=x := by linarith [lc]
  exact Monotone.imp monoderiv lc2

  apply DifferentiableAt.comp
  apply hf1
  apply DifferentiableAt.sub; exact differentiableAt_id; exact differentiableAt_const r;
  apply hf1;
  apply DifferentiableAt.sub; apply DifferentiableAt.comp; apply hf1;
  apply DifferentiableAt.sub; exact differentiableAt_id;  exact differentiableAt_const r;
  apply hf1;
  apply DifferentiableAt.mul; exact differentiableAt_const r;
  apply hf2
