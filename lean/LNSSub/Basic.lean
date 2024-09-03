import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import LNS.Common

/- Definitions of Φ⁺(x) and E(i, r) -/

noncomputable section

namespace LNS

open Real

/- Φ⁺ from Introduction -/

def Φ (x : ℝ) := logb 2 (1 - (2 : ℝ) ^ x)

/- Iₓ and Rₓ correspond to iₓ and rₓ from Eq (1) -/

def Iₓ (Δ x : ℝ) := ⌈x / Δ⌉ * Δ

def Rₓ (Δ x : ℝ) := Iₓ Δ x - x

/- Φₜ is the first order Taylor approximation of Φ⁺ from Eq (1) -/

def Φₜ (Δ x : ℝ) := Φ (Iₓ Δ x) - Rₓ Δ x * deriv Φ (Iₓ Δ x)

/- E i r is the error of the first order Taylor approximation
   defined for all real i and r -/

def E (i r : ℝ) :=  (Φ i - r * deriv Φ i) -Φ (i - r)

def Q (Δ i r : ℝ) := E i r / E i Δ


lemma err_eq_zero : E i 0 = 0 := by simp [E]

lemma i_sub_r_eq_x (Δ x : ℝ) : Iₓ Δ x - Rₓ Δ x = x := by
  simp only [Iₓ, Rₓ, sub_sub_cancel]


lemma x_le_ix {Δ} (hd : 0 < Δ) x : x ≤ Iₓ Δ x :=
  (div_le_iff hd).mp $ Int.le_ceil $ x / Δ

lemma x_neg_iff_ix_neg {Δ} (hd : 0 < Δ) x : x ≤ 0 ↔ Iₓ Δ x ≤ 0 := by
  constructor
  · intro hx
    apply mul_nonpos_of_nonpos_of_nonneg _ (le_of_lt hd)
    rw [← Int.cast_zero, Int.cast_le, Int.ceil_le, Int.cast_zero]
    exact div_nonpos_of_nonpos_of_nonneg hx (le_of_lt hd)
  · exact le_trans (x_le_ix hd x)

lemma rx_eq_zero_iff {Δ x : ℝ} : Rₓ Δ x = 0 ↔ Iₓ Δ x = x := by
  simp only [Rₓ, Iₓ, sub_eq_zero]

lemma rx_eq_fract {Δ x : ℝ} (hd : Δ ≠ 0) (ix : Iₓ Δ x ≠ x) :
    Rₓ Δ x = Δ * (1 - Int.fract (x / Δ)) := by
  unfold Rₓ Iₓ at *
  rcases Int.fract_eq_zero_or_add_one_sub_ceil (x / Δ) with h | h
  · exfalso; apply ix
    rw [Int.ceil_eq_self.mpr h, div_mul_cancel _ hd]
  · rw [h]; field_simp; ring

lemma rx_nonneg {Δ} (hd : 0 < Δ) x : 0 ≤ Rₓ Δ x :=
  Int.ceil_div_mul_sub_nonneg hd

lemma rx_lt_delta {Δ} (hd : 0 < Δ) x : Rₓ Δ x < Δ :=
  Int.ceil_div_mul_sub_lt hd

/- Derivatives and differentiability of Φ -/

lemma hasDerivAt_two_pow (x : ℝ) : HasDerivAt (fun x => (2 : ℝ) ^ x) ((2 : ℝ) ^ x * log 2) x := by
  rw [(by ring : (2 : ℝ) ^ x * log 2 = 0 * x * (2 : ℝ) ^ (x - 1) + 1 * (2 : ℝ) ^ x * log 2)]
  exact HasDerivAt.rpow (hasDerivAt_const x 2) (hasDerivAt_id' x) two_pos

lemma deriv_two_pow (x : ℝ) : deriv (fun x => (2 : ℝ) ^ x) x = (2 : ℝ) ^ x * log 2 :=
  HasDerivAt.deriv (hasDerivAt_two_pow x)

lemma one_minus_two_pow_pos  (hx: x ≤ (-1:ℝ)) : 1 - (2 : ℝ) ^ x > 0 :=by
  have i1: (2:ℝ)^x <= (2:ℝ)^(-1:ℝ) :=by apply monotone_rpow_of_base_ge_one; linarith; assumption
  have h1: 0 < (2:ℝ):=by simp;
  have e1: (2:ℝ)^(-1:ℝ) < 1 :=by
    apply (Real.rpow_lt_one_iff_of_pos h1).mpr;
    apply Or.intro_left; apply And.intro; linarith; linarith;
  linarith

lemma one_plus_two_pow_ne_zero (hx: x ≤ (-1:ℝ)) : 1 - (2 : ℝ) ^ x ≠ 0 := by
  have : 1 - (2 : ℝ) ^ x > 0 :=by exact one_minus_two_pow_pos hx
  linarith

lemma diff_aux1 : Differentiable ℝ (fun (x : ℝ) => 1 - (2 : ℝ) ^ x) := by
  apply Differentiable.const_add; simp;
  apply Differentiable.rpow <;> simp


lemma differentiable_phi : DifferentiableOn ℝ Φ (Set.Iic (-1:ℝ)):= by
  unfold Φ
  unfold logb
  apply DifferentiableOn.div;
  apply DifferentiableOn.log; apply DifferentiableOn.const_sub; apply DifferentiableOn.rpow;
  apply differentiableOn_const; apply differentiableOn_id;
  simp; simp; intro x hx;
  have i1: 1 - (2 : ℝ) ^ x > 0 := one_minus_two_pow_pos hx
  linarith
  apply differentiableOn_const; simp; intro x  _;  linarith



def dphi  (x:ℝ) :=  -(2 : ℝ) ^ x / (1 - (2 : ℝ) ^ x)

lemma deriv_phi (hx: x ≤ (-1:ℝ)) :deriv Φ x = dphi x:= by
  unfold Φ logb dphi
  simp
  have i1: 1 - (2 : ℝ) ^ x > 0 := one_minus_two_pow_pos hx
  rw [deriv.log, deriv_const_sub, deriv_two_pow]
  field_simp; ring_nf
  apply DifferentiableAt.const_sub
  apply DifferentiableAt.rpow _ differentiableAt_id' <;> simp
  linarith

def d2phi  (x:ℝ) :=  -(log 2 *(2 : ℝ) ^ x ) / (1 - (2 : ℝ) ^ x)^2


lemma deriv_phi2 {x}  (hx: x ≤ -1): deriv dphi x = d2phi x := by
  unfold dphi d2phi
  have i1: 1 - (2 : ℝ) ^ x > 0 := one_minus_two_pow_pos  hx
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

lemma differentiable_phi0 : DifferentiableOn ℝ Φ (Set.Iio (0:ℝ)):= by
  unfold Φ
  unfold logb
  apply DifferentiableOn.div;
  apply DifferentiableOn.log; apply DifferentiableOn.const_sub; apply DifferentiableOn.rpow;
  apply differentiableOn_const; apply differentiableOn_id;
  simp; simp; intro x hx;
  have i1: (2 : ℝ) ^ x < 1 := by apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith
  linarith
  apply differentiableOn_const; simp; intro x  _;  linarith

lemma differentiable_dphi : DifferentiableOn ℝ dphi (Set.Iic (-1:ℝ)):= by
  unfold dphi
  apply DifferentiableOn.div;
  simp; apply DifferentiableOn.rpow;
  apply differentiableOn_const; apply differentiableOn_id;
  simp
  apply DifferentiableOn.const_sub; apply DifferentiableOn.rpow;
  apply differentiableOn_const; apply differentiableOn_id;
  simp
  intro x hx;
  have i1: 1 - (2 : ℝ) ^ x > 0 := one_minus_two_pow_pos hx
  linarith


lemma dphi_anti (hx: x ≤ (-1:ℝ)) (ht0: 0 < t): dphi (x-t) >  dphi x :=by
  apply Convex.strictAntiOn_of_deriv_neg (convex_Iic (-1:ℝ))
  apply DifferentiableOn.continuousOn differentiable_dphi
  simp; intro x hx;
  rw[deriv_phi2]; unfold d2phi;
  have i1: 1 - (2 : ℝ) ^ x > 0 := by apply one_minus_two_pow_pos; linarith
  have i2: (2 ^ x * log 2) / (1 - 2 ^ x) ^ 2 > 0 :=by
    apply div_pos;
    apply mul_pos;
    apply rpow_pos_of_pos; simp;
    apply log_pos ; linarith
    apply pow_pos; linarith
  have : -((2 ^ x * log 2) / (1 - 2 ^ x) ^ 2) = -( log 2  * 2 ^ x )/ (1 - 2 ^ x) ^ 2 := by ring_nf
  linarith; linarith
  simp; linarith;
  simp; linarith;
  linarith


lemma differentiable_d2phi : DifferentiableOn ℝ d2phi (Set.Iic (-1:ℝ)):= by
  unfold d2phi
  apply DifferentiableOn.div;
  simp; apply DifferentiableOn.const_mul; apply DifferentiableOn.rpow;
  apply differentiableOn_const; apply differentiableOn_id;
  simp; apply DifferentiableOn.pow;
  apply DifferentiableOn.const_sub; apply DifferentiableOn.rpow;
  apply differentiableOn_const; apply differentiableOn_id;
  simp
  intro x hx;
  have i1: 1 - (2 : ℝ) ^ x > 0 := one_minus_two_pow_pos hx
  apply pow_ne_zero; linarith

lemma eaux (ht0: t > 0) (ht1: t < 1): deriv (fun x ↦ -(log 2 * x) / (1 - x) ^ 2) t < 0:=by
  have i1: 1-t ≠ 0 :=by linarith
  have e:  deriv (fun x ↦ -(log 2 * x) / (1 - x) ^ 2) t = -((log 2) * (t+1)/(1-t)^3):=by
    rw[deriv_div]; simp; rw[deriv_mul]; simp;
    have e2: (fun x:ℝ => (1-x)^2) = (fun x=>x^2) ∘ (fun x=>1-x):=by  funext x; simp
    rw[e2, deriv.comp, deriv_pow, deriv_const_sub]; simp;
    have e3: (1-t)^(2*2) = ((1 - t) ^ 2) ^ 2  := by apply pow_mul (1-t)
    have e4: 2*2 = 4 :=by simp
    rw[←  e3, e4]
    field_simp; ring_nf
    apply DifferentiableAt.pow; simp; apply DifferentiableAt.const_sub; simp; simp; simp;
    simp; apply DifferentiableAt.const_mul; simp; apply DifferentiableAt.pow;
    apply DifferentiableAt.const_sub; simp;
    apply pow_ne_zero; linarith;
  rw[e]; simp;
  apply div_pos; apply mul_pos; apply log_pos; linarith; linarith;
  apply pow_pos; linarith


lemma d2phi_anti (hx: x ≤ (-1:ℝ)) (ht0: t < x): d2phi x <  d2phi t :=by
  apply Convex.strictAntiOn_of_deriv_neg (convex_Iic (-1:ℝ))
  apply DifferentiableOn.continuousOn differentiable_d2phi
  simp; intro u hu;
  have e1: d2phi = (fun x=> -(log 2*x)/(1-x)^2) ∘ (fun x=> (2:ℝ)^x) :=by unfold d2phi; funext x; simp
  rw[e1,deriv.comp]; rw[deriv_two_pow];
  apply mul_neg_of_neg_of_pos; apply eaux; apply rpow_pos_of_pos; linarith;
  apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith
  apply mul_pos; apply rpow_pos_of_pos; linarith; apply log_pos; linarith;
  apply DifferentiableAt.div; simp; apply DifferentiableAt.const_mul; simp; apply DifferentiableAt.pow;
  apply DifferentiableAt.const_sub; simp; apply pow_ne_zero;
  apply ne_of_gt; apply one_minus_two_pow_pos; linarith
  apply DifferentiableAt.rpow; simp; simp; simp;
  simp; linarith; simp; linarith; linarith


lemma differentiable_E (hi: i ≤ (-1:ℝ)) : DifferentiableOn ℝ (E i) (Set.Ici 0):= by
    apply DifferentiableOn.sub;
    apply DifferentiableOn.const_sub
    apply DifferentiableOn.mul; apply differentiableOn_id;
    rw[deriv_phi hi]; unfold dphi; apply differentiableOn_const;
    intro x; simp; intro hx;
    apply DifferentiableAt.differentiableWithinAt
    have : (fun y ↦ Φ (i-y)) = Φ ∘ (fun y ↦ (i-y)) := by ext x; simp
    rw[this]
    apply DifferentiableAt.comp; apply DifferentiableOn.differentiableAt differentiable_phi0
    apply Iio_mem_nhds; linarith;
    apply DifferentiableAt.const_sub; simp


lemma deriv_ei_pos (hi: i ≤ (-1:ℝ)) (hr : r>0) : 0 < deriv (E i) r :=by
    unfold E
    rw [deriv_sub, deriv_sub]
    · rw [deriv_mul_const (by simp : _)] ; simp;
      have : (fun y ↦ Φ (i-y)) = Φ ∘ (fun y ↦ (i-y)) := by ext x; simp
      rw[this]
      rw[deriv.comp, deriv_const_sub]; simp;
      rw[deriv_phi, deriv_phi]; apply dphi_anti;
      any_goals linarith
      apply DifferentiableOn.differentiableAt differentiable_phi0
      apply Iio_mem_nhds; linarith;
      apply DifferentiableAt.const_sub; simp
    apply differentiableAt_const;
    apply DifferentiableAt.mul_const; simp;
    apply DifferentiableAt.const_sub
    apply DifferentiableAt.mul_const; simp;
    have : (fun y ↦ Φ (i-y)) = Φ ∘ (fun y ↦ (i-y)) := by ext x; simp
    rw[this]
    apply DifferentiableAt.comp; apply DifferentiableOn.differentiableAt differentiable_phi0
    apply Iio_mem_nhds; linarith;
    apply DifferentiableAt.const_sub; simp

lemma strictMonoOn_E_r (hi: i ≤ (-1:ℝ)) : StrictMonoOn (E i) (Set.Ici 0) := by

  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
  · apply DifferentiableOn.continuousOn (differentiable_E hi)
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x hx
    apply deriv_ei_pos hi hx

lemma monotoneOn_E_r (hi: i ≤ (-1:ℝ)) : MonotoneOn (E i) (Set.Ici 0) :=
  StrictMonoOn.monotoneOn (strictMonoOn_E_r hi)

/- First part of Lemma 5.1: E(i, r) ≥ 0 when r ≥ 0 -/

lemma err_nonneg (hi: i ≤ (-1:ℝ)) (hr : 0 ≤ r) : 0 ≤ E i r := by
  rw [(by simp [E] : 0 = E i 0)]
  rcases eq_or_gt_of_le hr with h | h
  · rw [h]
  · apply le_of_lt
    exact (strictMonoOn_E_r hi) Set.left_mem_Ici hr h


lemma err_pos (hi: i ≤ (-1:ℝ)) (hr : 0 < r) : 0 < E i r := by
  rw [(by simp [E] : 0 = E i 0)]
  apply strictMonoOn_E_r hi;
  simp; simp; linarith; assumption


noncomputable def Er r i := E i r

noncomputable def Et r i :=  Φ i - r * dphi i - Φ (i - r)


lemma deriv_er_pos (hi: i < (-1:ℝ)) (hr : 0 < r):  0 < deriv (Et r) i :=by
  have diff1 : DifferentiableOn ℝ (fun y ↦ Φ (y - r)) (Set.Iic (-1:ℝ)) := by
    intro x
    have : (fun y ↦ Φ (y-r)) = Φ ∘ (fun y ↦ (y-r)) := by ext x; simp
    rw[this]; simp; intro x; apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.comp; apply DifferentiableOn.differentiableAt differentiable_phi0
    apply Iio_mem_nhds; linarith;
    apply DifferentiableAt.sub_const; simp

  have diff4 : DifferentiableOn ℝ (fun y ↦ r * dphi y) (Set.Iic (-1:ℝ)):= by
    apply DifferentiableOn.const_mul; exact differentiable_dphi


  have diff2 : DifferentiableOn ℝ (fun y ↦ Φ y - r * dphi y ) (Set.Iic (-1:ℝ)) := by
    apply DifferentiableOn.sub  differentiable_phi diff4;

  have diffE : DifferentiableOn ℝ (Et r) (Set.Iic (-1:ℝ)) := by
    unfold Et; apply DifferentiableOn.sub; apply DifferentiableOn.sub;
    exact differentiable_phi; assumption; assumption

  unfold Et;
  rw [deriv_sub , deriv_sub ,
        deriv_const_mul , deriv_phi, deriv_comp_sub_const, deriv_phi]
  have i1: (i-r) < i :=by linarith;
  have diffdphi: DifferentiableOn ℝ dphi (Set.Icc (i - r) i):=by
      apply DifferentiableOn.mono differentiable_dphi
      have s1: Set.Icc (i - r) i ⊆ Set.Iic i := Set.Icc_subset_Iic_self
      have s2: Set.Iic i ⊆ Set.Iic (-1) :=by apply Set.Iic_subset_Iic.mpr; linarith
      exact subset_trans s1 s2
  have existc : ∃ c ∈ Set.Ioo (i-r) i,  deriv dphi c = (dphi i - dphi (i-r))/(i - (i-r)) := by
    apply exists_deriv_eq_slope dphi i1
    apply DifferentiableOn.continuousOn diffdphi
    apply DifferentiableOn.mono diffdphi Set.Ioo_subset_Icc_self;
  obtain ⟨c, hcc⟩ := existc
  have e1: dphi i - r * deriv (fun i ↦ dphi i) i - dphi (i - r) = r * (deriv dphi c - deriv dphi i):=by
    rw[hcc.right]; field_simp; ring_nf
  rw[e1]; apply mul_pos; assumption;
  rw[deriv_phi2, deriv_phi2]; simp; apply d2phi_anti; linarith
  any_goals have hcs: c < i := (Set.mem_Ioo.mp hcc.left).right
  assumption; any_goals linarith;
  apply DifferentiableOn.differentiableAt differentiable_dphi
  apply Iic_mem_nhds; linarith;
  apply DifferentiableOn.differentiableAt differentiable_phi
  apply Iic_mem_nhds; linarith;
  apply DifferentiableOn.differentiableAt diff4
  apply Iic_mem_nhds; linarith;
  apply DifferentiableOn.differentiableAt diff2
  apply Iic_mem_nhds; linarith;
  apply DifferentiableOn.differentiableAt diff1
  apply Iic_mem_nhds; linarith;

lemma strictMonoOn_E_i {r} (hr : 0 < r) : StrictMonoOn (Er r) (Set.Iic (-1:ℝ)) := by
  have e0: Set.EqOn (Et r) (Er r) (Set.Iic (-1:ℝ)) :=by
    unfold Set.EqOn; simp; intro x hx; unfold Et Er E; rw[deriv_phi]; assumption

  apply StrictMonoOn.congr _ e0;

  have diff1 : DifferentiableOn ℝ (fun y ↦ Φ (y - r)) (Set.Iic (-1:ℝ)) := by
    intro x
    have : (fun y ↦ Φ (y-r)) = Φ ∘ (fun y ↦ (y-r)) := by ext x; simp
    rw[this]; simp; intro x; apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.comp; apply DifferentiableOn.differentiableAt differentiable_phi0
    apply Iio_mem_nhds; linarith;
    apply DifferentiableAt.sub_const; simp
  have diff4 : DifferentiableOn ℝ (fun y ↦ r * dphi y) (Set.Iic (-1:ℝ)):= by
    apply DifferentiableOn.const_mul; exact differentiable_dphi

  have diffE : DifferentiableOn ℝ (Et r) (Set.Iic (-1:ℝ)) := by
    unfold Et; apply DifferentiableOn.sub; apply DifferentiableOn.sub;
    exact differentiable_phi; assumption; assumption

  apply Convex.strictMonoOn_of_deriv_pos (convex_Iic (-1:ℝ))
  exact DifferentiableOn.continuousOn diffE
  simp only [Set.nonempty_Ioi, interior_Iic', Set.mem_Iio]
  intro i i_neg
  apply deriv_er_pos i_neg hr


lemma monotoneOn_E_i {r} (hr : 0 ≤ r) : MonotoneOn (Er r) (Set.Iic (-1:ℝ)) := by
  rcases lt_or_eq_of_le hr with h | h
  · exact StrictMonoOn.monotoneOn $ strictMonoOn_E_i h
  · simp [← h, err_eq_zero];
    have: Er 0 = (fun x=> (0:ℝ)) :=by unfold Er E; simp;
    rw[this]
    exact monotoneOn_const

end LNS
