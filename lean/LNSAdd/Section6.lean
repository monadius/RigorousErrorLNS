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

variable {i Δ r : Real}
variable (delta_pos : Δ > 0)
def hrΔ :=  r < Δ

noncomputable def pow2 (x : ℝ) := (2 : ℝ) ^ x
private def f a r := a * r * log 2 - (a + 1) * log (a + 1) + (a + 1) * log (a * 2 ^ (-r) + 1)

def h  (r:ℝ) (i:ℝ) := f (2^i) r

def dih (r:ℝ) (i:ℝ) := (2^i* (2^(i-r)+1) * (r*(log 2) - (log (2^i +1)) +  (log (2^(i-r) +1))
 -1) + 2^(i-r)*(2^i+1)) * (log 2) / (2^(i-r) +1 )

def g  (i:ℝ) (r:ℝ) :=  (h r i)/ (dih r i)

def k (a:ℝ) (b:ℝ) := a * a * log (a + 1) - a * a * log (a + b) + a * b - a - b * log (a + 1) - b * log b + b * log (a + b)

def gbn (a:ℝ) (c:ℝ) (b:ℝ)  := (a+b)*(a*(log b) - c*(a+1) + (a+1)*(-log b + log (a+b)))

def gbd (a:ℝ) (c:ℝ) (b:ℝ)  := a*(log  2)*(a+1+(a+b)*(log (a+b) -c-1))

def gb (a:ℝ) (c:ℝ) (b:ℝ)  := (gbn a c b)/(gbd a c b)

def er (r:ℝ) (i:ℝ):=  E i r

def f1 (a : ℝ) := a * exp (-a) + exp (-a) - 1
def h1 (a : ℝ) := (a + 2) * exp (-a) + (a - 2)

/- ****************************************** -/


/-SUPPORTING 6.2******************************************************************************* -/

def dk a b := -(a*a)/(a+b) + a + b/(a+b) - log b -log (a+1) + log (a+b) - (1:ℝ)

lemma deriv_k (ha: a>0) (hb:b>=1): deriv (k a) b = dk a b := by
  unfold k; unfold dk;
  rw[deriv_add, deriv_sub, deriv_sub, deriv_sub, deriv_add, deriv_sub, deriv_mul]
  rw[deriv_mul, deriv_mul, deriv_mul,  deriv_mul, deriv_mul, deriv.log]
  simp;
  rw[deriv_mul,deriv_log,deriv_mul,deriv.log, deriv_add]
  simp;
  field_simp; ring_nf;
  any_goals simp;
  any_goals apply DifferentiableAt.log
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.sub
  any_goals apply DifferentiableAt.sub
  any_goals simp;
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.log
  any_goals simp;
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.sub
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.log
  any_goals apply DifferentiableAt.add
  any_goals simp
  any_goals linarith


lemma deriv_dk (ha: a>0) (hb:b>1): deriv (dk a) b > 0 :=by
  unfold dk
  rw[deriv_sub, deriv_add, deriv_sub, deriv_sub, deriv_add, deriv_add]; simp;
  rw[deriv_div, deriv.log, deriv_div, deriv_add]; simp;
  field_simp;
  apply div_pos;
  have t1 :  ((a * a + a) * b - (a + b) ^ 2) * (a + b) + (a + b) ^ 2 * b = a^2*(a+b)*(b-1) :=by ring
  rw[t1]
  apply mul_pos; apply mul_pos; apply pow_pos; linarith[ha];
  any_goals linarith
  apply mul_pos; apply mul_pos; apply pow_pos;
  any_goals linarith
  any_goals simp
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.div
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.inv
  any_goals simp
  any_goals apply DifferentiableAt.div
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.log
  any_goals simp
  any_goals linarith
  any_goals apply DifferentiableAt.div
  any_goals apply DifferentiableAt.add
  any_goals simp
  any_goals linarith

lemma dk_1 (ha: a>0): dk a 1  = 0 := by unfold dk ; field_simp; ring_nf

lemma differentiable_dk  (ha: a>0): DifferentiableOn ℝ (dk a) (Set.Ici (1:ℝ)):= by
  unfold dk
  apply DifferentiableOn.sub
  apply DifferentiableOn.add; apply DifferentiableOn.sub; apply DifferentiableOn.sub;
  apply DifferentiableOn.add; apply DifferentiableOn.add; apply DifferentiableOn.div;
  apply DifferentiableOn.neg; apply DifferentiableOn.mul;
  any_goals apply DifferentiableOn.div;
  any_goals apply DifferentiableOn.log;
  any_goals apply DifferentiableOn.add;
  any_goals apply differentiableOn_const
  any_goals apply differentiableOn_id
  any_goals simp
  any_goals intro x hx
  any_goals linarith


lemma dk_pos (ha: a>0) (hb:b>1): (dk a) b >0 :=by
  rw [← dk_1]
  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici 1)
  apply DifferentiableOn.continuousOn (differentiable_dk ha)
  any_goals simp;
  any_goals linarith;
  intro x h
  exact deriv_dk ha h

lemma k_1 : k a 1 = 0 := by unfold k ; field_simp;

lemma differentiable_k  (ha: a>0): DifferentiableOn ℝ (k a) (Set.Ici (1:ℝ)):= by
  unfold k
  apply DifferentiableOn.add
  apply DifferentiableOn.sub; apply DifferentiableOn.sub; apply DifferentiableOn.sub
  apply DifferentiableOn.add; apply DifferentiableOn.sub;
  apply DifferentiableOn.mul;
  any_goals apply DifferentiableOn.mul;
  any_goals apply DifferentiableOn.log;
  any_goals apply DifferentiableOn.add;
  any_goals apply DifferentiableOn.mul;
  any_goals apply differentiableOn_const
  any_goals apply differentiableOn_id
  any_goals simp
  any_goals intro x hx
  any_goals linarith



lemma knonneg (a:ℝ) (b:ℝ) (ha: a>0) (hb:b>=1) : k a b ≥ 0 :=by
  rw [← k_1]
  apply Convex.monotoneOn_of_deriv_nonneg (convex_Ici 1)
  apply DifferentiableOn.continuousOn (differentiable_k ha)
  apply DifferentiableOn.mono (differentiable_k ha)
  apply interior_subset
  any_goals simp;
  any_goals linarith;
  intro x h
  have hx: x ≥ 1 :=by linarith
  rw[deriv_k ha hx]
  apply le_of_lt
  exact dk_pos ha h




lemma derivd_pos (a:ℝ) (c:ℝ) (b:ℝ) (ha: a>0) (hb: b>1) (hc:c = log (a+1)) : 0 < deriv (gbd a c) b :=by
  have derivd: deriv (fun b ↦ gbd a c b) b = a *  (log 2) * (log (a+b) -c):=by
    unfold gbd
    rw[deriv_mul, deriv_mul, deriv_const]; simp
    rw[deriv_mul, deriv_add, deriv_const];
    rw[deriv_sub, deriv_sub, deriv_const, deriv_const, deriv.log, deriv_add];
    rw[deriv_const]; simp; field_simp;
    any_goals apply DifferentiableAt.sub
    any_goals apply DifferentiableAt.add
    any_goals simp
    any_goals apply DifferentiableAt.log
    any_goals apply DifferentiableAt.mul
    any_goals apply DifferentiableAt.add
    any_goals apply DifferentiableAt.sub
    any_goals apply DifferentiableAt.log
    any_goals apply DifferentiableAt.add
    any_goals simp
    any_goals linarith
  rw[derivd,hc]
  apply mul_pos; apply mul_pos; any_goals linarith;
  apply log_pos; linarith
  simp; apply log_lt_log; any_goals linarith;

lemma gbd_pos (a:ℝ) (c:ℝ) (b:ℝ) (ha: a>0) (hb: b>1) (hc:c = log (a+1)) : 0 < gbd a c b:= by
  have t1: StrictMonoOn (gbd a c) (Set.Ici (1:ℝ)) := by
    apply Convex.strictMonoOn_of_deriv_pos (convex_Ici (1:ℝ))
    unfold gbd
    apply ContinuousOn.mul; apply ContinuousOn.mul;
    exact continuousOn_const;  exact continuousOn_const;  apply ContinuousOn.add; apply ContinuousOn.add;
    any_goals apply ContinuousOn.mul
    any_goals apply ContinuousOn.sub
    any_goals apply ContinuousOn.sub
    any_goals apply ContinuousOn.add
    any_goals apply ContinuousOn.log
    any_goals apply ContinuousOn.add
    any_goals exact continuousOn_const
    any_goals exact continuousOn_id
    any_goals intro x hx
    have hx1: x>=1 := Set.mem_Ici.mp hx
    linarith
    have hx1: x>1 :=by
      apply Set.mem_Ioi.mp ;
      have : Set.Ioi (1:ℝ) = interior (Set.Ici 1) :=  by rw[interior_Ici]
      rw[this]; exact hx;
    apply derivd_pos
    any_goals  linarith;
  have t2: gbd a c 1 = 0 :=by unfold gbd; rw[hc]; ring;
  have tt: (gbd a c) 1 < (gbd a c) b ↔ 1<b := by apply StrictMonoOn.lt_iff_lt t1; simp; simp; linarith;
  have t : (gbd a c) 1 < (gbd a c) b := by apply tt.mpr ; linarith;
  rw[← t2]; linarith;


lemma deriv_gb_le0 (a:ℝ) (c:ℝ) (b:ℝ) (ha: a>0) (hb: b>1) (hc:c = log (a+1)):  (deriv (gb a c)) b <= 0 :=by
  have derivd: deriv (fun b ↦ gbd a c b) b = a *  (log 2) * (log (a+b) -c):=by
    unfold gbd
    rw[deriv_mul, deriv_mul, deriv_const]; simp
    rw[deriv_mul, deriv_add, deriv_const];
    rw[deriv_sub, deriv_sub, deriv_const, deriv_const, deriv.log, deriv_add];
    rw[deriv_const]; simp; field_simp;
    any_goals apply DifferentiableAt.sub
    any_goals apply DifferentiableAt.add
    any_goals simp
    any_goals apply DifferentiableAt.log
    any_goals apply DifferentiableAt.mul
    any_goals apply DifferentiableAt.add
    any_goals apply DifferentiableAt.sub
    any_goals apply DifferentiableAt.log
    any_goals apply DifferentiableAt.add
    any_goals simp
    any_goals linarith
  have derivn: deriv (fun b ↦ gbn a c b) b = -a*c + a*log (a+b) + a - a/b -c - log b + log (a+b):=by
    unfold gbn
    rw [deriv_mul, deriv_add]; simp; rw[deriv_add, deriv_sub, deriv_mul, deriv.log]; simp;
    rw [deriv_add, deriv.log, deriv_add];simp;
    field_simp; ring;
    any_goals simp
    any_goals apply DifferentiableAt.add
    any_goals apply DifferentiableAt.mul
    any_goals apply DifferentiableAt.log
    any_goals simp
    any_goals linarith
    any_goals apply DifferentiableAt.add
    any_goals apply DifferentiableAt.mul
    any_goals apply DifferentiableAt.log
    any_goals simp
    any_goals apply DifferentiableAt.add
    any_goals simp
    any_goals linarith

  unfold gb
  rw[deriv_div]
  have t1: gbd a c b ^ 2 >= 0 :=  by exact pow_two_nonneg (gbd a c b)
  simp
  apply div_nonpos_of_nonpos_of_nonneg
  any_goals assumption
  rw[derivd,derivn]
  unfold gbd
  unfold gbn
  field_simp;
  apply div_nonpos_of_nonpos_of_nonneg
  have : ((-(a * c) + a * log (a + b) + a) * b - a - b * c - b * log b + log (a + b) * b) *(a * log 2 * (a + 1 + (a + b) * (log (a + b) - c - 1))) -
  b * ((a + b) * (a * log b - c * (a + 1) + (a + 1) * (-log b + log (a + b))) * (a * log 2 * (log (a + b) - c))) =
  -a*(b-1)*(a*a*c - a*a*log (a+b) + a*b -a - b*c -b*log b + b*log (a+b)  )* log 2  :=by ring;
  rw[this]
  simp;
  apply mul_nonneg
  apply mul_nonneg
  apply mul_nonneg
  linarith; linarith
  rw[hc]
  apply knonneg
  any_goals linarith
  have t :0 < log 2 := by apply log_pos; linarith;
  linarith
  unfold gbn
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.sub
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.add
  any_goals simp
  any_goals apply DifferentiableAt.log
  any_goals apply DifferentiableAt.add
  any_goals simp
  any_goals linarith
  have t1: StrictMonoOn (gbd a c) (Set.Ici (1:ℝ)) := by
    apply Convex.strictMonoOn_of_deriv_pos (convex_Ici (1:ℝ))
    unfold gbd
    apply ContinuousOn.mul; apply ContinuousOn.mul;
    exact continuousOn_const;  exact continuousOn_const;  apply ContinuousOn.add; apply ContinuousOn.add;
    any_goals apply ContinuousOn.mul
    any_goals apply ContinuousOn.sub
    any_goals apply ContinuousOn.sub
    any_goals apply ContinuousOn.add
    any_goals apply ContinuousOn.log
    any_goals apply ContinuousOn.add
    any_goals exact continuousOn_const
    any_goals exact continuousOn_id
    any_goals intro x hx
    have hx1: x>=1 := Set.mem_Ici.mp hx
    linarith
    have hx1: x>1 :=by
      apply Set.mem_Ioi.mp ;
      have : Set.Ioi (1:ℝ) = interior (Set.Ici 1) :=  by rw[interior_Ici]
      rw[this]; exact hx;
    apply derivd_pos
    any_goals  linarith;
  have t2: gbd a c 1 = 0 :=by unfold gbd; rw[hc]; ring_nf;
  have tt: (gbd a c) 1 < (gbd a c) b ↔ 1<b := by apply StrictMonoOn.lt_iff_lt t1; simp; simp; linarith;
  have t : (gbd a c) 1 < (gbd a c) b := by apply tt.mpr ; linarith;
  rw[← t2]; linarith;



lemma deriv_h (r:ℝ) (i:ℝ) :  (deriv (h r)) i = dih r i:= by
 have t5: (2:ℝ)^i > 0 :=by  linarith [rpow_pos_of_pos two_pos i]
 have t6: (2:ℝ)^(-r) > 0 :=by  linarith [rpow_pos_of_pos two_pos (-r)]
 have t7: (2:ℝ)^i * (2:ℝ)^(-r) > 0 := by linarith[mul_pos t5 t6]
 unfold h
 unfold f
 rw[deriv_add, deriv_sub];
 rw[deriv_mul, deriv_mul];
 rw[deriv_two_pow, deriv_const, deriv_const]
 rw[deriv_mul, deriv_add, deriv_const, deriv_two_pow, deriv_mul, deriv_add, deriv_const]
 rw[deriv_two_pow, deriv.log, deriv_add, deriv_two_pow, deriv_const]
 rw[deriv.log, deriv_add,deriv_const,deriv_mul,deriv_two_pow, deriv_const]; simp
 have tt : (2:ℝ)^(i-r) = 2^i *2^(-r)  :=by
  have h1: 0< (2:ℝ):= by linarith
  rw[← rpow_add];  ring_nf; assumption
 have t1: 2 ^ i * log 2 * 2 ^ (-r) = 2 ^ i * 2 ^ (-r) * log 2 :=by ring
 rw[← tt, t1,  ← tt];
 have t2: dih r i = (log 2)*((2^i* (2^(i-r)+1) * (r*(log 2) - (log (2^i +1)) +  (log (2^(i-r) +1))
 -1)))/ (2^(i-r) +1 ) + 2^(i-r)*(2^i+1)*(log 2)/ (2^(i-r) +1 ):=by unfold dih; field_simp; ring;
 rw[t2];
 have t3: 2 ^ i * log 2 * r * log 2 - (2 ^ i * log 2 * log (2 ^ i + 1) + (2 ^ i + 1) * (2 ^ i * log 2 / (2 ^ i + 1))) +
    (2 ^ i * log 2 * log (2 ^ (i - r) + 1) + (2 ^ i + 1) * (2 ^ (i - r) * log 2 / (2 ^ (i - r) + 1))) =
    2 ^ i * log 2 * r * log 2 - (2 ^ i * log 2 * log (2 ^ i + 1) + (2 ^ i + 1) * (2 ^ i * log 2 / (2 ^ i + 1))) +
    2 ^ i * log 2 * log (2 ^ (i - r) + 1) + (2 ^ i + 1) * (2 ^ (i - r) * log 2 / (2 ^ (i - r) + 1)) :=by ring
 rw[t3];
 have t4: 2 ^ (i - r) * (2 ^ i + 1) * log 2 / (2 ^ (i - r) + 1) = (2 ^ i + 1) * (2 ^ (i - r) * log 2 / (2 ^ (i - r) + 1)):=by field_simp;ring;
 rw[t4]; simp;
 field_simp; ring;
 any_goals apply DifferentiableAt.rpow
 any_goals exact differentiableAt_const 1
 any_goals exact differentiableAt_const 2
 any_goals exact differentiableAt_id
 any_goals exact differentiableAt_const r
 any_goals simp
 any_goals apply DifferentiableAt.rpow
 any_goals exact differentiableAt_id
 any_goals exact differentiableAt_const 2
 any_goals simp
 any_goals apply DifferentiableAt.mul
 any_goals apply DifferentiableAt.rpow
 any_goals exact differentiableAt_const 2
 any_goals exact differentiableAt_id
 any_goals apply DifferentiableAt.sub
 any_goals apply DifferentiableAt.mul
 any_goals simp
 any_goals apply DifferentiableAt.rpow
 any_goals apply DifferentiableAt.log
 any_goals apply DifferentiableAt.add
 any_goals apply DifferentiableAt.mul
 any_goals apply DifferentiableAt.rpow
 any_goals simp
 any_goals linarith[t7]


/-******************************************************************-/

lemma strictMonoOn_E_r  : StrictMonoOn (E i) (Set.Ici 0) := by
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

lemma monotoneOn_E_r : MonotoneOn (E i) (Set.Ici 0) :=
  StrictMonoOn.monotoneOn (strictMonoOn_E_r)


lemma err_nonneg  (hr : 0 ≤ r) : 0 ≤ E i r := by
  rw [(by simp [E] : 0 = E i 0)]
  rcases eq_or_gt_of_le hr with h | h
  · rw [h]
  · apply le_of_lt
    exact (strictMonoOn_E_r) Set.left_mem_Ici hr h

private lemma differentiable_f : Differentiable ℝ f1 :=
  let dexp := Differentiable.exp differentiable_neg
  Differentiable.sub_const (Differentiable.add (Differentiable.mul differentiable_id' dexp) dexp) _

private lemma deriv_f (a : ℝ) : deriv f1 a = -a * exp (-a) := by
  unfold f1
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

private lemma f_zero : f1 0 = 0 := by simp [f1]
private lemma f_neg {a} (ha : a ≠ 0) : f1 a < 0 := by
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

private lemma h_nonneg (ha : 0 ≤ a) : 0 ≤ h1 a := by
  have h0 : h1 0 = 0 := by
    simp only [h1, zero_add, neg_zero, exp_zero, mul_one, zero_sub, add_right_neg]
  have dh0 : Differentiable ℝ (fun a : ℝ => -a) := Differentiable.neg differentiable_id'
  have dh1 : Differentiable ℝ (fun a => exp (-a)) := Differentiable.exp dh0
  have dh2 : Differentiable ℝ (fun a : ℝ => a + 2) := by simp
  have dh3 : Differentiable ℝ (fun a => (a + 2) * exp (-a)) := Differentiable.mul dh2 dh1
  have dh4 : Differentiable ℝ (fun a : ℝ => a - 2) := by simp
  have dh : Differentiable ℝ h1 := Differentiable.add dh3 dh4
  rw [← h0]
  apply Convex.monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · apply Continuous.continuousOn
    exact Differentiable.continuous dh
  · exact Differentiable.differentiableOn dh
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x hx; unfold h1
    rw [deriv_add (dh3 _) (dh4 _), deriv_sub_const, deriv_mul (dh2 _) (dh1 _), _root_.deriv_exp (dh0 _),
        deriv_add_const, deriv_neg, deriv_id'']
    simp only [one_mul, mul_neg, mul_one]
    calc
      exp (-x) + -((x + 2) * exp (-x)) + 1 = -(f1 x) := by unfold f1; ring
      _ ≥ 0 := le_of_lt $ neg_pos_of_neg $ f_neg $ ne_of_gt hx
  · exact Set.left_mem_Ici
  · exact ha
  · exact ha

private lemma h1_pos (ha : 0 < a) : 0 < h1 a := by
  have h0 : h1 0 = 0 := by
    simp only [h1, zero_add, neg_zero, exp_zero, mul_one, zero_sub, add_right_neg]
  have dh0 : Differentiable ℝ (fun a : ℝ => -a) := Differentiable.neg differentiable_id'
  have dh1 : Differentiable ℝ (fun a => exp (-a)) := Differentiable.exp dh0
  have dh2 : Differentiable ℝ (fun a : ℝ => a + 2) := by simp
  have dh3 : Differentiable ℝ (fun a => (a + 2) * exp (-a)) := Differentiable.mul dh2 dh1
  have dh4 : Differentiable ℝ (fun a : ℝ => a - 2) := by simp
  have dh : Differentiable ℝ h1 := Differentiable.add dh3 dh4
  rw [← h0]
  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici 0)
  · apply Continuous.continuousOn
    exact Differentiable.continuous dh
  · simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x hx; unfold h1
    rw [deriv_add (dh3 _) (dh4 _), deriv_sub_const, deriv_mul (dh2 _) (dh1 _), _root_.deriv_exp (dh0 _),
        deriv_add_const, deriv_neg, deriv_id'']
    simp only [one_mul, mul_neg, mul_one]
    calc
      exp (-x) + -((x + 2) * exp (-x)) + 1 = -(f1 x) := by unfold f1; ring
      _ > 0 :=  neg_pos_of_neg $ f_neg $ ne_of_gt hx
  · exact Set.left_mem_Ici;
  simp; linarith; assumption;



lemma deriv_er_pos (i:ℝ) (r:ℝ) (hi : i <= 0) (hr : 0 < r) : deriv (er r) i > 0 := by
  have diff1 : Differentiable ℝ fun y ↦ Φ (y - r) := by
    intro x
    rw [DifferentiableAt.comp_sub_const]
    exact differentiable_phi _
  have diff2 : Differentiable ℝ fun y ↦ Φ (y - r) - Φ y := Differentiable.sub diff1 differentiable_phi
  have diff3 : Differentiable ℝ (deriv Φ) := by
    rw [deriv_phi]
    apply Differentiable.div _ diff_aux1 one_plus_two_pow_ne_zero
    exact fun x => (hasDerivAt_two_pow x).differentiableAt
  have diff4 : Differentiable ℝ (fun y ↦ r * deriv Φ y) := Differentiable.const_mul diff3 _
  have diffE : Differentiable ℝ (er r) := Differentiable.add diff2 diff4
  have h1 : 0 < deriv (er r) i := by
    unfold er
    unfold E
    rw [deriv_add (diff2 _) (diff4 _), deriv_sub (diff1 _) (differentiable_phi _),
        deriv_const_mul _ (diff3 _), deriv_phi2, deriv_comp_sub_const, deriv_phi]
    simp only
    rw [rpow_sub two_pos, div_eq_inv_mul _ (2 ^ r), ← rpow_neg (le_of_lt two_pos)]
    field_simp
    set x := (2 : ℝ) ^ (-r)
    set y := (2 : ℝ) ^ i
    have ypos1 : 0 < 1 + y := one_plus_two_pow_pos i
    apply div_pos
    · have : (x * y * (1 + y) - (1 + x * y) * y) * (1 + y) ^ 2 + r * (y * log 2) * ((1 + x * y) * (1 + y)) =
             (1 + y) * y * (y * (r * log 2 * x + x - 1) + (x + r * log 2 - 1)) := by ring
      rw [this]; clear this
      apply mul_pos (mul_pos ypos1 (rpow_pos_of_pos two_pos _))
      set a := r * log 2
      have a_pos : 0 < a := mul_pos hr (log_pos one_lt_two)
      have exp_a : x = exp (-a) := by
        rw [← neg_mul, mul_comm, exp_mul, exp_log two_pos]
      rw [exp_a]
      let N t := t * f1 a + (exp (-a) + a - 1)
      have : N y = y * (a * exp (-a) + exp (-a) - 1) + (exp (-a) + a - 1) := by simp [f1]
      rw [← this]; clear this
      have : 0 < N 1 := by
        have h1 : h1 a = N 1 := by simp [f1, h1]; ring
        rw [← h1]
        exact h1_pos (a_pos)
      have vv: N 1 ≤ N y := by
        have antiN: StrictAntiOn N (Set.Ici 0):= by
          apply Convex.strictAntiOn_of_deriv_neg (convex_Ici 0)
          · apply Continuous.continuousOn
            apply Continuous.add (continuous_mul_right _) continuous_const
          . simp; intro x _
            exact f_neg (ne_of_gt a_pos)
        have t1: 1 ≥ y := by apply rpow_le_one_of_one_le_of_nonpos; linarith; linarith
        have t2: (1:ℝ) ∈ Set.Ici 0 :=by simp
        have t3: y ∈ Set.Ici 0 := by simp; apply le_of_lt; apply rpow_pos_of_pos; linarith
        have t4: N 1 ≤ N y ↔ y ≤ 1 := by apply StrictAntiOn.le_iff_le antiN; simp; assumption
        apply t4.mpr; linarith
      linarith
    apply mul_pos; apply mul_pos;
    any_goals apply pow_pos
    have t1: x>0 :=by simp; apply rpow_pos_of_pos; linarith
    have t2: y>0 :=by simp; apply rpow_pos_of_pos; linarith
    have t3: x*y > 0 :=by apply mul_pos; linarith; linarith;
    any_goals linarith
  linarith



lemma strictMonoOn_E_i {r} (hr : 0 < r) : StrictMonoOn (fun i => E i r) (Set.Iic 0) := by
  have diff1 : Differentiable ℝ fun y ↦ Φ (y - r) := by
    intro x
    rw [DifferentiableAt.comp_sub_const]
    exact differentiable_phi _
  have diff2 : Differentiable ℝ fun y ↦ Φ (y - r) - Φ y := Differentiable.sub diff1 differentiable_phi
  have diff3 : Differentiable ℝ (deriv Φ) := by
    rw [deriv_phi]
    apply Differentiable.div _ diff_aux1 one_plus_two_pow_ne_zero
    exact fun x => (hasDerivAt_two_pow x).differentiableAt
  have diff4 : Differentiable ℝ (fun y ↦ r * deriv Φ y) := Differentiable.const_mul diff3 _
  have diffE : Differentiable ℝ (fun i => E i r) := Differentiable.add diff2 diff4
  apply Convex.strictMonoOn_of_deriv_pos (convex_Iic 0)
  · apply Continuous.continuousOn
    exact Differentiable.continuous diffE
  · simp only [Set.nonempty_Ioi, interior_Iic', Set.mem_Iio]
    intro i i_neg
    unfold E
    rw [deriv_add (diff2 _) (diff4 _), deriv_sub (diff1 _) (differentiable_phi _),
        deriv_const_mul _ (diff3 _), deriv_phi2, deriv_comp_sub_const, deriv_phi]
    simp only
    rw [rpow_sub two_pos, div_eq_inv_mul _ (2 ^ r), ← rpow_neg (le_of_lt two_pos)]
    field_simp
    set x := (2 : ℝ) ^ (-r)
    set y := (2 : ℝ) ^ i
    have ypos1 : 0 < 1 + y := one_plus_two_pow_pos i
    apply div_pos
    · have : (x * y * (1 + y) - (1 + x * y) * y) * (1 + y) ^ 2 + r * (y * log 2) * ((1 + x * y) * (1 + y)) =
             (1 + y) * y * (y * (r * log 2 * x + x - 1) + (x + r * log 2 - 1)) := by ring
      rw [this]; clear this
      apply mul_pos (mul_pos ypos1 (rpow_pos_of_pos two_pos _))
      set a := r * log 2
      have a_pos : 0 < a := mul_pos hr (log_pos one_lt_two)
      have exp_a : x = exp (-a) := by
        rw [← neg_mul, mul_comm, exp_mul, exp_log two_pos]
      rw [exp_a]
      let N t := t * f1 a + (exp (-a) + a - 1)
      have : N y = y * (a * exp (-a) + exp (-a) - 1) + (exp (-a) + a - 1) := by simp [f1]
      rw [← this]; clear this
      have : 0 ≤ N 1 := by
        have h1 : h1 a = N 1 := by simp [f1, h1]; ring
        rw [← h1]
        exact h_nonneg (le_of_lt a_pos)
      apply lt_of_le_of_lt this
      apply Convex.strictAntiOn_of_deriv_neg (convex_Ici 0)
      · apply Continuous.continuousOn
        apply Continuous.add (continuous_mul_right _) continuous_const
      · simp; intro x _
        exact f_neg (ne_of_gt a_pos)
      · simp [rpow_nonneg_of_nonneg (le_of_lt two_pos)]
      · simp only [Set.mem_Ici, zero_le_one]
      · exact rpow_lt_one_of_one_lt_of_neg one_lt_two i_neg
    · apply mul_pos (mul_pos _ ypos1) (pow_pos ypos1 2)
      rw [← rpow_add two_pos]
      exact one_plus_two_pow_pos _

lemma monotoneOn_E_i {r} (hr : 0 ≤ r) : MonotoneOn (fun i => E i r) (Set.Iic 0) := by
  rcases lt_or_eq_of_le hr with h | h
  · exact StrictMonoOn.monotoneOn $ strictMonoOn_E_i h
  · simp [← h, err_eq_zero]
    exact monotoneOn_const

/- Lemma 5.1 -/

lemma err_taylor {i r Δ} (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r ≤ Δ) : |E i r| ≤ E 0 Δ := by
  rw [abs_of_nonneg (err_nonneg hr1)]
  have := monotoneOn_E_i hr1 hi Set.right_mem_Iic hi
  apply le_trans this
  exact monotoneOn_E_r hr1 (le_trans hr1 hr2) hr2

/-****************************************************************************************-/

lemma h_pos (i:ℝ) (r:ℝ) (hr: r>0) :  h r i >0 :=by
  have ie: (2:ℝ)^i > 0:= by apply rpow_pos_of_pos; linarith
  have ie2: log 2 >0:= by apply log_pos; linarith
  have eq: h r i = (E i r) * (2^i +1) * log 2:= by
    unfold E; unfold h;
    rw[deriv_phi]
    unfold Φ
    unfold logb
    unfold f
    simp; field_simp;
    have t1: (2:ℝ)^(i-r) = 2^i * 2^(-r) :=by apply rpow_add ; linarith
    rw[← t1]; ring_nf;
  rw[eq]
  apply mul_pos; apply mul_pos;
  any_goals linarith;
  have t1:  StrictMonoOn (E i) (Set.Ici 0):= by exact strictMonoOn_E_r
  have ie3 : (E i) 0 < (E i) r := by apply t1; simp;simp; linarith; linarith;
  have e2 : (E i) 0  = 0:= by unfold E; rw[deriv_phi]; unfold Φ; simp
  linarith

lemma dh_pos (i:ℝ) (r:ℝ) (hi: i ≤ 0) (hr: r>0) :  deriv (fun i ↦ h r i) i  >0 :=by
  have diffE : DifferentiableAt ℝ (fun i ↦ er r i) i := by
    unfold er
    unfold E
    apply DifferentiableAt.add
    apply DifferentiableAt.sub
    apply DifferentiableAt.comp
    unfold logb; apply DifferentiableAt.div; apply DifferentiableAt.log; any_goals simp
    have: (2:ℝ)^(i-r) > 0 := by  apply rpow_pos_of_pos; linarith
    any_goals linarith;
    apply DifferentiableAt.rpow;simp; apply DifferentiableAt.sub; any_goals simp
    apply differentiable_phi
    rw[deriv_phi]; apply DifferentiableAt.mul; apply differentiableAt_const; simp;
    apply DifferentiableAt.div; apply DifferentiableAt.rpow; apply differentiableAt_const;
    apply differentiableAt_id; simp;  apply DifferentiableAt.add;  apply differentiableAt_const;
    apply DifferentiableAt.rpow; any_goals simp;
    have t2: (2:ℝ)^i > 0 := by  apply rpow_pos_of_pos; linarith
    linarith
  have eq: (fun i => h r i) = fun i => (er r i) * (2^i +1) * log 2:= by
    ext i
    unfold er
    unfold E; unfold h;
    rw[deriv_phi]
    unfold Φ
    unfold logb
    unfold f
    simp; field_simp;
    have t1: (2:ℝ)^(i-r) = 2^i * 2^(-r) :=by apply rpow_add ; linarith
    rw[← t1]; ring_nf;
  rw[eq]
  rw[deriv_mul, deriv_const]; simp;
  rw[deriv_mul, deriv_add, deriv_two_pow, deriv_const]
  simp;
  have t1: deriv (fun i ↦ er r i) i > 0 := by apply deriv_er_pos; linarith; linarith
  have t2: (2:ℝ)^i > 0 := by  apply rpow_pos_of_pos; linarith
  have t3: (2:ℝ)^i + 1 > 0 := by   linarith
  have t4: log 2 >0 := by apply log_pos; linarith
  have t5: (2:ℝ)^i * log 2 >0 := by apply mul_pos; assumption; assumption
  have t6: (deriv (fun i ↦ er r i) i) * (2 ^ i + 1) > 0 := by apply mul_pos; assumption ; assumption;
  have t7: er r i ≥ 0 := by unfold er; apply (err_nonneg); linarith
  have t8: er r i * (2 ^ i * log 2) ≥ 0 :=by apply mul_nonneg; assumption; linarith;
  apply mul_pos; linarith; assumption;
  any_goals simp;
  any_goals apply DifferentiableAt.rpow
  any_goals simp;
  assumption;
  apply DifferentiableAt.mul; assumption; apply DifferentiableAt.add; apply DifferentiableAt.rpow
  any_goals simp



lemma gb_g (i:ℝ) :  g i  = (gb (2^i) (log (2^i +1)))  ∘ (fun r=>2^r):=by
  ext r; simp;
  unfold g
  unfold gb
  have ie1: (2:ℝ)^i >0 := by apply rpow_pos_of_pos; linarith
  have ie2: (2:ℝ)^r >0 := by apply rpow_pos_of_pos; linarith
  have ie3: (2:ℝ)^i + 2^r ≠ 0 := by linarith
  have t21: (2:ℝ)^(i-r) = 2^i / 2^r :=by apply rpow_sub ; linarith
  have t2: (2:ℝ)^(i-r) + 1 = (2^i + 2^r)/2^r :=by
      rw[t21]; field_simp;
  have t33: log ((2 ^ i + 2 ^ r) / 2 ^ r) = log (2 ^ i + 2 ^ r) - log (2^r) := by
      apply log_div ; linarith; linarith;
  have t11: log (2 ^ r) = r * log 2 :=by apply log_rpow; linarith
  have t1: (h r i) * ((2^(i-r) +1 )* (2^r)) = (gbn (2^i) (log (2^i +1)) (2^r)) :=by
    unfold h
    unfold gbn
    unfold f
    rw[t11];
    rw[t2]
    have t3: log (2 ^ i * 2 ^ (-r) + 1) = (-(r * log 2) + log (2 ^ i + 2 ^ r)):=by
      have t31: (2:ℝ)^ (-r) = (2 ^ r)⁻¹  := by apply rpow_neg; linarith
      rw[t31]
      have t32: (2:ℝ) ^ i * (2 ^ r)⁻¹ + 1 = (2 ^ i + 2 ^ r)/ (2 ^ r) :=by field_simp;
      rw[t32]
      rw[t33,t11]; ring;
    rw[t3]
    field_simp; ring;
  have t22: (dih r i) *((2^(i-r) +1 )* (2^r)) = (gbd (2^i) (log (2^i +1)) (2^r)):=by
    unfold dih
    unfold gbd
    field_simp;
    rw[t2];
    rw[t33,t11,t21]; field_simp; ring_nf; simp;
  rw[← t1, ← t22];
  have t4: h r i * ((2 ^ (i - r) + 1) * 2 ^ r) / (dih r i * ((2 ^ (i - r) + 1) * 2 ^ r)) = h r i / dih r i := by
    apply mul_div_mul_right
    have iex : (2:ℝ)^(i-r) > 0 := by apply rpow_pos_of_pos; linarith
    have ie: ((2:ℝ) ^ (i - r) + 1) * 2 ^ r >0 := by apply mul_pos; linarith; linarith
    linarith
  rw [t4]

lemma deriv_pow2 (x : ℝ) : deriv (fun x=>(2 : ℝ) ^ x ) x = (2 : ℝ) ^ x * log 2 :=
  HasDerivAt.deriv (hasDerivAt_two_pow x)

lemma deriv_g_le0 (i:ℝ) (r:ℝ) (hr : r>0): (deriv (g i)) r <= 0 := by
  have ie1: (2:ℝ)^i >0 := by apply rpow_pos_of_pos; linarith
  have ie2: (2:ℝ)^r >0 := by apply rpow_pos_of_pos; linarith
  have t1: (deriv (g i)) r = (deriv (gb (2^i) (log (2^i +1)))) (2^r) * 2^r * log 2:= by
    rw[gb_g i]; rw[deriv.comp, deriv_pow2]; ring;
    unfold gb
    any_goals apply DifferentiableAt.div;
    unfold gbn
    any_goals apply DifferentiableAt.mul
    any_goals apply DifferentiableAt.add
    any_goals apply DifferentiableAt.rpow
    any_goals apply DifferentiableAt.mul
    any_goals simp
    any_goals apply DifferentiableAt.add
    any_goals apply DifferentiableAt.mul
    any_goals apply DifferentiableAt.log
    any_goals simp
    any_goals apply DifferentiableAt.add
    any_goals simp
    any_goals linarith
    have t2: gbd (2 ^ i) (log (2 ^ i + 1)) (2 ^ r) > 0 := by
      apply gbd_pos ; any_goals linarith;
      apply one_lt_rpow; any_goals linarith;
    linarith;
  rw[t1]
  have ie2 : log 2 > 0 := by apply log_pos; linarith
  have ie3: deriv (gb (2 ^ i) (log (2 ^ i + 1))) (2 ^ r) <=0 := by
    apply deriv_gb_le0 (2 ^ i) (log (2 ^ i + 1)) (2 ^ r)
    any_goals simp;
    any_goals linarith;
    apply one_lt_rpow; linarith; linarith;
  have tx: deriv (gb (2 ^ i) (log (2 ^ i + 1))) (2 ^ r) * 2 ^ r * log 2 =
         (2 ^ r * log 2) * deriv (gb (2 ^ i) (log (2 ^ i + 1))) (2 ^ r) :=by ring;
  rw[tx]
  apply Linarith.mul_nonpos; linarith; apply mul_pos; linarith; linarith;


lemma gAnti (hi: i ≤ 0) : AntitoneOn (g i) (Set.Ioi (0:ℝ)):=by
  have hd: DifferentiableOn ℝ (g i) (Set.Ioi (0:ℝ)):=by
    unfold g ; unfold h;  unfold f;
    apply DifferentiableOn.div
    any_goals apply DifferentiableOn.add
    any_goals apply DifferentiableOn.sub
    any_goals apply DifferentiableOn.mul
    any_goals apply DifferentiableOn.mul
    any_goals apply DifferentiableOn.add
    any_goals apply DifferentiableOn.rpow
    any_goals apply DifferentiableOn.mul
    any_goals simp;
    any_goals apply DifferentiableOn.log
    any_goals apply DifferentiableOn.add
    any_goals apply DifferentiableOn.mul
    any_goals apply DifferentiableOn.rpow;
    any_goals apply DifferentiableOn.add
    any_goals apply DifferentiableOn.mul
    any_goals apply DifferentiableOn.rpow
    any_goals apply DifferentiableOn.inv
    any_goals simp;
    any_goals apply DifferentiableOn.sub
    any_goals apply DifferentiableOn.log
    any_goals apply DifferentiableOn.add
    any_goals apply DifferentiableOn.rpow
    any_goals apply DifferentiableOn.sub
    any_goals apply DifferentiableOn.neg
    any_goals apply differentiableOn_id
    any_goals exact differentiableOn_const 1
    any_goals exact differentiableOn_const 2
    any_goals exact differentiableOn_const i
    any_goals intro x hx
    any_goals have iei : (2:ℝ)^i > 0 := by apply rpow_pos_of_pos; linarith
    any_goals have iex : (2:ℝ)^(-x) > 0 := by apply rpow_pos_of_pos; linarith
    any_goals have ieix : (2:ℝ)^(i-x) > 0 := by apply rpow_pos_of_pos; linarith
    any_goals have iex : (2:ℝ)^i * (2:ℝ)^(-x) > 0 := by apply mul_pos; linarith; linarith;
    any_goals linarith
    rw[← deriv_h]
    have h1: deriv (h x) i>0:= by apply dh_pos; linarith; assumption;
    linarith;

  have dc: ContinuousOn (g i) (Set.Ioi (0:ℝ)):= DifferentiableOn.continuousOn hd

  apply Convex.antitoneOn_of_deriv_nonpos (convex_Ioi (0:ℝ))
  assumption; rw[interior_Ioi]; assumption
  rw[interior_Ioi]
  intro x hx;
  have ht: x>0 := Set.mem_Ioi.mp hx
  apply deriv_g_le0; assumption

lemma hdih_ie (hi: i ≤ 0)  (hr: r>0) (hΔ : r< Δ) :
        h Δ i / deriv (fun i ↦ h Δ i) i ≤ h r i /deriv (fun i ↦ h r i) i  := by
  have h1: (h Δ i) / deriv (fun i ↦ h Δ i) i = g i Δ  :=by
    unfold g; rw[deriv_h];
  have h2: (h r i) / deriv (fun i ↦ h r i) i = g i r  :=by
    unfold g; rw[deriv_h];
  rw[h1,h2]
  apply gAnti hi;
  any_goals simp
  any_goals linarith



/- ****************************************** -/
/- ****************************************** -/
/- ****************************************** -/
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

lemma q_eq2 : (fun i => Q Δ i r) = (fun i=>h r i / h Δ i) := by
  unfold h
  ext i
  rw[q_eq]


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

lemma dfh (r:ℝ) : Differentiable ℝ (fun i ↦ h r i ):=by
    unfold h
    unfold f
    apply Differentiable.add
    apply Differentiable.sub
    any_goals apply Differentiable.mul
    any_goals apply Differentiable.log
    any_goals apply Differentiable.add
    any_goals apply Differentiable.mul
    any_goals apply Differentiable.rpow
    any_goals simp;
    any_goals intro x
    have ie: (2:ℝ)^x > 0:= by apply rpow_pos_of_pos; linarith
    linarith
    have ie: (2:ℝ)^x > 0:= by apply rpow_pos_of_pos; linarith
    have ie1: (2:ℝ)^(-r) > 0:= by apply rpow_pos_of_pos; linarith
    have ie2: (2:ℝ) ^ x * 2 ^ (-r) >0 :=by apply mul_pos; linarith; linarith;
    linarith





/-SUPPORTING 6.3******************************************************************************* -/

def T X := 1/X + log X -1

def H X:= 2*log (1+X) - log X - 2* log 2

def F X R:= (T R) / (T X) - (H R) / (H X)

def B X := X*(H X)

def A X := (B X) - X*(T X)

def Root X := - (B X/ A X)


lemma F_eq_Q :  F  (2^Δ) (2^r) = Q_hi Δ r - Q_lo Δ r := by
  have e11: 1/(2:ℝ)^r = 2^(-r) :=by
      field_simp;
      have e111: (2:ℝ) ^ (-r) * 2 ^ r = 1 :=by
        rw[← rpow_add];
        have : -r + r = 0 := by simp;
        rw[this]; apply rpow_zero; linarith
      linarith

  have e12: 1/(2:ℝ)^Δ = 2^(-Δ) :=by
      field_simp;
      have e111: (2:ℝ) ^ (-Δ) * 2 ^ Δ = 1 :=by
        rw[← rpow_add];
        have : -Δ + Δ = 0 := by simp;
        rw[this]; apply rpow_zero; linarith
      linarith
  have i0: (2:ℝ)^(r) > 0 :=by apply rpow_pos_of_pos; linarith
  have i1: (2:ℝ)^(Δ) > 0 :=by apply rpow_pos_of_pos; linarith
  have e13: log (2 ^ r) = r * log 2:= by apply log_rpow; linarith
  have e14: log (2 ^ Δ) = Δ * log 2:= by apply log_rpow; linarith
  have e1: (T (2^r)) / (T (2^Δ))  = Q_hi Δ r :=by
    unfold Q_hi T
    rw[e11, e12, e13, e14]

  have e2: (H (2^r)) / (H (2^Δ))  = Q_lo Δ r :=by
    unfold Q_lo Q E
    simp;
    have e21: Φ 0 = 1 :=by
      unfold Φ; simp; unfold logb;
      have : (1:ℝ)+1 = 2 := by linarith;
      rw[this]; field_simp;
    rw[e21]
    have e22: deriv Φ 0 = 1/(2:ℝ) :=by
      rw[deriv_phi]; simp; linarith;
    rw[e22]
    have e23: Φ (-r) = (log (1+2^r) - log (2^r))/ log 2:=by
      unfold Φ
      have : 1+(2:ℝ)^(-r) = (1+2^r)/(2^r):=by
        rw[← e11]; field_simp; ring_nf
      unfold logb; rw[this]; field_simp;
      apply log_div; linarith; linarith;

    have e24: Φ (-Δ) = (log (1+2^Δ) - log (2^Δ))/ log 2:=by
      unfold Φ
      have : 1+(2:ℝ)^(-Δ) = (1+2^Δ)/(2^Δ):=by
        rw[← e12]; field_simp; ring_nf
      unfold logb; rw[this]; field_simp;
      apply log_div; linarith; linarith;
    have e25: Φ (-r) - 1 + r * (1 / 2) =  (H (2 ^ r)) / (2 *log 2):=by
      unfold H;
      rw[e23, e13]
      field_simp; ring_nf
    have e26: Φ (-Δ) - 1 + Δ * (1 / 2) =  (H (2 ^ Δ)) / (2 *log 2):=by
      unfold H;
      rw[e24, e14]
      field_simp; ring_nf
    rw[e25,e26]
    field_simp;
  unfold F; rw[e1,e2]


lemma Root_eq_t : logb 2 (Root (2^Δ)) = R_opt Δ :=by
  unfold R_opt;
  simp;
  unfold Root
  set X := (2:ℝ)^Δ
  have i1: X>0 :=by apply rpow_pos_of_pos; linarith
  have e1: -(X * (2 * log (X + 1) - log X - 2 * log 2)) = -(B X):=by
    unfold B H; ring_nf;
  rw[e1]
  have e2: (2 * X * (log (X + 1) - log X - log 2) + X - 1) = A X:=by
    unfold A B H T;
    field_simp; ring_nf
  rw[e2]
  have e3: -(B X / A X) = -B X / A X :=by field_simp;
  rw[e3]




lemma differentiable_T : DifferentiableOn ℝ T (Set.Ici (1:ℝ)):= by
  unfold T;
  apply DifferentiableOn.sub
  apply DifferentiableOn.add
  apply DifferentiableOn.div
  any_goals apply DifferentiableOn.log
  any_goals apply differentiableOn_const
  any_goals apply differentiableOn_id
  any_goals simp
  any_goals intro x hx
  any_goals linarith


lemma deriv_T (hx : X>1) : deriv T X = (X-1)/(X^2) := by
  unfold T
  simp
  rw[deriv_sub, deriv_add, deriv.log, deriv_inv]
  simp
  field_simp;
  ring_nf; simp; linarith;
  apply DifferentiableAt.inv; simp; linarith;
  apply DifferentiableAt.log; simp; linarith;
  apply DifferentiableAt.add; apply DifferentiableAt.inv; simp; linarith;
  apply DifferentiableAt.log; simp; linarith; simp

lemma T_1 : T 1 = 0 := by simp [T]

lemma T_pos (hx : X > 1) : T X > 0 := by
  rw [← T_1]
  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici 1)
  apply DifferentiableOn.continuousOn differentiable_T
  any_goals simp;
  any_goals linarith;
  intro x h
  rw[deriv_T]
  apply div_pos; linarith;
  apply pow_pos; linarith; linarith

lemma differentiable_H : DifferentiableOn ℝ H (Set.Ici (1:ℝ)):= by
  unfold H
  apply DifferentiableOn.sub
  apply DifferentiableOn.sub
  apply DifferentiableOn.mul
  any_goals apply DifferentiableOn.log
  any_goals apply DifferentiableOn.add
  any_goals apply differentiableOn_const
  any_goals apply differentiableOn_id
  any_goals simp;
  any_goals intro x hx
  any_goals linarith


lemma deriv_H (hx : X>1) : deriv H X = (X-1)/(X*(X+1)) := by
  unfold H
  rw[deriv_sub, deriv_sub, deriv_mul, deriv.log, deriv_add]; simp
  field_simp; ring_nf
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.neg
  any_goals apply DifferentiableAt.log
  any_goals apply DifferentiableAt.add
  any_goals apply differentiableAt_const
  any_goals apply differentiableAt_id
  any_goals linarith

lemma H_1 : H (1:ℝ) = 0 := by unfold H; simp; ring_nf;

lemma H_pos (hx : X > 1) : H X > 0 := by
  rw [← H_1]
  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici 1)
  apply DifferentiableOn.continuousOn differentiable_H
  any_goals simp;
  any_goals linarith;
  intro x h
  rw[deriv_H]
  apply div_pos; linarith;
  apply mul_pos
  any_goals linarith;

def C X := 2*X/(X+1) -2*log X + 2*log (X+1) - 2*log 2 -1

lemma deriv_A (hx : X>1) : deriv A X = C X := by
  unfold C
  unfold A
  unfold B
  rw[deriv_sub, deriv_mul];
  rw[deriv_H, deriv_mul, deriv_T]; simp;
  unfold H
  unfold T
  field_simp;
  ring_nf;
  any_goals simp;
  any_goals apply DifferentiableAt.mul
  any_goals simp;
  any_goals linarith;
  any_goals apply DifferentiableAt.sub
  any_goals apply DifferentiableAt.sub
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.log
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.inv
  any_goals apply differentiableAt_const
  any_goals apply differentiableAt_id
  any_goals linarith;


lemma deriv_C (hx : X>1) : deriv C X = -2/(X*(X+1)^2) := by
  unfold C
  rw[deriv_sub, deriv_sub, deriv_add, deriv_sub, deriv_mul, deriv_div]; simp;
  rw[deriv_mul, deriv.log, deriv_add]; simp;
  field_simp;
  ring_nf;
  any_goals simp;
  any_goals linarith;
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.inv
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.sub
  any_goals apply DifferentiableAt.div
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.sub
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.inv
  any_goals apply DifferentiableAt.log
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.add
  any_goals apply differentiableAt_const
  any_goals apply differentiableAt_id
  any_goals linarith;

lemma differentiable_C : DifferentiableOn ℝ C (Set.Ici (1:ℝ)):= by
  unfold C
  apply DifferentiableOn.sub
  apply DifferentiableOn.sub
  apply DifferentiableOn.add
  apply DifferentiableOn.sub
  apply DifferentiableOn.div
  any_goals apply DifferentiableOn.mul
  any_goals apply DifferentiableOn.log
  any_goals apply DifferentiableOn.add
  any_goals apply differentiableOn_const
  any_goals apply differentiableOn_id
  any_goals simp
  any_goals intro x hx
  any_goals linarith


lemma C_1 : C 1  = 0 :=by unfold C; ring_nf; simp

lemma C_neg (hx : X > 1) : C X < 0 := by
  rw [← C_1]
  apply Convex.strictAntiOn_of_deriv_neg (convex_Ici 1)
  apply DifferentiableOn.continuousOn differentiable_C
  any_goals simp;
  any_goals linarith;
  intro x h
  rw[deriv_C]
  have ha : 0 < 2 / (x * (x + 1) ^ 2)  :=by
    apply div_pos; linarith; apply mul_pos; linarith; apply pow_pos; linarith
  apply neg_of_neg_pos
  have : -(-2 / (x * (x + 1) ^ 2)) = 2 / (x * (x + 1) ^ 2) :=by ring_nf;
  rw[this]; assumption; assumption

lemma A_1 : A 1  = 0 :=by unfold A; unfold B; rw[T_1, H_1]; ring_nf;

lemma differentiable_A : DifferentiableOn ℝ A (Set.Ici (1:ℝ)):= by
  unfold A
  apply DifferentiableOn.sub
  unfold B
  any_goals apply DifferentiableOn.mul
  apply differentiableOn_id
  exact differentiable_H
  apply differentiableOn_id
  exact differentiable_T

lemma A_neg (hx : X > 1) : A X < 0 := by
  rw [← A_1]
  apply Convex.strictAntiOn_of_deriv_neg (convex_Ici 1)
  apply DifferentiableOn.continuousOn differentiable_A
  simp;
  intro x hx
  rw[deriv_A]
  exact C_neg hx
  any_goals simp;
  any_goals linarith;


lemma FX_1 : F X 1 = 0 :=by unfold F; rw[T_1, H_1]; simp;

lemma FX_X  (hx: X>1): F X X = 0 :=by
  unfold F;
  have h1: T X > 0 := T_pos hx
  have h2: H X > 0 := H_pos hx
  field_simp

lemma F_eq (hx: X>1) : F X  = fun R => (T R)*(X/(B X - A X)) - (H R)*(X/(B X)) := by
  ext R
  have h1: T X > 0 := T_pos hx
  have h2: H X > 0 := H_pos hx
  unfold A
  unfold B
  unfold F
  field_simp; ring_nf;

def D X R := (R-1)/((B X)*(R^2)*(T X)*(R+1))

lemma D_pos  (hr: R > 1) (hxr: R < X) : D X R > 0 :=by
  have hx : X > 1 :=by linarith
  have hx0 : X>0 :=by linarith
  have h1: T X > 0 := T_pos hx
  have h2: H X > 0 := H_pos hx
  have h3: B X > 0 := by unfold B; apply mul_pos; linarith; linarith
  apply div_pos; linarith;
  apply mul_pos; apply mul_pos; apply mul_pos;
  any_goals linarith;
  apply pow_pos; linarith

lemma deriv_F (hr: R > 1) (hxr: R < X) : deriv (F X) R = (D X R)*((A X)*R + B X):= by
  unfold D
  have hx : X > 1 :=by linarith
  have hx0 : X>0 :=by linarith
  have h1: T X > 0 := T_pos hx
  have h2: H X > 0 := H_pos hx
  have h3: B X > 0 := by unfold B; apply mul_pos; linarith; linarith
  have d1: DifferentiableAt ℝ (fun R ↦ H R) R :=by
    apply DifferentiableAt.sub;apply DifferentiableAt.sub;
    any_goals apply DifferentiableAt.mul
    any_goals apply DifferentiableAt.log
    any_goals apply DifferentiableAt.add
    any_goals simp
    any_goals linarith
  have d2: DifferentiableAt ℝ (fun R ↦ T R) R :=by
    apply DifferentiableAt.sub;apply DifferentiableAt.add;apply DifferentiableAt.div;
    simp; simp; linarith; apply DifferentiableAt.log; simp; linarith; simp;
  rw[F_eq hx]
  rw[deriv_sub, deriv_mul, deriv_mul]
  rw[deriv_T hr, deriv_H hr]
  simp;
  have e1 : X / (B X - A X) = 1/T X  :=by unfold A; field_simp;
  rw[e1]; field_simp;
  have e3: ((R - 1) * (R * (R + 1) * B X) - R ^ 2 * T X * ((R - 1) * X)) =   (R - 1) * (A X * R + B X)*R :=by
    have e: T X = (B X - A X)/X :=by unfold A; field_simp; ring_nf;
    rw[e]; field_simp;  ring_nf;
  rw[e3]; ring_nf;
  assumption; apply DifferentiableAt.div; simp;
  unfold B; apply DifferentiableAt.mul; simp; simp; linarith
  assumption; simp;  apply DifferentiableAt.mul; assumption; simp;
  apply DifferentiableAt.mul; assumption;simp;

def M X := 2 * H X -T X

lemma differentiable_M : DifferentiableOn ℝ M (Set.Ici (1:ℝ)):= by
  unfold M
  apply DifferentiableOn.sub
  apply DifferentiableOn.mul
  apply differentiableOn_const
  exact differentiable_H
  exact differentiable_T


lemma M_1 : M (1:ℝ) = 0 := by unfold M; rw[H_1,T_1]; simp;

lemma deriv_M (hx : X>1) : deriv M X = (X-1)^2/(X^2*(X+1)) := by
  unfold M; rw[deriv_sub, deriv_mul]
  rw[deriv_H hx, deriv_T hx]; simp;
  field_simp; ring_nf
  simp;
  apply DifferentiableOn.differentiableAt differentiable_H;
  apply Ici_mem_nhds; assumption;
  apply DifferentiableAt.mul; simp;
  apply DifferentiableOn.differentiableAt differentiable_H;
  apply Ici_mem_nhds; assumption;
  apply DifferentiableOn.differentiableAt differentiable_T;
  apply Ici_mem_nhds; assumption;

lemma M_pos (hx : X > 1) : M X > 0 := by
  rw [← M_1]
  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici 1)
  apply DifferentiableOn.continuousOn differentiable_M
  any_goals simp;
  any_goals linarith;
  intro x h
  rw[deriv_M]
  apply div_pos; apply pow_pos; linarith;
  apply mul_pos; apply pow_pos;
  any_goals linarith;

lemma Root_gt_1 (hx : X > 1) : Root X >1 :=by
  unfold Root;
  have hA: A X < 0 := by exact A_neg hx
  have e1 : -(B X / A X) = (B X )/ (-(A X)) :=by  ring_nf;
  rw[e1]
  have ie1 : (-(A X)) > 0 :=by linarith
  apply (one_lt_div ie1).mpr
  have e2 : A X + B X = X*M X := by unfold A; unfold B; unfold M; ring_nf;
  have ie2 : A X + B X > 0 := by rw[e2]; apply mul_pos; linarith; exact M_pos hx
  linarith



def K X := H X - T X

lemma differentiable_K : DifferentiableOn ℝ K (Set.Ici (1:ℝ)):= by
  unfold K
  apply DifferentiableOn.sub
  exact differentiable_H
  exact differentiable_T

lemma K_1 : K 1 = 0 :=by unfold K;  rw[H_1, T_1]; simp

lemma K_neg (hx : X > 1) : K X < 0 := by
  rw [← K_1]
  apply Convex.strictAntiOn_of_deriv_neg (convex_Ici 1)
  apply DifferentiableOn.continuousOn differentiable_K
  any_goals simp;
  any_goals linarith;
  intro x h
  unfold K; rw[deriv_sub, deriv_T, deriv_H]
  have e1: (x - 1) / (x * (x + 1)) - (x - 1) / x ^ 2  = -((x-1)/(x^2*(x+1))) := by field_simp; ring_nf
  rw[e1];
  have i1: (x-1)/(x^2*(x+1)) >0 := by apply div_pos; linarith; apply mul_pos; apply pow_pos; linarith;linarith
  any_goals linarith;
  apply DifferentiableOn.differentiableAt differentiable_H;
  apply Ici_mem_nhds; assumption;
  apply DifferentiableOn.differentiableAt differentiable_T;
  apply Ici_mem_nhds; assumption;

def N X := (X+1)* H X -  X * T X

lemma differentiable_N : DifferentiableOn ℝ N (Set.Ici (1:ℝ)):= by
  unfold N
  apply DifferentiableOn.sub
  apply DifferentiableOn.mul
  apply DifferentiableOn.add;
  apply differentiableOn_id
  apply differentiableOn_const
  exact differentiable_H
  apply DifferentiableOn.mul
  apply differentiableOn_id
  exact differentiable_T

lemma deriv_N (hx : X > 1) : deriv N X = K X :=by
  have diffH : DifferentiableAt ℝ (fun y ↦ H y) X := by
    apply DifferentiableOn.differentiableAt differentiable_H; apply Ici_mem_nhds; assumption;
  have diffT : DifferentiableAt ℝ (fun y ↦ T y) X := by
    apply DifferentiableOn.differentiableAt differentiable_T; apply Ici_mem_nhds; assumption;
  unfold N; unfold K;
  rw[deriv_sub, deriv_mul, deriv_H, deriv_mul, deriv_T]; simp;
  unfold H; unfold T;
  field_simp; ring_nf;
  assumption; simp; assumption ; assumption
  apply DifferentiableAt.add; simp; simp;
  assumption;
  any_goals apply DifferentiableAt.mul;  apply DifferentiableAt.add
  any_goals simp;
  assumption; apply DifferentiableAt.mul; simp; assumption ;

lemma N_1 : N 1 = 0 :=by unfold N; rw[H_1, T_1]; simp;

lemma N_neg (hx : X > 1) : N X < 0 := by
  rw [← N_1]
  apply Convex.strictAntiOn_of_deriv_neg (convex_Ici 1)
  apply DifferentiableOn.continuousOn differentiable_N
  any_goals simp;
  any_goals linarith;
  intro x h
  rw[deriv_N h];
  exact K_neg h


lemma Root_lt_X (hx : X > 1) : Root X < X :=by
  unfold Root;
  have hA: A X < 0 := by exact A_neg hx
  have hA1: -A X > 0 := by linarith
  have e0: -(B X + X * (A X)) = X*(- N X) :=by
    unfold A; unfold B; unfold N; field_simp; ring_nf
  have h0: -(B X + X * (A X)) >0  := by rw[e0]; apply mul_pos; linarith; simp; exact N_neg hx
  have h1: B X < X* (- A X) :=by  simp; linarith
  have h2: B X/ (-A X) < X* (- A X)/ (-A X) :=by apply div_lt_div_of_lt hA1 h1
  have e1:  X* (- A X)/ (-A X) = X :=by field_simp
  linarith




lemma mainlem63 (hr: R > 1) (hxr: R < X) :  F X R ≤ F X (Root X) := by

  have hx : X > 1 :=by linarith
  have hA: A X < 0 := by exact A_neg hx
  have diff : DifferentiableOn ℝ (F X) (Set.Ici (1:ℝ)):= by
    unfold F
    apply DifferentiableOn.sub
    any_goals apply DifferentiableOn.div
    exact differentiable_T
    apply differentiableOn_const
    simp; intro x h1
    have : T X > 0 := T_pos hx
    linarith;
    exact differentiable_H
    apply differentiableOn_const
    simp; intro x h1
    have : H X > 0 := H_pos hx
    linarith;

  have hroot1: Root X >1 :=by exact Root_gt_1 hx

  have hroot2: Root X < X :=by exact Root_lt_X hx

  have diff1 : DifferentiableOn ℝ (F X) (Set.Icc 1 (Root X)):= by
    apply DifferentiableOn.mono diff
    apply Set.Icc_subset_Ici_self

  have diff2 : DifferentiableOn ℝ (F X) (Set.Icc (Root X) X):= by
    apply DifferentiableOn.mono diff
    have h1: Set.Icc (Root X) X ⊆ Set.Ici (Root X)  :=by apply Set.Icc_subset_Ici_self
    have h2: Set.Ici (Root X)  ⊆ Set.Ici 1 := by apply Set.Ici_subset_Ici.mpr; linarith;
    exact subset_trans h1 h2

  have firsthalf: R ≤ Root X → F X R ≤ F X (Root X) := by
    intro hr1
    apply Convex.monotoneOn_of_deriv_nonneg (convex_Icc (1:ℝ) (Root X))
    apply DifferentiableOn.continuousOn diff1
    apply DifferentiableOn.mono diff1
    apply interior_subset
    simp;
    intro x h1 h2
    have h3: x<X :=by linarith
    rw[deriv_F h1 h3]
    apply mul_nonneg; apply le_of_lt; exact D_pos h1 h3
    have h4: A X * Root X  < A X * x := by apply mul_lt_mul_of_neg_left h2 hA
    have h5: A X * Root X  + B X < A X * x + B X :=by linarith
    have h51 : A X ≠ 0 := by linarith;
    have h6: A X * Root X  + B X = 0 := by unfold Root; field_simp; ring_nf;
    linarith;
    simp;
    have t1: 1 ≤ R :=by linarith;
    exact And.intro t1 hr1
    simp; linarith; assumption
  apply by_cases firsthalf; simp;

  have secondhalf (hr2: Root X < R ) : F X R ≤ F X (Root X) := by
    apply Convex.antitoneOn_of_deriv_nonpos (convex_Icc (Root X) X)
    apply DifferentiableOn.continuousOn diff2
    apply DifferentiableOn.mono diff2
    apply interior_subset
    simp;
    intro x h1 h2
    have h3: x>1 :=by linarith
    rw[deriv_F h3 h2] ;
    have hdd:  D X x * (-(A X * x + B X)) ≥ 0 :=by
      apply mul_nonneg; apply le_of_lt; exact D_pos h3 h2
      have h4: A X * x  < A X * Root X := by apply mul_lt_mul_of_neg_left h1 hA
      have h5: A X * x  + B X < A X * Root X + B X :=by linarith
      have h51 : A X ≠ 0 := by linarith;
      have h6: A X * Root X  + B X = 0 := by unfold Root; field_simp; ring_nf;
      linarith;
    linarith;
    simp; linarith;
    simp;
    have t1: Root X ≤ R :=by linarith;
    have t2: R ≤ X :=by linarith;
    exact And.intro t1 t2; linarith;

  intro hr2
  exact secondhalf hr2


lemma Root_eq_R_opt (hΔ : Δ >0):  2^(R_opt Δ) = Root (2^Δ)  :=by
  rw[← Root_eq_t]
  apply rpow_logb;
  linarith; linarith;
  have : Root (2 ^ Δ) > 1 := by
    apply Root_gt_1; apply one_lt_rpow
    any_goals linarith;
  linarith



lemma lemma63sub  (hr1 : 0 < r) (hr2 : r < Δ) :
    Q_hi Δ r - Q_lo Δ r ≤ Q_hi Δ (R_opt Δ) - Q_lo Δ (R_opt Δ) := by
  rw[← F_eq_Q, ← F_eq_Q , Root_eq_R_opt]
  apply mainlem63
  apply one_lt_rpow; linarith; linarith
  apply rpow_lt_rpow_of_exponent_lt; linarith; assumption; linarith;


/-SUPPORTING 6.4******************************************************************************* -/


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


lemma err_pos  (hr : 0 < r) : 0 < E i r := by
  rw [(by simp [E] : 0 = E i 0)]
  apply (strictMonoOn_E_r) Set.left_mem_Ici;
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



def W c Δ r t := (E c r - E c (r-t)) / (E c Δ)

def Wt c Δ t r := W c Δ r t


lemma monoW (h1: r ≥ ΔP) (hr: r > 0) (ht0: 0 ≤ t) (htp: t ≤ ΔP)
       (htr: t ≤ r)  (htd: r ≤ Δ) : (W c Δ) r t ≤  (W c Δ) r ΔP := by
  have diffE : Differentiable ℝ (E c) := by
    apply Differentiable.add _ (by simp : _)
    apply Differentiable.sub_const
    intro x
    apply DifferentiableAt.comp_const_sub.mpr
    apply differentiable_phi
  have ep : E c Δ > 0 := by apply err_pos; linarith
  have ec : (fun y ↦ E c (r - y)) = (fun y=> E c y) ∘ (fun y=>r-y) :=by ext y; simp;
  have ec2 : (fun y ↦ E c (y - t)) = (fun y=> E c y) ∘ (fun y=>y-t) :=by ext y; simp;
  have diffW : DifferentiableOn ℝ (W c Δ r) (Set.Icc 0 r) := by
    unfold W
    apply DifferentiableOn.div; apply DifferentiableOn.sub; apply differentiableOn_const;
    apply Differentiable.differentiableOn
    rw[ec]
    apply Differentiable.comp; assumption;
    apply Differentiable.sub; simp; simp;
    apply differentiableOn_const;
    intro x hx
    linarith
  have monoW : MonotoneOn (W c Δ r) (Set.Icc 0 r) := by
    apply Convex.monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    apply DifferentiableOn.continuousOn diffW
    apply DifferentiableOn.mono diffW; simp;
    apply Set.Ioo_subset_Icc_self
    simp;
    intro x hx1 hx2; unfold W
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

  have first : (W c Δ) r t ≤  (W c Δ) r ΔP := by
    apply monoW
    any_goals simp;
    any_goals apply And.intro;
    any_goals linarith;
  assumption


lemma mainlem64 (hr: r>0) (ht0: 0 ≤ t) (htp: t ≤ ΔP) (htr: t ≤ r)
            (htd: r ≤ Δ) (hΔ:  ΔP ≤ Δ ): (W c Δ) r t ≤  (W c Δ) Δ ΔP:= by
  have diffE : Differentiable ℝ (E c) := by
    apply Differentiable.add _ (by simp : _)
    apply Differentiable.sub_const
    intro x
    apply DifferentiableAt.comp_const_sub.mpr
    apply differentiable_phi
  have ep : E c Δ > 0 := by apply err_pos; linarith
  have ec : (fun y ↦ E c (r - y)) = (fun y=> E c y) ∘ (fun y=>r-y) :=by ext y; simp;
  have ec2 : (fun y ↦ E c (y - t)) = (fun y=> E c y) ∘ (fun y=>y-t) :=by ext y; simp;
  have diffW : DifferentiableOn ℝ (W c Δ r) (Set.Icc 0 r) := by
    unfold W
    apply DifferentiableOn.div; apply DifferentiableOn.sub; apply differentiableOn_const;
    apply Differentiable.differentiableOn
    rw[ec]
    apply Differentiable.comp; assumption;
    apply Differentiable.sub; simp; simp;
    apply differentiableOn_const;
    intro x hx
    linarith


  have diffWt: DifferentiableOn ℝ  (Wt c Δ t)  (Set.Ici t) :=by
    unfold Wt
    unfold W
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


  have first : (W c Δ) r t ≤ (W c Δ) Δ t :=by
    rw[← Wt, ← Wt]
    apply Convex.monotoneOn_of_deriv_nonneg (convex_Ici t)
    apply DifferentiableOn.continuousOn diffWt
    apply DifferentiableOn.mono diffWt; simp;
    simp; intro x hx
    unfold Wt
    unfold W
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

  have second : (W c Δ) Δ t ≤ (W c Δ) Δ ΔP := by
    apply monoW;
    any_goals linarith;
  linarith

lemma W_pos  (ht0: 0 ≤ t) (htr: t ≤ r) :  W c Δ r t ≥ 0:= by
  have diffE : Differentiable ℝ (E c) := by
    apply Differentiable.add _ (by simp : _)
    apply Differentiable.sub_const
    intro x
    apply DifferentiableAt.comp_const_sub.mpr
    apply differentiable_phi
  have ep : E c Δ > 0 := by apply err_pos; linarith
  have ec : (fun y ↦ E c (r - y)) = (fun y=> E c y) ∘ (fun y=>r-y) :=by ext y; simp;
  have ec2 : (fun y ↦ E c (y - t)) = (fun y=> E c y) ∘ (fun y=>y-t) :=by ext y; simp;
  have diffW : DifferentiableOn ℝ (W c Δ r) (Set.Icc 0 r) := by
    unfold W
    apply DifferentiableOn.div; apply DifferentiableOn.sub; apply differentiableOn_const;
    apply Differentiable.differentiableOn
    rw[ec]
    apply Differentiable.comp; assumption;
    apply Differentiable.sub; simp; simp;
    apply differentiableOn_const;
    intro x hx
    linarith
  have e0: 0 = W c Δ r 0 := by unfold W; field_simp
  have monoW : MonotoneOn (W c Δ r) (Set.Icc 0 r) := by
    apply Convex.monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    apply DifferentiableOn.continuousOn diffW
    apply DifferentiableOn.mono diffW; simp;
    apply Set.Ioo_subset_Icc_self
    simp;
    intro x hx1 hx2; unfold W
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
  rw[e0];
  apply monoW
  any_goals simp;
  any_goals apply And.intro;
  any_goals linarith;

lemma W_eq_Q_Δ  (hΔ : Δ >0): 1 - Q Δ c (Δ - ΔP) = (W c Δ) Δ ΔP:=by
  unfold W Q;
  have ep : E c Δ > 0 := by apply err_pos; linarith
  field_simp;

lemma W_eq_Q  (hΔ : Δ >0):  Q Δ c r - Q Δ c rr = W c Δ r (r - rr) :=by
  unfold W Q; simp
  have ep : E c Δ > 0 := by apply err_pos; linarith
  field_simp;

lemma lemma64sub (hr: r>0) (ht0: 0 ≤ r - rr) (htp: r - rr ≤ ΔP) (hrr: rr ≥ 0)
            (htd: r ≤ Δ) (hΔ:  ΔP ≤ Δ ) :  |Q Δ c r - Q Δ c rr| ≤ 1 - Q Δ c (Δ - ΔP) :=by
  have e1: |Q Δ c r - Q Δ c rr| = Q Δ c r - Q Δ c rr := by
    apply abs_of_nonneg; rw[W_eq_Q]; apply W_pos;
    any_goals linarith
  rw[e1, W_eq_Q_Δ, W_eq_Q ];
  apply mainlem64
  any_goals linarith;

/-LEMMAS***************************************************************************************-/

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


lemma lemma62 (hr1 : 0 < r) (hr2 : r < Δ) : AntitoneOn (fun i => Q Δ i r) (Set.Iic 0) := by
  rw[q_eq2]
  have hpos : ∀ (x : ℝ), h Δ x ≠ 0 := by
    intro x
    have : h Δ x > 0 :=by apply h_pos x Δ; linarith;
    linarith;

  have df : Differentiable ℝ (fun i ↦ h r i / h Δ i):=by
    apply Differentiable.div
    exact dfh r
    exact dfh Δ
    assumption
  apply Convex.antitoneOn_of_deriv_nonpos  (convex_Iic (0:ℝ))

  apply Continuous.continuousOn
  exact Differentiable.continuous df
  apply Differentiable.differentiableOn
  assumption
  simp;
  intro x hx
  rw[deriv_div];apply div_nonpos_of_nonpos_of_nonneg
  any_goals apply hpos
  any_goals exact pow_two_nonneg  (h Δ x)
  any_goals apply Differentiable.differentiableAt
  any_goals exact dfh r
  any_goals exact dfh Δ
  simp;
  have t2 : deriv (fun i ↦ h r i) x  >0 := by apply dh_pos x r; linarith; linarith
  have t1 : deriv (fun i ↦ h Δ i) x  >0 := by apply dh_pos x Δ; linarith; linarith
  have t3 : h Δ x / deriv (fun i ↦ h Δ i) x ≤ h r x /deriv (fun i ↦ h r i) x :=by
    have h1: (h Δ x) / deriv (fun i ↦ h Δ i) x = g x Δ  :=by
      unfold g; rw[deriv_h];
    have h2: (h r x) / deriv (fun i ↦ h r i) x = g x r  :=by
      unfold g; rw[deriv_h];
    rw[h1,h2]
    apply gAnti;
    any_goals simp
    any_goals linarith

  have h0: 0 < deriv (fun i ↦ h Δ i) x *deriv (fun i ↦ h r i) x := by apply mul_pos; assumption; assumption;
  have h01: 0  ≤ deriv (fun i ↦ h Δ i) x *deriv (fun i ↦ h r i) x := by linarith;
  have h1:  (h Δ x / deriv (fun i ↦ h Δ i) x)*(deriv (fun i ↦ h Δ i) x *deriv (fun i ↦ h r i) x)
            ≤ (h r x / deriv (fun i ↦ h r i) x)*(deriv (fun i ↦ h Δ i) x *deriv (fun i ↦ h r i) x) := by
            apply mul_le_mul_of_nonneg_right t3 h01;
  have h2: (h Δ x / deriv (fun i ↦ h Δ i) x)*(deriv (fun i ↦ h Δ i) x *deriv (fun i ↦ h r i) x)
           = deriv (fun i ↦ h r i) x * h Δ x := by field_simp; ring
  have h3: (h r x / deriv (fun i ↦ h r i) x)*(deriv (fun i ↦ h Δ i) x *deriv (fun i ↦ h r i) x)
           = h r x * deriv (fun i ↦ h Δ i) x := by field_simp; ring
  linarith;

/- Proof of Lemma 6.3 -/

lemma q_lower_bound (hi : i ≤ 0) (hr1 : 0 < r) (hr2 : r < Δ) : Q_lo Δ r ≤ Q Δ i r :=
  lemma62 hr1 hr2 hi Set.right_mem_Iic hi

lemma q_upper_bound (hi : i ≤ 0) (hr1 : 0 < r) (hr2 : r < Δ) : Q Δ i r ≤ Q_hi Δ r := by
  suffices h : ∀ᶠ (x : ℝ) in atBot, Q Δ i r ≤ Q Δ x r
  · exact ge_of_tendsto (lemma61 delta_pos) h
  · rw [eventually_atBot]
    exact ⟨i, fun j ji => lemma62 hr1 hr2 (le_trans ji hi) hi ji⟩

lemma lemma63 (hi : i ≤ 0) (hc : c ≤ 0) (hr1 : 0 < r) (hr2 : r < Δ) :
    |Q Δ i r - Q Δ c r| ≤ Q_hi Δ (R_opt Δ) - Q_lo Δ (R_opt Δ) := by
  have i1:  Q_hi Δ r - Q_lo Δ r ≤ Q_hi Δ (R_opt Δ) - Q_lo Δ (R_opt Δ):=by apply lemma63sub hr1 hr2
  have case1:  Q Δ i r - Q Δ c r ≥ 0 → |Q Δ i r - Q Δ c r| ≤ Q_hi Δ (R_opt Δ) - Q_lo Δ (R_opt Δ) :=by
    intro i0
    have i2: Q Δ i r ≤ Q_hi Δ r := by apply q_upper_bound; linarith; assumption; assumption; assumption
    have i3: Q_lo Δ r ≤ Q Δ c r := by apply q_lower_bound; assumption; assumption; assumption;
    have e0:   |Q Δ i r - Q Δ c r| = Q Δ i r - Q Δ c r :=by apply abs_of_nonneg; linarith
    linarith
  apply by_cases case1; simp;
  intro i0
  have i2: Q Δ c r ≤ Q_hi Δ r := by apply q_upper_bound; linarith; assumption; assumption; assumption
  have i3: Q_lo Δ r ≤ Q Δ i r := by apply q_lower_bound; assumption; assumption; assumption;
  have e0:   |Q Δ i r - Q Δ c r| = -(Q Δ i r - Q Δ c r) :=by apply abs_of_neg; linarith
  linarith

/- Proof of Lemma 6.4 -/


lemma lemma64 (hc : c ≤ 0) (hr1 : 0 < r) (hr2 : r < Δ) (hΔ:  ΔP < Δ ) (hΔP:  ΔP > 0 ):
    |Q Δ c r - Q Δ c (Int.floor (r / ΔP) * ΔP)| ≤ 1 - Q_lo Δ (Δ - ΔP) := by
  have i00: (Int.floor (r / ΔP) * ΔP) ≥ 0:= by
    apply mul_nonneg; simp; apply Int.floor_nonneg.mpr;
    apply div_nonneg;
    any_goals linarith;

  have i01: r - (Int.floor (r / ΔP) * ΔP) ≥ 0:= by
    simp;
    have i2: Int.floor (r / ΔP) * ΔP ≤ r / ΔP * ΔP := by
      apply mul_le_mul; apply Int.floor_le; simp; linarith
      apply div_nonneg;
      any_goals linarith;
    have e0: r / ΔP * ΔP = r := by field_simp
    linarith;

  have i02: r - (Int.floor (r / ΔP) * ΔP) <  ΔP:= by
    have i1: Int.floor (r / ΔP) +1 > r / ΔP:= by apply Int.lt_floor_add_one
    have i2: Int.floor (r / ΔP) * ΔP > (r/ΔP -1)* ΔP:=by
      apply mul_lt_mul; linarith; simp; linarith; simp;
      apply Int.floor_nonneg.mpr; apply div_nonneg; linarith;linarith
    have i3: r - (Int.floor (r / ΔP) * ΔP) < r - (r/ΔP -1)* ΔP :=by linarith;
    have e1: r - (r/ΔP -1)* ΔP = ΔP :=by field_simp;
    linarith

  have i1: |Q Δ c r - Q Δ c (Int.floor (r / ΔP) * ΔP)| ≤ 1 - Q Δ c (Δ - ΔP) :=by
    apply lemma64sub
    any_goals linarith
  have i2: Q Δ c (Δ - ΔP) ≥  Q_lo Δ (Δ - ΔP):= by apply q_lower_bound; assumption; linarith; linarith
  linarith


/- Proof of Theorem 6.8 -/

def EM Δ := E 0 Δ

def QR Δ :=  Q_hi Δ (R_opt Δ) - Q_lo Δ (R_opt Δ)

def QI Δ ΔP := 1 - Q_lo Δ (Δ - ΔP)

variable (rnd : ℝ → ℝ)

variable (ε  : ℝ)

variable (hrnd : ∀ x , |x - rnd x| ≤ ε)

variable (rnd_mono: Monotone rnd)

variable (rnd_1:  rnd (1:ℝ) = (1:ℝ))

variable (rnd_0:  rnd (0:ℝ) = (0:ℝ))

noncomputable def EEC (Δ ΔP c i r  : ℝ) := rnd (Φ i) - rnd (r * rnd (deriv Φ i) ) +
                      rnd (rnd (E i Δ) * rnd (Q Δ c (Int.floor (r / ΔP) * ΔP)))

noncomputable def EECfix (Δ ΔP c i r  : ℝ):= |Φ (i - r) - EEC rnd Δ ΔP c i r|

lemma Phi_eq_EC  (hr1 : 0 < r) (hr2 : r < Δ):
        Φ (i - r) = Φ i - r * (deriv Φ i) + (E i Δ)*(Q Δ i r) :=by
  have ep : E i Δ > 0 := by apply err_pos; linarith
  unfold Q; field_simp; unfold E; ring_nf

lemma hrndn :  |rnd x - x| ≤ ε := by
  have : |rnd x - x| = |x - rnd x| :=by apply abs_sub_comm
  rw[this]
  apply hrnd


lemma Q_lt_1 (hr1 : 0 ≤ r) (hr2 : r < Δ): |rnd (Q Δ c r)| ≤ (1:ℝ) :=by
  have i1: Q Δ c r ≥ 0:= by
    unfold Q; apply div_nonneg; apply err_nonneg; linarith; apply err_nonneg; linarith
  have i2: rnd (Q Δ c r) ≥ 0 :=by
    rw[← rnd_0]; apply rnd_mono; assumption
  have e1: |rnd (Q Δ c r)| = rnd (Q Δ c r):= by apply abs_of_nonneg; assumption;
  rw[e1, ← rnd_1];  apply rnd_mono;
  unfold Q; apply le_of_lt;
  have i3:  E c Δ >0 :=by apply err_pos; linarith
  apply (div_lt_one i3).mpr
  apply strictMonoOn_E_r;
  any_goals simp;
  any_goals linarith;



lemma sum_8_abs (a1 a2 a3 a4 a5 a6 a7 a8 :ℝ) :
  |a1+a2+a3+a4+a5+a6+a7+a8| ≤ |a1|+|a2|+|a3|+|a4|+|a5|+|a6|+|a7|+|a8|:=by
  have i1 :  |a1+a2+a3+a4+a5+a6+a7+a8|  ≤  |a1+a2+a3+a4+a5+a6+a7|+|a8|:= by  apply abs_add
  have i2 :  |a1+a2+a3+a4+a5+a6+a7|  ≤  |a1+a2+a3+a4+a5+a6|+|a7|:= by  apply abs_add
  have i3 :  |a1+a2+a3+a4+a5+a6|  ≤  |a1+a2+a3+a4+a5|+|a6|:= by  apply abs_add
  have i4 :  |a1+a2+a3+a4+a5|  ≤  |a1+a2+a3+a4|+|a5|:= by  apply abs_add
  have i5 :  |a1+a2+a3+a4|  ≤  |a1+a2+a3|+|a4|:= by  apply abs_add
  have i6 :  |a1+a2+a3|  ≤  |a1+a2|+|a3|:= by  apply abs_add
  have i7 :  |a1+a2|  ≤  |a1|+|a2|:= by  apply abs_add
  linarith;



lemma Theorem68 (hi : i ≤ 0)(hc : c ≤ 0) (hr1 : 0 < r) (hr2 : r < Δ) (hΔ:  ΔP < Δ ) (hΔP:  ΔP > 0 ):
    EECfix rnd Δ ΔP c i r ≤ (4+Δ)*ε + (EM Δ) * (QR Δ + QI Δ ΔP + ε) := by
    set rr := (Int.floor (r / ΔP) * ΔP)
    set a1 := Φ i - rnd (Φ i)
    set a2 := rnd (r * rnd (deriv Φ i) ) - r * rnd (deriv Φ i)
    set a3 := r * (rnd (deriv Φ i) -  (deriv Φ i))
    set a4 := (E i Δ)*((Q Δ i r) - (Q Δ c r))
    set a5 := (E i Δ)*((Q Δ c r) - (Q Δ c rr))
    set a6 := (E i Δ)*((Q Δ c rr) - (rnd (Q Δ c rr)))
    set a7 := (rnd (Q Δ c rr)) * ((E i Δ) - (rnd (E i Δ) ) )
    set a8 := (rnd (E i Δ) ) * (rnd (Q Δ c rr)) - rnd (rnd (E i Δ) * rnd (Q Δ c rr))

    have irr0: rr ≥ 0:= by
      apply mul_nonneg; simp; apply Int.floor_nonneg.mpr;
      apply div_nonneg;
      any_goals linarith;

    have irr1: r - rr ≥ 0:= by
      simp;
      have i2: Int.floor (r / ΔP) * ΔP ≤ r / ΔP * ΔP := by
        apply mul_le_mul; apply Int.floor_le; simp; linarith
        apply div_nonneg;
        any_goals linarith;
      have e0: r / ΔP * ΔP = r := by field_simp
      linarith;

    have eq0: Φ (i - r) - EEC rnd Δ ΔP c i r = a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 := by
      rw[Phi_eq_EC hr1 hr2]; unfold EEC; ring_nf
    have i0 : |E i Δ| ≤ (EM Δ) := by unfold EM; apply err_taylor hi ; linarith; linarith
    have i01 :  (EM Δ) ≥ 0 :=by
      have : |E i Δ| ≥ 0 := by simp;
      linarith
    have i1 : |a1| ≤ ε := by apply hrnd
    have i2 : |a2| ≤ ε := by apply hrndn; apply hrnd;
    have i3 : |a3| ≤ Δ * ε := by
      have e1 : |a3| = |r| * |rnd (deriv Φ i) -  (deriv Φ i)| :=by apply abs_mul
      have e2 : |r| = r := by apply abs_of_pos hr1;
      rw[e1,e2]; apply mul_le_mul; linarith; apply hrndn; apply hrnd; simp; linarith;
    have i4 : |a4| ≤ (EM Δ) * (QR Δ) :=by
      have e1: |a4| = |E i Δ| * |(Q Δ i r) - (Q Δ c r)| := by apply  abs_mul
      have i1: |(Q Δ i r) - (Q Δ c r)| ≤ (QR Δ):= by apply lemma63; any_goals linarith
      rw[e1] ; apply mul_le_mul; assumption;  assumption;  simp; assumption;
    have i5: |a5| ≤ (EM Δ) * (QI Δ ΔP) :=by
      have e1: |a5| = |E i Δ| * |(Q Δ c r) - (Q Δ c rr)| := by apply  abs_mul
      have i1: |(Q Δ c r) - (Q Δ c rr)| ≤ QI Δ ΔP := by apply lemma64; any_goals linarith
      rw[e1] ; apply mul_le_mul; assumption;  assumption;  simp; assumption;
    have i6: |a6| ≤ (EM Δ) * ε :=by
      have e1: |a6| = |E i Δ| * |(Q Δ c rr) - (rnd (Q Δ c rr))| := by apply  abs_mul
      have i1: |(Q Δ c rr) - (rnd (Q Δ c rr))| ≤ ε := by apply hrnd
      rw[e1] ; apply mul_le_mul; assumption;  assumption; simp; assumption;
    have i7: |a7| ≤  ε :=by
      have e1: |a7| = |rnd (Q Δ c rr)| * |(E i Δ) - (rnd (E i Δ) )| := by apply  abs_mul
      have i1: |(E i Δ) - (rnd (E i Δ) )| ≤ ε := by apply hrnd
      have i2: |rnd (Q Δ c rr)| ≤ (1:ℝ) :=by
        apply Q_lt_1; apply rnd_mono; apply rnd_1; apply rnd_0;
        assumption; linarith
      have e2: ε = (1:ℝ) * ε :=by simp
      rw[e1, e2] ; apply mul_le_mul; assumption;  assumption; simp; linarith;
    have i8: |a8| ≤  ε  := by apply hrnd
    have isum: EECfix rnd Δ ΔP c i r ≤ |a1|+|a2|+|a3|+|a4|+|a5|+|a6|+|a7|+|a8|:=by
      unfold EECfix; rw[eq0]; apply sum_8_abs
    linarith
