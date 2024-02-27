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
  have t2: gbd a c 1 = 0 :=by unfold gbd; rw[hc]; ring;
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
  rw[← rpow_add];  ring; assumption
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

lemma monotoneOn_E_r (i:ℝ) : MonotoneOn (E i) (Set.Ici 0) :=
  StrictMonoOn.monotoneOn (strictMonoOn_E_r i)


lemma err_nonneg (i:ℝ)(r:ℝ) (hr : 0 ≤ r) : 0 ≤ E i r := by
  rw [(by simp [E] : 0 = E i 0)]
  rcases eq_or_gt_of_le hr with h | h
  · rw [h]
  · apply le_of_lt
    exact (strictMonoOn_E_r i) Set.left_mem_Ici hr h

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
  have t1:  StrictMonoOn (E i) (Set.Ici 0):= by exact strictMonoOn_E_r i
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
  have t7: er r i ≥ 0 := by unfold er; apply (err_nonneg i r); linarith
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
    rw[t33,t11,t21]; field_simp; ring; simp;
  rw[← t1, ← t22];
  have t4: h r i * ((2 ^ (i - r) + 1) * 2 ^ r) / (dih r i * ((2 ^ (i - r) + 1) * 2 ^ r)) = h r i / dih r i := by
    apply mul_div_mul_right
    have iex : (2:ℝ)^(i-r) > 0 := by apply rpow_pos_of_pos; linarith
    have ie: ((2:ℝ) ^ (i - r) + 1) * 2 ^ r >0 := by apply mul_pos; linarith; linarith
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


lemma gAnti (i:ℝ) : AntitoneOn (g i) (Set.Ioi (0:ℝ)):=by
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
    have h1: deriv (h x) i>0:= by apply dh_pos; linarith;
    linarith;

  have dc: ContinuousOn (g i) (Set.Ioi (0:ℝ)):= DifferentiableOn.continuousOn hd

  apply Convex.antitoneOn_of_deriv_nonpos (convex_Ioi (0:ℝ))
  assumption; rw[interior_Ioi]; assumption
  rw[interior_Ioi]
  intro x hx;
  have ht: x>0 := Set.mem_Ioi.mp hx
  apply deriv_g_le0; assumption

lemma hdih_ie (i:ℝ) (r:ℝ) (Δ:ℝ) (hr: r>0) (hΔ : r< Δ) :
        h Δ i / deriv (fun i ↦ h Δ i) i ≤ h r i /deriv (fun i ↦ h r i) i  := by
  have h1: (h Δ i) / deriv (fun i ↦ h Δ i) i = g i Δ  :=by
    unfold g; rw[deriv_h];
  have h2: (h r i) / deriv (fun i ↦ h r i) i = g i r  :=by
    unfold g; rw[deriv_h];
  rw[h1,h2]
  apply gAnti i;
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
    apply gAnti x;
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







lemma q_lower_bound (hi : i ≤ 0) (hr1 : 0 < r) (hr2 : r < Δ) : Q_lo Δ r ≤ Q Δ i r :=
  lemma62 hr1 hr2 hi Set.right_mem_Iic hi

lemma q_upper_bound (hi : i ≤ 0) (hr1 : 0 < r) (hr2 : r < Δ) : Q Δ i r ≤ Q_hi Δ r := by
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
