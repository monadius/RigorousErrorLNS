import LNS.Common
import LNS.Basic
import LNS.Lemma61


noncomputable section

namespace LNS

open Real Filter Topology


def h  (r:ℝ) (i:ℝ) := f (2^i) r

def dih (r:ℝ) (i:ℝ) := (2^i* (1 - 2^(i-r)) * (r*(log 2) - (log (1 - 2^i )) +  (log (1-2^(i-r)))
 -1) + 2^(i-r)*(1-2^i)) * (log 2) / (1 -2^(i-r) )

def g  (i:ℝ) (r:ℝ) :=  (h r i)/ (dih r i)

def gbn (a:ℝ) (c:ℝ) (b:ℝ)  := (a-b)*( -a*(log b) + (a-1)*c + (a-1)* (log b -  log (b-a)))

def gbd (a:ℝ) (c:ℝ) (b:ℝ)  := a*(log  2)*(1-a+(a-b)*(-log (b-a) + c+1))

def gb (a:ℝ) (c:ℝ) (b:ℝ)  := (gbn a c b)/(gbd a c b)


/-FOR K -------------------------------------------------------------------------------------------------/

def k (a:ℝ) (b:ℝ) := - a * a * log (1-a) + a * a * log (b-a) + a * b - a + b * log (1-a) + b * log b - b * log (b-a)

def dk a b := (a*a)/(b-a) + a - b/(b-a) + log b + log (1-a) - log (b-a) + (1:ℝ)

lemma deriv_k (ha0: a>0) (hab: -a + b > 0) (hb:b>=1): deriv (k a) b = dk a b := by
  have diff1: DifferentiableAt ℝ (fun b ↦ log (b - a)) b :=by
    apply DifferentiableAt.log; apply DifferentiableAt.sub_const; simp; linarith;
  have diff2: DifferentiableAt ℝ (fun (b:ℝ) => a * a * log (b - a)) b :=by
    apply DifferentiableAt.mul; apply differentiableAt_const; assumption;
  unfold k; unfold dk;
  rw[deriv_sub, deriv_add, deriv_add, deriv_sub, deriv_add, deriv_add]; simp;
  rw[deriv_mul, deriv_mul, deriv_mul, deriv.log]; simp;
  field_simp; ring_nf;
  any_goals simp;
  linarith; assumption; linarith; assumption; assumption;
  apply DifferentiableAt.const_mul; apply differentiableAt_id;
  apply DifferentiableAt.add; apply DifferentiableAt.add;
  simp; assumption; apply DifferentiableAt.const_mul; apply differentiableAt_id;
  apply DifferentiableAt.add; apply DifferentiableAt.add
  simp; assumption; apply DifferentiableAt.const_mul; apply differentiableAt_id;
  apply DifferentiableAt.add; apply DifferentiableAt.sub; apply DifferentiableAt.add;
  apply DifferentiableAt.add; simp; assumption; apply DifferentiableAt.const_mul; apply differentiableAt_id;
  apply differentiableAt_const;  apply DifferentiableAt.mul_const; simp;
  apply DifferentiableAt.mul; simp; apply DifferentiableAt.log; simp;
  linarith; apply DifferentiableAt.add; apply DifferentiableAt.add
  apply DifferentiableAt.sub; apply DifferentiableAt.add; apply DifferentiableAt.add;
  simp; assumption; apply DifferentiableAt.const_mul; apply differentiableAt_id;
  apply differentiableAt_const;  apply DifferentiableAt.mul_const; simp;
  apply DifferentiableAt.mul; simp; apply DifferentiableAt.log; simp;
  linarith; apply DifferentiableAt.mul; simp; assumption

lemma differentiable_dk  (ha0: a>0) (ha1: a <1 ): DifferentiableOn ℝ (dk a) (Set.Ici (1:ℝ)):= by
  unfold dk
  apply DifferentiableOn.add
  apply DifferentiableOn.add; apply DifferentiableOn.add; apply DifferentiableOn.add;
  apply DifferentiableOn.add; apply DifferentiableOn.add; apply DifferentiableOn.div;
  apply differentiableOn_const; apply DifferentiableOn.sub_const;
  any_goals apply DifferentiableOn.neg;
  any_goals apply DifferentiableOn.div;
  any_goals apply DifferentiableOn.log;
  any_goals apply DifferentiableOn.add;
  any_goals apply differentiableOn_const
  any_goals apply differentiableOn_id
  any_goals simp
  any_goals intro x hx
  any_goals linarith

lemma deriv_dk  (ha0: a>0) (hab: b-a > 0) (hb:b>1): deriv (dk a) b = -((a^2*(b-1))/(b*(b-a)^2)) :=by
  unfold dk
  rw[deriv_add, deriv_sub, deriv_add, deriv_add, deriv_sub, deriv_add]; simp;
  rw[deriv_div, deriv.log, deriv_div, deriv_sub]; simp;
  field_simp; ring_nf;
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

lemma dk_1  (ha1: 1-a > 0 ): dk a 1  = 0 := by unfold dk ; field_simp; ring_nf

lemma dk_neg (ha0: a>0) (ha1: a <1 ) (hb:b>1): (dk a) b <0 :=by
  rw [← dk_1]
  apply Convex.strictAntiOn_of_deriv_neg (convex_Ici 1)
  apply DifferentiableOn.continuousOn (differentiable_dk ha0 ha1)
  any_goals simp;
  any_goals linarith;
  intro x h
  rw[deriv_dk]; simp; apply div_pos; apply mul_pos; apply pow_pos; assumption
  linarith; apply mul_pos; linarith; apply pow_pos; linarith; assumption; linarith; assumption

lemma k_1 : k a 1 = 0 := by unfold k ; field_simp;

lemma differentiable_k  (ha0: a>0) (ha1: a <1 ): DifferentiableOn ℝ (k a) (Set.Ici (1:ℝ)):= by
  unfold k
  apply DifferentiableOn.add
  apply DifferentiableOn.add; apply DifferentiableOn.add; apply DifferentiableOn.sub
  apply DifferentiableOn.add; apply DifferentiableOn.add;
  apply DifferentiableOn.mul;
  any_goals apply DifferentiableOn.mul;
  any_goals apply DifferentiableOn.log;
  any_goals apply DifferentiableOn.add;
  any_goals apply DifferentiableOn.mul;
  any_goals simp
  any_goals apply DifferentiableOn.mul;
  any_goals apply DifferentiableOn.log;
  any_goals apply DifferentiableOn.sub;
  any_goals apply differentiableOn_const
  any_goals apply differentiableOn_id
  any_goals simp
  any_goals intro x hx
  any_goals linarith

lemma k_neg (ha0: a>0) (ha1: a <1 ) (hb:b>1) : k a b < 0 :=by
  rw [← k_1]
  apply Convex.strictAntiOn_of_deriv_neg (convex_Ici 1)
  apply DifferentiableOn.continuousOn (differentiable_k ha0 ha1)
  any_goals simp;
  any_goals linarith;
  intro x h
  rw[deriv_k]; apply dk_neg
  any_goals linarith


/-FOR H G -------------------------------------------------------------------------------------------------/

lemma deriv_h  (hi: i≤-1) (hr: r>0):  (deriv (h r)) i = dih r i:= by
 have t5: (2:ℝ)^i > 0 :=by  linarith [rpow_pos_of_pos two_pos i]
 have i1: 1 - (2:ℝ)^(i-r) > 0 := by simp; apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith
 have i2: 1 - (2:ℝ)^i > 0 := by simp; apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith
 have tt : (2:ℝ)^(i-r) = 2^i *2^(-r)  :=by
  have h1: 0< (2:ℝ):= by linarith
  rw[← rpow_add];  ring_nf; assumption
 have t1: 2 ^ i * log 2 * 2 ^ (-r) = 2 ^ i * 2 ^ (-r) * log 2 :=by ring
 unfold h
 unfold f
 rw[deriv_sub, deriv_add];
 rw[deriv_mul, deriv_mul];
 rw[deriv_two_pow, deriv_const, deriv_const]
 rw[deriv_mul, deriv_sub, deriv_const, deriv_two_pow, deriv_mul, deriv_sub, deriv_const]
 rw[deriv_two_pow, deriv.log, deriv_sub, deriv_two_pow, deriv_const]
 rw[deriv.log, deriv_sub,deriv_const,deriv_mul,deriv_two_pow, deriv_const]; simp
 rw[← tt, t1,  ← tt];
 unfold dih;
 field_simp; ring_nf;

 any_goals apply DifferentiableAt.rpow
 any_goals apply DifferentiableAt.mul
 any_goals apply DifferentiableAt.rpow
 any_goals apply DifferentiableAt.sub
 any_goals apply DifferentiableAt.mul
 any_goals apply DifferentiableAt.rpow
 any_goals apply DifferentiableAt.log
 any_goals apply DifferentiableAt.add
 any_goals apply DifferentiableAt.mul
 any_goals simp
 any_goals apply DifferentiableAt.mul
 any_goals apply DifferentiableAt.log
 any_goals apply DifferentiableAt.rpow
 any_goals simp
 any_goals linarith
 apply DifferentiableAt.rpow
 any_goals simp

def d2 (a:ℝ) (b:ℝ):= 1 - a  -  (a-b)*(log (b-a) - log (1-a) -1)


lemma d2pos (ha: a < 1) (hb: b > 1) : d2 a b > 0:=by
  have : d2 a 1 = 0 :=by unfold d2; simp;
  rw[← this]
  have diffd2: DifferentiableOn ℝ (d2 a) (Set.Ici (1:ℝ)):=by
    unfold d2;
    apply DifferentiableOn.sub; apply differentiableOn_const;
    apply DifferentiableOn.mul; apply DifferentiableOn.const_sub; apply differentiableOn_id;
    apply DifferentiableOn.sub; apply DifferentiableOn.sub_const;
    apply DifferentiableOn.log; apply DifferentiableOn.sub_const; apply differentiableOn_id;
    simp; intro x hx; linarith; apply differentiableOn_const;

  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici (1:ℝ))
  apply DifferentiableOn.continuousOn diffd2;
  simp;intro x hx; unfold d2;
  rw[deriv_sub, deriv_mul, deriv_sub, deriv_sub]; simp;
  rw[deriv_sub, deriv_sub, deriv.log];
  have i1: x - a >0 :=by linarith
  field_simp;
  have e1: (a - x) / (x - a) = (-1:ℝ) :=by field_simp;
  rw[e1]; simp; apply log_lt_log; linarith; linarith
  any_goals apply DifferentiableAt.sub
  any_goals apply DifferentiableAt.log
  any_goals apply DifferentiableAt.sub
  any_goals simp
  any_goals linarith
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.sub
  any_goals apply DifferentiableAt.sub
  any_goals apply DifferentiableAt.log
  any_goals simp
  any_goals linarith



lemma dih_pos (hi: i ≤  -1) (hr: r>0) :  dih r i  >0 :=by
  have tt : (2:ℝ)^(i-r) = 2^i / 2^(r)  :=by rw[← rpow_sub];  ring_nf; linarith
  have i1: 1 - (2:ℝ)^(i-r) > 0 := by simp; apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith
  have i2: 1 - (2:ℝ)^i > 0 := by simp; apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith
  have i3: (2:ℝ)^r > 0 :=by  linarith [rpow_pos_of_pos two_pos r]
  have i31: (2:ℝ)^i > 0 :=by  linarith [rpow_pos_of_pos two_pos i]
  have i4: (2:ℝ) ^ r - 2 ^ i >0 :=by simp;  apply rpow_lt_rpow_of_exponent_lt; linarith; linarith
  have eq:  dih r i = ((d2 (2^i) (2^r) ) * 2^i  * log 2)/(1-2^(i-r)) /2^r:=by
    unfold dih d2; rw[tt]; field_simp;
    have e1: log ((2 ^ r - 2 ^ i) / 2 ^ r) = log (2 ^ r - 2 ^ i) - log (2^r):=
      by rw[log_div]; linarith; linarith
    have e2: log (2^r) = r * log 2 := by apply log_rpow; linarith;
    rw[e1,e2]; field_simp; ring_nf
  rw[eq]; apply div_pos; apply div_pos; apply mul_pos; apply mul_pos
  any_goals linarith;
  apply d2pos; linarith; apply one_lt_rpow;  linarith; assumption; apply log_pos; linarith

/-FOR GB GBN GBD -------------------------------------------------------------------------------------------------/

lemma hir_gbn (hi: i ≤  -1) (hr: r>0): (h r i) * ((1 -2^(i-r)  )* (2^r)) = (gbn (2^i) (log (1  -2^i )) (2^r)) :=by
  have ie2: (2:ℝ)^r >0 := by apply rpow_pos_of_pos; linarith
  have t21: (2:ℝ)^(i-r) = 2^i / 2^r :=by apply rpow_sub ; linarith
  have t31: (2:ℝ)^ (-r) = (2 ^ r)⁻¹  := by apply rpow_neg; linarith
  have t11: log (2 ^ r) = r * log 2 :=by apply log_rpow; linarith
  have i4: (2:ℝ) ^ r - 2 ^ i >0 :=by simp;  apply rpow_lt_rpow_of_exponent_lt; linarith; linarith
  have e1: log ((2 ^ r - 2 ^ i) / 2 ^ r) = log (2 ^ r - 2 ^ i) - log (2^r):=
      by rw[log_div]; linarith; linarith

  unfold h gbn f
  rw[t11,t31,t21]; field_simp;
  rw[e1,t11]; ring_nf


lemma dih_gbd (hi: i ≤  -1) (hr: r>0): (dih r i) *((1-2^(i-r))* (2^r)) = (gbd (2^i) (log (1 -2^i )) (2^r)) :=by
  have i1: 1 - (2:ℝ)^(i-r) > 0 := by simp; apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith
  have ie2: (2:ℝ)^r >0 := by apply rpow_pos_of_pos; linarith
  have t21: (2:ℝ)^(i-r) = 2^i / 2^r :=by apply rpow_sub ; linarith
  have t2: 1 -(2:ℝ)^(i-r)  = (2^r - 2^i)/2^r :=by
      rw[t21]; field_simp;
  have t11: log (2 ^ r) = r * log 2 :=by apply log_rpow; linarith
  have i4: (2:ℝ) ^ r - 2 ^ i >0 :=by simp;  apply rpow_lt_rpow_of_exponent_lt; linarith; linarith
  have e1: log ((2 ^ r - 2 ^ i) / 2 ^ r) = log (2 ^ r - 2 ^ i) - log (2^r):=
      by rw[log_div]; linarith; linarith
  unfold dih gbd; field_simp;
  rw[t2,e1,t11,t21];
  field_simp; ring_nf; simp;

lemma gb_g (hi: i ≤  -1) (hr: r>0) :  g i r  = ((gb (2^i) (log (1 -2^i)))  ∘ (fun r=>2^r))  r:=by
  unfold g gb
  have i1: 1 - (2:ℝ)^(i-r) > 0 := by simp; apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith
  have ie2: (2:ℝ)^r >0 := by apply rpow_pos_of_pos; linarith
  have t1: (h r i) * ((1 -2^(i-r)  )* (2^r)) = (gbn (2^i) (log (1  -2^i )) (2^r)) := hir_gbn hi hr
  have t22: (dih r i) *((1-2^(i-r))* (2^r)) = (gbd (2^i) (log (1 -2^i )) (2^r)):= dih_gbd hi hr
  simp; rw[← t1, ← t22];
  have ie: (1  - (2:ℝ) ^ (i - r)) * 2 ^ r >0 := by apply mul_pos; linarith; linarith
  set t:= (1  - (2:ℝ) ^ (i - r)) * 2 ^ r
  rw[← mul_div_mul_right]; linarith


lemma derivd_pos  (ha0: a>0) (ha: a<1) (hb: b>1) (hc:c = log (1-a)) : 0 < deriv (gbd a c) b :=by
  have derivd: deriv (fun b ↦ gbd a c b) b = a *  (log 2) * (log (b-a) -c):=by
    unfold gbd
    rw[deriv_mul, deriv_mul, deriv_const]; simp
    rw[deriv_mul, deriv_add, deriv_const];
    rw[deriv_sub, deriv_add, deriv_const, deriv_const]; simp; rw[deriv.log, deriv_sub]; simp;
    have i1: b-a>0 :=by linarith
    field_simp; apply Or.intro_left; ring_nf
    any_goals simp
    any_goals apply DifferentiableAt.sub
    any_goals apply DifferentiableAt.log
    any_goals simp
    any_goals apply DifferentiableAt.mul
    any_goals apply DifferentiableAt.add
    any_goals apply DifferentiableAt.add
    any_goals simp
    any_goals apply DifferentiableAt.log
    any_goals apply DifferentiableAt.add
    any_goals simp
    any_goals linarith
    apply DifferentiableAt.neg; simp;
  rw[derivd,hc]
  apply mul_pos; apply mul_pos; any_goals linarith;
  apply log_pos; linarith
  simp; apply log_lt_log; any_goals linarith;


lemma gbd_pos  (ha0: a>0) (ha: a<1) (hb: b>1) (hc:c = log (1-a)) : 0 < gbd a c b:= by
  have t1: StrictMonoOn (gbd a c) (Set.Ici (1:ℝ)) := by
    apply Convex.strictMonoOn_of_deriv_pos (convex_Ici (1:ℝ))
    unfold gbd
    apply ContinuousOn.mul; apply ContinuousOn.mul;
    exact continuousOn_const;  exact continuousOn_const;  apply ContinuousOn.add; apply ContinuousOn.add;
    any_goals apply ContinuousOn.mul
    any_goals apply ContinuousOn.sub
    any_goals apply ContinuousOn.add
    any_goals apply ContinuousOn.add
    any_goals apply ContinuousOn.neg
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


lemma deriv_gb_nonneg (ha0: a>0) (ha: a<1) (hb: b>1) (hc:c = log (1-a)):  (deriv (gb a c)) b ≥  0 :=by
  have i1: b-a>0 :=by linarith
  have derivd: deriv (fun b ↦ gbd a c b) b = a *  (log 2) * (log (b-a) -c):=by
    unfold gbd
    rw[deriv_mul, deriv_mul, deriv_const]; simp
    rw[deriv_mul, deriv_add, deriv_const];
    rw[deriv_sub, deriv_add] ; simp; rw[deriv.log, deriv_sub];
    rw[deriv_const]; simp; field_simp; apply Or.intro_left; ring_nf
    any_goals apply DifferentiableAt.sub
    any_goals apply DifferentiableAt.add
    any_goals simp
    any_goals apply DifferentiableAt.log
    any_goals apply DifferentiableAt.mul
    any_goals apply DifferentiableAt.add
    any_goals apply DifferentiableAt.add
    any_goals simp
    any_goals apply DifferentiableAt.log
    any_goals apply DifferentiableAt.add
    any_goals simp
    any_goals linarith
    apply DifferentiableAt.neg; simp;
  have derivn: deriv (fun b ↦ gbn a c b) b = -a*c + a*log (b-a) + a - a/b + c + log b - log (b-a):=by
    unfold gbn
    rw [deriv_mul, deriv_add]; simp; rw[deriv_sub, deriv_sub, deriv.log, deriv.log]; simp;
    field_simp; ring_nf;
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
    any_goals apply DifferentiableAt.log
    any_goals apply DifferentiableAt.add
    any_goals simp
    any_goals linarith
    apply DifferentiableAt.neg; simp;
  unfold gb
  rw[deriv_div];
  have t1: gbd a c b ^ 2 >= 0 :=  by exact pow_two_nonneg (gbd a c b)
  apply div_nonneg _ t1
  rw[derivd,derivn]
  unfold gbd
  unfold gbn
  field_simp;
  apply div_nonneg
  set t:= ((-(a * c) + a * log (b - a) + a) * b - a + c * b + log b * b - b * log (b - a)) *
      (a * log 2 * (1 - a + (a - b) * (-log (b - a) + c + 1))) -
    b * ((a - b) * (-(a * log b) + (a - 1) * c + (a - 1) * (log b - log (b - a))) * (a * log 2 * (log (b - a) - c)))
  have : t = a*(b-1)*(-(- a * a * c + a * a * log (b-a) + a * b - a + b * c + b * log b - b * log (b-a)))*log 2  :=by  ring_nf;
  rw[this];
  apply mul_nonneg; apply mul_nonneg;apply mul_nonneg
  linarith; linarith; apply nonneg_of_neg_nonpos;
  rw[ hc]
  have : (-a * a * log (1 - a) + a * a * log (b - a) + a * b - a + b * log (1 - a) + b * log b - b * log (b - a))
            =  (k a b) :=by unfold k; ring_nf
  rw[this]; simp; apply le_of_lt; apply k_neg;
  any_goals linarith
  have t :0 < log 2 := by apply log_pos; linarith;
  linarith
  unfold gbn
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.sub
  any_goals apply DifferentiableAt.log
  any_goals apply DifferentiableAt.add
  any_goals simp
  any_goals apply DifferentiableAt.log
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.mul
  any_goals simp
  any_goals linarith
  apply DifferentiableAt.neg; simp;
  apply ne_of_gt; apply gbd_pos;
  any_goals assumption



lemma gMono (hi: i ≤ -1) : MonotoneOn (g i) (Set.Ioi (0:ℝ)):=by
  have se : Set.EqOn ((gb (2^i) (log (1 -2^i)))  ∘ (fun r=>2^r))  (g i)  (Set.Ioi (0:ℝ)) :=by
    unfold Set.EqOn; simp; intro x hx; rw[gb_g]; simp; assumption; assumption
  apply MonotoneOn.congr _ se;
  have i1 : (2:ℝ) ^ i < 1 :=by apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith;
  have d1 :DifferentiableOn ℝ (gb (2 ^ i) (log (1 - 2 ^ i))) (Set.Ioi 1):=by
    unfold gb
    have i1: ∀ x ∈ Set.Ioi 1, gbd (2 ^ i) (log (1 - 2 ^ i)) x ≠ 0 :=by
      simp; intro x hx;
      apply ne_of_gt; apply gbd_pos; apply rpow_pos_of_pos; linarith; linarith; assumption; simp
    apply DifferentiableOn.div _ _ i1
    any_goals unfold gbn;
    any_goals unfold gbd;
    any_goals apply DifferentiableOn.mul
    any_goals apply DifferentiableOn.add
    any_goals apply DifferentiableOn.add
    any_goals apply DifferentiableOn.mul
    any_goals apply DifferentiableOn.add
    any_goals simp
    any_goals apply DifferentiableOn.log
    any_goals apply DifferentiableOn.rpow
    any_goals simp
    any_goals apply differentiableOn_const
    any_goals apply DifferentiableOn.neg;
    any_goals apply differentiableOn_id
    any_goals intro x hx
    any_goals linarith


  have difft: DifferentiableOn ℝ ((gb (2^i) (log (1 -2^i)))  ∘ (fun r=>2^r)) (Set.Ioi (0:ℝ)):=by
    have st: Set.MapsTo (fun r=>2^r) (Set.Ioi (0:ℝ)) (Set.Ioi (1:ℝ)):=by
      unfold Set.MapsTo; simp; intro x hxx; apply one_lt_rpow; linarith; assumption
    apply DifferentiableOn.comp d1 _ st;
    apply DifferentiableOn.rpow; apply differentiableOn_const; apply differentiableOn_id; simp;


  apply Convex.monotoneOn_of_deriv_nonneg (convex_Ioi (0:ℝ))
  apply DifferentiableOn.continuousOn difft
  apply DifferentiableOn.mono difft; simp;
  simp; intro x hx;
  rw[deriv.comp, deriv_two_pow];
  apply mul_nonneg; apply deriv_gb_nonneg
  apply rpow_pos_of_pos; any_goals linarith
  apply one_lt_rpow; linarith; assumption; apply mul_nonneg; apply le_of_lt
  apply rpow_pos_of_pos; linarith; apply log_nonneg; linarith;
  apply DifferentiableOn.differentiableAt d1;
  apply Ioi_mem_nhds; apply one_lt_rpow; linarith;assumption;
  apply DifferentiableAt.rpow; simp; simp; simp




lemma hdih_ie (hi: i ≤ -1)  (hr: r>0) (hΔ : r< Δ) :
        h Δ i / deriv (fun i ↦ h Δ i) i ≥ h r i /deriv (fun i ↦ h r i) i  := by
  have h1: (h Δ i) / deriv (fun i ↦ h Δ i) i = g i Δ  :=by
    unfold g; rw[deriv_h]; linarith; linarith
  have h2: (h r i) / deriv (fun i ↦ h r i) i = g i r  :=by
    unfold g; rw[deriv_h]; linarith; linarith
  rw[h1,h2]
  apply gMono hi;
  any_goals simp
  any_goals linarith




lemma h_pos (hi: i ≤ -1) (hr: r>0) :  h r i >0 :=by
  have ie: (2:ℝ)^i > 0:= by apply rpow_pos_of_pos; linarith
  have ie2: log 2 >0:= by apply log_pos; linarith
  have i1: 1 - (2 : ℝ) ^ i > 0 := one_minus_two_pow_pos hi
  have e00 : (2:ℝ) ^ (i - r) = (2^i) * 2^(-r) :=by apply Real.rpow_add; linarith
  have eq :  h r i  = (E i r)* (1 - 2^i) * log 2  := by
    unfold E h ; rw[deriv_phi]; unfold dphi Φ logb  f;
    rw[e00]
    field_simp; ring_nf; exact hi
  rw[eq]
  apply mul_pos; apply mul_pos;
  any_goals linarith;
  apply err_pos hi hr



lemma dfh (hr: r>0) : DifferentiableOn ℝ (fun i ↦ h r i ) (Set.Iic (-1:ℝ)):=by
    unfold h
    unfold f
    apply DifferentiableOn.add
    apply DifferentiableOn.add
    any_goals apply DifferentiableOn.mul
    any_goals apply DifferentiableOn.sub
    any_goals apply DifferentiableOn.neg
    any_goals apply DifferentiableOn.mul
    any_goals apply DifferentiableOn.log
    any_goals apply DifferentiableOn.sub
    any_goals apply DifferentiableOn.mul
    any_goals apply DifferentiableOn.rpow
    any_goals simp;
    any_goals apply differentiableOn_const
    any_goals apply differentiableOn_id
    any_goals intro x hx
    have i1 : (2:ℝ) ^ x < 1 :=by apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith;
    linarith
    have  : (2:ℝ) ^ (x - r) = (2^x) * 2^(-r) :=by apply Real.rpow_add; linarith
    rw[← this]
    have i1 : (2:ℝ) ^ (x-r) < 1 :=by apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith;
    linarith

lemma q_eq2  (hr1 : 0 < r) (hr2 : r < Δ): Set.EqOn (fun i=>h r i / h Δ i) (fun i => Q Δ i r)  (Set.Iic (-1:ℝ)) := by
  unfold h Set.EqOn
  simp; intro x hx
  rw[q_eq]; linarith; assumption


lemma lemma65 (hr1 : 0 < r) (hr2 : r < Δ) : MonotoneOn (fun i => Q Δ i r) (Set.Iic (-1:ℝ)) := by

  have se : Set.EqOn (fun i=>h r i / h Δ i) (fun i => Q Δ i r)  (Set.Iic (-1:ℝ)) :=by
    apply q_eq2 hr1 hr2
  apply MonotoneOn.congr _ se;
  have dhr : DifferentiableOn ℝ (fun x ↦ h r x) (Set.Iic (-1)):=by exact dfh hr1
  have dhΔ : DifferentiableOn ℝ (fun x ↦ h Δ x) (Set.Iic (-1)):=by apply dfh ; linarith
  have df : DifferentiableOn ℝ (fun i ↦ h r i / h Δ i) (Set.Iic (-1:ℝ)):=by
    apply DifferentiableOn.div
    assumption; assumption
    simp; intro x hx; apply ne_of_gt; apply h_pos; assumption; linarith

  apply Convex.monotoneOn_of_deriv_nonneg (convex_Iic (-1:ℝ))

  exact DifferentiableOn.continuousOn df
  apply DifferentiableOn.mono df; simp;
  simp
  intro x hx
  rw[deriv_div]; apply div_nonneg
  any_goals exact pow_two_nonneg  (h Δ x)
  any_goals apply DifferentiableOn.differentiableAt dhr
  any_goals apply DifferentiableOn.differentiableAt dhΔ
  any_goals apply Iic_mem_nhds hx
  simp; rw[deriv_h, deriv_h]
  have t2 : dih r x >0 := by apply dih_pos; linarith; linarith
  have t1 : dih Δ x >0 := by apply dih_pos; linarith; linarith
  have t3 : h Δ x / dih Δ x ≥  h r x /dih r x :=by
    have h1: (h Δ x) / dih Δ x = g x Δ  :=by unfold g; simp;
    have h2: (h r x) / dih r x = g x r  :=by unfold g; simp;
    rw[h1,h2]
    apply gMono;
    any_goals simp
    any_goals linarith

  have h0: 0 < dih Δ x * dih r x := by apply mul_pos; assumption; assumption;
  have h01: 0  ≤ dih Δ x * dih r x  := by linarith;
  have h1:  (h Δ x /dih Δ x) * (dih Δ x *dih r x)
            ≥  (h r x / dih r x)*(dih Δ x * dih r x ) := by
            apply mul_le_mul_of_nonneg_right t3 h01;
  have h2: (h Δ x /dih Δ x) * (dih Δ x *dih r x)
           = dih r x * h Δ x := by field_simp; ring
  have h3: (h r x / dih r x)*(dih Δ x * dih r x )
           = h r x * dih Δ x  := by field_simp; ring
  any_goals linarith;
  apply ne_of_gt; apply h_pos; linarith; linarith
