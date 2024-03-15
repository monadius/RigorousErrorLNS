import LNS.Common
import LNS.Basic

noncomputable section

namespace LNS

open Real Filter Topology



def F (x:ℝ) (t:ℝ) :=  Φ (x-t)  -  Φ x

noncomputable def Fx t x := F x t

lemma dphi_neg (hx: x ≤ (-1:ℝ)) : dphi x ≤ 0 :=by
  unfold dphi
  have i1:  (2 : ℝ) ^ x < 1 := by apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith
  have i3: (2:ℝ)^x/(1 - 2^x) >0 :=by apply div_pos; apply rpow_pos_of_pos; linarith; linarith;
  have : -2 ^ x / (1 - 2 ^ x) = -((2:ℝ)^x/(1-2^x)) :=by ring_nf;
  linarith



lemma main (hx: x ≤ (-1:ℝ)) (ht0: 0 ≤ t) (htp: t ≤ m): F x t ≤ F (-1) m :=by

  have diff_Fx (ht0: 0 ≤ t) : DifferentiableOn ℝ (Fx t) (Set.Iic (-1:ℝ)):= by
    unfold Fx  F;
    apply DifferentiableOn.sub;
    intro x; simp; intro hx;
    apply DifferentiableAt.differentiableWithinAt
    have : (fun y ↦ Φ (y - t)) = Φ ∘ (fun y ↦ (y - t)) := by ext x; simp
    rw[this]
    apply DifferentiableAt.comp; apply DifferentiableOn.differentiableAt differentiable_phi0;
    apply Iio_mem_nhds; linarith
    apply DifferentiableAt.sub_const;
    simp; exact differentiable_phi

  have sub1  :  F x t ≤ F (-1) t :=by
    rw[← Fx, ← Fx]
    apply Convex.monotoneOn_of_deriv_nonneg (convex_Iic (-1:ℝ))
    apply DifferentiableOn.continuousOn (diff_Fx ht0)
    apply DifferentiableOn.mono (diff_Fx ht0) ; simp
    simp; intro x hx;
    unfold Fx F;
    rw[deriv_sub, deriv_phi]
    have : (fun y ↦ Φ (y - t)) = Φ ∘ (fun y ↦ (y - t)) := by ext x; simp
    rw[this]
    rw[deriv.comp, deriv_phi]; simp;
    rcases lt_or_eq_of_le ht0 with h | h
    apply le_of_lt; apply dphi_anti; linarith; assumption;
    rw[← h]; simp; linarith
    apply DifferentiableOn.differentiableAt differentiable_phi
    apply Iic_mem_nhds; linarith
    apply DifferentiableAt.sub_const; simp;
    linarith
    have : (fun y ↦ Φ (y - t)) = Φ ∘ (fun y ↦ (y - t)) := by ext x; simp
    rw[this]
    apply DifferentiableAt.comp; apply DifferentiableOn.differentiableAt differentiable_phi0;
    apply Iio_mem_nhds; linarith
    apply DifferentiableAt.sub_const; simp; apply DifferentiableOn.differentiableAt differentiable_phi0;
    apply Iio_mem_nhds; linarith
    simp; linarith; simp; assumption

  have diffF : DifferentiableOn ℝ (F (-1)) (Set.Ici 0) :=by
    unfold F;
    apply DifferentiableOn.sub;
    intro x; simp; intro hx;
    apply DifferentiableAt.differentiableWithinAt
    have : (fun y ↦ Φ (-1-y)) = Φ ∘ (fun y ↦ (-1 - y)) := by ext x; simp
    rw[this]
    apply DifferentiableAt.comp; apply DifferentiableOn.differentiableAt differentiable_phi0;
    apply Iio_mem_nhds; linarith
    apply DifferentiableAt.const_sub
    simp;
    apply differentiableOn_const;


  have sub3  :  F (-1) t ≤ F (-1) m :=by
    apply Convex.monotoneOn_of_deriv_nonneg (convex_Ici 0)
    apply DifferentiableOn.continuousOn diffF
    apply DifferentiableOn.mono diffF; simp;
    simp; intro x hx;
    unfold F;
    rw[deriv_sub]; simp;
    have : (fun y ↦ Φ (-1-y)) = Φ ∘ (fun y ↦ (-1 - y)) := by ext x; simp
    rw[this,deriv.comp, deriv_phi, deriv_sub]; simp;

    apply dphi_neg; linarith;
    simp; simp; linarith;
    apply DifferentiableOn.differentiableAt differentiable_phi0;
    apply Iio_mem_nhds; linarith
    apply DifferentiableAt.const_sub; simp;
    have : (fun y ↦ Φ (-1-y)) = Φ ∘ (fun y ↦ (-1 - y)) := by ext x; simp
    rw[this]
    apply DifferentiableAt.comp; apply DifferentiableOn.differentiableAt differentiable_phi0;
    apply Iio_mem_nhds; linarith
    apply DifferentiableAt.const_sub; simp;
    apply differentiableAt_const;
    simp; assumption; simp; linarith;assumption
  linarith


lemma AntiPhi : StrictAntiOn Φ (Set.Iio 0):= by
    apply Convex.strictAntiOn_of_deriv_neg (convex_Iio 0)
    exact DifferentiableOn.continuousOn differentiable_phi0
    simp; intro t ht;
    have i1: (2 : ℝ) ^ t < 1 := by apply rpow_lt_one_of_one_lt_of_neg; linarith; assumption;
    have i2: log 2 > 0 := by apply log_pos; linarith
    have i3: log 2 ^ 2 > 0:= by apply pow_pos; linarith
    have e: -(2 ^ t * log 2) / (1 - 2 ^ t) * log 2 / log 2 ^ 2 = -((2 ^ t * log 2) / (1 - 2 ^ t) * log 2 / log 2 ^ 2):=by
      field_simp
    unfold Φ logb
    rw [deriv_div, deriv.log, deriv_const_sub, deriv_two_pow]; simp;
    rw[e]; simp
    apply div_pos _ i3; apply mul_pos _ i2; apply div_pos; apply mul_pos _ i2; apply rpow_pos_of_pos; linarith; linarith
    apply DifferentiableAt.const_sub; apply DifferentiableAt.rpow; simp; simp; simp; linarith
    apply DifferentiableAt.log; apply DifferentiableAt.const_sub; apply DifferentiableAt.rpow;
    any_goals simp;
    linarith; linarith;


lemma lemma71 (hx: x ≤ (-1:ℝ)) (hxs: xs ≤ (-1:ℝ)) (hd: |x-xs| ≤ m) : |Φ x - Φ xs| ≤ Φ (-1-m) - Φ (-1) :=by

  have e: Φ (-1 - m) - Φ (-1) = F (-1) m :=by unfold F; simp
  rw[e]

  have case1 :  x > xs → |Φ x - Φ xs| ≤ F (-1) m:= by
    intro hx;
    have i1: |Φ x - Φ xs| = - (Φ x - Φ xs) := by
      apply abs_of_neg; simp; apply AntiPhi;
      any_goals simp;
      any_goals linarith;
    set t := x -xs
    have e0:  xs = x-t :=by simp;
    have e: Φ x - Φ (x - t) = - F x t:=by unfold F; simp
    have i0: t ≤ |t| := by apply le_abs_self
    rw[i1, e0, e]; simp;  apply main; any_goals linarith;
  apply by_cases case1

  simp; intro hx1;
  have i1: |Φ x - Φ xs| = (Φ x - Φ xs) := by
    apply abs_of_nonneg; simp; apply StrictAntiOn.antitoneOn AntiPhi;
    any_goals simp;
    any_goals linarith;
  rw[i1]
  set t := xs -x
  have e0:  x = xs-t :=by simp;
  have e: Φ (xs - t) - Φ xs =  F xs t:=by unfold F; simp
  have i0: |x - xs| = t := by rw[abs_of_nonpos]; simp; linarith
  rw[e0, e]; apply main; any_goals linarith;







/- Theorem 7.2-/

variable (rnd : ℝ → ℝ)

variable (ε  : ℝ)

variable (hrnd : ∀ x , |x - rnd x| ≤ ε)

lemma hrndn :  |rnd x - x| ≤ ε := by
  have : |rnd x - x| = |x - rnd x| :=by apply abs_sub_comm
  rw[this]
  apply hrnd

variable (Φe : ℝ → ℝ)

variable (EΦ  : ℝ)

variable (hΦe : ∀ x , |Φe x - Φ x| ≤ EΦ)

lemma hΦen :  |Φ x - Φe x| ≤ EΦ := by
  have : |Φe x - Φ x| = |Φ x - Φe x| :=by apply abs_sub_comm
  rw[← this]
  apply hΦe

/-Case 2-/

def rb2 (x:ℝ) (Δa:ℝ) := (Int.ceil (x/Δa) - 1) * Δa

def ra2 (x:ℝ) (Δa:ℝ) := (rb2 x Δa) - x

def k (x:ℝ) (Δa:ℝ):= x - Φ (rb2 x Δa)  + Φ (ra2 x Δa)

def Pest2 (x:ℝ) (Δa:ℝ) := Φ (rb2 x Δa) + Φ (k x Δa)

def krnd (x:ℝ) (Δa:ℝ) := x - rnd (Φ (rb2 x Δa) )  + rnd (Φ (ra2 x Δa) )

def Prnd2 (x:ℝ) (Δa:ℝ) := rnd (Φ (rb2 x Δa) ) + Φe (krnd rnd x Δa)

lemma rb2_lt_x (ha:Δa >0): rb2 x Δa < x:=by
  unfold rb2
  have i11: (Int.ceil (x/Δa) -1 < x/Δa) ∧ ( x/Δa ≤ Int.ceil (x/Δa)) := by
    apply Int.ceil_eq_iff.mp; simp
  have i1: Int.ceil (x/Δa) -1 < x/Δa := i11.left
  have i2: (Int.ceil (x/Δa) -1)*Δa < (x/Δa)*Δa :=by apply (mul_lt_mul_right ha).mpr i1
  have e: (x/Δa)*Δa = x :=by field_simp;
  linarith

lemma k_neg (hx: x<0) (ha:Δa >0): k x Δa < 0 :=by
  have i1: rb2 x Δa < x := rb2_lt_x ha
  have : Φ (ra2 x Δa) < Φ (rb2 x Δa) :=by
    apply AntiPhi
    any_goals simp;
    linarith; unfold ra2; linarith; unfold ra2; linarith
  unfold k; linarith


lemma cotrans2 (hx: x<0) (ha:Δa >0) : Φ x = Pest2 x Δa :=by
  unfold Pest2 Φ
  have i0: (2:ℝ) ^ x < 1 :=by
    apply rpow_lt_one_of_one_lt_of_neg; linarith; linarith
  have i1: (2:ℝ) ^ rb2 x Δa < 1 :=by
    apply rpow_lt_one_of_one_lt_of_neg; linarith;
    have i0: rb2 x Δa < x := rb2_lt_x ha
    linarith
  have i2: (2:ℝ) ^ k x Δa < 1 :=by
    apply rpow_lt_one_of_one_lt_of_neg; linarith;
    apply k_neg hx ha
  have i3: (2:ℝ) ^ ra2 x Δa < 1 :=by
    apply rpow_lt_one_of_one_lt_of_neg; linarith;
    have i0: rb2 x Δa < x := rb2_lt_x ha
    unfold ra2; linarith
  have e1: logb 2 (1 - 2 ^ rb2 x Δa) + logb 2 (1 - 2 ^ k x Δa) = logb 2 ((1 - 2 ^ rb2 x Δa) * (1 - 2 ^ k x Δa)) :=by
    rw [← logb_mul]; linarith; linarith
  rw[e1]; unfold logb; field_simp;
  apply Real.exp_eq_exp.mp;
  have e: rexp (log (1 - 2 ^ x)) = 1 - 2 ^ x := by apply Real.exp_log; linarith
  rw[e]
  have e: rexp (log ((1 - 2 ^ rb2 x Δa) * (1 - 2 ^ k x Δa)))= (1 - 2 ^ rb2 x Δa) * (1 - 2 ^ k x Δa):= by
    apply Real.exp_log; apply mul_pos; linarith; linarith
  rw[e]
  set a:= (2:ℝ)^ra2 x Δa
  set b:= (2:ℝ)^rb2 x Δa
  have e: 2^ k x Δa = 2^x * (1-(2:ℝ)^ra2 x Δa)/(1-(2:ℝ)^rb2 x Δa) :=by
    unfold k Φ; rw [rpow_add, rpow_sub, rpow_logb, rpow_logb]; field_simp;
    any_goals linarith;
  rw[e];
  have e: (1 - b) * (1 - 2 ^ x * (1 - a) / (1 - b)) = 1 - b - 2^x + a* 2^x  := by
    have i: 1 - b ≠ 0 := by linarith;
    field_simp; ring_nf
  rw[e];
  have e: a * (2:ℝ) ^ x = b :=by rw [← rpow_add]; unfold ra2; simp; linarith
  rw[e]; ring_nf


lemma bound_case2 (hx: x<0) (ha:Δa >0) (hk: k x Δa ≤ -1) (hkr: krnd rnd x Δa ≤ -1) :
      |Φ x - Prnd2 rnd Φe x Δa| ≤ ε +  Φ (-1-2*ε) - Φ (-1) + EΦ :=by
  have e: Φ x = Pest2 x Δa := cotrans2 hx ha
  rw[e]
  set s1:= Φ (rb2 x Δa) - rnd (Φ (rb2 x Δa) )
  set s2:= Φ (k x Δa) - Φ (krnd rnd x Δa)
  set s3:= Φ (krnd rnd x Δa) - Φe (krnd rnd x Δa)
  have e: Pest2 x Δa - Prnd2 rnd Φe x Δa = s1 + s2 + s3  :=by unfold Pest2 Prnd2; ring_nf
  rw[e];
  have i01: |s1 + s2 + s3| ≤ |s1 + s2| + |s3|:= by apply abs_add
  have i02: |s1 + s2| ≤ |s1| + |s2|:= by apply abs_add
  have i1 : |s1| ≤ ε := by apply hrnd
  have i3 : |s3| ≤ EΦ := by apply hΦen; apply hΦe
  have i2 : |s2| ≤ Φ (-1-2*ε) - Φ (-1) :=by
    apply lemma71 hk hkr
    set a1:= rnd (Φ (rb2 x Δa) ) - Φ (rb2 x Δa)
    set a2:= Φ (ra2 x Δa) - rnd (Φ (ra2 x Δa) )
    have e: k x Δa - krnd rnd x Δa = a1 + a2:= by unfold k krnd; ring_nf;
    rw[e]
    have i0: |a1 + a2| ≤ |a1| + |a2|:= by apply abs_add
    have i1 : |a1| ≤ ε := by apply hrndn; apply hrnd;
    have i2 : |a2| ≤ ε := by apply hrnd
    linarith
  linarith



/-Case 3-/

def rc (x:ℝ) (Δb:ℝ) := (Int.ceil (x/Δb) - 1) * Δb

def rab (x:ℝ) (Δb:ℝ) := (rc x Δb) - x

def rb (x:ℝ) (Δa:ℝ) (Δb:ℝ) := (Int.ceil ( rab x Δb  /Δa) - 1) * Δa

def ra (x:ℝ) (Δa:ℝ) (Δb:ℝ) :=  rb x Δa Δb  - rab x Δb

def k1 (x:ℝ) (Δa:ℝ) (Δb:ℝ) := rab x Δb  - Φ (rb x Δa Δb)  + Φ (ra x Δa Δb)

def k2 (x:ℝ) (Δa:ℝ) (Δb:ℝ) := x + Φ (rb x Δa Δb) + Φ (k1 x Δa Δb) - Φ (rc x Δb)

def Pest3 (x:ℝ) (Δa:ℝ) (Δb:ℝ) := Φ (rc x Δb) +  Φ (k2 x Δa Δb)

def k1rnd (x:ℝ) (Δa:ℝ) (Δb:ℝ) := rab x Δb  - rnd (Φ (rb x Δa Δb))  + rnd (Φ (ra x Δa Δb))

def k2rnd (x:ℝ) (Δa:ℝ) (Δb:ℝ) := x + rnd (Φ (rb x Δa Δb)) + Φe (k1rnd rnd x Δa Δb) - rnd (Φ (rc x Δb))

def Prnd3 (x:ℝ) (Δa:ℝ) (Δb:ℝ) := rnd (Φ (rc x Δb)) +  Φe (k2rnd rnd Φe x Δa Δb)

lemma cotrans3 (hx: x<0) (ha:Δa >0) (hb:Δb >0): Φ x = Pest3 x Δa Δb :=by
  have e1: Φ x  = Pest2 x Δb := cotrans2 hx hb
  rw[e1]; unfold Pest2 Pest3
  have e0: rb2 x Δb = rc x Δb :=by unfold rb2 rc; simp;
  rw[e0]; simp;
  have e2: Φ (ra2 x Δb) = Φ (rb x Δa Δb) + Φ (k1 x Δa Δb) :=by
    apply cotrans2;
    have i0: rb2 x Δb < x := rb2_lt_x hb;
    unfold ra2; linarith; assumption
  have e: k x Δb = k2 x Δa Δb:=by
    unfold k k2; rw[e0, e2]; ring_nf;
  rw[e]


def Ek2 := 2*ε +  Φ (-1-2*ε) - Φ (-1) + EΦ

lemma bound_case3 (hx: x<0) (ha:Δa >0) (hb:Δb >0)
    (hk1: k1 x Δa Δb ≤ -1) (hk1r: k1rnd rnd x Δa Δb ≤ -1)
    (hk2: k2 x Δa Δb ≤ -1) (hk2r: k2rnd rnd Φe x Δa Δb ≤ -1):
    |Φ x - Prnd3 rnd Φe x Δa Δb| ≤ ε +  Φ (-1- Ek2 ε EΦ) - Φ (-1) + EΦ :=by
  have e: Φ x = Pest3 x Δa Δb := cotrans3 hx ha hb
  rw[e]
  set s1:= Φ (rc x Δb) - rnd (Φ (rc x Δb) )
  set s2:= Φ (k2 x Δa Δb) - Φ (k2rnd rnd Φe x Δa Δb)
  set s3:= Φ (k2rnd rnd Φe x Δa Δb) - Φe (k2rnd rnd Φe x Δa Δb)
  have e: Pest3 x Δa Δb - Prnd3 rnd Φe x Δa Δb = s1 + s2 + s3  :=by unfold Pest3 Prnd3; ring_nf
  rw[e];
  have i01: |s1 + s2 + s3| ≤ |s1 + s2| + |s3|:= by apply abs_add
  have i02: |s1 + s2| ≤ |s1| + |s2|:= by apply abs_add
  have i1 : |s1| ≤ ε := by apply hrnd
  have i3 : |s3| ≤ EΦ := by apply hΦen; apply hΦe
  have i2 : |s2| ≤  Φ (-1- Ek2 ε EΦ) - Φ (-1) :=by
    apply lemma71 hk2 hk2r
    set a1:=  Φ (rb x Δa Δb) - rnd ( Φ (rb x Δa Δb))
    set a2:=  rnd (Φ (rc x Δb)) - Φ (rc x Δb)
    set a3:=   Φ (k1 x Δa Δb) - Φ (k1rnd rnd x Δa Δb)
    set a4:=  Φ (k1rnd rnd x Δa Δb) - Φe (k1rnd rnd x Δa Δb)
    have e: k2 x Δa Δb - k2rnd rnd Φe x Δa Δb = a1 + a2 + a3 + a4 := by unfold k2 k2rnd; ring_nf;
    rw[e]
    have i00: |a1 + a2 + a3 + a4| ≤ |a1 + a2 + a3| + |a4|:= by apply abs_add
    have i01: |a1 + a2 + a3| ≤ |a1 + a2| + |a3|:= by apply abs_add
    have i02: |a1 + a2| ≤ |a1| + |a2|:= by apply abs_add
    have i1 : |a1| ≤ ε := by apply hrnd
    have i2 : |a2| ≤ ε := by apply hrndn; apply hrnd;
    have i4 : |a4| ≤ EΦ := by apply hΦen; apply hΦe
    have i3 : |a3| ≤  Φ (-1-2*ε) - Φ (-1) :=by
      apply lemma71 hk1 hk1r
      set b1:= rnd (Φ (rb x Δa Δb)) - Φ (rb x Δa Δb)
      set b2:= Φ (ra x Δa Δb) - rnd (Φ (ra x Δa Δb))
      have e: k1 x Δa Δb - k1rnd rnd x Δa Δb = b1 + b2 := by unfold k1 k1rnd; ring_nf;
      rw[e]
      have i0: |b1 + b2| ≤ |b1| + |b2|:= by apply abs_add
      have i1 : |b1| ≤ ε := by apply hrndn; apply hrnd;
      have i2 : |b2| ≤ ε := by apply hrnd
      linarith
    unfold Ek2; linarith
  linarith
