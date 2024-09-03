import LNS.Common
import LNS.Basic
import LNS.Lemma61
import LNS.Lemma65

noncomputable section

namespace LNS

open Real Filter Topology


def R_opt (Δ : ℝ) :=
  let X := 2 ^ Δ
  logb 2 ( (2*X*log X - X*log (2*X-1)) / (2*X*log X - 2*X*log (2*X-1) + 2*X -2))

def T X := 1/X + log X -1

def H X:= 2*log X - log (2*X-1)

def F X R:=  (H R) / (H X) - (T R) / (T X)

def A X := 2*X*log X - 2*X*log (2*X-1) + 2*X  -2

def B X := X*(H X)

def Root X := B X / A X

/-For T and H **********************************************************-/

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
  any_goals apply DifferentiableOn.log
  any_goals apply DifferentiableOn.sub
  any_goals apply DifferentiableOn.mul
  any_goals apply DifferentiableOn.log
  any_goals apply differentiableOn_const
  any_goals apply differentiableOn_id
  any_goals simp;
  any_goals intro x hx
  any_goals linarith


lemma deriv_H (hx : X>1) : deriv H X = 2*(X-1)/(X*(2*X-1)) := by
  unfold H
  rw[deriv_sub, deriv_mul, deriv.log, deriv.log, deriv_sub, deriv_mul]; simp
  have i1: 2*X - 1 >0 :=by linarith
  field_simp; ring_nf
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.mul
  any_goals apply DifferentiableAt.neg
  any_goals apply DifferentiableAt.log
  any_goals apply DifferentiableAt.add
  any_goals apply DifferentiableAt.mul
  any_goals apply differentiableAt_const
  any_goals apply differentiableAt_id
  any_goals linarith

lemma H_1 : H (1:ℝ) = 0 := by unfold H; simp; apply Or.intro_right; ring_nf;

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



/-For F  **********************************************************-/


lemma E_eq_H (hr: r>0): H (2^r) = (log 2)*(E (-1) r) :=by
  have e1: (2:ℝ) ^ (-1:ℝ) = ((2:ℝ) ^ (1:ℝ))⁻¹ :=by apply rpow_neg; linarith
  have e2: (1:ℝ) - 2⁻¹ = 1/2 :=by field_simp; linarith
  have i2: (2:ℝ) ^ r > 1 :=by apply one_lt_rpow; linarith; assumption

  unfold E H Φ logb; simp;
  rw[deriv.log,  deriv_sub, deriv_two_pow]; simp

  rw[e1]; simp; rw[e2]; field_simp;
  have e3: log (1 - 2 ^ (-1 - r)) = log (2 * 2 ^ r - 1) - log 2 - log (2^r):=by
    have: (-1 - r) = -(1+r):= by ring_nf;
    rw[this]
    have : (2:ℝ)  ^ (-(1 + r)) = (2^(1+r))⁻¹ :=by apply rpow_neg; linarith
    rw[this];
    have : (2:ℝ)^(1+r) = 2^(1:ℝ) * (2^r):=by apply rpow_add; linarith
    rw[this]; simp;
    have : (1:ℝ) - (2 ^ r)⁻¹ * 2⁻¹ = (2 * 2 ^ r - 1)/(2 * 2 ^ r) :=by  field_simp; ring_nf;
    rw[this]
    have : log ((2 * 2 ^ r - 1) / (2 * 2 ^ r)) = log (2 * 2 ^ r - 1)  - log (2 * 2 ^ r) :=by
      apply log_div; linarith; apply mul_ne_zero; simp; linarith
    rw[this];
    have : log (2 * 2 ^ r) = log 2 + log (2^r) :=by apply log_mul; linarith; linarith
    rw[this]; ring_nf;
  rw[e3]
  have : log (1/(2:ℝ)) = log 1 - log 2 :=by apply log_div; linarith; simp;
  rw[this]; simp;
  have : log (2^r) = r * log 2 :=by apply log_rpow; linarith
  rw[this]; ring_nf;
  simp;
  any_goals apply DifferentiableAt.sub
  any_goals apply DifferentiableAt.rpow
  any_goals simp
  have i4 : ((2:ℝ) ^ (1:ℝ))⁻¹ = 2⁻¹ :=by simp
  have :  1/(2:ℝ) >0 :=by apply div_pos; linarith; linarith;
  rw[e1, i4, e2]; linarith



lemma F_eq_Q (hr0: r>0) (hrΔ : r< Δ):  F (2^Δ) (2^r) = Q_lo Δ r - Q_hi Δ r := by
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

  have e13: log (2 ^ r) = r * log 2:= by apply log_rpow; linarith
  have e14: log (2 ^ Δ) = Δ * log 2:= by apply log_rpow; linarith
  have e1: (T (2^r)) / (T (2^Δ))  = Q_hi Δ r :=by
    unfold Q_hi T
    rw[e11, e12, e13, e14]

  have e2: (H (2^r)) / (H (2^Δ))  = Q_lo Δ r :=by
    unfold Q_lo Q
    have e1: H (2^r) = (log 2)*(E (-1) r) := by apply E_eq_H; assumption
    have e2: H (2^Δ) = (log 2)*(E (-1) Δ) := by apply E_eq_H; linarith
    have i1: log 2 > 0 :=by apply log_pos; linarith
    have i2: (E (-1) Δ) > 0 :=by apply err_pos; linarith; linarith
    rw[e1,e2]
    field_simp; ring_nf;
  unfold F; rw[e1,e2]

def AoX X:= 2*log X - 2*log (2*X-1) +2 -2/X

lemma differentiable_AoX : DifferentiableOn ℝ AoX (Set.Ici (1:ℝ)):= by
  unfold AoX
  apply DifferentiableOn.sub; apply DifferentiableOn.add_const; apply DifferentiableOn.sub;
  any_goals apply DifferentiableOn.const_mul;
  any_goals apply DifferentiableOn.log
  any_goals apply DifferentiableOn.sub;
  any_goals apply DifferentiableOn.const_mul;
  any_goals apply DifferentiableOn.inv;
  any_goals apply differentiableOn_const;
  any_goals apply differentiableOn_id;
  any_goals simp;
  any_goals intro x hx;
  any_goals linarith;

lemma AoX_1 : AoX 1 = 0 :=by unfold AoX; ring_nf

lemma deriv_AoX  (hx : X > 1) : deriv AoX X = 2*(X-1)/(X^2*(2*X-1)) :=by
    have i1: 2 * X - 1 > 0:= by linarith
    unfold AoX; rw[deriv_sub, deriv_div] ; simp ;
    rw[deriv_sub, deriv_mul, deriv_mul, deriv.log, deriv.log,deriv_sub, deriv_mul]; simp;
    field_simp; ring_nf
    any_goals apply DifferentiableAt.sub;
    any_goals apply DifferentiableAt.add;
    any_goals apply DifferentiableAt.mul;
    any_goals apply DifferentiableAt.log;
    any_goals apply DifferentiableAt.sub;
    any_goals apply DifferentiableAt.mul;
    any_goals simp;
    any_goals apply DifferentiableAt.inv;
    any_goals apply DifferentiableAt.log;
    any_goals apply DifferentiableAt.sub;
    any_goals apply DifferentiableAt.mul;
    any_goals simp;
    any_goals linarith;

lemma AoX_pos (hx : X > 1) : AoX X > 0 := by
  rw [← AoX_1]
  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici 1)
  apply DifferentiableOn.continuousOn differentiable_AoX
  any_goals simp;
  any_goals linarith;
  intro x h
  rw[deriv_AoX]; apply div_pos; linarith; apply mul_pos; apply pow_pos; linarith; linarith; assumption


lemma A_pos (hx : X > 1) : A X > 0 :=by
  have : A X = X * AoX X  :=by unfold A AoX; field_simp; ring_nf
  rw[this]; apply mul_pos; linarith; apply AoX_pos hx

lemma deriv_F_nonneg  (hx : X > 1) (hr : R > 1) (hxRoot: R ≤  Root X)  : deriv (F X) R ≥  0:=by
  have i1: H X > 0 := H_pos hx
  have i2: T X > 0 := T_pos hx
  have i3: A X > 0 := A_pos hx
  have i4: R^2 >0 := by apply pow_pos; linarith
  have i2: (H X)^2 >0 := by apply pow_pos; linarith
  have i5: (R^2 *  (2*R-1) * (H X) * T X ) >0 :=by apply mul_pos; apply mul_pos; apply mul_pos; any_goals linarith
  have i6: (R * (2 * R - 1) * H X ^ 2) >0 := by apply mul_pos; apply mul_pos;  any_goals linarith
  have i7: (R * (2 * R - 1) * H X ) >0 := by apply mul_pos; apply mul_pos;  any_goals linarith
  have e1: 2 * (R - 1) / (R * (2 * R - 1)) * H X / H X ^ 2 =  (R - 1)*2 / (R * (2 * R - 1)*H X) :=by field_simp; ring_nf
  have e2: (R - 1) / R ^ 2 * T X / T X ^ 2 = (R - 1) / (R ^ 2 * T X ):=by field_simp; ring_nf

  unfold F;
  rw[deriv_sub, deriv_div, deriv_div]; simp;
  rw[deriv_H, deriv_T];

  rw[e1,e2]; apply le_of_sub_nonneg;
  have e3: (R - 1) * 2 / (R * (2 * R - 1) * H X) - (R - 1) / (R ^ 2 * T X)
        = (R-1)*(2 / (R * (2 * R - 1) * H X) -1/ (R ^ 2 * T X)) :=by field_simp; ring_nf
  rw[e3]; apply mul_nonneg; linarith
  have i9: (R ^ 2 * (2 * R - 1) * H X * T X) >0:=by apply mul_pos; apply mul_pos; apply mul_pos; any_goals linarith
  have e4: (2 / (R * (2 * R - 1) * H X) - 1 / (R ^ 2 * T X)) =
       (2*R* T X - (2*R-1)*H X )/(R^2*(2*R-1)*H X * T X):= by field_simp; ring_nf
  rw[e4]; apply div_nonneg;
  have e6: 2 * R * T X - (2 * R - 1) * H X = (B X - R*A X)/X:= by unfold B H T A; field_simp; ring_nf
  rw[e6]; apply div_nonneg; simp;
  apply (div_le_div_right i3).mp;
  have : B X / A X = Root X:= by unfold Root; simp;
  rw[this];field_simp; assumption; linarith; linarith; any_goals linarith;
  any_goals apply DifferentiableAt.div
  any_goals apply DifferentiableOn.differentiableAt differentiable_T
  any_goals apply DifferentiableOn.differentiableAt differentiable_H
  any_goals apply Ici_mem_nhds
  any_goals linarith;
  any_goals apply differentiableAt_const

lemma deriv_F_nonpos (hx : X > 1) (hr : R > 1) (hxRoot: R ≥ Root X)  : deriv (F X) R ≤   0:=by
  have i1: H X > 0 := H_pos hx
  have i2: T X > 0 := T_pos hx
  have i3: A X > 0 := A_pos hx
  have i4: R^2 >0 := by apply pow_pos; linarith
  have i2: (H X)^2 >0 := by apply pow_pos; linarith
  have i5: (R^2 *  (2*R-1) * (H X) * T X ) >0 :=by apply mul_pos; apply mul_pos; apply mul_pos; any_goals linarith
  have i6: (R * (2 * R - 1) * H X ^ 2) >0 := by apply mul_pos; apply mul_pos;  any_goals linarith
  have i7: (R * (2 * R - 1) * H X ) >0 := by apply mul_pos; apply mul_pos;  any_goals linarith
  have e1: 2 * (R - 1) / (R * (2 * R - 1)) * H X / H X ^ 2 =  (R - 1)*2 / (R * (2 * R - 1)*H X) :=by field_simp; ring_nf
  have e2: (R - 1) / R ^ 2 * T X / T X ^ 2 = (R - 1) / (R ^ 2 * T X ):=by field_simp; ring_nf
  unfold F;
  rw[deriv_sub, deriv_div, deriv_div]; simp;
  rw[deriv_H, deriv_T];
  rw[e1,e2]; apply le_of_sub_nonneg;
  have e3:   (R - 1) / (R ^ 2 * T X) -(R - 1) * 2 / (R * (2 * R - 1) * H X)
        = (R-1)*( 1/ (R ^ 2 * T X) - 2 / (R * (2 * R - 1) * H X)) :=by field_simp; ring_nf
  rw[e3]; apply mul_nonneg; linarith
  have i9: (R ^ 2 * (2 * R - 1) * H X * T X) >0:=by apply mul_pos; apply mul_pos; apply mul_pos; any_goals linarith
  have e4: 1 / (R ^ 2 * T X)  -2 / (R * (2 * R - 1) * H X)  =
       ((2*R-1)*H X - 2*R* T X )/(R^2*(2*R-1)*H X * T X):= by field_simp; ring_nf
  rw[e4]; apply div_nonneg;
  have e6: (2 * R - 1) * H X -2 * R * T X = ( R*A X -B X )/X:= by unfold B H T A; field_simp; ring_nf
  rw[e6]; apply div_nonneg; simp;
  apply (div_le_div_right i3).mp;
  have : B X / A X = Root X:= by unfold Root; simp;
  rw[this];field_simp; assumption; linarith; linarith; any_goals linarith;
  any_goals apply DifferentiableAt.div
  any_goals apply DifferentiableOn.differentiableAt differentiable_T
  any_goals apply DifferentiableOn.differentiableAt differentiable_H
  any_goals apply Ici_mem_nhds
  any_goals linarith;
  any_goals apply differentiableAt_const

/-For ROOT ****************************************************************-/

def AH X := A X - H X

lemma differentiable_AH : DifferentiableOn ℝ AH (Set.Ici (1:ℝ)):= by
  apply DifferentiableOn.sub  _  differentiable_H
  unfold A; apply DifferentiableOn.sub_const;
  apply DifferentiableOn.add
  apply DifferentiableOn.sub
  any_goals apply DifferentiableOn.const_mul;
  any_goals apply DifferentiableOn.mul;
  any_goals apply DifferentiableOn.const_mul;
  any_goals apply DifferentiableOn.log
  any_goals apply DifferentiableOn.sub;
  any_goals apply DifferentiableOn.mul;
  any_goals apply differentiableOn_const;
  any_goals apply differentiableOn_id;
  any_goals simp;
  any_goals intro x hx;
  any_goals linarith;


lemma AH_1 : AH 1 = 0 :=by unfold AH A; rw[H_1]; ring_nf

lemma deriv_AH  (hx : X > 1) : deriv AH X = AoX X :=by
    have i1: 2 * X - 1 > 0:= by linarith
    unfold AH A; rw[deriv_sub, deriv_H, deriv_sub, deriv_add, deriv_sub, deriv_mul, deriv_mul] ; simp;
    rw[deriv_mul, deriv_mul, deriv.log,deriv_sub, deriv_mul]; simp; unfold AoX
    field_simp; ring_nf
    any_goals apply DifferentiableAt.sub;
    any_goals apply DifferentiableAt.mul;
    any_goals apply DifferentiableAt.add;
    any_goals apply DifferentiableAt.sub;
    any_goals apply DifferentiableAt.mul;
    any_goals apply DifferentiableAt.mul;
    any_goals apply DifferentiableAt.log;
    any_goals apply DifferentiableAt.sub;
    any_goals apply DifferentiableAt.mul;
    any_goals simp;
    any_goals linarith;


lemma AH_pos (hx : X > 1) : AH X > 0 := by
  rw [← AH_1]
  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici 1)
  apply DifferentiableOn.continuousOn differentiable_AH
  any_goals simp;
  any_goals linarith;
  intro x h
  rw[deriv_AH]; apply AoX_pos h; assumption



lemma Root_lt_X (hx : X > 1) : Root X < X :=by
  unfold Root B;
  have hA: A X > 0 := by exact A_pos hx
  apply (mul_lt_mul_right hA).mp; field_simp; apply lt_of_sub_pos
  have : A X - H X = AH X:=by simp [AH]
  rw[this]; apply AH_pos hx;


def HA X := H X - AoX X

lemma differentiable_HA : DifferentiableOn ℝ HA (Set.Ici (1:ℝ)):= by
  apply DifferentiableOn.sub  differentiable_H  differentiable_AoX


lemma HA_1 : HA 1 = 0 :=by unfold HA; rw[H_1, AoX_1];simp

lemma deriv_HA  (hx : X > 1) : deriv HA X = 2*(X-1)^2/(X^2*(2*X-1)) :=by
    have i1: 2 * X - 1 > 0:= by linarith
    unfold HA; rw[deriv_sub, deriv_H, deriv_AoX] ;field_simp; ring_nf
    assumption; assumption
    apply DifferentiableOn.differentiableAt differentiable_H
    apply Ici_mem_nhds; assumption
    apply DifferentiableOn.differentiableAt differentiable_AoX
    apply Ici_mem_nhds; assumption

lemma HA_pos (hx : X > 1) : HA X > 0 := by
  rw [← HA_1]
  apply Convex.strictMonoOn_of_deriv_pos (convex_Ici 1)
  apply DifferentiableOn.continuousOn differentiable_HA
  any_goals simp;
  any_goals linarith;
  intro x h
  rw[deriv_HA]; apply div_pos; apply mul_pos; linarith;  apply pow_pos; linarith;
  apply mul_pos;  apply pow_pos;linarith; linarith; assumption


lemma Root_gt_1 (hx : X > 1) : Root X >1 :=by
  unfold Root;
  have hA: A X > 0 := by exact A_pos hx
  apply (mul_lt_mul_right hA).mp
  unfold B; field_simp; apply lt_of_sub_pos
  have e1: X * H X - A X = X * HA X  :=by unfold HA A AoX; field_simp; ring_nf
  rw[e1]; apply mul_pos; linarith; apply HA_pos hx;


lemma Root_eq_t : logb 2 (Root (2^Δ)) = R_opt Δ :=by
  unfold R_opt; simp;
  unfold Root B A H
  set X := (2:ℝ)^Δ
  simp; ring_nf



lemma Root_eq_R_opt (hΔ : Δ >0):  2^(R_opt Δ) = Root (2^Δ)  :=by
  rw[← Root_eq_t]
  apply rpow_logb;
  linarith; linarith;
  have : Root (2 ^ Δ) > 1 := by
    apply Root_gt_1; apply one_lt_rpow
    any_goals linarith;
  linarith


/-For MAIN ****************************************************************-/

lemma main (hr: R > 1) (hxr: R < X) :  F X R ≤ F X (Root X) := by

  have hx : X > 1 :=by linarith
  have diff : DifferentiableOn ℝ (F X) (Set.Ici (1:ℝ)):= by
    unfold F
    apply DifferentiableOn.sub
    any_goals apply DifferentiableOn.div
    exact differentiable_H
    apply differentiableOn_const
    simp; intro x _

    have : H X > 0 := H_pos hx
    linarith;
    exact differentiable_T
    apply differentiableOn_const
    simp; intro x _
    have : T X > 0 := T_pos hx
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
    apply deriv_F_nonneg hx h1; linarith
    simp; apply And.intro; linarith; assumption
    simp;  linarith; assumption
  apply by_cases firsthalf; simp;

  have secondhalf (hr2: Root X < R ) : F X R ≤ F X (Root X) := by
    apply Convex.antitoneOn_of_deriv_nonpos (convex_Icc (Root X) X)
    apply DifferentiableOn.continuousOn diff2
    apply DifferentiableOn.mono diff2
    apply interior_subset
    simp;
    intro x h1 _
    apply deriv_F_nonpos hx; linarith
    linarith; simp; linarith; simp; apply And.intro; linarith; linarith; linarith;


  intro hr2
  exact secondhalf hr2


lemma lemma63sub  (hr1 : 0 < r) (hr2 : r < Δ) :
    Q_lo Δ r - Q_hi Δ r ≤ Q_lo Δ (R_opt Δ) - Q_hi Δ (R_opt Δ) := by

  have e : logb 2 (Root (2^Δ)) = R_opt Δ := by apply  Root_eq_t;
  have i0: (2:ℝ) ^ Δ > 1 := by apply one_lt_rpow; linarith; linarith
  have i1: logb 2 (Root (2^Δ)) > 0 := by
    apply logb_pos; linarith; apply Root_gt_1; assumption
  have i1: logb 2 (Root (2^Δ)) < Δ :=by
    have : Δ = logb 2 (2^Δ) := by simp;
    rw[this]; apply logb_lt_logb; linarith; rw[← this]
    have i1: Root (2^Δ) > 1 :=by apply Root_gt_1 i0;
    linarith; rw[← this]; apply Root_lt_X i0

  rw[← F_eq_Q, ← F_eq_Q , Root_eq_R_opt]
  apply main
  apply one_lt_rpow; linarith; linarith
  apply rpow_lt_rpow_of_exponent_lt; linarith; assumption; linarith;
  any_goals linarith


lemma q_upper_bound (hi : i ≤ -1) (hr1 : 0 < r) (hr2 : r < Δ) : Q Δ i r ≤ Q_lo Δ r := by
  apply lemma65 hr1 hr2 hi Set.right_mem_Iic hi

lemma q_lower_bound (hi : i ≤ -1) (hr1 : 0 < r) (hr2 : r < Δ) : Q_hi Δ r ≤ Q Δ i r := by
  have delta_pos : Δ > 0 :=by linarith
  suffices h : ∀ᶠ (x : ℝ) in atBot, Q Δ x r ≤ Q Δ i r
  · exact le_of_tendsto (lemma61 delta_pos) h
  · rw [eventually_atBot]
    exact ⟨i, fun j ji => lemma65 hr1 hr2 (le_trans ji hi) hi ji⟩

lemma lemma66 (hi : i ≤ -1) (hc : c ≤ -1) (hr1 : 0 < r) (hr2 : r < Δ) :
    |Q Δ i r - Q Δ c r| ≤ Q_lo Δ (R_opt Δ) - Q_hi Δ (R_opt Δ) := by
  have i1:  Q_lo Δ r - Q_hi Δ r ≤ Q_lo Δ (R_opt Δ) - Q_hi Δ (R_opt Δ):=by apply lemma63sub hr1 hr2
  have case1:  Q Δ i r - Q Δ c r ≥ 0 → |Q Δ i r - Q Δ c r| ≤ Q_lo Δ (R_opt Δ) - Q_hi Δ (R_opt Δ) :=by
    intro i0
    have i2: Q Δ i r ≤ Q_lo Δ r := by apply q_upper_bound; linarith; assumption; assumption;
    have i3: Q_hi Δ r ≤ Q Δ c r := by apply q_lower_bound; assumption; assumption; assumption;
    have e0:   |Q Δ i r - Q Δ c r| = Q Δ i r - Q Δ c r :=by apply abs_of_nonneg; linarith
    linarith
  apply by_cases case1; simp;
  intro i0
  have i2: Q Δ c r ≤ Q_lo Δ r := by apply q_upper_bound; linarith; assumption; assumption;
  have i3: Q_hi Δ r ≤ Q Δ i r := by apply q_lower_bound; assumption; assumption; assumption;
  have e0:   |Q Δ i r - Q Δ c r| = -(Q Δ i r - Q Δ c r) :=by apply abs_of_neg; linarith
  linarith
