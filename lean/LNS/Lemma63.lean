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




lemma main (hr: R > 1) (hxr: R < X) :  F X R ≤ F X (Root X) := by

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

lemma lemma63sub (hr: r > 0) (hxr: r < Δ) :  F (2^Δ) (2^r) ≤ F (2^Δ) (Root (2^Δ)) := by
  apply main
  apply one_lt_pow; linarith; linarith
  apply pow_right_strictMono; linarith; assumption


lemma lemma63sub2  (hr1 : 0 < r) (hr2 : r < Δ) :
    Q_hi Δ r - Q_lo Δ r ≤ Q_hi Δ (R_opt Δ) - Q_lo Δ (R_opt Δ) := by
  rw[← F_eq_Q, ← F_eq_Q , Root_eq_R_opt]
  apply main
  apply one_lt_rpow; linarith; linarith
  apply rpow_lt_rpow_of_exponent_lt; linarith; assumption; linarith;
