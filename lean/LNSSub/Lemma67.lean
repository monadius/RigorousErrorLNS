import LNS.Common
import LNS.Basic
import LNS.Lemma61
import LNS.Lemma65
import LNS.Lemma66

noncomputable section

namespace LNS

open Real Filter Topology



def W c Δ r t := (E c r - E c (r-t)) / (E c Δ)

def Wt c Δ t r := W c Δ r t

lemma monoW  (hc: c ≤ -1)  (hr: r > 0) (htd: r ≤ Δ) : MonotoneOn (W c Δ r) (Set.Icc 0 r) := by
    have diffE : DifferentiableOn ℝ (E c) (Set.Ici 0) := by apply differentiable_E hc
    have ep : E c Δ > 0 := by apply err_pos hc; linarith
    have ec : (fun y ↦ E c (r - y)) = (fun y=> E c y) ∘ (fun y=>r-y) :=by ext y; simp;

    have diffW : DifferentiableOn ℝ (W c Δ r) (Set.Icc 0 r) := by
      unfold W
      apply DifferentiableOn.div; apply DifferentiableOn.sub; apply differentiableOn_const;
      rw[ec]
      apply DifferentiableOn.comp; assumption;
      apply DifferentiableOn.const_sub differentiableOn_id;
      unfold Set.MapsTo; simp;
      apply differentiableOn_const;
      intro x _
      linarith

    apply Convex.monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
    apply DifferentiableOn.continuousOn diffW
    apply DifferentiableOn.mono diffW; simp; apply Set.Ioo_subset_Icc_self
    simp; intro x _ hx2; unfold W
    rw[deriv_div, deriv_sub]; simp; rw[ec, deriv.comp, deriv_sub]; simp;
    apply div_nonneg; apply mul_nonneg; apply le_of_lt;
    apply deriv_ei_pos; linarith; linarith; linarith; apply pow_nonneg; linarith; simp; simp
    apply DifferentiableOn.differentiableAt diffE; apply Ici_mem_nhds; linarith
    apply DifferentiableAt.const_sub; simp; apply differentiableAt_const;
    rw[ec]; apply DifferentiableAt.comp;
    apply DifferentiableOn.differentiableAt diffE; apply Ici_mem_nhds; linarith
    apply DifferentiableAt.const_sub; simp;
    apply DifferentiableAt.sub; simp;
    rw[ec]; apply DifferentiableAt.comp;
    apply DifferentiableOn.differentiableAt diffE; apply Ici_mem_nhds; linarith
    apply DifferentiableAt.const_sub; simp; apply differentiableAt_const; linarith

lemma mainlem64 (hc: c ≤ -1)  (hr: r > 0) (ht0: 0 ≤ t) (htp: t ≤ ΔP)
       (htr: t ≤ r)  (htd: r ≤ Δ) (hΔ:  ΔP ≤ Δ ): (W c Δ) r t ≤  (W c Δ) Δ ΔP := by
  have diffE : DifferentiableOn ℝ (E c) (Set.Ici 0) := by apply differentiable_E hc
  have ep : E c Δ > 0 := by apply err_pos hc; linarith
  have ec2 : (fun y ↦ E c (y - t)) = (fun y=> E c y) ∘ (fun y=>y-t) :=by ext y; simp;


  have diffWt: DifferentiableOn ℝ  (Wt c Δ t)  (Set.Ici t) :=by
    unfold Wt W
    apply DifferentiableOn.div; apply DifferentiableOn.sub;
    apply DifferentiableOn.mono diffE; apply Set.Ici_subset_Ici.mpr ht0
    rw[ec2]; apply DifferentiableOn.comp; assumption;
    apply DifferentiableOn.sub_const; apply differentiableOn_id;
    unfold Set.MapsTo; simp; apply differentiableOn_const;
    intro x _; linarith;

  have diffpc : DifferentiableOn ℝ (fun r ↦ Φ (c - r)) (Set.Ici 0):=by
    have : (fun r ↦ Φ (c - r)) = Φ ∘ (fun r => c -r) :=by ext r; simp;
    rw[this]; apply DifferentiableOn.comp differentiable_phi;
    apply DifferentiableOn.const_sub; apply differentiableOn_id;
    unfold Set.MapsTo; simp; intro x hx ; linarith;

  have diffEc : DifferentiableOn ℝ (fun r ↦ E c (r - t)) (Set.Ici t):=by
    have : (fun r ↦ E c (r-t)) = (E c) ∘ (fun r => r -t) :=by ext r; simp;
    rw[this]; apply DifferentiableOn.comp diffE;
    apply DifferentiableOn.sub_const; apply differentiableOn_id;
    unfold Set.MapsTo; simp

  have first : (W c Δ) r t ≤ (W c Δ) Δ t :=by
    rw[← Wt, ← Wt]
    apply Convex.monotoneOn_of_deriv_nonneg (convex_Ici t)
    apply DifferentiableOn.continuousOn diffWt
    apply DifferentiableOn.mono diffWt; simp;
    simp; intro x hx
    unfold Wt W
    rw[deriv_div, deriv_sub]; simp;
    apply div_nonneg; apply mul_nonneg;
    rw[ec2, deriv.comp]; simp; unfold E;
    rw[deriv_sub, deriv_sub, deriv_mul]; simp;
    rw[deriv_phi, deriv_comp_const_sub, deriv_phi];
    rw[deriv_sub, deriv_sub, deriv_mul]; simp;
    rw[ deriv_comp_const_sub, deriv_phi]; simp;
    rcases lt_or_eq_of_le ht0 with h | h
    set a:= c-(x-t)
    have e: c-x =a-t :=by ring_nf
    rw [e]; apply le_of_lt; apply dphi_anti; linarith; linarith
    rw[← h]; ring_nf; simp; linarith
    any_goals simp;
    any_goals apply DifferentiableOn.differentiableAt diffpc;
    any_goals apply Ici_mem_nhds;
    any_goals linarith;
    any_goals apply DifferentiableOn.differentiableAt diffE;
    any_goals apply Ici_mem_nhds;
    any_goals apply pow_nonneg;
    any_goals linarith;
    apply DifferentiableOn.differentiableAt diffEc (Ici_mem_nhds hx);
    apply DifferentiableAt.sub
    any_goals apply DifferentiableOn.differentiableAt diffE; apply Ici_mem_nhds; linarith
    apply DifferentiableOn.differentiableAt diffEc (Ici_mem_nhds hx);

  have second : (W c Δ) Δ t ≤ (W c Δ) Δ ΔP := by
    apply monoW;
    any_goals simp;
    any_goals linarith;
    apply And.intro ht0; linarith
    apply And.intro; linarith; linarith
  linarith


lemma W_pos  (hc: c ≤ -1) (hr1 : 0 < r)  (ht0: 0 ≤ t) (htr: t ≤ r)  (htd: r ≤ Δ) :  W c Δ r t ≥ 0:= by
  have : W c Δ r 0 = 0 :=by simp[W]
  rw[← this]; apply monoW;
  any_goals simp;
  any_goals linarith;
  apply And.intro ht0 htr



lemma W_eq_Q_Δ (hc: c ≤ -1) (hΔ : Δ >0): 1 - Q Δ c (Δ - ΔP) = (W c Δ) Δ ΔP:=by
  unfold W Q;
  have ep : E c Δ > 0 := by apply err_pos; linarith; assumption
  field_simp;

lemma W_eq_Q  (hc: c ≤ -1) (hΔ : Δ >0):  Q Δ c r - Q Δ c rr = W c Δ r (r - rr) :=by
  unfold W Q; simp
  have ep : E c Δ > 0 := by apply err_pos; linarith; assumption
  field_simp;

lemma lemma67sub (hc: c ≤ -1) (hr: r>0) (ht0: 0 ≤ r - rr) (htp: r - rr ≤ ΔP) (hrr: rr ≥ 0)
            (htd: r ≤ Δ) (hΔ:  ΔP ≤ Δ ) :  |Q Δ c r - Q Δ c rr| ≤ 1 - Q Δ c (Δ - ΔP) :=by
  have e1: |Q Δ c r - Q Δ c rr| = Q Δ c r - Q Δ c rr := by
    apply abs_of_nonneg; rw[W_eq_Q]; apply W_pos;
    any_goals linarith
  rw[e1, W_eq_Q_Δ, W_eq_Q ];
  apply mainlem64
  any_goals linarith;



lemma lemma67 (hc : c ≤ -1) (hr1 : 0 < r) (hr2 : r < Δ) (hΔ:  ΔP < Δ ) (hΔP:  ΔP > 0 ):
    |Q Δ c r - Q Δ c (Int.floor (r / ΔP) * ΔP)| ≤ 1 - Q_hi Δ (Δ - ΔP) := by
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
    apply lemma67sub
    any_goals linarith
  have i2: Q Δ c (Δ - ΔP) ≥  Q_hi Δ (Δ - ΔP):= by apply q_lower_bound; assumption; linarith; linarith
  linarith
