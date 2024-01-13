import Mathlib.Analysis.Calculus.LHopital
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

variable {Δ r : Real}
variable (delta_pos : Δ > 0)

lemma lemma61 : Tendsto (fun i => Q Δ i r) atBot (𝓝 (Q_hi Δ r)) := by
  sorry

lemma lemma62 (hr1 : 0 ≤ r) (hr2 : r < Δ) : AntitoneOn (fun i => Q Δ i r) (Set.Iic 0) := by
  sorry

lemma q_lower_bound (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) : Q_lo Δ r ≤ Q Δ i r :=
  lemma62 hr1 hr2 hi Set.right_mem_Iic hi

lemma q_upper_bound (hi : i ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) : Q Δ i r ≤ Q_hi Δ r := by
  suffices h : ∀ᶠ (x : ℝ) in atBot, Q Δ i r ≤ Q Δ x r
  · exact ge_of_tendsto (@lemma61 Δ r) h
  · rw [eventually_atBot]
    exact ⟨i, fun j ji => lemma62 hr1 hr2 (le_trans ji hi) hi ji⟩

lemma lemma63 (hi : i ≤ 0) (hc : c ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    |Q Δ i r - Q Δ c r| ≤ Q_hi Δ (R_opt Δ) - Q_lo Δ (R_opt Δ) := by
  sorry

lemma lemma64 {Δₚ} (hc : c ≤ 0) (hr1 : 0 ≤ r) (hr2 : r < Δ) :
    |Q Δ c r - Q Δ c (Int.ceil (r / Δₚ) * Δₚ)| ≤ 1 - Q_lo Δ (Δ - Δₚ) := by
  sorry
