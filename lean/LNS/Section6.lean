import Mathlib.Analysis.Calculus.LHopital
import LNS.Common
import LNS.Basic

noncomputable section

namespace LNS

open Real Filter Topology

def Q_lo Δ r := Q Δ 0 r

def Q_hi Δ r := (2 ^ (-r) + r * log 2 - 1) / (2 ^ (-Δ) + Δ * log 2 - 1)

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
