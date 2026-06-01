import DifferentialGeometry.Analysis.Sobolev.Euclidean.CompChainRuleK

/-!
# `eLpNorm`-of-second-iterated-Fréchet-derivative bound by `wkpNorm 2 2`

For a smooth function `u : EuclideanSpace ℝ (Fin d) → ℝ` with compact support
strictly inside an open set `Ω`, the `L²` norm of
`y ↦ ‖iteratedFDeriv ℝ 2 u y‖` (restricted to `Ω`) is bounded above by the
iterated Sobolev norm `wkpNorm 2 2 u Ω`.

This is the second-derivative analogue of
`chartTarget_fderiv_eLpNorm_le_wkpNorm_two`. The proof extracts the order-`2`
term from the bound
`∑_{n ≤ k} eLpNorm (‖iteratedFDeriv ℝ n ψ‖) p ≤ wkpNorm k p ψ Ω`
already supplied by `eLpNorm_iteratedFDeriv_le_wkpNorm`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

/-- **Second-iterated-Fréchet-derivative `L²` bound by `wkpNorm 2 2`.**
For a smooth function `u : EuclideanSpace ℝ (Fin d) → ℝ` with compact support
strictly inside an open set `Ω`, the `L²` norm of
`y ↦ ‖iteratedFDeriv ℝ 2 u y‖` (restricted to `Ω`) is bounded by the
iterated Sobolev norm `wkpNorm 2 2 u Ω`. -/
theorem chartTarget_iteratedFDeriv_two_eLpNorm_le_wkpNorm_two
    {Ω : Set EuclN} (hΩ_open : IsOpen Ω)
    {u : EuclN → ℝ} (hu_smooth : ContDiff ℝ ∞ u)
    (hu_compact : HasCompactSupport u) (hu_supp : tsupport u ⊆ Ω) :
    eLpNorm (fun y : EuclN => ‖iteratedFDeriv ℝ 2 u y‖) 2
        (volume.restrict Ω) ≤
      wkpNorm (d := d) 2 2 u Ω := by
  classical
  have hp_one : (1 : ℝ≥0∞) ≤ 2 := by
    exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)
  have hu_smooth' : ContDiff ℝ (⊤ : ℕ∞) u := hu_smooth
  have h_sum_le :=
    eLpNorm_iteratedFDeriv_le_wkpNorm (d := d) hΩ_open
      (p := (2 : ℝ≥0∞)) hp_one (k := 2)
      hu_smooth' hu_compact hu_supp
  have h2_mem : (2 : ℕ) ∈ Finset.range (2 + 1) := by
    rw [Finset.mem_range]; omega
  have h_single :
      eLpNorm (fun y : EuclN => ‖iteratedFDeriv ℝ 2 u y‖) 2
          (volume.restrict Ω) ≤
        ∑ n ∈ Finset.range (2 + 1),
          eLpNorm (fun y : EuclN => ‖iteratedFDeriv ℝ n u y‖) 2
            (volume.restrict Ω) :=
    Finset.single_le_sum
      (f := fun n : ℕ =>
        eLpNorm (fun y : EuclN => ‖iteratedFDeriv ℝ n u y‖) 2
          (volume.restrict Ω))
      (fun _ _ => zero_le _) h2_mem
  exact h_single.trans h_sum_le

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
