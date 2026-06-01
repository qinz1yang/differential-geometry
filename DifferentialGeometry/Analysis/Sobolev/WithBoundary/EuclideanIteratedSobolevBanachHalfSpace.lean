import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevBanach
import DifferentialGeometry.Analysis.Sobolev.Euclidean.IteratedSobolevHalfSpace

/-!
# Sequential completeness of the iterated Euclidean half-space Sobolev space `W^{k,p}_0`

This is the with-boundary mirror of `EuclideanIteratedSobolevBanach.lean`.

For a half-space-friendly carrier `Ω ⊆ EuclideanSpace ℝ (Fin d)`, the Dirichlet
half-space iterated Sobolev predicate `MemWkpHalfSpace k p u Ω` is *defined* as
the boundaryless `MemWkp k p u (interiorHalfSpace Ω)`, evaluated on the open
*interior part* of `Ω` (the slice strictly above the boundary hyperplane). The
half-space norm `wkpNormHalfSpace k p u Ω` is defined analogously.

Consequently, sequential completeness of `MemWkpHalfSpace` follows immediately
by re-application of the boundaryless completeness theorem
`MemWkp.exists_limit_of_wkpNorm_cauchy` to the open set `interiorHalfSpace Ω`.

## Main result

* `MemWkpHalfSpace.exists_limit_of_wkpNormHalfSpace_cauchy` — every Cauchy
  sequence with respect to `wkpNormHalfSpace` has a limit in
  `MemWkpHalfSpace`, with `wkpNormHalfSpace`-convergence.

The result holds for `1 ≤ p < ∞` and any half-space-friendly carrier.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- **Cauchy completeness** of the iterated Euclidean Dirichlet half-space
Sobolev space `W^{k,p}_0(Ω)`: every Cauchy sequence with respect to the
`wkpNormHalfSpace` semi-distance has a limit in `MemWkpHalfSpace k p`, with
`wkpNormHalfSpace`-convergence.

The proof reduces directly to the boundaryless theorem
`MemWkp.exists_limit_of_wkpNorm_cauchy` applied to the *open interior part*
`interiorHalfSpace Ω`, which is open in `E` whenever `Ω` is half-space-friendly. -/
theorem MemWkpHalfSpace.exists_limit_of_wkpNormHalfSpace_cauchy
    {Ω : Set E} (hΩ : IsHalfSpaceRelOpen (d := d) Ω)
    (k : ℕ) (p : ℝ≥0∞) (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {u : ℕ → E → ℝ}
    (hu_mem : ∀ n, MemWkpHalfSpace (d := d) k p (u n) Ω)
    (hu_cauchy : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNormHalfSpace (d := d) k p (fun x => u m x - u n x) Ω ≤
        ENNReal.ofReal ε) :
    ∃ u_lim : E → ℝ,
      MemWkpHalfSpace (d := d) k p u_lim Ω ∧
      Filter.Tendsto
        (fun n => wkpNormHalfSpace (d := d) k p (fun x => u n x - u_lim x) Ω)
        Filter.atTop (𝓝 0) := by
  have hΩ_open : IsOpen (interiorHalfSpace (d := d) Ω) :=
    interiorHalfSpace_isOpen hΩ
  have hu_mem' : ∀ n, MemWkp (d := d) k p (u n) (interiorHalfSpace Ω) := hu_mem
  have hu_cauchy' : ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n →
      wkpNorm (d := d) k p (fun x => u m x - u n x)
        (interiorHalfSpace Ω) ≤ ENNReal.ofReal ε := hu_cauchy
  obtain ⟨u_lim, hu_lim_mem, h_tendsto⟩ :=
    MemWkp.exists_limit_of_wkpNorm_cauchy hΩ_open k p hp_one hp_top
      hu_mem' hu_cauchy'
  refine ⟨u_lim, hu_lim_mem, ?_⟩
  exact h_tendsto

end Euclidean
end Sobolev
end Analysis
end DifferentialGeometry
