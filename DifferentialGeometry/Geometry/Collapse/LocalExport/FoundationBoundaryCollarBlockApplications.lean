import DifferentialGeometry.Geometry.Collapse.LocalExport.FoundationBoundaryCollarBlock

/-!
# Consumer of FC43: the ORIGINAL torus collar core read off the boundary block

FC43 extracts the torus collar core by "the adjusted marker `x''_i ≥ .9` with ratio `≤ 40`". For the
ORIGINAL block `(η_i ζ_i, ζ_i)` of `fc43_collar_block_FCF` this condition is a level band of the
physical collar coordinate: `ζ_i ≥ .9` and `u ≤ 40 v` force `20 < η_i ≤ 40`, and on the collar band
every level `30 ≤ η_i ≤ 40` satisfies both (`fc43_original_core_FCF`). The adjusted core (the same
test on the final boundary map) is BCG06's, on the boundary chain object.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} [ConnectedSpace W.Carrier]
  {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- **Consumer of FC43**: the original collar core test `ζ_i ≥ .9`, `u ≤ 40 v` on the block
`(u, v) = (η_i ζ_i, ζ_i)` confines the physical collar coordinate to `20 < η_i ≤ 40`, and on the
collar band every level `30 ≤ η_i ≤ 40` passes the test. -/
theorem fc43_original_core_FCF (P : BoundaryExportPacket W g K A w₀ ε) (i : Fin P.cusp.count) :
    (∀ x, 9 / 10 ≤ P.cutoff i x → (P.block i x).1 ≤ 40 * (P.block i x).2 →
      20 < P.height i x ∧ P.height i x ≤ 40) ∧
    ∀ p : CuspHalfSpace, 2 < p.2.val 0 → p.2.val 0 < 98 →
      P.height i ((P.cusp.collar i).toFun p) ∈ Icc (30 : ℝ) 40 →
      9 / 10 ≤ P.cutoff i ((P.cusp.collar i).toFun p) ∧
        (P.block i ((P.cusp.collar i).toFun p)).1 ≤
          40 * (P.block i ((P.cusp.collar i).toFun p)).2 := by
  obtain ⟨-, hblk, -, -, hsupp, hplat, -⟩ := fc43_collar_block_FCF P i
  refine ⟨fun x h9 h40 => ?_, fun p h2 h98 hη => ?_⟩
  · obtain ⟨h1, h2⟩ := hblk x
    have hpos : 0 < P.cutoff i x := by linarith
    have hne : P.block i x ≠ 0 := by
      intro h0
      rw [h0] at h2
      change (0 : ℝ) = P.cutoff i x at h2
      linarith
    refine ⟨(hsupp x hne).1, ?_⟩
    rw [h1, h2] at h40
    exact le_of_mul_le_mul_right h40 hpos
  · have hone := hplat p h2 h98 ⟨hη.1, hη.2.trans (by norm_num)⟩
    obtain ⟨h1, h2'⟩ := hblk ((P.cusp.collar i).toFun p)
    refine ⟨by rw [hone]; norm_num, ?_⟩
    rw [h1, h2', hone]
    linarith [hη.2]

end DifferentialGeometry.Geometry.Collapse
