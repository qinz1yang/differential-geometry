import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NeckBox

/-!
# Chapter-14 assembly, item L1, group G3b: the chart-free sign of a neck against a ball

`ballNeckDetAmb B e x L` is the determinant of the endomorphism of `ℝ³`
`dι_x ∘ de_{e⁻¹x} ∘ (dB_{e⁻¹x})⁻¹ ∘ L ∘ J`, where `ι : ClosedCell 3 → ℝ³` is the inclusion and
`J = neckSpaceEquiv`. It is the ambient (chart-free) form of `ballNeckDet`: the differentials of
`e` and of the ball map are read in charts of `ClosedCell 3` and of `W`, and composing with `dι_x`
removes the chart of `ClosedCell 3` at `x`, so the sign of a product of two such determinants at
two different points `x₀`, `x₁` is intrinsic. This is the sign that the two-disk normalization G2
(`exists_closedCell_diffeomorph_eqOn_two_boundary_disks`, hypothesis `hori`) consumes.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1bB : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

/-- The ambient (chart-free) orientation of a neck differential `L` relative to the ball
`B ∘ e⁻¹ : ClosedCell 3 → W` at `x`. -/
def ballNeckDetAmb {W : CompactCarrier.{u}} (B : PieceEmbedding W)
    (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3) (x : ClosedCell 3)
    (L : (EuclideanSpace ℝ (Fin 2) × ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 3)) : ℝ :=
  LinearMap.det ((mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3))
      x).toLinearMap ∘ₗ (mfderiv (𝓡∂ 3) (𝓡∂ 3) e (e.symm x)).toLinearMap ∘ₗ
    (LinearEquiv.ofBijective (mfderiv (𝓡∂ 3) W.model B.map (e.symm x)).toLinearMap
      (B.mfderiv_bijective (e.symm x))).symm.toLinearMap ∘ₗ L.toLinearMap ∘ₗ
    neckSpaceEquiv.toLinearMap)

end GC.GraphManifold.Assembly
