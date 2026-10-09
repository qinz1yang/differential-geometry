import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinAlternativesNonneg_S27

/-!
# CH12-S27: reduction of `boundaryVolumeCollapsed` to ambient `w`-collapse (C4 G3, part 3)

For a late cut family `L`, the interior scale theorem T2 (`eventually_interior_scale_ambient_T2`,
with the proved `collarNegativePlane_S16`) identifies, at every thin point at boundary distance
`> 10`, the curvature scale and the ball volumes of the piece with those of the ambient normalized
slice component.  Hence `boundaryVolumeCollapsed` of the piece follows from the *outer thinness*
input `hAmb`: the ambient slice is `w`-collapsed at the image of such points.  `hAmb` is supplied
by the H group / buffer chain; it is an explicit argument here.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open GC.Endpoint GC.Topology GC.LongTime Set
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

namespace LateCutFamily

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g} {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- **Reduction.**  Interior `w`-collapse (T2 transfer) + outer thinness `hAmb` give
`boundaryVolumeCollapsed` of every late thin piece. -/
theorem boundaryVolumeCollapsed_of_ambient_S27
    (L : GC.LongTime.LateCutFamily F K slices) (w : ℝ)
    (hAmb : ∃ N₀ : ℕ, ∀ j, N₀ ≤ j → ∀ C i, L.thin j C i →
      ∀ p : ((L.decomposition j C).component i).Carrier,
        ENNReal.ofReal 10 <
          distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p →
        volumeCollapsedAtCurvatureScale ((slices j).componentMetric C) w
          (cutPieceMap (L.decomposition j C) i p)) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ C i, L.thin j C i →
      boundaryVolumeCollapsed ((L.decomposition j C).component i) (L.metric j C i) w := by
  obtain ⟨N₀, hA⟩ := hAmb
  obtain ⟨N₁, hN⟩ := eventually_interior_scale_ambient_T2 L (collarNegativePlane_S16 K)
  refine ⟨max N₀ N₁, fun j hj C i hi p hD => ?_⟩
  have hD' : ENNReal.ofReal 10 <
      distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p := hD
  obtain ⟨-, -, hrad, hr⟩ := hN j ((le_max_right _ _).trans hj) C i hi p hD'
  intro r hr0 hcr
  have hamb := hA j ((le_max_left _ _).trans hj) C i hi p hD' r hr0 (hrad.trans hcr)
  rw [(hr r hr0 hcr.ge).2.1]
  exact hamb

/-- The `hasThinVolumeGeometry` alternative for late thin pieces: the boundary-free case needs
only `hAmb` (distance to the empty boundary is `⊤`); the case with boundary additionally needs a
nearly cuspidal boundary of size `w` (the truncation depth, supplied by C4). -/
theorem hasThinVolumeGeometry_of_ambient_S27
    (L : GC.LongTime.LateCutFamily F K slices) (w : ℝ)
    (hAmb : ∃ N₀ : ℕ, ∀ j, N₀ ≤ j → ∀ C i, L.thin j C i →
      ∀ p : ((L.decomposition j C).component i).Carrier,
        ENNReal.ofReal 10 <
          distanceToBoundary ((L.decomposition j C).component i) (L.metric j C i) p →
        volumeCollapsedAtCurvatureScale ((slices j).componentMetric C) w
          (cutPieceMap (L.decomposition j C) i p))
    (hB : ∀ j C i, L.thin j C i →
      ((L.decomposition j C).component i).model.boundary
          ((L.decomposition j C).component i).Carrier ≠ ∅ →
        Nonempty (NearlyCuspidalBoundary ((L.decomposition j C).component i)
          (L.metric j C i) (K + 4) w)) :
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ C i, L.thin j C i →
      hasThinVolumeGeometry ((L.decomposition j C).component i) (L.metric j C i) K w := by
  obtain ⟨N, hN⟩ := boundaryVolumeCollapsed_of_ambient_S27 L w hAmb
  refine ⟨N, fun j hj C i hi => ?_⟩
  have hv := hN j hj C i hi
  by_cases hb : ((L.decomposition j C).component i).model.boundary
      ((L.decomposition j C).component i).Carrier = ∅
  · refine Or.inl ⟨hb, fun p => hv p ?_⟩
    rw [distanceToBoundary_eq_top_of_boundary_empty _ _ hb p]
    exact ENNReal.ofReal_lt_top
  · exact Or.inr ⟨hB j C i hi hb, hv⟩

end LateCutFamily

end GC.LongTime.Ch12
