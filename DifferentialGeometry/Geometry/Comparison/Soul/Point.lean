import Batteries.Tactic.Alias
import DifferentialGeometry.Geometry.Comparison.Soul.Defs
import DifferentialGeometry.Geometry.Comparison.CompactGeodesicCarrier
import DifferentialGeometry.Topology.Manifold.ZeroDimensional
import Mathlib.Data.Set.Subsingleton

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

variable {EN HN N E H M : Type*}
  [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
  [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN} [IN.Boundaryless]
  [TopologicalSpace N] [ChartedSpace HN N] [IsManifold IN ∞ N]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
  [T2Space (TangentBundle I M)]

theorem subsingleton_of_compact_connected_geodesic_preserving_isometric_immersion
    [CompactSpace N] [ConnectedSpace N]
    [ConnectedSpace M] [NoncompactSpace M]
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : 2 ≤ Module.finrank ℝ E)
    (iota : N → M)
    (hisom : IsRiemannianIsometricImmersion gN gM iota)
    (hgeodesic : preservesGeodesics gN gM iota) :
    Subsingleton N := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ EN) with hdimN | hdimN
  · exact subsingleton_of_preconnected_of_finrank_eq_zero IN hdimN
  · exfalso
    exact no_compact_positive_dimensional_geodesic_preserving_isometric_immersion
      gN gM hcomplete hsec hdimM iota hisom hgeodesic hdimN

theorem subsingleton_of_compact_connected_vanishingSecondFundamentalForm_isometric_immersion
    [CompactSpace N] [ConnectedSpace N] [T2Space N]
    [ConnectedSpace M] [NoncompactSpace M]
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : 2 ≤ Module.finrank ℝ E)
    (iota : N → M)
    (hisom : IsRiemannianIsometricImmersion gN gM iota)
    (hII : hisom.hasVanishingSecondFundamentalForm) :
    Subsingleton N := by
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ EN) with hdimN | hdimN
  · exact subsingleton_of_preconnected_of_finrank_eq_zero IN hdimN
  · exfalso
    exact
      no_compact_positive_dimensional_vanishingSecondFundamentalForm_isometric_immersion
        gN gM hcomplete hsec hdimM iota hisom hII hdimN

namespace GeodesicPreservingSoul

theorem subsingleton
    [ConnectedSpace M] [NoncompactSpace M]
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (soul : GeodesicPreservingSoul gN gM iota)
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : 2 ≤ Module.finrank ℝ E) :
    Subsingleton N := by
  let _ : Nonempty N := soul.nonempty
  let _ : CompactSpace N := soul.compactSpace
  let _ : ConnectedSpace N := soul.connectedSpace
  exact subsingleton_of_compact_connected_geodesic_preserving_isometric_immersion
    gN gM hcomplete hsec hdimM iota soul.isometricImmersion
      soul.preservesGeodesics

theorem range_eq_singleton
    [ConnectedSpace M] [NoncompactSpace M]
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (soul : GeodesicPreservingSoul gN gM iota)
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : 2 ≤ Module.finrank ℝ E) :
    ∃ p : M, Set.range iota = {p} := by
  let _ : Subsingleton N := soul.subsingleton hcomplete hsec hdimM
  let _ : Nonempty N := soul.nonempty
  obtain ⟨x0⟩ := soul.nonempty
  refine ⟨iota x0, Set.range_eq_singleton ?_⟩
  intro x
  rw [Subsingleton.elim x x0]

end GeodesicPreservingSoul

namespace Soul

theorem subsingleton
    [ConnectedSpace M] [NoncompactSpace M]
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (soul : Soul gN gM iota)
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : 2 ≤ Module.finrank ℝ E) :
    Subsingleton N := by
  let _ : Nonempty N := soul.nonempty
  let _ : CompactSpace N := soul.compactSpace
  let _ : ConnectedSpace N := soul.connectedSpace
  let _ : T2Space N := soul.isSmoothEmbedding.isEmbedding.t2Space
  exact
    subsingleton_of_compact_connected_vanishingSecondFundamentalForm_isometric_immersion
      gN gM hcomplete hsec hdimM iota soul.isometricImmersion
        soul.vanishingSecondFundamentalForm

theorem range_eq_singleton
    [ConnectedSpace M] [NoncompactSpace M]
    {gN : SmoothRiemannianMetric IN N}
    {gM : SmoothRiemannianMetric I M} {iota : N → M}
    (soul : Soul gN gM iota)
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : 2 ≤ Module.finrank ℝ E) :
    ∃ p : M, Set.range iota = {p} := by
  let _ : Subsingleton N := soul.subsingleton hcomplete hsec hdimM
  let _ : Nonempty N := soul.nonempty
  obtain ⟨x0⟩ := soul.nonempty
  refine ⟨iota x0, Set.range_eq_singleton ?_⟩
  intro x
  rw [Subsingleton.elim x x0]

end Soul

theorem isSoul.eq_singleton
    [ConnectedSpace M] [NoncompactSpace M]
    {g : SmoothRiemannianMetric I M} {S : Set M} (hS : isSoul g S)
    (hcomplete : RiemannianMetricComplete g)
    (hsec : hasPositiveSectionalCurvature g)
    (hdim : 2 ≤ Module.finrank ℝ E) : ∃ p : M, S = {p} := by
  obtain ⟨d, c, m, gS, soul⟩ := hS
  let _ := c
  let _ := m
  simpa using soul.range_eq_singleton hcomplete hsec hdim

end DifferentialGeometry.Geometry

namespace Poincare.Geometry

alias subsingleton_of_compact_connected_geodesic_preserving_isometric_immersion := DifferentialGeometry.Geometry.subsingleton_of_compact_connected_geodesic_preserving_isometric_immersion
alias subsingleton_of_compact_connected_vanishingSecondFundamentalForm_isometric_immersion := DifferentialGeometry.Geometry.subsingleton_of_compact_connected_vanishingSecondFundamentalForm_isometric_immersion
end Poincare.Geometry

namespace Poincare.Geometry.GeodesicPreservingSoulData

alias subsingleton := DifferentialGeometry.Geometry.GeodesicPreservingSoul.subsingleton
alias range_eq_singleton := DifferentialGeometry.Geometry.GeodesicPreservingSoul.range_eq_singleton
end Poincare.Geometry.GeodesicPreservingSoulData

namespace Poincare.Geometry.VanishingSecondFundamentalFormSoulData

alias subsingleton := DifferentialGeometry.Geometry.Soul.subsingleton
alias range_eq_singleton := DifferentialGeometry.Geometry.Soul.range_eq_singleton
end Poincare.Geometry.VanishingSecondFundamentalFormSoulData

namespace Poincare.Geometry.isSoul

alias eq_singleton := DifferentialGeometry.Geometry.isSoul.eq_singleton

end Poincare.Geometry.isSoul
