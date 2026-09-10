import Batteries.Tactic.Alias
import DifferentialGeometry.Geometry.Comparison.FarPoint
import DifferentialGeometry.Geometry.Submanifold.IsometricImmersion
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.Pointwise
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold Set
open scoped Bundle ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry

section Carrier

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
    Tensor0SBundle.tangentSpaceNormedSpace in
theorem no_compact_geodesic_carrier
    [ConnectedSpace M] [NoncompactSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsec : hasPositiveSectionalCurvature (I := I) g)
    (hdim : 2 ≤ Module.finrank ℝ E)
    (C : Set M) (hCne : C.Nonempty) (hCcompact : IsCompact C)
    (hgerms : ∀ x ∈ C, ∃ alpha : ℝ → M,
      alpha 0 = x ∧ isUnitSpeedGeodesicGermIn g C alpha) :
    False := by
  classical
  obtain ⟨D, hDcompact, _hCD, hfar⟩ :=
    farPoint_noLocalMin_of_geodesicAt
      (I := I) g hcomplete hsec hdim C hCne hCcompact
  obtain ⟨q, hqD⟩ : ∃ q : M, q ∉ D := by
    by_contra hq
    push Not at hq
    exact hDcompact.ne_univ (Set.eq_univ_of_forall hq)
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun x : M ↦ TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  have hdistanceContinuous : ContinuousOn
      (fun z : M ↦ (riemannianEDistOf (I := I) g q z).toReal) C := by
    have hfinite : C ⊆
        {z : M | riemannianEDist I q z ≠ (⊤ : ℝ≥0∞)} := by
      intro z _hz
      exact riemannianEDist_ne_top (I := I) q z
    have hcontinuous :=
      continuousOn_riemannianEDist_toReal_on_finite (I := I) g q
    simpa only [riemannianEDistOf] using hcontinuous.mono hfinite
  obtain ⟨x, hxC, hxmin⟩ :=
    hCcompact.exists_isMinOn hCne hdistanceContinuous
  obtain ⟨alpha, halpha0, halphaGerm⟩ := hgerms x hxC
  obtain ⟨epsilon, hepsilon, halphaGeodesicAt, _halphaSmooth,
      _halphaGeodesic, halphaUnit, halphaMapsTo⟩ := halphaGerm
  have hzero : (0 : ℝ) ∈ Set.Ioo (-epsilon) epsilon :=
    ⟨neg_lt_zero.mpr hepsilon, hepsilon⟩
  have hlocalMin : IsLocalMin
      (fun s : ℝ ↦
        (riemannianEDistOf (I := I) g q (alpha s)).toReal) 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    rw [halpha0]
    exact hxmin (halphaMapsTo hs)
  exact (hfar q hqD alpha halphaGeodesicAt
    (halphaMapsTo hzero) (halphaUnit 0 hzero)) hlocalMin

end Carrier

section Immersion

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

theorem no_compact_positive_dimensional_geodesic_preserving_isometric_immersion
    [Nonempty N] [CompactSpace N]
    [ConnectedSpace M] [NoncompactSpace M]
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : 2 ≤ Module.finrank ℝ E)
    (iota : N → M)
    (hisom : IsRiemannianIsometricImmersion gN gM iota)
    (hgeodesic : preservesGeodesics gN gM iota)
    (hdimN : 0 < Module.finrank ℝ EN) :
    False := by
  let C : Set M := Set.range iota
  have hCne : C.Nonempty := Set.range_nonempty iota
  have hCcompact : IsCompact C := by
    simpa only [C, Set.image_univ] using
      (isCompact_univ.image hisom.continuous)
  apply no_compact_geodesic_carrier
    (I := I) gM hcomplete hsec hdimM C hCne hCcompact
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  exact exists_unit_speed_geodesic_germ_in_range
    gN gM iota hisom hgeodesic hdimN y

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
    Tensor0SBundle.tangentSpaceNormedSpace in
theorem no_compact_positive_dimensional_vanishingSecondFundamentalFormAlongCurves_isometric_immersion
    [Nonempty N] [CompactSpace N] [T2Space N]
    [ConnectedSpace M] [NoncompactSpace M]
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : 2 ≤ Module.finrank ℝ E)
    (iota : N → M)
    (hisom : IsRiemannianIsometricImmersion gN gM iota)
    (hII : hasVanishingSecondFundamentalFormAlongCurves gN gM iota)
    (hdimN : 0 < Module.finrank ℝ EN) :
    False := by
  let C : Set M := Set.range iota
  have hCne : C.Nonempty := Set.range_nonempty iota
  have hCcompact : IsCompact C := by
    simpa only [C, Set.image_univ] using
      (isCompact_univ.image hisom.continuous)
  apply no_compact_geodesic_carrier
    (I := I) gM hcomplete hsec hdimM C hCne hCcompact
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  exact
    exists_unit_speed_geodesic_germ_in_range_of_vanishingSecondFundamentalForm
      gN gM iota hisom hII hdimN y

theorem no_compact_positive_dimensional_vanishingSecondFundamentalForm_isometric_immersion
    [Nonempty N] [CompactSpace N] [T2Space N]
    [ConnectedSpace M] [NoncompactSpace M]
    (gN : SmoothRiemannianMetric IN N)
    (gM : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) gM)
    (hsec : hasPositiveSectionalCurvature (I := I) gM)
    (hdimM : 2 ≤ Module.finrank ℝ E)
    (iota : N → M)
    (hisom : IsRiemannianIsometricImmersion gN gM iota)
    (hII : hisom.hasVanishingSecondFundamentalForm)
    (hdimN : 0 < Module.finrank ℝ EN) :
    False :=
  no_compact_positive_dimensional_vanishingSecondFundamentalFormAlongCurves_isometric_immersion
    gN gM hcomplete hsec hdimM iota hisom hII.along_curves hdimN

end Immersion

end DifferentialGeometry.Geometry

namespace Poincare.Geometry

alias no_compact_geodesic_carrier := DifferentialGeometry.Geometry.no_compact_geodesic_carrier
alias no_compact_positive_dimensional_geodesic_preserving_isometric_immersion := DifferentialGeometry.Geometry.no_compact_positive_dimensional_geodesic_preserving_isometric_immersion
alias no_compact_positive_dimensional_vanishingSecondFundamentalFormAlongCurves_isometric_immersion := DifferentialGeometry.Geometry.no_compact_positive_dimensional_vanishingSecondFundamentalFormAlongCurves_isometric_immersion
alias no_compact_positive_dimensional_vanishingSecondFundamentalForm_isometric_immersion := DifferentialGeometry.Geometry.no_compact_positive_dimensional_vanishingSecondFundamentalForm_isometric_immersion

end Poincare.Geometry
