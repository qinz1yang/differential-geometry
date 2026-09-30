import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EscapeFiniteHornLimitRealization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelWitnesses

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.DifferentialGeometry.Manifold ContDiff ENNReal

universe u

attribute [local instance] CheegerGromovLimit.metricSpace CheegerGromovLimit.charted
  CheegerGromovLimit.smooth CheegerGromovLimit.sigmaCompact

noncomputable def hornScaleRadii {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
    [IsManifold I3 ∞ W] {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) : ℕ → ℝ :=
  fun i => min (H.axial.length / 2) ((i : ℝ) + 1)⁻¹

theorem hornScaleRadii_mem {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
    [IsManifold I3 ∞ W] {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) (i : ℕ) : hornScaleRadii H i ∈ Set.Ioc 0 H.axial.length := by
  have hhalf : 0 < H.axial.length / 2 := half_pos H.axial.length_pos
  have hpos : 0 < ((i : ℝ) + 1)⁻¹ := inv_pos.mpr (by positivity)
  exact ⟨lt_min hhalf hpos, (min_le_left _ _).trans (by linarith [H.axial.length_pos])⟩

theorem hornScaleRadii_tendsto_zero {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
    [IsManifold I3 ∞ W] {g : SmoothRiemannianMetric I3 W}
    (H : FiniteHorn g) : Filter.Tendsto (hornScaleRadii H) Filter.atTop (nhds 0) := by
  have hhalf : 0 ≤ H.axial.length / 2 := (half_pos H.axial.length_pos).le
  have hrec : Filter.Tendsto (fun i : ℕ => ((i : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hmin : Filter.Tendsto
      (fun i : ℕ => min (H.axial.length / 2) ((i : ℝ) + 1)⁻¹) Filter.atTop
      (nhds (min (H.axial.length / 2) 0)) := tendsto_const_nhds.min hrec
  rw [min_eq_right hhalf] at hmin
  exact hmin

theorem nonempty_hornOnLimit_of_finiteHorn_of_frontiers {X : FlowSequence.{u}}
    {L : CheegerGromovLimit X} (horn : FiniteHorn L.metric)
    (hdepth : hornDepthThreshold.{u} ≤ horn.collarDepth)
    (hnet : ScaleDirectionNet L.metric horn)
    (hsep : ScaleSeparatedEndRays L.metric horn)
    (hcone : ∀ (angles : EndAngles horn) (ray : EndRay horn.endpoint) (d : ℕ → ℝ),
      (∀ i, d i ∈ Set.Ioc 0 ray.length) → Filter.Tendsto d Filter.atTop (nhds 0) →
      ConeDistanceRealization horn angles ray d)
    (hupper : ScaleCurvatureUpperBound horn horn.axial (hornScaleRadii horn)) :
    Nonempty (HornOnLimit X L) :=
  ⟨{ horn := horn
     radii := hornScaleRadii horn
     radii_mem := hornScaleRadii_mem horn
     radii_zero := hornScaleRadii_tendsto_zero horn
     directionNet := hnet
     separatedRays := hsep
     coneRealization := hcone
     depth_ok := hdepth
     curvatureUpper := hupper }⟩

theorem finiteHorn_frontiers_of_hornOnLimit {X : FlowSequence.{u}} {L : CheegerGromovLimit X}
    (K : HornOnLimit X L) :
    hornDepthThreshold.{u} ≤ K.horn.collarDepth ∧
      ScaleDirectionNet L.metric K.horn ∧ ScaleSeparatedEndRays L.metric K.horn ∧
      (∀ (angles : EndAngles K.horn) (ray : EndRay K.horn.endpoint) (d : ℕ → ℝ),
        (∀ i, d i ∈ Set.Ioc 0 ray.length) → Filter.Tendsto d Filter.atTop (nhds 0) →
        ConeDistanceRealization K.horn angles ray d) ∧
      ScaleCurvatureUpperBound K.horn K.horn.axial K.radii :=
  ⟨K.depth_ok, K.directionNet, K.separatedRays, K.coneRealization, K.curvatureUpper⟩

theorem nonempty_hornOnLimit_of_collarDepthFrontiers {X : FlowSequence.{u}}
    {L : CheegerGromovLimit X} {H₀ : ℝ}
    (hnet : ∀ (g : SmoothRiemannianMetric I3 L.space) (H : FiniteHorn g),
      H₀ ≤ H.collarDepth → ScaleDirectionNet g H)
    (hsep : ∀ (g : SmoothRiemannianMetric I3 L.space) (H : FiniteHorn g),
      H₀ ≤ H.collarDepth → ScaleSeparatedEndRays g H)
    (hcone : ∀ (g : SmoothRiemannianMetric I3 L.space) (H : FiniteHorn g),
      H₀ ≤ H.collarDepth →
      ∀ (angles : EndAngles H) (ray : EndRay H.endpoint) (d : ℕ → ℝ),
        (∀ i, d i ∈ Set.Ioc 0 ray.length) → Filter.Tendsto d Filter.atTop (nhds 0) →
        ConeDistanceRealization H angles ray d)
    (horn : FiniteHorn L.metric)
    (hdepth : max H₀ (hornDepthThreshold.{u}) ≤ horn.collarDepth)
    (hupper : ScaleCurvatureUpperBound horn horn.axial (hornScaleRadii horn)) :
    Nonempty (HornOnLimit X L) :=
  nonempty_hornOnLimit_of_finiteHorn_of_frontiers horn
    ((le_max_right H₀ (hornDepthThreshold.{u})).trans hdepth)
    (hnet L.metric horn ((le_max_left H₀ (hornDepthThreshold.{u})).trans hdepth))
    (hsep L.metric horn ((le_max_left H₀ (hornDepthThreshold.{u})).trans hdepth))
    (hcone L.metric horn ((le_max_left H₀ (hornDepthThreshold.{u})).trans hdepth)) hupper

def FiniteHornEndRealization.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
      RealizedDistanceCurvatureEscape X →
        ∃ L : CheegerGromovLimit X.toFlowSequence, ∃ horn : FiniteHorn L.metric,
          hornDepthThreshold.{v} ≤ horn.collarDepth ∧
          ScaleDirectionNet L.metric horn ∧ ScaleSeparatedEndRays L.metric horn ∧
          (∀ (angles : EndAngles horn) (ray : EndRay horn.endpoint) (d : ℕ → ℝ),
            (∀ i, d i ∈ Set.Ioc 0 ray.length) → Filter.Tendsto d Filter.atTop (nhds 0) →
            ConeDistanceRealization horn angles ray d) ∧
          ScaleCurvatureUpperBound horn horn.axial (hornScaleRadii horn)

theorem hornOnLimitRealization_of_finiteHornEndRealization {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : FiniteHornEndRealization.{u} kappa sigma Phi) :
    HornOnLimitRealization.{u} kappa sigma Phi := by
  obtain ⟨e, he, hmain⟩ := h
  exact ⟨e, he, fun eps hp hle X hX => by
    obtain ⟨L, horn, hdepth, hnet, hsep, hcone, hupper⟩ := hmain eps hp hle X hX
    exact ⟨L, nonempty_hornOnLimit_of_finiteHorn_of_frontiers
      horn hdepth hnet hsep hcone hupper⟩⟩

theorem escapeFiniteHornRealization_of_finiteHornEndRealization
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : FiniteHornEndRealization.{u} kappa sigma Phi) :
    EscapeFiniteHornRealization.{u} kappa sigma Phi :=
  escapeFiniteHornRealization_iff_hornOnLimitRealization.mpr
    (hornOnLimitRealization_of_finiteHornEndRealization h)

theorem exists_endAngles_of_hornOnLimit {X : FlowSequence.{u}} {L : CheegerGromovLimit X}
    (K : HornOnLimit X L) : Nonempty (EndAngles K.horn) :=
  (RealizedFiniteHorn.ofParts L K).end_rays.elim fun e =>
    (RealizedFiniteHorn.ofParts L K).end_angle e

theorem directionCompactness_of_hornOnLimit {X : FlowSequence.{u}} {L : CheegerGromovLimit X}
    (K : HornOnLimit X L) (angles : EndAngles K.horn) :
    letI := angles.metric
    TotallyBounded (Set.univ : Set angles.quotient) ∧
      CompactSpace (UniformSpace.Completion angles.quotient) ∧
      ∃ a b : EndRay K.horn.endpoint, 0 < angles.angle a b :=
  (RealizedFiniteHorn.ofParts L K).end_rays.elim fun e =>
    finite_horn_direction_compactness K.horn e angles K.directionNet K.separatedRays

theorem exists_annularConvergence_of_hornOnLimit {X : FlowSequence.{u}} {L : CheegerGromovLimit X}
    (K : HornOnLimit X L) :
    ∃ angles : EndAngles K.horn,
      Nonempty (AnnularConvergence K.horn angles K.horn.axial K.radii) :=
  (RealizedFiniteHorn.ofParts L K).end_rays.elim fun e =>
    ((RealizedFiniteHorn.ofParts L K).end_angle e).elim fun angles =>
      ⟨angles, (RealizedFiniteHorn.ofParts L K).cone_convergence e angles K.horn.axial K.radii
        K.radii_mem K.radii_zero⟩

theorem exists_twoScaleComparison_of_hornOnLimit {X : FlowSequence.{u}} {L : CheegerGromovLimit X}
    (K : HornOnLimit X L) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ᶠ i in Filter.atTop,
      c ≤ metricScalarAt L.metric (K.horn.axial.point (K.radii i)) * K.radii i ^ 2 ∧
      metricScalarAt L.metric (K.horn.axial.point (K.radii i)) * K.radii i ^ 2 ≤ C :=
  finite_horn_two_scale_comparison_of_upper_bound K.horn K.horn.axial K.radii
    K.radii_mem K.radii_zero K.curvatureUpper.upper

theorem exists_hornBarriers_of_hornOnLimit {X : FlowSequence.{u}} {L : CheegerGromovLimit X}
    (K : HornOnLimit X L)
    (hlarge : Filter.Tendsto (fun i => metricScalarAt L.metric (K.horn.axial.point (K.radii i)) *
      K.radii i ^ 2) Filter.atTop Filter.atTop)
    (hexit : HornRadialExitPositionAtEndChart L.metric K.horn K.horn.axial K.radii) :
    Nonempty (HornBarriers K.horn K.horn.axial K.radii) :=
  (RealizedFiniteHorn.ofParts L K).end_rays.elim fun e =>
    finite_horn_barriers_of_hornRadialExitPositionAtEndChart K.horn e K.horn.axial K.radii
      K.radii_mem K.radii_zero hlarge hexit

def ScalarBoundedAbove {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 1 M]
    [CompleteSpace E] (g : SmoothRiemannianMetric I M) : Prop :=
  ∃ C : ℝ, ∀ x : M, metricScalarAt g x ≤ C

theorem not_nonempty_finiteHorn_of_scalarBoundedAbove {W : Type u} [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
    {g : SmoothRiemannianMetric I3 W} (h : ScalarBoundedAbove g) :
    ¬ Nonempty (FiniteHorn g) := by
  rintro ⟨H⟩
  obtain ⟨C, hC⟩ := h
  obtain ⟨i, hi⟩ := H.curvature_diverges C
  obtain ⟨d, hd, -, htail⟩ := H.cofinal_axial i
  have hs : d / 2 ∈ Set.Ioc (0 : ℝ) d := ⟨by linarith, by linarith⟩
  have hlt : C < metricScalarAt g (H.axial.point (d / 2)) := hi _ (htail (d / 2) hs)
  have hle : metricScalarAt g (H.axial.point (d / 2)) ≤ C := hC _
  linarith

theorem scalarBoundedAbove_of_ricciTensor_eq_zero {W : Type u} [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W]
    {g : SmoothRiemannianMetric I3 W}
    (hric : ∀ x (v w : TangentSpace I3 x), ricciTensor g x v w = 0) :
    ScalarBoundedAbove g :=
  ⟨0, fun x => by
    rw [metricScalarAt_eq_zero_of_ricciTensor_eq_zero g x (hric x)]⟩

theorem not_nonempty_finiteHorn_of_compactSpace {W : Type u} [MetricSpace W]
    [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] [CompactSpace W]
    {g : SmoothRiemannianMetric I3 W} : ¬ Nonempty (FiniteHorn g) := by
  rintro ⟨H⟩
  obtain ⟨d, hd, -, htail⟩ := H.cofinal_axial 0
  have hne : (Set.univ : Set W).Nonempty := ⟨H.axial.point (d / 2), Set.mem_univ _⟩
  obtain ⟨x, -, hmax⟩ := isCompact_univ.exists_isMaxOn hne
    (metricScalar_smooth g).continuous.continuousOn
  obtain ⟨i, hi⟩ := H.curvature_diverges (metricScalarAt g x)
  obtain ⟨d', hd', -, htail'⟩ := H.cofinal_axial i
  have hs : d' / 2 ∈ Set.Ioc (0 : ℝ) d' := ⟨by linarith, by linarith⟩
  have hlt : metricScalarAt g x < metricScalarAt g (H.axial.point (d' / 2)) :=
    hi _ (htail' (d' / 2) hs)
  have hle : metricScalarAt g (H.axial.point (d' / 2)) ≤ metricScalarAt g x :=
    hmax (Set.mem_univ _)
  linarith

theorem not_nonempty_finiteHorn_roundSphere_three :
    ¬ Nonempty (FiniteHorn (DifferentialGeometry.Geometry.roundMetric
      (E := EuclideanSpace ℝ (Fin 4)) (n := 3))) :=
  not_nonempty_finiteHorn_of_compactSpace

theorem scalarBoundedAbove_roundCylinderMetric :
    ScalarBoundedAbove (DifferentialGeometry.Geometry.Metric.roundCylinderMetric
      (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) :=
  ⟨1, fun x => (metricScalarAt_roundCylinderModel_eq_one x).le⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
