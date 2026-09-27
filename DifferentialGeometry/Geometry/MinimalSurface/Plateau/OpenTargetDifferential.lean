import DifferentialGeometry.Geometry.Connection.OpenTarget
import DifferentialGeometry.Geometry.Measure.Area.OpenTarget
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential








open Bundle Manifold DifferentialGeometry Set
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem diskMapPartial_open_inclusion (N : TopologicalSpace.Opens M)
    (U : ℂ → N) (z v : ℂ) :
    diskMapPartial (E := E) (Subtype.val ∘ U) z v = diskMapPartial (E := E) U z v := by
  unfold diskMapPartial
  have h := DifferentialGeometry.Topology.mfderiv_subtypeVal_comp
    (I := 𝓘(ℝ, ℂ)) (J := 𝓘(ℝ, E)) N U z
  exact DFunLike.congr_fun h v


theorem diskMapConformalAt_restrictOpen (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (N : TopologicalSpace.Opens M) [T2Space N] (U : ℂ → N) (z : ℂ) :
    DiskMapConformalAt (g.restrictOpen N) U z ↔
      DiskMapConformalAt g (Subtype.val ∘ U) z := by
  unfold DiskMapConformalAt
  simp only [diskMapPartial_open_inclusion, SmoothRiemannianMetric.restrictOpen_inner]
  rfl


theorem diskMapEnergyDensity_restrictOpen (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (N : TopologicalSpace.Opens M) [T2Space N] (U : ℂ → N) (z : ℂ) :
    diskMapEnergyDensity (g.restrictOpen N) U z =
      diskMapEnergyDensity g (Subtype.val ∘ U) z := by
  unfold diskMapEnergyDensity
  simp only [diskMapPartial_open_inclusion, SmoothRiemannianMetric.restrictOpen_inner]
  rfl



theorem diskMapCovariantPartial_restrictOpen (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (N : TopologicalSpace.Opens M) [T2Space N] (U : ℂ → N) (z v w : ℂ)
    (hU : ContinuousAt U z) :
    diskMapCovariantPartial (g.restrictOpen N) U z v w =
      diskMapCovariantPartial g (Subtype.val ∘ U) z v w := by
  have hc : ContinuousAt (fun t : ℝ => U (z + t • v)) 0 := by
    exact hU.comp_of_eq
      (continuousAt_const.add (continuousAt_id.smul continuousAt_const)) (by simp)
  unfold diskMapCovariantPartial
  simp only [diskMapPartial_open_inclusion]
  exact covDerivAlong_restrictOpen g N _ _ 0 hc



theorem diskMapTension_restrictOpen (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (N : TopologicalSpace.Opens M) [T2Space N] (U : ℂ → N) (z : ℂ)
    (hU : ContinuousAt U z) :
    diskMapTension (g.restrictOpen N) U z = diskMapTension g (Subtype.val ∘ U) z := by
  unfold diskMapTension
  rw [diskMapCovariantPartial_restrictOpen g N U z 1 1 hU,
    diskMapCovariantPartial_restrictOpen g N U z Complex.I Complex.I hU]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem diskSmoothUpToBoundary_open_inclusion_iff (N : TopologicalSpace.Opens M)
    (u : C(closedDisk, N)) :
    DiskSmoothUpToBoundary (E := E) ((⟨Subtype.val, continuous_subtype_val⟩ : C(N, M)).comp u) ↔
      DiskSmoothUpToBoundary (E := E) u := by
  change (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
    ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (Subtype.val ∘ diskExtension u)
      (Metric.closedBall 0 1) z) ↔ _
  simp only [contMDiffWithinAt_subtypeVal_comp_iff]
  rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem diskSmoothInterior_open_inclusion_iff (N : TopologicalSpace.Opens M)
    (u : C(closedDisk, N)) :
    DiskSmoothInterior (E := E) ((⟨Subtype.val, continuous_subtype_val⟩ : C(N, M)).comp u) ↔
      DiskSmoothInterior (E := E) u := by
  change (∀ z ∈ Metric.ball (0 : ℂ) 1,
    ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (Subtype.val ∘ diskExtension u)
      (Metric.ball 0 1) z) ↔ _
  simp only [contMDiffWithinAt_subtypeVal_comp_iff]
  rfl

end DifferentialGeometry.Geometry
