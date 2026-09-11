import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CompactHomogeneousRegularity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MetricCompleteness
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SelectedConformalDisk
import DifferentialGeometry.Geometry.Measure.Area.SpanningComponent
import DifferentialGeometry.Topology.LoopSpace.RegularDerivativeBounds









noncomputable section

open Bundle Manifold DifferentialGeometry ContinuousMap
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M]





theorem selectedMorreyDisk_conformal_output_of_compact
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hd : Module.finrank ℝ E = 3)
    (γ : lipschitzContractibleLoop g) (hγ : IsSmoothEmbeddedLoop (E := E) γ.val.val) :
    let hcomplete := riemannianMetricComplete_of_compact g
    let hregular := homogeneouslyRegularMetric_of_compact g hd
    let hfinite := spanningDiskCompetitors_nonempty_of_compact g
      γ.property.choose_spec γ.val.property
    let u := selectedMorreyDisk g hd hcomplete hregular γ.val.val hγ γ.val.property hfinite
    ∃ (v : C(closedDisk, M)) (σ : C(loopCircle, loopCircle)) (U : ℂ → M),
      (v = u ∨ v = u.comp ⟨diskReflection, diskReflection.continuous⟩) ∧
      riemannianDiskArea g v = riemannianDiskArea g u ∧
      IsConformalMinimizingDisk g γ.val.val v σ U ∧
      riemannianDiskArea g v = leastSpanningArea g γ := by
  dsimp only
  obtain ⟨v, σ, U, hid, harea, hconf⟩ := selectedMorreyDisk_conformal_output g hd
    (riemannianMetricComplete_of_compact g) (homogeneouslyRegularMetric_of_compact g hd)
    γ.val.val hγ γ.val.property
    (spanningDiskCompetitors_nonempty_of_compact g γ.property.choose_spec γ.val.property)
  exact ⟨v, σ, U, hid, harea, hconf, hconf.area_eq_leastSpanningArea hγ.smooth⟩





theorem exists_conformalMinimizingDisk_of_compact
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hd : Module.finrank ℝ E = 3)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ) (hnull : γ.Nullhomotopic) :
    ∃ (u : C(closedDisk, M)) (σ : C(loopCircle, loopCircle)) (U : ℂ → M),
      IsConformalMinimizingDisk g γ u σ U := by
  let : Nonempty M := ⟨γ 0⟩
  obtain ⟨L, hL⟩ := regularLoop_riemannian_lipschitz g
    (⟨γ, hγ.smooth.of_le (by simp)⟩ : regularLoop E M)
  obtain ⟨u, σ, U, _, _, hconf⟩ := selectedMorreyDisk_conformal_output g hd
    (riemannianMetricComplete_of_compact g) (homogeneouslyRegularMetric_of_compact g hd)
    γ hγ hnull (spanningDiskCompetitors_nonempty_of_compact g hL hnull)
  exact ⟨u, σ, U, hconf⟩

end DifferentialGeometry.Geometry
