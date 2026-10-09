import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Existence.Compact
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Regularity.BoundarySmoothness
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ComponentDisk
import DifferentialGeometry.Geometry.Metric.LoopLipschitz
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
    let u := selectedMorreyDisk g hcomplete hregular γ.val.val hγ hfinite
    ∃ (v : C(closedDisk, M)) (σ : C(loopCircle, loopCircle)) (U : ℂ → M),
      (v = u ∨ v = u.comp ⟨diskReflection, diskReflection.continuous⟩) ∧
      riemannianDiskArea g v = riemannianDiskArea g u ∧
      IsConformalMinimizingDisk g γ.val.val v σ U ∧
      riemannianDiskArea g v = leastSpanningArea g γ := by
  dsimp only
  obtain ⟨v, σ, U, hid, harea, hconf⟩ := selectedMorreyDisk_conformal_output g hd
    (riemannianMetricComplete_of_compact g) (homogeneouslyRegularMetric_of_compact g hd)
    γ.val.val hγ
    (spanningDiskCompetitors_nonempty_of_compact g γ.property.choose_spec γ.val.property)
  exact ⟨v, σ, U, hid, harea, hconf, hconf.area_eq_leastSpanningArea hγ.smooth⟩





theorem exists_conformalMinimizingDisk_of_compact
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hd : Module.finrank ℝ E = 3)
    (γ : freeLoop M) (hγ : IsSmoothEmbeddedLoop (E := E) γ) (hnull : γ.Nullhomotopic) :
    ∃ (u : C(closedDisk, M)) (σ : C(loopCircle, loopCircle)) (U : ℂ → M),
      IsConformalMinimizingDisk g γ u σ U := by
  let N := loopComponentOpen E γ
  let γN : freeLoop N := loopInComponent γ
  have hγN : IsSmoothEmbeddedLoop (E := E) γN :=
    (isSmoothEmbeddedLoop_open_inclusion_iff N γN).mp hγ
  obtain ⟨L, hL⟩ := exists_riemannian_lipschitz_freeLoop_of_contMDiff
    (g.restrictOpen N) (hγN.smooth.of_le (by simp))
  have hfinite : (weaklyMonotoneDiskCompetitors (g.restrictOpen N) γN).Nonempty :=
    (spanningDiskCompetitors_nonempty (g.restrictOpen N) hL
      (loopInComponent_nullhomotopic γ hnull)).mono
        (spanningDiskCompetitors_subset_weaklyMonotoneDiskCompetitors _ _)
  obtain ⟨q, hq⟩ := exists_morrey_disk_of_compact (g.restrictOpen N) γN hγN hfinite
  obtain ⟨τ, _, htrace⟩ := hq.trace
  obtain ⟨Q, hQ⟩ := exists_smooth_extension_of_conformal_harmonic_disk
    (g.restrictOpen N) hγN q hq.smoothInterior hq.conformal hq.harmonic τ htrace
  obtain ⟨u, σ, U, _, _, hu⟩ := hq.exists_conformal_minimizing_disk
    (g.restrictOpen N) hd hγN ⟨Q, hQ⟩
  exact ⟨_, σ, _, hu.component_inclusion g γ⟩


end DifferentialGeometry.Geometry
