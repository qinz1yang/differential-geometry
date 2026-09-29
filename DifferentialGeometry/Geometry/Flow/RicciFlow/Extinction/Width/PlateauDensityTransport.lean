import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.Comparison
import DifferentialGeometry.Geometry.Metric.DistancePullback

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology ENNReal NNReal
open DifferentialGeometry.Geometry

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {Q' : Type*} [TopologicalSpace Q'] [ChartedSpace H' Q'] [IsManifold I' ∞ Q']
  [T2Space Q'] [T2Space Q]

theorem plateauDiskDensity_of_diffeomorph (g : SmoothRiemannianMetric I Q)
    (Φ : Q ≃ₘ⟮I, I'⟯ Q') (γ : ContinuousFreeLoop Q)
    (h : PlateauDiskDensity (I := I') (Q := Q')
      (Diffeomorph.pullbackMetricCross g Φ.symm)
      ((⟨fun q => Φ q, Φ.continuous⟩ : C(Q, Q')).comp γ)) :
    PlateauDiskDensity (I := I) (Q := Q) g γ := by
  have hf : ∀ x y : Q, riemannianEDistOf (Diffeomorph.pullbackMetricCross g Φ.symm)
      (Φ x) (Φ y) ≤ (1 : ℝ≥0) * riemannianEDistOf g x y := by
    intro x y
    rw [DifferentialGeometry.Geometry.Metric.edistOf_pullbackMetricCross]
    simp only [Diffeomorph.symm_apply_apply, ENNReal.coe_one, one_mul, le_refl]
  intro v
  let v' : DiskCompetitor (Diffeomorph.pullbackMetricCross g Φ.symm)
      ((⟨fun q => Φ q, Φ.continuous⟩ : C(Q, Q')).comp γ) :=
    DiskCompetitor.postcompose g (Diffeomorph.pullbackMetricCross g Φ.symm)
      ⟨fun q => Φ q, Φ.continuous⟩ 1 hf γ v
  obtain ⟨w, hw, ht⟩ := h v'
  have hv'map : ⇑v'.1.map = fun z : Disk => Φ (v.1.map z) := rfl
  have hlim : diskArea (Diffeomorph.pullbackMetricCross g Φ.symm) (⇑v'.1.map) =
      diskArea g (⇑v.1.map) := by
    rw [hv'map, diskArea_pullbackMetricCross g Φ.symm (fun z : Disk => Φ (v.1.map z))]
    congr 1
    funext z
    exact Φ.symm_apply_apply (v.1.map z)
  refine ⟨fun j => (w j).compDiffeomorph Φ.symm, ?_, ?_⟩
  · intro j θ
    rw [SmoothDisk.comp_diffeomorph_map, hw j θ]
    simp
  · have hfun : (fun j => diskArea g (⇑((w j).compDiffeomorph Φ.symm).map)) =
        fun j => diskArea (Diffeomorph.pullbackMetricCross g Φ.symm) (⇑(w j).map) := by
      funext j
      exact (diskArea_pullbackMetricCross g Φ.symm (⇑(w j).map)).symm
    rw [hfun, ← hlim]
    exact ht

theorem plateauDiskDensity_of_standardModelCopy
    (c : Geometry.Topology.StandardModelCopy I Q E) (g : SmoothRiemannianMetric I Q)
    (γ : ContinuousFreeLoop Q)
    (h : PlateauDiskDensity (I := 𝓘(ℝ, E)) (Q := c.Q)
      (Diffeomorph.pullbackMetricCross g c.equiv.symm)
      ((⟨fun q => c.equiv q, c.equiv.continuous⟩ : C(Q, c.Q)).comp γ)) :
    PlateauDiskDensity (I := I) (Q := Q) g γ :=
  plateauDiskDensity_of_diffeomorph g c.equiv γ h

theorem smooth_exact_disk_density_of_standardModelCopy
    (c : Geometry.Topology.StandardModelCopy I Q E)
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (h : PlateauDiskDensity (I := 𝓘(ℝ, E)) (Q := c.Q)
      (Diffeomorph.pullbackMetricCross g c.equiv.symm)
      ((⟨fun q => c.equiv q, c.equiv.continuous⟩ : C(Q, c.Q)).comp γ.toContinuousLoop))
    (v : DiskCompetitor g γ.toContinuousLoop) :
    ∃ w : ℕ → SmoothDisk (I := I) (Q := Q),
      (∀ j θ, (w j).map (diskBoundary θ) = γ θ) ∧
      Filter.Tendsto (fun j => diskArea g (w j).map) Filter.atTop (𝓝 (diskArea g v.1.map)) :=
  plateauDiskDensity_of_standardModelCopy c g γ.toContinuousLoop h v

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
