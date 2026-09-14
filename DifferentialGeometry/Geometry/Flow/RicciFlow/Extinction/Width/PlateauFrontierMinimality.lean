import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ConformalDiskFromMorrey
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.InteriorConstDiskWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonDensity

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

def HasConformalMinimizingSmoothInteriorDisk
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q) : Prop :=
  ∃ u : InteriorSmoothDisk (I := I) (Q := Q),
    u.IsConformal g ∧ u.IsHarmonic g ∧
      IsSignedWeaklyMonotoneTrace u.map γ.toContinuousLoop ∧
      IntegrableOn (diskJacobian g u.map) (Metric.closedBall (0 : ℂ) 1) ∧
      ∀ v : SmoothDisk (I := I) (Q := Q),
        (∀ theta, v.map (diskBoundary theta) = γ theta) →
          diskArea g u.map ≤ diskArea g v.map

def HasMinimizingConformalInteriorDisk
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q) : Prop :=
  ∃ u : InteriorSmoothDisk (I := I) (Q := Q),
    u.IsConformal g ∧ u.IsHarmonic g ∧
      IsSignedWeaklyMonotoneTrace u.map γ.toContinuousLoop ∧
      IntegrableOn (diskJacobian g u.map) (Metric.closedBall (0 : ℂ) 1) ∧
      ∀ v : DiskCompetitor g γ.toContinuousLoop,
        diskArea g u.map ≤ diskArea g v.1.map

variable [boundarylessI : I.Boundaryless] [t2Q : T2Space Q] [compactQ : CompactSpace Q]

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ in
theorem diskCompetitor_minimization_of_lipschitzDisk_minimization
    (g : SmoothRiemannianMetric I Q) {u : InteriorSmoothDisk (I := I) (Q := Q)}
    {γ : RegularLoop I Q}
    (h : ∀ w : LipschitzDisk g, (∀ theta, w.map (diskBoundary theta) = γ theta) →
      diskArea g u.map ≤ diskArea g w.map) :
    ∀ v : DiskCompetitor g γ.toContinuousLoop,
      diskArea g u.map ≤ diskArea g v.1.map :=
  fun v => h v.1 v.2

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ in
theorem lipschitzDisk_minimization_of_diskCompetitor_minimization
    (g : SmoothRiemannianMetric I Q) {u : InteriorSmoothDisk (I := I) (Q := Q)}
    {γ : RegularLoop I Q}
    (h : ∀ v : DiskCompetitor g γ.toContinuousLoop,
      diskArea g u.map ≤ diskArea g v.1.map) :
    ∀ w : LipschitzDisk g, (∀ theta, w.map (diskBoundary theta) = γ theta) →
      diskArea g u.map ≤ diskArea g w.map :=
  fun w hw => h ⟨w, hw⟩

omit [FiniteDimensional ℝ E] boundarylessI t2Q compactQ in
theorem smoothDisk_minimization_vacuous_of_no_smoothDisk_trace
    (g : SmoothRiemannianMetric I Q) {u : InteriorSmoothDisk (I := I) (Q := Q)}
    {γ : RegularLoop I Q}
    (h : ∀ w : SmoothDisk (I := I) (Q := Q),
      ¬ (∀ theta, w.map (diskBoundary theta) = γ theta)) :
    ∀ w : SmoothDisk (I := I) (Q := Q),
      (∀ theta, w.map (diskBoundary theta) = γ theta) →
        diskArea g u.map ≤ diskArea g w.map :=
  fun w hw => absurd hw (h w)

theorem smoothDisk_minimization_of_lipschitzDisk_minimization
    (g : SmoothRiemannianMetric I Q) {u : InteriorSmoothDisk (I := I) (Q := Q)}
    {γ : RegularLoop I Q}
    (h : ∀ w : LipschitzDisk g, (∀ theta, w.map (diskBoundary theta) = γ theta) →
      diskArea g u.map ≤ diskArea g w.map) :
    ∀ w : SmoothDisk (I := I) (Q := Q),
      (∀ theta, w.map (diskBoundary theta) = γ theta) →
        diskArea g u.map ≤ diskArea g w.map := by
  intro w hw
  obtain ⟨v, hv⟩ := w.exists_lipschitz g
  have hle := h v (by rw [hv]; exact hw)
  rwa [hv] at hle

theorem hasConformalMinimizingSmoothInteriorDisk_of_minimizingConformalInteriorDisk
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (h : HasMinimizingConformalInteriorDisk (I := I) (Q := Q) g γ) :
    HasConformalMinimizingSmoothInteriorDisk (I := I) (Q := Q) g γ := by
  obtain ⟨u, hconf, hharm, htrace, hfinite, hmin⟩ := h
  exact ⟨u, hconf, hharm, htrace, hfinite,
    smoothDisk_minimization_of_lipschitzDisk_minimization g
      (lipschitzDisk_minimization_of_diskCompetitor_minimization g hmin)⟩

omit boundarylessI t2Q compactQ in
theorem hasMinimizingConformalInteriorDisk_of_hasConformalMinimizingInteriorDisk
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (h : HasConformalMinimizingInteriorDisk (I := I) (Q := Q) g γ) :
    HasMinimizingConformalInteriorDisk (I := I) (Q := Q) g γ := by
  obtain ⟨u, hconf, hharm, htrace, hfinite, hmin, _⟩ := h
  exact ⟨u, hconf, hharm, htrace, hfinite,
    diskCompetitor_minimization_of_lipschitzDisk_minimization g hmin⟩

omit boundarylessI t2Q compactQ in
theorem minimizingConformalInteriorDisk_of_hasConformalMinimizingSmoothInteriorDisk
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (hdensity : PlateauDiskDensity (I := I) (Q := Q) g γ.toContinuousLoop)
    (h : HasConformalMinimizingSmoothInteriorDisk (I := I) (Q := Q) g γ) :
    HasMinimizingConformalInteriorDisk (I := I) (Q := Q) g γ := by
  obtain ⟨u, hconf, hharm, htrace, hfinite, hminS⟩ := h
  refine ⟨u, hconf, hharm, htrace, hfinite, fun v => ?_⟩
  obtain ⟨wj, htrj, hlim⟩ := hdensity v
  exact ge_of_tendsto' hlim fun j => hminS (wj j) (htrj j)

theorem hasMinimizingConformalInteriorDisk_of_smoothInteriorDisk_of_density
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (hdensity : PlateauDiskDensity (I := I) (Q := Q) g γ.toContinuousLoop)
    (h : HasConformalMinimizingSmoothInteriorDisk (I := I) (Q := Q) g γ) :
    HasConformalMinimizingInteriorDisk (I := I) (Q := Q) g γ := by
  obtain ⟨u, hconf, hharm, htrace, hfinite, hmin⟩ :=
    minimizingConformalInteriorDisk_of_hasConformalMinimizingSmoothInteriorDisk
      g γ hdensity h
  exact ⟨u, hconf, hharm, htrace, hfinite,
    lipschitzDisk_minimization_of_diskCompetitor_minimization g hmin,
    smoothDisk_minimization_of_lipschitzDisk_minimization g
      (lipschitzDisk_minimization_of_diskCompetitor_minimization g hmin)⟩

theorem hasConformalMinimizingInteriorDisk_iff_smoothCompetitors_of_density
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (hdensity : PlateauDiskDensity (I := I) (Q := Q) g γ.toContinuousLoop) :
    HasConformalMinimizingInteriorDisk (I := I) (Q := Q) g γ ↔
      HasConformalMinimizingSmoothInteriorDisk (I := I) (Q := Q) g γ :=
   ⟨fun h => hasConformalMinimizingSmoothInteriorDisk_of_minimizingConformalInteriorDisk g γ
      (hasMinimizingConformalInteriorDisk_of_hasConformalMinimizingInteriorDisk g γ h),
    hasMinimizingConformalInteriorDisk_of_smoothInteriorDisk_of_density g γ hdensity⟩

theorem hasConformalMinimizingInteriorDisk_of_minimizingConformalInteriorDisk
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (h : HasMinimizingConformalInteriorDisk (I := I) (Q := Q) g γ) :
    HasConformalMinimizingInteriorDisk (I := I) (Q := Q) g γ := by
  obtain ⟨u, hconf, hharm, htrace, hfinite, hmin⟩ := h
  exact ⟨u, hconf, hharm, htrace, hfinite,
    lipschitzDisk_minimization_of_diskCompetitor_minimization g hmin,
    smoothDisk_minimization_of_lipschitzDisk_minimization g
      (lipschitzDisk_minimization_of_diskCompetitor_minimization g hmin)⟩

theorem hasConformalMinimizingInteriorDisk_iff_minimizingConformalInteriorDisk
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q) :
    HasConformalMinimizingInteriorDisk (I := I) (Q := Q) g γ ↔
      HasMinimizingConformalInteriorDisk (I := I) (Q := Q) g γ :=
  ⟨hasMinimizingConformalInteriorDisk_of_hasConformalMinimizingInteriorDisk g γ,
    hasConformalMinimizingInteriorDisk_of_minimizingConformalInteriorDisk g γ⟩

theorem conformal_disk_producer_of_minimizingConformalInteriorDisk
    (g : SmoothRiemannianMetric I Q) (hdim : Module.finrank ℝ E = 3) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → Q))
    (himm : ∀ t : ℝ, loopVelocity (I := I) γ.toContinuousLoop t ≠ 0)
    (h : HasMinimizingConformalInteriorDisk (I := I) (Q := Q) g γ) :
    ∃ u : SmoothDisk (I := I) (Q := Q), ∃ σ : SmoothWeaklyMonotoneCircleMap,
      (∀ θ, u.map (diskBoundary θ) = γ (σ.map θ)) ∧ u.IsConformal g ∧ u.IsHarmonic g ∧
      ∀ v : SmoothDisk (I := I) (Q := Q),
        (∀ θ, v.map (diskBoundary θ) = γ θ) →
          diskArea g u.map ≤ diskArea g v.map :=
  conformal_disk_producer_of_hasConformalMinimizingInteriorDisk g hdim γ hγ hemb himm
    (hasConformalMinimizingInteriorDisk_of_minimizingConformalInteriorDisk g γ h)

theorem conformal_disk_producer_of_smoothInteriorDisk_and_density
    (g : SmoothRiemannianMetric I Q) (hdim : Module.finrank ℝ E = 3) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → Q))
    (himm : ∀ t : ℝ, loopVelocity (I := I) γ.toContinuousLoop t ≠ 0)
    (hdensity : PlateauDiskDensity (I := I) (Q := Q) g γ.toContinuousLoop)
    (h : HasConformalMinimizingSmoothInteriorDisk (I := I) (Q := Q) g γ) :
    ∃ u : SmoothDisk (I := I) (Q := Q), ∃ σ : SmoothWeaklyMonotoneCircleMap,
      (∀ θ, u.map (diskBoundary θ) = γ (σ.map θ)) ∧ u.IsConformal g ∧ u.IsHarmonic g ∧
      ∀ v : SmoothDisk (I := I) (Q := Q),
        (∀ θ, v.map (diskBoundary θ) = γ θ) →
          diskArea g u.map ≤ diskArea g v.map :=
  conformal_disk_producer_of_minimizingConformalInteriorDisk g hdim γ hγ hemb himm
    (minimizingConformalInteriorDisk_of_hasConformalMinimizingSmoothInteriorDisk
      g γ hdensity h)

theorem hasMinimizingConformalInteriorDisk_constLoops_of_analytic
    (g : SmoothRiemannianMetric I Q) (q : Q)
    (hharm : (interiorSmoothDiskConst (I := I) (Q := Q) q).IsHarmonic g)
    (hfinite : IntegrableOn (diskJacobian g (fun _ : Disk => q)) (Metric.closedBall (0 : ℂ) 1)) :
    HasMinimizingConformalInteriorDisk (I := I) (Q := Q) g
      (regularLoopConst (I := I) (Q := Q) q) :=
  hasMinimizingConformalInteriorDisk_of_hasConformalMinimizingInteriorDisk
    g (regularLoopConst (I := I) (Q := Q) q)
    (hasConformalMinimizingInteriorDisk_constLoops_of_analytic g q hharm hfinite)

theorem hasConformalMinimizingSmoothInteriorDisk_constLoops_of_analytic
    (g : SmoothRiemannianMetric I Q) (q : Q)
    (hharm : (interiorSmoothDiskConst (I := I) (Q := Q) q).IsHarmonic g)
    (hfinite : IntegrableOn (diskJacobian g (fun _ : Disk => q)) (Metric.closedBall (0 : ℂ) 1)) :
    HasConformalMinimizingSmoothInteriorDisk (I := I) (Q := Q) g
      (regularLoopConst (I := I) (Q := Q) q) :=
  hasConformalMinimizingSmoothInteriorDisk_of_minimizingConformalInteriorDisk
    g (regularLoopConst (I := I) (Q := Q) q)
    (hasMinimizingConformalInteriorDisk_constLoops_of_analytic g q hharm hfinite)

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
