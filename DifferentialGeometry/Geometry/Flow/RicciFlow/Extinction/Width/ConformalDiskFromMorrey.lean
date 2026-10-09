import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauClassical

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

def HasConformalMinimizingInteriorDisk (g : SmoothRiemannianMetric I Q)
    (γ : RegularLoop I Q) : Prop :=
  ∃ u : InteriorSmoothDisk (I := I) (Q := Q),
    u.IsConformal g ∧ u.IsHarmonic g ∧
      IsSignedWeaklyMonotoneTrace u.map γ.toContinuousLoop ∧
      IntegrableOn (diskJacobian g u.map) (Metric.closedBall (0 : ℂ) 1) ∧
      (∀ w : LipschitzDisk g,
        (∀ theta, w.map (diskBoundary theta) = γ theta) →
          diskArea g u.map ≤ diskArea g w.map) ∧
      ∀ w : SmoothDisk (I := I) (Q := Q),
        (∀ theta, w.map (diskBoundary theta) = γ theta) →
          diskArea g u.map ≤ diskArea g w.map

theorem conformal_disk_producer_of_hasConformalMinimizingInteriorDisk
    [I.Boundaryless] [T2Space Q] [CompactSpace Q]
    (g : SmoothRiemannianMetric I Q) (hdim : Module.finrank ℝ E = 3) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → Q))
    (himm : ∀ t : ℝ, loopVelocity (I := I) γ.toContinuousLoop t ≠ 0)
    (h : HasConformalMinimizingInteriorDisk (I := I) (Q := Q) g γ) :
    ∃ u : SmoothDisk (I := I) (Q := Q), ∃ σ : SmoothWeaklyMonotoneCircleMap,
      (∀ θ, u.map (diskBoundary θ) = γ (σ.map θ)) ∧ u.IsConformal g ∧ u.IsHarmonic g ∧
      ∀ v : SmoothDisk (I := I) (Q := Q),
        (∀ θ, v.map (diskBoundary θ) = γ θ) →
          diskArea g u.map ≤ diskArea g v.map := by
  obtain ⟨u, hconf, hharm, htrace, hfinite, _, hmin⟩ := h
  obtain ⟨w, hwmap, hwconf, hwharm⟩ :=
    classical_plateau_boundary_regularity g hdim γ hγ hemb himm u hconf hharm htrace hfinite hmin
  have htracew : IsSignedWeaklyMonotoneTrace w.map γ.toContinuousLoop := by
    rw [hwmap]
    exact htrace
  obtain ⟨v, σ, _, hvtr, hvare, hvconf, hvharm⟩ :=
    smooth_monotone_trace g γ hγ hemb himm w htracew
  refine ⟨v, σ, hvtr, hvconf.mpr hwconf, hvharm.mpr hwharm, fun v' hv' => ?_⟩
  rw [hvare]
  simpa only [hwmap] using hmin v' hv'

theorem isSignedWeaklyMonotoneTrace_of_weaklyMonotoneCircleMap {u : Disk → Q}
    {γ : Surgery.Topology.ContinuousFreeLoop Q} (σ : SmoothWeaklyMonotoneCircleMap)
    (htrace : ∀ θ, u (diskBoundary θ) = γ (σ.map θ)) :
    IsSignedWeaklyMonotoneTrace u γ :=
  ⟨σ.lift, σ.smooth_lift.continuous, Or.inl ⟨σ.monotone_lift, σ.increment⟩,
    fun t => by simpa only [σ.lift_eq t] using htrace (t : Surgery.Topology.Circle)⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
