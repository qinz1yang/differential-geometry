import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauFrontierAudit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauFrontierMinimality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauMorreyFrontier

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem hasConformalMinimizingSmoothInteriorDisk_of_conformal_harmonic_minimizing_disk
    [boundarylessI : I.Boundaryless] [t2Q : T2Space Q] [compactQ : CompactSpace Q]
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (h : ∃ u : SmoothDisk (I := I) (Q := Q), ∃ σ : SmoothWeaklyMonotoneCircleMap,
      (∀ θ, u.map (diskBoundary θ) = γ.toContinuousLoop (σ.map θ)) ∧ u.IsConformal g ∧
        u.IsHarmonic g ∧
        ∀ v : SmoothDisk (I := I) (Q := Q),
          (∀ θ, v.map (diskBoundary θ) = γ.toContinuousLoop θ) →
            diskArea g u.map ≤ diskArea g v.map) :
    HasConformalMinimizingSmoothInteriorDisk (I := I) (Q := Q) g γ := by
  obtain ⟨u, σ, htrace, hconf, hharm, hmin⟩ := h
  obtain ⟨v, hv⟩ := u.exists_lipschitz g
  refine ⟨⟨u.map, fun z _ => u.smooth z⟩, fun z _ => hconf z, fun z _ F => hharm z F,
    isSignedWeaklyMonotoneTrace_of_weaklyMonotoneCircleMap σ htrace, ?_, hmin⟩
  simpa only [hv] using v.integrable_jacobian g

theorem conformal_disk_producer_of_hasConformalMinimizingSmoothInteriorDisk
    [boundarylessI : I.Boundaryless] [t2Q : T2Space Q] [compactQ : CompactSpace Q]
    (g : SmoothRiemannianMetric I Q) (hdim : Module.finrank ℝ E = 3) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → Q))
    (himm : ∀ t : ℝ, loopVelocity (I := I) γ.toContinuousLoop t ≠ 0)
    (h : HasConformalMinimizingSmoothInteriorDisk (I := I) (Q := Q) g γ) :
    ∃ u : SmoothDisk (I := I) (Q := Q), ∃ σ : SmoothWeaklyMonotoneCircleMap,
      (∀ θ, u.map (diskBoundary θ) = γ.toContinuousLoop (σ.map θ)) ∧ u.IsConformal g ∧
        u.IsHarmonic g ∧
        ∀ v : SmoothDisk (I := I) (Q := Q),
          (∀ θ, v.map (diskBoundary θ) = γ.toContinuousLoop θ) →
            diskArea g u.map ≤ diskArea g v.map := by
  obtain ⟨u, hconf, hharm, htrace, hfinite, hmin⟩ := h
  obtain ⟨w, hwmap, hwconf, hwharm⟩ :=
    classical_plateau_boundary_regularity g hdim γ hγ hemb himm u hconf hharm htrace hfinite hmin
  have htracew : IsSignedWeaklyMonotoneTrace w.map γ.toContinuousLoop := by
    rw [hwmap]
    exact htrace
  obtain ⟨v, σ, _, hvtr, hvare, hvconf, hvharm⟩ :=
    smooth_monotone_trace g γ hγ hemb himm w htracew
  refine ⟨v, σ, hvtr, hvconf.mpr hwconf, hvharm.mpr hwharm, fun v' hv' => ?_⟩
  rw [hvare, hwmap]
  exact hmin v' hv'

theorem exists_conformal_harmonic_minimizing_disk_iff_hasConformalMinimizingSmoothInteriorDisk
    [boundarylessI : I.Boundaryless] [t2Q : T2Space Q] [compactQ : CompactSpace Q]
    (g : SmoothRiemannianMetric I Q) (hdim : Module.finrank ℝ E = 3) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → Q))
    (himm : ∀ t : ℝ, loopVelocity (I := I) γ.toContinuousLoop t ≠ 0) :
    (∃ u : SmoothDisk (I := I) (Q := Q), ∃ σ : SmoothWeaklyMonotoneCircleMap,
      (∀ θ, u.map (diskBoundary θ) = γ.toContinuousLoop (σ.map θ)) ∧ u.IsConformal g ∧
        u.IsHarmonic g ∧
        ∀ v : SmoothDisk (I := I) (Q := Q),
          (∀ θ, v.map (diskBoundary θ) = γ.toContinuousLoop θ) →
            diskArea g u.map ≤ diskArea g v.map) ↔
      HasConformalMinimizingSmoothInteriorDisk (I := I) (Q := Q) g γ :=
  ⟨hasConformalMinimizingSmoothInteriorDisk_of_conformal_harmonic_minimizing_disk g γ,
    conformal_disk_producer_of_hasConformalMinimizingSmoothInteriorDisk g hdim γ hγ hemb himm⟩

theorem hasConformalMinimizingSmoothInteriorDisk_of_nonempty_plateauSpanningFrontier
    [boundarylessI : I.Boundaryless] [t2Q : T2Space Q] [compactQ : CompactSpace Q]
    (g : SmoothRiemannianMetric I Q) (γ : RegularLoop I Q)
    (h : Nonempty (PlateauSpanningFrontier (I := I) (Q := Q) g γ.toContinuousLoop)) :
    HasConformalMinimizingSmoothInteriorDisk (I := I) (Q := Q) g γ := by
  obtain ⟨F⟩ := h
  obtain ⟨v, hv⟩ := F.disk.exists_lipschitz g
  refine ⟨⟨F.disk.map, fun z _ => F.disk.smooth z⟩, fun z _ => F.conformal z,
    fun z _ G => F.harmonic z G,
    isSignedWeaklyMonotoneTrace_of_weaklyMonotoneCircleMap F.sigma F.trace, ?_, ?_⟩
  · simpa only [hv] using v.integrable_jacobian g
  · intro w hw
    obtain ⟨wv, hwv⟩ := w.exists_lipschitz g
    have hle := F.minimizing ⟨wv, fun θ => by rw [hwv]; exact hw θ⟩
    rwa [hwv] at hle

theorem nonempty_plateauSpanningFrontier_of_smoothInteriorDisk_and_plateauDiskDensity
    [boundarylessI : I.Boundaryless] [t2Q : T2Space Q] [compactQ : CompactSpace Q]
    (g : SmoothRiemannianMetric I Q) (hdim : Module.finrank ℝ E = 3) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → Q))
    (himm : ∀ t : ℝ, loopVelocity (I := I) γ.toContinuousLoop t ≠ 0)
    (hdensity : PlateauDiskDensity (I := I) (Q := Q) g γ.toContinuousLoop)
    (h : HasConformalMinimizingSmoothInteriorDisk (I := I) (Q := Q) g γ) :
    Nonempty (PlateauSpanningFrontier (I := I) (Q := Q) g γ.toContinuousLoop) := by
  obtain ⟨u, hconf, hharm, htrace, hfinite, hmin⟩ := h
  obtain ⟨w, hwmap, hwconf, hwharm⟩ :=
    classical_plateau_boundary_regularity g hdim γ hγ hemb himm u hconf hharm htrace hfinite hmin
  have htracew : IsSignedWeaklyMonotoneTrace w.map γ.toContinuousLoop := by
    rw [hwmap]
    exact htrace
  obtain ⟨v, σ, _, hvtr, hvare, hvconf, hvharm⟩ :=
    smooth_monotone_trace g γ hγ hemb himm w htracew
  refine ⟨{ disk := v
            sigma := σ
            trace := hvtr
            conformal := hvconf.mpr hwconf
            harmonic := hvharm.mpr hwharm
            minimizing := fun c => ?_ }⟩
  obtain ⟨W, hWtr, hlim⟩ := hdensity c
  have hbound (j : ℕ) : diskArea g v.map ≤ diskArea g (W j).map := by
    rw [hvare, hwmap]
    exact hmin (W j) (hWtr j)
  exact ge_of_tendsto' hlim hbound

section StandardModel

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type*} [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]

theorem hasConformalMinimizingSmoothInteriorDisk_constLoops
    [T2Space M] [CompactSpace M] (g : SmoothRiemannianMetric 𝓘(ℝ, F) M) (q : M) :
    HasConformalMinimizingSmoothInteriorDisk (I := 𝓘(ℝ, F)) (Q := M) g
      (regularLoopConst (I := 𝓘(ℝ, F)) (Q := M) q) :=
  hasConformalMinimizingSmoothInteriorDisk_of_nonempty_plateauSpanningFrontier (I := 𝓘(ℝ, F))
    (Q := M) g (regularLoopConst (I := 𝓘(ℝ, F)) (Q := M) q)
    (plateauSpanningFrontier_constLoops g q)

end StandardModel

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
