import DifferentialGeometry.Geometry.MinimalSurface.Plateau.CompactConformalDisk
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiffeomorphismTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauBridge

noncomputable section

open Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem conformal_disk_producer_standard_model
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hdim : Module.finrank ℝ E = 3) (γ : RegularLoop 𝓘(ℝ, E) M)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → M))
    (himm : ∀ t : ℝ, loopVelocity (I := 𝓘(ℝ, E)) γ.toContinuousLoop t ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop γ.toContinuousLoop) :
    ∃ u : SmoothDisk (I := 𝓘(ℝ, E)) (Q := M), ∃ σ : SmoothWeaklyMonotoneCircleMap,
      (∀ θ, u.map (diskBoundary θ) = γ (σ.map θ)) ∧
      u.IsConformal g ∧ u.IsHarmonic g ∧
      ∀ v : SmoothDisk (I := 𝓘(ℝ, E)) (Q := M),
        (∀ θ, v.map (diskBoundary θ) = γ θ) → diskArea g u.map ≤ diskArea g v.map := by
  obtain ⟨q, τ, Q, hq⟩ := Geometry.exists_conformalMinimizingDisk_of_compact g hdim
    γ.toContinuousLoop (isSmoothEmbeddedLoop_of_regularLoop γ hγ hemb himm) hctr
  let u := smoothDiskOfSmoothDiskExtension hq.extension
  obtain ⟨ψ, hψ, hmono, hinc, hlift⟩ := hq.positiveTrace
  let σ : SmoothWeaklyMonotoneCircleMap :=
    { map := τ
      lift := ψ
      smooth_lift := hψ
      monotone_lift := hmono
      increment := hinc
      lift_eq := fun t => (hlift t).symm }
  refine ⟨u, σ, ?_, ?_, ?_, ?_⟩
  · exact (diskTrace_eq_iff q (γ.toContinuousLoop.comp τ)).mp hq.trace
  · exact (u.isConformal_iff_diskMapConformalAt g hq.extension).mpr hq.conformal
  · exact u.isHarmonic_of_diskMapTension_eq_zero_on_ball g hq.extension
      (fun z hz => hq.harmonic z (Metric.ball_subset_closedBall hz))
  · intro v hv
    rw [diskArea_eq_riemannianDiskArea, diskArea_eq_riemannianDiskArea]
    exact hq.minimizesSmooth v.map v.diskSmoothUpToBoundary
      ((diskTrace_eq_iff v.map γ.toContinuousLoop).mpr hv)

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [FiniteDimensional ℝ E] [boundarylessI : I.Boundaryless] [t2Q : T2Space Q]
  [compactQ : CompactSpace Q]

theorem conformal_disk_producer (g : SmoothRiemannianMetric I Q)
    (hdim : Module.finrank ℝ E = 3) (γ : RegularLoop I Q)
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (loopLift γ.toContinuousLoop))
    (hemb : Topology.IsEmbedding (γ : Surgery.Topology.Circle → Q))
    (himm : ∀ t : ℝ, loopVelocity (I := I) γ.toContinuousLoop t ≠ 0)
    (hctr : Surgery.Topology.IsContractibleLoop γ.toContinuousLoop) :
    ∃ u : SmoothDisk (I := I) (Q := Q), ∃ σ : SmoothWeaklyMonotoneCircleMap,
      (∀ θ, u.map (diskBoundary θ) = γ (σ.map θ)) ∧
      u.IsConformal g ∧ u.IsHarmonic g ∧
      ∀ v : SmoothDisk (I := I) (Q := Q),
        (∀ θ, v.map (diskBoundary θ) = γ θ) → diskArea g u.map ≤ diskArea g v.map := by
  let c : Geometry.Topology.StandardModelCopy I Q E :=
    Geometry.Topology.standardModelCopy (I := I) (M := Q)
      (e := ContinuousLinearEquiv.refl ℝ E)
  let Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ c.Q := c.equiv
  let : CompactSpace c.Q := c.equiv.toHomeomorph.compactSpace
  let g' := Diffeomorph.pullbackMetricCross g Φ.symm
  let γ' := γ.postcomposeDiffeomorph Φ
  have hγ' : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (loopLift γ'.toContinuousLoop) :=
    Φ.contMDiff.comp hγ
  have hemb' : Topology.IsEmbedding (γ' : Surgery.Topology.Circle → c.Q) :=
    Φ.toHomeomorph.isEmbedding.comp hemb
  have himm' (t : ℝ) : loopVelocity (I := 𝓘(ℝ, E)) γ'.toContinuousLoop t ≠ 0 := by
    rw [loopVelocity_postcomposeDiffeomorph Φ γ hγ]
    exact fun h => himm t ((mfderiv_eq_zero_iff_of_diffeomorph Φ _).mp h)
  have hctr' : Surgery.Topology.IsContractibleLoop γ'.toContinuousLoop :=
    hctr.postcompose ⟨Φ, Φ.continuous⟩
  obtain ⟨u, σ, htrace, hconf, hharm, hmin⟩ :=
    conformal_disk_producer_standard_model g' hdim γ' hγ' hemb' himm' hctr'
  let v := SmoothDisk.compDiffeomorph Φ.symm u
  refine ⟨v, σ, ?_, u.isConformal_comp_diffeomorph_symm Φ g hconf,
    u.isHarmonic_comp_diffeomorph_symm Φ g hharm, ?_⟩
  · intro θ
    change Φ.symm (u.map (diskBoundary θ)) = γ (σ.map θ)
    rw [htrace]
    exact Φ.symm_apply_apply _
  · intro w hw
    have htracew (θ) : (SmoothDisk.compDiffeomorph Φ w).map (diskBoundary θ) = γ' θ :=
      congrArg Φ (hw θ)
    calc
      diskArea g v.map = diskArea g' u.map :=
        (diskArea_pullbackMetricCross g Φ.symm u.map).symm
      _ ≤ diskArea g' (SmoothDisk.compDiffeomorph Φ w).map := hmin _ htracew
      _ = diskArea g w.map := by
        rw [diskArea_pullbackMetricCross]
        congr 1

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
