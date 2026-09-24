import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ConformalDiskFromMorrey
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.InteriorConstDiskWitness
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskCriterion
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothDiskAreaDensity

noncomputable section

open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

def interiorSmoothDiskOfDiskSmoothInterior (u : C(Disk, Q))
    (h : Geometry.DiskSmoothInterior (E := E) u) :
    InteriorSmoothDisk (I := 𝓘(ℝ, E)) (Q := Q) where
  map := u
  smooth z hz := ⟨{
    map := Geometry.diskExtension u
    domain := Metric.ball (0 : ℂ) 1
    isOpen_domain := Metric.isOpen_ball
    mem_domain := hz
    smooth := h
    agrees := fun w hw => by
      rw [Geometry.diskExtension_coe u ⟨w, hw.2⟩, diskExtension, dif_pos hw.2] }⟩

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ Q] in
@[simp] theorem interiorSmoothDiskOfDiskSmoothInterior_map (u : C(Disk, Q))
    (h : Geometry.DiskSmoothInterior (E := E) u) :
    (interiorSmoothDiskOfDiskSmoothInterior u h).map = u := rfl

omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ Q] in
theorem interiorSmoothDiskOfDiskSmoothInterior_differential (u : C(Disk, Q))
    (h : Geometry.DiskSmoothInterior (E := E) u) (z : Disk)
    (hz : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1) (v : ℂ) :
    (interiorSmoothDiskOfDiskSmoothInterior u h).differential z v =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (Geometry.diskExtension u) (z : ℂ) v := by
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (z : ℂ) := Metric.isOpen_ball.mem_nhds hz
  have hcb : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 (z : ℂ) :=
    Filter.mem_of_superset hball Metric.ball_subset_closedBall
  have hgerm : diskExtension (⇑u) =ᶠ[𝓝 (z : ℂ)] Geometry.diskExtension u := by
    filter_upwards [hcb] with w hw
    rw [diskExtension, dif_pos hw, Geometry.diskExtension_coe u ⟨w, hw⟩]
  rw [InteriorSmoothDisk.differential]
  have hderiv : mfderivWithin 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension (⇑u))
        (Metric.closedBall (0 : ℂ) 1) (z : ℂ) =
      mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (Geometry.diskExtension u)
        (z : ℂ) := by
    have h1 := mfderivWithin_of_mem_nhds (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, E))
      (f := diskExtension (⇑u)) (s := Metric.closedBall (0 : ℂ) 1) hcb
    exact h1.trans hgerm.mfderiv_eq
  exact congrArg (fun (L : ℂ →L[ℝ] TangentSpace 𝓘(ℝ, E) (u z)) => L v) hderiv

omit [FiniteDimensional ℝ E] in
theorem interiorSmoothDiskOfDiskSmoothInterior_isConformal (u : C(Disk, Q))
    (h : Geometry.DiskSmoothInterior (E := E) u) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (hconf : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Geometry.DiskMapConformalAt g (Geometry.diskExtension u) z) :
    (interiorSmoothDiskOfDiskSmoothInterior u h).IsConformal g := by
  intro z hz
  have hd (v : ℂ) := interiorSmoothDiskOfDiskSmoothInterior_differential u h z hz v
  refine ⟨?_, ?_⟩
  · rw [hd 1, hd Complex.I]
    simp only [interiorSmoothDiskOfDiskSmoothInterior_map]
    rw [← Geometry.diskExtension_coe u z]
    exact (hconf z hz).1
  · rw [hd 1, hd Complex.I]
    simp only [interiorSmoothDiskOfDiskSmoothInterior_map]
    rw [← Geometry.diskExtension_coe u z]
    exact (hconf z hz).2

theorem interiorSmoothDiskOfDiskSmoothInterior_isHarmonic (u : C(Disk, Q))
    (h : Geometry.DiskSmoothInterior (E := E) u) (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    (hharm : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      Geometry.diskMapTension g (Geometry.diskExtension u) z = 0) :
    (interiorSmoothDiskOfDiskSmoothInterior u h).IsHarmonic g := by
  intro z hz F
  have hcb : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 (z : ℂ) :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  have hgerm : F.map =ᶠ[𝓝 (z : ℂ)] Geometry.diskExtension u := by
    filter_upwards [F.isOpen_domain.mem_nhds F.mem_domain, hcb] with w hwd hwb
    rw [F.agrees ⟨hwd, hwb⟩, diskExtension, dif_pos hwb,
      Geometry.diskExtension_coe u ⟨w, hwb⟩]
    rfl
  rw [diskLocalTension_congr_germ g F.map (Geometry.diskExtension u) (z : ℂ) hgerm,
    diskLocalTension_eq_diskMapTension]
  exact hharm z hz

theorem diskArea_le_of_isMorreyDisk_lipschitzDisk (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {γ : RegularLoop 𝓘(ℝ, E) Q} {u : C(Disk, Q)}
    (h : Geometry.IsMorreyDisk g γ.toContinuousLoop u)
    (w : LipschitzDisk (I := 𝓘(ℝ, E)) (Q := Q) g)
    (hw : ∀ theta, w.map (diskBoundary theta) = γ theta) :
    diskArea g (⇑u) ≤ diskArea g (⇑w.map) := by
  have htr : Geometry.DiskWeakJordanTrace γ.toContinuousLoop w.map :=
    Geometry.DiskWeakJordanTrace.of_diskTrace_eq
      ((diskTrace_eq_iff w.map γ.toContinuousLoop).mpr hw)
  have hle := h.minimizesLipschitz w.map htr w.isLipschitz
  rw [diskArea_eq_riemannianDiskArea, diskArea_eq_riemannianDiskArea]
  exact hle

theorem diskArea_le_of_isMorreyDisk_smoothDisk (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q)
    {γ : RegularLoop 𝓘(ℝ, E) Q} {u : C(Disk, Q)}
    (h : Geometry.IsMorreyDisk g γ.toContinuousLoop u)
    (w : SmoothDisk (I := 𝓘(ℝ, E)) (Q := Q))
    (hw : ∀ theta, w.map (diskBoundary theta) = γ theta) :
    diskArea g (⇑u) ≤ diskArea g (⇑w.map) := by
  have hle := h.minimizesSmooth w.map (SmoothDisk.diskSmoothUpToBoundary w)
    ((diskTrace_eq_iff w.map γ.toContinuousLoop).mpr hw)
  rw [diskArea_eq_riemannianDiskArea, diskArea_eq_riemannianDiskArea]
  exact hle

theorem hasConformalMinimizingInteriorDisk_of_isMorreyDisk
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (γ : RegularLoop 𝓘(ℝ, E) Q) (u : C(Disk, Q))
    (h : Geometry.IsMorreyDisk g γ.toContinuousLoop u) :
    HasConformalMinimizingInteriorDisk (I := 𝓘(ℝ, E)) (Q := Q) g γ := by
  refine ⟨interiorSmoothDiskOfDiskSmoothInterior u h.smoothInterior,
    interiorSmoothDiskOfDiskSmoothInterior_isConformal u h.smoothInterior g h.conformal,
    interiorSmoothDiskOfDiskSmoothInterior_isHarmonic u h.smoothInterior g h.harmonic,
    (isSignedWeaklyMonotoneTrace_iff_diskWeakJordanTrace u γ.toContinuousLoop).mpr h.trace,
    ?_, ?_, ?_⟩
  · have hae : (fun z => diskJacobian g (⇑u) z)
        =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) 1)]
        fun z => Geometry.riemannianAreaDensity g (Geometry.diskExtension u) z := by
      filter_upwards [Geometry.ae_disk_interior] with z hz
      simp only [diskJacobian]
      refine (parametricJacobian_eq_riemannianAreaDensity g (diskExtension (⇑u)) z hz).trans ?_
      refine Geometry.riemannianAreaDensity_congr g ?_
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      rw [diskExtension_coe u ⟨w, Metric.ball_subset_closedBall hw⟩,
        Geometry.diskExtension_coe u ⟨w, Metric.ball_subset_closedBall hw⟩]
    exact h.integrableArea.congr_fun_ae hae.symm
  · intro w hw
    exact diskArea_le_of_isMorreyDisk_lipschitzDisk g h w hw
  · intro w hw
    exact diskArea_le_of_isMorreyDisk_smoothDisk g h w hw

theorem hasConformalMinimizingInteriorDisk_of_exists_isMorreyDisk
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (γ : RegularLoop 𝓘(ℝ, E) Q)
    (h : ∃ u : C(Disk, Q), Geometry.IsMorreyDisk g γ.toContinuousLoop u) :
    HasConformalMinimizingInteriorDisk (I := 𝓘(ℝ, E)) (Q := Q) g γ :=
  h.elim fun u hu => hasConformalMinimizingInteriorDisk_of_isMorreyDisk g γ u hu

theorem hasConformalMinimizingInteriorDisk_constLoops
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) Q) (q : Q) :
    HasConformalMinimizingInteriorDisk (I := 𝓘(ℝ, E)) (Q := Q) g
      (regularLoopConst (I := 𝓘(ℝ, E)) (Q := Q) q) := by
  refine hasConformalMinimizingInteriorDisk_of_isMorreyDisk g (regularLoopConst q)
    (ContinuousMap.const Disk q) ?_
  rw [regularLoopConst_toContinuousLoop]
  simp only [constantLoops]
  exact Geometry.isMorreyDisk_const g q

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
