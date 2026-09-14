import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauUpperComparisonAttainment
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.ConformalDiskFromMorrey

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

omit [FiniteDimensional ℝ E] in
def interiorSmoothDiskConst (q : Q) : InteriorSmoothDisk (I := I) (Q := Q) where
  map := ⟨fun _ => q, continuous_const⟩
  smooth z _ := ⟨{
    map := fun _ => q
    domain := Set.univ
    isOpen_domain := isOpen_univ
    mem_domain := Set.mem_univ z
    smooth := contMDiffOn_const
    agrees := fun w _ => by simp [diskExtension] }⟩

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem interiorSmoothDiskConst_diskExtension (q : Q) :
    diskExtension (⇑(interiorSmoothDiskConst (I := I) (Q := Q) q).map) = fun _ : ℂ => q := by
  funext w
  rw [diskExtension]
  split_ifs <;> rfl

omit [FiniteDimensional ℝ E] in
theorem interiorSmoothDiskConst_isConformal (g : SmoothRiemannianMetric I Q) (q : Q) :
    (interiorSmoothDiskConst (I := I) (Q := Q) q).IsConformal g := by
  have hmap := interiorSmoothDiskConst_diskExtension (I := I) (Q := Q) q
  intro z _
  have hzero (v : ℂ) :
      (interiorSmoothDiskConst (I := I) (Q := Q) q).differential z v = 0 := by
    rw [InteriorSmoothDisk.differential, hmap]
    exact congrArg (fun (L : ℂ →L[ℝ] TangentSpace I q) => L v)
      (mfderivWithin_const (𝕜 := ℝ) (E := ℂ) (H := ℂ) (I := 𝓘(ℝ, ℂ)) (M := ℂ)
        (E' := E) (H' := H) (I' := I) (M' := Q) (s := Metric.closedBall (0 : ℂ) 1)
        (x := (z : ℂ)) (c := q))
  rw [hzero 1, hzero Complex.I]
  simp

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem interiorSmoothDiskConst_isSignedWeaklyMonotoneTrace (q : Q) :
    IsSignedWeaklyMonotoneTrace (⇑(interiorSmoothDiskConst (I := I) (Q := Q) q).map)
      (constantLoops q) :=
  ⟨id, continuous_id, Or.inl ⟨monotone_id, fun _ => rfl⟩, fun _ => rfl⟩

omit [FiniteDimensional ℝ E] in
theorem diskArea_le_of_lipschitzDisk_of_constantLoops (g : SmoothRiemannianMetric I Q) (q : Q)
    (w : LipschitzDisk g) (hw : ∀ theta, w.map (diskBoundary theta) = constantLoops q theta) :
    diskArea g (fun _ : Disk => q) ≤ diskArea g w.map :=
  diskArea_const_le_diskCompetitor g q ⟨w, hw⟩

theorem diskArea_le_of_smoothDisk_of_constantLoops
    [boundarylessI : I.Boundaryless] [t2Q : T2Space Q] [compactQ : CompactSpace Q]
    (g : SmoothRiemannianMetric I Q) (q : Q)
    (w : SmoothDisk (I := I) (Q := Q))
    (hw : ∀ theta, w.map (diskBoundary theta) = constantLoops q theta) :
    diskArea g (fun _ : Disk => q) ≤ diskArea g w.map := by
  obtain ⟨v, hv⟩ := SmoothDisk.exists_lipschitz g w
  rw [← hv]
  exact diskArea_const_le_diskCompetitor g q ⟨v, fun theta => by
    rw [hv]
    exact hw theta⟩

omit [FiniteDimensional ℝ E] in
def regularLoopConst (q : Q) : RegularLoop I Q where
  toContinuousLoop := constantLoops q
  contMDiff_lift := by
    have h : (fun t : ℝ => constantLoops q (t : Surgery.Topology.Circle)) = fun _ : ℝ => q := by
      funext t
      rfl
    rw [h]
    exact contMDiff_const

omit [FiniteDimensional ℝ E] [IsManifold I ∞ Q] in
theorem regularLoopConst_toContinuousLoop (q : Q) :
    (regularLoopConst (I := I) (Q := Q) q).toContinuousLoop = constantLoops q := rfl

theorem hasConformalMinimizingInteriorDisk_constLoops_of_analytic
    [boundarylessI : I.Boundaryless] [t2Q : T2Space Q] [compactQ : CompactSpace Q]
    (g : SmoothRiemannianMetric I Q) (q : Q)
    (hharm : (interiorSmoothDiskConst (I := I) (Q := Q) q).IsHarmonic g)
    (hfinite : IntegrableOn (diskJacobian g (fun _ : Disk => q)) (Metric.closedBall (0 : ℂ) 1)) :
    HasConformalMinimizingInteriorDisk (I := I) (Q := Q) g
      (regularLoopConst (I := I) (Q := Q) q) :=
  ⟨interiorSmoothDiskConst (I := I) (Q := Q) q,
    interiorSmoothDiskConst_isConformal g q,
    hharm,
    interiorSmoothDiskConst_isSignedWeaklyMonotoneTrace q,
    hfinite,
    fun w hw => diskArea_le_of_lipschitzDisk_of_constantLoops g q w hw,
    fun w hw => diskArea_le_of_smoothDisk_of_constantLoops g q w hw⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
