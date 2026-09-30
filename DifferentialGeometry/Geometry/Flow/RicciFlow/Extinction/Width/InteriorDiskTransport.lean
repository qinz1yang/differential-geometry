import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.DiffeomorphismTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Width.PlateauBridge

noncomputable section
open Bundle Manifold Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Width

section Differential
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}
  {Q A : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  [TopologicalSpace A] [ChartedSpace G A] [IsManifold J ∞ A]

omit [IsManifold I ∞ Q] in
theorem InteriorSmoothDisk.contMDiffAt_extension
    (u : InteriorSmoothDisk (I := I) (Q := Q)) (z : Disk)
    (hz : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1) :
    ContMDiffAt 𝓘(ℝ, ℂ) I ∞ (diskExtension u.map) (z : ℂ) := by
  obtain ⟨U⟩ := u.smooth z hz
  have heq : U.map =ᶠ[𝓝 (z : ℂ)] diskExtension u.map := by
    filter_upwards [U.isOpen_domain.mem_nhds U.mem_domain, Metric.isOpen_ball.mem_nhds hz] with w hw hb
    exact U.agrees ⟨hw, Metric.ball_subset_closedBall hb⟩
  exact (U.smooth.contMDiffAt (U.isOpen_domain.mem_nhds U.mem_domain)).congr_of_eventuallyEq heq.symm

omit [IsManifold I ∞ Q] [IsManifold J ∞ A] in
theorem InteriorSmoothDisk.differential_comp_diffeomorph
    (Φ : Q ≃ₘ⟮I, J⟯ A) (u : InteriorSmoothDisk (I := I) (Q := Q))
    (z : Disk) (hz : (z : ℂ) ∈ Metric.ball (0 : ℂ) 1) (X : ℂ) :
    (InteriorSmoothDisk.compDiffeomorph Φ u).differential z X =
      mfderiv I J (Φ : Q → A) (u.map z) (u.differential z X) := by
  have hext : diskExtension (InteriorSmoothDisk.compDiffeomorph Φ u).map =
      fun w => Φ (diskExtension u.map w) := by
    funext w
    by_cases hw : w ∈ Metric.closedBall (0 : ℂ) 1 <;>
      simp only [diskExtension, hw, ↓reduceDIte, InteriorSmoothDisk.compDiffeomorph, ContinuousMap.coe_mk]
  have hcomp := mfderiv_comp_mfderivWithin_of_eq (s := Metric.closedBall (0 : ℂ) 1)
    (f := diskExtension u.map) (g := (Φ : Q → A)) (y := u.map z)
    (Φ.contMDiff.contMDiffAt.mdifferentiableAt (by simp))
    ((u.contMDiffAt_extension z hz).mdifferentiableAt (by simp)).mdifferentiableWithinAt
    (disk_uniqueDiffWithinAt z).uniqueMDiffWithinAt (diskExtension_coe u.map z)
  change mfderivWithin 𝓘(ℝ, ℂ) J (diskExtension (InteriorSmoothDisk.compDiffeomorph Φ u).map)
    (Metric.closedBall (0 : ℂ) 1) (z : ℂ) X = _
  rw [hext]
  simp only [Function.comp_def] at hcomp
  rw [hcomp]
  rfl

end Differential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]
  {A : Type*} [TopologicalSpace A] [ChartedSpace E A] [IsManifold 𝓘(ℝ, E) ∞ A]
  [T2Space Q] [T2Space A]

omit [T2Space Q] in
theorem InteriorSmoothDisk.isConformal_comp_diffeomorph_symm
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : SmoothRiemannianMetric I Q)
    (u : InteriorSmoothDisk (I := 𝓘(ℝ, E)) (Q := A))
    (h : u.IsConformal (Diffeomorph.pullbackMetricCross g Φ.symm)) :
    (InteriorSmoothDisk.compDiffeomorph Φ.symm u).IsConformal g := by
  intro z hz
  have hid (X Y : ℂ) : g.inner ((InteriorSmoothDisk.compDiffeomorph Φ.symm u).map z)
      ((InteriorSmoothDisk.compDiffeomorph Φ.symm u).differential z X)
      ((InteriorSmoothDisk.compDiffeomorph Φ.symm u).differential z Y) =
      (Diffeomorph.pullbackMetricCross g Φ.symm).inner (u.map z)
        (u.differential z X) (u.differential z Y) := by
    rw [InteriorSmoothDisk.differential_comp_diffeomorph Φ.symm u z hz X,
      InteriorSmoothDisk.differential_comp_diffeomorph Φ.symm u z hz Y,
      Diffeomorph.pullbackMetricCross_inner]
    rfl
  exact ⟨(hid 1 Complex.I).trans (h z hz).1,
    (hid 1 1).trans ((h z hz).2.trans (hid Complex.I Complex.I).symm)⟩

theorem InteriorSmoothDisk.isHarmonic_comp_diffeomorph_symm [I.Boundaryless]
    (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (g : SmoothRiemannianMetric I Q)
    (u : InteriorSmoothDisk (I := 𝓘(ℝ, E)) (Q := A))
    (h : u.IsHarmonic (Diffeomorph.pullbackMetricCross g Φ.symm)) :
    (InteriorSmoothDisk.compDiffeomorph Φ.symm u).IsHarmonic g := by
  intro z hz F
  let G : DiskLocalExtension (I := 𝓘(ℝ, E)) u.map z := {
    map := fun w => Φ (F.map w)
    domain := F.domain
    isOpen_domain := F.isOpen_domain
    mem_domain := F.mem_domain
    smooth := Φ.contMDiff.comp_contMDiffOn F.smooth
    agrees := by
      intro w hw
      have hF : F.map w = Φ.symm (u.map ⟨w, hw.2⟩) :=
        (F.agrees hw).trans
          (diskExtension_coe (InteriorSmoothDisk.compDiffeomorph Φ.symm u).map ⟨w, hw.2⟩)
      change Φ (F.map w) = diskExtension u.map w
      rw [hF, Φ.apply_symm_apply]
      exact (diskExtension_coe u.map ⟨w, hw.2⟩).symm }
  have hzero : diskLocalTension (Diffeomorph.pullbackMetricCross g Φ.symm)
      (fun w => Φ (F.map w)) z = 0 := h z hz G
  have hnat := diskLocalTension_natCrossAt (g := g) (Φ := Φ)
    (F := F.map) (F.smooth.contMDiffAt (F.isOpen_domain.mem_nhds F.mem_domain))
  exact (mfderiv_eq_zero_iff_of_diffeomorph Φ (diskLocalTension g F.map z)).mp (hnat.symm.trans hzero)

omit [T2Space Q] in
theorem diskJacobian_pullbackMetricCross_ae
    (g : SmoothRiemannianMetric I Q) (Φ : Q ≃ₘ⟮I, 𝓘(ℝ, E)⟯ A) (u : Disk → A) :
    diskJacobian (Diffeomorph.pullbackMetricCross g Φ.symm) u
      =ᵐ[volume.restrict (Metric.closedBall (0 : ℂ) 1)]
        diskJacobian g (fun z => Φ.symm (u z)) := by
  filter_upwards [Geometry.ae_disk_interior] with z hz
  have hmem : Metric.closedBall (0 : ℂ) 1 ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  rw [diskJacobian, diskJacobian,
    parametricJacobian_eq_riemannianAreaDensity_of_mem_nhds _ _ hmem,
    parametricJacobian_eq_riemannianAreaDensity_of_mem_nhds _ _ hmem,
    riemannianAreaDensity_pullbackMetricCross]
  congr 1
  funext w
  by_cases hw : w ∈ Metric.closedBall (0 : ℂ) 1 <;>
    simp only [diskExtension, hw, ↓reduceDIte]

end DifferentialGeometry.PDE.RicciFlow.Extinction.Width
