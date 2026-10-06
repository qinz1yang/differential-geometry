import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SourceChartReplacement
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.WeakJordanDensity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskCriterion
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskLocality
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Lipschitz
import DifferentialGeometry.Geometry.HarmonicMap.ConformalSource

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Topology
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

/-- The literal affine restriction, using the existing disk extension.
The proper-subdisk hypotheses in the theorems below ensure that no value is
taken outside the original open disk. -/
def affineSubdisk {M : Type*} [TopologicalSpace M]
    (u : C(closedDisk, M)) (a : ℂ) (r : ℝ) : C(closedDisk, M) :=
  ⟨fun z => diskExtension u (a + r • (z : ℂ)),
    (u.continuous.comp diskRetraction_lipschitz.continuous).comp
      (continuous_const.add
        ((continuous_const : Continuous (fun _ : closedDisk => r)).smul continuous_subtype_val))⟩

private def affineSourceDiffeomorph (a : ℂ) (r : ℝ) (hr : r ≠ 0) :
    Diffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ ∞ where
  toEquiv :=
    { toFun := fun z => a + r • z
      invFun := fun z => r⁻¹ • (z - a)
      left_inv := fun z => by
        change r⁻¹ • ((a + r • z) - a) = z
        rw [add_sub_cancel_left, inv_smul_smul₀ hr]
      right_inv := fun z => by
        change a + r • (r⁻¹ • (z - a)) = z
        rw [smul_inv_smul₀ hr, add_comm a, sub_add_cancel] }
  contMDiff_toFun := (contDiff_const.add (contDiff_const_smul r)).contMDiff
  contMDiff_invFun := (contDiff_const_smul r⁻¹).contMDiff.comp
    (contMDiff_id.sub contMDiff_const)

private theorem affineSubdisk_mapsTo {a : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hinside : ‖a‖ + r < 1) :
    MapsTo (fun z : ℂ => a + r • z) (Metric.closedBall (0 : ℂ) 1)
      (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have hz' : ‖z‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hnorm : ‖a + r • z‖ < 1 := calc
    ‖a + r • z‖ ≤ ‖a‖ + ‖r • z‖ := norm_add_le _ _
    _ = ‖a‖ + r * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
    _ ≤ ‖a‖ + r := by nlinarith
    _ < 1 := hinside
  simpa only [Metric.mem_ball, dist_zero_right] using hnorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- Every Lipschitz weak-phase filling of the induced regular boundary loop
has at least the area of the literal source-chart restriction. The comparison
uses the original metric and the original disk's minimality. -/
theorem IsMorreyDisk.minimizesLipschitz_diskThroughSourceChart
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u) {L : ℝ≥0}
    (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    {n : WithTop ℕ∞} (e : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ n)
    (hn : 1 ≤ n) (hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source)
    (hinside : e '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1)
    (hsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
      (fun t : ℝ => diskTrace (diskThroughSourceChart u e hsrc) (t : loopCircle)))
    (himmersed : ∀ t : ℝ, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun s : ℝ => diskTrace (diskThroughSourceChart u e hsrc) (s : loopCircle)) t 1 ≠ 0)
    (v : C(closedDisk, M))
    (hvtrace : DiskWeakJordanTrace (diskTrace (diskThroughSourceChart u e hsrc)) v)
    (hvLip : ∃ C : ℝ≥0, ∀ z w, riemannianEDistOf g (v z) (v w) ≤
      (C : ℝ≥0∞) * edist z w) :
    riemannianDiskArea g (diskThroughSourceChart u e hsrc) ≤ riemannianDiskArea g v := by
  obtain ⟨C, hC⟩ := hvLip
  obtain ⟨d, ⟨hdtrace, D, hdLip⟩, hdarea⟩ :=
    exists_spanning_disk_area_eq_of_weakJordanTrace g hsmooth himmersed hvtrace hC
  by_contra hle
  have hdlt : riemannianDiskArea g d < riemannianDiskArea g (diskThroughSourceChart u e hsrc) := by
    rw [hdarea]
    exact lt_of_not_ge hle
  obtain ⟨w, K, hwLip, hwtrace, _, hwarea⟩ :=
    exists_disk_area_lt_of_sourceChart_competitor g u d huLip hdLip e hn hsrc hinside
      hdtrace (W := Set.univ) (subset_univ _) (subset_univ _) hdlt
  obtain ⟨σ, hσ, htrace⟩ := hu.trace
  have hw : DiskWeakJordanTrace γ w := ⟨σ, hσ, hwtrace.trans htrace⟩
  exact (not_lt_of_ge (hu.minimizesLipschitz w hw ⟨K, hwLip⟩)) hwarea

omit [T3Space M] in
/-- An interior affine restriction has the literal smooth extension obtained
by composing the original disk extension with that same affine map. -/
theorem IsMorreyDisk.smoothDiskExtension_affineSubdisk
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u)
    (a : ℂ) (r : ℝ) (hr : 0 ≤ r) (hinside : ‖a‖ + r < 1) :
    SmoothDiskExtension (E := E) (affineSubdisk u a r)
      (fun z => diskExtension u (a + r • z)) := by
  have hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (fun z : ℂ => a + r • z) :=
    (contDiff_const.add (contDiff_const_smul r)).contMDiff
  refine ⟨fun _ => rfl, (fun z : ℂ => a + r • z) ⁻¹' Metric.ball (0 : ℂ) 1,
    Metric.isOpen_ball.preimage hφ.continuous, affineSubdisk_mapsTo hr hinside, ?_⟩
  exact hu.smoothInterior.comp hφ.contMDiffOn (fun _ hz => hz)

/-- The same disk restricted to a proper interior round subdisk remains a
Morrey disk for its literal induced trace and the original metric. Regularity
of that boundary parametrization is explicit; no rank is inferred from smoothness. -/
theorem IsMorreyDisk.affineSubdisk
    {g : SmoothRiemannianMetric 𝓘(ℝ, E) M} {γ : freeLoop M}
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g γ u) {L : ℝ≥0}
    (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤ (L : ℝ≥0∞) * edist z w)
    (a : ℂ) (r : ℝ) (hr : 0 < r) (hinside : ‖a‖ + r < 1)
    (himmersed : ∀ t : ℝ, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun s : ℝ => diskTrace (affineSubdisk u a r) (s : loopCircle)) t 1 ≠ 0) :
    IsMorreyDisk g (diskTrace (affineSubdisk u a r)) (affineSubdisk u a r) := by
  let φ : ℂ → ℂ := fun z => a + r • z
  let d := DifferentialGeometry.Geometry.affineSubdisk u a r
  have hExt : SmoothDiskExtension (E := E) d (diskExtension u ∘ φ) :=
    hu.smoothDiskExtension_affineSubdisk a r hr.le hinside
  have hφ (z : ℂ) : AnalyticAt ℂ φ z := by
    simpa only [φ, Complex.real_smul] using
      (analyticAt_const.fun_add (analyticAt_const.fun_mul analyticAt_id) :
        AnalyticAt ℂ (fun w : ℂ => a + (r : ℂ) * w) z)
  have hmaps := affineSubdisk_mapsTo hr.le hinside
  obtain ⟨K, hdLip⟩ := hExt.lipschitz g
  apply isMorreyDisk_of_minimizesLipschitz g hExt.smoothUpToBoundary.interior
  · intro z hz
    have hzin := hmaps (Metric.ball_subset_closedBall hz)
    have hU := (hu.smoothInterior.contMDiffAt (Metric.isOpen_ball.mem_nhds hzin))
    have hc : DiskMapConformalAt g (diskExtension u ∘ φ) z :=
      conformal_mfderiv_comp_complex g (hU.mdifferentiableAt (by simp))
        (hφ z).differentiableAt (hu.conformal _ hzin).1 (hu.conformal _ hzin).2
    exact (diskMapConformalAt_congr_of_eventuallyEq g
      (hExt.eventuallyEq_diskExtension hz)).mp hc
  · intro z hz
    have hzin := hmaps (Metric.ball_subset_closedBall hz)
    have hU := (hu.smoothInterior.contMDiffAt (Metric.isOpen_ball.mem_nhds hzin)).of_le
      (show (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) from by simp)
    have ht : diskMapTension g (diskExtension u ∘ φ) z = 0 := by
      change planarTension g (diskExtension u ∘ φ) z = 0
      rw [planarTension_comp_holomorphic g (U := diskExtension u) (ψ := φ) (z := z) hU (hφ z)]
      change ‖deriv φ z‖ ^ 2 • diskMapTension g (diskExtension u) (φ z) = 0
      rw [hu.harmonic _ hzin, smul_zero]
    have ht' : (diskMapTension g (diskExtension d) z : E) = 0 := by
      rw [← diskMapTension_congr_of_eventuallyEq g (hExt.eventuallyEq_diskExtension hz)]
      exact ht
    exact ht'
  · exact integrable_diskMapEnergyDensity g hdLip
  · exact DiskWeakJordanTrace.of_diskTrace_eq rfl
  · let e := (affineSourceDiffeomorph a r hr.ne').toPartialDiffeomorph
    have hsrc : Metric.closedBall (0 : ℂ) 1 ⊆ e.source := subset_univ _
    have he : diskThroughSourceChart u e hsrc = d := by ext z; rfl
    have hei : e '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 := by
      rintro _ ⟨z, hz, rfl⟩
      exact hmaps hz
    have hsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
        (fun t : ℝ => diskTrace (diskThroughSourceChart u e hsrc) (t : loopCircle)) := by
      rw [he]
      exact hExt.smoothUpToBoundary.trace
    have himmersed' : ∀ t : ℝ, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
        (fun s : ℝ => diskTrace (diskThroughSourceChart u e hsrc) (s : loopCircle)) t 1 ≠ 0 := by
      rw [he]
      exact himmersed
    simpa only [he] using hu.minimizesLipschitz_diskThroughSourceChart huLip e
      (by simp) hsrc hei hsmooth himmersed'

end DifferentialGeometry.Geometry
