import DifferentialGeometry.Geometry.Measure.Area.ManifoldMeasurable
import DifferentialGeometry.Geometry.Measure.Area.EuclideanDisk
import Mathlib.MeasureTheory.Function.LocallyIntegrable










noncomputable section

open Bundle Manifold DifferentialGeometry Filter Set MeasureTheory
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


def riemannianArea (g : SmoothRiemannianMetric I M) (u : ℂ → M) (s : Set ℂ) : ℝ :=
  ∫ z in s, riemannianAreaDensity g u z

theorem riemannianArea_nonneg (g : SmoothRiemannianMetric I M)
    (u : ℂ → M) (s : Set ℂ) : 0 ≤ riemannianArea g u s :=
  integral_nonneg (fun z => riemannianAreaDensity_nonneg g u z)

@[simp] theorem riemannianArea_const (g : SmoothRiemannianMetric I M)
    (q : M) (s : Set ℂ) : riemannianArea g (fun _ => q) s = 0 := by
  simp [riemannianArea]

theorem riemannianArea_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (u : ℂ → M) (s : Set ℂ) :
    riemannianArea (scaleMetric c hc g) u s = c * riemannianArea g u s := by
  simp only [riemannianArea, riemannianAreaDensity_scaleMetric, integral_const_mul]


def riemannianDiskArea (g : SmoothRiemannianMetric I M) (u : closedDisk → M) : ℝ :=
  riemannianArea g (diskExtension u) (Metric.closedBall 0 1)



theorem riemannianDiskArea_eq_of_extension (g : SmoothRiemannianMetric I M)
    (u : closedDisk → M) (U : ℂ → M) (hU : ∀ z : closedDisk, U z = u z) :
    riemannianDiskArea g u = riemannianArea g U (Metric.closedBall 0 1) := by
  apply integral_congr_ae
  filter_upwards [ae_disk_interior] with z hz
  apply riemannianAreaDensity_congr
  filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
  have hw' := Metric.ball_subset_closedBall hw
  exact (diskExtension_coe u ⟨w, hw'⟩).trans (hU ⟨w, hw'⟩).symm

theorem riemannianDiskArea_nonneg (g : SmoothRiemannianMetric I M)
    (u : closedDisk → M) : 0 ≤ riemannianDiskArea g u := riemannianArea_nonneg _ _ _

@[simp] theorem riemannianDiskArea_const (g : SmoothRiemannianMetric I M)
    (q : M) : riemannianDiskArea g (fun _ => q) = 0 := riemannianArea_const _ _ _

theorem riemannianDiskArea_scaleMetric (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c) (u : closedDisk → M) :
    riemannianDiskArea (scaleMetric c hc g) u = c * riemannianDiskArea g u :=
  riemannianArea_scaleMetric _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem continuousOn_riemannianAreaDensity (g : SmoothRiemannianMetric I M)
    {u : ℂ → M} {s : Set ℂ} (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I 1 u s) :
    ContinuousOn (riemannianAreaDensity g u) s := by
  have ht := hu.continuousOn_tangentMapWithin le_rfl hs.uniqueMDiffOn
  have hv (v : ℂ) : ContinuousOn (fun z : ℂ =>
      TotalSpace.mk' E (u z) (mfderiv 𝓘(ℝ, ℂ) I u z v)) s := by
    have hinput : Continuous (fun z : ℂ =>
        (TotalSpace.mk' ℂ z v : TangentBundle 𝓘(ℝ, ℂ) ℂ)) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℂ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    have hc := ht.comp hinput.continuousOn (fun _ hz => hz)
    apply hc.congr
    intro z hz
    dsimp only [Function.comp_apply, tangentMapWithin]
    rw [mfderivWithin_of_mem_nhds (hs.mem_nhds hz)]
  exact continuousOn_tangentTwoJacobian g (hv 1) (hv Complex.I)



theorem integrableOn_riemannianAreaDensity_of_contMDiffOn
    (g : SmoothRiemannianMetric I M) {u : ℂ → M} {s K : Set ℂ}
    (hs : IsOpen s) (hu : ContMDiffOn 𝓘(ℝ, ℂ) I 1 u s)
    (hK : IsCompact K) (hKs : K ⊆ s) : IntegrableOn (riemannianAreaDensity g u) K :=
  ((continuousOn_riemannianAreaDensity g hs hu).mono hKs).integrableOn_compact hK


theorem riemannianArea_union (g : SmoothRiemannianMetric I M)
    (u : ℂ → M) {s t : Set ℂ} (hs : IntegrableOn (riemannianAreaDensity g u) s)
    (ht : IntegrableOn (riemannianAreaDensity g u) t)
    (hst : AEDisjoint volume s t) (htm : MeasurableSet t) :
    riemannianArea g u (s ∪ t) = riemannianArea g u s + riemannianArea g u t :=
  setIntegral_union₀ hst htm.nullMeasurableSet hs ht

end DifferentialGeometry.Geometry
