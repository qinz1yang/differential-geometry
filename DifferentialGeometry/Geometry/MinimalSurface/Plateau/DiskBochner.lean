import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskCovariantCommutation
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.LaplacianCalculus



noncomputable section

open Set Function Bundle Manifold DifferentialGeometry Filter
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]



theorem second_fderiv_diskMapConformalCoefficient
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v w : ℂ) :
    fderiv ℝ (fderiv ℝ (diskMapConformalCoefficient g U)) z v w =
      2 * g.inner (U z) (diskMapCovariantThirdPartial g U z v w 1) (diskMapPartial U z 1) +
      2 * g.inner (U z) (diskMapCovariantPartial g U z w 1)
        (diskMapCovariantPartial g U z v 1) := by
  let line : ℝ → ℂ := fun t => z + t • v
  have hl : ContDiff ℝ ∞ line := contDiff_const.add (contDiff_id.smul contDiff_const)
  have hl0 : line 0 = z := by simp [line]
  have ht : Tendsto line (𝓝 0) (𝓝 z) := by
    have h := hl.continuous.continuousAt (x := 0)
    change Tendsto line (𝓝 0) (𝓝 (line 0)) at h
    rwa [hl0] at h
  have hγ : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (U ∘ line) 0 :=
    ((hU z hz).contMDiffAt (hs.mem_nhds hz)).comp_of_eq hl.contMDiff.contMDiffAt hl0
  have hV := contMDiffAt_diskMapCovariantPartial_line g hs hU hz v w 1
  have hW : ContMDiffAt 𝓘(ℝ, ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun t => TotalSpace.mk' E (U (line t)) (diskMapPartial (E := E) U (line t) 1)) 0 :=
    (((contMDiffOn_source_partial hs hU (m := ∞) (by simp) (1 : ℂ)) z hz).contMDiffAt
      (hs.mem_nhds hz)).comp_of_eq hl.contMDiff.contMDiffAt hl0
  have hinner := inner_deriv_at (by simp : (1 : WithTop ℕ∞) ≤ ∞) g (U ∘ line)
    (fun t => diskMapCovariantPartial g U (line t) w 1)
    (fun t => diskMapPartial U (line t) 1) 0 hγ
    ((contDiffAt_chartRepAt_of_section hV).differentiableAt (by norm_num))
    ((contDiffAt_chartRepAt_of_section hW).differentiableAt (by simp))
  have hnear : (fun t => fderiv ℝ (diskMapConformalCoefficient g U) (line t) w) =ᶠ[𝓝 0]
      (fun t => 2 * g.inner (U (line t)) (diskMapCovariantPartial g U (line t) w 1)
        (diskMapPartial U (line t) 1)) := by
    filter_upwards [ht.eventually (hs.mem_nhds hz)] with t ht
    exact fderiv_diskMapConformalCoefficient g hs hU ht w
  have ha : ContDiffAt ℝ 2 (diskMapConformalCoefficient g U) z :=
    ((contDiffOn_diskMapConformalCoefficient g hs hU z hz).contDiffAt
      (hs.mem_nhds hz)).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hd := (ha.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdw := ((ha.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
    (by norm_num) (f := fun q => fderiv ℝ (diskMapConformalCoefficient g U) q w)
  have hline : HasDerivAt line v 0 := by
    simpa [line] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hchain := hdw.hasFDerivAt.comp_hasDerivAt_of_eq (x := 0) hline hl0.symm
  have heq := hchain.unique ((hinner.const_mul (2 : ℝ)).congr_of_eventuallyEq hnear)
  have hpartial : fderiv ℝ (fun q => fderiv ℝ (diskMapConformalCoefficient g U) q w) z v =
      fderiv ℝ (fderiv ℝ (diskMapConformalCoefficient g U)) z v w := by
    rw [fderiv_clm_apply hd (differentiableAt_const w)]
    simp
  rw [hpartial] at heq
  simp only [Function.comp_apply] at heq
  erw [hl0] at heq
  rw [heq]
  exact mul_add _ _ _



theorem diskMapCovariantThirdPartial_symm_right
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    {z : ℂ} (hz : z ∈ s) (v w x : ℂ) :
    diskMapCovariantThirdPartial g U z v w x = diskMapCovariantThirdPartial g U z v x w := by
  apply covDerivAlong_congr_of_eventuallyEq
  have hl : Tendsto (fun t : ℝ => z + t • v) (𝓝 0) (𝓝 z) := by
    have h : Continuous (fun t : ℝ => z + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [ContinuousAt, zero_smul, add_zero] using h.continuousAt (x := (0 : ℝ))
  filter_upwards [hl.eventually (hs.mem_nhds hz)] with t ht
  exact diskMapCovariantPartial_symm g hs hU ht w x



theorem diskMapCovariantThirdPartial_trace_eq_zero
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hharm : ∀ q ∈ s, diskMapTension g U q = 0)
    {z : ℂ} (hz : z ∈ s) (v : ℂ) :
    diskMapCovariantThirdPartial g U z v 1 1 +
      diskMapCovariantThirdPartial g U z v Complex.I Complex.I = 0 := by
  let line : ℝ → ℂ := fun t => z + t • v
  have hl : Tendsto line (𝓝 0) (𝓝 z) := by
    have h : Continuous (fun t : ℝ => z + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [ContinuousAt, zero_smul, add_zero, line] using h.continuousAt (x := (0 : ℝ))
  have hzero : ∀ᶠ t in 𝓝 (0 : ℝ),
      diskMapCovariantPartial g U (line t) 1 1 +
        diskMapCovariantPartial g U (line t) Complex.I Complex.I = 0 := by
    filter_upwards [hl.eventually (hs.mem_nhds hz)] with t ht
    exact hharm _ ht
  have hadd := covDerivAlong_add g (U ∘ line)
    (fun t => diskMapCovariantPartial g U (line t) 1 1)
    (fun t => diskMapCovariantPartial g U (line t) Complex.I Complex.I) 0
    ((contDiffAt_chartRepAt_of_section
      (contMDiffAt_diskMapCovariantPartial_line g hs hU hz v 1 1)).differentiableAt (by norm_num))
    ((contDiffAt_chartRepAt_of_section
      (contMDiffAt_diskMapCovariantPartial_line g hs hU hz v Complex.I Complex.I)).differentiableAt
        (by norm_num))
  rw [covDerivAlong_congr_of_eventuallyEq g (U ∘ line) hzero, covDerivAlong_zero] at hadd
  exact hadd.symm



theorem diskMapCovariantThirdPartial_harmonic_trace [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hharm : ∀ q ∈ s, diskMapTension g U q = 0)
    {z : ℂ} (hz : z ∈ s) :
    diskMapCovariantThirdPartial g U z 1 1 1 +
      diskMapCovariantThirdPartial g U z Complex.I Complex.I 1 =
      -riemannOp (LeviCivita g) (U z) (diskMapPartial U z 1)
        (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I) := by
  have hc := diskMapCovariantThirdPartial_commute g hs hU hz 1 Complex.I Complex.I
  rw [diskMapCovariantThirdPartial_symm_right g hs hU hz Complex.I 1 Complex.I] at hc
  apply eq_neg_iff_add_eq_zero.mpr
  rw [← hc]
  calc
    _ = diskMapCovariantThirdPartial g U z 1 1 1 +
        diskMapCovariantThirdPartial g U z 1 Complex.I Complex.I := by abel
    _ = 0 := diskMapCovariantThirdPartial_trace_eq_zero g hs hU hharm hz 1



theorem laplacian_diskMapConformalCoefficient_of_harmonic [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hharm : ∀ q ∈ s, diskMapTension g U q = 0)
    {z : ℂ} (hz : z ∈ s) :
    Laplacian.laplacian (diskMapConformalCoefficient g U) z =
      2 * (g.inner (U z) (diskMapCovariantPartial g U z 1 1) (diskMapCovariantPartial g U z 1 1) +
        g.inner (U z) (diskMapCovariantPartial g U z Complex.I 1)
          (diskMapCovariantPartial g U z Complex.I 1) -
        g.inner (U z) (riemannOp (LeviCivita g) (U z) (diskMapPartial U z 1)
          (diskMapPartial U z Complex.I) (diskMapPartial U z Complex.I)) (diskMapPartial U z 1)) := by
  rw [DifferentialGeometry.Analysis.laplacian_complex_eq_fderiv,
    second_fderiv_diskMapConformalCoefficient g hs hU hz,
    second_fderiv_diskMapConformalCoefficient g hs hU hz]
  have ht := congrArg (fun X : TangentSpace 𝓘(ℝ, E) (U z) => g.inner (U z) X (diskMapPartial U z 1))
    (diskMapCovariantThirdPartial_harmonic_trace g hs hU hharm hz)
  simp only [map_add, _root_.add_apply, map_neg, _root_.neg_apply] at ht
  linarith

end DifferentialGeometry.Geometry
