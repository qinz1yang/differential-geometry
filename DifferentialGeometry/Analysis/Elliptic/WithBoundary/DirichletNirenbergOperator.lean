import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergTest
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalSobolevNorm
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.NormBounds

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.Chart

private def nirenbergTest
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω)
    (u : H1ComplDirichlet q) : H1ComplDirichlet q :=
  (exists_h1ComplDirichlet_standardNirenbergTest (n := n) (M := M) q α hΩ hΩc hΩs u hη hηc k h hηs).choose

private theorem nirenbergTest_coeFn
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
  (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
  (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
  {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
  (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
  (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω)
     (u : H1ComplDirichlet (n := n) (M := M) q) :
    (H1ComplDirichletToLp q (nirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs u) : M → ℝ)
      =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (standardNirenbergTest k h η (fun z => H1ComplDirichletToLp q u
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))) :=
  (exists_h1ComplDirichlet_standardNirenbergTest (n := n) (M := M) q α hΩ hΩc hΩs u hη hηc k h hηs).choose_spec.1

private theorem nirenbergTest_add
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
  (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
  (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
  {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
  (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
  (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω)
     (u v : H1ComplDirichlet (n := n) (M := M) q) :
    nirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs (u + v) =
      nirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs u +
        nirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs v := by
  apply H1ComplDirichletToLp_injective q
  apply Lp.ext
  have hval : (fun z => H1ComplDirichletToLp q (u + v)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) =ᵐ[volume.restrict Ω]
      ((fun z => H1ComplDirichletToLp q u ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) +
        (fun z => H1ComplDirichletToLp q v ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))) := by
    have heq := Lp.coeFn_add (H1ComplDirichletToLp q u) (H1ComplDirichletToLp q v)
    rw [← map_add] at heq
    exact ae_chartInverse_of_ae q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) heq
  have htest := chartPullback_ae_eq_of_ae_eq q α
    (standardNirenbergTest_congr_ae_local hΩ.measurableSet k h η hηs hval)
  rw [map_add]
  filter_upwards [nirenbergTest_coeFn q α hΩ hΩc hΩs hη hηc k h hηs (u + v),
    nirenbergTest_coeFn q α hΩ hΩc hΩs hη hηc k h hηs u,
    nirenbergTest_coeFn q α hΩ hΩc hΩs hη hηc k h hηs v,
    Lp.coeFn_add (H1ComplDirichletToLp q (nirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs u))
      (H1ComplDirichletToLp q (nirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs v)), htest]
      with x hx hu hv hsum htest
  rw [hx, htest, standardNirenbergTest_add, hsum, Pi.add_apply, hu, hv]
  simp only [chartPullback]
  split_ifs <;> simp

private theorem nirenbergTest_smul
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
  (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
  (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
  {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
  (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
  (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω)
     (c : ℝ) (u : H1ComplDirichlet (n := n) (M := M) q) :
    nirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs (c • u) =
      c • nirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs u := by
  apply H1ComplDirichletToLp_injective q
  apply Lp.ext
  have hval : (fun z => H1ComplDirichletToLp q (c • u)
        ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) =ᵐ[volume.restrict Ω]
      c • (fun z => H1ComplDirichletToLp q u ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) := by
    have heq := Lp.coeFn_smul c (H1ComplDirichletToLp q u)
    rw [← map_smul] at heq
    exact ae_chartInverse_of_ae q α hΩ.measurableSet hΩc
      (hΩs.trans (image_mono interior_subset)) heq
  have htest := chartPullback_ae_eq_of_ae_eq q α
    (standardNirenbergTest_congr_ae_local hΩ.measurableSet k h η hηs hval)
  rw [map_smul]
  filter_upwards [nirenbergTest_coeFn q α hΩ hΩc hΩs hη hηc k h hηs (c • u),
    nirenbergTest_coeFn q α hΩ hΩc hΩs hη hηc k h hηs u,
    Lp.coeFn_smul c (H1ComplDirichletToLp q (nirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs u)), htest]
      with x hx hu hsum htest
  rw [hx, htest, standardNirenbergTest_smul, hsum, Pi.smul_apply, hu]
  simp only [chartPullback]
  split_ifs <;> simp

private def nirenbergTestLinear
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
  (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
  (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
  {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
  (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
  (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω)
     : H1ComplDirichlet (n := n) (M := M) q →ₗ[ℝ] H1ComplDirichlet (n := n) (M := M) q where
  toFun := nirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs
  map_add' := nirenbergTest_add q α hΩ hΩc hΩs hη hηc k h hηs
  map_smul' := nirenbergTest_smul q α hΩ hΩc hΩs hη hηc k h hηs


private theorem exists_norm_nirenbergTest_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {r : ℝ} (hηs : Metric.cthickening r (tsupport η) ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin (Module.finrank ℝ EuN)) (h : ℝ) (hh : |h| ≤ r)
      (u : H1ComplDirichlet q),
      ‖nirenbergTest q α hΩ hΩc hΩs hη hηc k h ((Metric.cthickening_mono hh _).trans hηs) u‖ ≤
        C * |h⁻¹| ^ 2 * ‖u‖ := by
  obtain ⟨A, hA, hAb⟩ := exists_norm_h1ComplDirichletChartPullback_le_wkpNorm q α hΩ hΩc hΩs
  obtain ⟨B, hB, hBb⟩ := exists_wkpNorm_chartInverse_H1ComplDirichletToLp_le q α hΩ hΩc hΩs
  obtain ⟨D, hD, hDb⟩ := exists_wkpNorm_standardNirenbergTest_le_local hΩ hη hηc hηs
  refine ⟨A * D * B, by positivity, ?_⟩
  intro k h hh u
  let v : EuStd → ℝ := fun z => H1ComplDirichletToLp q u
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  let f := standardNirenbergTest k h η v
  have hv : MemWkp 1 2 v Ω := memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u
  have hroom := (Metric.cthickening_mono hh (tsupport η)).trans hηs
  have hf : MemWkp 1 2 f Ω :=
    (memWkp_standardNirenbergTest_of_memWkp_local hΩ hv hη hηc k h hroom).mono_set
      (by norm_num) hΩ (subset_univ _)
  have hfs : tsupport f ⊆ Ω :=
    (standardNirenbergTest_tsupport_subset_cthickening k h η v).trans hroom
  have heq : nirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom u =
      h1ComplDirichletChartPullback q α hΩ hΩc hΩs hf hfs := by
    apply eq_h1ComplDirichletChartPullback_of_coeFn
    exact nirenbergTest_coeFn q α hΩ hΩc hΩs hη hηc k h hroom u
  rw [heq]
  have hn : iteratedWeakSobolevNorm 1 2 f Ω ≤ ENNReal.ofReal (D * |h⁻¹| ^ 2 * (B * ‖u‖)) := by
    calc
      _ ≤ iteratedWeakSobolevNorm 1 2 f univ :=
        wkpNorm_mono_set (by norm_num) hΩ (subset_univ _)
          (memWkp_standardNirenbergTest_of_memWkp_local hΩ hv hη hηc k h hroom)
      _ ≤ ENNReal.ofReal (D * |h⁻¹| ^ 2) * iteratedWeakSobolevNorm 1 2 v Ω := hDb k h hh hv
      _ ≤ ENNReal.ofReal (D * |h⁻¹| ^ 2) * ENNReal.ofReal (B * ‖u‖) := mul_le_mul' le_rfl (hBb u)
      _ = _ := (ENNReal.ofReal_mul (mul_nonneg hD (sq_nonneg _))).symm
  have hr := ENNReal.toReal_le_of_le_ofReal (mul_nonneg (mul_nonneg hD (sq_nonneg _))
    (mul_nonneg hB (norm_nonneg u))) hn
  exact (hAb f hf hfs).trans ((mul_le_mul_of_nonneg_left hr hA).trans_eq (by ring))

def dirichletNirenbergTest
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    H1ComplDirichlet q →L[ℝ] H1ComplDirichlet q :=
  (nirenbergTestLinear q α hΩ hΩc hΩs hη hηc k h hηs).mkContinuous
    ((exists_norm_nirenbergTest_le q α hΩ hΩc hΩs hη hηc hηs).choose * |h⁻¹| ^ 2)
    (fun u => (exists_norm_nirenbergTest_le q α hΩ hΩc hΩs hη hηc hηs).choose_spec.2 k h le_rfl u)


theorem dirichletNirenbergTest_coeFn
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω) (u : H1ComplDirichlet q) :
    (H1ComplDirichletToLp q (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs u) : M → ℝ)
      =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
        chartPullback I_hs α (standardNirenbergTest k h η (fun z => H1ComplDirichletToLp q u
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))) :=
  nirenbergTest_coeFn q α hΩ hΩc hΩs hη hηc k h hηs u

theorem dirichletNirenbergTest_chartInverse_coeFn
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (v : H1ComplDirichlet q) {η : EuStd → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (h : ℝ) (hroom : Metric.cthickening |h| (tsupport η) ⊆ Ω) :
    let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    (fun z => H1ComplDirichletToLp q
      (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom v) (x z)) =ᵐ[volume.restrict Ω]
        standardNirenbergTest k h η (fun z => H1ComplDirichletToLp q v (x z)) := by
  intro x
  have hraw := ae_chartInverse_of_ae q α hΩ.measurableSet hΩc
    (hΩs.trans (image_mono interior_subset))
    (dirichletNirenbergTest_coeFn q α hΩ hΩc hΩs hη hηc k h hroom v)
  filter_upwards [hraw, ae_restrict_mem hΩ.measurableSet] with z hz hzΩ
  change H1ComplDirichletToLp q
    (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom v) (x z) = _ at hz
  rw [hz]
  have hzt : (toEuclidean (E := EuN)).symm z ∈ (extChartAt I_hs α).target := by
    obtain ⟨y, hy, hyz⟩ := hΩs (subset_closure hzΩ)
    rw [← hyz, (toEuclidean (E := EuN)).symm_apply_apply]
    exact interior_subset hy
  have hxs := (extChartAt I_hs α).map_target hzt
  rw [extChartAt_source] at hxs
  dsimp only [x]
  rw [chartPullback_apply_of_mem α _ hxs, (extChartAt I_hs α).right_inv hzt,
    (toEuclidean (E := EuN)).apply_symm_apply]

theorem dirichletLocalWeakPartialLp_dirichletNirenbergTest_coeFn
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k i : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω) (u : H1ComplDirichlet q) :
    (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i
      (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs u) : EuStd → ℝ)
      =ᵐ[volume.restrict Ω] chosenWeakPartial' 2 i
        (standardNirenbergTest k h η (fun z => H1ComplDirichletToLp q u
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))) Ω :=
  (exists_h1ComplDirichlet_standardNirenbergTest q α hΩ hΩc hΩs u hη hηc k h hηs).choose_spec.2 i

theorem exists_norm_dirichletNirenbergTest_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {r : ℝ} (hηs : Metric.cthickening r (tsupport η) ⊆ Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin (Module.finrank ℝ EuN)) (h : ℝ) (hh : |h| ≤ r),
      ‖dirichletNirenbergTest (n := n) (M := M) q α hΩ hΩc hΩs hη hηc k h
        ((Metric.cthickening_mono hh _).trans hηs)‖ ≤ C * |h⁻¹| ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_norm_nirenbergTest_le q α hΩ hΩc hΩs hη hηc hηs
  refine ⟨C, hC, fun k h hh => ?_⟩
  exact (dirichletNirenbergTest (n := n) (M := M) q α hΩ hΩc hΩs hη hηc k h
    ((Metric.cthickening_mono hh _).trans hηs)).opNorm_le_bound
      (mul_nonneg hC (sq_nonneg _)) (hb k h hh)

theorem dirichletNirenbergTest_zero_h
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (hηs : Metric.cthickening |(0 : ℝ)| (tsupport η) ⊆ Ω) :
    dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k 0 hηs = 0 := by
  ext u
  apply H1ComplDirichletToLp_injective q
  apply Lp.ext
  simp only [zero_apply, map_zero]
  filter_upwards [dirichletNirenbergTest_coeFn q α hΩ hΩc hΩs hη hηc k 0 hηs u,
    Lp.coeFn_zero ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)] with x hx hz
  rw [hx, hz, standardNirenbergTest_zero_h]
  simp only [chartPullback]
  split_ifs <;> rfl


theorem dirichletNirenbergTest_compLpL_coeFn
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
    (hηs : Metric.cthickening |h| (tsupport η) ⊆ Ω)
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (u : Lp (H1ComplDirichlet q) 2 μ) :
    ∀ᵐ t ∂μ,
      (H1ComplDirichletToLp q
        ((dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs).compLpL 2 μ u t) : M → ℝ)
        =ᵐ[riemannianVolumeMeasure (I := I_hs) (M := M) q]
          chartPullback I_hs α (standardNirenbergTest k h η (fun z => H1ComplDirichletToLp q (u t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)))) := by
  filter_upwards [(dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hηs).coeFn_compLpL u] with t ht
  rw [ht]
  exact dirichletNirenbergTest_coeFn q α hΩ hΩc hΩs hη hηc k h hηs (u t)

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
