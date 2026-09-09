import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.SourceBounds
import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergOperator

noncomputable section

open Manifold MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff Manifold

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Sobolev (diffQuot)
open DifferentialGeometry.Analysis.Sobolev.NirenbergStandardTest
open DifferentialGeometry.Analysis.Sobolev.NirenbergDiffQuotTestFunction
open DifferentialGeometry.Analysis.Sobolev.Chart
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

private theorem abs_integral_mul_standardNirenbergTest_chart_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (v : H1ComplDirichlet q) {f η : EuStd → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) (k : Fin (Module.finrank ℝ EuN)) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    {ε : ℝ} (hε : 0 < ε) (h : ℝ) (hroom : cthickening |h| (tsupport η) ⊆ Ω) :
    let U := fun z => H1ComplDirichletToLp q v
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
    |∫ z in Ω, f z * standardNirenbergTest k h η U z| ≤
      ε * (∫ z, (η z * diffQuot k h (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k v) z)^2) +
      (2 * ε)⁻¹ * (∫ z in Ω, (f z)^2) +
      4 * ε * N^2 * (∫ z in tsupport η, (diffQuot k h U z)^2) := by
  exact abs_integral_mul_standardNirenbergTest_le_local hΩ
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs v).memLp
    (Lp.memLp (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k v)) hf k
    (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k v)
    hη hηc hηb hηd hε h hroom

private theorem dirichletNirenbergTest_chart_ae
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (v : H1ComplDirichlet q) {η : EuStd → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin (Module.finrank ℝ EuN)) (h : ℝ) (hroom : cthickening |h| (tsupport η) ⊆ Ω) :
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

theorem abs_integral_mul_dirichletNirenbergTest_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (v : H1ComplDirichlet q) {f η : EuStd → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω))
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηb : ∀ x, |η x| ≤ 1) (k : Fin (Module.finrank ℝ EuN)) {N : ℝ}
    (hηd : ∀ x, |fderiv ℝ η x (EuclideanSpace.single k 1)| ≤ N)
    {ε : ℝ} (hε : 0 < ε) (h : ℝ) (hroom : cthickening |h| (tsupport η) ⊆ Ω) :
    let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
    let U := fun z => H1ComplDirichletToLp q v (x z)
    |∫ z in Ω, f z * H1ComplDirichletToLp q
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom v) (x z)| ≤
      ε * (∫ z, (η z * diffQuot k h (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k v) z)^2) +
      (2 * ε)⁻¹ * (∫ z in Ω, (f z)^2) +
      4 * ε * N^2 * (∫ z in tsupport η, (diffQuot k h U z)^2) := by
  intro x U
  have heq : (∫ z in Ω, f z * H1ComplDirichletToLp q
        (dirichletNirenbergTest q α hΩ hΩc hΩs hη hηc k h hroom v) (x z)) =
      ∫ z in Ω, f z * standardNirenbergTest k h η U z := by
    apply integral_congr_ae
    filter_upwards [dirichletNirenbergTest_chart_ae q α hΩ hΩc hΩs v hη hηc k h hroom] with z hz
    exact congrArg (fun r => f z * r) hz
  rw [heq]
  exact abs_integral_mul_standardNirenbergTest_chart_le q α hΩ hΩc hΩs v hf hη hηc hηb k hηd hε h hroom

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
