import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergIntegration
import DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.NormBounds

noncomputable section

open Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Laplacian
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

theorem exists_integral_cutoff_sq_diffQuot_chartInverse_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω' Ω'' : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {η : EuStd → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω'') {r : ℝ} (hr : 0 < r)
    (hroom : Metric.cthickening r (closure Ω'') ⊆ Ω') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
      (_ : |h| ≤ r) (u : H1ComplDirichlet q),
      let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
      (∫ z, η z ^ 2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun z => H1ComplDirichletToLp q u (x z)) z) ^ 2) ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨A, hηbound⟩ := hηc.exists_bound_of_continuous hη
  have hA : 0 ≤ A := (norm_nonneg (η 0)).trans (hηbound 0)
  let D := fun k => dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k
  let K : ℝ := ∑ k, ‖D k‖
  refine ⟨A ^ 2 * K ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
  intro k h hh u
  let U := fun z => H1ComplDirichletToLp q u
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  have hu : MemLp U 2 (volume.restrict Ω) :=
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u).memLp
  have hd := hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k u
  have hb := integral_cutoff_sq_diffQuot_le_eLpNorm_weakPartial_sq hΩ hΩ' hΩ''
    hΩ'c hΩ'Ω hΩ''c hu (Lp.memLp (D k u)) hη hηc hηs hA
    (fun x => by simpa only [Real.norm_eq_abs] using hηbound x) k hd hr hroom hh
  have hnorm : (eLpNorm (D k u) 2 (volume.restrict Ω')).toReal ≤ K * ‖u‖ := by
    calc
      _ ≤ (eLpNorm (D k u) 2 (volume.restrict Ω)).toReal :=
        ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_mono_measure _
          (Measure.restrict_mono (subset_closure.trans hΩ'Ω) le_rfl))
      _ = ‖D k u‖ := (Lp.norm_def _).symm
      _ ≤ ‖D k‖ * ‖u‖ := (D k).le_opNorm u
      _ ≤ K * ‖u‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact Finset.single_le_sum (fun i _ => norm_nonneg (D i)) (Finset.mem_univ k)
  change (∫ z, η z ^ 2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h U z) ^ 2) ≤ _
  calc
    _ ≤ A ^ 2 * (eLpNorm (D k u) 2 (volume.restrict Ω')).toReal ^ 2 := hb
    _ ≤ A ^ 2 * (K * ‖u‖) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg hnorm 2) (sq_nonneg _)
    _ = _ := by ring

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
