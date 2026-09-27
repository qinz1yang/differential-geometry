import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.ScalarComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothCompactSupportDense

open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]
variable {ι : Type*} [Fintype ι]

theorem exists_norm_ccTensorToHs_scalarCompOn_affine_le_of_isCompact
    (g : SmoothRiemannianMetric I M) (u0 u1 : ι → SmoothCcTensor g 0 0)
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (a b : ℝ)
    (hu : ∀ t ∈ Set.Icc a b, ∀ x,
      (fun i => TensorRSField.scalar0 (u0 i + t • u1 i).toSection x) ∈ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (ht : t ∈ Set.Icc a b),
      ‖ccTensorToHs g 0 1
        (SmoothCcTensor.scalarCompOn (fun i => u0 i + t • u1 i) F hF
          (fun x => hKU (hu t ht x)))‖ ≤ C := by
  classical
  by_cases hab : a ≤ b
  · have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
    let w (t : ℝ) := fun i => u0 i + t • u1 i
    let L := ccToHsLin g 0 1
    let P := SmoothCcTensor.scalarCompOn (w a) F hF (fun x => hKU (hu a ha x))
    let N : ℝ := ∑ i, ‖L (u1 i)‖
    let B : ℝ := ∑ i, ‖L (w a i)‖
    have hN : 0 ≤ N := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    obtain ⟨A, hA, hbound⟩ :=
      exists_norm_ccTensorToHs_scalarCompOn_sub_le_of_isCompact g F hF hU hK hKU
    refine ⟨‖L P‖ + A * ((b - a) * N + Metric.diam K * B), by positivity, ?_⟩
    intro t ht
    have hta : |t - a| ≤ b - a := by
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
      exact sub_le_sub_right ht.2 a
    have hsep (x : M) :
        ‖(fun i => TensorRSField.scalar0 (w t i).toSection x) -
          (fun i => TensorRSField.scalar0 (w a i).toSection x)‖ ≤ Metric.diam K := by
      rw [← dist_eq_norm]
      exact Metric.dist_le_diam_of_mem hK.isBounded (hu t ht x) (hu a ha x)
    have hd := hbound (w t) (w a) (hu t ht) (hu a ha)
      (Metric.diam K) Metric.diam_nonneg hsep
    have hdiff : (∑ i, ‖L (w t i - w a i)‖) ≤ (b - a) * N := by
      have heq (i : ι) : w t i - w a i = (t - a) • u1 i := by
        dsimp [w]
        rw [sub_smul]
        abel
      simp_rw [heq, map_smul, norm_smul, Real.norm_eq_abs]
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_right hta hN
    let Q := SmoothCcTensor.scalarCompOn (w t) F hF (fun x => hKU (hu t ht x))
    change ‖L Q‖ ≤ _
    have hd' : ‖L (Q - P)‖ ≤ A * ((b - a) * N + Metric.diam K * B) := by
      exact hd.trans (mul_le_mul_of_nonneg_left (add_le_add hdiff le_rfl) hA)
    calc
      ‖L Q‖ ≤ ‖L Q - L P‖ + ‖L P‖ := norm_le_norm_sub_add _ _
      _ = ‖L (Q - P)‖ + ‖L P‖ := by rw [map_sub]
      _ ≤ A * ((b - a) * N + Metric.diam K * B) + ‖L P‖ :=
        add_le_add hd' le_rfl
      _ = _ := add_comm _ _
  · refine ⟨0, le_rfl, fun t ht => ?_⟩
    exact (hab (ht.1.trans ht.2)).elim

end DifferentialGeometry.Analysis.Spectral
