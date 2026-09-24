import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.ScalarComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuous
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Product
import DifferentialGeometry.Topology.MetricSpace.DenseExtension
import DifferentialGeometry.Topology.ContinuousMap.CompactRange

noncomputable section
open Manifold Set
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M]
  [BoundarylessManifold 𝓘(ℝ, ℝ) M] [T2Space M] [SigmaCompactSpace M]

local notation "I" => 𝓘(ℝ, ℝ)

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by norm_num⟩

private theorem ccTensorToHs_sub
    (g : SmoothRiemannianMetric I M) (S T : SmoothCcTensor g 0 0) :
    ccTensorToHs g 0 1 (S - T) = ccTensorToHs g 0 1 S - ccTensorToHs g 0 1 T :=
  (ccToHsLin g 0 1).map_sub S T

private theorem scalar0_sub_norm_le_piLp
    (g : SmoothRiemannianMetric I M) (S T : ι → SmoothCcTensor g 0 0) (x : M) :
    ‖(fun i => TensorRSField.scalar0 (S i).toSection x) -
      (fun i => TensorRSField.scalar0 (T i).toSection x)‖ ≤
    ‖scalarHsToContinuous g‖ *
      ‖WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (S i)) -
        WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (T i))‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro i
  have hval := scalarHsToContinuous_apply_ccTensorToHs g (S i - T i) x
  have hbound := (ContinuousMap.norm_coe_le_norm
      (scalarHsToContinuous g (ccTensorToHs g 0
        ((Module.finrank ℝ ℝ / 2 + 1 : ℕ) : ℝ) (S i - T i))) x).trans
    ((scalarHsToContinuous g).le_opNorm (ccTensorToHs g 0
      ((Module.finrank ℝ ℝ / 2 + 1 : ℕ) : ℝ) (S i - T i)))
  rw [hval, SmoothCcTensor.toSection_sub, TensorRSField.scalar0_sub] at hbound
  have heq : ((Module.finrank ℝ ℝ / 2 + 1 : ℕ) : ℝ) = 1 := by norm_num
  have hnorm : ‖ccTensorToHs g 0 ((Module.finrank ℝ ℝ / 2 + 1 : ℕ) : ℝ)
      (S i - T i)‖ = ‖ccTensorToHs g 0 1 (S i - T i)‖ := by rw [heq]
  rw [hnorm, ccTensorToHs_sub] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le
    (WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (S i)) -
      WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (T i))) i) (norm_nonneg _))

theorem exists_norm_ccTensorToHs_scalarCompOn_sub_le_on_ball
    (g : SmoothRiemannianMetric I M) (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (c0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1)) (r : ℝ)
    (hRange : ∀ S : ι → SmoothCcTensor g 0 0,
      WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (S i)) ∈ Metric.ball c0 r →
      ∀ x, (fun i => TensorRSField.scalar0 (S i).toSection x) ∈ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S T : ι → SmoothCcTensor g 0 0)
      (hS : WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (S i)) ∈ Metric.ball c0 r)
      (hT : WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (T i)) ∈ Metric.ball c0 r),
      ‖ccTensorToHs g 0 1
        (SmoothCcTensor.scalarCompOn S F hF (fun x => hKU (hRange S hS x)) -
          SmoothCcTensor.scalarCompOn T F hF (fun x => hKU (hRange T hT x)))‖ ≤
        C * ‖WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (S i)) -
          WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (T i))‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_ccTensorToHs_scalarCompOn_sub_le_of_isCompact
    g F hF hU hK hKU
  let L := ‖scalarHsToContinuous g‖
  let R := max 0 (‖c0‖ + r)
  let n : ℝ := Fintype.card ι
  refine ⟨C * (n + L * (n * R)), mul_nonneg hC (by positivity), ?_⟩
  intro S T hS hT
  let eS := WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (S i))
  let eT := WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (T i))
  let d := ‖eS - eT‖
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hL : 0 ≤ L := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hsum : (∑ i, ‖ccTensorToHs g 0 1 (S i - T i)‖) ≤ n * d := by
    calc
      _ ≤ ∑ _i : ι, d := by
        apply Finset.sum_le_sum
        intro i _
        rw [ccTensorToHs_sub]
        exact PiLp.norm_apply_le (eS - eT) i
      _ = _ := by simp [n]
  have hnormT : ‖eT‖ ≤ R :=
    (norm_lt_of_mem_ball hT).le.trans (le_max_right _ _)
  have hsumT : (∑ i, ‖ccTensorToHs g 0 1 (T i)‖) ≤ n * R := by
    calc
      _ ≤ ∑ _i : ι, R := Finset.sum_le_sum
        (fun i _ => (PiLp.norm_apply_le eT i).trans hnormT)
      _ = _ := by simp [n]
  have hraw := hbound S T (hRange S hS) (hRange T hT) (L * d)
    (mul_nonneg hL hd) (fun x => scalar0_sub_norm_le_piLp g S T x)
  calc
    _ ≤ C * ((∑ i, ‖ccTensorToHs g 0 1 (S i - T i)‖) +
        (L * d) * ∑ i, ‖ccTensorToHs g 0 1 (T i)‖) := hraw
    _ ≤ C * (n * d + (L * d) * (n * R)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hsum (mul_le_mul_of_nonneg_left hsumT (mul_nonneg hL hd))) hC
    _ = (C * (n + L * (n * R))) * d := by ring

end DifferentialGeometry.Analysis.Spectral
noncomputable section
open scoped NNReal ENNReal
namespace DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold 𝓘(ℝ, ℝ) ∞ M] [CompactSpace M] [T2Space M] [SigmaCompactSpace M]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private local instance hsNorm (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) :
    NormedAddCommGroup (TensorHs g 0 0 1) := TensorHs.instNormedAddCommGroup
private local instance hsSpace (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) :
    NormedSpace ℝ (TensorHs g 0 0 1) :=
  (TensorHs.instInnerProductSpace (g := g) (r := 0) (s := 0) (σ := 1)).toNormedSpace
private local instance hsComplete (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M) :
    CompleteSpace (TensorHs g 0 0 1) := TensorHs.instCompleteSpace

theorem exists_scalarH1Pi_ball_range_subset
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1))
    {U : Set (ι → ℝ)} (hU : IsOpen U)
    (hu0 : range (scalarH1PiToContinuous g u0) ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ ∃ K : Set (ι → ℝ), IsCompact K ∧ K ⊆ U ∧
      ∀ u ∈ Metric.ball u0 r, range (scalarH1PiToContinuous g u) ⊆ K := by
  obtain ⟨K, hK, hKU, hball⟩ :=
    (scalarH1PiToContinuous g).continuous.continuousAt.exists_isCompact_range_subset hU hu0
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff.mp hball
  exact ⟨r, hr, K, hK, hKU, fun u hu => hb hu⟩


theorem exists_scalarH1_composition_on_ball
    [BoundarylessManifold 𝓘(ℝ, ℝ) M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) M)
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 1))
    (hu0 : range (scalarH1PiToContinuous g u0) ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ≥0,
      ∃ N : Metric.ball u0 r → TensorHs g 0 0 1,
        LipschitzWith C N ∧
        (∀ u ∈ Metric.ball u0 r, range (scalarH1PiToContinuous g u) ⊆ U) ∧
        (∀ u x, scalarH1ToContinuous g (N u) x = F (scalarH1PiToContinuous g u x)) ∧
        ∀ (S : ι → SmoothCcTensor g 0 0)
          (hS : WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (S i)) ∈ Metric.ball u0 r)
          (hSU : ∀ x, (fun i => TensorRSField.scalar0 (S i).toSection x) ∈ U),
          N ⟨WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (S i)), hS⟩ =
            ccTensorToHs g 0 1 (SmoothCcTensor.scalarCompOn S F hF hSU) := by
  obtain ⟨r, hr, K, hK, hKU, hrange⟩ := exists_scalarH1Pi_ball_range_subset g u0 hU hu0
  let e : (ι → SmoothCcTensor g 0 0) → PiLp 2 (fun _ : ι => TensorHs g 0 0 1) :=
    fun S => WithLp.toLp 2 (fun i => ccTensorToHs g 0 1 (S i))
  let B := Metric.ball u0 r
  have hRange (S : ι → SmoothCcTensor g 0 0) (hS : e S ∈ B) :
      ∀ x, (fun i => TensorRSField.scalar0 (S i).toSection x) ∈ K := by
    intro x
    rw [← scalarH1PiToContinuous_apply_ccTensorToHs]
    exact hrange (e S) hS (mem_range_self x)
  obtain ⟨C, hC, hbound⟩ := exists_norm_ccTensorToHs_scalarCompOn_sub_le_on_ball
    g F hF hU hK hKU u0 r hRange
  let f : (e ⁻¹' B) → TensorHs g 0 0 1 := fun S =>
    ccTensorToHs g 0 1 (SmoothCcTensor.scalarCompOn S.1 F hF
      (fun x => hKU (hRange S.1 S.2 x)))
  have hf (S T : e ⁻¹' B) : ‖f S - f T‖ ≤ C * ‖e S.1 - e T.1‖ := by
    have hb := hbound S.1 T.1 S.2 T.2
    change ‖ccToHsLin g 0 1 _‖ ≤ _ at hb
    rw [map_sub] at hb
    exact hb
  have he : DenseRange e := denseRange_ccTensorToHs_piLp g 0 (by norm_num) 2
  have heB : DenseRange (B.restrictPreimage e) := he.restrictPreimage_of_isOpen Metric.isOpen_ball
  have hfe (S T : e ⁻¹' B) :
      edist (f S) (f T) ≤ ENNReal.ofReal C * edist (B.restrictPreimage e S) (B.restrictPreimage e T) := by
    have hh := ENNReal.ofReal_le_ofReal (hf S T)
    simpa [edist_dist, Subtype.dist_eq, dist_eq_norm, ENNReal.ofReal_mul hC] using hh
  obtain ⟨N, hN, hNe⟩ := heB.exists_lipschitz_extension f hfe
  refine ⟨r, hr, Real.toNNReal C, N, hN, fun u hu => (hrange u hu).trans hKU, ?_, ?_⟩
  · intro u x
    have hleft : Continuous (fun v : B => scalarH1ToContinuous g (N v) x) := by
      exact ((ContinuousMap.evalCLM ℝ x).comp (scalarH1ToContinuous g)).continuous.comp hN.continuous
    have hright : Continuous (fun v : B => F (scalarH1PiToContinuous g v x)) := by
      apply hF.continuousOn.comp_continuous
      · exact ((ContinuousMap.evalCLM ℝ x).comp
          (scalarH1PiToContinuous g)).continuous.comp continuous_subtype_val
      · intro v
        exact hKU (hrange v v.2 (mem_range_self x))
    refine heB.induction_on u (isClosed_eq hleft hright) ?_
    intro S
    rw [hNe]
    change scalarH1ToContinuous g (ccTensorToHs g 0 1 _) x = _
    rw [scalarH1ToContinuous_apply_ccTensorToHs]
    rw [SmoothCcTensor.scalar0_scalarCompOn]
    change F _ = F (scalarH1PiToContinuous g (e S.1) x)
    rw [scalarH1PiToContinuous_apply_ccTensorToHs]
  · intro S hS hSU
    exact hNe ⟨S, hS⟩

end DifferentialGeometry.Analysis.Spectral
