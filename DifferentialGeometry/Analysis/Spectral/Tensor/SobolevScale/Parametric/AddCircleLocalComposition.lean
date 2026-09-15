import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.AddCircleComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.Product
import DifferentialGeometry.Topology.MetricSpace.DenseExtension
import DifferentialGeometry.Topology.ContinuousMap.CompactRange

noncomputable section
open Set
open scoped Manifold ContDiff BigOperators NNReal ENNReal

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]
private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

private theorem exists_norm_ccTensorToHs_scalarCompOn_sub_le_on_ball
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (c0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1))) (r : ℝ)
    (hRange : ∀ S : ι → SmoothCcTensor g 0 0,
      WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((k : ℝ) + 1) (S i)) ∈ Metric.ball c0 r →
      ∀ x, (fun i => TensorRSField.scalar0 (S i).toSection x) ∈ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S T : ι → SmoothCcTensor g 0 0)
      (hS : WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((k : ℝ) + 1) (S i)) ∈ Metric.ball c0 r)
      (hT : WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((k : ℝ) + 1) (T i)) ∈ Metric.ball c0 r),
      ‖ccTensorToHs g 0 ((k : ℝ) + 1)
        (SmoothCcTensor.scalarCompOn S F hF (fun x => hKU (hRange S hS x)) -
          SmoothCcTensor.scalarCompOn T F hF (fun x => hKU (hRange T hT x)))‖ ≤
        C * ‖WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((k : ℝ) + 1) (S i)) -
          WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((k : ℝ) + 1) (T i))‖ := by
  let n : ℝ := Fintype.card ι
  let R := max 0 (‖c0‖ + r)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  obtain ⟨C, hC, hbound⟩ := exists_norm_ccTensorToHs_scalarCompOn_sub_le_of_isCompact
    g k F hF hU hK hKU (n * R)
  refine ⟨C * n, mul_nonneg hC hn, ?_⟩
  intro S T hS hT
  let eS := WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((k : ℝ) + 1) (S i))
  let eT := WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((k : ℝ) + 1) (T i))
  have hsum (W : ι → SmoothCcTensor g 0 0)
      (hW : WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((k : ℝ) + 1) (W i)) ∈ Metric.ball c0 r) :
      (∑ i, ‖ccTensorToHs g 0 ((k : ℝ) + 1) (W i)‖) ≤ n * R := by
    have hw : ‖WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((k : ℝ) + 1) (W i))‖ ≤ R :=
      (norm_lt_of_mem_ball hW).le.trans (le_max_right _ _)
    calc
      _ ≤ ∑ _i : ι, R := Finset.sum_le_sum
        (fun i _ => (PiLp.norm_apply_le _ i).trans hw)
      _ = _ := by simp [n]
  have hd : (∑ i, ‖ccTensorToHs g 0 ((k : ℝ) + 1) (S i - T i)‖) ≤ n * ‖eS - eT‖ := by
    calc
      _ ≤ ∑ _i : ι, ‖eS - eT‖ := by
        apply Finset.sum_le_sum
        intro i _
        change ‖ccToHsLin g 0 ((k : ℝ) + 1) (S i - T i)‖ ≤ _
        rw [map_sub]
        exact PiLp.norm_apply_le (eS - eT) i
      _ = _ := by simp [n]
  exact (hbound S T (hRange S hS) (hRange T hT) (hsum S hS) (hsum T hT)).trans
    ((mul_le_mul_of_nonneg_left hd hC).trans_eq (mul_assoc _ _ _).symm)

private theorem exists_scalar_composition_on_ball_of_order
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ) {σ : ℝ} (hσ : σ = (k : ℝ) + 1)
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 σ))
    (hu0 : range (scalarH1PiToContinuous g
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by rw [hσ]; norm_num : (1 : ℝ) ≤ σ)) u0)) ⊆ U) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by rw [hσ]; norm_num : (1 : ℝ) ≤ σ)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ≥0,
      ∃ N : Metric.ball u0 r → TensorHs g 0 0 σ,
        LipschitzWith C N ∧
        (∀ u ∈ Metric.ball u0 r, range (scalarH1PiToContinuous g (P u)) ⊆ U) ∧
        (∀ u x, scalarH1ToContinuous g (J (N u)) x =
          F (scalarH1PiToContinuous g (P u) x)) ∧
        ∀ (S : ι → SmoothCcTensor g 0 0)
          (hS : WithLp.toLp 2 (fun i => ccTensorToHs g 0 σ (S i)) ∈ Metric.ball u0 r)
          (hSU : ∀ x, (fun i => TensorRSField.scalar0 (S i).toSection x) ∈ U),
          N ⟨WithLp.toLp 2 (fun i => ccTensorToHs g 0 σ (S i)), hS⟩ =
            ccTensorToHs g 0 σ (SmoothCcTensor.scalarCompOn S F hF hSU) := by
  subst σ
  intro J P
  let A := (scalarH1PiToContinuous g).comp P
  let B := (scalarH1ToContinuous g).comp J
  have ha (S : ι → SmoothCcTensor g 0 0) (x : AddCircle (1 : ℝ)) :
      A (WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((k : ℝ) + 1) (S i))) x =
        fun i => TensorRSField.scalar0 (S i).toSection x := by
    ext i
    change scalarH1ToContinuous g
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1) (ccTensorToHs g 0 ((k : ℝ) + 1) (S i))) x = _
    rw [tensorHsInclusion_ccTensorToHs, scalarH1ToContinuous_apply_ccTensorToHs]
  have hb (S : SmoothCcTensor g 0 0) (x : AddCircle (1 : ℝ)) :
      B (ccTensorToHs g 0 ((k : ℝ) + 1) S) x = TensorRSField.scalar0 S.toSection x := by
    change scalarH1ToContinuous g
      (tensorHsInclusion (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1) (ccTensorToHs g 0 ((k : ℝ) + 1) S)) x = _
    rw [tensorHsInclusion_ccTensorToHs, scalarH1ToContinuous_apply_ccTensorToHs]
  obtain ⟨K, hK, hKU, hball⟩ := A.continuous.continuousAt.exists_isCompact_range_subset hU hu0
  obtain ⟨r, hr, hrange⟩ := Metric.eventually_nhds_iff.mp hball
  let e : (ι → SmoothCcTensor g 0 0) → PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)) :=
    fun S => WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((k : ℝ) + 1) (S i))
  let D := Metric.ball u0 r
  have hRange (S : ι → SmoothCcTensor g 0 0) (hS : e S ∈ D) :
      ∀ x, (fun i => TensorRSField.scalar0 (S i).toSection x) ∈ K := by
    intro x
    rw [← ha]
    exact hrange hS (mem_range_self x)
  obtain ⟨C, hC, hbound⟩ := exists_norm_ccTensorToHs_scalarCompOn_sub_le_on_ball
    g k F hF hU hK hKU u0 r hRange
  let f : (e ⁻¹' D) → TensorHs g 0 0 ((k : ℝ) + 1) := fun S =>
    ccTensorToHs g 0 ((k : ℝ) + 1) (SmoothCcTensor.scalarCompOn S.1 F hF
      (fun x => hKU (hRange S.1 S.2 x)))
  have hf (S T : e ⁻¹' D) : ‖f S - f T‖ ≤ C * ‖e S.1 - e T.1‖ := by
    have hh := hbound S.1 T.1 S.2 T.2
    change ‖ccToHsLin g 0 ((k : ℝ) + 1) _‖ ≤ _ at hh
    rw [map_sub] at hh
    exact hh
  have he : DenseRange e := denseRange_ccTensorToHs_piLp g 0 (by positivity) 2
  have heD : DenseRange (D.restrictPreimage e) := he.restrictPreimage_of_isOpen Metric.isOpen_ball
  have hfe (S T : e ⁻¹' D) :
      edist (f S) (f T) ≤ ENNReal.ofReal C * edist (D.restrictPreimage e S) (D.restrictPreimage e T) := by
    have hh := ENNReal.ofReal_le_ofReal (hf S T)
    simpa [edist_dist, Subtype.dist_eq, dist_eq_norm, ENNReal.ofReal_mul hC] using hh
  obtain ⟨N, hN, hNe⟩ := heD.exists_lipschitz_extension f hfe
  refine ⟨r, hr, Real.toNNReal C, N, hN, fun u hu => (hrange hu).trans hKU, ?_, ?_⟩
  · intro u x
    have hleft : Continuous (fun v : D => B (N v) x) :=
      ((ContinuousMap.evalCLM ℝ x).comp B).continuous.comp hN.continuous
    have hright : Continuous (fun v : D => F (A v x)) := by
      apply hF.continuousOn.comp_continuous
      · exact ((ContinuousMap.evalCLM ℝ x).comp A).continuous.comp continuous_subtype_val
      · intro v
        exact hKU (hrange v.2 (mem_range_self x))
    change B (N u) x = F (A u x)
    refine heD.induction_on u (isClosed_eq hleft hright) ?_
    intro S
    rw [hNe]
    change B (ccTensorToHs g 0 ((k : ℝ) + 1) _) x = F (A (e S.1) x)
    rw [hb, SmoothCcTensor.scalar0_scalarCompOn, ha]
  · intro S hS hSU
    exact hNe ⟨S, hS⟩

theorem exists_scalarHs_composition_on_ball
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ))) (k : ℕ)
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 ((k : ℝ) + 1)))
    (hu0 : range (scalarH1PiToContinuous g
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)) u0)) ⊆ U) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ (k : ℝ) + 1)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ≥0,
      ∃ N : Metric.ball u0 r → TensorHs g 0 0 ((k : ℝ) + 1),
        LipschitzWith C N ∧
        (∀ u ∈ Metric.ball u0 r, range (scalarH1PiToContinuous g (P u)) ⊆ U) ∧
        (∀ u x, scalarH1ToContinuous g (J (N u)) x =
          F (scalarH1PiToContinuous g (P u) x)) ∧
        ∀ (S : ι → SmoothCcTensor g 0 0)
          (hS : WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((k : ℝ) + 1) (S i)) ∈ Metric.ball u0 r)
          (hSU : ∀ x, (fun i => TensorRSField.scalar0 (S i).toSection x) ∈ U),
          N ⟨WithLp.toLp 2 (fun i => ccTensorToHs g 0 ((k : ℝ) + 1) (S i)), hS⟩ =
            ccTensorToHs g 0 ((k : ℝ) + 1) (SmoothCcTensor.scalarCompOn S F hF hSU) := by
  exact exists_scalar_composition_on_ball_of_order g k rfl F hF hU u0 hu0

theorem exists_scalarH2_composition_on_ball
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (ι → ℝ) → ℝ) {U : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U)
    (u0 : PiLp 2 (fun _ : ι => TensorHs g 0 0 2))
    (hu0 : range (scalarH1PiToContinuous g
      (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
        tensorHsInclusion (g := g) (r := 0) (s := 0)
          (by norm_num : (1 : ℝ) ≤ 2)) u0)) ⊆ U) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ≥0,
      ∃ N : Metric.ball u0 r → TensorHs g 0 0 2,
        LipschitzWith C N ∧
        (∀ u ∈ Metric.ball u0 r, range (scalarH1PiToContinuous g (P u)) ⊆ U) ∧
        (∀ u x, scalarH1ToContinuous g (J (N u)) x =
          F (scalarH1PiToContinuous g (P u) x)) ∧
        ∀ (S : ι → SmoothCcTensor g 0 0)
          (hS : WithLp.toLp 2 (fun i => ccTensorToHs g 0 2 (S i)) ∈ Metric.ball u0 r)
          (hSU : ∀ x, (fun i => TensorRSField.scalar0 (S i).toSection x) ∈ U),
          N ⟨WithLp.toLp 2 (fun i => ccTensorToHs g 0 2 (S i)), hS⟩ =
            ccTensorToHs g 0 2 (SmoothCcTensor.scalarCompOn S F hF hSU) := by
  exact exists_scalar_composition_on_ball_of_order g 1 (by norm_num : (2 : ℝ) = ((1 : ℕ) : ℝ) + 1)
    F hF hU u0 hu0

end AddCircle
