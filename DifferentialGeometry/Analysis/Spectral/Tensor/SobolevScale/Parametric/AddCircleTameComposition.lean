import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.AddCircleLocalComposition
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.ScalarContinuousInjective
import DifferentialGeometry.Analysis.Integration.Lp.Lifting
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Separable

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff BigOperators Topology ENNReal

namespace AddCircle

open DifferentialGeometry
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {ι : Type*} [Fintype ι]

private local instance : NeZero (Module.finrank ℝ ℝ) := ⟨by simp⟩

theorem exists_scalarH2_composition_bound_of_h1_bound
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : PiLp 2 (fun _ : ι => TensorHs g 0 0 2),
      range (scalarH1PiToContinuous g (P u)) ⊆ K →
      (∑ i, ‖J (u i)‖) ≤ R →
      ∃ v : TensorHs g 0 0 2,
        ‖v‖ ≤ C * (1 + ∑ i, ‖u i‖) ∧
        ∀ x, scalarH1ToContinuous g (J v) x =
          F (scalarH1PiToContinuous g (P u) x) := by
  classical
  intro J P
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨C, hC, hc⟩ := exists_norm_ccTensorToHs_scalarCompOn_h2_le_of_h1_bound
    g F hF hU hL hLU (R + 1)
  refine ⟨C, hC, ?_⟩
  intro u hu hnu
  let A := (scalarH1PiToContinuous g).comp P
  have huU : range (A u) ⊆ U := hu.trans hKU
  obtain ⟨r, hr, Cn, N, hN, _, hEval, hSmooth⟩ :=
    exists_scalarH2_composition_on_ball g F hF hU u huU
  have hlow : Continuous (fun w : PiLp 2 (fun _ : ι => TensorHs g 0 0 2) =>
      ∑ i, ‖J (w i)‖) := by fun_prop
  have hnearNorm : ∀ᶠ w in 𝓝 u, (∑ i, ‖J (w i)‖) < R + 1 :=
    hlow.continuousAt.eventually (Iio_mem_nhds (by linarith))
  have hnearRange : ∀ᶠ w in 𝓝 u, range (A w) ⊆ interior L :=
    A.continuous.continuousAt.eventually
      (ContinuousMap.eventually_range_subset isOpen_interior (hu.trans hKL))
  obtain ⟨δ, hδ, hnear⟩ := Metric.eventually_nhds_iff.mp (hnearNorm.and hnearRange)
  let d := min r δ
  have hd : 0 < d := lt_min hr hδ
  let D := Metric.ball u d
  let incl : D → Metric.ball u r := fun w =>
    ⟨w.1, Metric.ball_subset_ball (min_le_left r δ) w.2⟩
  have hIncl : Continuous incl := by fun_prop
  let e : (ι → SmoothCcTensor g 0 0) → PiLp 2 (fun _ : ι => TensorHs g 0 0 2) :=
    fun S => WithLp.toLp 2 (fun i => ccTensorToHs g 0 2 (S i))
  have he : DenseRange e := denseRange_ccTensorToHs_piLp g 0 (by norm_num) 2
  have heD : DenseRange (D.restrictPreimage e) :=
    he.restrictPreimage_of_isOpen Metric.isOpen_ball
  have heval (S : ι → SmoothCcTensor g 0 0) (x : AddCircle (1 : ℝ)) :
      A (e S) x = fun i => TensorRSField.scalar0 (S i).toSection x := by
    ext i
    change scalarH1ToContinuous g (J (ccTensorToHs g 0 2 (S i))) x = _
    rw [tensorHsInclusion_ccTensorToHs, scalarH1ToContinuous_apply_ccTensorToHs]
  have hbound (w : D) : ‖N (incl w)‖ ≤ C * (1 + ∑ i, ‖w.1 i‖) := by
    refine heD.induction_on w (isClosed_le
      (hN.continuous.comp hIncl).norm (by fun_prop)) ?_
    intro S
    have hSδ : e S.1 ∈ Metric.ball u δ :=
      Metric.ball_subset_ball (min_le_right r δ) S.2
    have hSn := hnear hSδ
    have hSL : ∀ x, (fun i => TensorRSField.scalar0 (S.1 i).toSection x) ∈ L := by
      intro x
      rw [← heval]
      exact interior_subset (hSn.2 (mem_range_self x))
    have hSU : ∀ x, (fun i => TensorRSField.scalar0 (S.1 i).toSection x) ∈ U :=
      fun x => hLU (hSL x)
    have hlowS : (∑ i, ‖ccTensorToHs g 0 1 (S.1 i)‖) ≤ R + 1 := by
      simpa only [e, J, WithLp.ofLp_toLp, tensorHsInclusion_ccTensorToHs] using hSn.1.le
    have hNS : N (incl (D.restrictPreimage e S)) =
        ccTensorToHs g 0 2 (SmoothCcTensor.scalarCompOn S.1 F hF hSU) :=
      hSmooth S.1 _ hSU
    rw [hNS]
    exact hc S.1 hSL hlowS
  let uD : D := ⟨u, Metric.mem_ball_self hd⟩
  exact ⟨N (incl uD), hbound uD, fun x => hEval (incl uD) x⟩

theorem exists_lp_scalarH2_composition_of_h1_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (g : SmoothRiemannianMetric 𝓘(ℝ, ℝ) (AddCircle (1 : ℝ)))
    (F : (ι → ℝ) → ℝ) {U K : Set (ι → ℝ)}
    (hF : ContDiffOn ℝ ∞ F U) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {p : ℝ≥0∞} {u : Ω → PiLp 2 (fun _ : ι => TensorHs g 0 0 2)}
    (hu : MemLp u p μ) {a : Ω → TensorHs g 0 0 1}
    (ha : AEStronglyMeasurable a μ) {R : ℝ} :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (1 : ℝ) ≤ 2)
    let P := ContinuousLinearMap.piLpMap 2 (fun _ : ι => J)
    (∀ᵐ t ∂μ, range (scalarH1PiToContinuous g (P (u t))) ⊆ K) →
    (∀ᵐ t ∂μ, (∑ i, ‖J (u t i)‖) ≤ R) →
    (∀ᵐ t ∂μ, ∀ x, scalarH1ToContinuous g (a t) x =
      F (scalarH1PiToContinuous g (P (u t)) x)) →
    ∃ v : Lp (TensorHs g 0 0 2) p μ, (fun t => J (v t)) =ᵐ[μ] a := by
  classical
  intro J P hRange hBound hEval
  obtain ⟨C, hC, hc⟩ := exists_scalarH2_composition_bound_of_h1_bound
    g F hF hU hK hKU R
  let b : Ω → ℝ := fun t => C * (1 + (Fintype.card ι : ℝ) * ‖u t‖)
  have hb : MemLp b p μ := by
    have h := ((memLp_const (1 : ℝ)).add
      (hu.norm.const_mul (Fintype.card ι : ℝ))).const_mul C
    exact h
  have hLift : ∀ᵐ t ∂μ, ∃ v : TensorHs g 0 0 2, J v = a t ∧ ‖v‖ ≤ b t := by
    filter_upwards [hRange, hBound, hEval] with t hRt hBt hEt
    obtain ⟨v, hv, hve⟩ := hc (u t) hRt hBt
    refine ⟨v, ?_, ?_⟩
    · apply scalarH1ToContinuous_injective g
      exact ContinuousMap.ext (fun x => (hve x).trans (hEt x).symm)
    · have hsum : (∑ i, ‖u t i‖) ≤ (Fintype.card ι : ℝ) * ‖u t‖ := by
        calc
          _ ≤ ∑ _i : ι, ‖u t‖ := Finset.sum_le_sum (fun i _ => PiLp.norm_apply_le _ i)
          _ = _ := by simp
      exact hv.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum) hC)
  obtain ⟨v, hv, _⟩ := exists_lp_lift_of_ae_exists_norm_le J.continuous
    (tensorHsInclusion_injective (by norm_num : (1 : ℝ) ≤ 2)) ha hb hLift
  exact ⟨v, hv⟩

end AddCircle
