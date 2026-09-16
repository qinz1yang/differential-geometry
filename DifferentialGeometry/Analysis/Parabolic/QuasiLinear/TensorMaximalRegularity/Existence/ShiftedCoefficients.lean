import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.ShiftedTame
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.FiniteProduct

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance vectorTensorHsNormedSpace
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ) :
    NormedSpace ℝ (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) := inferInstance

theorem exists_uniform_time_shifted_vector
    {A : Type*} [SeminormedAddCommGroup A] [NormedSpace ℝ A]
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ)
    (m : A →L[ℝ] PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (Q : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (D : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (d : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a) →L[ℝ]
      PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (q : A) (b₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (f₀ : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)))
    {δ R τ : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R) (hτ : 0 < τ)
    (alpha : Metric.closedBall f₀ δ → ℝ →
      PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) → A)
    (reaction : Metric.closedBall f₀ δ → ℝ →
      PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) →
        PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (K L Cb M₀ : ℝ≥0)
    (halip : ∀ f t, t ∈ Icc (0 : ℝ) τ →
      LipschitzOnWith L (alpha f t) (Metric.closedBall 0 R))
    (haclose : ∀ f t, t ∈ Icc (0 : ℝ) τ → ∀ z, ‖z‖ ≤ R →
      ‖alpha f t z - q‖ ≤ (K : ℝ) * R)
    (hreaction : ∀ f t, t ∈ Icc (0 : ℝ) τ →
      LipschitzOnWith Cb (reaction f t) (Metric.closedBall 0 R))
    (hreaction_zero : ∀ f t, t ∈ Icc (0 : ℝ) τ →
      ‖reaction f t 0 - b₀‖ ≤ (M₀ : ℝ) * R)
    (hsmallA : (‖m‖ * K * ‖Q‖) * R ≤ 1 / 16)
    (hsmallC : (‖m‖ * L * ‖Q‖) * R ≤ 1 / 16) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (I := I) (M := M) (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
    let N := fun f t (v : {v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)) |
      ‖J v‖ ≤ R}) => shiftedRemainder m Q J D d q (alpha f) (reaction f) f t v
    let Bconst : ℝ≥0 := ‖m‖₊ * L * (‖Q f₀‖ + ‖Q‖ * δ).toNNReal + Cb + ‖d‖₊ * ‖D‖₊
    let D₀ := ‖m‖ * (‖q‖ + (K : ℝ) * R) * (‖Q f₀‖ + ‖Q‖ * δ) +
      ‖b₀‖ + (M₀ : ℝ) * R
    (∀ f, TimeNemyMeas
      (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) ∈
        {v | ‖J v‖ ≤ R} by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le)
      (N f) τ) →
    ∃ T₀ : ℝ,
      T₀ = min τ (min 1 (min (1 / (64 * ((Bconst : ℝ) + 1) ^ 2))
        (((R / 4) / (2 * (D₀ + 1))) ^ 2))) ∧
      0 < T₀ ∧ ∀ (f : Metric.closedBall f₀ δ) {T : ℝ} (hT : 0 < T), T ≤ T₀ →
      ∃ (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T)
        (gforce : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T),
        let field := maximalRegularityDuhamelVectorField hT
          (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) gforce
        u = maximalRegularityDuhamelVectorMap hT
            (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) gforce ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖J v‖ ≤ R}) ∧
          gforce =ᵐ[timeMeasure T] (fun t => N f t (aeSetLift
            (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) ∈
              {v | ‖J v‖ ≤ R} by
                simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le) field t)) ∧
          u.toFunL2 =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
              (I := I) (M := M) (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).compLpL
                2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := I) (M := M) (g := g) (r := r) (s := s) a)).compLpL
                2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ R / 4 := by
  intro J N Bconst D₀ hNmeas
  let Aconst : ℝ≥0 := ‖m‖₊ * K * ‖Q‖₊
  let Cconst : ℝ≥0 := ‖m‖₊ * L * ‖Q‖₊
  have hD₀ : 0 ≤ D₀ := by dsimp only [D₀]; positivity
  have huniform := shifted_remainder_uniform_tame_estimate m Q J D d q b₀ f₀ hδ hR.le
    alpha reaction (Icc (0 : ℝ) τ) K L Cb M₀ halip haclose hreaction hreaction_zero
  have hsmallA' : (Aconst : ℝ) * R ≤ 1 / 16 := by
    simpa only [Aconst, NNReal.coe_mul, coe_nnnorm] using hsmallA
  have hsmallC' : (Cconst : ℝ) * R ≤ 1 / 16 := by
    simpa only [Cconst, NNReal.coe_mul, coe_nnnorm] using hsmallC
  let T₀ := min τ (min 1 (min (1 / (64 * ((Bconst : ℝ) + 1) ^ 2))
    (((R / 4) / (2 * (D₀ + 1))) ^ 2)))
  have hT₀ : 0 < T₀ := by dsimp only [T₀]; positivity
  refine ⟨T₀, rfl, hT₀, ?_⟩
  intro f T hT hTT₀
  obtain ⟨Tf, hTf, _, hsol⟩ := time_partial_tame_vector g r s a hR hτ (N f) (hNmeas f)
    Aconst Bconst Cconst D₀ hD₀
    (fun t ht => (huniform f t ht).2) hsmallA' hsmallC'
    (fun t ht u v => (huniform f t ht).1 u v u.property v.property)
  apply hsol hT
  exact hTT₀.trans_eq hTf.symm

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
