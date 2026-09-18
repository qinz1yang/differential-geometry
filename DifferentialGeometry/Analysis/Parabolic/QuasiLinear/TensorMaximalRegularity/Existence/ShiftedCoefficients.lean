import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.ShiftedParameterDependence
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Nemytskii.ShiftedTimeDependent
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.VectorParameterDependence
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

theorem exists_uniform_time_translated_vector_lipschitz
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
    {δ R ρ : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R) (hρ : 0 < ρ)
    (alpha : Metric.closedBall f₀ δ → ℝ →
      PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) → A)
    (reaction : Metric.closedBall f₀ δ → ℝ →
      PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) →
        PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (P : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)) →L[ℝ] V)
    (K L Cb M₀ CaParam CbParam : ℝ≥0)
    (halip : ∀ f t, t ∈ Icc (-ρ) ρ →
      LipschitzOnWith L (alpha f t) (Metric.closedBall 0 R))
    (haclose : ∀ f t, t ∈ Icc (-ρ) ρ → ∀ z, ‖z‖ ≤ R →
      ‖alpha f t z - q‖ ≤ (K : ℝ) * R)
    (hreaction : ∀ f t, t ∈ Icc (-ρ) ρ →
      LipschitzOnWith Cb (reaction f t) (Metric.closedBall 0 R))
    (hreaction_zero : ∀ f t, t ∈ Icc (-ρ) ρ →
      ‖reaction f t 0 - b₀‖ ≤ (M₀ : ℝ) * R)
    (hsmallA : (‖m‖ * K * ‖Q‖) * R ≤ 1 / 16)
    (hsmallC : (‖m‖ * L * ‖Q‖) * R ≤ 1 / 16)
    (haJoint : ∀ f, Continuous (fun p : Icc (-ρ) ρ × Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1))) R =>
        alpha f p.1 p.2))
    (hbJoint : ∀ f, Continuous (fun p : Icc (-ρ) ρ × Metric.closedBall
      (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1))) R =>
        reaction f p.1 p.2))
    (haParam : ∀ f k t, t ∈ Icc (-ρ) ρ → ∀ t', t' ∈ Icc (-ρ) ρ →
      ∀ z, ‖z‖ ≤ R →
      ‖alpha f t z - alpha k t' z‖ ≤
        CaParam * max |t - t'| ‖P ((f : _) - (k : _))‖)
    (hbParam : ∀ f k t, t ∈ Icc (-ρ) ρ → ∀ t', t' ∈ Icc (-ρ) ρ →
      ∀ z, ‖z‖ ≤ R →
      ‖reaction f t z - reaction k t' z‖ ≤
        CbParam * max |t - t'| ‖P ((f : _) - (k : _))‖) :
    let J := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (I := I) (M := M) (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
    let Params := Icc (-ρ / 4) (ρ / 4) × Metric.closedBall f₀ δ
    let Cq := ‖Q f₀‖ + ‖Q‖ * δ
    let A₀ := (‖q‖ + (K : ℝ) * R).toNNReal
    let Hparam : ℝ≥0 := max 1 ‖P‖₊
    let K₁ := ‖m‖₊ * CaParam * Hparam * ‖Q‖₊
    let K₀ := ‖m‖₊ * A₀ * ‖Q‖₊ + ‖m‖₊ * CaParam * Hparam * Cq.toNNReal +
      CbParam * Hparam
    let N := fun (p : Params) t
      (v : {v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)) |
      ‖J v‖ ≤ R}) => shiftedRemainder m Q J D d q
        (fun t z => alpha p.2 ((p.1 : ℝ) + t) z)
        (fun t z => reaction p.2 ((p.1 : ℝ) + t) z) p.2 t v
    let Bconst : ℝ≥0 := ‖m‖₊ * L * (‖Q f₀‖ + ‖Q‖ * δ).toNNReal + Cb + ‖d‖₊ * ‖D‖₊
    let D₀ := ‖m‖ * (‖q‖ + (K : ℝ) * R) * (‖Q f₀‖ + ‖Q‖ * δ) +
      ‖b₀‖ + (M₀ : ℝ) * R
    ∃ T₀ : ℝ,
      T₀ = min (ρ / 4) (min 1 (min (1 / (64 * ((Bconst : ℝ) + 1) ^ 2))
        (((R / 4) / (2 * (D₀ + 1))) ^ 2))) ∧
      0 < T₀ ∧ ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
      let κ := (‖m‖ * K * ‖Q‖) * R * (1 + T) +
        (Bconst : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
        2 * (‖m‖ * L * ‖Q‖) * (R / 4) * Real.sqrt (1 + T) * (1 + T)
      ∃ (u : Params → timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T)
        (gforce : Params → timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T),
        LipschitzWith
          ((K₁ * (1 + T).toNNReal * (R / 4).toNNReal + (Real.sqrt T).toNNReal * K₀) /
            (1 - κ).toNNReal) gforce ∧
        LipschitzWith
          (2 * ((K₁ * (1 + T).toNNReal * (R / 4).toNNReal + (Real.sqrt T).toNNReal * K₀) /
            (1 - κ).toNNReal)) u ∧
        ∀ f,
        let field := maximalRegularityDuhamelVectorField hT
          (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) (gforce f)
        u f = maximalRegularityDuhamelVectorMap hT
            (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) (gforce f) ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖J v‖ ≤ R}) ∧
          gforce f =ᵐ[timeMeasure T] (fun t => N f t (aeSetLift
            (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) ∈
              {v | ‖J v‖ ≤ R} by
                simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le) field t)) ∧
          (u f).toFunL2 =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
              (I := I) (M := M) (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).compLpL
                2 (timeMeasure T) field ∧
          timeH1.trace0 _ T (u f) = 0 ∧
          timeH1.timeDeriv _ T (u f) =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := I) (M := M) (g := g) (r := r) (s := s) a)).compLpL
                2 (timeMeasure T) field + gforce f ∧
          ‖gforce f‖ ≤ R / 4 := by
  intro J Params Cq A₀ Hparam K₁ K₀ N Bconst D₀
  let Aconst : ℝ≥0 := ‖m‖₊ * K * ‖Q‖₊
  let Cconst : ℝ≥0 := ‖m‖₊ * L * ‖Q‖₊
  have hD₀ : 0 ≤ D₀ := by dsimp only [D₀]; positivity
  have hCq : 0 ≤ Cq := by dsimp only [Cq]; positivity
  have hA₀ : 0 ≤ ‖q‖ + (K : ℝ) * R := by positivity
  have htime (p : Params) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (ρ / 4)) :
      (p.1 : ℝ) + t ∈ Icc (-ρ) ρ := by
    constructor <;> linarith [p.1.property.1, p.1.property.2, ht.1, ht.2]
  have huniform := shifted_remainder_uniform_tame_estimate m Q J D d q b₀ f₀ hδ hR.le
    alpha reaction (Icc (-ρ) ρ) K L Cb M₀ halip haclose hreaction hreaction_zero
  have hsmallA' : (Aconst : ℝ) * R ≤ 1 / 16 := by
    simpa only [Aconst, NNReal.coe_mul, coe_nnnorm] using hsmallA
  have hsmallC' : (Cconst : ℝ) * R ≤ 1 / 16 := by
    simpa only [Cconst, NNReal.coe_mul, coe_nnnorm] using hsmallC
  have hNmeas (p : Params) : TimeNemyMeas
      (show (0 : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) ∈
        {v | ‖J v‖ ≤ R} by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le)
      (N p) (ρ / 4) := by
    let shiftTime : Icc (0 : ℝ) (ρ / 4) → Icc (-ρ) ρ :=
      fun t => ⟨(p.1 : ℝ) + t, htime p t t.property⟩
    have hshiftTime : Continuous shiftTime :=
      (continuous_const.add continuous_subtype_val).subtype_mk _
    intro T hT f hf
    exact (shiftedRemainder_timeNemyMeas m Q J D d q
      (fun t z => alpha p.2 ((p.1 : ℝ) + t) z)
      (fun t z => reaction p.2 ((p.1 : ℝ) + t) z) (p.2 : _)
      (show (0 : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2))) ∈
        {v | ‖J v‖ ≤ R} by simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hR.le)
      (R := R) (τ := ρ / 4) (fun u => u.property)
      ((haJoint p.2).comp ((hshiftTime.comp continuous_fst).prodMk continuous_snd))
      ((hbJoint p.2).comp ((hshiftTime.comp continuous_fst).prodMk continuous_snd))).2 hT f hf
  have hparam (p k : Params) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (ρ / 4))
      (v : {v : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)) | ‖J v‖ ≤ R}) :
      ‖N p t v - N k t v‖ ≤
        ((K₁ : ℝ) * ‖(v : PiLp 2 (fun _ : ι => TensorHs g r s (a + 2)))‖ + K₀) *
          dist p k := by
    have hAf : ‖alpha p.2 ((p.1 : ℝ) + t) (J v)‖ ≤ A₀ := by
      dsimp only [A₀]
      rw [Real.coe_toNNReal _ hA₀]
      exact (norm_le_norm_add_norm_sub' _ q).trans
        (add_le_add le_rfl (haclose p.2 _ (htime p t ht) (J v) v.property))
    have ha := haParam p.2 k.2 ((p.1 : ℝ) + t) (htime p t ht)
      ((k.1 : ℝ) + t) (htime k t ht) (J v) v.property
    have hb := hbParam p.2 k.2 ((p.1 : ℝ) + t) (htime p t ht)
      ((k.1 : ℝ) + t) (htime k t ht) (J v) v.property
    rw [add_sub_add_right_eq_sub] at ha hb
    have h := shifted_remainder_time_parameter_sub_norm_le m Q J D d q P f₀
      alpha reaction p.2 k.2 (v : _) p.1 k.1 t A₀ CaParam CbParam hAf ha hb
    have hdist : dist ((p.1 : ℝ), p.2) ((k.1 : ℝ), k.2) = dist p k := rfl
    rw [hdist] at h
    simpa only [N, K₁, K₀, Hparam, NNReal.coe_add, NNReal.coe_mul, coe_nnnorm,
      NNReal.coe_max, NNReal.coe_one, Real.coe_toNNReal _ hCq, Cq] using h
  have hfamily := exists_lipschitz_time_partial_tame_vector g r s a hR
    (by positivity : 0 < ρ / 4) N hNmeas Aconst Bconst Cconst D₀ hD₀
    (fun p t ht => (huniform p.2 ((p.1 : ℝ) + t) (htime p t ht)).2)
    hsmallA' hsmallC'
    (fun p t ht u v =>
      (huniform p.2 ((p.1 : ℝ) + t) (htime p t ht)).1 u v u.property v.property)
    K₀ K₁ hparam
  simpa only [Aconst, Cconst, NNReal.coe_mul, coe_nnnorm] using hfamily


end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
