import DifferentialGeometry.Analysis.FunctionalAnalysis.ContinuousLinearMap.ClosedBall
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.Existence.ShiftedCoefficients

noncomputable section

open MeasureTheory Set Filter
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.Analysis.Parabolic.QuasiLinear

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

theorem coefficient_bounds_precomp
    {P X V A : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup V] [NormedSpace ℝ V] [SeminormedAddCommGroup A]
    (J : X →L[ℝ] V) {R ρ : ℝ} (hJρ : ‖J‖ * ρ ≤ R) (timeSet : Set ℝ)
    (a : P → ℝ → Metric.closedBall (0 : V) R → A) (alpha : P → ℝ → X → A)
    (q : A) (Ca : ℝ≥0)
    (ha : ∀ p, LipschitzWith Ca
      (fun z : ℝ × Metric.closedBall (0 : V) R => a p z.1 z.2))
    (hclose : ∀ p t, t ∈ timeSet → ∀ z, ‖a p t z - q‖ ≤ (Ca : ℝ) * (2 * R))
    (halpha : ∀ p t, t ∈ timeSet → ∀ z : Metric.closedBall (0 : X) ρ,
      alpha p t z = a p t (J.closedBallMap hJρ z)) :
    (∀ p t, t ∈ timeSet →
      LipschitzOnWith (Ca * ‖J‖₊) (alpha p t) (Metric.closedBall 0 ρ)) ∧
    (∀ p t, t ∈ timeSet → ∀ z, ‖z‖ ≤ ρ →
      ‖alpha p t z - q‖ ≤ (Ca : ℝ) * (2 * R)) ∧
    (∀ p, Continuous
      (fun z : timeSet × Metric.closedBall (0 : X) ρ => alpha p z.1 z.2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    rw [halpha p t ht ⟨z, hz⟩, halpha p t ht ⟨w, hw⟩]
    have h := ((ha p).norm_sub_time_precomp_closedBall J hJρ t ⟨z, hz⟩ ⟨w, hw⟩).trans
      (mul_le_mul_of_nonneg_left (J.le_opNorm (z - w)) Ca.coe_nonneg)
    simpa only [NNReal.coe_mul, coe_nnnorm, dist_eq_norm, mul_assoc] using h
  · intro p t ht z hz
    have hz' : z ∈ Metric.closedBall (0 : X) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [halpha p t ht ⟨z, hz'⟩]
    exact hclose p t ht _
  · intro p
    have hc : Continuous (fun z : timeSet × Metric.closedBall (0 : X) ρ =>
        a p z.1 (J.closedBallMap hJρ z.2)) :=
      ((ha p).prod_precomp_closedBall J hJρ).continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    apply hc.congr
    intro z
    exact (halpha p z.1 z.1.property z.2).symm

theorem precomp_radius_smallness
    (m Q J Ca : ℝ≥0) {R : ℝ} (hR : 0 < R)
    (hCa : (Ca : ℝ) * R ≤ 1 / (32 * ((m : ℝ) * Q + 1))) :
    let ρ := R / (1 + (J : ℝ))
    0 < ρ ∧ ρ ≤ R ∧ (J : ℝ) * ρ ≤ R ∧
      ((m : ℝ) * (2 * Ca * (1 + (J : ℝ))) * Q) * ρ ≤ 1 / 16 ∧
      ((m : ℝ) * (Ca * J) * Q) * ρ ≤ 1 / 16 := by
  intro ρ
  have hJ : 0 < 1 + (J : ℝ) := by positivity
  have hρ : 0 < ρ := div_pos hR hJ
  have hρeq : (1 + (J : ℝ)) * ρ = R := by
    dsimp only [ρ]
    field_simp
  have hρR : ρ ≤ R := by nlinarith [J.coe_nonneg]
  have hJρ : (J : ℝ) * ρ ≤ R := by nlinarith
  have hden : 0 < 32 * ((m : ℝ) * Q + 1) := by positivity
  have hscaled : (Ca : ℝ) * R * (32 * ((m : ℝ) * Q + 1)) ≤ 1 :=
    (le_div_iff₀ hden).mp hCa
  have hmQ : 0 ≤ (m : ℝ) * Q := mul_nonneg m.coe_nonneg Q.coe_nonneg
  have hbound : 2 * (m : ℝ) * Q * (Ca : ℝ) * R ≤ 1 / 16 := by
    nlinarith [mul_nonneg Ca.coe_nonneg hR.le]
  have hA : ((m : ℝ) * (2 * Ca * (1 + (J : ℝ))) * Q) * ρ ≤ 1 / 16 := by
    calc
      _ = 2 * (m : ℝ) * Q * (Ca : ℝ) * ((1 + (J : ℝ)) * ρ) := by ring
      _ ≤ 1 / 16 := by rw [hρeq]; exact hbound
  refine ⟨hρ, hρR, hJρ, hA, ?_⟩
  calc
    ((m : ℝ) * (Ca * J) * Q) * ρ = (m : ℝ) * Ca * Q * ((J : ℝ) * ρ) := by ring
    _ ≤ (m : ℝ) * Ca * Q * R := by
      gcongr
    _ ≤ 2 * (m : ℝ) * Q * Ca * R := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg m.coe_nonneg Ca.coe_nonneg)
        Q.coe_nonneg) hR.le]
    _ ≤ 1 / 16 := hbound

variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance vectorTensorHsNormedSpace
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (a : ℝ) :
    NormedSpace ℝ (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) := inferInstance

theorem exists_uniform_time_precomposed_vector
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
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (J : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) →L[ℝ] V)
    {δ R ρ : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R)
    (hρeq : ρ = R / (1 + ‖J‖)) :
    let hJρ : ‖J‖ * ρ ≤ R := by
      rw [hρeq, ← mul_div_assoc]
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith [hR.le])
    ∀ (alpha₀ : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → A)
    (reaction₀ : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (alpha : Metric.closedBall f₀ δ → ℝ → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) → A)
    (reaction : Metric.closedBall f₀ δ → ℝ → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (Ca Cb : ℝ≥0)
    (ha : ∀ f, LipschitzWith Ca
      (fun z : ℝ × Metric.closedBall (0 : V) R => alpha₀ f z.1 z.2))
    (hb : ∀ f, LipschitzWith Cb
      (fun z : ℝ × Metric.closedBall (0 : V) R => reaction₀ f z.1 z.2))
    (haclose : ∀ f t, t ∈ Icc (0 : ℝ) R → ∀ z,
      ‖alpha₀ f t z - q‖ ≤ (Ca : ℝ) * (2 * R))
    (hbclose : ∀ f t, t ∈ Icc (0 : ℝ) R → ∀ z,
      ‖reaction₀ f t z - b₀‖ ≤ (Cb : ℝ) * (2 * R))
    (halpha : ∀ f t, t ∈ Icc (0 : ℝ) ρ → ∀ z : Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1))) ρ,
      alpha f t z = alpha₀ f t (J.closedBallMap hJρ z))
    (hbeta : ∀ f t, t ∈ Icc (0 : ℝ) ρ → ∀ z : Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1))) ρ,
      reaction f t z = reaction₀ f t (J.closedBallMap hJρ z))
    (hCa : (Ca : ℝ) * R ≤ 1 / (32 * (‖m‖ * ‖Q‖ + 1))),
    let hρ : 0 < ρ := by rw [hρeq]; exact div_pos hR (by positivity)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (I := I) (M := M) (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
    let N := fun f t (v : {v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)) |
      ‖K v‖ ≤ ρ}) => shiftedRemainder m Q K D d q (alpha f) (reaction f) f t v
    let Bconst : ℝ≥0 := ‖m‖₊ * (Ca * ‖J‖₊) * (‖Q f₀‖ + ‖Q‖ * δ).toNNReal + (Cb * ‖J‖₊) + ‖d‖₊ * ‖D‖₊
    let D₀ := ‖m‖ * (‖q‖ + ((2 * Ca * (1 + ‖J‖₊)) : ℝ) * ρ) * (‖Q f₀‖ + ‖Q‖ * δ) +
      ‖b₀‖ + ((2 * Cb * (1 + ‖J‖₊)) : ℝ) * ρ
    ∃ T₀ : ℝ,
      T₀ = min ρ (min 1 (min (1 / (64 * ((Bconst : ℝ) + 1) ^ 2))
        (((ρ / 4) / (2 * (D₀ + 1))) ^ 2))) ∧
      0 < T₀ ∧ T₀ ≤ ρ ∧ ∀ (f : Metric.closedBall f₀ δ) {T : ℝ} (hT : 0 < T), T ≤ T₀ →
      ∃ (u : timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T)
        (gforce : timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T),
        let field := maximalRegularityDuhamelVectorField hT
          (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) gforce
        u = maximalRegularityDuhamelVectorMap hT
            (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) gforce ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖K v‖ ≤ ρ}) ∧
          gforce =ᵐ[timeMeasure T] (fun t => N f t (aeSetLift
            (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) ∈
              {v | ‖K v‖ ≤ ρ} by
                simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hρ.le) field t)) ∧
          u.toFunL2 =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
              (I := I) (M := M) (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).compLpL
                2 (timeMeasure T) field ∧
          timeH1.trace0 _ T u = 0 ∧
          timeH1.timeDeriv _ T u =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := I) (M := M) (g := g) (r := r) (s := s) a)).compLpL
                2 (timeMeasure T) field + gforce ∧
          ‖gforce‖ ≤ ρ / 4 := by
  intro hJρ alpha₀ reaction₀ alpha reaction Ca Cb ha hb haclose hbclose halpha hbeta hCa hρ K N Bconst D₀
  have hden : 0 < 1 + ‖J‖ := by positivity
  have hρmul : (1 + ‖J‖) * ρ = R := by
    rw [hρeq]
    field_simp [ne_of_gt hden]
  have hρR : ρ ≤ R := by nlinarith [norm_nonneg J]
  have hboundsA := coefficient_bounds_precomp J hJρ (Icc (0 : ℝ) ρ) alpha₀ alpha q Ca ha
    (fun f t ht z => haclose f t ⟨ht.1, ht.2.trans hρR⟩ z) halpha
  have hboundsB := coefficient_bounds_precomp J hJρ (Icc (0 : ℝ) ρ) reaction₀ reaction b₀ Cb hb
    (fun f t ht z => hbclose f t ⟨ht.1, ht.2.trans hρR⟩ z) hbeta
  have hcloseA : ∀ f t, t ∈ Icc (0 : ℝ) ρ → ∀ z, ‖z‖ ≤ ρ →
      ‖alpha f t z - q‖ ≤ (2 * (Ca : ℝ) * (1 + ‖J‖)) * ρ := by
    intro f t ht z hz
    calc
      _ ≤ (Ca : ℝ) * (2 * R) := hboundsA.2.1 f t ht z hz
      _ = (2 * (Ca : ℝ) * (1 + ‖J‖)) * ρ := by rw [← hρmul]; ring
  have hcloseB : ∀ f t, t ∈ Icc (0 : ℝ) ρ → ∀ z, ‖z‖ ≤ ρ →
      ‖reaction f t z - b₀‖ ≤ (2 * (Cb : ℝ) * (1 + ‖J‖)) * ρ := by
    intro f t ht z hz
    calc
      _ ≤ (Cb : ℝ) * (2 * R) := hboundsB.2.1 f t ht z hz
      _ = (2 * (Cb : ℝ) * (1 + ‖J‖)) * ρ := by rw [← hρmul]; ring
  have hsmall := precomp_radius_smallness ‖m‖₊ ‖Q‖₊ ‖J‖₊ Ca hR hCa
  simp only [coe_nnnorm] at hsmall
  rw [← hρeq] at hsmall
  have hmeas : ∀ f, TimeNemyMeas
      (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) ∈ {v | ‖K v‖ ≤ ρ} by
        simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hρ.le) (N f) ρ := by
    intro f
    exact (DifferentialGeometry.Analysis.Parabolic.shiftedRemainder_timeNemyMeas
      m Q K D d q (alpha f) (reaction f) f
      (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) ∈ {v | ‖K v‖ ≤ ρ} by
        simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hρ.le)
      (fun v => v.property) (hboundsA.2.2 f) (hboundsB.2.2 f)).2
  obtain ⟨T₀, hT₀eq, hT₀, hsol⟩ :=
    exists_uniform_time_shifted_vector g r s a m Q D d q b₀ f₀ hδ hρ hρ
      alpha reaction (2 * Ca * (1 + ‖J‖₊)) (Ca * ‖J‖₊) (Cb * ‖J‖₊)
      (2 * Cb * (1 + ‖J‖₊)) hboundsA.1
      (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one,
        coe_nnnorm] using hcloseA) hboundsB.1
      (fun f t ht => by
        simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one,
          coe_nnnorm] using hcloseB f t ht 0 (by simpa using hρ.le))
      (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one,
        coe_nnnorm] using hsmall.2.2.2.1)
      (by simpa only [NNReal.coe_mul, coe_nnnorm] using hsmall.2.2.2.2) hmeas
  refine ⟨T₀, hT₀eq, hT₀, ?_, hsol⟩
  rw [hT₀eq]
  exact min_le_left _ _

theorem exists_uniform_time_precomposed_translated_vector_lipschitz
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
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (J : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) →L[ℝ] V)
    {δ R ρ : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R)
    (hρeq : ρ = R / (1 + ‖J‖)) :
    let hJρ : ‖J‖ * ρ ≤ R := by
      rw [hρeq, ← mul_div_assoc]
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith [hR.le])
    ∀ (alpha₀ : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → A)
    (reaction₀ : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (alpha : Metric.closedBall f₀ δ → ℝ → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) → A)
    (reaction : Metric.closedBall f₀ δ → ℝ → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (P : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)) →L[ℝ] V)
    (Ca Cb : ℝ≥0)
    (ha : ∀ f, LipschitzWith Ca
      (fun z : ℝ × Metric.closedBall (0 : V) R => alpha₀ f z.1 z.2))
    (hb : ∀ f, LipschitzWith Cb
      (fun z : ℝ × Metric.closedBall (0 : V) R => reaction₀ f z.1 z.2))
    (haclose : ∀ f t, t ∈ Icc (-R) R → ∀ z,
      ‖alpha₀ f t z - q‖ ≤ (Ca : ℝ) * (2 * R))
    (hbclose : ∀ f t, t ∈ Icc (-R) R → ∀ z,
      ‖reaction₀ f t z - b₀‖ ≤ (Cb : ℝ) * (2 * R))
    (halpha : ∀ f t, t ∈ Icc (-ρ) ρ → ∀ z : Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1))) ρ,
      alpha f t z = alpha₀ f t (J.closedBallMap hJρ z))
    (hbeta : ∀ f t, t ∈ Icc (-ρ) ρ → ∀ z : Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1))) ρ,
      reaction f t z = reaction₀ f t (J.closedBallMap hJρ z))
    (haparam : ∀ f k t s z, ‖alpha₀ f t z - alpha₀ k s z‖ ≤
      (Ca : ℝ) * max |t - s| ‖P (f.val - k.val)‖)
    (hbparam : ∀ f k t s z, ‖reaction₀ f t z - reaction₀ k s z‖ ≤
      (Cb : ℝ) * max |t - s| ‖P (f.val - k.val)‖)
    (hCa : (Ca : ℝ) * R ≤ 1 / (32 * (‖m‖ * ‖Q‖ + 1))),
    let hρ : 0 < ρ := by rw [hρeq]; exact div_pos hR (by positivity)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (I := I) (M := M) (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
    let Params := Icc (-ρ / 4) (ρ / 4) × Metric.closedBall f₀ δ
    let Cq := ‖Q f₀‖ + ‖Q‖ * δ
    let A₀ := (‖q‖ + ((2 * Ca * (1 + ‖J‖₊)) : ℝ) * ρ).toNNReal
    let Hparam : ℝ≥0 := max 1 ‖P‖₊
    let K₁ := ‖m‖₊ * Ca * Hparam * ‖Q‖₊
    let K₀ := ‖m‖₊ * A₀ * ‖Q‖₊ + ‖m‖₊ * Ca * Hparam * Cq.toNNReal +
      Cb * Hparam
    let N := fun (p : Params) t
      (v : {v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)) |
      ‖K v‖ ≤ ρ}) => shiftedRemainder m Q K D d q
        (fun t z => alpha p.2 ((p.1 : ℝ) + t) z)
        (fun t z => reaction p.2 ((p.1 : ℝ) + t) z) p.2 t v
    let Bconst : ℝ≥0 := ‖m‖₊ * (Ca * ‖J‖₊) * (‖Q f₀‖ + ‖Q‖ * δ).toNNReal + (Cb * ‖J‖₊) + ‖d‖₊ * ‖D‖₊
    let D₀ := ‖m‖ * (‖q‖ + ((2 * Ca * (1 + ‖J‖₊)) : ℝ) * ρ) * (‖Q f₀‖ + ‖Q‖ * δ) +
      ‖b₀‖ + ((2 * Cb * (1 + ‖J‖₊)) : ℝ) * ρ
    ∃ T₀ : ℝ,
      T₀ = min (ρ / 4) (min 1 (min (1 / (64 * ((Bconst : ℝ) + 1) ^ 2))
        (((ρ / 4) / (2 * (D₀ + 1))) ^ 2))) ∧
      0 < T₀ ∧ T₀ ≤ ρ / 4 ∧ ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
      let κ := (‖m‖ * (2 * Ca * (1 + ‖J‖₊)) * ‖Q‖) * ρ * (1 + T) +
        (Bconst : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
        2 * (‖m‖ * (Ca * ‖J‖₊) * ‖Q‖) * (ρ / 4) * Real.sqrt (1 + T) * (1 + T)
      ∃ (u : Params → timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T)
        (gforce : Params → timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T),
        LipschitzWith
          ((K₁ * (1 + T).toNNReal * (ρ / 4).toNNReal + (Real.sqrt T).toNNReal * K₀) /
            (1 - κ).toNNReal) gforce ∧
        LipschitzWith
          (2 * ((K₁ * (1 + T).toNNReal * (ρ / 4).toNNReal + (Real.sqrt T).toNNReal * K₀) /
            (1 - κ).toNNReal)) u ∧
        ∀ f,
        let field := maximalRegularityDuhamelVectorField hT
          (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) (gforce f)
        u f = maximalRegularityDuhamelVectorMap hT
            (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) (gforce f) ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖K v‖ ≤ ρ}) ∧
          gforce f =ᵐ[timeMeasure T] (fun t => N f t (aeSetLift
            (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) ∈
              {v | ‖K v‖ ≤ ρ} by
                simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hρ.le) field t)) ∧
          (u f).toFunL2 =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
              (I := I) (M := M) (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).compLpL
                2 (timeMeasure T) field ∧
          timeH1.trace0 _ T (u f) = 0 ∧
          timeH1.timeDeriv _ T (u f) =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := I) (M := M) (g := g) (r := r) (s := s) a)).compLpL
                2 (timeMeasure T) field + gforce f ∧
          ‖gforce f‖ ≤ ρ / 4 := by
  intro hJρ alpha₀ reaction₀ alpha reaction P Ca Cb ha hb haclose hbclose halpha hbeta haparam hbparam hCa hρ K Params Cq A₀ Hparam K₁ K₀ N Bconst D₀
  have hden : 0 < 1 + ‖J‖ := by positivity
  have hρmul : (1 + ‖J‖) * ρ = R := by
    rw [hρeq]
    field_simp [ne_of_gt hden]
  have hρR : ρ ≤ R := by nlinarith [norm_nonneg J]
  have hboundsA := coefficient_bounds_precomp J hJρ (Icc (-ρ) ρ) alpha₀ alpha q Ca ha
    (fun f t ht z => haclose f t ⟨(neg_le_neg hρR).trans ht.1, ht.2.trans hρR⟩ z) halpha
  have hboundsB := coefficient_bounds_precomp J hJρ (Icc (-ρ) ρ) reaction₀ reaction b₀ Cb hb
    (fun f t ht z => hbclose f t ⟨(neg_le_neg hρR).trans ht.1, ht.2.trans hρR⟩ z) hbeta
  have hcloseA : ∀ f t, t ∈ Icc (-ρ) ρ → ∀ z, ‖z‖ ≤ ρ →
      ‖alpha f t z - q‖ ≤ (2 * (Ca : ℝ) * (1 + ‖J‖)) * ρ := by
    intro f t ht z hz
    calc
      _ ≤ (Ca : ℝ) * (2 * R) := hboundsA.2.1 f t ht z hz
      _ = (2 * (Ca : ℝ) * (1 + ‖J‖)) * ρ := by rw [← hρmul]; ring
  have hcloseB : ∀ f t, t ∈ Icc (-ρ) ρ → ∀ z, ‖z‖ ≤ ρ →
      ‖reaction f t z - b₀‖ ≤ (2 * (Cb : ℝ) * (1 + ‖J‖)) * ρ := by
    intro f t ht z hz
    calc
      _ ≤ (Cb : ℝ) * (2 * R) := hboundsB.2.1 f t ht z hz
      _ = (2 * (Cb : ℝ) * (1 + ‖J‖)) * ρ := by rw [← hρmul]; ring
  have hsmall := precomp_radius_smallness ‖m‖₊ ‖Q‖₊ ‖J‖₊ Ca hR hCa
  simp only [coe_nnnorm] at hsmall
  rw [← hρeq] at hsmall
  have haparam' : ∀ f k t, t ∈ Icc (-ρ) ρ → ∀ t', t' ∈ Icc (-ρ) ρ →
      ∀ z, ‖z‖ ≤ ρ → ‖alpha f t z - alpha k t' z‖ ≤
        (Ca : ℝ) * max |t - t'| ‖P (f.val - k.val)‖ := by
    intro f k t ht t' ht' z hz
    have hz' : z ∈ Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1))) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [halpha f t ht ⟨z, hz'⟩, halpha k t' ht' ⟨z, hz'⟩]
    exact haparam f k t t' _
  have hbparam' : ∀ f k t, t ∈ Icc (-ρ) ρ → ∀ t', t' ∈ Icc (-ρ) ρ →
      ∀ z, ‖z‖ ≤ ρ → ‖reaction f t z - reaction k t' z‖ ≤
        (Cb : ℝ) * max |t - t'| ‖P (f.val - k.val)‖ := by
    intro f k t ht t' ht' z hz
    have hz' : z ∈ Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1))) ρ := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [hbeta f t ht ⟨z, hz'⟩, hbeta k t' ht' ⟨z, hz'⟩]
    exact hbparam f k t t' _
  obtain ⟨T₀, hT₀eq, hT₀, hsol⟩ :=
    exists_uniform_time_translated_vector_lipschitz g r s a m Q D d q b₀ f₀ hδ hρ hρ
      alpha reaction P (2 * Ca * (1 + ‖J‖₊)) (Ca * ‖J‖₊) (Cb * ‖J‖₊)
      (2 * Cb * (1 + ‖J‖₊)) Ca Cb hboundsA.1
      (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one,
        coe_nnnorm] using hcloseA) hboundsB.1
      (fun f t ht => by
        simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one,
          coe_nnnorm] using hcloseB f t ht 0 (by simpa using hρ.le))
      (by simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat, NNReal.coe_one,
        coe_nnnorm] using hsmall.2.2.2.1)
      (by simpa only [NNReal.coe_mul, coe_nnnorm] using hsmall.2.2.2.2) hboundsA.2.2 hboundsB.2.2 haparam' hbparam'
  refine ⟨T₀, hT₀eq, hT₀, ?_, hsol⟩
  rw [hT₀eq]
  exact min_le_left _ _

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear

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

attribute [local instance] vectorTensorHsNormedSpace

theorem exists_uniform_time_precomposed_translated_vector_solutions_lipschitz
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
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (J : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) →L[ℝ] V)
    {δ R ρ : ℝ} (hδ : 0 ≤ δ) (hR : 0 < R)
    (hρeq : ρ = R / (1 + ‖J‖)) :
    let hJρ : ‖J‖ * ρ ≤ R := by
      rw [hρeq, ← mul_div_assoc]
      exact (div_le_iff₀ (by positivity)).2 (by nlinarith [hR.le])
    ∀ (alpha₀ : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → A)
    (reaction₀ : Metric.closedBall f₀ δ → ℝ → Metric.closedBall (0 : V) R → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (alpha : Metric.closedBall f₀ δ → ℝ → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) → A)
    (reaction : Metric.closedBall f₀ δ → ℝ → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1)) → PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a))
    (P : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)) →L[ℝ] V)
    (Ca Cb : ℝ≥0)
    (ha : ∀ f, LipschitzWith Ca
      (fun z : ℝ × Metric.closedBall (0 : V) R => alpha₀ f z.1 z.2))
    (hb : ∀ f, LipschitzWith Cb
      (fun z : ℝ × Metric.closedBall (0 : V) R => reaction₀ f z.1 z.2))
    (haclose : ∀ f t, t ∈ Icc (-R) R → ∀ z,
      ‖alpha₀ f t z - q‖ ≤ (Ca : ℝ) * (2 * R))
    (hbclose : ∀ f t, t ∈ Icc (-R) R → ∀ z,
      ‖reaction₀ f t z - b₀‖ ≤ (Cb : ℝ) * (2 * R))
    (halpha : ∀ f t, t ∈ Icc (-ρ) ρ → ∀ z : Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1))) ρ,
      alpha f t z = alpha₀ f t (J.closedBallMap hJρ z))
    (hbeta : ∀ f t, t ∈ Icc (-ρ) ρ → ∀ z : Metric.closedBall (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 1))) ρ,
      reaction f t z = reaction₀ f t (J.closedBallMap hJρ z))
    (haparam : ∀ f k t s z, ‖alpha₀ f t z - alpha₀ k s z‖ ≤
      (Ca : ℝ) * max |t - s| ‖P (f.val - k.val)‖)
    (hbparam : ∀ f k t s z, ‖reaction₀ f t z - reaction₀ k s z‖ ≤
      (Cb : ℝ) * max |t - s| ‖P (f.val - k.val)‖)
    (hCa : (Ca : ℝ) * R ≤ 1 / (32 * (‖m‖ * ‖Q‖ + 1)))
    (hL : let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
        (I := I) (M := M) (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
      ∀ v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)),
        ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
          tensorScaleLaplacian (I := I) (M := M) (g := g) (r := r) (s := s) a) v =
          m q (Q v) + d (D (K v))),
    let hρ : 0 < ρ := by rw [hρeq]; exact div_pos hR (by positivity)
    let K := ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
      (I := I) (M := M) (g := g) (r := r) (s := s) (show a + 1 ≤ a + 2 by linarith))
    let Params := Icc (-ρ / 4) (ρ / 4) × Metric.closedBall f₀ δ
    let Cq := ‖Q f₀‖ + ‖Q‖ * δ
    let A₀ := (‖q‖ + ((2 * Ca * (1 + ‖J‖₊)) : ℝ) * ρ).toNNReal
    let Hparam : ℝ≥0 := max 1 ‖P‖₊
    let K₁ := ‖m‖₊ * Ca * Hparam * ‖Q‖₊
    let K₀ := ‖m‖₊ * A₀ * ‖Q‖₊ + ‖m‖₊ * Ca * Hparam * Cq.toNNReal +
      Cb * Hparam
    let N := fun (p : Params) t
      (v : {v : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2)) |
      ‖K v‖ ≤ ρ}) => shiftedRemainder m Q K D d q
        (fun t z => alpha p.2 ((p.1 : ℝ) + t) z)
        (fun t z => reaction p.2 ((p.1 : ℝ) + t) z) p.2 t v
    let Bconst : ℝ≥0 := ‖m‖₊ * (Ca * ‖J‖₊) * (‖Q f₀‖ + ‖Q‖ * δ).toNNReal + (Cb * ‖J‖₊) + ‖d‖₊ * ‖D‖₊
    let D₀ := ‖m‖ * (‖q‖ + ((2 * Ca * (1 + ‖J‖₊)) : ℝ) * ρ) * (‖Q f₀‖ + ‖Q‖ * δ) +
      ‖b₀‖ + ((2 * Cb * (1 + ‖J‖₊)) : ℝ) * ρ
    ∃ T₀ : ℝ,
      T₀ = min (ρ / 4) (min 1 (min (1 / (64 * ((Bconst : ℝ) + 1) ^ 2))
        (((ρ / 4) / (2 * (D₀ + 1))) ^ 2))) ∧
      0 < T₀ ∧ T₀ ≤ ρ / 4 ∧ ∀ {T : ℝ} (hT : 0 < T), T ≤ T₀ →
      let κ := (‖m‖ * (2 * Ca * (1 + ‖J‖₊)) * ‖Q‖) * ρ * (1 + T) +
        (Bconst : ℝ) * Real.sqrt T * Real.sqrt (1 + T) +
        2 * (‖m‖ * (Ca * ‖J‖₊) * ‖Q‖) * (ρ / 4) * Real.sqrt (1 + T) * (1 + T)
      ∃ (u : Params → timeH1 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T)
        (gforce : Params → timeL2 (PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s a)) T),
        LipschitzWith
          ((K₁ * (1 + T).toNNReal * (ρ / 4).toNNReal + (Real.sqrt T).toNNReal * K₀) /
            (1 - κ).toNNReal) gforce ∧
        LipschitzWith
          (2 * ((K₁ * (1 + T).toNNReal * (ρ / 4).toNNReal + (Real.sqrt T).toNNReal * K₀) /
            (1 - κ).toNNReal)) u ∧
        ∀ f,
        let field := maximalRegularityDuhamelVectorField hT
          (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) (gforce f)
        u f = maximalRegularityDuhamelVectorMap hT
            (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) (gforce f) ∧
          (∀ᵐ t ∂(timeMeasure T), field t ∈ {v | ‖K v‖ ≤ ρ}) ∧
          gforce f =ᵐ[timeMeasure T] (fun t => N f t (aeSetLift
            (show (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) ∈
              {v | ‖K v‖ ≤ ρ} by
                simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hρ.le) field t)) ∧
          (u f).toFunL2 =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι => tensorHsInclusion
              (I := I) (M := M) (g := g) (r := r) (s := s) (show a ≤ a + 2 by linarith))).compLpL
                2 (timeMeasure T) field ∧
          timeH1.trace0 _ T (u f) = 0 ∧
          timeH1.timeDeriv _ T (u f) =
            (ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
              tensorScaleLaplacian (I := I) (M := M) (g := g) (r := r) (s := s) a)).compLpL
                2 (timeMeasure T) field + gforce f ∧
          ‖gforce f‖ ≤ ρ / 4 ∧
          (∀ᵐ t ∂timeMeasure T,
            ContinuousLinearMap.piLpMap 2 (fun _ : ι =>
                tensorScaleLaplacian (I := I) (M := M) (g := g) (r := r) (s := s) a)
                  (field t) + gforce f t =
              m (alpha f.2 ((f.1 : ℝ) + t) (K (field t))) (Q (f.2.val + field t)) +
                reaction f.2 ((f.1 : ℝ) + t) (K (field t))) := by
  intro hJρ alpha₀ reaction₀ alpha reaction P Ca Cb ha hb haclose hbclose halpha hbeta haparam hbparam hCa hL hρ K Params Cq A₀ Hparam K₁ K₀ N Bconst D₀
  apply Exists.elim
    (exists_uniform_time_precomposed_translated_vector_lipschitz
      (ι := ι) (I := I) (M := M) g r s a m Q D d q b₀ f₀ J hδ hR hρeq
      alpha₀ reaction₀ alpha reaction P Ca Cb ha hb haclose hbclose halpha hbeta
      haparam hbparam hCa)
  intro T₀ htime
  refine ⟨T₀, ?_⟩
  apply And.intro htime.1
  apply And.intro htime.2.1
  apply And.intro htime.2.2.1
  intro T hT hTT₀ κ
  apply Exists.elim (htime.2.2.2 hT hTT₀)
  intro u hu
  apply Exists.elim hu
  intro gforce hg
  refine ⟨u, ?_⟩
  refine ⟨gforce, ?_⟩
  apply And.intro hg.1
  apply And.intro hg.2.1
  intro f field
  have hf := hg.2.2 f
  apply And.intro hf.1
  apply And.intro hf.2.1
  apply And.intro hf.2.2.1
  apply And.intro hf.2.2.2.1
  apply And.intro hf.2.2.2.2.1
  apply And.intro hf.2.2.2.2.2.1
  apply And.intro hf.2.2.2.2.2.2
  have hz : (0 : PiLp 2 (fun _ : ι => TensorHs (I := I) (M := M) g r s (a + 2))) ∈
      {v | ‖K v‖ ≤ ρ} := by
    simpa only [Set.mem_ofPred_eq, map_zero, norm_zero] using hρ.le
  have hforce := hf.2.2.1
  have hlift := aeSetLift_coe_ae hz field hf.2.1
  filter_upwards [hforce, hlift] with t ht htval
  change gforce f t = shiftedRemainder m Q K D d q
    (fun t z => alpha f.2 ((f.1 : ℝ) + t) z)
    (fun t z => reaction f.2 ((f.1 : ℝ) + t) z) f.2.val t
      (aeSetLift hz field t).val at ht
  rw [htval] at ht
  rw [ht, hL (field t)]
  exact DifferentialGeometry.Analysis.Parabolic.shifted_remainder_operator_identity
    m Q K D d q
    (fun t z => alpha f.2 ((f.1 : ℝ) + t) z)
    (fun t z => reaction f.2 ((f.1 : ℝ) + t) z) f.2.val t (field t)

end DifferentialGeometry.Analysis.Parabolic.QuasiLinear
