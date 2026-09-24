import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyFlow
import DifferentialGeometry.Analysis.Elliptic.Lichnerowicz

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open Bundle Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M] [I.Boundaryless] [T2Space M]

local instance surfaceSolitonMeasurable : MeasurableSpace M := borel M
local instance surfaceSolitonBorel : BorelSpace M := ⟨rfl⟩

omit [CompleteSpace E] [IsManifold I 1 M] [T2Space M] in
private theorem surfaceSoliton_gradient_pair_continuous
    (g : SmoothRiemannianMetric I M) {p q : M → ℝ}
    (hp : ContMDiff I 𝓘(ℝ, ℝ) ∞ p) (hq : ContMDiff I 𝓘(ℝ, ℝ) ∞ q) :
    Continuous (fun x : M => g.inner x (gradFun (I := I) g p x)
      (gradFun (I := I) g q x)) :=
  (contMDiff_g_inner_of_smooth_sections (I := I) g
    (gradG (I := I) g ⟨p, hp⟩) (gradG (I := I) g ⟨q, hq⟩)).continuous

omit [I.Boundaryless] in
private theorem surfaceSoliton_energy_expansion
    (g : SmoothRiemannianMetric I M) {f : M → ℝ} (x : M)
    (hpositive : 0 < metricScalarAt (I := I) g x) :
    let R := fun y : M => metricScalarAt (I := I) g y
    let V := gradFun (I := I) g (fun y => Real.log (R y)) x - gradFun (I := I) g f x
    R x * g.inner x V V =
      normGradSqFun (I := I) g R x / R x -
        2 * g.inner x (gradFun (I := I) g R x) (gradFun (I := I) g f x) +
        R x * normGradSqFun (I := I) g f x := by
  let R := fun y : M => metricScalarAt (I := I) g y
  have hlog : gradFun (I := I) g (fun y => Real.log (R y)) x =
      (R x)⁻¹ • gradFun (I := I) g R x := by
    simpa only [gradient_eq_gradFun] using gradientFun_log (I := I) g
      ((metricScalar_smooth g).mdifferentiableAt (by decide)) hpositive
  change R x * g.inner x
      (gradFun (I := I) g (fun y => Real.log (R y)) x - gradFun (I := I) g f x)
      (gradFun (I := I) g (fun y => Real.log (R y)) x - gradFun (I := I) g f x) = _
  rw [hlog]
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, normGradSqFun_def]
  rw [g.symm x (gradFun (I := I) g f x) (gradFun (I := I) g R x)]
  dsimp only [R]
  field_simp [ne_of_gt hpositive]
  ring

private theorem surfaceSoliton_energy_continuous
    (g : SmoothRiemannianMetric I M) (F : C^∞⟮I, M; ℝ⟯)
    (hpositive : ∀ x : M, 0 < metricScalarAt (I := I) g x) :
    Continuous (fun x : M =>
      let R := fun y : M => metricScalarAt (I := I) g y
      let V := gradFun (I := I) g (fun y => Real.log (R y)) x -
        gradFun (I := I) g (F : M → ℝ) x
      R x * g.inner x V V) := by
  let R := fun y : M => metricScalarAt (I := I) g y
  have hR : ContMDiff I 𝓘(ℝ, ℝ) ∞ R := metricScalar_smooth (I := I) g
  have hRc : Continuous R := hR.continuous
  have h1 : Continuous (fun x : M => normGradSqFun (I := I) g R x / R x) :=
    (normGradSqFun_continuous (I := I) g hR).div hRc
      (fun x => (hpositive x).ne')
  have h2 : Continuous (fun x : M =>
      2 * g.inner x (gradFun (I := I) g R x) (gradFun (I := I) g (F : M → ℝ) x)) :=
    (surfaceSoliton_gradient_pair_continuous (I := I) (M := M) g hR F.contMDiff).const_mul 2
  have h3 : Continuous (fun x : M => R x * normGradSqFun (I := I) g (F : M → ℝ) x) :=
    hRc.mul (normGradSqFun_continuous (I := I) g F.contMDiff)
  refine ((h1.sub h2).add h3).congr (fun x => ?_)
  exact (surfaceSoliton_energy_expansion (I := I) (M := M) (f := (F : M → ℝ)) g x
    (hpositive x)).symm

omit [CompleteSpace E] in
private theorem surfaceSoliton_square_continuous
    [NeZero (Module.finrank ℝ E)]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (F : C^∞⟮I, M; ℝ⟯) :
    Continuous (fun x : M =>
      normSq0S (I := I) g x 2
        (hessTensorAt (I := I) g (F : M → ℝ) x -
          (ΔG (I := I) g F x / 2) • metricTensor0S (I := I) g x)) := by
  have hchart : Continuous (fun b : M => chartHessFrobeniusSq (I := I) g (F : M → ℝ) b) :=
    DifferentialGeometry.Analysis.Laplacian.chartHessFrobeniusSq_continuous
      (I := I) g F.contMDiff
  have hdelta : Continuous (fun b : M => (ΔG (I := I) g F b) ^ 2 / 2) :=
    ((((Δ_g_contMDiff (I := I) g F).continuous).pow 2)).div_const 2
  refine (hchart.sub hdelta).congr (fun x => ?_)
  rw [surfaceEntropy_traceFree_hessian_norm (I := I) g hdim F x,
    surfaceEntropy_hessian_norm_eq_chart (I := I) g F x]
  rfl

section Rigidity

variable [CompactSpace M] [Nonempty M]

theorem surfaceEntropy_static_firstVariation_eq_zero_iff_soliton
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (hpositive : ∀ x : M, 0 < metricScalarAt (I := I) g x)
    (F : C^∞⟮I, M; ℝ⟯)
    (hpoisson : ∀ x : M, ΔG (I := I) g F x =
      (∫ y, metricScalarAt (I := I) g y
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) /
          (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ -
        metricScalarAt (I := I) g x) :
    let μ := riemannianVolumeMeasure (I := I) (M := M) g
    let R := fun x : M => metricScalarAt (I := I) g x
    let r := (∫ x, R x ∂μ) / μ.real Set.univ
    (-(∫ x, normGradSqFun (I := I) g R x / R x ∂μ) +
        ∫ x, (R x - r) ^ 2 ∂μ = 0 ↔
      (∀ x : M, gradFun (I := I) g (fun y => Real.log (R y)) x -
          gradFun (I := I) g (F : M → ℝ) x = 0) ∧
      (∀ x : M, hessTensorAt (I := I) g (F : M → ℝ) x -
          (ΔG (I := I) g F x / 2) • metricTensor0S (I := I) g x = 0)) := by
  dsimp only
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  let R := fun x : M => metricScalarAt (I := I) g x
  let r := (∫ x, R x ∂μ) / μ.real Set.univ
  let V := fun x : M => gradFun (I := I) g (fun y => Real.log (R y)) x -
    gradFun (I := I) g (F : M → ℝ) x
  let Sq := fun x : M => hessTensorAt (I := I) g (F : M → ℝ) x -
    (ΔG (I := I) g F x / 2) • metricTensor0S (I := I) g x
  have htwo := surfaceEntropy_static_two_squares (I := I) (M := M) g hdim hpositive F hpoisson
  change -(∫ x, normGradSqFun (I := I) g R x / R x ∂μ) + ∫ x, (R x - r) ^ 2 ∂μ =
    -(∫ x, R x * g.inner x (V x) (V x) ∂μ) -
      2 * ∫ x, normSq0S (I := I) g x 2 (Sq x) ∂μ at htwo
  have hAc : Continuous (fun x : M => R x * g.inner x (V x) (V x)) := by
    simpa only [V, R] using surfaceSoliton_energy_continuous (I := I) (M := M) g F hpositive
  have hBc : Continuous (fun x : M => normSq0S (I := I) g x 2 (Sq x)) := by
    let : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; decide⟩
    simpa only [Sq] using surfaceSoliton_square_continuous (I := I) (M := M) g hdim F
  have hA0 : 0 ≤ ∫ x, R x * g.inner x (V x) (V x) ∂μ := by
    apply integral_nonneg
    intro x
    refine mul_nonneg (hpositive x).le ?_
    by_cases hv : V x = 0
    · rw [hv]
      simp
    · exact (g.pos x (V x) hv).le
  have hB0 : 0 ≤ ∫ x, normSq0S (I := I) g x 2 (Sq x) ∂μ :=
    integral_nonneg (fun x => normSq0S_nonneg (I := I) g x 2 (Sq x))
  constructor
  · intro hzero
    have hAz : (∫ x, R x * g.inner x (V x) (V x) ∂μ) = 0 := by
      linarith [htwo, hzero]
    have hBz : (∫ x, normSq0S (I := I) g x 2 (Sq x) ∂μ) = 0 := by
      linarith [htwo, hzero]
    have hAint : Integrable (fun x : M => R x * g.inner x (V x) (V x)) μ :=
      hAc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hBint : Integrable (fun x : M => normSq0S (I := I) g x 2 (Sq x)) μ :=
      hBc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
    have hAae : (fun x : M => R x * g.inner x (V x) (V x)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun x => by
        refine mul_nonneg (hpositive x).le ?_
        by_cases hv : V x = 0
        · rw [hv]
          simp
        · exact (g.pos x (V x) hv).le) hAint).mp hAz
    have hAall : ∀ x : M, R x * g.inner x (V x) (V x) = 0 := fun x =>
      congrFun (MeasureTheory.Measure.eq_of_ae_eq hAae hAc continuous_const) x
    have hBae : (fun x : M => normSq0S (I := I) g x 2 (Sq x)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun x => normSq0S_nonneg (I := I) g x 2 (Sq x)) hBint).mp hBz
    have hBall : ∀ x : M, normSq0S (I := I) g x 2 (Sq x) = 0 := fun x =>
      congrFun (MeasureTheory.Measure.eq_of_ae_eq hBae hBc continuous_const) x
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have hg : g.inner x (V x) (V x) = 0 := by
        rcases mul_eq_zero.mp (hAall x) with h | h
        · exact absurd h (hpositive x).ne'
        · exact h
      by_contra hv
      exact absurd hg (ne_of_gt (g.pos x (V x) hv))
    · exact (normSq0S_eq_zero_iff (I := I) g x 2 (Sq x)).mp (hBall x)
  · rintro ⟨hV, hSq⟩
    have hAzero : (∫ x, R x * g.inner x (V x) (V x) ∂μ) = 0 := by
      have hfun : (fun x : M => R x * g.inner x (V x) (V x)) = fun _ => (0 : ℝ) := by
        funext x
        have hv : V x = 0 := hV x
        rw [hv]
        simp
      rw [hfun, integral_zero]
    have hBzero : (∫ x, normSq0S (I := I) g x 2 (Sq x) ∂μ) = 0 := by
      have hfun : (fun x : M => normSq0S (I := I) g x 2 (Sq x)) = fun _ => (0 : ℝ) := by
        funext x
        exact (normSq0S_eq_zero_iff (I := I) g x 2 (Sq x)).mpr (hSq x)
      rw [hfun, integral_zero]
    rw [htwo, hAzero, hBzero]
    ring

theorem surfaceEntropy_static_soliton_equation_of_firstVariation_eq_zero
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (hpositive : ∀ x : M, 0 < metricScalarAt (I := I) g x)
    (F : C^∞⟮I, M; ℝ⟯)
    (hpoisson : ∀ x : M, ΔG (I := I) g F x =
      (∫ y, metricScalarAt (I := I) g y
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) /
          (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ -
        metricScalarAt (I := I) g x)
    (hzero : -(∫ x, normGradSqFun (I := I) g (fun y => metricScalarAt (I := I) g y) x /
          metricScalarAt (I := I) g x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        ∫ x, (metricScalarAt (I := I) g x -
          (∫ y, metricScalarAt (I := I) g y
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) /
              (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ) ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0) :
    ∀ x : M, metricRicciAt (I := I) g x + hessTensorAt (I := I) g (F : M → ℝ) x =
      ((∫ y, metricScalarAt (I := I) g y
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) /
          (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ / 2) •
        metricTensor0S (I := I) g x := by
  obtain ⟨-, hSq⟩ :=
    (surfaceEntropy_static_firstVariation_eq_zero_iff_soliton (I := I) (M := M)
      g hdim hpositive F hpoisson).mp hzero
  intro x
  have hHess : hessTensorAt (I := I) g (F : M → ℝ) x =
      (ΔG (I := I) g F x / 2) • metricTensor0S (I := I) g x :=
    sub_eq_zero.mp (hSq x)
  rw [metricRicciAt_eq_half_scalar_smul_metric_of_finrank_two (I := I) g hdim x,
    hHess, ← add_smul]
  congr 1
  have h := hpoisson x
  linarith

end Rigidity

section FlowRigidity

variable [ConnectedSpace M] [CompactSpace M] [Nonempty M]

theorem surfaceEntropy_deriv_eq_zero_soliton
    {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (hdim : Module.finrank ℝ E = 2)
    (hpositive : ∀ s ∈ D.regular, ∀ x : M, 0 < S.scalar s x)
    {t : ℝ} (ht : t ∈ D.regular)
    (hzero : deriv (fun s => surfaceEntropy (S.family.metric s)) t = 0) :
    ∃ F : C^∞⟮I, M; ℝ⟯,
      (∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) = 0 ∧
      (∀ x : M, ΔG (I := I) (S.family.metric t) F x =
        meanScalarCurvature (I := I) (M := M) (S.family.metric t) - S.scalar t x) ∧
      (∀ x : M, metricRicciAt (I := I) (S.family.metric t) x +
          hessTensorAt (I := I) (S.family.metric t) (F : M → ℝ) x =
        (meanScalarCurvature (I := I) (M := M) (S.family.metric t) / 2) •
          metricTensor0S (I := I) (S.family.metric t) x) := by
  let : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; decide⟩
  have hmean : meanScalarCurvature (I := I) (M := M) (S.family.metric t) =
      (∫ y, metricScalarAt (I := I) (S.family.metric t) y
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) /
        (riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t)).real
          Set.univ := rfl
  rw [hmean]
  let g := S.family.metric t
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hd := surfaceEntropy_hasDerivAt_first (I := I) (M := M) S hS hdim hpositive ht
  have h0 : -(∫ x, normGradSqFun (I := I) (S.family.metric t) (S.scalar t) x / S.scalar t x
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t))) +
      ∫ x, (S.scalar t x - meanScalarCurvature (I := I) (M := M) (S.family.metric t)) ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) (S.family.metric t)) = 0 :=
    hd.deriv.symm.trans hzero
  have hex : ∃ F : C^∞⟮I, M; ℝ⟯,
      (∫ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g)) = 0 ∧
      (∀ x : M, ΔG (I := I) g F x =
        meanScalarCurvature (I := I) (M := M) g - metricScalarAt (I := I) g x) :=
    surfaceEntropy_exists_meanZero_poisson (I := I) (M := M) g
  obtain ⟨F, hFmean, hFpoisson⟩ := hex
  refine ⟨F, hFmean, ?_, ?_⟩
  · intro x
    rw [← hmean]
    exact hFpoisson x
  have hpos : ∀ x : M, 0 < metricScalarAt (I := I) g x := fun x => hpositive t ht x
  have hpoisson : ∀ x : M, ΔG (I := I) g F x =
      (∫ y, metricScalarAt (I := I) g y ∂μ) / μ.real Set.univ -
        metricScalarAt (I := I) g x := by
    intro x
    have h := hFpoisson x
    rw [hmean] at h
    simpa only [g, μ] using h
  have hLHS : -(∫ x, normGradSqFun (I := I) g (fun y => metricScalarAt (I := I) g y) x /
        metricScalarAt (I := I) g x ∂μ) +
      ∫ x, (metricScalarAt (I := I) g x - (∫ y, metricScalarAt (I := I) g y ∂μ) /
        μ.real Set.univ) ^ 2 ∂μ = 0 := by
    have hfun : S.scalar t = fun y : M => metricScalarAt (I := I) g y := rfl
    rw [hmean] at h0
    rw [hfun] at h0
    simpa only [g, μ, SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.family] using h0
  intro x
  have hsol := surfaceEntropy_static_soliton_equation_of_firstVariation_eq_zero
    (I := I) (M := M) g hdim hpos F hpoisson hLHS x
  simpa only [g, μ] using hsol

end FlowRigidity

section RigidityHypothesisSharpness

theorem exists_nonneg_integral_eq_zero_not_ae_eq_zero :
    ∃ f : ℝ → ℝ, (∀ x : ℝ, 0 ≤ f x) ∧ (∫ x, f x ∂(volume : Measure ℝ)) = 0 ∧
      ¬ f =ᵐ[(volume : Measure ℝ)] 0 := by
  have htop : (volume : Measure ℝ) Set.univ = ⊤ := by
    have hmono : (volume : Measure ℝ) (Set.Ioi (0 : ℝ)) ≤ volume Set.univ :=
      measure_mono (Set.subset_univ _)
    rw [Real.volume_Ioi] at hmono
    exact top_unique hmono
  refine ⟨fun _ => (1 : ℝ), fun _ => zero_le_one, ?_, ?_⟩
  · rw [MeasureTheory.integral_const]
    change ((volume : Measure ℝ) Set.univ).toReal • (1 : ℝ) = 0
    rw [htop, ENNReal.toReal_top, zero_smul]
  · intro hf
    have hf' : ∀ᵐ x ∂(volume : Measure ℝ), (1 : ℝ) = (0 : ℝ) := hf
    rw [MeasureTheory.ae_iff] at hf'
    have hset : {x : ℝ | ¬ (1 : ℝ) = 0} = Set.univ := by
      ext x
      simp
    rw [hset, htop] at hf'
    exact ENNReal.top_ne_zero hf'

end RigidityHypothesisSharpness

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
