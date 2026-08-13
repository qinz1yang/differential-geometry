import DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothScalar.PreH1
import DifferentialGeometry.Analysis.Integration.L2.ParametricFiberInnerSmooth
import DifferentialGeometry.Analysis.Parabolic.Energy.TimeCutoff
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Metric.MetricBounds
import DifferentialGeometry.Geometry.Operator.NormGradSq
import DifferentialGeometry.Geometry.Operator.NormGradSqTime

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Parabolic.Energy

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

def smoothScalarSlice (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (t : ℝ) : SmoothScalar g where
  toFun := fun x => u t x
  smooth := hu.comp (contMDiff_const.prodMk contMDiff_id)

omit [Module.Finite ℝ E] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [CompactSpace M] in
@[simp] lemma smoothScalarSlice_toFun
    (g : SmoothRiemannianMetric I M)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (t : ℝ) (x : M) :
    (smoothScalarSlice (I := I) g u hu t).toFun x = u t x := rfl

def localizedIntegral {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) : ℝ :=
  ∫ x, cutoff.toFun x ^ 2 * u.toFun x
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

def localizedL2Mass {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) : ℝ :=
  ∫ x, cutoff.toFun x ^ 2 * u.toFun x ^ 2
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

def localizedDirichletEnergy {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) : ℝ :=
  ∫ x, cutoff.toFun x ^ 2 *
      g.inner x
        (gradFun (I := I) g u.toFun x)
        (gradFun (I := I) g u.toFun x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

def cutoffGradientError {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) : ℝ :=
  ∫ x, u.toFun x ^ 2 *
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g cutoff.toFun x)
    ∂(riemannianVolumeMeasure (I := I) (M := M) g)

omit [I.Boundaryless] [CompactSpace M] in
theorem localizedL2Mass_nonneg {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) :
    0 ≤ localizedL2Mass (I := I) (M := M) cutoff u := by
  exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))

omit [I.Boundaryless] [CompactSpace M] in
theorem localizedDirichletEnergy_nonneg {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) :
    0 ≤ localizedDirichletEnergy (I := I) (M := M) cutoff u := by
  exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _)
    (metric_inner_self_nonneg (I := I) (M := M) g x _))

omit [I.Boundaryless] [CompactSpace M] in
theorem cutoffGradientError_nonneg {g : SmoothRiemannianMetric I M}
    (cutoff u : SmoothScalar g) :
    0 ≤ cutoffGradientError (I := I) (M := M) cutoff u := by
  exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _)
    (metric_inner_self_nonneg (I := I) (M := M) g x _))

omit [I.Boundaryless] in
theorem localizedL2Mass_le_of_sq_le
    {g : SmoothRiemannianMetric I M}
    (cutoff outer u : SmoothScalar g)
    (hcutoff : ∀ x : M, cutoff.toFun x ^ 2 ≤ outer.toFun x ^ 2) :
    localizedL2Mass (I := I) (M := M) cutoff u ≤
      localizedL2Mass (I := I) (M := M) outer u := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hcutoff_int : Integrable
      (fun x : M => cutoff.toFun x ^ 2 * u.toFun x ^ 2) μ :=
    ((cutoff.smooth.continuous.pow 2).mul (u.smooth.continuous.pow 2))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have houter_int : Integrable
      (fun x : M => outer.toFun x ^ 2 * u.toFun x ^ 2) μ :=
    ((outer.smooth.continuous.pow 2).mul (u.smooth.continuous.pow 2))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact integral_mono hcutoff_int houter_int fun x =>
    mul_le_mul_of_nonneg_right (hcutoff x) (sq_nonneg (u.toFun x))

omit [I.Boundaryless] in
theorem localizedL2Mass_le_of_nonneg_of_le
    {g : SmoothRiemannianMetric I M}
    (cutoff outer u : SmoothScalar g)
    (hcutoff_nonneg : ∀ x : M, 0 ≤ cutoff.toFun x)
    (hcutoff : ∀ x : M, cutoff.toFun x ≤ outer.toFun x) :
    localizedL2Mass (I := I) (M := M) cutoff u ≤
      localizedL2Mass (I := I) (M := M) outer u := by
  apply localizedL2Mass_le_of_sq_le (I := I) (M := M) cutoff outer u
  intro x
  exact (sq_le_sq₀ (hcutoff_nonneg x)
    ((hcutoff_nonneg x).trans (hcutoff x))).2 (hcutoff x)

theorem cutoffGradientError_le_localizedL2Mass
    {g : SmoothRiemannianMetric I M}
    (cutoff outer u : SmoothScalar g) {K : ℝ}
    (hgrad : ∀ x : M,
      g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x) ≤
        K * outer.toFun x ^ 2) :
    cutoffGradientError (I := I) (M := M) cutoff u ≤
      K * localizedL2Mass (I := I) (M := M) outer u := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let gradNormSq : M → ℝ := fun x =>
    g.inner x
      (gradFun (I := I) g cutoff.toFun x)
      (gradFun (I := I) g cutoff.toFun x)
  have hgrad_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ gradNormSq := by
    have h := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g ⟨cutoff.toFun, cutoff.smooth⟩) (grad_g (I := I) g ⟨cutoff.toFun,
        cutoff.smooth⟩)
    simpa only [gradNormSq, grad_g_apply] using h
  have hleft_int : Integrable (fun x : M => u.toFun x ^ 2 * gradNormSq x) μ :=
    ((u.smooth.continuous.pow 2).mul hgrad_smooth.continuous)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hright_int : Integrable
      (fun x : M => K * (outer.toFun x ^ 2 * u.toFun x ^ 2)) μ :=
    (continuous_const.mul ((outer.smooth.continuous.pow 2).mul
      (u.smooth.continuous.pow 2))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  change (∫ x, u.toFun x ^ 2 * gradNormSq x ∂μ) ≤
    K * ∫ x, outer.toFun x ^ 2 * u.toFun x ^ 2 ∂μ
  rw [← integral_const_mul]
  apply integral_mono hleft_int hright_int
  intro x
  have hmul := mul_le_mul_of_nonneg_left (hgrad x) (sq_nonneg (u.toFun x))
  change u.toFun x ^ 2 * gradNormSq x ≤
    K * (outer.toFun x ^ 2 * u.toFun x ^ 2)
  nlinarith

omit [I.Boundaryless] in
theorem contDiff_localizedIntegral
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    ContDiff ℝ ∞
      (fun t => localizedIntegral (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t)) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hcutoff_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1) :=
    cutoff.smooth.comp contMDiff_fst
  have hu_swap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => u p.2 p.1) :=
    hu.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hintegrand : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1 ^ 2 * u p.2 p.1) :=
    (hcutoff_joint.pow 2).mul hu_swap
  simpa only [localizedIntegral, smoothScalarSlice, μ] using
    contDiff_integral_of_jointContMDiff μ
      (fun x t => cutoff.toFun x ^ 2 * u t x) hintegrand

omit [I.Boundaryless] in
theorem contDiff_localizedL2Mass
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    ContDiff ℝ ∞
      (fun t => localizedL2Mass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t)) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hcutoff_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1) :=
    cutoff.smooth.comp contMDiff_fst
  have hu_swap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => u p.2 p.1) :=
    hu.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hintegrand : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1 ^ 2 * u p.2 p.1 ^ 2) :=
    (hcutoff_joint.pow 2).mul (hu_swap.pow 2)
  simpa only [localizedL2Mass, smoothScalarSlice, μ] using
    contDiff_integral_of_jointContMDiff μ
      (fun x t => cutoff.toFun x ^ 2 * u t x ^ 2) hintegrand

omit [I.Boundaryless] in
theorem contDiff_localizedDirichletEnergy
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    ContDiff ℝ ∞
      (fun t => localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t)) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let G : MetricConnectionFamily (I := I) (M := M) ℝ :=
    { metric := fun _ => g
      connection := fun _ => LeviCivita (I := I) g
      metricCompatible := fun _ => by
        simpa [LeviCivita] using
          (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g) }
  have hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (G.metric p.1) x₀ p.2 i j)
        (Set.univ ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet) := by
    intro x₀ i j
    have hspace := chartGramMatrix_entry_contMDiffOn (I := I) g x₀ i j
    simpa only [G] using hspace.comp contMDiffOn_snd
      (fun p hp => hp.2)
  have hgrad_joint : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        g.inner p.2
          (gradientFun (I := I) g (u p.1) p.2)
          (gradientFun (I := I) g (u p.1) p.2)) := by
    have h := gradSq_joint (I := I) G.metric isOpen_univ hgram u hu.contMDiffOn
    simpa only [G, Set.univ_prod_univ, contMDiffOn_univ] using h
  have hcutoff_joint : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => cutoff.toFun p.2) :=
    cutoff.smooth.comp contMDiff_snd
  have hintegrand : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1 ^ 2 *
        g.inner p.1
          (gradientFun (I := I) g (u p.2) p.1)
          (gradientFun (I := I) g (u p.2) p.1)) := by
    exact ((hcutoff_joint.pow 2).mul hgrad_joint).comp
      (contMDiff_snd.prodMk contMDiff_fst)
  simpa only [localizedDirichletEnergy, smoothScalarSlice, μ] using
    contDiff_integral_of_jointContMDiff μ
      (fun x t => cutoff.toFun x ^ 2 *
        g.inner x
          (gradientFun (I := I) g (u t) x)
          (gradientFun (I := I) g (u t) x)) hintegrand

theorem contDiff_cutoffGradientError
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2)) :
    ContDiff ℝ ∞
      (fun t => cutoffGradientError (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t)) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hcutoff_grad_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M =>
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g cutoff.toFun x)) := by
    have h := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g ⟨cutoff.toFun, cutoff.smooth⟩) (grad_g (I := I) g ⟨cutoff.toFun,
        cutoff.smooth⟩)
    simpa only [grad_g_apply] using h
  have hcutoff_grad_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        g.inner p.1
          (gradFun (I := I) g cutoff.toFun p.1)
          (gradFun (I := I) g cutoff.toFun p.1)) :=
    hcutoff_grad_smooth.comp contMDiff_fst
  have hu_swap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => u p.2 p.1) :=
    hu.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hintegrand : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => u p.2 p.1 ^ 2 *
        g.inner p.1
          (gradFun (I := I) g cutoff.toFun p.1)
          (gradFun (I := I) g cutoff.toFun p.1)) :=
    (hu_swap.pow 2).mul hcutoff_grad_joint
  simpa only [cutoffGradientError, smoothScalarSlice, μ] using
    contDiff_integral_of_jointContMDiff μ
      (fun x t => u t x ^ 2 *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x)) hintegrand

theorem intervalIntegral_cutoffGradientError_le_localizedL2Mass
    {g : SmoothRiemannianMetric I M}
    (cutoff outer : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {K a b : ℝ} (hab : a ≤ b)
    (hgrad : ∀ x : M,
      g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x) ≤
        K * outer.toFun x ^ 2) :
    (∫ t in a..b,
      cutoffGradientError (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t)) ≤
      K * ∫ t in a..b,
        localizedL2Mass (I := I) (M := M) outer
          (smoothScalarSlice (I := I) g u hu t) := by
  let error : ℝ → ℝ := fun t =>
    cutoffGradientError (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  let outerMass : ℝ → ℝ := fun t =>
    localizedL2Mass (I := I) (M := M) outer
      (smoothScalarSlice (I := I) g u hu t)
  have herror_cont : ContinuousOn error (Icc a b) := by
    simpa only [error] using
      (contDiff_cutoffGradientError (I := I) (M := M) cutoff u hu).continuous.continuousOn
  have hmass_cont : ContinuousOn outerMass (Icc a b) := by
    simpa only [outerMass] using
      (contDiff_localizedL2Mass (I := I) (M := M) outer u hu).continuous.continuousOn
  have herror_int : IntervalIntegrable error volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using herror_cont
  have hmass_int : IntervalIntegrable outerMass volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hab] using hmass_cont
  have hmono : (∫ t in a..b, error t) ≤ ∫ t in a..b, K * outerMass t :=
    intervalIntegral.integral_mono_on hab herror_int (hmass_int.const_mul K)
      (fun t _ => cutoffGradientError_le_localizedL2Mass
        (I := I) (M := M) cutoff outer
          (smoothScalarSlice (I := I) g u hu t) hgrad)
  rw [intervalIntegral.integral_const_mul] at hmono
  simpa only [error, outerMass] using hmono

theorem timeCutoff_caccioppoli_rhs_le
    {g : SmoothRiemannianMetric I M}
    (cutoff outer : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    {a t₀ t t₁ D K L : ℝ}
    (hat₀ : a < t₀) (ht₀t : t₀ ≤ t) (htt₁ : t ≤ t₁)
    (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hcutoff : ∀ x : M, cutoff.toFun x ^ 2 ≤ outer.toFun x ^ 2)
    (hgrad : ∀ x : M,
      g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x) ≤
        K * outer.toFun x ^ 2)
    (hderiv_le : ∀ s ∈ Icc a t₁, timeCutoffDeriv a t₀ s ≤ D)
    (houterMass_le :
      (∫ s in a..t₁,
        localizedL2Mass (I := I) (M := M) outer
          (smoothScalarSlice (I := I) g u hu s)) ≤ L) :
    (∫ s in a..t,
      timeCutoffDeriv a t₀ s *
          localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu s) +
        timeCutoff a t₀ s *
          (4 * cutoffGradientError (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu s))) ≤
      (D + 4 * K) * L := by
  apply timeCutoff_mass_error_intervalIntegral_le
    hat₀ ht₀t htt₁ hD hK
  · exact (contDiff_localizedL2Mass (I := I) (M := M) cutoff u hu).continuous.continuousOn
  · exact (contDiff_cutoffGradientError
      (I := I) (M := M) cutoff u hu).continuous.continuousOn
  · exact (contDiff_localizedL2Mass (I := I) (M := M) outer u hu).continuous.continuousOn
  · intro s _
    exact localizedL2Mass_nonneg (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu s)
  · intro s _
    exact cutoffGradientError_nonneg (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu s)
  · intro s _
    exact localizedL2Mass_nonneg (I := I) (M := M) outer
      (smoothScalarSlice (I := I) g u hu s)
  · intro s _
    exact localizedL2Mass_le_of_sq_le (I := I) (M := M) cutoff outer
      (smoothScalarSlice (I := I) g u hu s) hcutoff
  · intro s _
    exact cutoffGradientError_le_localizedL2Mass
      (I := I) (M := M) cutoff outer
        (smoothScalarSlice (I := I) g u hu s) hgrad
  · exact hderiv_le
  · exact houterMass_le

omit [I.Boundaryless] in
theorem hasDerivAt_localizedIntegral
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (t : ℝ) :
    HasDerivAt
      (fun s => localizedIntegral (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu s))
      (∫ x, cutoff.toFun x ^ 2 * deriv (fun s => u s x) t
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) t := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp only [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hcutoff_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1) :=
    cutoff.smooth.comp contMDiff_fst
  have hu_swap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => u p.2 p.1) :=
    hu.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hintegrand : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1 ^ 2 * u p.2 p.1) :=
    (hcutoff_joint.pow 2).mul hu_swap
  have hraw := hasDerivAt_integral_of_jointContMDiff μ
    (fun x s => cutoff.toFun x ^ 2 * u s x) hintegrand t
  have hderiv : ∀ x : M,
      deriv (fun s => cutoff.toFun x ^ 2 * u s x) t =
        cutoff.toFun x ^ 2 * deriv (fun s => u s x) t := by
    intro x
    have hfiber : ContDiff ℝ ∞ (fun s : ℝ => u s x) :=
      contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
    have hu_at : HasDerivAt (fun s : ℝ => u s x) (deriv (fun s : ℝ => u s x) t) t :=
      (hfiber.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hproduct := ((hasDerivAt_const t (cutoff.toFun x ^ 2)).mul hu_at).deriv
    simpa only [Pi.mul_apply, zero_mul, zero_add] using hproduct
  convert hraw using 1
  simpa only [μ] using (integral_congr_ae (ae_of_all μ hderiv)).symm

omit [I.Boundaryless] in
theorem hasDerivAt_localizedL2Mass
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (t : ℝ) :
    HasDerivAt
      (fun s => localizedL2Mass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu s))
      (∫ x, 2 * cutoff.toFun x ^ 2 * u t x * deriv (fun s => u s x) t
        ∂(riemannianVolumeMeasure (I := I) (M := M) g)) t := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hcutoff_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1) :=
    cutoff.smooth.comp contMDiff_fst
  have hu_swap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => u p.2 p.1) :=
    hu.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hintegrand : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1 ^ 2 * u p.2 p.1 ^ 2) :=
    (hcutoff_joint.pow 2).mul (hu_swap.pow 2)
  have hraw := hasDerivAt_integral_of_jointContMDiff μ
    (fun x s => cutoff.toFun x ^ 2 * u s x ^ 2) hintegrand t
  have hderiv : ∀ x : M,
      deriv (fun s => cutoff.toFun x ^ 2 * u s x ^ 2) t =
        2 * cutoff.toFun x ^ 2 * u t x * deriv (fun s => u s x) t := by
    intro x
    have hfiber : ContDiff ℝ ∞ (fun s : ℝ => u s x) :=
      contMDiff_iff_contDiff.mp (hu.comp (contMDiff_id.prodMk contMDiff_const))
    have hu_at : HasDerivAt (fun s : ℝ => u s x) (deriv (fun s : ℝ => u s x) t) t :=
      (hfiber.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hproduct := (hasDerivAt_const t (cutoff.toFun x ^ 2)).mul (hu_at.pow 2)
    have heq : HasDerivAt (fun s => cutoff.toFun x ^ 2 * u s x ^ 2)
        (2 * cutoff.toFun x ^ 2 * u t x * deriv (fun s => u s x) t) t := by
      convert hproduct using 1
      all_goals ring
    exact heq.deriv
  convert hraw using 1
  simpa only [μ] using (integral_congr_ae (ae_of_all μ hderiv)).symm

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma neg_four_mul_inner_grad_le
    (g : SmoothRiemannianMetric I M) (cutoff u : SmoothScalar g) (x : M) :
    -4 * (cutoff.toFun x * u.toFun x *
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g u.toFun x)) ≤
      cutoff.toFun x ^ 2 *
          g.inner x
            (gradFun (I := I) g u.toFun x)
            (gradFun (I := I) g u.toFun x) +
        4 * (u.toFun x ^ 2 *
          g.inner x
            (gradFun (I := I) g cutoff.toFun x)
            (gradFun (I := I) g cutoff.toFun x)) := by
  have hnonneg := metric_inner_self_nonneg (I := I) (M := M) g x
    (cutoff.toFun x • gradFun (I := I) g u.toFun x +
      (2 * u.toFun x) • gradFun (I := I) g cutoff.toFun x)
  have hexpand :
      g.inner x
          (cutoff.toFun x • gradFun (I := I) g u.toFun x +
            (2 * u.toFun x) • gradFun (I := I) g cutoff.toFun x)
          (cutoff.toFun x • gradFun (I := I) g u.toFun x +
            (2 * u.toFun x) • gradFun (I := I) g cutoff.toFun x) =
        cutoff.toFun x ^ 2 *
            g.inner x
              (gradFun (I := I) g u.toFun x)
              (gradFun (I := I) g u.toFun x) +
          4 * (cutoff.toFun x * u.toFun x *
            g.inner x
              (gradFun (I := I) g cutoff.toFun x)
              (gradFun (I := I) g u.toFun x)) +
          4 * (u.toFun x ^ 2 *
            g.inner x
              (gradFun (I := I) g cutoff.toFun x)
              (gradFun (I := I) g cutoff.toFun x)) := by
    simp only [map_add, ContinuousLinearMap.add_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [g.symm x
      (gradFun (I := I) g u.toFun x)
      (gradFun (I := I) g cutoff.toFun x)]
    ring
  rw [hexpand] at hnonneg
  linarith

omit [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M] in
private lemma gradFun_sq_mul
    (g : SmoothRiemannianMetric I M) (cutoff u : SmoothScalar g) (x : M) :
    gradFun (I := I) g
        (fun y : M => cutoff.toFun y ^ 2 * u.toFun y) x =
      cutoff.toFun x ^ 2 • gradFun (I := I) g u.toFun x +
        (2 * cutoff.toFun x * u.toFun x) •
          gradFun (I := I) g cutoff.toFun x := by
  change gradientFun (I := I) g
      (fun y : M => cutoff.toFun y ^ 2 * u.toFun y) x = _
  rw [gradientFun_mul (I := I) (f := fun y : M => cutoff.toFun y ^ 2)
    (h := u.toFun) g
    ((cutoff.smooth.mdifferentiable (by simp) x).pow 2)
    (u.smooth.mdifferentiable (by simp) x)]
  rw [gradientFun_pow (I := I) g 1
    (cutoff.smooth.mdifferentiable (by simp) x)]
  rw [smul_smul]
  congr 1
  ring_nf
  rfl

theorem caccioppoli_spatial
    {g : SmoothRiemannianMetric I M} (cutoff u : SmoothScalar g) :
    localizedDirichletEnergy (I := I) (M := M) cutoff u ≤
      -2 * ∫ x, cutoff.toFun x ^ 2 * u.toFun x *
          Δ_g (I := I) g ⟨u.toFun, u.smooth⟩ x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) +
      4 * cutoffGradientError (I := I) (M := M) cutoff u := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let test : SmoothScalar g :=
    ⟨fun x => cutoff.toFun x ^ 2 * u.toFun x,
      (cutoff.smooth.pow 2).mul u.smooth⟩
  have hgrad_u : Continuous (fun x : M =>
      g.inner x
        (gradFun (I := I) g u.toFun x)
        (gradFun (I := I) g u.toFun x)) := by
    simpa only [grad_g_apply] using u.continuous_inner_grad u
  have hgrad_cutoff : Continuous (fun x : M =>
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g cutoff.toFun x)) := by
    simpa only [grad_g_apply] using cutoff.continuous_inner_grad cutoff
  have hgrad_cross : Continuous (fun x : M =>
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g u.toFun x)) := by
    simpa only [grad_g_apply] using cutoff.continuous_inner_grad u
  have hD_cont : Continuous (fun x : M =>
      cutoff.toFun x ^ 2 *
        g.inner x
          (gradFun (I := I) g u.toFun x)
          (gradFun (I := I) g u.toFun x)) :=
    (cutoff.smooth.continuous.pow 2).mul hgrad_u
  have hE_cont : Continuous (fun x : M =>
      u.toFun x ^ 2 *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x)) :=
    (u.smooth.continuous.pow 2).mul hgrad_cutoff
  have hC_cont : Continuous (fun x : M =>
      cutoff.toFun x * u.toFun x *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g u.toFun x)) :=
    (cutoff.smooth.continuous.mul u.smooth.continuous).mul hgrad_cross
  have hD_int : Integrable (fun x : M =>
      cutoff.toFun x ^ 2 *
        g.inner x
          (gradFun (I := I) g u.toFun x)
          (gradFun (I := I) g u.toFun x)) μ :=
    hD_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hE_int : Integrable (fun x : M =>
      u.toFun x ^ 2 *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x)) μ :=
    hE_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hC_int : Integrable (fun x : M =>
      cutoff.toFun x * u.toFun x *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g u.toFun x)) μ :=
    hC_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hgreen :=
    green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
      (I := I) g test.smooth u.smooth (HasCompactSupport.of_compactSpace _)
  have htest_pointwise : ∀ x : M,
      g.inner x
          (gradFun (I := I) g test.toFun x)
          (gradFun (I := I) g u.toFun x) =
        cutoff.toFun x ^ 2 *
            g.inner x
              (gradFun (I := I) g u.toFun x)
              (gradFun (I := I) g u.toFun x) +
          2 * (cutoff.toFun x * u.toFun x *
            g.inner x
              (gradFun (I := I) g cutoff.toFun x)
              (gradFun (I := I) g u.toFun x)) := by
    intro x
    dsimp only [test]
    rw [gradFun_sq_mul (I := I) (M := M) g cutoff u x]
    simp only [map_add, ContinuousLinearMap.add_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hidentity :
      (∫ x, cutoff.toFun x ^ 2 *
          g.inner x
            (gradFun (I := I) g u.toFun x)
            (gradFun (I := I) g u.toFun x) ∂μ) +
        2 * ∫ x, cutoff.toFun x * u.toFun x *
          g.inner x
            (gradFun (I := I) g cutoff.toFun x)
            (gradFun (I := I) g u.toFun x) ∂μ =
        -∫ x, cutoff.toFun x ^ 2 * u.toFun x *
          Δ_g (I := I) g ⟨u.toFun, u.smooth⟩ x ∂μ := by
    rw [← integral_const_mul]
    rw [← integral_add hD_int (hC_int.const_mul 2)]
    rw [← integral_congr_ae (ae_of_all μ htest_pointwise)]
    simpa [μ, test, grad_g_apply] using hgreen
  have hcross :
      -4 * ∫ x, cutoff.toFun x * u.toFun x *
          g.inner x
            (gradFun (I := I) g cutoff.toFun x)
            (gradFun (I := I) g u.toFun x) ∂μ ≤
        (∫ x, cutoff.toFun x ^ 2 *
          g.inner x
            (gradFun (I := I) g u.toFun x)
            (gradFun (I := I) g u.toFun x) ∂μ) +
        4 * ∫ x, u.toFun x ^ 2 *
          g.inner x
            (gradFun (I := I) g cutoff.toFun x)
            (gradFun (I := I) g cutoff.toFun x) ∂μ := by
    rw [← integral_const_mul]
    rw [← integral_const_mul]
    rw [← integral_add hD_int (hE_int.const_mul 4)]
    exact integral_mono (hC_int.const_mul (-4)) (hD_int.add (hE_int.const_mul 4))
      (fun x => neg_four_mul_inner_grad_le (I := I) (M := M) g cutoff u x)
  change (∫ x, cutoff.toFun x ^ 2 *
      g.inner x
        (gradFun (I := I) g u.toFun x)
        (gradFun (I := I) g u.toFun x) ∂μ) ≤
    -2 * ∫ x, cutoff.toFun x ^ 2 * u.toFun x *
      Δ_g (I := I) g ⟨u.toFun, u.smooth⟩ x ∂μ +
    4 * ∫ x, u.toFun x ^ 2 *
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g cutoff.toFun x) ∂μ
  linarith

theorem caccioppoli_differential
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (t : ℝ)
    (hpde : ∀ x : M,
      deriv (fun s => u s x) t =
        Δ_g (I := I) g ⟨(smoothScalarSlice (I := I) g u hu t).toFun,
          (smoothScalarSlice (I := I) g u hu t).smooth⟩ x + source t x) :
    deriv
        (fun s => localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu s)) t +
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu t) +
        ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let ut := smoothScalarSlice (I := I) g u hu t
  let ft := smoothScalarSlice (I := I) g source hsource t
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hlap_cont : Continuous (fun x : M =>
      Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x) :=
    (Δ_g_contMDiff (I := I) g ⟨ut.toFun, ut.smooth⟩).continuous
  have hcoeff_cont : Continuous (fun x : M => 2 * cutoff.toFun x ^ 2 * u t x) :=
    (continuous_const.mul (cutoff.smooth.continuous.pow 2)).mul ut.smooth.continuous
  have hsource_cont : Continuous (fun x : M => source t x) := ft.smooth.continuous
  have hlap_int : Integrable (fun x : M =>
      2 * cutoff.toFun x ^ 2 * u t x * Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x) μ :=
    (hcoeff_cont.mul hlap_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsource_int : Integrable (fun x : M =>
      2 * cutoff.toFun x ^ 2 * u t x * source t x) μ :=
    (hcoeff_cont.mul hsource_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsplit :
      ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * deriv (fun s => u s x) t ∂μ =
        (∫ x, 2 * cutoff.toFun x ^ 2 * u t x *
          Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x ∂μ) +
        ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x ∂μ := by
    rw [← integral_add hlap_int hsource_int]
    apply integral_congr_ae
    refine ae_of_all μ (fun x => ?_)
    change 2 * cutoff.toFun x ^ 2 * u t x * deriv (fun s => u s x) t =
      2 * cutoff.toFun x ^ 2 * u t x * Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x +
        2 * cutoff.toFun x ^ 2 * u t x * source t x
    rw [hpde x]
    ring
  have hmass := hasDerivAt_localizedL2Mass
    (I := I) (M := M) cutoff u hu t
  have hspatial := caccioppoli_spatial
    (I := I) (M := M) cutoff ut
  change deriv
        (fun s => localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu s)) t +
      localizedDirichletEnergy (I := I) (M := M) cutoff ut ≤
    4 * cutoffGradientError (I := I) (M := M) cutoff ut +
      ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x ∂μ
  have hlap_scale :
      ∫ x, 2 * cutoff.toFun x ^ 2 * u t x *
          Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x ∂μ =
        2 * ∫ x, cutoff.toFun x ^ 2 * ut.toFun x *
          Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine ae_of_all μ (fun x => ?_)
    change 2 * cutoff.toFun x ^ 2 * u t x * Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x =
      2 * (cutoff.toFun x ^ 2 * u t x * Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x)
    ring
  rw [hmass.deriv, hsplit]
  rw [hlap_scale]
  linarith

theorem caccioppoli_differential_of_subsolution
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    (t : ℝ)
    (hu_nonneg : ∀ x : M, 0 ≤ u t x)
    (hpde : ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) g ⟨(smoothScalarSlice (I := I) g u hu t).toFun,
          (smoothScalarSlice (I := I) g u hu t).smooth⟩ x + source t x) :
    deriv
        (fun s => localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu s)) t +
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu t) ≤
      4 * cutoffGradientError (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu t) +
        ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let ut := smoothScalarSlice (I := I) g u hu t
  let ft := smoothScalarSlice (I := I) g source hsource t
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hu_swap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => u p.2 p.1) :=
    hu.comp (contMDiff_snd.prodMk contMDiff_fst)
  have htime_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => deriv (fun s => u s p.1) p.2) := by
    simpa using DifferentialGeometry.contMDiff_partial_deriv_snd I
      (⟨fun p : M × ℝ => u p.2 p.1, hu_swap⟩ :
        C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; ℝ⟯)
  have htime_cont : Continuous (fun x : M => deriv (fun s => u s x) t) :=
    htime_joint.continuous.comp (continuous_id.prodMk continuous_const)
  have hlap_cont : Continuous (fun x : M =>
      Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x) :=
    (Δ_g_contMDiff (I := I) g ⟨ut.toFun, ut.smooth⟩).continuous
  have hcoeff_cont : Continuous (fun x : M => 2 * cutoff.toFun x ^ 2 * u t x) :=
    (continuous_const.mul (cutoff.smooth.continuous.pow 2)).mul ut.smooth.continuous
  have hsource_cont : Continuous (fun x : M => source t x) := ft.smooth.continuous
  have htime_int : Integrable (fun x : M =>
      2 * cutoff.toFun x ^ 2 * u t x * deriv (fun s => u s x) t) μ :=
    (hcoeff_cont.mul htime_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlap_int : Integrable (fun x : M =>
      2 * cutoff.toFun x ^ 2 * u t x * Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x) μ :=
    (hcoeff_cont.mul hlap_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsource_int : Integrable (fun x : M =>
      2 * cutoff.toFun x ^ 2 * u t x * source t x) μ :=
    (hcoeff_cont.mul hsource_cont).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have htime_le :
      ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * deriv (fun s => u s x) t ∂μ ≤
        (∫ x, 2 * cutoff.toFun x ^ 2 * u t x *
          Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x ∂μ) +
        ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x ∂μ := by
    rw [← integral_add hlap_int hsource_int]
    apply integral_mono htime_int (hlap_int.add hsource_int)
    intro x
    have hcoeff : 0 ≤ 2 * cutoff.toFun x ^ 2 * u t x :=
      mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (hu_nonneg x)
    change 2 * cutoff.toFun x ^ 2 * u t x * deriv (fun s => u s x) t ≤
      2 * cutoff.toFun x ^ 2 * u t x * Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x +
        2 * cutoff.toFun x ^ 2 * u t x * source t x
    calc
      _ ≤ (2 * cutoff.toFun x ^ 2 * u t x) *
          (Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x + source t x) :=
        mul_le_mul_of_nonneg_left (hpde x) hcoeff
      _ = _ := by ring
  have hmass := hasDerivAt_localizedL2Mass
    (I := I) (M := M) cutoff u hu t
  have hspatial := caccioppoli_spatial
    (I := I) (M := M) cutoff ut
  have hlap_scale :
      ∫ x, 2 * cutoff.toFun x ^ 2 * u t x *
          Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x ∂μ =
        2 * ∫ x, cutoff.toFun x ^ 2 * ut.toFun x *
          Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    refine ae_of_all μ (fun x => ?_)
    change 2 * cutoff.toFun x ^ 2 * u t x * Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x =
      2 * (cutoff.toFun x ^ 2 * u t x * Δ_g (I := I) g ⟨ut.toFun, ut.smooth⟩ x)
    ring
  change deriv
        (fun s => localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu s)) t +
      localizedDirichletEnergy (I := I) (M := M) cutoff ut ≤
    4 * cutoffGradientError (I := I) (M := M) cutoff ut +
      ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x ∂μ
  rw [hmass.deriv]
  rw [hlap_scale] at htime_le
  linarith

private theorem caccioppoli_of_differential
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    {weight dweight : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hdirichlet : ContinuousOn
      (fun t => localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t)) (Icc a b))
    (hdifferential : ∀ t ∈ Icc a b,
      deriv
          (fun s => localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu s)) t +
          localizedDirichletEnergy (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) ≤
        4 * cutoffGradientError (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) +
          ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g)) :
    weight b * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu b) -
        weight a * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu a) +
        ∫ t in a..b, weight t *
          localizedDirichletEnergy (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) ≤
      ∫ t in a..b,
        dweight t * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) +
          weight t *
            (4 * cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g u hu t) +
              ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let mass : ℝ → ℝ := fun t =>
    localizedL2Mass (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  let dirichlet : ℝ → ℝ := fun t =>
    localizedDirichletEnergy (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  let error : ℝ → ℝ := fun t =>
    cutoffGradientError (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  let forcing : ℝ → ℝ := fun t =>
    ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x ∂μ
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    exact riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  have hmass_smooth : ContDiff ℝ ∞ mass := by
    simpa only [mass] using
      contDiff_localizedL2Mass (I := I) (M := M) cutoff u hu
  have hmass_cont : ContinuousOn mass (Icc a b) := hmass_smooth.continuous.continuousOn
  have hdmass_cont : ContinuousOn (deriv mass) (Icc a b) :=
    (hmass_smooth.continuous_deriv (by simp)).continuousOn
  have hmass_deriv : ∀ t ∈ Icc a b, HasDerivAt mass (deriv mass t) t := by
    intro t _
    exact (hmass_smooth.differentiable (by simp) t).hasDerivAt
  have hweight_cont : ContinuousOn weight (Icc a b) :=
    fun t ht => (hweight t ht).continuousAt.continuousWithinAt
  have hcutoff_grad_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M =>
      g.inner x
        (gradFun (I := I) g cutoff.toFun x)
        (gradFun (I := I) g cutoff.toFun x)) := by
    have h := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
      (grad_g (I := I) g ⟨cutoff.toFun, cutoff.smooth⟩) (grad_g (I := I) g ⟨cutoff.toFun,
        cutoff.smooth⟩)
    simpa only [grad_g_apply] using h
  have hcutoff_grad_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        g.inner p.1
          (gradFun (I := I) g cutoff.toFun p.1)
          (gradFun (I := I) g cutoff.toFun p.1)) :=
    hcutoff_grad_smooth.comp contMDiff_fst
  have hu_swap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => u p.2 p.1) :=
    hu.comp (contMDiff_snd.prodMk contMDiff_fst)
  have hsource_swap : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => source p.2 p.1) :=
    hsource.comp (contMDiff_snd.prodMk contMDiff_fst)
  have herror_integrand : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => u p.2 p.1 ^ 2 *
        g.inner p.1
          (gradFun (I := I) g cutoff.toFun p.1)
          (gradFun (I := I) g cutoff.toFun p.1)) :=
    (hu_swap.pow 2).mul hcutoff_grad_joint
  have herror_cont : ContinuousOn error (Icc a b) := by
    have hsmooth := contDiff_integral_of_jointContMDiff μ
      (fun x t => u t x ^ 2 *
        g.inner x
          (gradFun (I := I) g cutoff.toFun x)
          (gradFun (I := I) g cutoff.toFun x)) herror_integrand
    exact (by simpa only [error, cutoffGradientError, smoothScalarSlice, μ]
      using hsmooth.continuous.continuousOn)
  have hcutoff_joint : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ => cutoff.toFun p.1) :=
    cutoff.smooth.comp contMDiff_fst
  have hforcing_integrand : ContMDiff (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : M × ℝ =>
        2 * cutoff.toFun p.1 ^ 2 * u p.2 p.1 * source p.2 p.1) :=
    ((contMDiff_const.mul (hcutoff_joint.pow 2)).mul hu_swap).mul hsource_swap
  have hforcing_cont : ContinuousOn forcing (Icc a b) := by
    have hsmooth := contDiff_integral_of_jointContMDiff μ
      (fun x t => 2 * cutoff.toFun x ^ 2 * u t x * source t x) hforcing_integrand
    exact (by simpa only [forcing] using hsmooth.continuous.continuousOn)
  have hdissipation : ContinuousOn (fun t => weight t * dirichlet t) (Icc a b) :=
    hweight_cont.mul (by simpa only [dirichlet] using hdirichlet)
  have hrhs : ContinuousOn
      (fun t => dweight t * mass t + weight t * (4 * error t + forcing t))
      (Icc a b) :=
    (hdweight.mul hmass_cont).add
      (hweight_cont.mul ((continuousOn_const.mul herror_cont).add hforcing_cont))
  have hpointwise : ∀ t ∈ Icc a b,
      dweight t * mass t + weight t * deriv mass t + weight t * dirichlet t ≤
        dweight t * mass t + weight t * (4 * error t + forcing t) := by
    intro t ht
    have hdiff := hdifferential t ht
    have hmul := mul_le_mul_of_nonneg_left hdiff (hweight_nonneg t ht)
    change weight t * (deriv mass t + dirichlet t) ≤
      weight t * (4 * error t + forcing t) at hmul
    linarith
  have hresult := weight_mul_energy_inequality
    hab hdweight hweight hdmass_cont hmass_deriv hdissipation hrhs hpointwise
  simpa only [mass, dirichlet, error, forcing, μ] using hresult

theorem caccioppoli
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    {weight dweight : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      deriv (fun s => u s x) t =
        Δ_g (I := I) g ⟨(smoothScalarSlice (I := I) g u hu t).toFun,
          (smoothScalarSlice (I := I) g u hu t).smooth⟩ x + source t x) :
    weight b * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu b) -
        weight a * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu a) +
        ∫ t in a..b, weight t *
          localizedDirichletEnergy (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) ≤
      ∫ t in a..b,
        dweight t * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) +
          weight t *
            (4 * cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g u hu t) +
              ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have hdirichlet : ContinuousOn
      (fun t => localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t)) (Icc a b) :=
    (contDiff_localizedDirichletEnergy (I := I) (M := M) cutoff u hu).continuous.continuousOn
  apply caccioppoli_of_differential
    (I := I) (M := M) cutoff u source hu hsource hab hdweight hweight
      hweight_nonneg hdirichlet
  intro t ht
  exact caccioppoli_differential
    (I := I) (M := M) cutoff u source hu hsource t (hpde t ht)

theorem caccioppoli_of_subsolution
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    {weight dweight : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b)
    (hdweight : ContinuousOn dweight (Icc a b))
    (hweight : ∀ t ∈ Icc a b, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a b, 0 ≤ weight t)
    (hu_nonneg : ∀ t ∈ Icc a b, ∀ x : M, 0 ≤ u t x)
    (hpde : ∀ t ∈ Icc a b, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) g ⟨(smoothScalarSlice (I := I) g u hu t).toFun,
          (smoothScalarSlice (I := I) g u hu t).smooth⟩ x + source t x) :
    weight b * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu b) -
        weight a * localizedL2Mass (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu a) +
        ∫ t in a..b, weight t *
          localizedDirichletEnergy (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) ≤
      ∫ t in a..b,
        dweight t * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) +
          weight t *
            (4 * cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g u hu t) +
              ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x
                ∂(riemannianVolumeMeasure (I := I) (M := M) g)) := by
  have hdirichlet : ContinuousOn
      (fun t => localizedDirichletEnergy (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t)) (Icc a b) :=
    (contDiff_localizedDirichletEnergy (I := I) (M := M) cutoff u hu).continuous.continuousOn
  apply caccioppoli_of_differential
    (I := I) (M := M) cutoff u source hu hsource hab hdweight hweight
      hweight_nonneg hdirichlet
  intro t ht
  exact caccioppoli_differential_of_subsolution
    (I := I) (M := M) cutoff u source hu hsource t (hu_nonneg t ht) (hpde t ht)

theorem caccioppoli_inner_energy_of_subsolution
    {g : SmoothRiemannianMetric I M}
    (cutoff : SmoothScalar g)
    (u source : ℝ → M → ℝ)
    (hu : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => u p.1 p.2))
    (hsource : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => source p.1 p.2))
    {weight dweight : ℝ → ℝ} {a t₀ t₁ A : ℝ}
    (hat₀ : a ≤ t₀) (ht₀t₁ : t₀ ≤ t₁)
    (hdweight : ContinuousOn dweight (Icc a t₁))
    (hweight : ∀ t ∈ Icc a t₁, HasDerivAt weight (dweight t) t)
    (hweight_nonneg : ∀ t ∈ Icc a t₁, 0 ≤ weight t)
    (hweight_a : weight a = 0)
    (hweight_inner : ∀ t ∈ Icc t₀ t₁, weight t = 1)
    (hu_nonneg : ∀ t ∈ Icc a t₁, ∀ x : M, 0 ≤ u t x)
    (hpde : ∀ t ∈ Icc a t₁, ∀ x : M,
      deriv (fun s => u s x) t ≤
        Δ_g (I := I) g ⟨(smoothScalarSlice (I := I) g u hu t).toFun,
          (smoothScalarSlice (I := I) g u hu t).smooth⟩ x + source t x)
    (hrhs_le : ∀ t ∈ Icc t₀ t₁,
      (∫ s in a..t,
        dweight s * localizedL2Mass (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu s) +
          weight s *
            (4 * cutoffGradientError (I := I) (M := M) cutoff
                (smoothScalarSlice (I := I) g u hu s) +
              ∫ x, 2 * cutoff.toFun x ^ 2 * u s x * source s x
                ∂(riemannianVolumeMeasure (I := I) (M := M) g))) ≤ A) :
    (∀ t ∈ Icc t₀ t₁,
      localizedL2Mass (I := I) (M := M) cutoff
        (smoothScalarSlice (I := I) g u hu t) ≤ A) ∧
      (∫ t in t₀..t₁,
        localizedDirichletEnergy (I := I) (M := M) cutoff
          (smoothScalarSlice (I := I) g u hu t)) ≤ A := by
  let mass : ℝ → ℝ := fun t =>
    localizedL2Mass (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  let dissipation : ℝ → ℝ := fun t =>
    localizedDirichletEnergy (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  have hdirichlet : ContinuousOn dissipation (Icc a t₁) := by
    simpa only [dissipation] using
      (contDiff_localizedDirichletEnergy
        (I := I) (M := M) cutoff u hu).continuous.continuousOn
  let rhs : ℝ → ℝ := fun t =>
    dweight t * mass t +
      weight t *
        (4 * cutoffGradientError (I := I) (M := M) cutoff
            (smoothScalarSlice (I := I) g u hu t) +
          ∫ x, 2 * cutoff.toFun x ^ 2 * u t x * source t x
            ∂(riemannianVolumeMeasure (I := I) (M := M) g))
  apply inner_mass_and_dissipation_le
    (weight := weight) (mass := mass) (dissipation := dissipation) (source := rhs)
    hat₀ ht₀t₁
  · intro t ht
    exact (hweight t ht).continuousAt.continuousWithinAt
  · simpa only [dissipation] using hdirichlet
  · exact hweight_nonneg
  · intro t _
    exact localizedDirichletEnergy_nonneg (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  · exact hweight_a
  · exact hweight_inner
  · intro t _
    exact localizedL2Mass_nonneg (I := I) (M := M) cutoff
      (smoothScalarSlice (I := I) g u hu t)
  · simpa only [rhs, mass] using hrhs_le
  · intro t ht
    have hat : a ≤ t := hat₀.trans ht.1
    have hsubset : Icc a t ⊆ Icc a t₁ := fun s hs =>
      ⟨hs.1, hs.2.trans ht.2⟩
    have henergy := caccioppoli_of_subsolution
      (I := I) (M := M) cutoff u source hu hsource hat
      (hdweight.mono hsubset)
      (fun s hs => hweight s (hsubset hs))
      (fun s hs => hweight_nonneg s (hsubset hs))
      (fun s hs => hu_nonneg s (hsubset hs))
      (fun s hs => hpde s (hsubset hs))
    simpa only [mass, dissipation, rhs] using henergy

end DifferentialGeometry.Analysis.Parabolic.Energy

end
