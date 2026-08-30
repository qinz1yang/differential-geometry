import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Reparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Regularized
import DifferentialGeometry.Geometry.Metric.CurveEnergy
import DifferentialGeometry.Tensor.RSTensor.QuadraticBounds.TimeSlab

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle
open MeasureTheory

universe u uE uH

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {D : RealTimeInterval}

noncomputable def lRegLag
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (s : Real) : Real :=
  let g := S.base.metric (T - s ^ 2)
  let A := lVelocity (I := I) alpha s
  (1 / 2 : Real) * g.inner (alpha s) A A +
    2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)

noncomputable def lRegAction
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (a b : Real) : Real :=
  ∫ s in a..b, lRegLag S T alpha s

end

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegAction_add
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (a b c : Real)
    (hab : IntervalIntegrable (lRegLag S T alpha) volume a b)
    (hbc : IntervalIntegrable (lRegLag S T alpha) volume b c) :
    lRegAction S T alpha a b + lRegAction S T alpha b c =
      lRegAction S T alpha a c := by
  exact intervalIntegral.integral_add_adjacent_intervals hab hbc

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegAction_sum
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) {t : ℕ → Real} {n : ℕ}
    (hint : ∀ k < n,
      IntervalIntegrable (lRegLag S T alpha) volume (t k) (t (k + 1))) :
    (∑ k ∈ Finset.range n, lRegAction S T alpha (t k) (t (k + 1))) =
      lRegAction S T alpha (t 0) (t n) := by
  exact intervalIntegral.sum_integral_adjacent_intervals hint

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegAction_congr
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha beta : Real → M) (a b : Real)
    (h : Set.EqOn alpha beta (Set.uIoo a b)) :
    lRegAction S T alpha a b = lRegAction S T beta a b := by
  unfold lRegAction
  apply intervalIntegral.integral_congr_ae
  filter_upwards
    [MeasureTheory.Measure.ae_ne MeasureTheory.volume (max a b)]
      with s hsmax hs
  change s ∈ Set.Ioc (min a b) (max a b) at hs
  have hsIoo : s ∈ Set.Ioo (min a b) (max a b) :=
    ⟨hs.1, lt_of_le_of_ne hs.2 hsmax⟩
  have hev : alpha =ᶠ[𝓝 s] beta := by
    filter_upwards [Ioo_mem_nhds hsIoo.1 hsIoo.2] with r hr
    exact h (by simpa only [Set.uIoo] using hr)
  have hval : alpha s = beta s := hev.self_of_nhds
  have hmf :
      mfderiv 𝓘(Real, Real) I alpha s =
        mfderiv 𝓘(Real, Real) I beta s :=
    Filter.EventuallyEq.mfderiv_eq (I := 𝓘(Real, Real)) (I' := I) hev
  have hvel : lVelocity (I := I) alpha s = lVelocity (I := I) beta s := by
    with_unfolding_all exact
      (congrArg (fun L => L (1 : Real)) hmf)
  simp only [lRegLag]
  rw [hval, hvel]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lScalar_lower
    [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : ScalarSTContOn (I := I) (M := M) S)
    (T a b : Real)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.carrier) :
    ∃ C : Real, ∀ s ∈ Set.uIcc a b, ∀ x : M,
      C ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) x := by
  let K : Set (Real × M) := Set.uIcc a b ×ˢ (Set.univ : Set M)
  let f : Real × M → Real := fun q =>
    2 * q.1 ^ 2 * S.scalar (T - q.1 ^ 2) q.2
  let phi : Real × M → Real × M := fun q => (T - q.1 ^ 2, q.2)
  have hphi : Continuous phi :=
    (continuous_const.sub (continuous_fst.pow 2)).prodMk continuous_snd
  have hmaps : Set.MapsTo phi K
      (D.carrier ×ˢ (Set.univ : Set M)) := by
    intro q hq
    exact ⟨ht q.1 hq.1, Set.mem_univ q.2⟩
  have hscalar : ContinuousOn
      (fun q : Real × M => S.scalar (T - q.1 ^ 2) q.2) K := by
    simpa only [phi, Function.comp_def] using
      hS.scalar_continuousOn.comp hphi.continuousOn hmaps
  have hf : ContinuousOn f K := by
    exact ((continuous_const.mul (continuous_fst.pow 2)).continuousOn.mul hscalar)
  have hK : IsCompact K := by
    simpa only [K] using isCompact_uIcc.prod isCompact_univ
  obtain ⟨C, hC⟩ := bddBelow_def.mp (hK.bddBelow_image hf)
  refine ⟨C, ?_⟩
  intro s hs x
  exact hC (f (s, x)) ⟨(s, x), ⟨hs, Set.mem_univ x⟩, rfl⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegAction_lower
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (gRef : SmoothRiemannianMetric I M)
    (a b c C : Real) (hab : a ≤ b)
    (hg : ∀ s ∈ Set.Icc a b,
      c * gRef.inner (alpha s) (lVelocity (I := I) alpha s)
          (lVelocity (I := I) alpha s) ≤
        (S.base.metric (T - s ^ 2)).inner (alpha s)
          (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s))
    (hpot : ∀ s ∈ Set.Icc a b,
      C ≤ 2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s))
    (href : IntervalIntegrable
      (fun s => gRef.inner (alpha s) (lVelocity (I := I) alpha s)
        (lVelocity (I := I) alpha s)) volume a b)
    (hLag : IntervalIntegrable (lRegLag S T alpha) volume a b) :
    (∫ s in a..b, (c / 2) *
        gRef.inner (alpha s) (lVelocity (I := I) alpha s)
          (lVelocity (I := I) alpha s)) +
      C * (b - a) ≤ lRegAction S T alpha a b := by
  have href' : IntervalIntegrable
      (fun s => (c / 2) *
        gRef.inner (alpha s) (lVelocity (I := I) alpha s)
          (lVelocity (I := I) alpha s)) volume a b :=
    href.const_mul (c / 2)
  have hmono :
      (∫ s in a..b, (c / 2) *
          gRef.inner (alpha s) (lVelocity (I := I) alpha s)
            (lVelocity (I := I) alpha s) + C) ≤
        ∫ s in a..b, lRegLag S T alpha s := by
    refine intervalIntegral.integral_mono_on hab
      (href'.add intervalIntegrable_const) hLag ?_
    intro s hs
    change
      (c / 2) * gRef.inner (alpha s) (lVelocity (I := I) alpha s)
          (lVelocity (I := I) alpha s) + C ≤
        (1 / 2 : Real) *
            (S.base.metric (T - s ^ 2)).inner (alpha s)
              (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) +
          2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s)
    calc
      (c / 2) * gRef.inner (alpha s) (lVelocity (I := I) alpha s)
            (lVelocity (I := I) alpha s) + C =
          (1 / 2 : Real) *
              (c * gRef.inner (alpha s) (lVelocity (I := I) alpha s)
                (lVelocity (I := I) alpha s)) + C := by ring
      _ ≤ (1 / 2 : Real) *
              (S.base.metric (T - s ^ 2)).inner (alpha s)
                (lVelocity (I := I) alpha s) (lVelocity (I := I) alpha s) +
            2 * s ^ 2 * S.scalar (T - s ^ 2) (alpha s) :=
        add_le_add (mul_le_mul_of_nonneg_left (hg s hs) (by norm_num))
          (hpot s hs)
  rw [intervalIntegral.integral_add href' intervalIntegrable_const,
    intervalIntegral.integral_const] at hmono
  simpa [lRegAction, smul_eq_mul, mul_comm] using hmono

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lAction_consts
    [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T t0 t1 : Real) (gRef : SmoothRiemannianMetric I M)
    (a b : Real) (hab : a ≤ b)
    (htime : Set.Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ Set.Icc t0 t1) :
    ∃ c C : Real, 0 < c ∧
      ∀ alpha : Real → M,
        IntervalIntegrable
            (fun s => gRef.inner (alpha s) (lVelocity (I := I) alpha s)
              (lVelocity (I := I) alpha s)) volume a b →
          IntervalIntegrable (lRegLag S T alpha) volume a b →
            (∫ s in a..b, (c / 2) *
                gRef.inner (alpha s) (lVelocity (I := I) alpha s)
                  (lVelocity (I := I) alpha s)) +
              C * (b - a) ≤ lRegAction S T alpha a b := by
  have hquad :
      Continuous
        (DifferentialGeometry.metricTimeBundleQuad
          (I := I) (M := M) S.family.metric (Set.Icc t0 t1)) :=
    metricTimeBundleQuad_cont_of_metricFamilySmoothOn
      (I := I) (M := M) S.family.metric hS.smoothMetric htime
  obtain ⟨c, hc, hmetric⟩ :=
    DifferentialGeometry.metric_lower_icc
      (I := I) (M := M) S.family.metric t0 t1 gRef hquad
  have hST : ScalarSTContOn (I := I) (M := M) S :=
    ⟨hS.scalarCont⟩
  obtain ⟨C, hscalar⟩ :=
    lScalar_lower (I := I) S hST T a b (by
      intro s hs
      exact htime (hback s (by
        simpa only [Set.uIcc_of_le hab] using hs)))
  refine ⟨c, C, hc, ?_⟩
  intro alpha href hLag
  apply lRegAction_lower (I := I) S T alpha gRef a b c C hab
  · intro s hs
    exact hmetric (T - s ^ 2) (hback s hs) (alpha s)
      (lVelocity (I := I) alpha s)
  · intro s hs
    exact hscalar s (by
      simpa only [Set.uIcc_of_le hab] using hs) (alpha s)
  · exact href
  · exact hLag

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegAction_bound
    [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T t0 t1 : Real) (gRef : SmoothRiemannianMetric I M)
    (alpha : Real → M) (a b : Real) (hab : a ≤ b)
    (htime : Set.Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ Set.Icc t0 t1)
    (href : IntervalIntegrable
      (fun s => gRef.inner (alpha s) (lVelocity (I := I) alpha s)
        (lVelocity (I := I) alpha s)) volume a b)
    (hLag : IntervalIntegrable (lRegLag S T alpha) volume a b) :
    ∃ c C : Real, 0 < c ∧
      (∫ s in a..b, (c / 2) *
          gRef.inner (alpha s) (lVelocity (I := I) alpha s)
            (lVelocity (I := I) alpha s)) +
        C * (b - a) ≤ lRegAction S T alpha a b := by
  obtain ⟨c, C, hc, hall⟩ :=
    lAction_consts (I := I) S hS T t0 t1 gRef a b hab htime hback
  exact ⟨c, C, hc, hall alpha href hLag⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRefEnergy_bound
    [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T t0 t1 : Real) (gRef : SmoothRiemannianMetric I M)
    (a b A : Real) (hab : a ≤ b)
    (htime : Set.Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ Set.Icc t0 t1) :
    ∃ c C : Real, 0 < c ∧
      ∀ alpha : Real → M,
        IntervalIntegrable
            (fun s => gRef.inner (alpha s) (lVelocity (I := I) alpha s)
              (lVelocity (I := I) alpha s)) volume a b →
          IntervalIntegrable (lRegLag S T alpha) volume a b →
            lRegAction S T alpha a b ≤ A →
              DifferentialGeometry.Geometry.Riemannian.curveEnergy
                  (I := I) gRef alpha a b ≤
                (2 / c) * (A - C * (b - a)) := by
  obtain ⟨c, C, hc, hall⟩ :=
    lAction_consts (I := I) S hS T t0 t1 gRef a b hab htime hback
  refine ⟨c, C, hc, ?_⟩
  intro alpha href hLag hA
  have hcoerc := hall alpha href hLag
  change
    (∫ s in a..b, gRef.inner (alpha s) (lVelocity (I := I) alpha s)
        (lVelocity (I := I) alpha s)) ≤
      (2 / c) * (A - C * (b - a))
  have hscaled :
      (c / 2) *
          (∫ s in a..b, gRef.inner (alpha s) (lVelocity (I := I) alpha s)
            (lVelocity (I := I) alpha s)) + C * (b - a) ≤ A := by
    calc
      (c / 2) *
            (∫ s in a..b, gRef.inner (alpha s) (lVelocity (I := I) alpha s)
              (lVelocity (I := I) alpha s)) + C * (b - a) =
          (∫ s in a..b, (c / 2) *
              gRef.inner (alpha s) (lVelocity (I := I) alpha s)
                (lVelocity (I := I) alpha s)) + C * (b - a) := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ lRegAction S T alpha a b := hcoerc
      _ ≤ A := hA
  have henergy :
      (c / 2) *
          (∫ s in a..b, gRef.inner (alpha s) (lVelocity (I := I) alpha s)
            (lVelocity (I := I) alpha s)) ≤ A - C * (b - a) := by
    linarith
  calc
    (∫ s in a..b, gRef.inner (alpha s) (lVelocity (I := I) alpha s)
        (lVelocity (I := I) alpha s)) =
        (2 / c) * ((c / 2) *
          (∫ s in a..b, gRef.inner (alpha s) (lVelocity (I := I) alpha s)
            (lVelocity (I := I) alpha s))) := by
          field_simp
    _ ≤ (2 / c) * (A - C * (b - a)) :=
      mul_le_mul_of_nonneg_left henergy (div_nonneg (by norm_num) hc.le)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lEdistOf_bound
    [CompactSpace M]
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T t0 t1 : Real) (gRef : SmoothRiemannianMetric I M)
    (alpha : Real → M) (a b A : Real) (hab : a ≤ b)
    (htime : Set.Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Set.Icc a b, T - s ^ 2 ∈ Set.Icc t0 t1)
    (halpha : ContMDiffOn 𝓘(Real, Real) I 1 alpha (Set.Icc a b))
    (hE : IntegrableOn
      (fun s => gRef.inner (alpha s) (lVelocity (I := I) alpha s)
        (lVelocity (I := I) alpha s)) (Set.Icc a b))
    (hLag : IntervalIntegrable (lRegLag S T alpha) volume a b)
    (hA : lRegAction S T alpha a b ≤ A) :
    ∃ c C : Real, 0 < c ∧
      ∀ s t, a ≤ s → s ≤ t → t ≤ b →
        DifferentialGeometry.riemannianEDistOf
            (I := I) gRef (alpha s) (alpha t) ≤
          ENNReal.ofReal
            (Real.sqrt (t - s) *
              Real.sqrt ((2 / c) * (A - C * (b - a)))) := by
  have href : IntervalIntegrable
      (fun s => gRef.inner (alpha s) (lVelocity (I := I) alpha s)
        (lVelocity (I := I) alpha s)) volume a b := by
    apply MeasureTheory.IntegrableOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hab] using hE
  obtain ⟨c, C, hc, hbudget⟩ :=
    lRefEnergy_bound (I := I) S hS T t0 t1 gRef a b A hab htime hback
  refine ⟨c, C, hc, ?_⟩
  intro s t has hst htb
  have hsub : Set.Icc s t ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc has htb
  have hsubE :
      DifferentialGeometry.Geometry.Riemannian.curveEnergy
          (I := I) gRef alpha s t ≤
        DifferentialGeometry.Geometry.Riemannian.curveEnergy
          (I := I) gRef alpha a b :=
    DifferentialGeometry.Geometry.Riemannian.curveEnergy_mono
      (I := I) gRef has hst htb hE
  exact DifferentialGeometry.Geometry.Riemannian.edistOf_le_budget
    (I := I) gRef hst (halpha.mono hsub) (hE.mono_set hsub)
      (hsubE.trans (hbudget alpha href hLag hA))

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lRegDensity_eq
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (s : Real) :
    lRegDensity S T gamma s = lRegLag S T (sqReparam gamma) s := by
  rfl

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lLength_reg
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (tau1 tau2 : Real)
    (htau1 : 0 ≤ tau1) (htau2 : 0 ≤ tau2)
    (hgamma : ∀ s ∈ Set.uIcc (Real.sqrt tau1) (Real.sqrt tau2),
      MDifferentiableAt 𝓘(Real, Real) I gamma (s ^ 2)) :
    lLength S T gamma tau1 tau2 =
      lRegAction S T (sqReparam gamma)
        (Real.sqrt tau1) (Real.sqrt tau2) := by
  simpa only [lRegAction, lRegDensity_eq] using
    lLength_sq (I := I) S T gamma tau1 tau2 htau1 htau2 hgamma

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lLength_reg_ae
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (tau1 tau2 : Real)
    (htau1 : 0 ≤ tau1) (htau2 : 0 ≤ tau2) :
    lLength S T gamma tau1 tau2 =
      lRegAction S T (sqReparam gamma)
        (Real.sqrt tau1) (Real.sqrt tau2) := by
  simpa only [lRegAction, lRegDensity_eq] using
    lLength_sq_ae (I := I) S T gamma tau1 tau2 htau1 htau2

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lLength_sqrt
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (alpha : Real → M) (tau : Real) (htau : 0 ≤ tau) :
    lLength S T (sqrtReparam alpha) 0 tau =
      lRegAction S T alpha 0 (Real.sqrt tau) := by
  have hsq := lLength_reg_ae (I := I) S T (sqrtReparam alpha)
    0 tau (by norm_num) htau
  have hsq' : lLength S T (sqrtReparam alpha) 0 tau =
      lRegAction S T (sqReparam (sqrtReparam alpha)) 0
        (Real.sqrt tau) := by
    simpa only [Real.sqrt_zero] using hsq
  have hEq : Set.EqOn (sqReparam (sqrtReparam alpha)) alpha
      (Set.uIoo 0 (Real.sqrt tau)) := by
    intro s hs
    have hs' : s ∈ Set.Ioo 0 (Real.sqrt tau) := by
      simpa only [Set.uIoo_of_le (Real.sqrt_nonneg tau)] using hs
    simp only [sqReparam, sqrtReparam, Real.sqrt_sq hs'.1.le]
  exact hsq'.trans
    (lRegAction_congr (I := I) S T
      (sqReparam (sqrtReparam alpha)) alpha 0 (Real.sqrt tau) hEq)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegLag_deriv
    (S : SolutionOn (I := I) (M := M) D) (T s : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    HasDerivAt (fun u : Real ↦ lRegLag S T (f u) s)
      ((S.base.metric (T - s ^ 2)).inner (f 0 s)
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (f 0) (fun r : Real ↦
              lVelocity (I := I) (fun u : Real ↦ f u r) 0) s)
          (lVelocity (I := I) (f 0) s) +
        2 * s ^ 2 *
          (S.base.metric (T - s ^ 2)).inner (f 0 s)
            (gradientFun (I := I) (S.base.metric (T - s ^ 2))
              (S.scalar (T - s ^ 2)) (f 0 s))
            (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) 0 := by
  let g := S.base.metric (T - s ^ 2)
  have hspeed := speedSq_hasDerivAt (I := I) g f s hf
  rw [commute_ds_dt_intrinsic (I := I) g f hf s] at hspeed
  have hspeed' : HasDerivAt (fun u : Real ↦ speedSq (I := I) g f u s)
      (2 * g.inner (f 0 s)
        (covDerivAlong (I := I) g (f 0)
          (fun r : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u r) 0) s)
        (lVelocity (I := I) (f 0) s)) 0 := by
    simpa only [lVelocity] using hspeed
  have hslice : MDifferentiableAt 𝓘(Real, Real) I
      (fun u : Real ↦ f u s) 0 := by
    have hincl : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : Nat)
        (fun u : Real ↦ (u, s)) :=
      contMDiff_id.prodMk contMDiff_const
    exact ((hf : ContMDiff _ _ (8 : Nat) _).comp hincl).contMDiffAt.mdifferentiableAt
      (by norm_num)
  have hscalar := lScalar_var_deriv S (T - s ^ 2 + s) s f hslice
  have hscalar' : HasDerivAt
      (fun u : Real ↦ S.scalar (T - s ^ 2) (f u s))
      ((S.base.metric (T - s ^ 2)).inner (f 0 s)
        (gradientFun (I := I) (S.base.metric (T - s ^ 2))
          (S.scalar (T - s ^ 2)) (f 0 s))
        (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) 0 := by
    convert hscalar using 1 <;> ring_nf
  have hout := (hspeed'.const_mul (1 / 2 : Real)).add
    (hscalar'.const_mul (2 * s ^ 2))
  have hfun : (fun u : Real ↦ lRegLag S T (f u) s) =
      (fun y ↦ (1 / 2 : Real) * speedSq (I := I) g f y s) +
        (fun y ↦ 2 * s ^ 2 * S.scalar (T - s ^ 2) (f y s)) := by
    funext u
    rfl
  rw [← hfun] at hout
  refine hout.congr_deriv ?_
  with_unfolding_all
    ring

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lRegScalar_c2
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real ↦ S.scalar (T - p.2 ^ 2) (f p.1 p.2))
      {p : Real × Real | T - p.2 ^ 2 ∈ D.regular} := by
  intro p hp
  have hfAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ f q.1 q.2) p :=
    (hf : ContMDiff _ _ (8 : Nat) _).contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ (T - q.2 ^ 2, f q.1 q.2)) p :=
    (contMDiffAt_const.sub (contMDiffAt_snd.pow 2)).prodMk hfAt
  have hscalar₀ : ContMDiffAt
      (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun q : Real × M ↦ S.scalar q.1 q.2)
      (T - p.2 ^ 2, f p.1 p.2) :=
    (scalar_joint (I := I) S hS).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds hp) Filter.univ_mem)
  have hscalarMD : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ S.scalar (T - q.2 ^ 2) (f q.1 q.2)) p :=
    (hscalar₀.of_le (by
      change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)).comp p harg
  have hscalar : ContDiffAt Real 2
      (fun q : Real × Real ↦ S.scalar (T - q.2 ^ 2) (f q.1 q.2)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalarMD
  exact hscalar.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lRegSpeed_c2
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real ↦
        (S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
          (lVelocity (I := I) (f p.1) p.2)
          (lVelocity (I := I) (f p.1) p.2))
      {p : Real × Real | T - p.2 ^ 2 ∈ D.regular} := by
  intro p hp
  have hfAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ f q.1 q.2) p :=
    (hf : ContMDiff _ _ (8 : Nat) _).contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ (T - q.2 ^ 2, f q.1 q.2)) p :=
    (contMDiffAt_const.sub (contMDiffAt_snd.pow 2)).prodMk hfAt
  have hmetric₀ := hS.smoothMetric.metricCLMSmoothAt
    (t := T - p.2 ^ 2) (x := f p.1 p.2)
    (D.regular_isOpen.mem_nhds hp)
  have hmetric : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y ↦ TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (f q.1 q.2) ((S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2))) p := by
    have hcomp := (hmetric₀.of_le (by
        change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
        exact WithTop.coe_le_coe.mpr le_top)).comp p harg
    rw [SolutionOn.family_metric] at hcomp
    with_unfolding_all exact hcomp
  have hvel : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2) : TangentBundle I M)) p := by
    simpa only [lVelocity] using
      ((velocity_totalSpace_contMDiff (I := I) (M := M) f hf) p).of_le
        (by norm_num)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun y : M ↦ TangentSpace I y)
    (E₂ := fun y : M ↦ TangentSpace I y)
    (E₃ := fun _ : M ↦ Real) hmetric hvel hvel
  have hscalar : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        (S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2)
          (lVelocity (I := I) (f q.1) q.2)) p := by
    rw [Bundle.contMDiffAt_totalSpace] at htotal
    with_unfolding_all exact htotal.2
  have hcd : ContDiffAt Real 2
      (fun q : Real × Real ↦
        (S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2)
          (lVelocity (I := I) (f q.1) q.2)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalar
  exact hcd.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lRegPair_c2
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real ↦
        (S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
          (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
          (lVelocity (I := I) (f p.1) p.2))
      {p : Real × Real | T - p.2 ^ 2 ∈ D.regular} := by
  have hswap : IsSmoothVariation (I := I)
      (fun a b : Real ↦ f b a) := by
    exact (hf : ContMDiff _ _ (8 : Nat) _).comp
      (contMDiff_snd.prodMk contMDiff_fst)
  have hYall : ContMDiff
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E))
      (7 : Nat)
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (fun u : Real ↦ f u q.2) q.1) :
            TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff
      (I := I) (M := M) (fun a b : Real ↦ f b a) hswap
    have hcomp := hbase.comp
      (contMDiff_snd.prodMk contMDiff_fst :
        ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real))
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (7 : Nat)
          (fun q : Real × Real ↦ (q.2, q.1)))
    with_unfolding_all exact hcomp
  have hXall := velocity_totalSpace_contMDiff (I := I) (M := M) f hf
  intro p hp
  have hfAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ f q.1 q.2) p :=
    (hf : ContMDiff _ _ (8 : Nat) _).contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ (T - q.2 ^ 2, f q.1 q.2)) p :=
    (contMDiffAt_const.sub (contMDiffAt_snd.pow 2)).prodMk hfAt
  have hmetric₀ := hS.smoothMetric.metricCLMSmoothAt
    (t := T - p.2 ^ 2) (x := f p.1 p.2)
    (D.regular_isOpen.mem_nhds hp)
  have hmetric : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y ↦ TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (f q.1 q.2) ((S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2))) p := by
    have hcomp := (hmetric₀.of_le (by
        change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
        exact WithTop.coe_le_coe.mpr le_top)).comp p harg
    rw [SolutionOn.family_metric] at hcomp
    with_unfolding_all exact hcomp
  have hY : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E))
      (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (fun u : Real ↦ f u q.2) q.1) :
            TangentBundle I M)) p :=
    hYall.contMDiffAt.of_le (by norm_num)
  have hX : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E))
      (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2) : TangentBundle I M)) p := by
    simpa only [lVelocity] using hXall.contMDiffAt.of_le (by norm_num)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun y : M ↦ TangentSpace I y)
    (E₂ := fun y : M ↦ TangentSpace I y)
    (E₃ := fun _ : M ↦ Real) hmetric hY hX
  have hscalar : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        (S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2)
          (lVelocity (I := I) (fun u : Real ↦ f u q.2) q.1)
          (lVelocity (I := I) (f q.1) q.2)) p := by
    rw [Bundle.contMDiffAt_totalSpace] at htotal
    with_unfolding_all exact htotal.2
  have hcd : ContDiffAt Real 2
      (fun q : Real × Real ↦
        (S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2)
          (lVelocity (I := I) (fun u : Real ↦ f u q.2) q.1)
          (lVelocity (I := I) (f q.1) q.2)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalar
  exact hcd.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lRegLag_c2
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real ↦ lRegLag S T (f p.1) p.2)
      {p : Real × Real | T - p.2 ^ 2 ∈ D.regular} := by
  have hscalar := lRegScalar_c2 (I := I) S hS T f hf
  have hspeed := lRegSpeed_c2 (I := I) S hS T f hf
  simpa only [lRegLag] using
    (contDiffOn_const.mul hspeed).add
      ((contDiffOn_const.mul (contDiffOn_snd.pow 2)).mul hscalar)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegAction_deriv
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular) :
    HasDerivAt (fun u : Real ↦ lRegAction S T (f u) a b)
      (∫ s in a..b,
        (S.base.metric (T - s ^ 2)).inner (f 0 s)
            (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
              (f 0) (fun r : Real ↦
                lVelocity (I := I) (fun u : Real ↦ f u r) 0) s)
            (lVelocity (I := I) (f 0) s) +
          2 * s ^ 2 *
            (S.base.metric (T - s ^ 2)).inner (f 0 s)
              (gradientFun (I := I) (S.base.metric (T - s ^ 2))
                (S.scalar (T - s ^ 2)) (f 0 s))
              (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) 0 := by
  let U : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ^ 2 ∈ D.regular}
  let lag : Real → Real → Real := fun u s ↦ lRegLag S T (f u) s
  let dLag : Real → Real → Real := fun u s ↦
    fderiv Real (fun p : Real × Real ↦ lRegLag S T (f p.1) p.2)
      (u, s) (1, 0)
  have hUopen : IsOpen U :=
    D.regular_isOpen.preimage
      (continuous_const.sub (continuous_snd.pow 2))
  have hlag2 : ContDiffOn Real 2
      (fun p : Real × Real ↦ lRegLag S T (f p.1) p.2) U := by
    simpa only [U] using lRegLag_c2 (I := I) S hS T f hf
  have hlag1 : ContDiffOn Real 1
      (fun p : Real × Real ↦ lRegLag S T (f p.1) p.2) U :=
    hlag2.of_le (by norm_num)
  have hlagJoint : ContinuousOn
      (fun p : Real × Real ↦ lRegLag S T (f p.1) p.2) U :=
    hlag2.continuousOn
  have hfd : ContinuousOn
      (fderiv Real (fun p : Real × Real ↦ lRegLag S T (f p.1) p.2)) U :=
    hlag1.continuousOn_fderiv_of_isOpen hUopen (by norm_num)
  have hdJoint : ContinuousOn (fun p : Real × Real ↦ dLag p.1 p.2) U := by
    simpa only [dLag] using hfd.clm_apply continuousOn_const
  have hlagCont (u : Real) : ContinuousOn (lag u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ (u, s)) (Set.uIcc a b) :=
      continuousOn_const.prodMk continuousOn_id
    apply hlagJoint.comp hmap
    intro s hs
    exact ht s hs
  have hdCont (u : Real) : ContinuousOn (dLag u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ (u, s)) (Set.uIcc a b) :=
      continuousOn_const.prodMk continuousOn_id
    apply hdJoint.comp hmap
    intro s hs
    exact ht s hs
  have hlagDiff : DifferentiableOn Real
      (fun p : Real × Real ↦ lRegLag S T (f p.1) p.2) U :=
    hlag1.differentiableOn (by norm_num)
  have hslice (u s : Real) (hs : s ∈ Set.uIcc a b) :
      HasDerivAt (fun z : Real ↦ lag z s) (dLag u s) u := by
    have hpU : (u, s) ∈ U := ht s hs
    have hat := (hlagDiff (u, s) hpU).differentiableAt
      (hUopen.mem_nhds hpU)
    simpa only [lag, dLag] using Aux2.hasDerivAt_slice_fst
      (fun z r : Real ↦ lRegLag S T (f z) r) u s hat
  let K : Set (Real × Real) := Set.Icc (-1 : Real) 1 ×ˢ Set.uIcc a b
  have hKcompact : IsCompact K := by
    simpa only [K] using isCompact_Icc.prod isCompact_uIcc
  have hKsub : K ⊆ U := by
    intro p hp
    exact ht p.2 hp.2
  obtain ⟨C, hC⟩ :=
    hKcompact.bddAbove_image (hdJoint.mono hKsub).norm
  let C₀ : Real := max C 0
  have hC₀ : ∀ p ∈ K, ‖dLag p.1 p.2‖ ≤ C₀ := by
    intro p hp
    exact (hC ⟨p, hp, rfl⟩).trans (le_max_left C 0)
  have hnhds : Set.Icc (-1 : Real) 1 ∈ 𝓝 (0 : Real) :=
    Icc_mem_nhds (by norm_num) (by norm_num)
  have hmeas : ∀ᶠ u in 𝓝 (0 : Real),
      AEStronglyMeasurable (lag u)
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    Filter.Eventually.of_forall fun u ↦
      (hlagCont u).aestronglyMeasurable_of_subset_isCompact
        isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hint : IntervalIntegrable (lag 0) MeasureTheory.volume a b :=
    (hlagCont 0).intervalIntegrable
  have hdmeas : AEStronglyMeasurable (dLag 0)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    (hdCont 0).aestronglyMeasurable_of_subset_isCompact
      isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hbound : ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        ‖dLag u s‖ ≤ (fun _ : Real ↦ C₀) s :=
    Filter.Eventually.of_forall fun s hs u hu ↦
      hC₀ (u, s) ⟨hu, Set.uIoc_subset_uIcc hs⟩
  have hboundInt : IntervalIntegrable (fun _ : Real ↦ C₀)
      MeasureTheory.volume a b := continuousOn_const.intervalIntegrable
  have hdiff : ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        HasDerivAt (fun z : Real ↦ lag z s) (dLag u s) u :=
    Filter.Eventually.of_forall fun s hs u _ ↦
      hslice u s (Set.uIoc_subset_uIcc hs)
  have hparam :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := lag) (F' := dLag) (x₀ := (0 : Real))
      (s := Set.Icc (-1 : Real) 1) (a := a) (b := b)
      (bound := fun _ : Real ↦ C₀) hnhds hmeas hint hdmeas
      hbound hboundInt hdiff
  let raw : Real → Real := fun s ↦
    (S.base.metric (T - s ^ 2)).inner (f 0 s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (f 0) (fun r : Real ↦
            lVelocity (I := I) (fun u : Real ↦ f u r) 0) s)
        (lVelocity (I := I) (f 0) s) +
      2 * s ^ 2 *
        (S.base.metric (T - s ^ 2)).inner (f 0 s)
          (gradientFun (I := I) (S.base.metric (T - s ^ 2))
            (S.scalar (T - s ^ 2)) (f 0 s))
          (lVelocity (I := I) (fun u : Real ↦ f u s) 0)
  have heq : Set.EqOn (dLag 0) raw (Set.uIcc a b) := by
    intro s hs
    exact (hslice 0 s hs).unique (by
      simpa only [lag, raw] using lRegLag_deriv (I := I) S T s f hf)
  have heqInt : (∫ s in a..b, dLag 0 s) = ∫ s in a..b, raw s :=
    intervalIntegral.integral_congr heq
  rw [heqInt] at hparam
  simpa only [lRegAction, lag, raw] using hparam.2

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegEuler_var_c1
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 1
      (fun p : Real × Real ↦
        lRegEulerPair S T (f p.1) p.2
          (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1))
      {p : Real × Real | T - p.2 ^ 2 ∈ D.regular} := by
  let U : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ^ 2 ∈ D.regular}
  let pair : Real × Real → Real := fun p ↦
    (S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
      (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
      (lVelocity (I := I) (f p.1) p.2)
  let lag : Real × Real → Real := fun p ↦ lRegLag S T (f p.1) p.2
  let dPair : Real × Real → Real := fun p ↦
    fderiv Real pair p (0, 1)
  let dLag : Real × Real → Real := fun p ↦
    fderiv Real lag p (1, 0)
  let raw : Real × Real → Real := fun p ↦ dPair p - dLag p
  let euler : Real × Real → Real := fun p ↦
    lRegEulerPair S T (f p.1) p.2
      (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
  have hUopen : IsOpen U :=
    D.regular_isOpen.preimage
      (continuous_const.sub (continuous_snd.pow 2))
  have hpair2 : ContDiffOn Real 2 pair U := by
    simpa only [pair, U] using lRegPair_c2 (I := I) S hS T f hf
  have hlag2 : ContDiffOn Real 2 lag U := by
    simpa only [lag, U] using lRegLag_c2 (I := I) S hS T f hf
  have hdPair : ContDiffOn Real 1 dPair U := by
    have hfd : ContDiffOn Real 1 (fderiv Real pair) U :=
      hpair2.fderiv_of_isOpen hUopen (by norm_num)
    simpa only [dPair] using hfd.clm_apply contDiffOn_const
  have hdLag : ContDiffOn Real 1 dLag U := by
    have hfd : ContDiffOn Real 1 (fderiv Real lag) U :=
      hlag2.fderiv_of_isOpen hUopen (by norm_num)
    simpa only [dLag] using hfd.clm_apply contDiffOn_const
  have hraw : ContDiffOn Real 1 raw U := by
    simpa only [raw] using hdPair.sub hdLag
  have hpairDiff : DifferentiableOn Real pair U :=
    hpair2.differentiableOn (by norm_num)
  have hlagDiff : DifferentiableOn Real lag U :=
    hlag2.differentiableOn (by norm_num)
  have heq : Set.EqOn euler raw U := by
    intro p hp
    let fp : Real → Real → M := fun a s ↦ f (p.1 + a) s
    have hfp : IsSmoothVariation (I := I) fp := by
      exact (hf : ContMDiff _ _ (8 : Nat) _).comp
        ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
    have hfp0 : fp 0 = f p.1 := by
      funext s
      simp only [fp, add_zero]
    have hYshift (s : Real) :
        lVelocity (I := I) (fun a : Real ↦ fp a s) 0 =
          lVelocity (I := I) (fun a : Real ↦ f a s) p.1 := by
      simpa only [fp, lVelocity, varFst] using
        varFst_shift (I := I) f hf p.1 s
    have hYfun :
        (fun s : Real ↦ lVelocity (I := I) (fun a : Real ↦ fp a s) 0) =
          fun s : Real ↦
            lVelocity (I := I) (fun a : Real ↦ f a s) p.1 :=
      funext hYshift
    have hpairAt : DifferentiableAt Real pair p :=
      (hpairDiff p hp).differentiableAt (hUopen.mem_nhds hp)
    have hlagAt : DifferentiableAt Real lag p :=
      (hlagDiff p hp).differentiableAt (hUopen.mem_nhds hp)
    have hpairSlice : HasDerivAt
        (fun s : Real ↦ pair (p.1, s)) (dPair p) p.2 := by
      simpa only [dPair] using Aux2.hasDerivAt_slice_snd
        (fun u s : Real ↦ pair (u, s)) p.1 p.2 hpairAt
    have hlagSlice : HasDerivAt
        (fun u : Real ↦ lag (u, p.2)) (dLag p) p.1 := by
      simpa only [dLag] using Aux2.hasDerivAt_slice_fst
        (fun u s : Real ↦ lag (u, s)) p.1 p.2 hlagAt
    have hlagShift : HasDerivAt
        (fun u : Real ↦ lag (p.1 + u, p.2)) (dLag p) 0 :=
      HasDerivAt.comp_const_add p.1 0 (by
        simpa only [add_zero] using hlagSlice)
    have hlagGeom := lRegLag_deriv (I := I) S T p.2 fp hfp
    rw [hfp0, hYfun, hYshift p.2] at hlagGeom
    have hdLagEq := hlagShift.unique (by
      simpa only [lag, fp] using hlagGeom)
    have hcentral : MDifferentiableAt 𝓘(Real, Real) I (fp 0) p.2 := by
      have hline : ContMDiff 𝓘(Real, Real)
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : Nat)
          (fun s : Real ↦ ((0 : Real), s)) :=
        contMDiff_const.prodMk contMDiff_id
      have hcomp := (hfp : ContMDiff _ _ (8 : Nat) _).comp hline
      exact hcomp.contMDiffAt.mdifferentiableAt (by norm_num)
    have hYdiff : DifferentiableAt Real
        (chartRepAt (I := I) (fp 0)
          (fun s : Real ↦
            lVelocity (I := I) (fun a : Real ↦ fp a s) 0) p.2) p.2 := by
      with_unfolding_all exact
        (variationField_chartRep_differentiableAt (I := I) fp hfp p.2)
    have hAdiff : DifferentiableAt Real
        (chartRepAt (I := I) (fp 0)
          (fun s : Real ↦ lVelocity (I := I) (fp 0) s) p.2) p.2 := by
      with_unfolding_all exact
        (velocityField_chartRep_differentiableAt (I := I) fp hfp p.2)
    have hpairGeom := lRegInner_deriv (I := I) S hS T (fp 0)
      (fun s : Real ↦ lVelocity (I := I) (fun a : Real ↦ fp a s) 0)
      (fun s : Real ↦ lVelocity (I := I) (fp 0) s) p.2 hp
      hcentral hYdiff hAdiff
    rw [hfp0, hYfun, hYshift p.2] at hpairGeom
    have hpairFun :
        (fun r : Real ↦
          (S.base.metric (T - r ^ 2)).inner (f p.1 r)
            (lVelocity (I := I) (fun a : Real ↦ fp a r) 0)
            (lVelocity (I := I) (f p.1) r)) =
          fun r : Real ↦ pair (p.1, r) := by
      funext r
      rw [hYshift r]
    rw [hpairFun] at hpairGeom
    have hdPairEq : dPair p =
        ((S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
              (covDerivAlong (I := I) (S.base.metric (T - p.2 ^ 2))
                (f p.1) (fun r : Real ↦
                  lVelocity (I := I) (fun u : Real ↦ f u r) p.1) p.2)
              (lVelocity (I := I) (f p.1) p.2) +
            (S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
              (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
              (covDerivAlong (I := I) (S.base.metric (T - p.2 ^ 2))
                (f p.1) (fun r : Real ↦
                  lVelocity (I := I) (f p.1) r) p.2)) +
          4 * p.2 * S.ricciAt (T - p.2 ^ 2) (f p.1 p.2)
            (vec2
              (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
              (lVelocity (I := I) (f p.1) p.2)) := by
      exact hpairSlice.unique hpairGeom
    dsimp only [euler, raw]
    rw [hdPairEq, hdLagEq]
    simp only [lRegEulerPair]
    rw [((S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
      (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)).map_sub]
    rw [lRegAccel_inner]
    ring
  have hout : ContDiffOn Real 1 euler U :=
    hraw.congr (fun p hp ↦ heq hp)
  simpa only [euler, U] using hout

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lRegAction_first
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real)
    (ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular) :
    HasDerivAt (fun u : Real ↦ lRegAction S T (f u) a b)
      ((S.base.metric (T - b ^ 2)).inner (f 0 b)
            (lVelocity (I := I) (fun u : Real ↦ f u b) 0)
            (lVelocity (I := I) (f 0) b) -
        (S.base.metric (T - a ^ 2)).inner (f 0 a)
            (lVelocity (I := I) (fun u : Real ↦ f u a) 0)
            (lVelocity (I := I) (f 0) a) -
        ∫ s in a..b,
          lRegEulerPair S T (f 0) s
            (lVelocity (I := I) (fun u : Real ↦ f u s) 0)) 0 := by
  let U : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ^ 2 ∈ D.regular}
  let pair : Real × Real → Real := fun p ↦
    (S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
      (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
      (lVelocity (I := I) (f p.1) p.2)
  let dPair : Real → Real := fun s ↦
    fderiv Real pair (0, s) (0, 1)
  let B : Real → Real := fun s ↦ pair (0, s)
  let raw : Real → Real := fun s ↦
    (S.base.metric (T - s ^ 2)).inner (f 0 s)
        (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (f 0) (fun r : Real ↦
            lVelocity (I := I) (fun u : Real ↦ f u r) 0) s)
        (lVelocity (I := I) (f 0) s) +
      2 * s ^ 2 *
        (S.base.metric (T - s ^ 2)).inner (f 0 s)
          (gradientFun (I := I) (S.base.metric (T - s ^ 2))
            (S.scalar (T - s ^ 2)) (f 0 s))
          (lVelocity (I := I) (fun u : Real ↦ f u s) 0)
  let Eul : Real → Real := fun s ↦
    lRegEulerPair S T (f 0) s
      (lVelocity (I := I) (fun u : Real ↦ f u s) 0)
  have hUopen : IsOpen U :=
    D.regular_isOpen.preimage
      (continuous_const.sub (continuous_snd.pow 2))
  have hpair2 : ContDiffOn Real 2 pair U := by
    simpa only [pair, U] using lRegPair_c2 (I := I) S hS T f hf
  have hpairDiff : DifferentiableOn Real pair U :=
    hpair2.differentiableOn (by norm_num)
  have hpair1 : ContDiffOn Real 1 pair U :=
    hpair2.of_le (by norm_num)
  have hfd : ContinuousOn (fderiv Real pair) U :=
    hpair1.continuousOn_fderiv_of_isOpen hUopen (by norm_num)
  have hdJoint : ContinuousOn
      (fun p : Real × Real ↦ fderiv Real pair p (0, 1)) U :=
    hfd.clm_apply continuousOn_const
  have hdCont : ContinuousOn dPair (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ ((0 : Real), s))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hdJoint.comp hmap
    intro s hs
    exact ht s hs
  have hBslice : ∀ s ∈ Set.uIcc a b, HasDerivAt B (dPair s) s := by
    intro s hs
    have hp : ((0 : Real), s) ∈ U := ht s hs
    have hat : DifferentiableAt Real pair (0, s) :=
      (hpairDiff (0, s) hp).differentiableAt (hUopen.mem_nhds hp)
    simpa only [B, dPair] using Aux2.hasDerivAt_slice_snd
      (fun u r : Real ↦ pair (u, r)) 0 s hat
  have hdBint : IntervalIntegrable (deriv B)
      MeasureTheory.volume a b := by
    exact hdCont.intervalIntegrable.congr (fun s hs ↦
      (hBslice s (Set.uIoc_subset_uIcc hs)).deriv.symm)
  have hEulJoint : ContinuousOn
      (fun p : Real × Real ↦
        lRegEulerPair S T (f p.1) p.2
          (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)) U := by
    simpa only [U] using (lRegEuler_var_c1 (I := I) S hS T f hf).continuousOn
  have hEulCont : ContinuousOn Eul (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ ((0 : Real), s))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hEulJoint.comp hmap
    intro s hs
    exact ht s hs
  have hEulInt : IntervalIntegrable Eul MeasureTheory.volume a b :=
    hEulCont.intervalIntegrable
  have hBgeom : ∀ s ∈ Set.uIcc a b,
      HasDerivAt B (raw s + Eul s) s := by
    intro s hs
    have hcentral : MDifferentiableAt 𝓘(Real, Real) I (f 0) s := by
      have hline : ContMDiff 𝓘(Real, Real)
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : Nat)
          (fun r : Real ↦ ((0 : Real), r)) :=
        contMDiff_const.prodMk contMDiff_id
      have hcomp := (hf : ContMDiff _ _ (8 : Nat) _).comp hline
      exact hcomp.contMDiffAt.mdifferentiableAt (by norm_num)
    have hYdiff : DifferentiableAt Real
        (chartRepAt (I := I) (f 0)
          (fun r : Real ↦
            lVelocity (I := I) (fun u : Real ↦ f u r) 0) s) s := by
      with_unfolding_all exact
        (variationField_chartRep_differentiableAt (I := I) f hf s)
    have hAdiff : DifferentiableAt Real
        (chartRepAt (I := I) (f 0)
          (fun r : Real ↦ lVelocity (I := I) (f 0) r) s) s := by
      with_unfolding_all exact
        (velocityField_chartRep_differentiableAt (I := I) f hf s)
    have hinner := lRegInner_deriv (I := I) S hS T (f 0)
      (fun r : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u r) 0)
      (fun r : Real ↦ lVelocity (I := I) (f 0) r) s (ht s hs)
      hcentral hYdiff hAdiff
    convert hinner using 1
    simp only [raw, Eul, lRegEulerPair]
    rw [((S.base.metric (T - s ^ 2)).inner (f 0 s)
      (lVelocity (I := I) (fun u : Real ↦ f u s) 0)).map_sub]
    rw [lRegAccel_inner]
    ring
  have hftc := intervalIntegral.integral_deriv_eq_sub
    (fun s hs ↦ (hBslice s hs).differentiableAt) hdBint
  have hrawEq : (∫ s in a..b, raw s) =
      B b - B a - ∫ s in a..b, Eul s := by
    calc
      (∫ s in a..b, raw s) =
          ∫ s in a..b, (deriv B s - Eul s) := by
            apply intervalIntegral.integral_congr
            intro s hs
            have hderiv := (hBgeom s hs).deriv
            linarith
      _ = (∫ s in a..b, deriv B s) - ∫ s in a..b, Eul s :=
        intervalIntegral.integral_sub hdBint hEulInt
      _ = B b - B a - ∫ s in a..b, Eul s := by rw [hftc]
  have hact : HasDerivAt (fun u : Real ↦ lRegAction S T (f u) a b)
      (∫ s in a..b, raw s) 0 := by
    simpa only [raw] using lRegAction_deriv (I := I) S hS T f hf a b ht
  apply hact.congr_deriv
  simpa only [B, pair, Eul] using hrawEq

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegEulerInt_deriv
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (x : M) (Z : TangentSpace I x)
    (hgeo : IsLRegCurveOn S T (f 0) (Set.uIcc a b) x Z) :
    HasDerivAt
      (fun u : Real ↦
        ∫ s in a..b,
          -lRegEulerPair S T (f u) s
            (lVelocity (I := I) (fun v : Real ↦ f v s) u))
      (-(∫ s in a..b,
        lRegJacobiPair S T (f 0)
          (fun r : Real ↦
            lVelocity (I := I) (fun u : Real ↦ f u r) 0)
          s (lVelocity (I := I) (fun u : Real ↦ f u s) 0))) 0 := by
  let U : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ^ 2 ∈ D.regular}
  let F : Real → Real → Real := fun u s ↦
    -lRegEulerPair S T (f u) s
      (lVelocity (I := I) (fun v : Real ↦ f v s) u)
  let dF : Real → Real → Real := fun u s ↦
    fderiv Real (fun p : Real × Real ↦ F p.1 p.2) (u, s) (1, 0)
  let J : Real → Real := fun s ↦
    -lRegJacobiPair S T (f 0)
      (fun r : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u r) 0)
      s (lVelocity (I := I) (fun u : Real ↦ f u s) 0)
  have ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo.2.2 s hs).1
  have hUopen : IsOpen U :=
    D.regular_isOpen.preimage
      (continuous_const.sub (continuous_snd.pow 2))
  have hFJoint : ContDiffOn Real 1
      (fun p : Real × Real ↦ F p.1 p.2) U := by
    simpa only [F, U] using (lRegEuler_var_c1 (I := I) S hS T f hf).neg
  have hFContJoint : ContinuousOn
      (fun p : Real × Real ↦ F p.1 p.2) U :=
    hFJoint.continuousOn
  have hfdCont : ContinuousOn
      (fderiv Real (fun p : Real × Real ↦ F p.1 p.2)) U :=
    hFJoint.continuousOn_fderiv_of_isOpen hUopen (by norm_num)
  have hdFJoint : ContinuousOn
      (fun p : Real × Real ↦ dF p.1 p.2) U := by
    simpa only [dF] using hfdCont.clm_apply continuousOn_const
  have hFCont (u : Real) : ContinuousOn (F u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ (u, s))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hFContJoint.comp hmap
    intro s hs
    exact ht s hs
  have hdFCont (u : Real) : ContinuousOn (dF u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ (u, s))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hdFJoint.comp hmap
    intro s hs
    exact ht s hs
  have hFDiff : DifferentiableOn Real
      (fun p : Real × Real ↦ F p.1 p.2) U :=
    hFJoint.differentiableOn (by norm_num)
  have hFDeriv (u s : Real) (hs : s ∈ Set.uIcc a b) :
      HasDerivAt (fun z : Real ↦ F z s) (dF u s) u := by
    have hpU : (u, s) ∈ U := ht s hs
    have hFAt : DifferentiableAt Real
        (fun p : Real × Real ↦ F p.1 p.2) (u, s) :=
      (hFDiff (u, s) hpU).differentiableAt (hUopen.mem_nhds hpU)
    simpa only [dF] using Aux2.hasDerivAt_slice_fst
      (fun z r : Real ↦ F z r) u s hFAt
  let K : Set (Real × Real) :=
    Set.Icc (-1 : Real) 1 ×ˢ Set.uIcc a b
  have hKcompact : IsCompact K := by
    simpa only [K] using isCompact_Icc.prod isCompact_uIcc
  have hKsub : K ⊆ U := by
    intro p hp
    exact ht p.2 hp.2
  obtain ⟨C, hC⟩ :=
    hKcompact.bddAbove_image (hdFJoint.mono hKsub).norm
  let C₀ : Real := max C 0
  have hC₀ : ∀ p ∈ K, ‖dF p.1 p.2‖ ≤ C₀ := by
    intro p hp
    exact (hC ⟨p, hp, rfl⟩).trans (le_max_left C 0)
  have hnhds : Set.Icc (-1 : Real) 1 ∈ 𝓝 (0 : Real) :=
    Icc_mem_nhds (by norm_num) (by norm_num)
  have hFmeas : ∀ᶠ u in 𝓝 (0 : Real),
      AEStronglyMeasurable (F u)
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    Filter.Eventually.of_forall fun u ↦
      (hFCont u).aestronglyMeasurable_of_subset_isCompact
        isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hFint : IntervalIntegrable (F 0) MeasureTheory.volume a b :=
    (hFCont 0).intervalIntegrable
  have hF'meas : AEStronglyMeasurable (dF 0)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    (hdFCont 0).aestronglyMeasurable_of_subset_isCompact
      isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hbound : ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        ‖dF u s‖ ≤ (fun _ : Real ↦ C₀) s :=
    Filter.Eventually.of_forall fun s hs u hu ↦
      hC₀ (u, s) ⟨hu, Set.uIoc_subset_uIcc hs⟩
  have hboundInt : IntervalIntegrable (fun _ : Real ↦ C₀)
      MeasureTheory.volume a b := continuousOn_const.intervalIntegrable
  have hdiff : ∀ᵐ s ∂MeasureTheory.volume,
      s ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        HasDerivAt (fun z : Real ↦ F z s) (dF u s) u :=
    Filter.Eventually.of_forall fun s hs u _ ↦
      hFDeriv u s (Set.uIoc_subset_uIcc hs)
  have hparam :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := F) (F' := dF) (x₀ := (0 : Real))
      (s := Set.Icc (-1 : Real) 1) (a := a) (b := b)
      (bound := fun _ : Real ↦ C₀) hnhds hFmeas hFint hF'meas
      hbound hboundInt hdiff
  have hJEq : Set.EqOn (dF 0) J (Set.uIcc a b) := by
    intro s hs
    let W : (u : Real) → TangentSpace I (f u s) := fun u ↦
      lVelocity (I := I) (fun v : Real ↦ f v s) u
    have hfAt : ContMDiffAt
        (𝓘(Real, Real).prod 𝓘(Real, Real)) I 3
        (fun p : Real × Real ↦ f p.1 p.2) (0, s) :=
      (hf : ContMDiff _ _ _ _).contMDiffAt.of_le (by norm_num)
    have hslice : ContMDiffAt 𝓘(Real, Real) I 2
        (fun u : Real ↦ f u s) 0 := by
      have hincl : ContMDiff 𝓘(Real, Real)
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : Nat)
          (fun u : Real ↦ (u, s)) :=
        contMDiff_id.prodMk contMDiff_const
      have hcomp := (hf : ContMDiff _ _ (8 : Nat) _).comp hincl
      exact hcomp.contMDiffAt.of_le (by norm_num)
    have hW : DifferentiableAt Real
        (chartRepAt (I := I) (fun u : Real ↦ f u s) W 0) 0 := by
      with_unfolding_all exact
        (DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.velocity_coord_diff
          (I := I) (fun u : Real ↦ f u s) 0 hslice)
    have hpoint := lRegEuler_deriv (I := I) S T s f W hfAt hW
    have hzero :
        lRegEulerPair S T (f 0) s
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (fun u : Real ↦ f u s) W 0) = 0 := by
      simp only [lRegEulerPair]
      rw [(hgeo.2.2 s hs).2.2.2, sub_self, map_zero]
    rw [hzero, add_zero] at hpoint
    have hneg : HasDerivAt (fun u : Real ↦ F u s) (J s) 0 := by
      with_unfolding_all exact hpoint.neg
    exact (hFDeriv 0 s hs).unique hneg
  have hint : (∫ s in a..b, dF 0 s) = ∫ s in a..b, J s :=
    intervalIntegral.integral_congr hJEq
  rw [hint] at hparam
  simpa only [F, J, intervalIntegral.integral_neg] using hparam.2

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem lRegAction_jac
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (x : M) (Z : TangentSpace I x)
    (hgeo : IsLRegCurveOn S T (f 0) (Set.uIcc a b) x Z)
    (hfixa : ∀ u : Real, f u a = f 0 a)
    (hfixb : ∀ u : Real, f u b = f 0 b) :
    HasDerivAt
      (fun u : Real ↦
        deriv (fun v : Real ↦ lRegAction S T (f v) a b) u)
      (-(∫ s in a..b,
        lRegJacobiPair S T (f 0)
          (fun r : Real ↦
            lVelocity (I := I) (fun u : Real ↦ f u r) 0)
          s (lVelocity (I := I) (fun u : Real ↦ f u s) 0))) 0 := by
  let L : Real → Real := fun u ↦ lRegAction S T (f u) a b
  let Eul : Real → Real := fun u ↦
    ∫ s in a..b,
      -lRegEulerPair S T (f u) s
        (lVelocity (I := I) (fun v : Real ↦ f v s) u)
  have ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo.2.2 s hs).1
  have hderivEq (u : Real) : deriv L u = Eul u := by
    let fu : Real → Real → M := fun v s ↦ f (u + v) s
    have hfu : IsSmoothVariation (I := I) fu := by
      exact (hf : ContMDiff _ _ (8 : Nat) _).comp
        ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
    have hfu0 : fu 0 = f u := by
      funext s
      simp only [fu, add_zero]
    have hYshift (s : Real) :
        lVelocity (I := I) (fun v : Real ↦ fu v s) 0 =
          lVelocity (I := I) (fun v : Real ↦ f v s) u := by
      simpa only [fu, lVelocity, varFst] using
        varFst_shift (I := I) f hf u s
    have hYa :
        lVelocity (I := I) (fun v : Real ↦ fu v a) 0 = 0 := by
      have hconst : (fun v : Real ↦ fu v a) = fun _ : Real ↦ f 0 a := by
        funext v
        exact hfixa (u + v)
      rw [hconst]
      simp only [lVelocity, mfderiv_const]
      rfl
    have hYb :
        lVelocity (I := I) (fun v : Real ↦ fu v b) 0 = 0 := by
      have hconst : (fun v : Real ↦ fu v b) = fun _ : Real ↦ f 0 b := by
        funext v
        exact hfixb (u + v)
      rw [hconst]
      simp only [lVelocity, mfderiv_const]
      rfl
    have hshift := lRegAction_first (I := I) S hS T fu hfu a b ht
    rw [hYa, hYb] at hshift
    simp only [map_zero, zero_apply, sub_self, zero_sub]
      at hshift
    rw [hfu0] at hshift
    have hshift' : HasDerivAt (fun v : Real ↦ L (u + v)) (Eul u) 0 := by
      with_unfolding_all
        simpa only [L, Eul, fu, hYshift, intervalIntegral.integral_neg]
          using hshift
    have hderiv := hshift'.deriv
    rw [deriv_comp_const_add L u 0, add_zero] at hderiv
    exact hderiv
  have hEul := lRegEulerInt_deriv (I := I) S hS T f hf a b x Z hgeo
  have hfun : (fun u : Real ↦ deriv L u) = Eul :=
    funext hderivEq
  rw [hfun]
  simpa only [L, Eul] using hEul

omit [InnerProductSpace Real E] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem lRegJacobi_contOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (x : M) (Z : TangentSpace I x)
    (hgeo : IsLRegCurveOn S T (f 0) (Set.uIcc a b) x Z) :
    ContinuousOn
      (fun s : Real ↦
        lRegJacobiPair S T (f 0)
          (fun r : Real ↦
            lVelocity (I := I) (fun u : Real ↦ f u r) 0)
          s (lVelocity (I := I) (fun u : Real ↦ f u s) 0))
      (Set.uIcc a b) := by
  let U : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ^ 2 ∈ D.regular}
  let Eul : Real × Real → Real := fun p ↦
    lRegEulerPair S T (f p.1) p.2
      (lVelocity (I := I) (fun u : Real ↦ f u p.2) p.1)
  let dEul : Real → Real := fun s ↦
    fderiv Real Eul (0, s) (1, 0)
  let J : Real → Real := fun s ↦
    lRegJacobiPair S T (f 0)
      (fun r : Real ↦ lVelocity (I := I) (fun u : Real ↦ f u r) 0)
      s (lVelocity (I := I) (fun u : Real ↦ f u s) 0)
  have ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo.2.2 s hs).1
  have hUopen : IsOpen U :=
    D.regular_isOpen.preimage
      (continuous_const.sub (continuous_snd.pow 2))
  have hEul1 : ContDiffOn Real 1 Eul U := by
    simpa only [Eul, U] using lRegEuler_var_c1 (I := I) S hS T f hf
  have hEulDiff : DifferentiableOn Real Eul U :=
    hEul1.differentiableOn (by norm_num)
  have hdJoint : ContinuousOn
      (fun p : Real × Real ↦ fderiv Real Eul p (1, 0)) U :=
    (hEul1.continuousOn_fderiv_of_isOpen hUopen (by norm_num)).clm_apply
      continuousOn_const
  have hdCont : ContinuousOn dEul (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun s : Real ↦ ((0 : Real), s))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    apply hdJoint.comp hmap
    intro s hs
    exact ht s hs
  have hslice : ∀ s ∈ Set.uIcc a b,
      HasDerivAt (fun u : Real ↦ Eul (u, s)) (dEul s) 0 := by
    intro s hs
    have hp : ((0 : Real), s) ∈ U := ht s hs
    have hat : DifferentiableAt Real Eul (0, s) :=
      (hEulDiff (0, s) hp).differentiableAt (hUopen.mem_nhds hp)
    simpa only [dEul] using Aux2.hasDerivAt_slice_fst
      (fun u r : Real ↦ Eul (u, r)) 0 s hat
  have hdEq : ∀ s ∈ Set.uIcc a b, dEul s = J s := by
    intro s hs
    let W : (u : Real) → TangentSpace I (f u s) := fun u ↦
      lVelocity (I := I) (fun v : Real ↦ f v s) u
    have hfAt : ContMDiffAt
        (𝓘(Real, Real).prod 𝓘(Real, Real)) I 3
        (fun p : Real × Real ↦ f p.1 p.2) (0, s) :=
      (hf : ContMDiff _ _ _ _).contMDiffAt.of_le (by norm_num)
    have hline : ContMDiffAt 𝓘(Real, Real) I 2
        (fun u : Real ↦ f u s) 0 := by
      have hincl : ContMDiff 𝓘(Real, Real)
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : Nat)
          (fun u : Real ↦ (u, s)) :=
        contMDiff_id.prodMk contMDiff_const
      exact ((hf : ContMDiff _ _ _ _).comp hincl).contMDiffAt.of_le
        (by norm_num)
    have hW : DifferentiableAt Real
        (chartRepAt (I := I) (fun u : Real ↦ f u s) W 0) 0 := by
      with_unfolding_all exact
        (DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.velocity_coord_diff
          (I := I) (fun u : Real ↦ f u s) 0 hline)
    have hpoint := lRegEuler_deriv (I := I) S T s f W hfAt hW
    have hzero :
        lRegEulerPair S T (f 0) s
          (covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
            (fun u : Real ↦ f u s) W 0) = 0 := by
      simp only [lRegEulerPair]
      rw [(hgeo.2.2 s hs).2.2.2, sub_self, map_zero]
    rw [hzero, add_zero] at hpoint
    have hpoint' : HasDerivAt (fun u : Real ↦ Eul (u, s)) (J s) 0 := by
      simpa only [Eul, J, W] using hpoint
    exact (hslice s hs).unique hpoint'
  exact hdCont.congr (fun s hs ↦ (hdEq s hs).symm)

omit [InnerProductSpace Real E] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lRegAction_second
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (x : M) (Z : TangentSpace I x)
    (hgeo : IsLRegCurveOn S T (f 0) (Set.uIcc a b) x Z)
    (hfixa : ∀ u : Real, f u a = f 0 a)
    (hfixb : ∀ u : Real, f u b = f 0 b) :
    HasDerivAt
      (fun u : Real ↦
        deriv (fun v : Real ↦ lRegAction S T (f v) a b) u)
      (2 * lRegIndex S T (f 0)
        (fun s : Real ↦
          lVelocity (I := I) (fun u : Real ↦ f u s) 0)
        (fun s : Real ↦
          lVelocity (I := I) (fun u : Real ↦ f u s) 0) a b) 0 := by
  let alpha : Real → M := f 0
  let Y : (s : Real) → TangentSpace I (alpha s) := fun s ↦
    lVelocity (I := I) (fun u : Real ↦ f u s) 0
  let B : Real → Real := fun s ↦
    (S.base.metric (T - s ^ 2)).inner (alpha s)
      (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha Y s)
      (Y s)
  let J : Real → Real := fun s ↦
    lRegJacobiPair S T alpha Y s (Y s)
  let G : Real → Real := lRegIndexInt S T alpha Y Y
  let V : Set Real := {s : Real | T - s ^ 2 ∈ D.regular}
  let W : Set (Real × Real) :=
    {p : Real × Real | T - p.1 ∈ D.regular}
  let Q : Real × Real → Real := fun p ↦
    (S.base.metric (T - p.1)).inner (alpha p.2) (Y p.2) (Y p.2)
  let dQ : Real × Real → Real := fun p ↦
    fderiv Real Q p (0, 1)
  let Braw : Real → Real := fun s ↦ dQ (s ^ 2, s) / 2
  have ht : ∀ s ∈ Set.uIcc a b, T - s ^ 2 ∈ D.regular :=
    fun s hs ↦ (hgeo.2.2 s hs).1
  have halphaAll : ContMDiff 𝓘(Real, Real) I (8 : Nat) alpha := by
    exact (hf : ContMDiff _ _ (8 : Nat) _).comp
      (contMDiff_const.prodMk contMDiff_id)
  have halpha : ∀ s ∈ Set.uIcc a b, ∀ᶠ r in nhds s,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha r := by
    intro s _
    exact Filter.Eventually.of_forall fun r ↦
      halphaAll.mdifferentiableAt (by norm_num)
  have hA : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r : Real ↦ lVelocity (I := I) alpha r) s) s := by
    intro s hs
    simpa only [alpha] using (hgeo.2.2 s hs).2.2.1
  have hY : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha Y s) s := by
    intro s _
    simpa only [alpha, Y] using
      (lRegVar_reg (I := I) S T s f hf).2.1
  have hZ : ∀ s ∈ Set.uIcc a b, DifferentiableAt Real
      (chartRepAt (I := I) alpha
        (fun r : Real ↦ covDerivAlong (I := I)
          (S.base.metric (T - s ^ 2)) alpha Y r) s) s := by
    intro s _
    simpa only [alpha, Y] using
      (lRegVar_reg (I := I) S T s f hf).2.2
  have hJcont : ContinuousOn J (Set.uIcc a b) := by
    simpa only [J, alpha, Y] using
      lRegJacobi_contOn (I := I) S hS T f hf a b x Z hgeo
  have hJint : IntervalIntegrable J MeasureTheory.volume a b :=
    hJcont.intervalIntegrable
  have hVopen : IsOpen V :=
    D.regular_isOpen.preimage
      (continuous_const.sub (continuous_id.pow 2))
  have hWopen : IsOpen W :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_fst)
  have hQ2 : ContDiffOn Real 2 Q W := by
    simpa only [Q, W, alpha, Y] using
      lVarMetric_c2 (I := I) S T f hS.smoothMetric hf 0
  have hdQ : ContDiffOn Real 1 dQ W := by
    have hfd : ContDiffOn Real 1 (fderiv Real Q) W :=
      hQ2.fderiv_of_isOpen hWopen (by norm_num)
    simpa only [dQ] using hfd.clm_apply contDiffOn_const
  have hphi : ContDiffOn Real 1 (fun s : Real ↦ (s ^ 2, s)) V :=
    (contDiffOn_id.pow 2).prodMk contDiffOn_id
  have hdComp : ContDiffOn Real 1
      (fun s : Real ↦ dQ (s ^ 2, s)) V :=
    hdQ.comp hphi (fun s hs ↦ hs)
  have hBraw1 : ContDiffOn Real 1 Braw V := by
    simpa only [Braw] using hdComp.div_const 2
  have hQDiff : DifferentiableOn Real Q W :=
    hQ2.differentiableOn (by norm_num)
  have hBeq : Set.EqOn B Braw V := by
    intro s hs
    have hpW : (s ^ 2, s) ∈ W := hs
    have hQAt : DifferentiableAt Real Q (s ^ 2, s) :=
      (hQDiff (s ^ 2, s) hpW).differentiableAt
        (hWopen.mem_nhds hpW)
    have hslice : HasDerivAt
        (fun r : Real ↦ Q (s ^ 2, r)) (dQ (s ^ 2, s)) s := by
      simpa only [dQ] using Aux2.hasDerivAt_slice_snd
        (fun u r : Real ↦ Q (u, r)) (s ^ 2) s hQAt
    have hYs : DifferentiableAt Real
        (chartRepAt (I := I) alpha Y s) s := by
      simpa only [alpha, Y] using
        (lRegVar_reg (I := I) S T s f hf).2.1
    have hinner := inner_deriv_at
      (I := I) (n := (8 : WithTop ENat)) (by norm_num)
      (S.base.metric (T - s ^ 2)) alpha Y Y s
      halphaAll.contMDiffAt hYs hYs
    have hdQEq : dQ (s ^ 2, s) = 2 * B s := by
      have heq := hslice.unique (by
        simpa only [Q] using hinner)
      rw [heq]
      simp only [B]
      rw [(S.base.metric (T - s ^ 2)).symm]
      ring
    dsimp only [Braw]
    rw [hdQEq]
    ring
  have hB1 : ContDiffOn Real 1 B V :=
    hBraw1.congr (fun s hs ↦ hBeq hs)
  have hdBcont : ContinuousOn (deriv B) (Set.uIcc a b) :=
    (hB1.continuousOn_deriv_of_isOpen hVopen (by norm_num)).mono
      (fun s hs ↦ ht s hs)
  have hbal : ∀ s ∈ Set.uIcc a b,
      HasDerivAt B (2 * G s + J s) s := by
    intro s hs
    simpa only [B, G, J] using
      lRegIndex_balance (I := I) S hS T alpha Y Y s (ht s hs)
        (halpha s hs) (hA s hs) (hY s hs) (hZ s hs) (hY s hs)
  let Graw : Real → Real := fun s ↦ (deriv B s - J s) / 2
  have hGrawCont : ContinuousOn Graw (Set.uIcc a b) := by
    exact (hdBcont.sub hJcont).div_const 2
  have hGeq : Set.EqOn G Graw (Set.uIcc a b) := by
    intro s hs
    dsimp only [Graw]
    have hderiv := (hbal s hs).deriv
    linarith
  have hGcont : ContinuousOn G (Set.uIcc a b) :=
    hGrawCont.congr (fun s hs ↦ hGeq hs)
  have hIint : IntervalIntegrable G MeasureTheory.volume a b :=
    hGcont.intervalIntegrable
  have hYa : Y a = 0 := by
    have hconst : (fun u : Real ↦ f u a) = fun _ : Real ↦ f 0 a := by
      funext u
      exact hfixa u
    simp only [Y, alpha]
    rw [hconst]
    simp only [lVelocity, mfderiv_const]
    rfl
  have hYb : Y b = 0 := by
    have hconst : (fun u : Real ↦ f u b) = fun _ : Real ↦ f 0 b := by
      funext u
      exact hfixb u
    simp only [Y, alpha]
    rw [hconst]
    simp only [lVelocity, mfderiv_const]
    rfl
  have hindex := lRegIndex_zero_ends (I := I) S hS T alpha Y Y a b ht
    halpha hA hY hZ hY hIint hJint hYa hYb
  have hjac := lRegAction_jac (I := I) S hS T f hf a b x Z hgeo hfixa hfixb
  apply hjac.congr_deriv
  symm
  simpa only [alpha, Y, G, J] using (by
    rw [hindex]
    ring : 2 * lRegIndex S T alpha Y Y a b = -(∫ s in a..b, J s))

end DifferentialGeometry.PDE.RicciFlow.Perelman
