import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Basic
import DifferentialGeometry.Geometry.Metric.Comparison.CurveEnergy
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.TimeSlab

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open MeasureTheory

universe u uE uH

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
theorem exists_uniform_lower_bound_lRegularizedPotential
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
theorem lRegularizedAction_ge_reference_energy_add_constant
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
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b) :
    (∫ s in a..b, (c / 2) *
        gRef.inner (alpha s) (lVelocity (I := I) alpha s)
          (lVelocity (I := I) alpha s)) +
      C * (b - a) ≤ lRegularizedAction S T alpha a b := by
  have href' : IntervalIntegrable
      (fun s => (c / 2) *
        gRef.inner (alpha s) (lVelocity (I := I) alpha s)
          (lVelocity (I := I) alpha s)) volume a b :=
    href.const_mul (c / 2)
  have hmono :
      (∫ s in a..b, (c / 2) *
          gRef.inner (alpha s) (lVelocity (I := I) alpha s)
            (lVelocity (I := I) alpha s) + C) ≤
        ∫ s in a..b, lRegularizedLagrangian S T alpha s := by
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
  simpa [lRegularizedAction, smul_eq_mul, mul_comm] using hmono

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem exists_lRegularizedAction_coercivity_constants
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
          IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b →
            (∫ s in a..b, (c / 2) *
                gRef.inner (alpha s) (lVelocity (I := I) alpha s)
                  (lVelocity (I := I) alpha s)) +
              C * (b - a) ≤ lRegularizedAction S T alpha a b := by
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
    exists_uniform_lower_bound_lRegularizedPotential (I := I) S hST T a b (by
      intro s hs
      exact htime (hback s (by
        simpa only [Set.uIcc_of_le hab] using hs)))
  refine ⟨c, C, hc, ?_⟩
  intro alpha href hLag
  apply lRegularizedAction_ge_reference_energy_add_constant (I := I) S T alpha gRef a b c C hab
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
theorem exists_lRegularizedAction_coercivity_bound
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
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b) :
    ∃ c C : Real, 0 < c ∧
      (∫ s in a..b, (c / 2) *
          gRef.inner (alpha s) (lVelocity (I := I) alpha s)
            (lVelocity (I := I) alpha s)) +
        C * (b - a) ≤ lRegularizedAction S T alpha a b := by
  obtain ⟨c, C, hc, hall⟩ :=
    exists_lRegularizedAction_coercivity_constants (I := I) S hS T t0 t1 gRef a b hab htime hback
  exact ⟨c, C, hc, hall alpha href hLag⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem exists_curveEnergy_le_of_lRegularizedAction_le
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
          IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b →
            lRegularizedAction S T alpha a b ≤ A →
              DifferentialGeometry.Geometry.Riemannian.curveEnergy
                  (I := I) gRef alpha a b ≤
                (2 / c) * (A - C * (b - a)) := by
  obtain ⟨c, C, hc, hall⟩ :=
    exists_lRegularizedAction_coercivity_constants (I := I) S hS T t0 t1 gRef a b hab htime hback
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
      _ ≤ lRegularizedAction S T alpha a b := hcoerc
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
theorem exists_riemannianEDistOf_le_of_lRegularizedAction_le
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
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b)
    (hA : lRegularizedAction S T alpha a b ≤ A) :
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
    exists_curveEnergy_le_of_lRegularizedAction_le (I := I) S hS T t0 t1 gRef a b A hab htime hback
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


end DifferentialGeometry.PDE.RicciFlow.Perelman
