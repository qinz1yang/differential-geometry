import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.RegularizedComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Minimizer.CompleteManifoldExistence

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M] {D : RealTimeInterval}

theorem isLSegmentMinimizer_squareRootReparametrization_iff
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T K a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M, -K ≤ S.scalar (T - tau) z)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (x y : M) (gamma : ℝ → M)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b)) :
    isLSegmentMinimizer S T univ (a ^ 2) (b ^ 2) x y
      (squareRootReparametrization gamma) ↔
      gamma a = x ∧ gamma b = y ∧
        lRegularizedAction S T gamma a b = lRegularizedCostC1 S T a b x y := by
  let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace
  have hb : 0 ≤ b := ha.trans hab
  have hlength := lLength_squareRootReparametrization_sq S T gamma a b ha hb
  constructor
  · intro hmin
    have hga : gamma a = x := by
      simpa only [squareRootReparametrization, Real.sqrt_sq ha] using hmin.2.1
    have hgb : gamma b = y := by
      simpa only [squareRootReparametrization, Real.sqrt_sq hb] using hmin.2.2.1
    refine ⟨hga, hgb, WithTop.coe_inj.mp ?_⟩
    calc
      (lRegularizedAction S T gamma a b : WithTop ℝ) =
          (lLength S T (squareRootReparametrization gamma) (a ^ 2) (b ^ 2) :
            WithTop ℝ) := congrArg (fun r : ℝ => (r : WithTop ℝ)) hlength.symm
      _ = lSegmentValue S T univ (a ^ 2) (b ^ 2) x y := hmin.2.2.2.symm
      _ = (lRegularizedCostC1 S T a b x y : WithTop ℝ) :=
        lSegmentValue_eq_lRegularizedCostC1_of_contMDiffOn S hMet hSc T K a b ha hab
          hR hreg x y gamma hgamma hga hgb
  · rintro ⟨hga, hgb, hcost⟩
    have hLag := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one
      S hMet hSc T a b hab gamma hgamma hreg
    refine ⟨isFiniteActionLCurve_squareRootReparametrization S T univ a b ha hab
      gamma hgamma hLag (by simp), ?_, ?_, ?_⟩
    · simpa only [squareRootReparametrization, Real.sqrt_sq ha] using hga
    · simpa only [squareRootReparametrization, Real.sqrt_sq hb] using hgb
    · rw [hlength, hcost]
      exact lSegmentValue_eq_lRegularizedCostC1_of_contMDiffOn S hMet hSc T K a b ha hab
        hR hreg x y gamma hgamma hga hgb

open scoped Bundle in
theorem exists_isLSegmentMinimizer_of_complete_bounded_curvature
    [NeZero (Module.finrank ℝ E)] [T2Space M]
    [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (K T : ℝ) (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hreg : Icc (T - b ^ 2) T ⊆ D.regular)
    (hRm : ∀ q ∈ Icc (T - b ^ 2) T, ∀ z : M,
      normSq0S (I := I) (S.base.metric q) z 4 (S.base.rm04 q z) ≤ K)
    (x y : M) :
    ∃ gamma : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 gamma (Icc a b) ∧
        isLSegmentMinimizer S T univ (a ^ 2) (b ^ 2) x y
          (squareRootReparametrization gamma) := by
  let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace
  have hcompetitor : ∃ alpha0 : ℝ → M,
      alpha0 a = x ∧ alpha0 b = y ∧ ContMDiff 𝓘(ℝ, ℝ) I 1 alpha0 := by
    let _ : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(S.base.metric T).toRiemannianMetric⟩
    let _ : (x : M) → NormedAddCommGroup (TangentSpace I x) := fun x =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
    let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨(S.base.metric T).inner, (S.base.metric T).contMDiff.continuous, fun _ _ _ => rfl⟩
    obtain ⟨alpha0, h0a, h0b, halpha0, _, _, _⟩ :=
      Manifold.exists_lt_locally_constant_of_riemannianEDist_lt
        (Manifold.riemannianEDist_lt_top (I := I) x y) hab
    exact ⟨alpha0, h0a, h0b, halpha0⟩
  obtain ⟨alpha0, h0a, h0b, halpha0⟩ := hcompetitor
  have hb : 0 ≤ b := ha.trans hab.le
  have hregBack : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    apply hreg
    have hs2 : s ^ 2 ≤ b ^ 2 := (sq_le_sq₀ (ha.trans hs.1) hb).2 hs.2
    constructor <;> linarith [sq_nonneg s]
  obtain ⟨gamma, _, hgamma, hga, hgb, hcost, _, _⟩ :=
    exists_lRegularizedMin_rm S hS K T hg a b ha hab hreg hRm x y alpha0
      halpha0 h0a h0b
  have hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M,
      -((Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K) ≤ S.scalar (T - tau) z := by
    intro tau htau z
    have ht : T - tau ∈ Icc (T - b ^ 2) T := by
      constructor <;> linarith [sq_nonneg a, htau.1, htau.2]
    have hs := scalar_abs_le_rm (I := I) (S.base.metric (T - tau)) z
    apply neg_le_of_abs_le
    simpa only [SolutionOn.scalar, SolutionFamily.scalar, SolutionFamily.rm04,
      metricRm04_apply,
      show Module.finrank ℝ (TangentSpace I z) = Module.finrank ℝ E by rfl] using
      hs.trans (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hRm _ ht z)) (sq_nonneg _))
  exact ⟨gamma, hgamma,
    (isLSegmentMinimizer_squareRootReparametrization_iff S hS.smoothMetric
      ⟨hS.scalarCont⟩ T _ a b ha hab.le hR hregBack x y gamma hgamma).mpr
      ⟨hga, hgb, hcost⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
