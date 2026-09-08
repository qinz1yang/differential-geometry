import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.Reparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.Value
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Integrability

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M] {D : RealTimeInterval}

theorem lSegmentValue_le_lRegularizedAction
    (S : SolutionOn (I := I) (M := M) D) (T K : ℝ)
    (Ω : Set (M × ℝ)) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M, -K ≤ S.scalar (T - tau) z)
    (x y : M) (alpha : ℝ → M)
    (halpha : ContMDiffOn 𝓘(ℝ, ℝ) I 1 alpha (Icc a b))
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b)
    (hΩ : ∀ s ∈ Icc a b, (alpha s, T - s ^ 2) ∈ Ω)
    (hxa : alpha a = x) (hyb : alpha b = y) :
    lSegmentValue S T Ω (a ^ 2) (b ^ 2) x y ≤
      (lRegularizedAction S T alpha a b : WithTop ℝ) := by
  have hb : 0 ≤ b := ha.trans hab
  have hseg := isFiniteActionLCurve_squareRootReparametrization
    S T Ω a b ha hab alpha halpha hLag hΩ
  have hle := lSegmentValue_le_lLength_of_scalar_lower_bound_on_time_interval
    S T K Ω (sq_nonneg a) ((sq_le_sq₀ ha hb).2 hab) hR x y
    (squareRootReparametrization alpha) hseg
    (by simpa only [squareRootReparametrization, Real.sqrt_sq ha] using hxa)
    (by simpa only [squareRootReparametrization, Real.sqrt_sq hb] using hyb)
  rwa [lLength_squareRootReparametrization_sq S T alpha a b ha hb] at hle

theorem lSegmentValue_le_lRegularizedAction_of_contMDiff
    (S : SolutionOn (I := I) (M := M) D) (T K : ℝ)
    (Ω : Set (M × ℝ)) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M, -K ≤ S.scalar (T - tau) z)
    (x y : M) (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha)
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b)
    (hΩ : ∀ s ∈ Icc a b, (alpha s, T - s ^ 2) ∈ Ω)
    (hxa : alpha a = x) (hyb : alpha b = y) :
    lSegmentValue S T Ω (a ^ 2) (b ^ 2) x y ≤
      (lRegularizedAction S T alpha a b : WithTop ℝ) :=
  lSegmentValue_le_lRegularizedAction S T K Ω a b ha hab hR x y alpha
    halpha.contMDiffOn hLag hΩ hxa hyb

theorem lSegmentValue_le_lRegularizedCostC1_of_intervalIntegrable
    (S : SolutionOn (I := I) (M := M) D) (T K a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M, -K ≤ S.scalar (T - tau) z)
    (x y : M)
    (hInt : ∀ alpha : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 alpha →
      alpha a = x → alpha b = y →
      IntervalIntegrable (lRegularizedLagrangian S T alpha) volume a b)
    (alpha0 : ℝ → M) (halpha0 : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha0)
    (h0a : alpha0 a = x) (h0b : alpha0 b = y) :
    lSegmentValue S T univ (a ^ 2) (b ^ 2) x y ≤
      (lRegularizedCostC1 S T a b x y : WithTop ℝ) := by
  let costs : Set ℝ := {r | ∃ alpha : ℝ → M,
    ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
      alpha a = x ∧ alpha b = y ∧ lRegularizedAction S T alpha a b = r}
  have hne : costs.Nonempty :=
    ⟨lRegularizedAction S T alpha0 a b, alpha0, halpha0, h0a, h0b, rfl⟩
  have hb : 0 ≤ b := ha.trans hab
  have hbdd : BddBelow costs := by
    refine ⟨-(2 * K / 3) *
      (b ^ 2 * Real.sqrt (b ^ 2) - a ^ 2 * Real.sqrt (a ^ 2)), ?_⟩
    rintro r ⟨alpha, halpha, hxa, hyb, rfl⟩
    have hLag := hInt alpha halpha hxa hyb
    have hlow := lLength_ge_of_scalar_lower_bound S T (a ^ 2) (b ^ 2) K
      (sq_nonneg a) ((sq_le_sq₀ ha hb).2 hab) (squareRootReparametrization alpha)
      (fun tau htau => hR tau htau (squareRootReparametrization alpha tau))
      ((intervalIntegrable_lDensity_squareRootReparametrization_sq_iff
        S T alpha a b ha hb).mpr hLag)
    rwa [lLength_squareRootReparametrization_sq S T alpha a b ha hb] at hlow
  change lSegmentValue S T univ (a ^ 2) (b ^ 2) x y ≤ (sInf costs : ℝ)
  rw [WithTop.coe_sInf' hne hbdd]
  apply le_csInf (hne.image fun r : ℝ => (r : WithTop ℝ))
  rintro q ⟨r, ⟨alpha, halpha, hxa, hyb, rfl⟩, rfl⟩
  exact lSegmentValue_le_lRegularizedAction S T K univ a b ha hab hR x y alpha
    halpha.contMDiffOn (hInt alpha halpha hxa hyb) (by simp) hxa hyb

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [UniformSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [PreconnectedSpace M] {D : RealTimeInterval}

theorem lSegmentValue_le_lRegularizedCostC1
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T K a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M, -K ≤ S.scalar (T - tau) z)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (x y : M) (alpha0 : ℝ → M)
    (halpha0 : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha0)
    (h0a : alpha0 a = x) (h0b : alpha0 b = y) :
    lSegmentValue S T univ (a ^ 2) (b ^ 2) x y ≤
      (lRegularizedCostC1 S T a b x y : WithTop ℝ) :=
  lSegmentValue_le_lRegularizedCostC1_of_intervalIntegrable S T K a b ha hab hR x y
    (fun alpha halpha _ _ =>
      intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one
        S hMet hSc T a b hab alpha halpha.contMDiffOn hreg)
    alpha0 halpha0 h0a h0b

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
