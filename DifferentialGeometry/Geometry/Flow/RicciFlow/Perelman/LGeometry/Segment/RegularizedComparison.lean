import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.Reparametrization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.Value
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Segment.Sobolev
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Compactness.ActionDensity

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

section

open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RegularSpace M] [PreconnectedSpace M] {D : RealTimeInterval}

theorem lSegmentValue_eq_lRegularizedCostC1_of_isFiniteActionLCurve
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T K a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M, -K ≤ S.scalar (T - tau) z)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (x y : M) (gamma0 : ℝ → M)
    (hgamma0 : isFiniteActionLCurve S T univ (a ^ 2) (b ^ 2) gamma0)
    (h0a : gamma0 (a ^ 2) = x) (h0b : gamma0 (b ^ 2) = y) :
    lSegmentValue S T univ (a ^ 2) (b ^ 2) x y =
      (lRegularizedCostC1 S T a b x y : WithTop ℝ) := by
  let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace
  have hb : 0 ≤ b := ha.trans hab
  have hfin : lSegmentValue S T univ (a ^ 2) (b ^ 2) x y ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top
      (lSegmentValue_le_lLength_of_scalar_lower_bound_on_time_interval
        S T K univ (sq_nonneg a) ((sq_le_sq₀ ha hb).mpr hab) hR x y gamma0 hgamma0 h0a h0b)
  obtain ⟨c, hc⟩ := WithTop.ne_top_iff_exists.mp hfin
  let costs : Set ℝ := {r | ∃ alpha : ℝ → M,
    ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
      alpha a = x ∧ alpha b = y ∧ lRegularizedAction S T alpha a b = r}
  have hclow : ∀ r ∈ costs, c ≤ r := by
    rintro r ⟨alpha, halpha, hxa, hyb, rfl⟩
    apply WithTop.coe_le_coe.mp
    rw [hc]
    exact lSegmentValue_le_lRegularizedAction S T K univ a b ha hab hR x y alpha
      halpha.contMDiffOn
      (intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one
        S hMet hSc T a b hab alpha halpha.contMDiffOn hreg) (by simp) hxa hyb
  have hbdd : BddBelow costs := ⟨c, hclow⟩
  obtain ⟨m0, t0, p0, u0, ht00, hmono0, htlast0, hsrc0, hrep0, _hder0⟩ :=
    isFiniteActionLCurve.exists_timeH1_chart_partition S hMet hSc T a b ha hab univ gamma0 hgamma0 hreg
  obtain ⟨beta0, _v0, hbeta0, hbeta0a, hbeta0b, _hsrcBeta0, _hrepBeta0, _hu0, _hunif0, _hact0⟩ :=
    lAction_c1_dense S hMet hSc T a b t0 hmono0 ht00 htlast0 p0
      (squareReparametrization gamma0) u0 hsrc0 hrep0 hreg
  have hne : costs.Nonempty :=
    ⟨lRegularizedAction S T (beta0 0) a b, beta0 0, hbeta0 0,
      (hbeta0a 0).trans h0a, (hbeta0b 0).trans h0b, rfl⟩
  refine le_antisymm ?_ ?_
  · rw [← hc]
    exact WithTop.coe_le_coe.mpr (le_csInf hne hclow)
  · apply le_lSegmentValue S T univ (a ^ 2) (b ^ 2) x y
    intro gamma hgamma hga hgb
    apply WithTop.coe_le_coe.mpr
    obtain ⟨m, t, p, u, ht0, hmono, htlast, hsrc, hrep, _hder⟩ :=
      isFiniteActionLCurve.exists_timeH1_chart_partition S hMet hSc T a b ha hab univ gamma hgamma hreg
    obtain ⟨beta, _v, hbeta, hbetaa, hbetab, _hsrcBeta, _hrepBeta, _hu, _hunif, hact⟩ :=
      lAction_c1_dense S hMet hSc T a b t hmono ht0 htlast p
        (squareReparametrization gamma) u hsrc hrep hreg
    have hcost : lRegularizedCostC1 S T a b x y ≤
        lRegularizedAction S T (squareReparametrization gamma) a b := by
      apply ge_of_tendsto hact
      exact Eventually.of_forall fun n ↦ lRegularizedCostC1_le_bdd S T a b x y hbdd
        (beta n) (hbeta n) ((hbetaa n).trans hga) ((hbetab n).trans hgb)
    have hlen : lLength S T gamma (a ^ 2) (b ^ 2) =
        lRegularizedAction S T (squareReparametrization gamma) a b := by
      simpa only [Real.sqrt_sq ha, Real.sqrt_sq hb] using
        lLength_eq_lRegularizedAction_squareReparametrization_ae
          S T gamma (a ^ 2) (b ^ 2) (sq_nonneg a) (sq_nonneg b)
    exact hcost.trans_eq hlen.symm

theorem lSegmentValue_eq_lRegularizedCostC1_of_contMDiffOn
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T K a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hR : ∀ tau ∈ Icc (a ^ 2) (b ^ 2), ∀ z : M, -K ≤ S.scalar (T - tau) z)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (x y : M) (alpha0 : ℝ → M) (halpha0 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 alpha0 (Icc a b))
    (h0a : alpha0 a = x) (h0b : alpha0 b = y) :
    lSegmentValue S T univ (a ^ 2) (b ^ 2) x y =
      (lRegularizedCostC1 S T a b x y : WithTop ℝ) := by
  let _ : PseudoMetricSpace M := (S.base.metric T).toPseudoMetricSpace
  have hLag := intervalIntegrable_lRegularizedLagrangian_of_contMDiffOn_one
    S hMet hSc T a b hab alpha0 halpha0 hreg
  exact lSegmentValue_eq_lRegularizedCostC1_of_isFiniteActionLCurve S hMet hSc T K a b ha hab hR hreg
    x y (squareRootReparametrization alpha0)
    (isFiniteActionLCurve_squareRootReparametrization S T univ a b ha hab alpha0
      halpha0 hLag (by simp))
    (by simpa only [squareRootReparametrization, Real.sqrt_sq ha] using h0a)
    (by simpa only [squareRootReparametrization, Real.sqrt_sq (ha.trans hab)] using h0b)

end

end DifferentialGeometry.PDE.RicciFlow.Perelman
