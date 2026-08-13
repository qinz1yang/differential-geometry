import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.HeatPotential
import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.ScalarStrong
import DifferentialGeometry.Geometry.Operator.MetricFamilyRegularity

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Set Filter
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

omit [CompleteSpace E] in
theorem heat_pot_pos_of_barrier
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (V u : Real -> M -> Real)
    (hsol : IsHeatPotOn (RealTimeInterval.closed 0 T hT) G V u)
    (C : Real)
    (hV_upper : ∀ t ∈ Set.Icc 0 T, ∀ x : M, V t x ≤ C)
    (hinit : ∀ x : M, 0 ≤ u 0 x)
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    (L : Real) (hV_lower : ∀ t ∈ Set.Icc 0 tau, ∀ x : M, L ≤ V t x)
    {rho : M → Real}
    (hrho : ContMDiff I 𝓘(Real, Real) ∞ rho)
    (hrho_nonneg : ∀ x : M, 0 ≤ rho x)
    {r R delta eta m B kappa alpha : Real}
    (hR : 0 < R) (hdelta : 0 < delta) (heta : 0 < eta)
    (hlocal : ∀ t ∈ Set.Icc 0 tau, tau - delta < t → ∀ x : M,
      rho x < r → eta ≤ u t x)
    (hgrad_lower : ∀ t ∈ Set.Icc 0 tau, 0 < t → ∀ x : M,
      r ≤ rho x → rho x ≤ R →
      m ≤ (G.metric t).inner x
        (gradientFun (I := I) (G.metric t) rho x)
        (gradientFun (I := I) (G.metric t) rho x))
    (hheat_upper : ∀ t ∈ Set.Icc 0 tau, 0 < t → ∀ x : M,
      r ≤ rho x → rho x ≤ R →
      heatOperatorWithDrift (I := I) G t
        (fun y => (0 : TangentSpace I y)) rho x ≤ B)
    (hkappa : 0 < kappa) (hbarrier_init : R ≤ kappa * tau ^ 2)
    (hbarrier_time : R ≤ kappa * delta ^ 2)
    (halpha : 0 < alpha) (hdom : 2 * kappa * tau + B ≤ alpha * m)
    {y : M} (hy : rho y < R) :
    0 < u tau y := by
  let X : Real -> (x : M) -> TangentSpace I x :=
    fun _ x => (0 : TangentSpace I x)
  have hu_nonneg : ∀ t ∈ Set.Icc 0 tau, ∀ x : M, 0 ≤ u t x := by
    intro t ht x
    exact heat_pot_nonneg (I := I) G hT V u hsol C hV_upper hinit
      t ⟨ht.1, ht.2.trans htau.2.le⟩ x
  have hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) tau) := by
    apply hsol.jointCont.mono
    intro p hp
    exact ⟨⟨hp.1.1, hp.1.2.trans htau.2.le⟩, hp.2⟩
  have hu_time : ∀ t ∈ Set.Icc 0 tau, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 tau) t := by
    intro t ht htpos x
    have htreg : t ∈ (RealTimeInterval.closed 0 T hT).regular := by
      change t ∈ Set.Ioo 0 T
      exact ⟨htpos, lt_of_le_of_lt ht.2 htau.2⟩
    exact (hsol.equation t htreg x).differentiableAt.differentiableWithinAt
  have hu_mdiff : ∀ t ∈ Set.Icc 0 tau, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x := by
    intro t ht htpos x
    have htcarrier : t ∈ (RealTimeInterval.closed 0 T hT).carrier := by
      change t ∈ Set.Icc 0 T
      exact ⟨ht.1, ht.2.trans htau.2.le⟩
    exact (hsol.sliceSmooth t htcarrier).mdifferentiable (by simp) x
  have hu_grad : ∀ t ∈ Set.Icc 0 tau, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x := by
    intro t ht htpos x
    have htcarrier : t ∈ (RealTimeInterval.closed 0 T hT).carrier := by
      change t ∈ Set.Icc 0 T
      exact ⟨ht.1, ht.2.trans htau.2.le⟩
    exact gradientFun_mdiffAt (I := I) (G.metric t)
      (hsol.sliceSmooth t htcarrier) x
  have hu_super : ∀ t ∈ Set.Icc 0 tau, 0 < t → ∀ x : M,
      0 ≤ parabolicOperatorWithDrift (I := I) G tau X u t x -
        V t x * u t x := by
    intro t ht htpos x
    have htreg : t ∈ (RealTimeInterval.closed 0 T hT).regular := by
      change t ∈ Set.Ioo 0 T
      exact ⟨htpos, lt_of_le_of_lt ht.2 htau.2⟩
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 tau) t :=
      (uniqueDiffOn_Icc htau.1).uniqueDiffWithinAt ht
    have hderiv : derivWithin (fun s => u s x) (Set.Icc 0 tau) t =
        laplacianAt (I := I) G t (u t) x + V t x * u t x :=
      (hsol.equation t htreg x).hasDerivWithinAt.derivWithin huniq
    unfold parabolicOperatorWithDrift heatOperatorWithDrift driftTerm
    rw [hderiv]
    simp [X]
  exact scalar_strong_maximum_principle_with_potential_of_barrier (I := I)
    G htau.1 X V L u hu_cont hu_nonneg hu_time hu_mdiff hu_grad
    hu_super hV_lower hrho hrho_nonneg hR hdelta heta hlocal
    hgrad_lower hheat_upper hkappa hbarrier_init hbarrier_time
    halpha hdom hy

theorem heat_pot_pos_of_initial_pos
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (V u : Real -> M -> Real)
    (hsol : IsHeatPotOn (RealTimeInterval.closed 0 T hT) G V u)
    (C : Real)
    (hV_upper : ∀ t ∈ Set.Icc 0 T, ∀ x : M, V t x ≤ C)
    (hinit : ∀ x : M, 0 ≤ u 0 x)
    {c : M} (hc : 0 < u 0 c)
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    (hgrad_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        (G.metric p.1).inner p.2
          (gradientFun (I := I) (G.metric p.1) rho p.2)
          (gradientFun (I := I) (G.metric p.1) rho p.2))
        (spacetimeSlab (M := M) tau))
    (hlaplacian_cont : ∀ (rho : M → Real),
      ContMDiff I 𝓘(Real, Real) ∞ rho →
      ContinuousOn (fun p : Real × M =>
        laplacianAt (I := I) G p.1 rho p.2)
        (spacetimeSlab (M := M) tau))
    (L : Real) (hV_lower : ∀ t ∈ Set.Icc 0 tau, ∀ x : M, L ≤ V t x)
    (y : M) :
    0 < u tau y := by
  have hu_nonneg : ∀ t ∈ Set.Icc 0 tau, ∀ x : M, 0 ≤ u t x := by
    intro t ht x
    exact heat_pot_nonneg (I := I) G hT V u hsol C hV_upper hinit
      t ⟨ht.1, ht.2.trans htau.2.le⟩ x
  have hu_cont : ContinuousOn (fun p : Real × M => u p.1 p.2)
      (spacetimeSlab (M := M) tau) := by
    exact hsol.jointCont.mono fun p hp =>
      ⟨⟨hp.1.1, hp.1.2.trans htau.2.le⟩, hp.2⟩
  have hu_time : ∀ t ∈ Set.Icc 0 tau, 0 < t → ∀ x : M,
      DifferentiableWithinAt Real (fun s => u s x) (Set.Icc 0 tau) t := by
    intro t ht htpos x
    have htreg : t ∈ (RealTimeInterval.closed 0 T hT).regular := by
      change t ∈ Set.Ioo 0 T
      exact ⟨htpos, lt_of_le_of_lt ht.2 htau.2⟩
    exact (hsol.equation t htreg x).differentiableAt.differentiableWithinAt
  have hu_mdiff : ∀ t ∈ Set.Icc 0 tau, 0 < t → ∀ x : M,
      MDifferentiableAt I 𝓘(Real, Real) (u t) x := by
    intro t ht _ x
    have htcarrier : t ∈ (RealTimeInterval.closed 0 T hT).carrier := by
      change t ∈ Set.Icc 0 T
      exact ⟨ht.1, ht.2.trans htau.2.le⟩
    exact (hsol.sliceSmooth t htcarrier).mdifferentiable (by simp) x
  have hu_grad : ∀ t ∈ Set.Icc 0 tau, 0 < t → ∀ x : M,
      MDiffAt (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (u t) y) x := by
    intro t ht _ x
    have htcarrier : t ∈ (RealTimeInterval.closed 0 T hT).carrier := by
      change t ∈ Set.Icc 0 T
      exact ⟨ht.1, ht.2.trans htau.2.le⟩
    exact gradientFun_mdiffAt (I := I) (G.metric t)
      (hsol.sliceSmooth t htcarrier) x
  have hu_super : ∀ t ∈ Set.Icc 0 tau, 0 < t → ∀ x : M,
      0 ≤ derivWithin (fun s => u s x) (Set.Icc 0 tau) t -
        laplacianAt (I := I) G t (u t) x - V t x * u t x := by
    intro t ht htpos x
    have htreg : t ∈ (RealTimeInterval.closed 0 T hT).regular := by
      change t ∈ Set.Ioo 0 T
      exact ⟨htpos, lt_of_le_of_lt ht.2 htau.2⟩
    have huniq : UniqueDiffWithinAt Real (Set.Icc 0 tau) t :=
      (uniqueDiffOn_Icc htau.1).uniqueDiffWithinAt ht
    have hderiv : derivWithin (fun s => u s x) (Set.Icc 0 tau) t =
        laplacianAt (I := I) G t (u t) x + V t x * u t x :=
      (hsol.equation t htreg x).hasDerivWithinAt.derivWithin huniq
    rw [hderiv]
    ring_nf
    exact le_rfl
  exact scalar_strong_maximum_principle_time_dependent_metric_with_potential_positive
    (I := I) G htau.1 hgrad_cont hlaplacian_cont V L u hu_cont
    hu_nonneg hu_time hu_mdiff hu_grad hu_super hV_lower
    (t := 0) ⟨le_rfl, htau.1.le⟩ hc y

theorem heat_pot_pos_of_initial_pos_of_metricFamilySmoothOn
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (V u : Real -> M -> Real)
    (hsol : IsHeatPotOn (RealTimeInterval.closed 0 T hT) G V u)
    (C : Real)
    (hV_upper : ∀ t ∈ Set.Icc 0 T, ∀ x : M, V t x ≤ C)
    (hinit : ∀ x : M, 0 ≤ u 0 x)
    {c : M} (hc : 0 < u 0 c)
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D (G.restrict D).metric)
    (hslab : Set.Icc 0 tau ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 tau,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (L : Real) (hV_lower : ∀ t ∈ Set.Icc 0 tau, ∀ x : M, L ≤ V t x)
    (y : M) :
    0 < u tau y := by
  exact heat_pot_pos_of_initial_pos (I := I) G hT V u hsol C hV_upper hinit hc htau
    (fun ρ hρ => G.gradient_norm_sq_continuousOn hG hslab hρ)
    (fun ρ hρ => G.laplacianAt_continuousOn
      hG hslab (uniqueDiffOn_Icc htau.1) hconn hρ)
    L hV_lower y

theorem heat_pos_of_initial_pos_of_metricFamilySmoothOn
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M]
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    {T : Real} (hT : 0 ≤ T) (u : Real -> M -> Real)
    (hsol : IsHeatOn (RealTimeInterval.closed 0 T hT) G u)
    (hinit : ∀ x : M, 0 ≤ u 0 x)
    {c : M} (hc : 0 < u 0 c)
    {tau : Real} (htau : tau ∈ Set.Ioo 0 T)
    {D : RealTimeInterval}
    (hG : MetricFamilySmoothOn (I := I) (M := M) D (G.restrict D).metric)
    (hslab : Set.Icc 0 tau ⊆ D.regular)
    (hconn : ∀ t ∈ Set.Icc 0 tau,
      G.connection t = LeviCivita (I := I) (G.metric t))
    (y : M) :
    0 < u tau y := by
  exact heat_pot_pos_of_initial_pos_of_metricFamilySmoothOn
    (I := I) G hT (fun _ _ => 0) u hsol 0 (fun _ _ _ => le_rfl)
    hinit hc htau hG hslab hconn 0 (fun _ _ _ => le_rfl) y

end

end DifferentialGeometry.Analysis.Parabolic
