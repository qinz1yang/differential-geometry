import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompleteNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.LifetimeInterval

set_option autoImplicit false

noncomputable section

open Bundle Set DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Geometry.Riemannian
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.PDE.RicciFlow

section Predicate

variable {E F M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace F] {I : ModelWithCorners ℝ E F}
  [TopologicalSpace M] [ChartedSpace F M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] {D : RealTimeInterval}

def FixedTerminalBallNoncollapsedBelowScale
    (S : SolutionOn (I := I) (M := M) D) (kappa rho : ℝ) : Prop :=
  0 < rho ∧ ∀ (time : RealTimeInterval.FlowTime D) (B : FlowMetricBall S time),
    B.radius ≤ rho →
    Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ D.carrier →
    (∀ t ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ), ∀ z ∈ B.set,
      Real.sqrt (FlowMetricBall.rmNormSq S t z) ≤ (B.radius ^ 2)⁻¹) →
    B.IsKappaNoncollapsed kappa

end Predicate

private theorem radius_four_mul_le_one_of_sqrt_le
    {r a : ℝ} (hr : 0 < r) (h : Real.sqrt a ≤ (r ^ 2)⁻¹) :
    r ^ 4 * a ≤ 1 := by
  have hsq : a ≤ ((r ^ 2)⁻¹) ^ 2 := (Real.sqrt_le_iff.mp h).2
  calc
    r ^ 4 * a ≤ r ^ 4 * ((r ^ 2)⁻¹) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (pow_nonneg hr.le _)
    _ = 1 := by
      rw [inv_pow, ← div_eq_mul_inv, ← pow_mul]
      norm_num [hr.ne']

section FiniteLifetime

variable {E F M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace F] {I : ModelWithCorners ℝ E F} [I.Boundaryless]
  [PseudoMetricSpace M] [ChartedSpace F M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem complete_bounded_geometry_noncollapsed_belowScale
    (H rho K c : ℝ) (hH : 0 < H) (hrho : 0 < rho) (hK : 0 < K) (hc : 0 < c)
    (T : ℝ) (hT : 0 < T) (hTH : T ≤ H)
    (S : SolutionOn (I := I) (M := M)
      (lifetimeInterval (ENNReal.ofReal T) (ENNReal.ofReal_pos.mpr hT)))
    (hS : IsSolutionOn S)
    (hcomplete : ∀ t ∈ Ico (0 : ℝ) T,
      RiemannianMetricComplete (I := I) (S.base.metric t))
    (hbounded : ∀ b ∈ Ico (0 : ℝ) T, ∃ Q : ℝ,
      ∀ t ∈ Icc (0 : ℝ) b, ∀ z : M,
        Real.sqrt (FlowMetricBall.rmNormSq S t z) ≤ Q)
    (hinit : ∀ z : M, Real.sqrt (FlowMetricBall.rmNormSq S 0 z) ≤ K)
    (hInj : ∀ p : M, ENNReal.ofReal c ≤
      intrinsicInjectivityRadiusOf (I := I) (S.base.metric 0)
        (hcomplete 0 ⟨le_rfl, hT⟩) p) :
    FixedTerminalBallNoncollapsedBelowScale S
      (boundedGeometryNoncollapseCoeff (Module.finrank ℝ E) H K c) rho := by
  let D := lifetimeInterval (ENNReal.ofReal T) (ENNReal.ofReal_pos.mpr hT)
  have hD : D = RealTimeInterval.closedOpen 0 T hT := lifetimeInterval_ofReal T hT
  refine ⟨hrho, ?_⟩
  intro time B _hrho hballSlab hRm
  have htime : (time : ℝ) ∈ Ico (0 : ℝ) T := by
    have ht : (time : ℝ) ∈ D.carrier := time.property
    rw [hD] at ht
    exact ht
  have hnonneg : D.carrier ⊆ Ici (0 : ℝ) := by
    rw [hD]
    exact fun _ ht ↦ ht.1
  have hleft : 0 ≤ (time : ℝ) - B.radius ^ 2 :=
    hnonneg (hballSlab ⟨le_rfl, sub_le_self _ (sq_nonneg _)⟩)
  have htimePos : 0 < (time : ℝ) := by
    have hr2 : 0 < B.radius ^ 2 := sq_pos_of_pos B.radius_pos
    linarith only [hleft, hr2]
  have hfull : Icc (0 : ℝ) (time : ℝ) ⊆ D.carrier := by
    rw [hD]
    exact fun _ ht ↦ ⟨ht.1, ht.2.trans_lt htime.2⟩
  have hregular : Ioc (0 : ℝ) (time : ℝ) ⊆ D.regular := by
    rw [hD]
    exact fun _ ht ↦ ⟨ht.1, ht.2.trans_lt htime.2⟩
  have hcompleteTest : ∀ t ∈ Icc (0 : ℝ) (time : ℝ),
      RiemannianMetricComplete (I := I) (S.base.metric t) :=
    fun t ht ↦ hcomplete t ⟨ht.1, ht.2.trans_lt htime.2⟩
  obtain ⟨Q, hQ⟩ := hbounded (time : ℝ) htime
  have hboundedSq : ∃ Q' : ℝ, ∀ t ∈ Icc (0 : ℝ) (time : ℝ), ∀ z : M,
      normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ Q' :=
    ⟨Q ^ 2, fun t ht z ↦ (Real.sqrt_le_iff.mp (hQ t ht z)).2⟩
  have hRmSq : ∀ t ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ), ∀ z ∈ B.set,
      B.radius ^ 4 * FlowMetricBall.rmNormSq S t z ≤ 1 :=
    fun t ht z hz ↦ radius_four_mul_le_one_of_sqrt_le B.radius_pos (hRm t ht z hz)
  exact fixed_terminal_ball_noncollapsed_complete H K c hH hK hc S hS time htimePos
    (htime.2.le.trans hTH) hnonneg hfull hregular hcompleteTest hboundedSq hinit hInj
    B hballSlab hRmSq

end FiniteLifetime

universe uE uF uM

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem complete_bounded_geometry_no_local_collapsing
    (n : ℕ) (hn : 2 ≤ n) (H rho K c : ℝ)
    (hH : 0 < H) (hrho : 0 < rho) (hK : 0 < K) (hc : 0 < c) :
    ∃ kappa : ℝ, kappa = boundedGeometryNoncollapseCoeff n H K c ∧ 0 < kappa ∧
      AntitoneOn (fun h : ℝ ↦ boundedGeometryNoncollapseCoeff n h K c) (Ioi 0) ∧
      ∀ (E : Type uE) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = n),
        letI : CompleteSpace E := FiniteDimensional.complete ℝ E
        letI : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
        ∀ (F : Type uF) [TopologicalSpace F] (I : ModelWithCorners ℝ E F) [I.Boundaryless]
          (M : Type uM) [PseudoMetricSpace M] [ChartedSpace F M] [IsManifold I ∞ M]
          [T2Space M] [SigmaCompactSpace M],
          ∀ (T : ℝ) (hT : 0 < T), T ≤ H →
            ∀ (S : SolutionOn (I := I) (M := M)
              (lifetimeInterval (ENNReal.ofReal T) (ENNReal.ofReal_pos.mpr hT))),
              IsSolutionOn S →
              ∀ (hcomplete : ∀ t ∈ Ico (0 : ℝ) T,
                RiemannianMetricComplete (I := I) (S.base.metric t)),
                (∀ b ∈ Ico (0 : ℝ) T, ∃ Q : ℝ,
                  ∀ t ∈ Icc (0 : ℝ) b, ∀ z : M,
                    Real.sqrt (FlowMetricBall.rmNormSq S t z) ≤ Q) →
                (∀ z : M, Real.sqrt (FlowMetricBall.rmNormSq S 0 z) ≤ K) →
                (∀ p : M, ENNReal.ofReal c ≤
                  intrinsicInjectivityRadiusOf (I := I) (S.base.metric 0)
                    (hcomplete 0 ⟨le_rfl, hT⟩) p) →
                FixedTerminalBallNoncollapsedBelowScale S kappa rho := by
  refine ⟨boundedGeometryNoncollapseCoeff n H K c, rfl,
    boundedGeometryNoncollapseCoeff_pos n H K c hH hK hc,
    boundedGeometryNoncollapseCoeff_antitoneOn n K c hK hc, ?_⟩
  intro E _ _ _ hdim
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  intro F _ I _ M _ _ _ _ _ T hT hTH S hS hcomplete hbounded hinit hInj
  have h := complete_bounded_geometry_noncollapsed_belowScale H rho K c
    hH hrho hK hc T hT hTH S hS hcomplete hbounded hinit hInj
  simpa only [hdim] using h

end DifferentialGeometry.PDE.RicciFlow

end
