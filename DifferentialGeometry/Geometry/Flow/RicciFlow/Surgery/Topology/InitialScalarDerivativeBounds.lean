import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialCurvatureLifespan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabJointSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabUniqueness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabPullback
import DifferentialGeometry.Geometry.Operator.Gradient.PullbackAt

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u

private theorem ClosedSlab.exists_curvature_derivative_bound
    {P : OrientedThreeStage.{u}} {a b : ℝ} (S : P.ClosedSlab a b) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k ≤ N, ∀ t ∈ Icc a b, ∀ x : P.Carrier,
      curvDerivNormSq k (S.flow.base.metric t) x ≤ B := by
  have hgram := chartGramMatrix_joint_contMDiffOn S.flow.base.metric (Icc a b)
    S.smoothUpTo.jointContMDiffOn
  have hk (k : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc a b, ∀ x : P.Carrier,
      curvDerivNormSq k (S.flow.base.metric t) x ≤ B := by
    obtain ⟨B, hB, hbound⟩ := nablaKRmSlabSup S.flow.base.metric S.flow.base.metric
      hgram hgram k
    refine ⟨B, hB, fun t ht x => ?_⟩
    have heq := curvNormSq_eq (solutionOfMetric (D := RealTimeInterval.univ 0) S.flow.base.metric) k t x
    change curvDerivNormSq k (S.flow.base.metric t) x = _ at heq
    rw [heq]
    exact hbound t ht x
  choose B hB hbound using hk
  refine ⟨∑ k ∈ Finset.range (N + 1), B k, Finset.sum_nonneg (fun k _ => hB k), ?_⟩
  intro k hk t ht x
  exact (hbound k t ht x).trans
    (Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range.mpr (by omega)))

private theorem scalar_gradient_norm_sq_le_of_curvature_jet
    {P : OrientedThreeStage.{u}} {D : RealTimeInterval}
    (S : SolutionOn (I := ThreeModel) (M := P.Carrier) D)
    {t B : ℝ} (x : P.Carrier)
    (hfirst : curvDerivNormSq 1 (S.base.metric t) x ≤ B) :
    (S.base.metric t).inner x (gradientFun (S.base.metric t) (S.scalar t) x)
      (gradientFun (S.base.metric t) (S.scalar t) x) ≤
        ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt B) ^ 2 := by
  have h := abs_scalarDifferential_le_of_curvature_jet S x hfirst
    (gradientFun (S.base.metric t) (S.scalar t) x)
  have hn := metric_inner_self_nonneg (S.base.metric t) x
    (gradientFun (S.base.metric t) (S.scalar t) x)
  change |mvfderiv (I := ThreeModel) (S.scalar t) x
    (gradientFun (S.base.metric t) (S.scalar t) x)| ≤ _ at h
  rw [← inner_gradientFun, abs_of_nonneg hn] at h
  have hs := Real.sq_sqrt hn
  have hA : 0 ≤ (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt B := by positivity
  nlinarith [Real.sqrt_nonneg ((S.base.metric t).inner x
    (gradientFun (S.base.metric t) (S.scalar t) x)
    (gradientFun (S.base.metric t) (S.scalar t) x))]

private theorem exists_pos_scalar_derivative_threshold {A B C : ℝ} (hC : 0 < C) :
    ∃ q : ℝ, 0 < q ∧ A < C ^ 2 * q ^ 3 ∧ B < C * q ^ 2 := by
  let q : ℝ := max 1 (max (A / C ^ 2) (B / C)) + 1
  have hq1 : 1 ≤ q := by dsimp [q]; linarith [le_max_left 1 (max (A / C ^ 2) (B / C))]
  have hAq : A / C ^ 2 < q := by
    have hh := (le_max_left (A / C ^ 2) (B / C)).trans (le_max_right 1 (max (A / C ^ 2) (B / C)))
    dsimp [q]
    linarith
  have hBq : B / C < q := by
    have hh := (le_max_right (A / C ^ 2) (B / C)).trans (le_max_right 1 (max (A / C ^ 2) (B / C)))
    dsimp [q]
    linarith
  refine ⟨q, lt_of_lt_of_le zero_lt_one hq1, ?_, ?_⟩
  · have h := (div_lt_iff₀ (sq_pos_of_pos hC)).mp hAq
    have hp : q ≤ q ^ 3 := le_self_pow₀ hq1 (by decide)
    exact h.trans_le (by nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg C)])
  · have h := (div_lt_iff₀ hC).mp hBq
    have hp : q ≤ q ^ 2 := le_self_pow₀ hq1 (by decide)
    exact h.trans_le (by nlinarith [mul_le_mul_of_nonneg_left hp hC.le])



theorem exists_uniform_initial_scalar_derivative_bounds
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ C : ℝ, 0 < C → ∃ q : ℝ, 0 < q ∧
      ∀ {finish : ℝ} (G : P.IncomingSlab 0 finish), G.flow.base.metric 0 = g →
      ∀ t ∈ Ioc 0 τ, t < finish → ∀ x : P.Carrier,
        (G.flow.base.metric t).inner x (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x)
          (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x) <
            C ^ 2 * (max q (G.flow.scalar t x)) ^ 3 ∧
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| <
          C * (max q (G.flow.scalar t x)) ^ 2 := by
  obtain ⟨d, hd, S, hS⟩ := exists_closedSlab_of_metric P g 0
  obtain ⟨B, hB, hjets⟩ := S.exists_curvature_derivative_bound 2
  refine ⟨d / 2, half_pos hd, ?_⟩
  intro C hC
  let A := ((Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt B) ^ 2
  let T := (Module.finrank ℝ ThreeSpace : ℝ) ^ 6 * Real.sqrt B +
    2 * (Module.finrank ℝ ThreeSpace : ℝ) ^ 4 * B
  obtain ⟨q, hq, hAq, hTq⟩ := exists_pos_scalar_derivative_threshold (A := A) (B := T) hC
  refine ⟨q, hq, ?_⟩
  intro finish G hG t ht htf x
  let F := S.restrictIncoming le_rfl hd le_rfl
  have heq := G.metric_eq_on_Ico_of_initial F (hG.trans hS.symm)
  have htd : t < d := ht.2.trans_lt (half_lt_self hd)
  have heqt : G.flow.base.metric t = S.flow.base.metric t :=
    heq t ⟨ht.1.le, lt_min htf htd⟩
  have hjet (k : ℕ) (hk : k ≤ 2) : curvDerivNormSq k (G.flow.base.metric t) x ≤ B := by
    rw [heqt]
    exact hjets k hk t ⟨ht.1.le, htd.le⟩ x
  have hgradient := scalar_gradient_norm_sq_le_of_curvature_jet G.flow x (hjet 1 (by decide))
  have htime := abs_deriv_scalar_le_of_curvature_jets G.flow G.equation
    (show t ∈ (RealTimeInterval.closedOpen 0 finish G.lt).regular from ⟨ht.1, htf⟩)
    x (hjet 0 (by decide)) (hjet 2 le_rfl)
  have hderiv : derivWithin (fun v => G.flow.scalar v x) (Iic t) t =
      deriv (fun v => G.flow.scalar v x) t :=
    ((G.equation.scalarTime
      (show t ∈ (RealTimeInterval.closedOpen 0 finish G.lt).carrier from ⟨ht.1.le, htf⟩)
      Subset.rfl x).differentiableAt
      ((RealTimeInterval.closedOpen 0 finish G.lt).regular_mem_nhds ⟨ht.1, htf⟩)).derivWithin
      (uniqueDiffWithinAt_Iic t)
  have hp3 : q ^ 3 ≤ (max q (G.flow.scalar t x)) ^ 3 :=
    pow_le_pow_left₀ hq.le (le_max_left _ _) _
  have hp2 : q ^ 2 ≤ (max q (G.flow.scalar t x)) ^ 2 :=
    pow_le_pow_left₀ hq.le (le_max_left _ _) _
  constructor
  · exact hgradient.trans_lt (hAq.trans_le (mul_le_mul_of_nonneg_left hp3 (sq_nonneg C)))
  · rw [hderiv]
    exact htime.trans_lt (hTq.trans_le (mul_le_mul_of_nonneg_left hp2 hC.le))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u v

theorem exists_uniform_initial_scalar_derivative_bounds_of_isometry
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ C : ℝ, 0 < C → ∃ q : ℝ, 0 < q ∧
      ∀ {Q : OrientedThreeStage.{v}} {finish : ℝ} (G : Q.IncomingSlab 0 finish)
        (φ : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.Carrier),
      (∀ x : P.Carrier, ∀ v w : TangentSpace ThreeModel x,
        (G.flow.base.metric 0).inner (φ x) (mfderiv ThreeModel ThreeModel φ x v)
          (mfderiv ThreeModel ThreeModel φ x w) = g.inner x v w) →
      ∀ t ∈ Ioc 0 τ, t < finish → ∀ x : Q.Carrier,
        (G.flow.base.metric t).inner x (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x)
          (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x) <
            C ^ 2 * (max q (G.flow.scalar t x)) ^ 3 ∧
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| <
          C * (max q (G.flow.scalar t x)) ^ 2 := by
  obtain ⟨τ, hτ, hbound⟩ := exists_uniform_initial_scalar_derivative_bounds P g
  refine ⟨τ, hτ, ?_⟩
  intro C hC
  obtain ⟨q, hq, hqbound⟩ := hbound C hC
  refine ⟨q, hq, ?_⟩
  intro Q finish G φ hmetric t ht htf x
  let F := G.pullback φ
  have hinit : F.flow.base.metric 0 = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    exact hmetric y v w
  obtain ⟨y, rfl⟩ := φ.surjective x
  have hb := hqbound F hinit t ht htf y
  have hscalar (r : ℝ) (z : P.Carrier) : F.flow.scalar r z = G.flow.scalar r (φ z) :=
    G.flow.pullback_scalar φ r z
  have hscalarFun : F.flow.scalar t = G.flow.scalar t ∘ φ := funext (hscalar t)
  have hgradient :
      (F.flow.base.metric t).inner y (gradientFun (F.flow.base.metric t) (F.flow.scalar t) y)
        (gradientFun (F.flow.base.metric t) (F.flow.scalar t) y) =
      (G.flow.base.metric t).inner (φ y)
        (gradientFun (G.flow.base.metric t) (G.flow.scalar t) (φ y))
        (gradientFun (G.flow.base.metric t) (G.flow.scalar t) (φ y)) := by
    rw [hscalarFun]
    exact normGradSqFun_comp_of_pullback_inner (F.flow.base.metric t) (G.flow.base.metric t)
      (φ.contMDiff.mdifferentiable (by simp) y)
      (fun v w => Diffeomorph.pullbackMetricCross_inner (G.flow.base.metric t) φ y v w)
      (φ.mfderivToContinuousLinearEquiv (by simp) y).surjective
      ((metricScalar_smooth (G.flow.base.metric t)).mdifferentiableAt (by simp))
  have htimeFun : (fun r => F.flow.scalar r y) = fun r => G.flow.scalar r (φ y) :=
    funext (fun r => hscalar r y)
  rw [hgradient, hscalar t y, htimeFun] at hb
  exact hb

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

universe u v

theorem exists_uniform_initial_scalar_bound_of_isometry
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ τ Qbound : ℝ, 0 < τ ∧ 0 < Qbound ∧
      ∀ {Q : OrientedThreeStage.{v}} {finish : ℝ} (G : Q.IncomingSlab 0 finish)
        (φ : P.Carrier ≃ₘ⟮ThreeModel, ThreeModel⟯ Q.Carrier),
      (∀ x : P.Carrier, ∀ v w : TangentSpace ThreeModel x,
        (G.flow.base.metric 0).inner (φ x) (mfderiv ThreeModel ThreeModel φ x v)
          (mfderiv ThreeModel ThreeModel φ x w) = g.inner x v w) →
      ∀ t ∈ Icc 0 τ, t < finish → ∀ x : Q.Carrier, G.flow.scalar t x < Qbound := by
  obtain ⟨d, hd, S, hS⟩ := exists_closedSlab_of_metric P g 0
  have hcompact : IsCompact (Icc (0 : ℝ) d ×ˢ (univ : Set P.Carrier)) :=
    isCompact_Icc.prod isCompact_univ
  obtain ⟨B, hB⟩ := hcompact.bddAbove_image S.equation.scalarCont
  refine ⟨d / 2, max B 0 + 1, half_pos hd, by positivity, ?_⟩
  intro Q finish G φ hmetric t ht htf x
  let F := G.pullback φ
  have hinit : F.flow.base.metric 0 = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    exact hmetric y v w
  let A := S.restrictIncoming le_rfl hd le_rfl
  have heq := F.metric_eq_on_Ico_of_initial A (hinit.trans hS.symm)
  have htd : t < d := ht.2.trans_lt (half_lt_self hd)
  have heqt : F.flow.base.metric t = S.flow.base.metric t :=
    heq t ⟨ht.1, lt_min htf htd⟩
  obtain ⟨y, rfl⟩ := φ.surjective x
  have hscalar : F.flow.scalar t y = G.flow.scalar t (φ y) := G.flow.pullback_scalar φ t y
  have href : F.flow.scalar t y = S.flow.scalar t y := by
    change metricScalarAt (F.flow.base.metric t) y = metricScalarAt (S.flow.base.metric t) y
    rw [heqt]
  have hbound : S.flow.scalar t y ≤ B :=
    hB ⟨(t, y), ⟨⟨ht.1, htd.le⟩, mem_univ _⟩, rfl⟩
  change G.flow.scalar t (φ y) < max B 0 + 1
  rw [← hscalar, href]
  exact hbound.trans_lt (by linarith [le_max_left B 0])

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem incoming_metric_cast_initial_time
    {P : OrientedThreeStage.{u}} {a b finish : ℝ} (h : a = b)
    (G : P.IncomingSlab a finish) :
    (h ▸ G : P.IncomingSlab b finish).flow.base.metric = G.flow.base.metric := by
  cases h
  rfl

theorem exists_uniform_initial_scalar_and_derivative_bounds_of_initialIdentification
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ C : ℝ, 0 < C → ∃ q : ℝ, 0 < q ∧
      ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
      (∀ j : Fin H.eventCount, (H.event j).incoming.SingularEndpoint) →
      ∀ (last : Fin (H.eventCount + 1)) (finish : ℝ)
        (G : (H.stage last).IncomingSlab (H.time last) finish),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ t ∈ Ioo (H.time last) finish, t ≤ τ → ∀ x : (H.stage last).Carrier,
        G.flow.scalar t x < q ∧
        (G.flow.base.metric t).inner x (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x)
          (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x) < C ^ 2 * q ^ 3 ∧
        |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| < C * q ^ 2 := by
  obtain ⟨aSing, haSing, hsingTime⟩ :=
    exists_pos_le_singular_incoming_time_of_initialIdentification P g
  obtain ⟨τderiv, hτderiv, hderiv⟩ :=
    OrientedThreeStage.exists_uniform_initial_scalar_derivative_bounds_of_isometry P g
  obtain ⟨τscalar, Qbound, hτscalar, hQbound, hscalar⟩ :=
    OrientedThreeStage.exists_uniform_initial_scalar_bound_of_isometry P g
  refine ⟨min aSing (min τderiv τscalar), lt_min haSing (lt_min hτderiv hτscalar), ?_⟩
  intro C hC
  obtain ⟨qderiv, hqderiv, hderivBound⟩ := hderiv C hC
  let q := max qderiv Qbound
  have hq : 0 < q := hqderiv.trans_le (le_max_left _ _)
  refine ⟨q, hq, ?_⟩
  intro H A hsing last finish G hinit t ht htτ x
  have htSing : t ≤ aSing := htτ.trans (min_le_left _ _)
  have htDeriv : t ≤ τderiv := htτ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htScalar : t ≤ τscalar := htτ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hlast : last = 0 := by
    cases last using Fin.cases with
    | zero => rfl
    | succ i =>
      let j : Fin H.eventCount := ⟨0, Nat.zero_lt_of_lt i.isLt⟩
      have hfirst := hsingTime H A hsing j.castSucc (H.time j.succ)
        (H.event j).incoming (H.event_initial j) (hsing j)
      have hstage : aSing ≤ H.time i.succ := hfirst.trans
        (H.time_strictMono.monotone
          (show j.succ ≤ i.succ from Nat.succ_le_succ (Nat.zero_le _)))
      exact False.elim ((not_lt_of_ge htSing) (hstage.trans_lt ht.1))
  subst last
  have hz : H.time 0 = 0 := H.time_zero
  let F : (H.stage 0).IncomingSlab 0 finish := hz ▸ G
  have hFmetric : F.flow.base.metric = G.flow.base.metric := incoming_metric_cast_initial_time hz G
  have hFscalar : F.flow.scalar = G.flow.scalar := by
    funext r y
    change metricScalarAt (F.flow.base.metric r) y = metricScalarAt (G.flow.base.metric r) y
    rw [hFmetric]
  have hmetric : ∀ y : P.Carrier, ∀ v w : TangentSpace ThreeModel y,
      (F.flow.base.metric 0).inner (A.map y) (mfderiv ThreeModel ThreeModel A.map y v)
        (mfderiv ThreeModel ThreeModel A.map y w) = g.inner y v w := by
    intro y v w
    rw [hFmetric, ← hz, hinit]
    exact A.metric_eq y v w
  have ht0 : 0 < t := by simpa only [H.time_zero] using ht.1
  have hR := hscalar F A.map hmetric t ⟨ht0.le, htScalar⟩ ht.2 x
  have hb := hderivBound F A.map hmetric t ⟨ht0, htDeriv⟩ ht.2 x
  rw [hFmetric, hFscalar] at hb
  rw [hFscalar] at hR
  have hRq : G.flow.scalar t x < q := hR.trans_le (le_max_right _ _)
  have hmax : max qderiv (G.flow.scalar t x) ≤ q :=
    max_le (le_max_left _ _) hRq.le
  have hmnonneg : 0 ≤ max qderiv (G.flow.scalar t x) := hqderiv.le.trans (le_max_left _ _)
  refine ⟨hRq, ?_, ?_⟩
  · exact hb.1.trans_le (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hmnonneg hmax 3) (sq_nonneg C))
  · exact hb.2.trans_le (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hmnonneg hmax 2) hC.le)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
