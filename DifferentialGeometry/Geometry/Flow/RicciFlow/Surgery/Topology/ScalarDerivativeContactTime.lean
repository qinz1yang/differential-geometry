import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialCurvatureLifespan
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.InitialScalarDerivativeBounds

noncomputable section
open Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem exists_pos_le_positive_stage_time_of_initialIdentification
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ a : ℝ, 0 < a ∧
      ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
      (∀ j : Fin H.eventCount, (H.event j).incoming.SingularEndpoint) →
      ∀ last : Fin (H.eventCount + 1), last ≠ 0 → a ≤ H.time last := by
  obtain ⟨a, ha, htime⟩ := exists_pos_le_singular_incoming_time_of_initialIdentification P g
  refine ⟨a, ha, ?_⟩
  intro H A hsing last hlast
  cases last using Fin.cases with
  | zero => exact (hlast rfl).elim
  | succ i =>
    let j : Fin H.eventCount := ⟨0, Nat.zero_lt_of_lt i.isLt⟩
    have hfirst := htime H A hsing j.castSucc (H.time j.succ)
      (H.event j).incoming (H.event_initial j) (hsing j)
    exact hfirst.trans (H.time_strictMono.monotone
      (show j.succ ≤ i.succ from Nat.succ_le_succ (Nat.zero_le _)))


private theorem metric_cast_start
    {P : OrientedThreeStage.{u}} {a b finish : ℝ} (h : a = b)
    (G : P.IncomingSlab a finish) :
    (h ▸ G : P.IncomingSlab b finish).flow.base.metric = G.flow.base.metric := by
  cases h
  rfl

theorem exists_pos_lt_scalar_derivative_failure_time_of_initialIdentification
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ a : ℝ, 0 < a ∧ ∀ C : ℝ, 0 < C → ∃ q : ℝ, 0 < q ∧
      ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
      (∀ j : Fin H.eventCount, (H.event j).incoming.SingularEndpoint) →
      ∀ (last : Fin (H.eventCount + 1)) (finish : ℝ)
        (G : (H.stage last).IncomingSlab (H.time last) finish),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ t ∈ Ioo (H.time last) finish, ∀ x : (H.stage last).Carrier,
        q ≤ G.flow.scalar t x →
        (C ^ 2 * G.flow.scalar t x ^ 3 ≤
          (G.flow.base.metric t).inner x (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x)
            (gradientFun (G.flow.base.metric t) (G.flow.scalar t) x) ∨
          C * G.flow.scalar t x ^ 2 ≤ |derivWithin (fun v => G.flow.scalar v x) (Iic t) t|) →
        a < t := by
  obtain ⟨aSing, haSing, hstage⟩ := exists_pos_le_positive_stage_time_of_initialIdentification P g
  obtain ⟨τ, hτ, hseed⟩ :=
    OrientedThreeStage.exists_uniform_initial_scalar_derivative_bounds_of_isometry P g
  refine ⟨min aSing τ, lt_min haSing hτ, ?_⟩
  intro C hC
  obtain ⟨q, hq, hbound⟩ := hseed C hC
  refine ⟨q, hq, ?_⟩
  intro H A hsing last finish G hinit t ht x hqx hfail
  by_cases hlast : last = 0
  · subst last
    have hz : H.time 0 = 0 := H.time_zero
    let F : (H.stage 0).IncomingSlab 0 finish := hz ▸ G
    have hFmetric : F.flow.base.metric = G.flow.base.metric := metric_cast_start hz G
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
    by_contra hn
    have httau : t ≤ τ := (le_of_not_gt hn).trans (min_le_right _ _)
    have hb := hbound F A.map hmetric t ⟨ht0, httau⟩ ht.2 x
    rw [hFmetric, hFscalar, max_eq_right hqx] at hb
    exact hfail.elim (fun h => (not_le_of_gt hb.1) h) (fun h => (not_le_of_gt hb.2) h)
  · exact (min_le_left aSing τ).trans_lt ((hstage H A hsing last hlast).trans_lt ht.1)



private theorem gradient_norm_sq_ge_of_direction_eq
    {P : OrientedThreeStage.{u}} (g : P.Metric) (f : P.Carrier → ℝ) (x : P.Carrier)
    {A : ℝ} (hA : 0 < A) (v : TangentSpace ThreeModel x) (hv : v ≠ 0)
    (heq : A * Real.sqrt (g.inner x v v) =
      |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) f x v)|) :
    A ^ 2 ≤ g.inner x (gradientFun g f x) (gradientFun g f x) := by
  by_contra h
  have hn := metric_inner_self_nonneg g x (gradientFun g f x)
  have hs : Real.sqrt (g.inner x (gradientFun g f x) (gradientFun g f x)) < A :=
    (Real.sqrt_lt hn hA.le).mpr (lt_of_not_ge h)
  have hcs := SmoothRiemannianMetric.abs_metric_inner_le_sqrt_metric_quadratic
    g x (gradientFun g f x) v
  rw [inner_gradientFun] at hcs
  have hvpos : 0 < Real.sqrt (g.inner x v v) := Real.sqrt_pos.mpr (g.pos x v hv)
  exact (not_lt_of_ge (heq.trans_le hcs)) (mul_lt_mul_of_pos_right hs hvpos)

theorem exists_pos_lt_scalar_derivative_contact_time_of_initialIdentification
    (P : OrientedThreeStage.{u}) (g : P.Metric) :
    ∃ a : ℝ, 0 < a ∧ ∀ C : ℝ, 0 < C → ∃ q : ℝ, 0 < q ∧
      ∀ (H : ObservedHistory.{u}), InitialIdentification P g H →
      (∀ j : Fin H.eventCount, (H.event j).incoming.SingularEndpoint) →
      ∀ (last : Fin (H.eventCount + 1)) (finish : ℝ)
        (G : (H.stage last).IncomingSlab (H.time last) finish),
      G.flow.base.metric (H.time last) = H.initialMetric last →
      ∀ t ∈ Ioo (H.time last) finish, ∀ x : (H.stage last).Carrier,
        q ≤ G.flow.scalar t x →
        ((∃ v : TangentSpace ThreeModel x, v ≠ 0 ∧
          C * G.flow.scalar t x * Real.sqrt (G.flow.scalar t x) *
            Real.sqrt ((G.flow.base.metric t).inner x v v) =
              |(show ℝ from mfderiv ThreeModel 𝓘(ℝ, ℝ) (G.flow.scalar t) x v)|) ∨
          |derivWithin (fun v => G.flow.scalar v x) (Iic t) t| = C * G.flow.scalar t x ^ 2) →
        a < t := by
  obtain ⟨a, ha, hfloor⟩ := exists_pos_lt_scalar_derivative_failure_time_of_initialIdentification P g
  refine ⟨a, ha, ?_⟩
  intro C hC
  obtain ⟨q, hq, hbound⟩ := hfloor C hC
  refine ⟨q, hq, ?_⟩
  intro H A hsing last finish G hinit t ht x hqx hcontact
  apply hbound H A hsing last finish G hinit t ht x hqx
  rcases hcontact with ⟨v, hv, heq⟩ | heq
  · left
    have hR : 0 < G.flow.scalar t x := hq.trans_le hqx
    have hb := gradient_norm_sq_ge_of_direction_eq (G.flow.base.metric t)
      (G.flow.scalar t) x (by positivity) v hv heq
    have hs := Real.sq_sqrt hR.le
    have hpow : (C * G.flow.scalar t x * Real.sqrt (G.flow.scalar t x)) ^ 2 =
        C ^ 2 * G.flow.scalar t x ^ 3 := by
      calc
        _ = C ^ 2 * G.flow.scalar t x ^ 2 * Real.sqrt (G.flow.scalar t x) ^ 2 := by ring
        _ = _ := by rw [hs]; ring
    rw [hpow] at hb
    exact hb
  · exact Or.inr heq.ge

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
