import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalMetricSandwich
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedCanonicalDomain
import DifferentialGeometry.Geometry.Metric.Distance.Ball

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance sourceBallSandwichC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

omit [SigmaCompactSpace M] in
private theorem source_ball_sandwich_of_reserve
    {delta kappa eps C1 C2 a b A L : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (ha : 0 < a) (hA : 0 < A) (hL : 0 < L)
    (hinner : riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint a ⊆ K.domain.carrier)
    (houter : K.domain.carrier ⊆ riemannianBallOf (I := I3)
      (W.model.S.base.metric 0) W.model.basepoint b)
    (hbuffer : b ≤ modelRadius delta)
    (hreserve : L * b < 2 * (a / A))
    (hAcomp : 1 ≤ (1 - delta) * A ^ 2)
    (hLcomp : 1 + delta ≤ L ^ 2) :
    ∃ margin : ℝ, 0 < margin ∧ L * b < (2 - margin) * (a / A) ∧
      riemannianBallOf (I := I3)
          (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x (a / A) ⊆
        W.embedding '' K.domain.carrier ∧
      W.embedding '' K.domain.carrier ⊆ riemannianBallOf (I := I3)
        (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x (L * b) := by
  have hball : riemannianBallOf (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint b ⊆ riemannianClosedBallOf (I := I3)
        (W.model.S.base.metric 0) W.model.basepoint (modelRadius delta) := by
    intro y hy
    exact hy.le.trans (ENNReal.ofReal_le_ofReal hbuffer)
  have hsource : riemannianBallOf (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint b ⊆ W.embedding.source :=
    hball.trans ((riemannianClosedBallOf_mono (W.model.S.base.metric 0)
      W.model.basepoint (le_add_of_nonneg_right zero_le_one)).trans W.buffered_ball)
  have ht0 : (0 : ℝ) ∈ Icc (-modelDepth delta) 0 :=
    ⟨neg_nonpos.mpr (inv_nonneg.mpr W.eps_pos.le), le_rfl⟩
  have hlow : ∀ y ∈ riemannianClosedBallOf (I := I3)
      (W.model.S.base.metric 0) W.model.basepoint a, ∀ v : TangentSpace I3 y,
      (W.model.S.base.metric 0).inner y v v ≤ A ^ 2 *
        (rescaledMetric S t (S.scalar t x) W.scalar_pos 0).inner
          (W.embedding y) (mfderiv I3 I3 W.embedding y v)
            (mfderiv I3 I3 W.embedding y v) := by
    intro y hy v
    have heq := W.comparison.pullback_eq 0 y
      (hball (houter (hinner hy))) (fun _ => v)
    have he := W.comparison.equivalence 0 ht0 y
      (hball (houter (hinner hy))) v
    rw [heq] at he
    have hnonneg := inner_self_nonneg (W.model.S.base.metric 0) y v
    calc
      _ = 1 * (W.model.S.base.metric 0).inner y v v := by ring
      _ ≤ ((1 - delta) * A ^ 2) *
          (W.model.S.base.metric 0).inner y v v :=
        mul_le_mul_of_nonneg_right hAcomp hnonneg
      _ = A ^ 2 * ((1 - delta) * (W.model.S.base.metric 0).inner y v v) := by ring
      _ ≤ A ^ 2 *
          (rescaledMetric S t (S.scalar t x) W.scalar_pos 0).inner
            (W.embedding y) (mfderiv I3 I3 W.embedding y v)
              (mfderiv I3 I3 W.embedding y v) :=
        mul_le_mul_of_nonneg_left he.1 (sq_nonneg A)
  have hupp : ∀ y ∈ riemannianBallOf (I := I3)
      (W.model.S.base.metric 0) W.model.basepoint b, ∀ v : TangentSpace I3 y,
      (rescaledMetric S t (S.scalar t x) W.scalar_pos 0).inner
          (W.embedding y) (mfderiv I3 I3 W.embedding y v)
            (mfderiv I3 I3 W.embedding y v) ≤ L ^ 2 *
        (W.model.S.base.metric 0).inner y v v := by
    intro y hy v
    have heq := W.comparison.pullback_eq 0 y
      (hball hy) (fun _ => v)
    have he := W.comparison.equivalence 0 ht0 y
      (hball hy) v
    rw [heq] at he
    have hnonneg := inner_self_nonneg (W.model.S.base.metric 0) y v
    exact (he.2.trans (mul_le_mul_of_nonneg_right hLcomp hnonneg))
  have hresult := CompactDomain.map_strict_ball_sandwich K.domain
    (W.model.S.base.metric 0)
    (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) W.embedding W.model.basepoint
    (houter.trans hsource)
    ha hA hL hinner houter hsource hlow hupp hreserve
  simpa only [CompactDomain.map_carrier, W.base_map] using hresult

omit [SigmaCompactSpace M] in
theorem WindowedModelWitness.exists_source_image_radius_of_reserve
    {delta kappa eps C1 C2 a b margin : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (K : CanonicalWitness W.model.S eps C1 C2 W.model.basepoint 0)
    (hdelta : delta ≤ 1 / 8) (htolerance : delta ≤ margin / 8)
    (ha : 5 / 4 < a) (haC : a ≤ max C1 2) (hbuffer : b ≤ modelRadius delta)
    (hinner : riemannianClosedBallOf (I := I3) (W.model.S.base.metric 0)
      W.model.basepoint a ⊆ K.domain.carrier)
    (houter : K.domain.carrier ⊆ riemannianBallOf (I := I3)
      (W.model.S.base.metric 0) W.model.basepoint b)
    (hreserve : b < (2 - margin) * a) :
    ∃ r : ℝ, (Real.sqrt (S.scalar t x))⁻¹ ≤ r ∧
      r ≤ max C1 2 / Real.sqrt (S.scalar t x) ∧
      riemannianBallOf (I := I3) (S.base.metric t) x r ⊆ W.embedding '' K.domain.carrier ∧
      W.embedding '' K.domain.carrier ⊆ riemannianBallOf (I := I3) (S.base.metric t) x (2 * r) := by
  have hmargin : 0 < margin := by linarith [W.eps_pos]
  have ha0 : 0 < a := by linarith
  have hminus : 0 < 1 - delta := by linarith
  have hplus : 0 < 1 + delta := by linarith [W.eps_pos]
  have hAcomp : 1 ≤ (1 - delta) * ((1 - delta)⁻¹) ^ 2 := by
    rw [pow_two, ← mul_assoc, mul_inv_cancel₀ hminus.ne', one_mul]
    exact (one_le_inv₀ hminus).mpr (by linarith [W.eps_pos])
  have hLcomp : 1 + delta ≤ (1 + delta) ^ 2 := by nlinarith [W.eps_pos]
  have hratio : (1 + delta) * (2 - margin) < 2 * (1 - delta) := by
    nlinarith [mul_pos W.eps_pos hmargin]
  have htrans : (1 + delta) * b < 2 * (a / (1 - delta)⁻¹) := by
    rw [div_inv_eq_mul]
    calc
      _ < (1 + delta) * ((2 - margin) * a) := mul_lt_mul_of_pos_left hreserve hplus
      _ = ((1 + delta) * (2 - margin)) * a := by ring
      _ < (2 * (1 - delta)) * a := mul_lt_mul_of_pos_right hratio ha0
      _ = _ := by ring
  obtain ⟨sourceMargin, _, _, hball, hout⟩ :=
    source_ball_sandwich_of_reserve W K ha0 (inv_pos.mpr hminus) hplus
      hinner houter hbuffer htrans hAcomp hLcomp
  simp only [div_inv_eq_mul] at hball
  have hout' : W.embedding '' K.domain.carrier ⊆
      riemannianBallOf (I := I3) (rescaledMetric S t (S.scalar t x) W.scalar_pos 0)
        x (2 * (a * (1 - delta))) :=
    hout.trans (riemannianBallOf_mono _ _ (by simpa only [div_inv_eq_mul] using htrans.le))
  have hnum : 1 ≤ a * (1 - delta) := by
    have hh := mul_lt_mul_of_pos_right ha hminus
    nlinarith
  have hnumC : a * (1 - delta) ≤ max C1 2 := by
    exact (mul_le_of_le_one_right ha0.le (by linarith [W.eps_pos])).trans haC
  have hQ := Real.sqrt_pos.mpr W.scalar_pos
  have hscale (eta : ℝ) :
      riemannianBallOf (I := I3) (S.base.metric t) x (eta / Real.sqrt (S.scalar t x)) =
        riemannianBallOf (I := I3) (rescaledMetric S t (S.scalar t x) W.scalar_pos 0) x eta := by
    have heq := riemannianBallOf_scaleMetric (S.scalar t x) W.scalar_pos (S.base.metric t)
      x (eta / Real.sqrt (S.scalar t x))
    have hprod : Real.sqrt (S.scalar t x) * (eta / Real.sqrt (S.scalar t x)) = eta := by
      rw [mul_comm, div_mul_cancel₀ _ hQ.ne']
    rw [hprod] at heq
    simpa only [rescaledMetric, parabolicTime_zero] using heq.symm
  refine ⟨a * (1 - delta) / Real.sqrt (S.scalar t x), ?_, ?_, ?_, ?_⟩
  · simpa only [one_div] using div_le_div_of_nonneg_right hnum hQ.le
  · exact div_le_div_of_nonneg_right hnumC hQ.le
  · rw [hscale]
    exact hball
  · rw [show 2 * (a * (1 - delta) / Real.sqrt (S.scalar t x)) =
        (2 * (a * (1 - delta))) / Real.sqrt (S.scalar t x) by ring,
      hscale]
    exact hout'

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
