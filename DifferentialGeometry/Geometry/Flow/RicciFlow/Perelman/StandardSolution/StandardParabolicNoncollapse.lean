import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CompleteNoncollapse
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Injectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.DerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardUniformExistence

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

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private def parabolicCapCurvatureBound : ℝ :=
  Classical.choose (DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bound_iterCov_metricRm04 0)

private def parabolicCapInjectivityBound : ℝ :=
  Classical.choose DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_le_intrinsicInjectivityRadius

def standardParabolicNoncollapseCoeff : ℝ :=
  boundedGeometryNoncollapseCoeff 3 1 parabolicCapCurvatureBound parabolicCapInjectivityBound

theorem standardParabolicNoncollapseCoeff_pos : 0 < standardParabolicNoncollapseCoeff := by
  have hK : 0 < parabolicCapCurvatureBound :=
    (Classical.choose_spec
      (DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bound_iterCov_metricRm04 0)).1
  have hc : 0 < parabolicCapInjectivityBound :=
    (Classical.choose_spec
      DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_le_intrinsicInjectivityRadius).1
  exact boundedGeometryNoncollapseCoeff_pos 3 1 _ _ zero_lt_one hK hc

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem standard_uniform_parabolic_noncollapse :
    Nonempty StandardSolution ∧ 0 < standardParabolicNoncollapseCoeff ∧
      ∀ S : PartialStandardSolution,
        ∀ time : RealTimeInterval.FlowTime (lifetimeInterval S.lifetime S.lifetime_pos),
          (time : ℝ) < 1 → ∀ B : FlowMetricBall S.toSolutionOn time,
            B.radius ≤ 1 →
            Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ) ⊆ S.domain →
            (∀ t ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ), ∀ z ∈ B.set,
              Real.sqrt (FlowMetricBall.rmNormSq S.toSolutionOn t z) ≤ (B.radius ^ 2)⁻¹) →
            B.IsKappaNoncollapsed standardParabolicNoncollapseCoeff := by
  let : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
  have hK : 0 < parabolicCapCurvatureBound :=
    (Classical.choose_spec
      (DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bound_iterCov_metricRm04 0)).1
  have hc : 0 < parabolicCapInjectivityBound :=
    (Classical.choose_spec
      DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_le_intrinsicInjectivityRadius).1
  refine ⟨standard_solution_nonempty, standardParabolicNoncollapseCoeff_pos, ?_⟩
  intro S time htimeOne B _hradius hslab hRm
  have htime := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos (time : ℝ)).mp
    time.property
  have hnonneg : (lifetimeInterval S.lifetime S.lifetime_pos).carrier ⊆ Ici (0 : ℝ) := by
    intro t ht
    exact ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mp ht).1
  have hleft : 0 ≤ (time : ℝ) - B.radius ^ 2 :=
    hnonneg (hslab ⟨le_rfl, sub_le_self _ (sq_nonneg _)⟩)
  have htimePos : 0 < (time : ℝ) := by
    have hr2 : 0 < B.radius ^ 2 := sq_pos_of_pos B.radius_pos
    linarith only [hleft, hr2]
  have hfull : Icc (0 : ℝ) (time : ℝ) ⊆ S.domain :=
    (Icc_subset_lifetimeInterval_iff S.lifetime S.lifetime_pos (time : ℝ) htime.1).mpr htime.2
  have hregular : Ioc (0 : ℝ) (time : ℝ) ⊆
      (lifetimeInterval S.lifetime S.lifetime_pos).regular := by
    intro t ht
    exact (mem_lifetimeInterval_regular S.lifetime S.lifetime_pos t).mpr
      ⟨ht.1, (ENNReal.ofReal_le_ofReal ht.2).trans_lt htime.2⟩
  have hcomplete : ∀ t ∈ Icc (0 : ℝ) (time : ℝ),
      RiemannianMetricComplete (I := 𝓡 3) (S.toSolutionOn.base.metric t) :=
    fun t ht ↦ S.complete t (hfull ht)
  obtain ⟨Q, _hQ, hbound⟩ := S.curvature_bound (time : ℝ) htime.1 htime.2
  have hbounded : ∃ Q' : ℝ, ∀ t ∈ Icc (0 : ℝ) (time : ℝ), ∀ z : E3,
      normSq0S (I := 𝓡 3) (S.toSolutionOn.base.metric t) z 4
        (S.toSolutionOn.base.rm04 t z) ≤ Q' :=
    ⟨Q ^ 2, fun t ht z ↦ (Real.sqrt_le_iff.mp (hbound t ht z)).2⟩
  have hinit : ∀ z : E3, Real.sqrt (normSq0S (I := 𝓡 3)
      (S.toSolutionOn.base.metric 0) z 4 (S.toSolutionOn.base.rm04 0 z)) ≤
        parabolicCapCurvatureBound := by
    intro z
    change Real.sqrt (normSq0S (S.metric 0) z 4 (metricRm04 (S.metric 0) z)) ≤ _
    rw [S.initial]
    exact (Classical.choose_spec
      (DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_bound_iterCov_metricRm04 0)).2 z
  have hInj : ∀ p : E3, ENNReal.ofReal parabolicCapInjectivityBound ≤
      intrinsicInjectivityRadiusOf (S.toSolutionOn.base.metric 0)
        (hcomplete 0 ⟨le_rfl, htimePos.le⟩) p := by
    intro p
    simpa only [parabolicCapInjectivityBound, intrinsicInjectivityRadiusOf_model_eq,
      PartialStandardSolution.toSolutionOn_metric, S.initial] using
        (Classical.choose_spec
          DifferentialGeometry.PDE.RicciFlow.StandardCap.exists_pos_le_intrinsicInjectivityRadius).2 p
  have hRmSq : ∀ t ∈ Icc ((time : ℝ) - B.radius ^ 2) (time : ℝ), ∀ z ∈ B.set,
      B.radius ^ 4 * FlowMetricBall.rmNormSq S.toSolutionOn t z ≤ 1 := by
    intro t ht z hz
    have hsquare := (Real.sqrt_le_iff.mp (hRm t ht z hz)).2
    calc
      _ ≤ B.radius ^ 4 * ((B.radius ^ 2)⁻¹) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (pow_nonneg B.radius_pos.le _)
      _ = 1 := by
        rw [inv_pow, ← div_eq_mul_inv, ← pow_mul]
        norm_num [B.radius_pos.ne']
  have h := fixed_terminal_ball_noncollapsed_complete 1
    parabolicCapCurvatureBound parabolicCapInjectivityBound zero_lt_one hK hc
    S.toSolutionOn S.isSolutionOn time htimePos htimeOne.le
    hnonneg hfull hregular hcomplete hbounded hinit hInj B hslab hRmSq
  simpa only [finrank_euclideanSpace, Fintype.card_fin, standardParabolicNoncollapseCoeff] using h

end DifferentialGeometry.PDE.RicciFlow

end
