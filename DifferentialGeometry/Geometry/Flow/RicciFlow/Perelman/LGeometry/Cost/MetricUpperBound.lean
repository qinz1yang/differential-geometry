import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import DifferentialGeometry.Topology.Manifold.ZeroDimensional

noncomputable section

open Set MeasureTheory Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
  (IsMetricNorm tensor0SBundle_enorm_eq_riemannianBundle_enorm)
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped _root_.Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [PreconnectedSpace M] {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lCost_le_riemannianEDistOf_sq_div_add_of_metric_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    {T r R : ℝ} (hr : 0 < r)
    (htime : ∀ u ∈ Icc 0 r, T - u ^ 2 ∈ D.carrier)
    (hmetric : ∀ u ∈ Icc 0 r, ∀ z : M, ∀ v : TangentSpace I z,
      (S.base.metric (T - u ^ 2)).inner z v v ≤ g.inner z v v)
    (hscalar : ∀ u ∈ Icc 0 (r ^ 2), ∀ z : M,
      0 ≤ S.scalar (T - u) z ∧ S.scalar (T - u) z ≤ R)
    (p q : M) :
    lCost S T p q (r ^ 2) ≤
      (riemannianEDistOf (I := I) g p q).toReal ^ 2 / (2 * r) +
        2 * R * r ^ 3 := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : Nonempty M := ⟨p⟩
  let : ConnectedSpace M := ⟨inferInstance⟩
  let : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : CompleteSpace M := hg.complete
  let hEnorm : IsMetricNorm (I := I) (M := M) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  obtain ⟨alpha, halpha, hzero, hend, hspeed⟩ :
      ∃ alpha : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I 1 alpha ∧
        alpha 0 = p ∧ alpha r = q ∧ ∀ u : ℝ,
        g.inner (alpha u) (lVelocity alpha u) (lVelocity alpha u) =
          (riemannianEDistOf (I := I) g p q).toReal ^ 2 / r ^ 2 := by
    by_cases hdim : Module.finrank ℝ E = 0
    · let : Subsingleton M := subsingleton_of_preconnected_of_finrank_eq_zero I hdim
      have hpq : p = q := Subsingleton.elim _ _
      refine ⟨fun _ => p, contMDiff_const, rfl, hpq, ?_⟩
      intro u
      rw [← hpq]
      have hv : lVelocity (I := I) (fun _ : ℝ => p) u = 0 := by
        simp only [lVelocity, mfderiv_const]
        with_unfolding_all exact zero_apply _
      rw [hv, riemannianEDistOf_self]
      simp only [map_zero, ENNReal.toReal_zero, zero_pow (by decide : 2 ≠ 0),
        zero_div]
    · let : NeZero (Module.finrank ℝ E) := ⟨hdim⟩
      obtain ⟨v, hv, hvnorm⟩ := minExp_of_ne_top g hEnorm p q
        (riemannianEDist_ne_top (I := I) p q)
      let w : TangentSpace I p := r⁻¹ • v
      let alpha : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p w
      have halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha := by
        rw [← contMDiffOn_univ]
        exact intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p w
      have hzero : alpha 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p w
      have hrw : r • w = v := by
        dsimp only [w]
        rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      have hend : alpha r = q := by
        change intrinsicGeodesic (I := I) g hEnorm p w r = q
        rw [← intrinsicGeodesic_smul, ← expMapIntrinsic_def, hrw]
        exact hv
      have hvnormSq : g.inner p v v = (riemannianEDistOf (I := I) g p q).toReal ^ 2 := by
        exact (Real.sq_sqrt (gInner_self_nonneg (I := I) g p v)).symm.trans
          (congrArg (fun x : ℝ => x ^ 2) hvnorm)
      have hspeed (u : ℝ) :
          g.inner (alpha u) (lVelocity alpha u) (lVelocity alpha u) =
            (riemannianEDistOf (I := I) g p q).toReal ^ 2 / r ^ 2 := by
        change g.inner (intrinsicGeodesic (I := I) g hEnorm p w u)
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p w) u 1)
          (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p w) u 1) = _
        rw [intrinsicGeodesic_speedSq_eq]
        change g.inner p (r⁻¹ • v) (r⁻¹ • v) = _
        rw [gInner_smul_self, hvnormSq]
        simp only [div_eq_mul_inv, inv_pow, mul_comm]
      exact ⟨alpha, halpha, hzero, hend, hspeed⟩
  have hR : 0 ≤ R :=
    (hscalar 0 ⟨le_rfl, sq_nonneg r⟩ p).1.trans
      (hscalar 0 ⟨le_rfl, sq_nonneg r⟩ p).2
  have hcont : ContinuousOn (lRegularizedLagrangian S T alpha) (Icc 0 r) := by
    have h := lRegularizedLagrangian_continuousOn_carrier S hS alpha halpha
    have hc := h.comp (s := Icc 0 r)
      (continuous_const.prodMk continuous_id).continuousOn (fun u hu => htime u hu)
    simpa only [Function.comp_def, id_eq] using hc
  have hpoint (u : ℝ) (hu : u ∈ Icc 0 r) :
      lRegularizedLagrangian S T alpha u ≤
        (1 / 2 : ℝ) * ((riemannianEDistOf (I := I) g p q).toReal ^ 2 / r ^ 2) +
          2 * r ^ 2 * R := by
    have hu2 : u ^ 2 ≤ r ^ 2 := (sq_le_sq₀ hu.1 hr.le).mpr hu.2
    have hkin := hmetric u hu (alpha u) (lVelocity alpha u)
    rw [hspeed u] at hkin
    have hsc := (hscalar (u ^ 2) ⟨sq_nonneg u, hu2⟩ (alpha u)).2
    have hpot := mul_le_mul_of_nonneg_left hsc (by positivity : 0 ≤ 2 * u ^ 2)
    have hmax := mul_le_mul_of_nonneg_right hu2 hR
    change (1 / 2 : ℝ) * _ + 2 * u ^ 2 * _ ≤ _
    nlinarith
  have haction := intervalIntegral.integral_mono_on (μ := volume) hr.le
    (hcont.intervalIntegrable_of_Icc hr.le) intervalIntegrable_const hpoint
  rw [intervalIntegral.integral_const] at haction
  have hbound : lRegularizedAction S T alpha 0 r ≤
      (riemannianEDistOf (I := I) g p q).toReal ^ 2 / (2 * r) + 2 * R * r ^ 3 := by
    calc
      lRegularizedAction S T alpha 0 r ≤
          (r - 0) • ((1 / 2 : ℝ) *
            ((riemannianEDistOf (I := I) g p q).toReal ^ 2 / r ^ 2) +
              2 * r ^ 2 * R) := haction
      _ = _ := by
        simp only [sub_zero, smul_eq_mul]
        field_simp [hr.ne']
  have hcost := lCost_le_lRegularizedAction_of_scalar_nonneg S (sq_nonneg r)
    (fun u hu z => (hscalar u hu z).1) alpha halpha
  rw [Real.sqrt_sq hr.le, hzero, hend] at hcost
  exact hcost.trans hbound

end DifferentialGeometry.PDE.RicciFlow.Perelman
