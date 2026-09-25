import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.SpeedBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.DomainContinuation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Ray.ActionIntegrability
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Topology.FirstExit

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mem_lRegularizedDomain_and_edist_lt_of_prefix_speed_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) (Z : TangentSpace I x)
    (g : SmoothRiemannianMetric I M) (B r A Q : ℝ)
    (hB : 0 ≤ B) (hr : 0 < r) (hA : 0 ≤ A)
    (hslab : Icc (T - B ^ 2) T ⊆ D.regular)
    (hcompact : IsCompact {y : M | riemannianEDistOf g x y ≤ ENNReal.ofReal r})
    (hcompare : ∀ q ∈ Icc (0 : ℝ) B, ∀ y : M,
      riemannianEDistOf g x y ≤ ENNReal.ofReal r → ∀ v : TangentSpace I y,
      g.inner y v v ≤ A * (S.base.metric (T - q ^ 2)).inner y v v)
    (hspeed : ∀ q ∈ Icc (0 : ℝ) B, q ∈ lRegularizedDomain S T x Z →
      (∀ u ∈ Icc (0 : ℝ) q,
        riemannianEDistOf g x (lRegularizedCurve S T x Z u) ≤ ENNReal.ofReal r) →
      lRegularizedSpeedSq S T (lRegularizedCurve S T x Z) q ≤ Q)
    (hreach : B * Real.sqrt (A * Q) < r) :
    B ∈ lRegularizedDomain S T x Z ∧
      ∀ s ∈ Icc (0 : ℝ) B,
        riemannianEDistOf g x (lRegularizedCurve S T x Z s) < ENNReal.ofReal r := by
  let alpha : ℝ → M := lRegularizedCurve S T x Z
  let K : Set M := {y : M | riemannianEDistOf g x y ≤ ENNReal.ofReal r}
  let O : Set M := {y : M | riemannianEDistOf g x y < ENNReal.ofReal r}
  have hKclosed : IsClosed K := hcompact.isClosed
  have hOopen : IsOpen O := by
    let : RiemannianBundle (fun y : M => TangentSpace I y) := ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
      ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
    exact isOpen_lt (continuous_riemannianEDist g x) continuous_const
  have hOK : O ⊆ K := by
    intro y hy
    exact (show riemannianEDistOf g x y < ENNReal.ofReal r from hy).le
  have hxO : x ∈ O := by
    change riemannianEDistOf g x x < ENNReal.ofReal r
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hxKi : x ∈ interior K := (interior_maximal hOK hOopen) hxO
  have hzero : alpha 0 = x := lRegularizedCurve_zero S T x Z
  have hstrict : ∀ s ∈ Icc (0 : ℝ) B,
      s ∈ lRegularizedDomain S T x Z →
      (∀ u ∈ Icc (0 : ℝ) s, alpha u ∈ K) → alpha s ∈ O := by
    intro s hs hsdom hstay
    have hc1 := lRegularizedCurve_c1On S hS T x Z hsdom
    have hEi := integrableOn_inner_lVelocity_lRegularizedCurve S hS T x Z g
      (fun u hu => lRegularizedDomain_segment S T x Z hsdom hu.1 hu.2)
    have hEint : IntervalIntegrable (fun u =>
        g.inner (alpha u) (lVelocity (I := I) alpha u) (lVelocity (I := I) alpha u))
        volume 0 s := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hs.1]
      exact hEi
    have henergy : curveEnergy g alpha 0 s ≤ s * (A * Q) := by
      calc
        curveEnergy g alpha 0 s ≤ ∫ _u in (0 : ℝ)..s, A * Q := by
          unfold curveEnergy
          apply intervalIntegral.integral_mono_on hs.1 hEint intervalIntegrable_const
          intro q hq
          have hqB : q ∈ Icc (0 : ℝ) B := ⟨hq.1, hq.2.trans hs.2⟩
          have hqdom := lRegularizedDomain_segment S T x Z hsdom hq.1 hq.2
          have hbound := hspeed q hqB hqdom
            (fun u hu => hstay u ⟨hu.1, hu.2.trans hq.2⟩)
          exact (hcompare q hqB (alpha q) (hstay q hq)
            (lVelocity (I := I) alpha q)).trans
              (mul_le_mul_of_nonneg_left hbound hA)
        _ = s * (A * Q) := by
          simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    have hed := edistOf_le_budget g hs.1 hc1 hEi henergy
    have hrad : Real.sqrt s * Real.sqrt (s * (A * Q)) < r := by
      calc
        Real.sqrt s * Real.sqrt (s * (A * Q)) = s * Real.sqrt (A * Q) := by
          rw [Real.sqrt_mul hs.1, ← mul_assoc, ← pow_two, Real.sq_sqrt hs.1]
        _ ≤ B * Real.sqrt (A * Q) :=
          mul_le_mul_of_nonneg_right hs.2 (Real.sqrt_nonneg _)
        _ < r := hreach
    have hed' : riemannianEDistOf g x (alpha s) ≤
        ENNReal.ofReal (Real.sqrt s * Real.sqrt (s * (A * Q))) := by
      simpa only [alpha, lRegularizedCurve_zero, sub_zero] using hed
    exact hed'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hrad)
  have hstay : ∀ s ∈ Icc (0 : ℝ) B,
      s ∈ lRegularizedDomain S T x Z → alpha s ∈ K := by
    intro s hs hsdom
    by_contra hsK
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (by
      intro h
      apply hsK
      rw [← h, hzero]
      exact interior_subset hxKi)
    have hc : ContinuousOn alpha (Icc (0 : ℝ) s) :=
      (lRegularizedCurve_c1On S hS T x Z hsdom).continuousOn
    obtain ⟨t, ht, htstay, htfront⟩ :=
      exists_first_exit_frontier hKclosed hspos hc (hzero ▸ hxKi) hsK
    have htdom := lRegularizedDomain_segment S T x Z hsdom ht.1.le ht.2
    have htO := hstrict t ⟨ht.1.le, ht.2.trans hs.2⟩ htdom htstay
    have htnot : alpha t ∉ interior K := htfront.2
    exact htnot ((interior_maximal hOK hOopen) htO)
  have hbdom : B ∈ lRegularizedDomain S T x Z :=
    mem_lRegularizedDomain_of_isCompact_range_of_speed_le S hS T x Z B hB hslab
      K hcompact Q hstay
      (fun s hs hsdom => hspeed s hs hsdom (fun u hu =>
        hstay u ⟨hu.1, hu.2.trans hs.2⟩
          (lRegularizedDomain_segment S T x Z hsdom hu.1 hu.2)))
  refine ⟨hbdom, ?_⟩
  intro s hs
  have hsdom := lRegularizedDomain_segment S T x Z hbdom hs.1 hs.2
  exact hstrict s hs hsdom (fun u hu =>
    hstay u ⟨hu.1, hu.2.trans hs.2⟩
      (lRegularizedDomain_segment S T x Z hsdom hu.1 hu.2))

end DifferentialGeometry.PDE.RicciFlow.Perelman

noncomputable section
open Set Bundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
 [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {D : RealTimeInterval}

theorem mem_lRegularizedDomain_and_edist_lt_of_local_gradient_ricci_bounds
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) (T : ℝ) (x : M)
    (g : SmoothRiemannianMetric I M) {b r A G K R : ℝ}
    (hb : 0 < b) (hr : 0 < r) (hA : 0 ≤ A) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hslab : Icc (T - b ^ 2) T ⊆ D.regular)
    (hcpt : IsCompact {y : M | riemannianEDistOf g x y ≤ ENNReal.ofReal r})
    (hcompare : ∀ q ∈ Icc (0 : ℝ) b, ∀ y : M,
      riemannianEDistOf g x y ≤ ENNReal.ofReal r → ∀ w : TangentSpace I y,
      g.inner y w w ≤ A * (S.base.metric (T - q ^ 2)).inner y w w)
    (hgrad : ∀ q ∈ Icc (0 : ℝ) b, ∀ y : M,
      riemannianEDistOf g x y ≤ ENNReal.ofReal r → ∀ w : TangentSpace I y,
      |(S.base.metric (T - q ^ 2)).inner y (gradientFun (S.base.metric (T - q ^ 2)) (S.scalar (T - q ^ 2)) y) w| ≤
        G * Real.sqrt ((S.base.metric (T - q ^ 2)).inner y w w))
    (hric : ∀ q ∈ Icc (0 : ℝ) b, ∀ y : M,
      riemannianEDistOf g x y ≤ ENNReal.ofReal r → ∀ w : TangentSpace I y,
      |S.ricciAt (T - q ^ 2) y (vec2 w w)| ≤ K * (S.base.metric (T - q ^ 2)).inner y w w)
    (hreach : b * Real.sqrt (A * (Real.exp ((1 + 2 * G * b ^ 2 + 4 * K * b) * b) * (4 * R ^ 2 + 1))) < r)
    (Z : TangentSpace I x) (hZ : (S.base.metric T).inner x Z Z ≤ R ^ 2) :
    b ∈ lRegularizedDomain S T x Z ∧ ∀ q ∈ Icc (0 : ℝ) b,
      riemannianEDistOf g x (lRegularizedCurve S T x Z q) < ENNReal.ofReal r := by
  let Q := Real.exp ((1 + 2 * G * b ^ 2 + 4 * K * b) * b) * (4 * R ^ 2 + 1)
  have hT : T ∈ D.regular := hslab ⟨sub_le_self _ (sq_nonneg b), le_rfl⟩
  have hzero : lRegularizedSpeedSq S T (lRegularizedCurve S T x Z) 0 ≤ 4 * R ^ 2 := by
    unfold lRegularizedSpeedSq
    norm_num only [zero_pow, sub_zero]
    rw [lRegularizedCurve_zero, lRegularizedCurve_velocity_zero S hS T x Z hT]
    have hh := metric_smul2 (I := I) (S.base.metric T) (2 : ℝ) Z
    nlinarith [hZ]
  apply mem_lRegularizedDomain_and_edist_lt_of_prefix_speed_le S hS T x Z g b r A Q hb.le hr hA
    hslab hcpt hcompare ?_ hreach
  intro q hq hqdom hstay
  have hc : 0 < 1 + 2 * G * b ^ 2 + 4 * K * b := by positivity
  have hC : 1 ≤ Real.exp ((1 + 2 * G * b ^ 2 + 4 * K * b) * b) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hc.le hb.le)
  by_cases hqzero : q = 0
  · subst q
    exact hzero.trans (by dsimp [Q]; nlinarith [sq_nonneg R])
  have hqpos : 0 < q := lt_of_le_of_ne hq.1 (Ne.symm hqzero)
  have hcurve := lRegularizedCurve_isLRegularizedCurveOn S hS T x Z hqpos hqdom
  have hg := lRegularizedSpeedSq_le_of_gradient_ricci_bounds S hS T hcurve 0 q G K b hG hK
    Subset.rfl (fun s hs => by
      rw [uIcc_of_le hq.1] at hs
      rw [abs_of_nonneg hs.1]
      exact hs.2.trans hq.2)
    (fun s hs => by
      rw [uIcc_of_le hq.1] at hs
      exact hgrad s ⟨hs.1, hs.2.trans hq.2⟩ _ (hstay s hs) _)
    (fun s hs => by
      rw [uIcc_of_le hq.1] at hs
      exact hric s ⟨hs.1, hs.2.trans hq.2⟩ _ (hstay s hs) _)
  have hratio : (1 + 2 * G * b ^ 2) / (1 + 2 * G * b ^ 2 + 4 * K * b) ≤ 1 := by
    apply (div_le_iff₀ hc).mpr
    nlinarith [mul_nonneg hK hb.le]
  have hexp : Real.exp ((1 + 2 * G * b ^ 2 + 4 * K * b) * |q - 0|) ≤
      Real.exp ((1 + 2 * G * b ^ 2 + 4 * K * b) * b) := by
    rw [sub_zero, abs_of_nonneg hq.1]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hq.2 hc.le)
  apply hg.trans
  exact mul_le_mul hexp (add_le_add hzero hratio)
    (add_nonneg (lRegularizedSpeedSq_nonneg S T _ 0) (div_nonneg (by positivity) hc.le))
    (Real.exp_pos _).le

theorem exists_pos_lRegularizedCurve_mem_ball_of_local_gradient_ricci_bounds
    {B r A G K R : ℝ} (hB : 0 < B) (hr : 0 < r) (hA : 0 ≤ A) (hG : 0 ≤ G) (hK : 0 ≤ K) :
    ∃ b ∈ Ioc (0 : ℝ) B,
      ∀ {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D), IsSolutionOn S →
      ∀ (T : ℝ) (x : M) (g : SmoothRiemannianMetric I M),
      Icc (T - B ^ 2) T ⊆ D.regular →
      IsCompact {y : M | riemannianEDistOf g x y ≤ ENNReal.ofReal r} →
      (∀ q ∈ Icc (0 : ℝ) B, ∀ y : M, riemannianEDistOf g x y ≤ ENNReal.ofReal r →
        ∀ w : TangentSpace I y, g.inner y w w ≤ A * (S.base.metric (T - q ^ 2)).inner y w w) →
      (∀ q ∈ Icc (0 : ℝ) B, ∀ y : M, riemannianEDistOf g x y ≤ ENNReal.ofReal r →
        ∀ w : TangentSpace I y,
        |(S.base.metric (T - q ^ 2)).inner y (gradientFun (S.base.metric (T - q ^ 2)) (S.scalar (T - q ^ 2)) y) w| ≤
          G * Real.sqrt ((S.base.metric (T - q ^ 2)).inner y w w)) →
      (∀ q ∈ Icc (0 : ℝ) B, ∀ y : M, riemannianEDistOf g x y ≤ ENNReal.ofReal r →
        ∀ w : TangentSpace I y, |S.ricciAt (T - q ^ 2) y (vec2 w w)| ≤
          K * (S.base.metric (T - q ^ 2)).inner y w w) →
      ∀ Z : TangentSpace I x, (S.base.metric T).inner x Z Z ≤ R ^ 2 →
        b ∈ lRegularizedDomain S T x Z ∧ ∀ q ∈ Icc (0 : ℝ) b,
          riemannianEDistOf g x (lRegularizedCurve S T x Z q) < ENNReal.ofReal r := by
  let Q := Real.exp ((1 + 2 * G * B ^ 2 + 4 * K * B) * B) * (4 * R ^ 2 + 1)
  let b := min B (r / (2 * (Real.sqrt (A * Q) + 1)))
  have hb : 0 < b := lt_min hB (div_pos hr (by positivity))
  have hbB : b ≤ B := min_le_left _ _
  have hbR : b ≤ r / (2 * (Real.sqrt (A * Q) + 1)) := min_le_right _ _
  have hreach : b * Real.sqrt (A * Q) < r := by
    have hm := (le_div_iff₀ (by positivity : 0 < 2 * (Real.sqrt (A * Q) + 1))).mp hbR
    nlinarith [Real.sqrt_nonneg (A * Q)]
  refine ⟨b, ⟨hb, hbB⟩, ?_⟩
  intro D S hS T x g hslab hcpt hcompare hgrad hric Z hZ
  have hb2 : b ^ 2 ≤ B ^ 2 := (sq_le_sq₀ hb.le hB.le).mpr hbB
  have hsub : Icc (0 : ℝ) b ⊆ Icc (0 : ℝ) B := Icc_subset_Icc le_rfl hbB
  apply mem_lRegularizedDomain_and_edist_lt_of_local_gradient_ricci_bounds S hS T x g hb hr hA hG hK
    (fun t ht => hslab ⟨by linarith [ht.1], ht.2⟩) hcpt
    (fun q hq => hcompare q (hsub hq)) (fun q hq => hgrad q (hsub hq)) (fun q hq => hric q (hsub hq)) ?_ Z hZ
  have hcoeff : 1 + 2 * G * b ^ 2 + 4 * K * b ≤ 1 + 2 * G * B ^ 2 + 4 * K * B := by
    gcongr
  have hexp := Real.exp_le_exp.mpr (mul_le_mul hcoeff hbB hb.le (by positivity))
  have hQ : Real.exp ((1 + 2 * G * b ^ 2 + 4 * K * b) * b) * (4 * R ^ 2 + 1) ≤ Q :=
    mul_le_mul_of_nonneg_right hexp (by positivity)
  exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hQ hA)) hb.le).trans_lt hreach

end DifferentialGeometry.PDE.RicciFlow.Perelman
end
