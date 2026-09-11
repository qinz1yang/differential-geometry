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
