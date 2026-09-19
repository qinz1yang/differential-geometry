import DifferentialGeometry.Analysis.Calculus.Compactness.ArzelaAscoli
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.BallImage
import DifferentialGeometry.Geometry.Metric.Distance.Topology

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open scoped Manifold ContDiff NNReal Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

theorem PointedRiemannianConvergenceMaps.exists_lipschitz_subseq_limit
    [PreconnectedSpace P.M]
    (F : PointedRiemannianConvergenceMaps X P phi)
    (C : MetricConvergenceData F)
    (href : ∀ i, (C.domain i).referenceMetric = (C.domain i).limitMetric)
    (hcomplete : MetricComplete P)
    (f : ∀ i : ℕ, (X.obj i).M → ℝ) (K : ℝ≥0)
    (hLip : ∀ i x y, |f i x - f i y| ≤
      (K : ℝ) * (riemannianEDistOf (X.obj i).metric x y).toReal)
    (hbdd : ∃ B : ℝ, ∀ᶠ i in atTop, |f (phi i) (X.obj (phi i)).basepoint| ≤ B) :
    ∃ (psi : ℕ → ℕ) (g : C(P.M, ℝ)), StrictMono psi ∧
      (∀ x y, |g x - g y| ≤ (K : ℝ) * (riemannianEDistOf P.metric x y).toReal) ∧
      ∀ A : Set P.M, IsCompact A →
        TendstoUniformlyOn (fun i x => f (phi (psi i)) (F.map (psi i) x)) g atTop A := by
  let _ : TopologicalSpace.MetrizableSpace P.M := Manifold.metrizableSpace I P.M
  let _ : PseudoMetricSpace P.M := P.metric.toPseudoMetricSpace
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace H P.M
  let a : ℕ → P.M → ℝ := fun i x => f (phi i) (F.map i x)
  have hbound (R L : ℝ) (hR : 0 ≤ R) (hL : 1 < L) : ∀ᶠ i in atTop,
      ∀ x ∈ Metric.closedBall P.basepoint R, ∀ y ∈ Metric.closedBall P.basepoint R,
        |a i x - a i y| ≤ (K : ℝ) * L * dist x y := by
    filter_upwards [F.eventually_edist_map_le_on_closed_ball C href hcomplete P.basepoint hR hL]
      with i hi
    intro x hx y hy
    have hball (z : P.M) (hz : z ∈ Metric.closedBall P.basepoint R) :
        z ∈ riemannianClosedBallOf P.metric P.basepoint R := by
      change edist P.basepoint z ≤ ENNReal.ofReal R
      rw [edist_dist, ENNReal.ofReal_le_ofReal_iff hR, dist_comm]
      exact hz
    have hd := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (riemannianEDistOf_ne_top P.metric x y)) (hi.2 x (hball x hx) y (hball y hy))
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ L)] at hd
    calc
      _ ≤ (K : ℝ) * (riemannianEDistOf (X.obj (phi i)).metric (F.map i x) (F.map i y)).toReal :=
        hLip (phi i) _ _
      _ ≤ (K : ℝ) * (L * dist x y) := mul_le_mul_of_nonneg_left hd K.coe_nonneg
      _ = _ := by ring
  have hlocal (R : ℝ) (hR : 0 ≤ R) : ∀ᶠ i in atTop,
      LipschitzOnWith (2 * K) (a i) (Metric.closedBall P.basepoint R) := by
    filter_upwards [hbound R 2 hR (by norm_num)] with i hi
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat, mul_comm (K : ℝ) 2]
      using hi x hx y hy
  have hbase : ∃ B : ℝ, ∀ᶠ i in atTop, |a i P.basepoint| ≤ B := by
    obtain ⟨B, hB⟩ := hbdd
    refine ⟨B, hB.mono fun i hi => ?_⟩
    simpa only [a, PointedRiemannianConvergenceMaps.map, F.basepoint_map] using hi
  obtain ⟨psi, g, hpsi, _, hconv⟩ :=
    ArzelaAscoli.exists_lipschitz_subseq_limit_of_eventually_lipschitzOn_closedBall
      a P.basepoint (2 * K) hlocal hbase
  refine ⟨psi, g, hpsi, ?_, hconv⟩
  intro x y
  apply (le_iff_forall_one_lt_le_mul₀ (mul_nonneg K.coe_nonneg ENNReal.toReal_nonneg)).mpr
  intro L hL
  let R := max (dist x P.basepoint) (dist y P.basepoint)
  have hR : 0 ≤ R := dist_nonneg.trans (le_max_left _ _)
  have hx : x ∈ Metric.closedBall P.basepoint R := by
    exact le_max_left (dist x P.basepoint) (dist y P.basepoint)
  have hy : y ∈ Metric.closedBall P.basepoint R := by
    exact le_max_right (dist x P.basepoint) (dist y P.basepoint)
  have hpoint (z : P.M) : Tendsto (fun i => a (psi i) z) atTop (𝓝 (g z)) :=
    (hconv {z} isCompact_singleton).tendsto_at (mem_singleton z)
  apply le_of_tendsto ((hpoint x).sub (hpoint y)).abs
  filter_upwards [hpsi.tendsto_atTop (hbound R L hR hL)] with i hi
  have hh := hi x hx y hy
  change |a (psi i) x - a (psi i) y| ≤ (K : ℝ) * dist x y * L
  nlinarith only [hh]

end DifferentialGeometry.CheegerGromovCompactness
