import DifferentialGeometry.Geometry.Metric.Comparison.CompactMapDistance
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.AmbientQuadraticControl

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology

universe u v uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedRiemannianSeq.{u, uE, uH} I}
  {L : PointedRiemannianManifold.{u, uE, uH} I} {subseq : ℕ → ℕ}
  {F : PointedRiemannianConvergenceMaps X L subseq}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem eventually_riemannianEDistOf_map_lt_of_metric_convergence
    (C : MetricConvergenceData F)
    (href : ∀ k, (C.domain k).referenceMetric = (C.domain k).limitMetric)
    (x y : L.M) {r : ℝ} (hxy : riemannianEDistOf L.metric x y < ENNReal.ofReal r) :
    ∀ᶠ k in atTop, riemannianEDistOf (X.obj (subseq k)).metric (F.map k x) (F.map k y) <
      ENNReal.ofReal r := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : RiemannianBundle (fun x : L.M => TangentSpace I x) := L.riemBundle
  let : IsContinuousRiemannianBundle E (fun x : L.M => TangentSpace I x) := L.riemBundle_cont
  let : ∀ k, RiemannianBundle (fun x : (X.obj (subseq k)).M => TangentSpace I x) :=
    fun k => (X.obj (subseq k)).riemBundle
  let : ∀ k, IsContinuousRiemannianBundle E
      (fun x : (X.obj (subseq k)).M => TangentSpace I x) :=
    fun k => (X.obj (subseq k)).riemBundle_cont
  have hnorm := Geometry.Riemannian.isMetricNorm_of_riemannianBundle L.metric
  have hnorms (k : ℕ) := Geometry.Riemannian.isMetricNorm_of_riemannianBundle (X.obj (subseq k)).metric
  have hupper : ∀ K : Set L.M, IsCompact K → ∀ B : ℝ, 1 < B →
      ∀ᶠ k in atTop, (∀ z ∈ K, ContMDiffAt I I 1 (F.map k) z) ∧
        ∀ z ∈ K, ∀ v : TangentSpace I z,
          ‖mfderiv I I (F.map k) z v‖ₑ ≤ ENNReal.ofReal B * ‖v‖ₑ := by
    intro K hK B hB
    obtain ⟨N, hN⟩ := PDE.RicciFlow.Perelman.KappaSolutions.exists_pointed_full_ambient_quadratic_control
      C href K hK (B ^ 2 - 1) (by nlinarith)
    filter_upwards [eventually_ge_atTop N] with k hk
    refine ⟨?_, ?_⟩
    · intro z hz
      exact ((F.partialDiffeomorph k).contMDiffOn_toFun.contMDiffAt
        ((F.partialDiffeomorph k).open_source.mem_nhds ((hN k hk).1 hz))).of_le (by simp)
    · intro z hz v
      have h := (abs_le.mp ((hN k hk).2 z hz v)).2
      have hb : 0 ≤ B := by linarith
      have hnv := hnorms k (F.map k z) (mfderiv I I (F.map k) z v)
      have hn := hnorm z v
      erw [hnv, hn, ← ENNReal.ofReal_mul hb]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ Real.sqrt (B ^ 2 * L.metric.inner z v v) :=
          Real.sqrt_le_sqrt (by nlinarith)
        _ = _ := by rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hb]
  have hxy' : Manifold.riemannianEDist I x y < ENNReal.ofReal r := by
    exact (riemannianEDistOf_eq_riemannianEDist L.metric hnorm x y).symm.trans_lt hxy
  have h := Geometry.Riemannian.eventually_riemannianEDist_map_lt F.map hupper x y hxy'
  filter_upwards [h] with k hk
  rwa [riemannianEDistOf_eq_riemannianEDist (X.obj (subseq k)).metric (hnorms k)]

end DifferentialGeometry.CheegerGromovCompactness
