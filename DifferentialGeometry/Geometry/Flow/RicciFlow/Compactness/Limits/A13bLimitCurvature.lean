import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.A13bFixedScaleFlowLimit
import DifferentialGeometry.Geometry.Metric.Convergence.Curvature.TensorConvergence

/-!
# A13b, group G4: the curvature bound passes to the local flow limit

Erratum E7 of `docs/geometrization/chapter13/design-a13b-fixed-scale-flow-limit-20261004.md`: on the
limit of A13b, `curvDerivNormSq 0 (Gloc k s) z ≤ (K k)^2` for `s ∈ [-(τ k / 2), 0]` and `z ∈ V k`.  This
is not a field of `LocalPointedFlowLimit.lean:221`; it is proved by pulling the bound of output (i) back
along the real subsequence `f ∘ ψ` and passing to the limit in the `C²` convergence.

`FILL910.curvDerivNormSq_zero_le_of_local_flow_limit` is the transfer in the exact output shape of
`:221` / A13b (maps `φ k j` into `W k (f j)`, second subsequence `ψ`, windows `[-c k, 0]`), for an
arbitrary bound `B k`; no sign, no completeness and no time-0 identity are used.  Per point it is the
argument of `ST/TracedRegionWindowLimit.lean:137` (one ball `V k`, the convergence at the singleton
`{z}`, `MetricCPConvergenceOn.tendsto_normSq_metricRm04At`, `le_of_tendsto`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

namespace FILL910

universe u

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.CheegerGromovCompactness

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

/-- G4 (transfer).  A bound `curvDerivNormSq 0 (h k n s) ≤ B k` on `W k n` for `s ∈ [-c k, 0]`,
eventually in `n`, passes to the local limit flows `Gloc k` on `V k`, in the output shape of
`exists_pointed_local_flow_limits_of_local_solutions` (and of A13b with `c k = τ k / 2`). -/
theorem curvDerivNormSq_zero_le_of_local_flow_limit
    {X : PointedRiemannianSeq.{u, 0, 0} ThreeModel}
    {P : PointedRiemannianManifold.{u, 0, 0} ThreeModel}
    {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
    {h : ∀ k n, ℝ → SmoothRiemannianMetric ThreeModel (W k n)} {f : ℕ → ℕ} (hf : StrictMono f)
    {V : ℕ → Opens P.M} {N : ℕ → ℕ} {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
    {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph ThreeModel ThreeModel ∞ (φ k j hj)}
    {c : ℕ → ℝ} {Gloc : ∀ k : ℕ, ℝ → SmoothRiemannianMetric ThreeModel (V k)}
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hconv : ∀ k (Kc : Set (V k)), IsCompact Kc → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ s ∈ Icc (-c k) 0,
        metricDerivNormSupOn Kc p
          (localPullMetric (h k (f (ψ i)) s) (φ k (ψ i) hi) (hφ k (ψ i) hi))
          (Gloc k s) (P.metric.restrictOpen (V k)) < η)
    {B : ℕ → ℝ} (hbound : ∀ k : ℕ, ∀ᶠ n in atTop, ∀ s ∈ Icc (-c k) 0, ∀ x : W k n,
      curvDerivNormSq 0 (h k n s) x ≤ B k) :
    ∀ k, ∀ s ∈ Icc (-c k) 0, ∀ z : V k, curvDerivNormSq 0 (Gloc k s) z ≤ B k := by
  intro k s hs z
  have hfψ : Tendsto (fun i => f (ψ i)) atTop atTop := (hf.comp hψ).tendsto_atTop
  obtain ⟨i0, hi0⟩ := eventually_atTop.mp
    ((hψ.tendsto_atTop.eventually (eventually_ge_atTop (N k))).and
      (hfψ.eventually (hbound k)))
  let seq : ℕ → SmoothRiemannianMetric ThreeModel (V k) := fun i =>
    localPullMetric (h k (f (ψ (i + i0))) s) (φ k (ψ (i + i0)) (hi0 (i + i0) (by omega)).1)
      (hφ k (ψ (i + i0)) (hi0 (i + i0) (by omega)).1)
  have hconvU : MetricCInfConvergenceOnCompacts seq (Gloc k s) (P.metric.restrictOpen (V k)) := by
    intro K' hK' p η hη
    obtain ⟨j₀, hj₀⟩ := hconv k K' hK' p η hη
    refine ⟨j₀, fun i hi => ?_⟩
    obtain ⟨_, hb⟩ := hj₀ (i + i0) (by omega)
    exact hb s hs
  have hKs : IsCompact ({z} : Set (V k)) := isCompact_singleton
  have hlim := (hconvU _ hKs 2).tendsto_normSq_metricRm04At hKs (mem_singleton _)
  have hterm : ∀ i, normSq0S (seq i) z 4 (metricRm04At (seq i) z) ≤ B k := by
    intro i
    have h1 := (hi0 (i + i0) (by omega)).2 s hs
      (φ k (ψ (i + i0)) (hi0 (i + i0) (by omega)).1 z)
    rw [← curvDerivNormSq_localPullMetric (h k (f (ψ (i + i0))) s)
      (φ k (ψ (i + i0)) (hi0 (i + i0) (by omega)).1)
      (hφ k (ψ (i + i0)) (hi0 (i + i0) (by omega)).1) 0 z,
      curvDerivNormSq_zero_eq_normSq0S_metricRm04At] at h1
    exact h1
  rw [curvDerivNormSq_zero_eq_normSq0S_metricRm04At]
  exact le_of_tendsto hlim (Eventually.of_forall hterm)

end FILL910
