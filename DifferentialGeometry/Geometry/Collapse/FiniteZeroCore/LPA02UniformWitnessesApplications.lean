import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA02UniformWitnesses

/-!
# LPA02 for a scale family (consumer)

`lpa02_eventually_model_balls_at_scale`: for LPA01's standing data and ANY positive scale family
`ρ` that eventually satisfies LPA01's upper bound `ρ_i(p) ≤ 2 r_p(w')` (for instance LC02's
modified scale on LPA04's tail), there is `V ≥ T` such that eventually every point `p` has a scale
`s ∈ [T, V]` and a smooth three-manifold `Ns` with every ball `B(p, ρ' s ρ_i(p))`,
`ρ' ∈ [1/5, 2]`, diffeomorphic to `Ns`, the original buffer on `B(p, 400 s ρ_i(p))`, and `Ns`
homeomorphic to a complete connected nonnegatively curved model. It instantiates
`lpa02_uniform_joint_zero_witnesses` at `r = ρ_i(p)` with fixed LC57 ranges.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **LPA02 at a scale family.** For LPA01's standing data (`10 ≤ K`), `T`, and a positive scale
family `ρ` eventually below `2 r_p(w')`: there is `V ≥ T` such that eventually every point `p` has
`s ∈ [T, V]`, the original buffer `sec ≥ -(1/60)² (s ρ)⁻²` on `B(p, 400 s ρ_i(p))`, and a smooth
manifold `Ns`, homeomorphic to a proper connected model `N`, with `B(p, ρ' s ρ_i(p)) ≃ Ns` for
every `ρ' ∈ [1/5, 2]`. -/
theorem lpa02_eventually_model_balls_at_scale
    {X : ℕ → Type} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
    [∀ i, IsManifold I3 ∞ (X i)] [∀ i, CompactSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric I3 (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {α : ℕ → ℝ} (hα : Tendsto α atTop atTop)
    (hstand : ∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
      curvatureRadius (g i) p) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v)
    (hder : ∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
      ∀ C, 0 < C → C < α i → ∀ k ≤ K,
      ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
        curvatureDerivativeNorm (g i) k y ≤
          A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹)
    {Λ w : ℝ} (hΛ : 0 < Λ) (hw : 0 < w) (hwc : w < 4 * Real.pi / 3) (T : ℝ)
    (ρ : ∀ i, X i → ℝ) (hρ : ∀ i x, 0 < ρ i x)
    (hρw : ∀ᶠ i in atTop, ∀ x : X i,
      ρ i x ≤ 2 * firstVolumeScale (g i) x (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) :
    ∃ V : ℝ, T ≤ V ∧ ∀ᶠ i in atTop, ∀ p : X i, ∃ s ∈ Icc T V,
      (∀ y ∈ Metric.ball p (400 * (s * ρ i p)),
        SectionalBoundedBelowAt (g i) y (-((1 / 60) ^ 2 * (s * ρ i p)⁻¹ ^ 2))) ∧
      ∃ (N : Type) (mN : MetricSpace N), letI := mN
        ProperSpace N ∧ ConnectedSpace N ∧
        ∃ (Ns : Type) (_ : TopologicalSpace Ns) (_ : ChartedSpace E3 Ns)
          (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N),
          ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I3 I3 (X i) Ns ∞,
            Ψ.source = Metric.ball p (ρ' * (s * ρ i p)) ∧ Ψ.target = univ := by
  obtain ⟨V, hTV, _, -, -, hall⟩ := lpa02_uniform_joint_zero_witnesses g hmetric hα hstand K hK
    A hA hder hΛ hw hwc (ε := 1 / 2) (δ' := 1) (e := 1 / 80) (T := T) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨V, hTV, ?_⟩
  filter_upwards [hall, hρw] with i hi hiρ p
  obtain ⟨s, hsI, -, N, mN, _, _, _, _, hprop, hconn, -, -, -, -, _, _, _, -, -, -, Ns, tNs, cNs,
      hNs, hhom, hbuf, -, -, hball⟩ := hi p (ρ i p) (hρ i p) (hiρ p)
  exact ⟨s, hsI, hbuf, N, mN, hprop, hconn, Ns, tNs, cNs, hNs, hhom, hball⟩

end DifferentialGeometry.Geometry.Collapse
