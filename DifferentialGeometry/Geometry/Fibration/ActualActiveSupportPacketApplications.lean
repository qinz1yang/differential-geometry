import DifferentialGeometry.Geometry.Fibration.ActualActiveSupportPacket

/-!
# Consumers of FC07's input packet

* `fc07_pointwise_active_le`: at every point the numbers of NONZERO circle, slim, edge and zero
  cutoffs of `P` (the blocks of `cgpGlobalMap P.toLocalChartFamily P.zero`) add up to at most
  `fc07ActiveBound` (the pointwise multiplicity that CGP02's derivative constant uses).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNB_C14KA
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNB_C14KA
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCB_C14KA
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- At every point at most `fc07ActiveBound` circle, slim, edge and zero cutoffs of `P` are
nonzero. -/
theorem fc07_pointwise_active_le
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (x : X) :
    ({j | j ∈ P.circle.centres ∧ P.circle.cutoff j x ≠ 0}.ncard : ℝ) +
      {j | j ∈ P.slim.centres ∧ P.slim.cutoff j x ≠ 0}.ncard +
      {j | j ∈ P.edge.centres ∧ P.edge.cutoff j x ≠ 0}.ncard +
      {k | ∃ hk : k ∈ P.zero.centres,
        Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero k hk).radial x) ≠ 0}.ncard ≤
      fc07ActiveBound := by
  have hcount := (fc07_input_packet P hΛ hΔ hμ hτ hLΛ hLmax he hT x).1
  have hx : x ∈ ball x (10 * ρ x) := mem_ball_self (mul_pos (by norm_num) (hρ x))
  have hC : {j | j ∈ P.circle.centres ∧ P.circle.cutoff j x ≠ 0}.ncard ≤
      {j | j ∈ P.circle.centres ∧
        (tsupport (P.circle.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard :=
    Set.ncard_le_ncard (fun j hj => ⟨hj.1, x, subset_tsupport _ hj.2, hx⟩)
      (P.circle.finite_centres.subset fun _ hj => hj.1)
  have hS : {j | j ∈ P.slim.centres ∧ P.slim.cutoff j x ≠ 0}.ncard ≤
      {j | j ∈ P.slim.centres ∧
        (tsupport (P.slim.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard :=
    Set.ncard_le_ncard (fun j hj => ⟨hj.1, x, subset_tsupport _ hj.2, hx⟩)
      (P.slim.finite_centres.subset fun _ hj => hj.1)
  have hE : {j | j ∈ P.edge.centres ∧ P.edge.cutoff j x ≠ 0}.ncard ≤
      {j | j ∈ P.edge.centres ∧
        (tsupport (P.edge.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard :=
    Set.ncard_le_ncard (fun j hj => ⟨hj.1, x, subset_tsupport _ hj.2, hx⟩)
      (P.edge.finite_centres.subset fun _ hj => hj.1)
  have hZ : {k | ∃ hk : k ∈ P.zero.centres,
        Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero k hk).radial x) ≠ 0}.ncard ≤
      (zeroMeetingList P.zero x 10).ncard := by
    refine Set.ncard_le_ncard ?_ (P.zero.finite_centres.subset fun _ hk => hk.choose)
    rintro k ⟨hk, hne⟩
    exact ⟨hk, x, subset_tsupport _ hne, hx⟩
  have hC' : ({j | j ∈ P.circle.centres ∧ P.circle.cutoff j x ≠ 0}.ncard : ℝ) ≤
      {j | j ∈ P.circle.centres ∧
        (tsupport (P.circle.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard := by
    exact_mod_cast hC
  have hS' : ({j | j ∈ P.slim.centres ∧ P.slim.cutoff j x ≠ 0}.ncard : ℝ) ≤
      {j | j ∈ P.slim.centres ∧
        (tsupport (P.slim.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard := by
    exact_mod_cast hS
  have hE' : ({j | j ∈ P.edge.centres ∧ P.edge.cutoff j x ≠ 0}.ncard : ℝ) ≤
      {j | j ∈ P.edge.centres ∧
        (tsupport (P.edge.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard := by
    exact_mod_cast hE
  have hZ' : ({k | ∃ hk : k ∈ P.zero.centres,
        Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero k hk).radial x) ≠ 0}.ncard :
          ℝ) ≤ (zeroMeetingList P.zero x 10).ncard := by
    exact_mod_cast hZ
  linarith

end DifferentialGeometry.Geometry.Collapse
