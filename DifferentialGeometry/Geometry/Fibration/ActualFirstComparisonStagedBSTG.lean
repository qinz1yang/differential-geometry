import DifferentialGeometry.Geometry.Fibration.ActualFirstComparisonList
import DifferentialGeometry.Geometry.Collapse.ShortBufferSupplierBSTG

/-!
# TCP01's whole-support count on the staged final family (lane BSTG, consumer of PR13)

Binding consumer of the Δ-stage short-buffer supplier `ShortBufferSupplierBSTG`: lane C14-STG's
`exists_c14d_staged_assignment_STG` produces, for every STG request record, ONE admissible prefix
`P` and, on every standing sequence, late members `LocalChartPacketsC14D` at `P`'s parameters with
`Lmax = c14Lmax Rq P V`. At that prefix the PR13 short buffer (`1200 ≤ Δ`, the finite maximum of
the fixed short windows of TCP01–TCP04, FC22, LFR35–LFR38) and the whole numeric block of the
accepted TCP rows hold (`C14PreFinal.tcp_row_numerics_BSTG`), so the accepted row `tcp01_row`
fires on the produced family itself:

* `exists_c14d_staged_tcp01_count_BSTG`: at every circle centre `x` of every late member, the
  whole closed-support comparison list (circle, slim, edge charts whose closed support meets
  `D_x = B(x, 10ρ(x))`, and the meeting zero list) has at most `fc07ActiveBound` entries, and the
  meeting zero list has at most one entry (kept as its own clause, review 57 §6.3).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The model metrics of `LocalChartPacketsC14D`, as a named local instance. -/
local instance instMetricNC14D_BSTG {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (L : LocalChartPacketsC14D X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
      e T V vs ζ Λz) (a : X) : MetricSpace (L.N a) :=
  L.instMetricN a

/-- The model charts of `LocalChartPacketsC14D`, as a named local instance. -/
local instance instChartedNC14D_BSTG {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (L : LocalChartPacketsC14D X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
      e T V vs ζ Λz) (a : X) : ChartedSpace E3 (L.N a) :=
  L.instChartedN a

/-- The cone metrics of `LocalChartPacketsC14D`, as a named local instance. -/
local instance instMetricCC14D_BSTG {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
    (L : LocalChartPacketsC14D X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr
      e T V vs ζ Λz) (a : X) : MetricSpace (L.C a) :=
  L.instMetricC a

/-- **TCP01's whole-support count on the staged final family** (consumer of the PR13 short
buffer): for every STG request record, the staged assignment's ONE prefix meets the short-buffer
request, and on every standing sequence every late member `L : LocalChartPacketsC14D` at the
prefix's parameters satisfies, at every circle centre `x`, TCP01's count `≤ fc07ActiveBound` of
the circle, slim, edge and zero charts whose closed support meets `B(x, 10ρ(x))`, and its
"at most one meeting zero" clause. -/
theorem exists_c14d_staged_tcp01_count_BSTG (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) (t : C14Tol)
    (Rq : C14StagedRequestsSTG) :
    ∃ P : C14PreFinal, P.toC14Tol = t ∧ Rq.toC14.Meets P ∧
      c14ShortBufferRq_BSTG.Δ P.toC14PreExcl ≤ P.Δ ∧
      ∀ (X : ℕ → Type) [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (X i)] [∀ i, CompactSpace (X i)]
        (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (X i))
        (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
        (α : ℕ → ℝ), Tendsto α atTop atTop →
        (∀ i (p : X i), ENNReal.ofReal (α i * firstVolumeScale (g i) p (α i)⁻¹) ≤
          curvatureRadius (g i) p) →
        (∀ i (p : X i) v, 0 < v → v < 4 * Real.pi / 3 → (α i)⁻¹ ≤ v →
          ∀ C, 0 < C → C < α i → ∀ k ≤ K,
          ∀ y ∈ riemannianBallOf (g i) p (C * firstVolumeScale (g i) p v),
            curvatureDerivativeNorm (g i) k y ≤
              A C v * (firstVolumeScale (g i) p v ^ (k + 2))⁻¹) →
        (∀ i, ManifoldOrientation (𝓡 3) (X i) 3) →
      ∃ V : ℝ, P.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < P.δ' ∧
        ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        ∃ L : LocalChartPacketsC14D (X i) (g i) (hmetric i) ρ hρpos P.Λ P.β P.Δ P.σs K
          P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc (c14Lmax Rq.toC14 P V) P.τ P.γ δ P.εr
          P.e P.T V P.vs P.ζ P.Λz,
        ∀ x ∈ L.circle.centres,
          (({j | j ∈ L.circle.centres ∧
                (tsupport (L.circle.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard : ℝ) +
              {j | j ∈ L.slim.centres ∧
                (tsupport (L.slim.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard +
              {j | j ∈ L.edge.centres ∧
                (tsupport (L.edge.cutoff j) ∩ ball x (10 * ρ x)).Nonempty}.ncard +
              (zeroMeetingList L.zero x 10).ncard ≤ fc07ActiveBound) ∧
          ∀ k ∈ zeroMeetingList L.zero x 10, ∀ k' ∈ zeroMeetingList L.zero x 10, k = k' := by
  obtain ⟨P, hPt, hM, -, h⟩ := exists_c14d_staged_assignment_STG K hK A hA t Rq
  refine ⟨P, hPt, hM, P.meets_shortBufferΔ_BSTG, ?_⟩
  intro X _ _ _ _ g hmetric α hα hstand hder hor
  obtain ⟨V, hTV, δ, hδ, hδδ', -, -, hev⟩ := h X g hmetric α hα hstand hder hor
  obtain ⟨hΛ, h1200, hμ, hτ, hLΛ, hLmax, he, hT⟩ := P.tcp_row_numerics_BSTG Rq.toC14 hTV
  refine ⟨V, hTV, δ, hδ, hδδ', ?_⟩
  filter_upwards [hev] with i hi
  obtain ⟨ρ, hρ, -, ⟨L⟩⟩ := hi
  refine ⟨ρ, hρ, L, fun x hx => ?_⟩
  have hrow := tcp01_row L.toLocalChartPackets hΛ (by linarith) hμ hτ hLΛ hLmax he hT
    P.γ_pos.le hx
  exact ⟨hrow.1, hrow.2.2.2.2.1⟩

end DifferentialGeometry.Geometry.Collapse
