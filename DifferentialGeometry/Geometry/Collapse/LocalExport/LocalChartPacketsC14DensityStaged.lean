import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14Staged
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14DensityProducer

/-!
# The staged assignment of the final family with LFR44 item 2 (`LocalChartPacketsC14D`)

Lane C14-FAM3. `eventually_nonempty_localChartPacketsC14D` has the parameter prefix of
`eventually_nonempty_localChartPacketsC14` verbatim (LFR44's thresholds are folded into the existing
outputs `w₀` and `b₀`), so the staged requests contract `C14StagedRequests` (lanes C14-FAM2 /
C14-FAM2b) applies unchanged: `exists_c14d_staged_assignment` is `exists_c14_staged_assignment`
with the extended family in the conclusion. Every row stated on `C14StagedRequests` / `C14PreFinal`
keeps its request; rows on `LocalChartPacketsC14` apply through `toLocalChartPacketsC14`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology NNReal
open DifferentialGeometry.Topology.Ehresmann
open DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open GC.MetricGeometry DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-- **ONE staged admissible assignment for the family with LFR44 item 2** (review 50, A1–A3; lead decision T50-2): for the external
tolerances `t` and every staged requests record `Rq` there is ONE admissible prefix `P` (every
parameter of `eventually_nonempty_localChartPacketsC14` together with the producer's threshold
outputs, each stage below the request evaluated at the prefix BEFORE it) such that, for every
standing sequence, with the joint zero output `V ≥ T`, `δ < δ'` and
`Lmax := 1 + max(1, max(400V, Rq.Lmax P V))`, every late member carries the final family
`LocalChartPacketsC14D` with exactly these parameters (the proof of
`exists_c14_staged_assignment` verbatim, on `eventually_nonempty_localChartPacketsC14D`). -/
theorem exists_c14d_staged_assignment (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) (t : C14Tol)
    (Rq : C14StagedRequests) :
    ∃ P : C14PreFinal, P.toC14Tol = t ∧ Rq.Meets P ∧
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
        400 * V < c14Lmax Rq P V ∧ Rq.Lmax P V ≤ c14Lmax Rq P V ∧
        ∀ᶠ i in atTop, ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p P.w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (P.w / (2 * (1 + 2 * P.Λ⁻¹) ^ 3))) ∧
        Nonempty (LocalChartPacketsC14D (X i) (g i) (hmetric i) ρ hρpos P.Λ P.β P.Δ P.σs K
          P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc (c14Lmax Rq P V) P.τ P.γ δ P.εr
          P.e P.T V P.vs P.ζ P.Λz) := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartPacketsC14D K hK A hA
  obtain ⟨p1, rfl, rfl, h1γ, h⟩ := c14_stage_circ_FAM2b t ha₂ (Rq.γ_pos t) h
  obtain ⟨p2, rfl, h2βc, h2γc, h⟩ := c14_stage_collar_FAM2b p1 (Rq.βc_pos p1) (Rq.γc_pos p1) h
  obtain ⟨p3, rfl, h3β₂, h⟩ := c14_stage_excl_FAM2b p2 (Rq.β₂_pos p2) h
  obtain ⟨p4, rfl, h4Δ, h⟩ := c14_stage_scale_FAM2b p3 (Rq.Δ p3) h
  obtain ⟨p5, rfl, h5σc, h5ε, h5μ, h5τ, h5s, h5b', h5s', h⟩ := c14_stage_edge_FAM2b p4
    (Rq.σc_pos p4) (Rq.ε_pos p4) (Rq.μ_pos p4) (Rq.τ_pos p4) (Rq.s_pos p4) (Rq.b'_pos p4)
    (Rq.s'_pos p4) h
  obtain ⟨p6, rfl, h6Λ, h⟩ := c14_stage_lip_FAM2b p5 (Rq.Λ_pos p5) h
  obtain ⟨p7, rfl, h7w, h⟩ := c14_stage_vol_FAM2b p6 (Rq.w_pos p6) h
  obtain ⟨p8, rfl, h8b, h⟩ := c14_stage_split_FAM2b p7 (Rq.b_pos p7) h
  obtain ⟨p9, rfl, h9σs, h9vs, h⟩ := c14_stage_slim_FAM2b p8 (Rq.σs_pos p8) (Rq.vs_pos p8) h
  obtain ⟨p10, rfl, h10ζ, h10β, h⟩ := c14_stage_beta_FAM2b p9 (Rq.ζ_pos p9) (Rq.β₁_pos p9) h
  obtain ⟨p11, rfl, h11cap, h⟩ := c14_stage_zero_FAM2b p10 (Rq.cap_pos p10) h
  obtain ⟨P, rfl, h12T, h12e, h⟩ := c14_stage_final_FAM2b p11 (Rq.T p11) (Rq.e_pos p11) h
  refine ⟨P, rfl, ⟨h1γ, h2γc, h2βc, h3β₂, h4Δ, h5σc, h5ε, h5μ, h5τ, h5s, h5b', h5s', h6Λ, h7w,
    h8b, h9σs, h9vs, h10ζ, h10β, h11cap, h12T, h12e⟩, ?_⟩
  intro X _ _ _ _ g hmetric α hα hstand hder hor
  obtain ⟨V, hTV, δ, hδ, hδδ', hV⟩ := h X g hmetric α hα hstand hder hor
  exact ⟨V, hTV, δ, hδ, hδδ', c14Lmax_gt Rq P V, c14Lmax_ge Rq P V,
    hV _ (c14Lmax_pos Rq P V)⟩

end DifferentialGeometry.Geometry.Collapse
