import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14StagedSTG
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypesProducer

/-!
# The staged assignment of the complete closed family `LocalChartPacketsC14Z` (lane C14-FAM-Z)

`eventually_nonempty_localChartPacketsC14Z_FAMZ` has the parameter prefix of
`eventually_nonempty_localChartPacketsC14D` verbatim (only the tail is stronger), so lane C14-STG's
staged contract (`C14StagedRequestsSTG`, the stage lemmas `c14_stage_*` with abstract
continuations, `3βc ≤ β₂`) applies unchanged: `exists_c14z_staged_assignment_FAMZ` is
`exists_c14d_staged_assignment_STG` with the complete family, LPA02's joint witness and the
selection in the conclusion (generated from `LocalChartPacketsC14StagedSTG.lean` by
`build-logs/scratch/C14-FAM-Z/gen_st.py`). Every row stated on `C14StagedRequestsSTG` /
`C14PreFinal` keeps its request.
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

/-- **ONE staged admissible assignment for the complete closed family** (lane C14-FAM-Z): the
statement of `exists_c14d_staged_assignment_STG` (the same prefix `P`, `P.toC14Tol = t`,
`Rq.toC14.Meets P`, `3βc ≤ β 2`, the same `V`, `δ`, `Lmax := c14Lmax Rq.toC14 P V`; the orientation
hypothesis is named `hor`) whose late members carry, on the SAME tail, LPA02's joint witness and the
complete family `LocalChartPacketsC14Z … (hor i)` (with `zero_sublevel_types`) with its zero balls
selected from that witness. The proof of `exists_c14d_staged_assignment_STG` verbatim, on
`eventually_nonempty_localChartPacketsC14Z_FAMZ` (the stage lemmas take an abstract
continuation). -/
theorem exists_c14z_staged_assignment_FAMZ (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ → ℝ)
    (hA : ∀ C v, 0 < C → 0 < v → v < 4 * Real.pi / 3 → 0 < A C v) (t : C14Tol)
    (Rq : C14StagedRequestsSTG) :
    ∃ P : C14PreFinal, P.toC14Tol = t ∧ Rq.toC14.Meets P ∧ 3 * P.βc ≤ P.β 2 ∧
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
      ∀ hor : ∀ i, ManifoldOrientation (𝓡 3) (X i) 3,
      ∃ V : ℝ, P.T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < P.δ' ∧
        400 * V < c14Lmax Rq.toC14 P V ∧ Rq.Lmax P V ≤ c14Lmax Rq.toC14 P V ∧
        ∀ᶠ i in atTop, Lpa02WitnessV2 (g i) K P.Λ P.w P.εr P.e P.T V δ ∧
        ∃ ρ : X i → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
        (∀ p, firstVolumeScale (g i) p P.w / 2 < ρ p ∧
          ρ p < 2 * firstVolumeScale (g i) p (P.w / (2 * (1 + 2 * P.Λ⁻¹) ^ 3))) ∧
        ∃ F : LocalChartPacketsC14Z (X i) (g i) (hmetric i) ρ hρpos P.Λ P.β P.Δ P.σs K
          P.σc P.μ P.b P.s P.b' P.s' P.ε P.γc P.βc (c14Lmax Rq.toC14 P V) P.τ P.γ δ P.εr
          P.e P.T V P.vs P.ζ P.Λz (hor i),
          ∀ c (hc : c ∈ F.zero.centres), ∃ t ∈ Icc P.T V, ∃ ht : 0 < t,
            (F.zero.zero c hc).radius = t * ρ c ∧
              Lpa02WitnessAtV2 (g i) K P.εr P.e δ c (ρ c) t (hρpos c) ht := by
  obtain ⟨a₂, ha₂, h⟩ := eventually_nonempty_localChartPacketsC14Z_FAMZ K hK A hA
  obtain ⟨p1, rfl, rfl, h1γ, h⟩ := c14_stage_circ_FAM2b t ha₂ (Rq.γ_pos t) h
  obtain ⟨p2, rfl, h2βc, h2γc, h⟩ := c14_stage_collar_STG p1
    (fun g => min (Rq.βc g.toC14PreCirc) (c14β₂Value_STG Rq g / 3))
    (fun g => lt_min (Rq.βc_pos _) (div_pos (c14β₂Value_pos_STG Rq g) zero_lt_three))
    (Rq.γc_pos p1) h
  have h2 : p2.βc ≤ min p2.β₀ (min (Rq.β₂ p2.toGc_STG) (min (1 / 10000000) (p2.γT / 20))) / 3 :=
    h2βc.trans (min_le_right _ _)
  obtain ⟨p3, rfl, h3β₂, h3v, h⟩ := c14_stage_excl_STG p2 (Rq.β₂_pos p2.toGc_STG) h
  have h3βc : 3 * p3.βc ≤ p3.β₂ := by
    rw [h3v]
    linarith
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
  refine ⟨P, rfl, ⟨h1γ, h2γc, h2βc.trans (min_le_left _ _), h3β₂, h4Δ, h5σc, h5ε, h5μ, h5τ, h5s,
    h5b', h5s', h6Λ, h7w, h8b, h9σs, h9vs, h10ζ, h10β, h11cap, h12T, h12e⟩,
    by rw [P.β_two]; exact h3βc, ?_⟩
  intro X _ _ _ _ g hmetric α hα hstand hder hor
  obtain ⟨V, hTV, δ, hδ, hδδ', hV⟩ := h X g hmetric α hα hstand hder hor
  exact ⟨V, hTV, δ, hδ, hδδ', c14Lmax_gt Rq.toC14 P V, c14Lmax_ge Rq.toC14 P V,
    hV _ (c14Lmax_pos Rq.toC14 P V)⟩

end DifferentialGeometry.Geometry.Collapse
