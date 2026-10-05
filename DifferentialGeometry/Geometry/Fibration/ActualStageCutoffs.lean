import DifferentialGeometry.Geometry.Fibration.ActualSegmentLocalization
import DifferentialGeometry.Analysis.Calculus.Cutoff.BufferedEdgeCutoff
import DifferentialGeometry.Analysis.Calculus.Cutoff.UniformAxisCutoff

/-!
# GAF02, stages two and three: CFS23's edge cutoff and CFS22's slim cutoff on the actual `𝓔⁰`

Blueprint `master207B.tex`, GAF02 (`thm:fibration-actual-final-submersions`, B:5826–5834):
"CFS31 first constructs the source cutoff, then the edge cutoff and then the slim cutoff. At each
step its CLOSED support localizes the original point to the corresponding original core." Stage one
is `gaf02_stageOne_sourceCutoff` (C14-GAF G2). This module binds CFS23 (`cfs23_row`) and CFS22
(`cfs22_row`) to CGP01's actual `𝓔⁰ = cgpGlobalMap L Z` on `LocalChartPackets`:

* edge family `𝓘₂ = I_e`: blocks `u_j = (·)_j.fst`, `v_j = (·)_j.snd` of the edge tags
  (`gafEdgeVector`, `gafEdgeMarker`), `R_j = ρ(c_j)`, `η_j = planeAxis ∘ (edge coordinate)`,
  `U_j = B(c_j, 100Δρ(c_j))`; scale `x_ρ = (·)_ρ.snd` (`gafScaleMarker`), the `E'` block
  `x₁ = (·)_{E'}.fst`, `x₂ = (·)_{E'}.snd` (`gafHeightVector`, `gafHeightMarker`), height
  `t = F/ρ` (`cgpHeight`) and CGP01's `h = cgpEdgeH`;
* slim family `𝓘₃ = I_s`: slim blocks (`gafSlimVector`, `gafSlimMarker`), `ℓ = 10⁵Δ`,
  `η_j = planeAxis ∘ (slim coordinate)`, `U_j = B(c_j, 10⁶Δρ(c_j))`;
* profile `χ_E = lc87EdgeTransition`, `P₀ = cgpProfileBound`, `N = gafMultiplicity`.

`gaf02_stageTwo_cutoff`, `gaf02_stageThree_cutoff`: for ANY map `f` (the preceding stage output)
with CFS31's boxed contract — `|f − 𝓔⁰| ≤ (4κ/5)ρ` and `ζ_j = 0 ⇒ |v_j(f)| ≤ R_j/32` for the
stage's family — the cutoff is smooth (edge: on `{x_ρ > 0}`), `[0,1]`-valued, exactly one on the
threshold-`6` plateau, its closed support localizes the ORIGINAL point to the threshold-`7` core,
and `‖Dψ‖ ≤ b_cut/ρ` along the whole segment from `𝓔⁰` to `f`. Hypotheses: the producer's
parameter ranges only.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

section Blocks

variable (L : LocalChartFamily X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc)
  (Z : ZeroModelFamily 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V)

/-- The stage-two vector blocks `u_j` (edge centres) of `𝓔⁰`. -/
def gafEdgeVector (j : L.edge.finite_centres.toFinset) :
    BlockSpace (fun _ : CGPTag L Z => ℝ²) →L[ℝ] ℝ² :=
  blockVectorCLM (V := fun _ : CGPTag L Z => ℝ²) (.inr (.inr (.inl j)))

/-- The stage-two markers `v_j` (edge centres) of `𝓔⁰`. -/
def gafEdgeMarker (j : L.edge.finite_centres.toFinset) :
    BlockSpace (fun _ : CGPTag L Z => ℝ²) →L[ℝ] ℝ :=
  blockMarkerCLM (V := fun _ : CGPTag L Z => ℝ²) (.inr (.inr (.inl j)))

/-- The stage-three vector blocks `u_j` (slim centres) of `𝓔⁰`. -/
def gafSlimVector (j : L.slim.finite_centres.toFinset) :
    BlockSpace (fun _ : CGPTag L Z => ℝ²) →L[ℝ] ℝ² :=
  blockVectorCLM (V := fun _ : CGPTag L Z => ℝ²) (.inr (.inl j))

/-- The stage-three markers `v_j` (slim centres) of `𝓔⁰`. -/
def gafSlimMarker (j : L.slim.finite_centres.toFinset) :
    BlockSpace (fun _ : CGPTag L Z => ℝ²) →L[ℝ] ℝ :=
  blockMarkerCLM (V := fun _ : CGPTag L Z => ℝ²) (.inr (.inl j))

/-- The scale coordinate `x_ρ` of `𝓔⁰`. -/
def gafScaleMarker : BlockSpace (fun _ : CGPTag L Z => ℝ²) →L[ℝ] ℝ :=
  blockMarkerCLM (V := fun _ : CGPTag L Z => ℝ²) (cgpScaleTag L Z)

/-- The vector of the `E'` block (`ρ t z₀` on the axis). -/
def gafHeightVector : BlockSpace (fun _ : CGPTag L Z => ℝ²) →L[ℝ] ℝ² :=
  blockVectorCLM (V := fun _ : CGPTag L Z => ℝ²) (cgpEdgeTag L Z)

/-- The marker of the `E'` block (`ρ z₀`). -/
def gafHeightMarker : BlockSpace (fun _ : CGPTag L Z => ℝ²) →L[ℝ] ℝ :=
  blockMarkerCLM (V := fun _ : CGPTag L Z => ℝ²) (cgpEdgeTag L Z)

/-- **GAF02's stage-two cutoff**: CFS23's buffered edge cutoff on the actual edge family. -/
def gafStageTwoCutoff : BlockSpace (fun _ : CGPTag L Z => ℝ²) → ℝ :=
  cfsBufferedEdgeCutoff lc87EdgeTransition Δ (fun j : L.edge.finite_centres.toFinset => ρ j.1)
    (gafEdgeVector L Z) (gafEdgeMarker L Z) (gafScaleMarker L Z) (gafHeightVector L Z)
    (gafHeightMarker L Z)

/-- **GAF02's stage-three cutoff**: CFS22's uniform one-axis cutoff on the actual slim family. -/
def gafStageThreeCutoff : BlockSpace (fun _ : CGPTag L Z => ℝ²) → ℝ :=
  cfsUniformAxisCutoff lc87EdgeTransition (10 ^ 5 * Δ)
    (fun j : L.slim.finite_centres.toFinset => ρ j.1) (gafSlimVector L Z) (gafSlimMarker L Z)

/-- The edge blocks of `𝓔⁰`: `(u_j, v_j)(𝓔⁰ p) = (ρ(c_j) ζ_j(p) η_j(p), ρ(c_j) ζ_j(p))`. -/
theorem gafEdge_block_GAF2 (j : L.edge.finite_centres.toFinset) (p : X) :
    gafEdgeVector L Z j (cgpGlobalMap L Z p) =
        (ρ j.1 * L.edge.cutoff j.1 p) • planeAxis (L.edge.coord j.1 p) ∧
      gafEdgeMarker L Z j (cgpGlobalMap L Z p) = ρ j.1 * L.edge.cutoff j.1 p :=
  cgpGlobalMap_edgeBlock L Z j p

/-- The slim blocks of `𝓔⁰`. -/
theorem gafSlim_block_GAF2 (j : L.slim.finite_centres.toFinset) (p : X) :
    gafSlimVector L Z j (cgpGlobalMap L Z p) =
        (ρ j.1 * L.slim.cutoff j.1 p) •
          planeAxis ((L.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p) ∧
      gafSlimMarker L Z j (cgpGlobalMap L Z p) = ρ j.1 * L.slim.cutoff j.1 p :=
  ⟨rfl, rfl⟩

/-- The scale coordinate of `𝓔⁰` is `ρ`. -/
theorem gafScaleMarker_globalMap_GAF2 (p : X) :
    gafScaleMarker L Z (cgpGlobalMap L Z p) = ρ p :=
  cgpGlobalMap_scale L Z p

/-- CFS23's joint edge block identity for the actual `E'` block. -/
theorem gafHeight_block_GAF2 (p : X) :
    ‖gafHeightVector L Z (cgpGlobalMap L Z p)‖ = ρ p * cgpHeight L p *
        (cgpEdgeH (cgpHeight L p / Δ) * cfsRamp lc87EdgeTransition (1 / 2) 1
          (∑ j : L.edge.finite_centres.toFinset, L.edge.cutoff j.1 p)) ∧
      gafHeightMarker L Z (cgpGlobalMap L Z p) = ρ p *
        (cgpEdgeH (cgpHeight L p / Δ) * cfsRamp lc87EdgeTransition (1 / 2) 1
          (∑ j : L.edge.finite_centres.toFinset, L.edge.cutoff j.1 p)) :=
  ⟨norm_cgpGlobalMap_edgeCoord L Z p, cgpGlobalMap_edgeMarker L Z p⟩

end Blocks

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricNST_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedNST_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricCST_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- The number of edge cutoffs positive at a point is at most `N = gafMultiplicity`. -/
theorem gafEdge_count_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (p : X) :
    (Finset.univ.filter fun j : P.edge.finite_centres.toFinset =>
      0 < P.edge.cutoff j.1 p).card ≤ gafMultiplicity := by
  classical
  have h := cgp_active_edge_card_le_fc07 P hΛ hΔ hμ hτ hLΛ hLmax he hT p
  have hsub : (Finset.univ.filter fun j : P.edge.finite_centres.toFinset =>
      0 < P.edge.cutoff j.1 p) ⊆ (Finset.univ.filter fun j : P.edge.finite_centres.toFinset =>
      p ∈ tsupport (P.edge.cutoff j)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact subset_tsupport _ hj.ne'
  have hcard := Finset.card_le_card hsub
  refine Nat.le_floor ?_
  calc ((Finset.univ.filter fun j : P.edge.finite_centres.toFinset =>
        0 < P.edge.cutoff j.1 p).card : ℝ) ≤
      ((Finset.univ.filter fun j : P.edge.finite_centres.toFinset =>
        p ∈ tsupport (P.edge.cutoff j)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ fc07ActiveBound := h

/-- The number of slim cutoffs positive at a point is at most `N = gafMultiplicity`. -/
theorem gafSlim_count_GAF2
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (p : X) :
    (Finset.univ.filter fun j : P.slim.finite_centres.toFinset =>
      0 < P.slim.cutoff j.1 p).card ≤ gafMultiplicity := by
  have hN := cgp_active_tags_ncard_le_fc07 P hΛ hΔ hμ hτ hLΛ hLmax he hT p
  set A : Set (CGPTag P.toLocalChartFamily P.zero) :=
    {i | i ≠ cgpScaleTag P.toLocalChartFamily P.zero ∧
      i ≠ cgpEdgeTag P.toLocalChartFamily P.zero ∧
      p ∈ tsupport (cgpCutoff P.toLocalChartFamily P.zero i)} with hA
  let S := Finset.univ.filter fun j : P.slim.finite_centres.toFinset => 0 < P.slim.cutoff j.1 p
  let emb : P.slim.finite_centres.toFinset ↪ CGPTag P.toLocalChartFamily P.zero :=
    ⟨fun j => .inr (.inl j), fun a b h => by
      simp only [Sum.inr.injEq, Sum.inl.injEq] at h
      exact h⟩
  have hsub : ((S.map emb : Finset (CGPTag P.toLocalChartFamily P.zero)) : Set _) ⊆ A := by
    intro i hi
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at hi
    obtain ⟨j, hjS, rfl⟩ := hi
    have hpos : 0 < P.slim.cutoff j.1 p := (Finset.mem_filter.mp hjS).2
    refine ⟨fun h => ?_, fun h => ?_, subset_tsupport _ ?_⟩
    · change (Sum.inr (Sum.inl j) : CGPTag P.toLocalChartFamily P.zero) = _ at h
      simp at h
    · change (Sum.inr (Sum.inl j) : CGPTag P.toLocalChartFamily P.zero) = _ at h
      simp at h
    · exact hpos.ne'
  have hcard : (S.card : ℝ) ≤ A.ncard := by
    have := Set.ncard_le_ncard hsub (Set.toFinite A)
    rw [Set.ncard_coe_finset, Finset.card_map] at this
    exact_mod_cast this
  exact Nat.le_floor (hcard.trans hN)

/-- **GAF02, stage two** (CFS23's edge cutoff on the actual `𝓔⁰`): for any `f` with CFS31's boxed
contract for the edge family, the cutoff is smooth on `{x_ρ > 0}`, `[0,1]`-valued, one on the
threshold-`6Δ` plateau, its closed support localizes the original point to the threshold-`7Δ` edge
core, and `‖Dψ₂‖ ≤ b_cut/ρ` along the segment from `𝓔⁰` to `f`. -/
theorem gaf02_stageTwo_cutoff
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hpert : ∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤
      4 * gafKappa / 5 * ρ p)
    (hZM : ∀ (j : P.edge.finite_centres.toFinset) p, P.edge.cutoff j.1 p = 0 →
      |gafEdgeMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) :
    ContDiffOn ℝ ∞ (gafStageTwoCutoff P.toLocalChartFamily P.zero)
        {z | 0 < gafScaleMarker P.toLocalChartFamily P.zero z} ∧
      (∀ z, gafStageTwoCutoff P.toLocalChartFamily P.zero z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
          |P.edge.coord j.1 p| < 6 * Δ ∧ cgpHeight P.toLocalChartFamily p < 6 * Δ) →
        gafStageTwoCutoff P.toLocalChartFamily P.zero (f p) = 1) ∧
      (∀ p, f p ∈ tsupport (gafStageTwoCutoff P.toLocalChartFamily P.zero) →
        ∃ j : P.edge.finite_centres.toFinset, p ∈ ball j.1 (100 * Δ * ρ j.1) ∧
          |P.edge.coord j.1 p| < 7 * Δ ∧ cgpHeight P.toLocalChartFamily p < 7 * Δ) ∧
      (∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
        0 < gafScaleMarker P.toLocalChartFamily P.zero
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • f p) ∧
        ‖fderiv ℝ (gafStageTwoCutoff P.toLocalChartFamily P.zero)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • f p)‖ ≤
            gafCutoffConstant / ρ p) := by
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hζU : ∀ (j : P.edge.finite_centres.toFinset) p, p ∉ ball j.1 (100 * Δ * ρ j.1) →
      P.edge.cutoff j.1 p = 0 := by
    intro j p hp
    by_contra h
    exact hp (cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inr (.inr j)) p h)
  have hcomp : ∀ (j : P.edge.finite_centres.toFinset) p, 0 < P.edge.cutoff j.1 p →
      3 / 4 * ρ j.1 ≤ ρ p ∧ ρ p ≤ 5 / 4 * ρ j.1 ∧
        ‖planeAxis (P.edge.coord j.1 p)‖ ≤ 9 * Δ := by
    intro j p hpos
    obtain ⟨h1, h2⟩ := cgpMarkerCutoff_scale_GAF2 P.toLocalChartFamily P.zero hΔ hσs hσs1 hΛ
      hsmall (.inr (.inr j)) p hpos
    obtain ⟨-, -, h3, -⟩ := P.edge.mem_of_cutoff_ne_zero hΔ0 hpos.ne'
    change 3 * ρ j.1 / 4 ≤ ρ p at h1
    change ρ p ≤ 5 * ρ j.1 / 4 at h2
    refine ⟨by linarith, by linarith, ?_⟩
    rw [norm_planeAxis]
    exact h3.le
  have hedge : ∀ (j : P.edge.finite_centres.toFinset) p, p ∈ ball j.1 (100 * Δ * ρ j.1) →
      ‖planeAxis (P.edge.coord j.1 p)‖ < 8 * Δ →
      P.edge.cutoff j.1 p = 1 - cfsRamp lc87EdgeTransition 8 9 (cgpHeight P.toLocalChartFamily p / Δ) := by
    intro j p hp hη
    rw [norm_planeAxis] at hη
    exact cgp01_edge_identity P.toLocalChartFamily ((Set.Finite.mem_toFinset _).mp j.2) hp hη hΔ0
  have hkappa : gafKappa = 1 / (1000 * ((gafMultiplicity : ℝ) + 1) * cgpProfileBound ^ 2) := rfl
  have hC : gafCutoffConstant = 10 ^ 4 * ((gafMultiplicity : ℝ) + 1) ^ 2 * cgpProfileBound ^ 4 :=
    rfl
  rw [hkappa] at hpert
  obtain ⟨h1, h2, h3, h4, h5⟩ := cfs23_row (fun j : P.edge.finite_centres.toFinset => ρ j.1)
    (gafEdgeVector P.toLocalChartFamily P.zero) (gafEdgeMarker P.toLocalChartFamily P.zero)
    (gafScaleMarker P.toLocalChartFamily P.zero) (gafHeightVector P.toLocalChartFamily P.zero)
    (gafHeightMarker P.toLocalChartFamily P.zero) lc87EdgeTransition_contDiff
    (fun _ ht => lc87EdgeTransition_eq_zero ht) (fun _ ht => lc87EdgeTransition_eq_one ht)
    lc87EdgeTransition_mem_Icc lc87EdgeTransition_monotone cgpProfileBound_spec.1
    abs_deriv_lc87EdgeTransition_le_cgp gafMultiplicity (fun _ => norm_blockVectorCLM_le _)
    (fun _ => norm_blockMarkerCLM_le _) (norm_blockMarkerCLM_le _) (norm_blockVectorCLM_le _)
    (norm_blockMarkerCLM_le _) hΔ (fun _ => hρ _) ρ hρ
    (fun j => ball j.1 (100 * Δ * ρ j.1)) (fun j p => planeAxis (P.edge.coord j.1 p))
    (fun j p => P.edge.cutoff j.1 p) (fun j p => cgpEdgeCutoff_mem_Icc P.toLocalChartFamily hΔ0 j.1 p)
    (cgpGlobalMap P.toLocalChartFamily P.zero) f hζU
    (gafEdge_block_GAF2 P.toLocalChartFamily P.zero)
    (gafEdge_count_GAF2 P hΛ hΔ hμ hτ hLΛ hLmax he hT) hcomp hpert hZM
    (cgpHeight P.toLocalChartFamily) cgpEdgeH cgpEdgeH_mem_Icc (fun _ hs => cgpEdgeH_eq_of_le hs)
    (gafScaleMarker_globalMap_GAF2 P.toLocalChartFamily P.zero)
    (fun p _ => gafHeight_block_GAF2 P.toLocalChartFamily P.zero p) hedge
  refine ⟨h1, h2, fun p hp => h3 p ?_, fun p hp => ?_, fun p t ht => ?_⟩
  · obtain ⟨j, hj, hη, ht⟩ := hp
    exact ⟨j, hj, by rw [norm_planeAxis]; exact hη, ht⟩
  · obtain ⟨j, hj, hη, ht⟩ := h4 p hp
    rw [norm_planeAxis] at hη
    exact ⟨j, hj, hη, ht⟩
  · obtain ⟨ha, hb⟩ := h5 p t ht
    exact ⟨ha, by rw [hC]; exact hb⟩

/-- **GAF02, stage three** (CFS22's slim cutoff on the actual `𝓔⁰`): for any `f` with CFS31's boxed
contract for the slim family, the cutoff is smooth, `[0,1]`-valued, one on the threshold-`6ℓ`
plateau (`ℓ = 10⁵Δ`), its closed support localizes the original point to the threshold-`7ℓ` slim
core, and `‖Dψ₃‖ ≤ b_cut/ρ` along the segment from `𝓔⁰` to `f`. -/
theorem gaf02_stageThree_cutoff
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (f : X → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hpert : ∀ p, ‖f p - cgpGlobalMap P.toLocalChartFamily P.zero p‖ ≤
      4 * gafKappa / 5 * ρ p)
    (hZM : ∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p = 0 →
      |gafSlimMarker P.toLocalChartFamily P.zero j (f p)| ≤ ρ j.1 / 32) :
    ContDiff ℝ ∞ (gafStageThreeCutoff P.toLocalChartFamily P.zero) ∧
      (∀ z, gafStageThreeCutoff P.toLocalChartFamily P.zero z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p, (∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
          |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| < 6 * (10 ^ 5 * Δ)) →
        gafStageThreeCutoff P.toLocalChartFamily P.zero (f p) = 1) ∧
      (∀ p, f p ∈ tsupport (gafStageThreeCutoff P.toLocalChartFamily P.zero) →
        ∃ j : P.slim.finite_centres.toFinset, p ∈ ball j.1 (1000000 * Δ * ρ j.1) ∧
          |(P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p| <
            7 * (10 ^ 5 * Δ)) ∧
      (∀ p, ∀ t ∈ Icc (0 : ℝ) 1,
        ‖fderiv ℝ (gafStageThreeCutoff P.toLocalChartFamily P.zero)
          ((1 - t) • cgpGlobalMap P.toLocalChartFamily P.zero p + t • f p)‖ ≤
            gafCutoffConstant / ρ p) := by
  have hΔ0 : 0 < Δ := by linarith
  have hsmall : Λ * (1000000 * Δ) ≤ 1 / 4 := by nlinarith
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  have hζI : ∀ (j : P.slim.finite_centres.toFinset) p, P.slim.cutoff j.1 p ∈ Icc (0 : ℝ) 1 := by
    intro j p
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    rw [slimFamily_cutoff_eq_KA2 P.toLocalChartFamily hj]
    exact (P.slim.centre j.1 hj).cutoff_mem_Icc p
  have hζU : ∀ (j : P.slim.finite_centres.toFinset) p, p ∉ ball j.1 (1000000 * Δ * ρ j.1) →
      P.slim.cutoff j.1 p = 0 := by
    intro j p hp
    by_contra h
    exact hp (cgpMarkerCutoff_ne_zero P.toLocalChartFamily hΔ0 (.inr (.inl j)) p h)
  have hcomp : ∀ (j : P.slim.finite_centres.toFinset) p, 0 < P.slim.cutoff j.1 p →
      3 / 4 * ρ j.1 ≤ ρ p ∧ ρ p ≤ 5 / 4 * ρ j.1 ∧
        ‖planeAxis ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p)‖ ≤
          9 * (10 ^ 5 * Δ) := by
    intro j p hpos
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    obtain ⟨h1, h2⟩ := cgpMarkerCutoff_scale_GAF2 P.toLocalChartFamily P.zero hΔ hσs hσs1 hΛ
      hsmall (.inr (.inl j)) p hpos
    change 3 * ρ j.1 / 4 ≤ ρ p at h1
    change ρ p ≤ 5 * ρ j.1 / 4 at h2
    have hpos' : 0 < (P.slim.centre j.1 hj).cutoff p := by
      rw [← slimFamily_cutoff_eq_KA2 P.toLocalChartFamily hj]
      exact hpos
    have h3 := (P.slim.centre j.1 hj).abs_coord_le_of_mem_tsupport (subset_tsupport _ hpos'.ne')
    refine ⟨by linarith, by linarith, ?_⟩
    rw [norm_planeAxis]
    linarith
  have hplateau : ∀ (j : P.slim.finite_centres.toFinset) p, p ∈ ball j.1 (1000000 * Δ * ρ j.1) →
      ‖planeAxis ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p)‖ <
        6 * (10 ^ 5 * Δ) → P.slim.cutoff j.1 p = 1 := by
    intro j p hp hη
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    rw [norm_planeAxis] at hη
    rw [slimFamily_cutoff_eq_KA2 P.toLocalChartFamily hj]
    refine (P.slim.centre j.1 hj).cutoff_eq_one_of_abs_coord_le ?_ (by linarith)
    convert hp using 2
    norm_num
  have hkappa : gafKappa = 1 / (1000 * ((gafMultiplicity : ℝ) + 1) * cgpProfileBound ^ 2) := rfl
  have hC : gafCutoffConstant = 10 ^ 4 * ((gafMultiplicity : ℝ) + 1) ^ 2 * cgpProfileBound ^ 4 :=
    rfl
  rw [hkappa] at hpert
  obtain ⟨h1, h2, h3, h4, h5⟩ := cfs22_row lc87EdgeTransition_contDiff
    (fun _ ht => lc87EdgeTransition_eq_zero ht) (fun _ ht => lc87EdgeTransition_eq_one ht)
    lc87EdgeTransition_mem_Icc cgpProfileBound_spec.1 abs_deriv_lc87EdgeTransition_le_cgp
    gafMultiplicity (gafSlimVector P.toLocalChartFamily P.zero)
    (gafSlimMarker P.toLocalChartFamily P.zero) (fun _ => norm_blockVectorCLM_le _)
    (fun _ => norm_blockMarkerCLM_le _) hℓ (fun j : P.slim.finite_centres.toFinset => ρ j.1)
    (fun _ => hρ _) ρ hρ (fun j => ball j.1 (1000000 * Δ * ρ j.1))
    (fun j p => planeAxis ((P.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord p))
    (fun j p => P.slim.cutoff j.1 p) hζI (cgpGlobalMap P.toLocalChartFamily P.zero) f hζU
    (gafSlim_block_GAF2 P.toLocalChartFamily P.zero)
    (gafSlim_count_GAF2 P hΛ hΔ hμ hτ hLΛ hLmax he hT) hcomp hplateau hpert hZM
  refine ⟨h1, h2, fun p hp => h3 p ?_, fun p hp => ?_, fun p t ht => ?_⟩
  · obtain ⟨j, hj, hη⟩ := hp
    exact ⟨j, hj, by rw [norm_planeAxis]; exact hη⟩
  · obtain ⟨j, hj, hη⟩ := h4 p hp
    rw [norm_planeAxis] at hη
    exact ⟨j, hj, hη⟩
  · rw [hC]
    exact h5 p t ht

end DifferentialGeometry.Geometry.Collapse
