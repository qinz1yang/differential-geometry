import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortEdgeMarkers
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPacketsBF

/-!
# Pointwise clauses of the edge stage table on a boundary supply (lane B-PORT-EDGEb)

The clauses (SEL), (PRE), (LOC), (COV) of `port_edge_interior_table_BAUGP` at ONE core witness, on
the actual slot `actualSlotsV2_BAUGD S` (`f(q) = π₁F_∂(q)`, `q ∈ W°`, distances `d_ĝ`). Closed
twins: `egp07_full_marker` / `egp07_exact_coordinate` (PRE), `egp07_localization_KC5` (LOC),
the section step of `egp07_coverage` (COV), all in `Fibration/ActualEdgeCloud*.lean`. The reference
domain `D_a = B(a, 20Δρ(a))` (`stageDomain_BIF Δ 1`) comes from the edge support
`⊆ B̄(a, 14Δρ(a))` (FC18 (ii), `edge_dist_le_of_cutoff_ne_zero_BPE`); the height of a localized
point is the ONE global height `t_B`, bounded at its own core witness; the coverage uses EGP05's
section, the family field `LocalPacketsOnBF.edgeB_section`.

* `LocalPacketsOnBF.edgeB_section_phys_BPE` (EGP05's section in physical units, twin
  `LocalChartPacketsC14.edge_section_FAM`);
* `stageDomain_one_BPE`, `edge_core_dist_lt_BPE` (a threshold-`8` core point lies in `D_a`);
* `edge_preimage_core_BPE` (PRE), `edge_localization_BPE` (LOC), `edge_coverage_BPE` (COV).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Section

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **EGP05's section in physical units** on the boundary family (twin
`LocalChartPacketsC14.edge_section_FAM`): for every `|u| < 8.5Δ` there is `q` with `η_j(q) = u`,
height `F(q)/ρ(q) < Δ/100` and `d(q, j) < 10Δρ(j)`. -/
theorem LocalPacketsOnBF.edgeB_section_phys_BPE
    (P : LocalPacketsOnBF X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
      ζ Λz U₁ U₂ Ue₁ Ue₂) {j : X} (hj : j ∈ P.edgeB.centres) (u : ℝ) (hu : |u| < 17 / 2 * Δ) :
    ∃ q : X, P.edgeB.coord_BAUGA j q = u ∧ P.edgeB.smoothing q / ρ q < Δ / 100 ∧
      dist q j < 10 * Δ * ρ j := by
  obtain ⟨sec, -, hsec⟩ := P.edgeB_section j hj
  obtain ⟨h1, h2, h3⟩ := hsec ⟨u, abs_lt.mp hu⟩
  have hrj := hρ j
  have hrs := hρ (sec ⟨u, abs_lt.mp hu⟩)
  refine ⟨sec ⟨u, abs_lt.mp hu⟩, ?_, ?_, ?_⟩
  · rw [P.edgeB.coord_BAUGA_of_mem hj]
    exact h1
  · have hq : P.edgeB.smoothing (sec ⟨u, abs_lt.mp hu⟩) / ρ j /
        (ρ (sec ⟨u, abs_lt.mp hu⟩) / ρ j) =
        P.edgeB.smoothing (sec ⟨u, abs_lt.mp hu⟩) / ρ (sec ⟨u, abs_lt.mp hu⟩) := by
      field_simp
    rw [← hq]
    exact h2
  · have h3' : (ρ j)⁻¹ * dist (sec ⟨u, abs_lt.mp hu⟩) j < 10 * Δ := h3
    rw [inv_mul_lt_iff₀ hrj] at h3'
    linarith

end Section

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- The edge reference domain constant: `C_1 = 20Δ`. -/
theorem stageDomain_one_BPE (Δ : ℝ) : stageDomain_BIF Δ 1 = 20 * Δ :=
  rfl

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- A point with positive edge cutoff of `j` lies in `D_j = B(j, 20Δρ_j)`. -/
theorem edge_domain_of_cutoff_ne_zero_BPE (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (j : S.EdgeIdx_BAUGD)
    {q : W.pieceInterior ⊤}
    (hq : (letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      S.family.edgeB.cutoff_BAUGA j.1 q) ≠ 0) :
    letI := inducedMetricSpace S.completion.metric
    dist q j.1 < stageDomain_BIF Δ 1 * S.rho j.1 := by
  have h := S.edge_dist_le_of_cutoff_ne_zero_BPE hΛ hΔ hμ hτ hΔΛ j hq
  have hrj := S.rho_pos j.1
  rw [stageDomain_one_BPE]
  have h2 : 14 * Δ * S.rho j.1 < 20 * Δ * S.rho j.1 := by nlinarith [mul_pos hΔ hrj]
  exact lt_of_le_of_lt h h2

/-- **A threshold-`8` core point lies in `D_j`** (plateau + FC18 (ii)). -/
theorem edge_core_dist_lt_BPE (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (j : S.EdgeIdx_BAUGD)
    {q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist q j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 q| ≤ 8 * Δ) (ht : S.edgeHeightRaw q ≤ 8 * Δ) :
    letI := inducedMetricSpace S.completion.metric
    dist q j.1 < stageDomain_BIF Δ 1 * S.rho j.1 :=
  S.edge_domain_of_cutoff_ne_zero_BPE hΛ hΔ hμ hτ hΔΛ j
    (by rw [S.edge_cutoff_eq_one_BPE hΔ j hd hη ht]; exact one_ne_zero)

/-- **(PRE) at one core witness** (closed `egp07_full_marker` + `egp07_exact_coordinate`): a
preimage `q` of `f(p)`, `p` in the threshold-`8` core of the edge chart `j`, has full marker
`ζ_j(q) = 1`, the same coordinate `η_j(q) = η_j(p)`, lies in the threshold-`8` core and in `D_j`. -/
theorem edge_preimage_core_BPE (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (j : S.EdgeIdx_BAUGD)
    {p q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist p j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 p| ≤ 8 * Δ) (ht : S.edgeHeightRaw p ≤ 8 * Δ)
    (hpq : (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) =
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val)) :
    letI := inducedMetricSpace S.completion.metric
    ((dist q j.1 < 100 * Δ * S.rho j.1 ∧ |S.edgeEta_BIF j.1 q| ≤ 8 * Δ ∧
        S.edgeHeightRaw q ≤ 8 * Δ) ∧
      dist q j.1 < stageDomain_BIF Δ 1 * S.rho j.1 ∧ S.edgeEta_BIF j.1 q = S.edgeEta_BIF j.1 p) ∧
      (letI := S.completion.complete; S.family.edgeB.cutoff_BAUGA j.1 q) = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hrj := S.rho_pos j.1
  have hcp := S.edge_cutoff_eq_one_BPE hΔ j hd hη ht
  have hm := congrArg (S.edgeMarker_BAUGD j) hpq
  rw [S.edgeMarker_stageOne_BPE j q, S.edgeMarker_stageOne_BPE j p, hcp, mul_one] at hm
  have hcq : S.family.edgeB.cutoff_BAUGA j.1 q = 1 :=
    mul_left_cancel₀ hrj.ne' (hm.trans (mul_one _).symm)
  have hv := congrArg (S.edgeVector_BAUGD j) hpq
  rw [S.edgeVector_stageOne_BPE j q, S.edgeVector_stageOne_BPE j p, hcp, hcq, mul_one] at hv
  have hηq : S.edgeEta_BIF j.1 q = S.edgeEta_BIF j.1 p :=
    planeAxis_injective_SGP3 (smul_right_injective _ hrj.ne' hv)
  have hcore := S.edge_core_of_cutoff_eq_one_BPE hΔ j hcq
  refine ⟨⟨hcore, ?_, hηq⟩, hcq⟩
  exact S.edge_domain_of_cutoff_ne_zero_BPE hΛ hΔ hμ hτ hΔΛ j (by rw [hcq]; exact one_ne_zero)

/-- **(LOC) at one core witness** (closed `egp07_localization_KC5`): if `p` is in the threshold-`7`
core of the edge chart `j`, `q` has height `t(q) ≤ 8Δ` (a core point of some edge chart) and
`‖pr_int(f(q) − f(p))‖ ≤ Rρ_j` with `R < 1/100`, then `q` is in the threshold-`8` core of `j` and
in `D_j`. -/
theorem edge_localization_BPE (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (j : S.EdgeIdx_BAUGD)
    {p q : W.pieceInterior ⊤}
    (hd : letI := inducedMetricSpace S.completion.metric; dist p j.1 < 100 * Δ * S.rho j.1)
    (hη : |S.edgeEta_BIF j.1 p| ≤ 7 * Δ) (ht : S.edgeHeightRaw p ≤ 7 * Δ)
    (htq : S.edgeHeightRaw q ≤ 8 * Δ) {R : ℝ} (hR : R < 1 / 100)
    (hpq : ‖augIntProjCLM_BAUGC ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) -
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val))‖ ≤ R * S.rho j.1) :
    letI := inducedMetricSpace S.completion.metric
    (dist q j.1 < 100 * Δ * S.rho j.1 ∧ |S.edgeEta_BIF j.1 q| ≤ 8 * Δ ∧
        S.edgeHeightRaw q ≤ 8 * Δ) ∧
      dist q j.1 < stageDomain_BIF Δ 1 * S.rho j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ : 0 < Δ := by linarith
  have hrj := S.rho_pos j.1
  have hcp := S.edge_cutoff_eq_one_BPE hΔ j hd (by linarith) (by linarith)
  have hblk := norm_inl_sub_le_augIntProj_BPS
    ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val))
    ((actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap p.val)) (.inr (.inr (.inl j)))
  rw [S.edgeBlock_stageOne_BPE j q, S.edgeBlock_stageOne_BPE j p, hcp, ← dist_eq_norm,
    dist_block_scale_GAF hrj, one_smul] at hblk
  have hd1 : dist (WithLp.toLp 2 (S.family.edgeB.cutoff_BAUGA j.1 q •
      planeAxis (S.edgeEta_BIF j.1 q), S.family.edgeB.cutoff_BAUGA j.1 q))
      (WithLp.toLp 2 (planeAxis (S.edgeEta_BIF j.1 p), (1 : ℝ))) < 1 / 100 := by
    have h := hblk.trans hpq
    have h' : S.rho j.1 * dist (WithLp.toLp 2 (S.family.edgeB.cutoff_BAUGA j.1 q •
        planeAxis (S.edgeEta_BIF j.1 q), S.family.edgeB.cutoff_BAUGA j.1 q))
        (WithLp.toLp 2 (planeAxis (S.edgeEta_BIF j.1 p), (1 : ℝ))) < S.rho j.1 * (1 / 100) := by
      nlinarith
    exact lt_of_mul_lt_mul_left h' hrj.le
  have hA : ‖planeAxis (S.edgeEta_BIF j.1 p)‖ ≤ 7 * Δ := by
    rw [norm_planeAxis]; exact hη
  obtain ⟨hζ, hv⟩ := norm_coordinate_sub_lt_of_block_dist (by norm_num) (by norm_num) hA hd1
  rw [← map_sub, norm_planeAxis] at hv
  have hcq : S.family.edgeB.cutoff_BAUGA j.1 q ≠ 0 := by
    intro h
    rw [h] at hζ
    norm_num at hζ
  have hdq := S.edge_dist_lt_of_cutoff_ne_zero_BPE hΔ j hcq
  have hηq : |S.edgeEta_BIF j.1 q| ≤ 8 * Δ := by
    have h1 := abs_sub_abs_le_abs_sub (S.edgeEta_BIF j.1 q) (S.edgeEta_BIF j.1 p)
    have h2 : (1 + 7 * Δ) * (1 / 100) / (1 - 1 / 100) ≤ Δ := by
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    linarith
  exact ⟨⟨hdq, hηq, htq⟩, S.edge_domain_of_cutoff_ne_zero_BPE hΛ hΔ hμ hτ hΔΛ j hcq⟩

/-- **(COV) at one core witness** (the section step of closed `egp07_coverage`): for `p` in the
threshold-`7` core of the edge chart `j` and `|u − η_j(p)| ≤ 1/100` there is `q` in the
threshold-`8` core of `j` and in `D_j` with `η_j(q) = u` and `f(q) ∈ S̃₁` (EGP05's section). -/
theorem edge_coverage_BPE (hΔ1 : 1 ≤ Δ) (j : S.EdgeIdx_BAUGD) {p : W.pieceInterior ⊤}
    (hη : |S.edgeEta_BIF j.1 p| ≤ 7 * Δ) {u : ℝ} (hu : |u - S.edgeEta_BIF j.1 p| ≤ 1 / 100) :
    letI := inducedMetricSpace S.completion.metric
    ∃ q : W.pieceInterior ⊤,
      (dist q j.1 < 100 * Δ * S.rho j.1 ∧ |S.edgeEta_BIF j.1 q| ≤ 8 * Δ ∧
        S.edgeHeightRaw q ≤ 8 * Δ) ∧
      dist q j.1 < stageDomain_BIF Δ 1 * S.rho j.1 ∧ S.edgeEta_BIF j.1 q = u ∧
      (actualSlotsV2_BAUGD S).stageProj 1 (S.boundaryOriginalMap q.val) ∈
        (actualSlotsV2_BAUGD S).stageCloudEnlarged 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ : 0 < Δ := by linarith
  have hrj := S.rho_pos j.1
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hu8 : |u| ≤ 8 * Δ := by
    have := abs_sub_abs_le_abs_sub u (S.edgeEta_BIF j.1 p)
    linarith
  obtain ⟨q, hqu, hqt, hqd⟩ :=
    S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF.edgeB_section_phys_BPE hj u (by linarith)
  have hqη : S.edgeEta_BIF j.1 q = u := by rw [S.edgeEta_eq_coord_BAUGP2]; exact hqu
  have hqt' : S.edgeHeightRaw q ≤ 8 * Δ := by
    rw [S.edgeHeightRaw_apply]
    have : Δ / 100 ≤ 8 * Δ := by linarith
    exact (hqt.trans_le this).le
  have hqd' : dist q j.1 < 100 * Δ * S.rho j.1 := by nlinarith [mul_pos hΔ hrj]
  have hηq : |S.edgeEta_BIF j.1 q| ≤ 8 * Δ := by rw [hqη]; exact hu8
  refine ⟨q, ⟨hqd', hηq, hqt'⟩, ?_, hqη,
    S.stageProj_mem_stageCloudEnlarged_one_BPE j hqd' hηq hqt'⟩
  rw [stageDomain_one_BPE]
  nlinarith [mul_pos hΔ hrj]

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
