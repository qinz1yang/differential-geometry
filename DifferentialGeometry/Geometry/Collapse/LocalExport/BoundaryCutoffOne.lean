import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCutoffZero

/-!
# BCG03: CFS23's edge cutoff `ψ₁` of the boundary chain, bound to the actual map (lane BAUG-PSI)

Part (a) of target A2-mk (`TargetsBoundary-A-v2.lean.txt`; review 69 D69-5): the second component
of `BoundaryGaf02Chain.cutoff_bindings` on the ACTUAL slot (`actualSlotsV2_BAUGD`, cutoff
`ψ₁ = cutoffOne_BAUGD`, CFS23's buffered edge cutoff on the `edgeB` blocks, the scale marker and the
`E'` block of `H^∂`), stated — as on the closed side (`gaf02_stageTwo_cutoff`) — for ANY map `f`
with CFS31's boxed contract `‖f − F_∂‖ ≤ (4κ/5)ρ` and the zero-marker clause `ζ_j = 0 ⟹
|v_j(f)| ≤ ρ_j/32`, at the actual augmented map `F_∂ = S.boundaryOriginalMap` on the WHOLE original
carrier `W` (kernel `cfs23_row`).

* early constants: the family multiplicities `edgeCount_BAUGP2`, `slimCount_BAUGP2`, the derivative
  constants `cutoffOneConst_BAUGP2`, `cutoffTwoConst_BAUGP2` and the ONE perturbation constant
  `cutoffKappa_BAUGP2 = min(κ₁, κ₂)`;
* the `edgeB` blocks of `F_∂` on `W`: `edgeCutoffW_BAUGP2`, `edgeCoordW_BAUGP2`,
  `edgeHeightW_BAUGP2` (zero extensions), `edgeBlock_boundaryOriginalMap_BAUGP2`;
* the `E'` block `heightBlock_boundaryOriginalMap_BAUGP2` (`‖x₁(F_∂)‖ = ρ t z_{E'}`,
  `x₂(F_∂) = ρ z_{E'}`), the count `edge_count_BAUGP2` (the `edgeB` family's own `multiplicity`),
  the comparability `edge_scale_comparable_BAUGP2` (T3B transport, `Λ`-Lipschitz `ρ`), the edge
  identity `edgeCutoffW_identity_BAUGP2` (`ζ_j = 1 − χ_{8,9}(t/Δ)` where `|η_j| < 8Δ`);
* **`cutoffOne_binding_BAUGP2`** (the chain's `cutoff_bindings.2.1` verbatim with `f` for the
  stage input, at every `b_cut ≥ b₁`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-! ## Early constants (independent of carrier, member and supply) -/

/-- The `edgeB` multiplicity bound (the real bound of `EdgeFamilyOn.multiplicity`). -/
def edgeCountReal_BAUGP2 : ℝ :=
  modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3
      (4 * (1 + 2 * 2000000 + 1 / 3)) /
    modelVolume (-((1 / (4 * (1 + 2 * 2000000 + 1 / 3)) : ℝ) ^ 2)) 3 (1 / 3)

/-- `N₁ = ⌊…⌋₊`, the `edgeB` count. -/
def edgeCount_BAUGP2 : ℕ := ⌊edgeCountReal_BAUGP2⌋₊

/-- The slim multiplicity bound (the real bound of `SlimFamilyOn.multiplicity`). -/
def slimCountReal_BAUGP2 : ℝ :=
  modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
    modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)

/-- `N₂ = ⌊…⌋₊`, the slim count. -/
def slimCount_BAUGP2 : ℕ := ⌊slimCountReal_BAUGP2⌋₊

/-- CFS23's derivative constant of `ψ₁`: `b₁ = 10⁴ (N₁ + 1)² P₀⁴`. -/
def cutoffOneConst_BAUGP2 : ℝ :=
  10 ^ 4 * ((edgeCount_BAUGP2 : ℝ) + 1) ^ 2 * cgpProfileBound ^ 4

/-- CFS22's derivative constant of `ψ₂`: `b₂ = 10⁴ (N₂ + 1)² P₀⁴`. -/
def cutoffTwoConst_BAUGP2 : ℝ :=
  10 ^ 4 * ((slimCount_BAUGP2 : ℝ) + 1) ^ 2 * cgpProfileBound ^ 4

/-- The ONE perturbation constant `κ = min(κ₁, κ₂)`, `κ_j = 1/(1000 (N_j + 1) P₀²)`. -/
def cutoffKappa_BAUGP2 : ℝ :=
  min (1 / (1000 * ((edgeCount_BAUGP2 : ℝ) + 1) * cgpProfileBound ^ 2))
    (1 / (1000 * ((slimCount_BAUGP2 : ℝ) + 1) * cgpProfileBound ^ 2))

theorem cutoffOneConst_nonneg_BAUGP2 : 0 ≤ cutoffOneConst_BAUGP2 := by
  unfold cutoffOneConst_BAUGP2
  positivity

theorem cutoffTwoConst_nonneg_BAUGP2 : 0 ≤ cutoffTwoConst_BAUGP2 := by
  unfold cutoffTwoConst_BAUGP2
  positivity

theorem cutoffKappa_pos_BAUGP2 : 0 < cutoffKappa_BAUGP2 := by
  have hP : 0 < cgpProfileBound := lt_of_lt_of_le one_pos cgpProfileBound_spec.1
  unfold cutoffKappa_BAUGP2
  exact lt_min (by positivity) (by positivity)

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- **Comparability through T3B's transport**: for a centre `j` with `D(j) > 10`, a point of the
`d_ĝ`-ball `B(j, rρ_j)` (`r ≤ 2·10⁶Δ`, `Λr ≤ 1/4`) has `3ρ_j/4 ≤ ρ ≤ 5ρ_j/4`. -/
theorem rho_comparable_of_dist_lt_BAUGP2 (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) {j q : W.pieceInterior ⊤}
    (hj : ENNReal.ofReal 10 < distanceToBoundary W g j) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ 2000000 * Δ) (hΛr : Λ * r ≤ 1 / 4)
    (hq : letI := inducedMetricSpace S.completion.metric; dist q j < r * S.rho j) :
    3 / 4 * S.rho j ≤ S.rho q ∧ S.rho q ≤ 5 / 4 * S.rho j := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ : 0 < Δ := by linarith
  have htr := (S.transport_spec.2.1 j hj).2
  have hK0 := consumerConstant_ge_BAUGA hΔ hV hβ1 hb
  have hrj := S.rho_pos j
  have hqK : q ∈ ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * S.rho j) := by
    rw [mem_ball]
    refine hq.trans_le (mul_le_mul_of_nonneg_right ?_ hrj.le)
    linarith
  have hjK : j ∈ ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * S.rho j) :=
    mem_ball_self (mul_pos (by nlinarith) hrj)
  have hdist : riemannianEDistOf g q.val j.val = edist q j := htr q hqK j hjK
  have hedist : edist q j < ENNReal.ofReal (r * S.rho j) := edist_lt_ofReal.mpr hq
  have hlip := S.scale_spec.2.1 q.val j.val
  have h1 : ENNReal.ofReal |S.rho q.val - S.rho j.val| ≤ ENNReal.ofReal (Λ * (r * S.rho j)) := by
    refine hlip.trans ?_
    rw [hdist, ENNReal.ofReal_mul hΛ]
    exact mul_le_mul_right hedist.le _
  have h2 : |S.rho q.val - S.rho j.val| ≤ Λ * (r * S.rho j) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have h3 : Λ * (r * S.rho j) ≤ 1 / 4 * S.rho j := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hΛr hrj.le
  have h4 := abs_le.mp (h2.trans h3)
  constructor <;> linarith [h4.1, h4.2]

/-! ### The `edgeB` blocks of `F_∂` on `W` -/

/-- The `edgeB` cutoff `ζ_j` on `W` (zero extension from `W°`). -/
def edgeCutoffW_BAUGP2 (j : S.EdgeIdx_BAUGD) : W.Carrier → ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  Subtype.val.extend (S.family.edgeB.cutoff_BAUGA j.1) 0

/-- The `edgeB` coordinate `η_j` on the axis of `ℝ²`, on `W` (zero extension from `W°`). -/
def edgeCoordW_BAUGP2 (j : S.EdgeIdx_BAUGD) : W.Carrier → ℝ² :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  Subtype.val.extend (fun x => planeAxis (S.family.edgeB.coord_BAUGA j.1 x)) 0

/-- The normalized weak-edge height `t_B = edgeB.smoothing/ρ` on `W` (zero extension). -/
def edgeHeightW_BAUGP2 : W.Carrier → ℝ :=
  Subtype.val.extend S.edgeHeightRaw 0

/-- The `edgeB` chart domain `B(j, 100Δρ_j)` (in `d_ĝ`) as a subset of `W`. -/
def edgeDomW_BAUGP2 (j : S.EdgeIdx_BAUGD) : Set W.Carrier :=
  letI := inducedMetricSpace S.completion.metric
  Subtype.val '' ball j.1 (100 * Δ * S.rho j.1)

theorem edgeCutoffW_val_BAUGP2 (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.edgeCutoffW_BAUGP2 j q.val =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       S.family.edgeB.cutoff_BAUGA j.1 q) :=
  Subtype.val_injective.extend_apply _ _ q

theorem edgeCoordW_val_BAUGP2 (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.edgeCoordW_BAUGP2 j q.val =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       planeAxis (S.family.edgeB.coord_BAUGA j.1 q)) :=
  Subtype.val_injective.extend_apply _ _ q

theorem edgeHeightW_val_BAUGP2 (q : W.pieceInterior ⊤) :
    S.edgeHeightW_BAUGP2 q.val = S.edgeHeightRaw q :=
  Subtype.val_injective.extend_apply _ _ q

theorem edgeCutoffW_of_notMem_BAUGP2 (j : S.EdgeIdx_BAUGD) {p : W.Carrier}
    (hp : ¬ ∃ q : W.pieceInterior ⊤, q.val = p) : S.edgeCutoffW_BAUGP2 j p = 0 := by
  unfold edgeCutoffW_BAUGP2
  rw [Function.extend_apply' _ _ _ hp]
  rfl

theorem edgeCoordW_of_notMem_BAUGP2 (j : S.EdgeIdx_BAUGD) {p : W.Carrier}
    (hp : ¬ ∃ q : W.pieceInterior ⊤, q.val = p) : S.edgeCoordW_BAUGP2 j p = 0 := by
  unfold edgeCoordW_BAUGP2
  rw [Function.extend_apply' _ _ _ hp]
  rfl

/-- The `edgeB` coordinate of the reference table is the `edgeB` block coordinate on `W°`. -/
theorem edgeEta_eq_coord_BAUGP2 (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.edgeEta_BIF j.1 q =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       S.family.edgeB.coord_BAUGA j.1 q) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  rw [S.family.edgeB.coord_BAUGA_of_mem hj]
  simp only [edgeEta_BIF, hj, ↓reduceDIte]

/-- `‖η_j‖ = |edgeEta_j|` at an interior point. -/
theorem norm_edgeCoordW_val_BAUGP2 (j : S.EdgeIdx_BAUGD) (q : W.pieceInterior ⊤) :
    ‖S.edgeCoordW_BAUGP2 j q.val‖ = |S.edgeEta_BIF j.1 q| := by
  rw [S.edgeCoordW_val_BAUGP2, norm_planeAxis, S.edgeEta_eq_coord_BAUGP2]

/-- **The `edgeB` blocks of `F_∂` on `W`**: `u_j(F_∂ p) = (ρ_j ζ_j(p)) • η_j(p)` and
`v_j(F_∂ p) = ρ_j ζ_j(p)` (both zero at boundary points). -/
theorem edgeBlock_boundaryOriginalMap_BAUGP2 (j : S.EdgeIdx_BAUGD) (p : W.Carrier) :
    S.edgeVector_BAUGD j (S.boundaryOriginalMap p) =
        (S.rho j.1 * S.edgeCutoffW_BAUGP2 j p) • S.edgeCoordW_BAUGP2 j p ∧
      S.edgeMarker_BAUGD j (S.boundaryOriginalMap p) =
        S.rho j.1 * S.edgeCutoffW_BAUGP2 j p := by
  have hne : (.inr (.inr (.inl j)) : S.IntTag_BAUGA) ≠ S.scaleTag_BAUGA := by
    simp [scaleTag_BAUGA]
  have hslot : S.boundaryOriginalMap p (Sum.inl (.inr (.inr (.inl j)))) =
      Subtype.val.extend (fun x => S.interiorMapOn_BAUGA x (.inr (.inr (.inl j)))) 0 p := by
    change S.intSlotW_BAUGA (.inr (.inr (.inl j))) p = _
    simp only [intSlotW_BAUGA, hne, ↓reduceIte]
  by_cases hp : ∃ q : W.pieceInterior ⊤, q.val = p
  · obtain ⟨q, rfl⟩ := hp
    rw [Subtype.val_injective.extend_apply] at hslot
    rw [S.edgeCutoffW_val_BAUGP2, S.edgeCoordW_val_BAUGP2]
    simp only [edgeVector_BAUGD, edgeMarker_BAUGD, blockVectorCLM_apply,
      blockMarkerCLM_apply, hslot]
    exact ⟨rfl, rfl⟩
  · rw [Function.extend_apply' _ _ _ hp] at hslot
    rw [S.edgeCutoffW_of_notMem_BAUGP2 j hp, S.edgeCoordW_of_notMem_BAUGP2 j hp]
    simp only [edgeVector_BAUGD, edgeMarker_BAUGD, blockVectorCLM_apply,
      blockMarkerCLM_apply, hslot, Pi.zero_apply, mul_zero, zero_smul]
    exact ⟨rfl, rfl⟩

/-- The `edgeB` cutoff vanishes off its chart domain. -/
theorem edgeCutoffW_eq_zero_BAUGP2 (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD) (p : W.Carrier)
    (hp : p ∉ S.edgeDomW_BAUGP2 j) : S.edgeCutoffW_BAUGP2 j p = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  by_cases hq : ∃ q : W.pieceInterior ⊤, q.val = p
  · obtain ⟨q, rfl⟩ := hq
    rw [S.edgeCutoffW_val_BAUGP2]
    refine S.family.edgeB.cutoff_eq_zero_of_notMem_ball_BAUGA hΔ fun hqb => hp ⟨q, hqb, rfl⟩
  · exact S.edgeCutoffW_of_notMem_BAUGP2 j hq

/-- The `edgeB` cutoffs on `W` take values in `[0, 1]`. -/
theorem edgeCutoffW_mem_Icc_BAUGP2 (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD) (p : W.Carrier) :
    S.edgeCutoffW_BAUGP2 j p ∈ Icc (0 : ℝ) 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  by_cases hq : ∃ q : W.pieceInterior ⊤, q.val = p
  · obtain ⟨q, rfl⟩ := hq
    rw [S.edgeCutoffW_val_BAUGP2]
    exact S.family.edgeB.cutoff_mem_Icc_BAUGA hΔ j.1 q
  · rw [S.edgeCutoffW_of_notMem_BAUGP2 j hq]
    exact ⟨le_rfl, zero_le_one⟩

/-- **The `edgeB` count**: at every point of `W` at most `N₁` `edgeB` cutoffs are positive (the
family's own `multiplicity` field). -/
theorem edge_count_BAUGP2 (hΔ : 0 < Δ) (p : W.Carrier) :
    (Finset.univ.filter fun j : S.EdgeIdx_BAUGD => 0 < S.edgeCutoffW_BAUGP2 j p).card ≤
      edgeCount_BAUGP2 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  by_cases hq : ∃ q : W.pieceInterior ⊤, q.val = p
  swap
  · have h0 : (Finset.univ.filter fun j : S.EdgeIdx_BAUGD => 0 < S.edgeCutoffW_BAUGP2 j p) =
        ∅ := by
      refine Finset.filter_false_of_mem fun j _ => ?_
      rw [S.edgeCutoffW_of_notMem_BAUGP2 j hq]
      exact lt_irrefl 0
    rw [h0, Finset.card_empty]
    exact Nat.zero_le _
  obtain ⟨q, rfl⟩ := hq
  have hM := S.family.edgeB.multiplicity q
  set A : Set (W.pieceInterior ⊤) := S.family.edgeB.centres ∩
    {j | q ∈ ball j (2000000 * (Δ * S.rho j))} with hA
  let F := Finset.univ.filter fun j : S.EdgeIdx_BAUGD => 0 < S.edgeCutoffW_BAUGP2 j q.val
  have hsub : ((F.map ⟨fun j : S.EdgeIdx_BAUGD => j.1, Subtype.val_injective⟩ :
      Finset (W.pieceInterior ⊤)) : Set (W.pieceInterior ⊤)) ⊆ A := by
    intro x hx
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image,
      Finset.mem_coe] at hx
    obtain ⟨j, hjF, rfl⟩ := hx
    have hpos : 0 < S.edgeCutoffW_BAUGP2 j q.val := (Finset.mem_filter.mp hjF).2
    rw [S.edgeCutoffW_val_BAUGP2] at hpos
    obtain ⟨hj, hball, -, -⟩ := S.family.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ hpos.ne'
    refine ⟨hj, ?_⟩
    have hrj := S.rho_pos j.1
    have hh := (inv_mul_lt_iff₀ hrj).mp hball
    change dist q j.1 < 2000000 * (Δ * S.rho j.1)
    nlinarith
  have hfin : A.Finite := S.family.edgeB.finite_centres.subset Set.inter_subset_left
  have hcard : (F.card : ℝ) ≤ A.ncard := by
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, Finset.card_map] at this
    exact_mod_cast this
  exact Nat.le_floor (hcard.trans hM)

/-- **Comparability on the `edgeB` supports**: `ζ_j(p) > 0 ⟹ 3ρ_j/4 ≤ ρ(p) ≤ 5ρ_j/4` and
`‖η_j(p)‖ ≤ 9Δ`. -/
theorem edge_scale_comparable_BAUGP2 (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (j : S.EdgeIdx_BAUGD) (p : W.Carrier) (hpos : 0 < S.edgeCutoffW_BAUGP2 j p) :
    3 / 4 * S.rho j.1 ≤ S.rho p ∧ S.rho p ≤ 5 / 4 * S.rho j.1 ∧
      ‖S.edgeCoordW_BAUGP2 j p‖ ≤ 9 * Δ := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ : 0 < Δ := by linarith
  by_cases hq : ∃ q : W.pieceInterior ⊤, q.val = p
  swap
  · rw [S.edgeCutoffW_of_notMem_BAUGP2 j hq] at hpos
    exact absurd hpos (lt_irrefl 0)
  obtain ⟨q, rfl⟩ := hq
  rw [S.edgeCutoffW_val_BAUGP2] at hpos
  obtain ⟨hj, hball, hη, -⟩ := S.family.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ hpos.ne'
  have hrj := S.rho_pos j.1
  have hd : dist q j.1 < 100 * Δ * S.rho j.1 := by
    have hh := (inv_mul_lt_iff₀ hrj).mp hball
    linarith
  have hj10 : ENNReal.ofReal 10 < distanceToBoundary W g j.1 :=
    lt_trans (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by norm_num, by norm_num⟩)
      (S.family.edgeB.centres_subset hj)
  have hΛr : Λ * (100 * Δ) ≤ 1 / 4 := by nlinarith
  obtain ⟨h1, h2⟩ := S.rho_comparable_of_dist_lt_BAUGP2 hΛ hΔ1 hV hβ1 hb hj10
    (by positivity) (by nlinarith) hΛr hd
  refine ⟨h1, h2, ?_⟩
  rw [S.edgeCoordW_val_BAUGP2, norm_planeAxis]
  exact hη.le

/-- **The `E'` block of `F_∂`** at an interior point: `‖x₁(F_∂)‖ = ρ t (h(t/Δ) χ_{1/2,1}(Σζ))` and
`x₂(F_∂) = ρ (h(t/Δ) χ_{1/2,1}(Σζ))` with `t = edgeB.smoothing/ρ` (BAUG-A's (WB)). -/
theorem heightBlock_boundaryOriginalMap_BAUGP2 (q : W.pieceInterior ⊤) :
    ‖S.heightVector_BAUGD (S.boundaryOriginalMap q.val)‖ =
        S.rho q.val * S.edgeHeightW_BAUGP2 q.val *
          (cgpEdgeH (S.edgeHeightW_BAUGP2 q.val / Δ) * cfsRamp lc87EdgeTransition (1 / 2) 1
            (∑ i : S.EdgeIdx_BAUGD, S.edgeCutoffW_BAUGP2 i q.val)) ∧
      S.heightMarker_BAUGD (S.boundaryOriginalMap q.val) =
        S.rho q.val * (cgpEdgeH (S.edgeHeightW_BAUGP2 q.val / Δ) *
          cfsRamp lc87EdgeTransition (1 / 2) 1
            (∑ i : S.EdgeIdx_BAUGD, S.edgeCutoffW_BAUGP2 i q.val)) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hE := S.boundaryOriginalMap_edgePrime_formula q
  have hsum : (∑ i : S.EdgeIdx_BAUGD, S.edgeCutoffW_BAUGP2 i q.val) =
      S.family.edgeBSum_BAUGA q := by
    simp only [S.edgeCutoffW_val_BAUGP2]
    rfl
  have hz : S.family.edgeBMarker_BAUGA q = cgpEdgeH (S.edgeHeightW_BAUGP2 q.val / Δ) *
      cfsRamp lc87EdgeTransition (1 / 2) 1
        (∑ i : S.EdgeIdx_BAUGD, S.edgeCutoffW_BAUGP2 i q.val) := by
    rw [hsum, S.edgeHeightW_val_BAUGP2]
    rfl
  have ht : S.family.edgeBHeight_BAUGA q = S.edgeHeightW_BAUGP2 q.val := by
    rw [S.edgeHeightW_val_BAUGP2]
    rfl
  have hz0 : 0 ≤ S.family.edgeBMarker_BAUGA q := (S.family.edgeBMarker_mem_Icc_BAUGA q).1
  have ht0 : 0 ≤ S.edgeHeightW_BAUGP2 q.val := by
    rw [S.edgeHeightW_val_BAUGP2, edgeHeightRaw_apply]
    exact div_nonneg (S.family.edgeB.smoothing_nonneg q) (S.rho_pos _).le
  have hrq := S.rho_pos q.val
  simp only [heightVector_BAUGD, heightMarker_BAUGD, blockVectorCLM_apply,
    blockMarkerCLM_apply, hE]
  rw [← hz]
  refine ⟨?_, rfl⟩
  change ‖(S.rho q.val * S.family.edgeBMarker_BAUGA q) •
    planeAxis (S.family.edgeBHeight_BAUGA q)‖ = _
  rw [norm_smul, norm_planeAxis, ht, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrq.le hz0),
    abs_of_nonneg ht0]
  ring

/-- **The edge identity** (CGP01): on the chart domain, where `‖η_j‖ < 8Δ`,
`ζ_j = 1 − χ_{8,9}(t/Δ)`. -/
theorem edgeCutoffW_identity_BAUGP2 (hΔ : 0 < Δ) (j : S.EdgeIdx_BAUGD) (p : W.Carrier)
    (hp : p ∈ S.edgeDomW_BAUGP2 j) (hη : ‖S.edgeCoordW_BAUGP2 j p‖ < 8 * Δ) :
    S.edgeCutoffW_BAUGP2 j p =
      1 - cfsRamp lc87EdgeTransition 8 9 (S.edgeHeightW_BAUGP2 p / Δ) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨q, hq, rfl⟩ := hp
  rw [S.edgeCoordW_val_BAUGP2, norm_planeAxis] at hη
  rw [S.edgeCutoffW_val_BAUGP2, S.edgeHeightW_val_BAUGP2]
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  rw [S.family.edgeB.cutoff_eq_formula_BAUGA hj hq, edgeCoordinateProfile_eq_one_sub_cfsRamp_abs,
    edgeHeightProfile_eq_one_sub_cfsRamp]
  have h0 : cfsRamp lc87EdgeTransition 8 9 |S.family.edgeB.coord_BAUGA j.1 q / Δ| = 0 := by
    refine cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num) ?_
    rw [abs_div, abs_of_pos hΔ, div_le_iff₀ hΔ]
    linarith
  rw [h0, sub_zero, one_mul]
  rfl

end BoundarySupplyCore

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- **`ψ₁` bound to the actual map** (CFS23 on the actual `edgeB` blocks, scale marker and `E'`
block of `F_∂`; the chain's `cutoff_bindings.2.1` verbatim with `f` for the stage input, at every
`b_cut ≥ b₁`). -/
theorem cutoffOne_binding_BAUGP2 (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (f : W.Carrier → BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (hpert : ∀ p, ‖f p - S.boundaryOriginalMap p‖ ≤ 4 * cutoffKappa_BAUGP2 / 5 * S.rho p)
    (hZM : ∀ (j : S.EdgeIdx_BAUGD) (p : W.Carrier), S.edgeCutoffW_BAUGP2 j p = 0 →
      |S.edgeMarker_BAUGD j (f p)| ≤ S.rho j.1 / 32)
    {bcut : ℝ} (hbcut : cutoffOneConst_BAUGP2 ≤ bcut) :
    letI := inducedMetricSpace S.completion.metric
    ContDiffOn ℝ ∞ ((actualSlotsV2_BAUGD S).cutoff 1) {z | 0 < S.scaleMarker_BIF z} ∧
      (∀ z, (actualSlotsV2_BAUGD S).cutoff 1 z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p : W.pieceInterior ⊤, (∃ j ∈ S.stageCentres_BIF 1, dist p j < 100 * Δ * S.rho j ∧
          |S.edgeEta_BIF j p| < 6 * Δ ∧ S.edgeHeightRaw p < 6 * Δ) →
        (actualSlotsV2_BAUGD S).cutoff 1 (f p.val) = 1) ∧
      (∀ p : W.Carrier, f p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 1) →
        ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 1,
          dist q j < 100 * Δ * S.rho j ∧ |S.edgeEta_BIF j q| < 7 * Δ ∧
            S.edgeHeightRaw q < 7 * Δ) ∧
      ∀ p : W.Carrier, ∀ t ∈ Icc (0 : ℝ) 1,
        0 < S.scaleMarker_BIF ((1 - t) • S.boundaryOriginalMap p + t • f p) ∧
        ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 1)
          ((1 - t) • S.boundaryOriginalMap p + t • f p)‖ ≤ bcut / S.rho p := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ : 0 < Δ := by linarith
  have hψ : (actualSlotsV2_BAUGD S).cutoff 1 = S.cutoffOne_BAUGD :=
    (actualSlotsV2_cutoff_BAUGD S).2.1
  have hpert' : ∀ p, ‖f p - S.boundaryOriginalMap p‖ ≤
      4 * (1 / (1000 * ((edgeCount_BAUGP2 : ℝ) + 1) * cgpProfileBound ^ 2)) / 5 * S.rho p := by
    intro p
    refine (hpert p).trans (mul_le_mul_of_nonneg_right ?_ (S.rho_pos p).le)
    have := min_le_left (1 / (1000 * ((edgeCount_BAUGP2 : ℝ) + 1) * cgpProfileBound ^ 2))
      (1 / (1000 * ((slimCount_BAUGP2 : ℝ) + 1) * cgpProfileBound ^ 2))
    unfold cutoffKappa_BAUGP2
    linarith
  obtain ⟨h1, h2, h3, h4, h5⟩ := cfs23_row (fun j : S.EdgeIdx_BAUGD => S.rho j.1)
    S.edgeVector_BAUGD S.edgeMarker_BAUGD S.scaleMarker_BIF S.heightVector_BAUGD
    S.heightMarker_BAUGD lc87EdgeTransition_contDiff
    (fun _ ht => lc87EdgeTransition_eq_zero ht) (fun _ ht => lc87EdgeTransition_eq_one ht)
    lc87EdgeTransition_mem_Icc lc87EdgeTransition_monotone cgpProfileBound_spec.1
    abs_deriv_lc87EdgeTransition_le_cgp edgeCount_BAUGP2 (fun _ => norm_blockVectorCLM_le _)
    (fun _ => norm_blockMarkerCLM_le _) (norm_blockMarkerCLM_le _) (norm_blockVectorCLM_le _)
    (norm_blockMarkerCLM_le _) hΔ1 (fun _ => S.rho_pos _) S.rho S.rho_pos
    S.edgeDomW_BAUGP2 S.edgeCoordW_BAUGP2 S.edgeCutoffW_BAUGP2
    (S.edgeCutoffW_mem_Icc_BAUGP2 hΔ) S.boundaryOriginalMap f
    (S.edgeCutoffW_eq_zero_BAUGP2 hΔ) S.edgeBlock_boundaryOriginalMap_BAUGP2
    (S.edge_count_BAUGP2 hΔ)
    (fun j p hp => S.edge_scale_comparable_BAUGP2 hΛ hΔ1 hΛΔ hV hβ1 hb j p hp) hpert' hZM
    S.edgeHeightW_BAUGP2 cgpEdgeH cgpEdgeH_mem_Icc (fun _ hs => cgpEdgeH_eq_of_le hs)
    S.scaleMarker_boundaryOriginalMap_BIF
    (fun p hp => by
      obtain ⟨i, q, -, rfl⟩ := hp
      exact S.heightBlock_boundaryOriginalMap_BAUGP2 q)
    (fun j p hp hη => S.edgeCutoffW_identity_BAUGP2 hΔ j p hp hη)
  rw [hψ]
  refine ⟨h1, h2, fun p hp => h3 p.val ?_, fun p hp => ?_, fun p t ht => ?_⟩
  · obtain ⟨j, hj, hd, hη, ht⟩ := hp
    have hj' : j ∈ S.family.edgeB.centres := hj
    let jj : S.EdgeIdx_BAUGD := ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩
    refine ⟨jj, ⟨p, hd, rfl⟩, ?_, ?_⟩
    · rw [S.norm_edgeCoordW_val_BAUGP2 jj p]
      exact hη
    · rw [S.edgeHeightW_val_BAUGP2]
      exact ht
  · obtain ⟨jj, ⟨q, hq, rfl⟩, hη, ht⟩ := h4 p hp
    refine ⟨q, rfl, jj.1, (Set.Finite.mem_toFinset _).mp jj.2, hq, ?_, ?_⟩
    · rw [← S.norm_edgeCoordW_val_BAUGP2 jj q]
      exact hη
    · rw [← S.edgeHeightW_val_BAUGP2]
      exact ht
  · obtain ⟨ha, hd⟩ := h5 p t ht
    refine ⟨ha, hd.trans (div_le_div_of_nonneg_right ?_ (S.rho_pos p).le)⟩
    exact hbcut

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
