import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryActualSlotV2

/-!
# BCG03: CFS31's source cutoff `ψ₀` of the boundary chain, bound to the actual map (lane BAUG-D)

The first component of `BoundaryGaf02Chain.cutoff_bindings` on the ACTUAL slot
(`actualSlotsV2_BAUGD`, cutoff `ψ₀ = cutoffZero_BAUGD`, CFS31's source cutoff on the circle blocks
of `H^∂`), at the actual augmented map `F_∂ = S.boundaryOriginalMap` on the WHOLE original carrier
`W` (closed twin `gaf02_stageOne_sourceCutoff`; kernel `markerLocalitySourceCutoff_row`):
smooth, `[0, 1]`-valued, exact plateau over `‖η_j‖ < 6` on `B(j, 200ρ_j)`, closed support
localizing the ORIGINAL point to an INTERIOR point with `‖η_j‖ ≤ 13/2`, and
`‖Dψ₀(F_∂ p)‖ ≤ b₀/ρ(p)` with the early constant `b₀ = cutoffZeroConst_BAUGD`.

* the circle blocks of `F_∂` on `W`: `circleCutoffW_BAUGD`, `circleCoordW_BAUGD` (zero extensions),
  `circleVector_boundaryOriginalMap_BAUGD` (`u_j(F_∂ p) = (ρ_j ζ_j(p)) η_j(p)`, `v_j(F_∂ p) = ρ_j ζ_j(p)`);
* the comparability `circle_scale_comparable_BAUGD` (`ζ_j(p) > 0 ⟹ 3ρ_j/4 ≤ ρ(p) ≤ 5ρ_j/4`, from
  `ρ` Λ-Lipschitz for `g`, T3B's consumer-ball transport, and `200Λ ≤ 1/4`);
* the multiplicity `circle_count_BAUGD` (the circle family's own `multiplicity` field, the early
  constant `circleCount_BAUGD`);
* **`cutoffZero_binding_BAUGD`** (the chain's `cutoff_bindings.1` verbatim, at `b_cut ≥ b₀`).
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

/-- The circle family's multiplicity constant (the real bound of its `multiplicity` field). -/
def circleCountReal_BAUGD : ℝ :=
  modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (3 * 2000000 + 2 / 3) /
    modelVolume (-((1 / 2000000 : ℝ) ^ 2)) 3 (1 / 3)

/-- The circle multiplicity `N₀ = ⌊…⌋₊` (early, independent of the member). -/
def circleCount_BAUGD : ℕ := ⌊circleCountReal_BAUGD⌋₊

/-- CFS31's early derivative constant of `ψ₀`: `b₀ = 10⁴ (N₀ + 1)² P₀⁴`. -/
def cutoffZeroConst_BAUGD : ℝ :=
  10 ^ 4 * ((circleCount_BAUGD : ℝ) + 1) ^ 2 * cgpProfileBound ^ 4

theorem cutoffZeroConst_nonneg_BAUGD : 0 ≤ cutoffZeroConst_BAUGD := by
  unfold cutoffZeroConst_BAUGD
  positivity

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- The circle cutoff `ζ_j` on `W` (zero extension of the family's cutoff from `W°`). -/
def circleCutoffW_BAUGD (j : S.CircleIdx_BAUGD) : W.Carrier → ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  Subtype.val.extend (S.family.circle.cutoff j.1) 0

/-- The circle coordinate `η_j` on `W` (zero extension from `W°`). -/
def circleCoordW_BAUGD (j : S.CircleIdx_BAUGD) : W.Carrier → ℝ² :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  Subtype.val.extend (S.family.circle.coord_BAUGA j.1) 0

/-- The circle chart domain `B(j, 200ρ_j)` (in `d_ĝ`) as a subset of `W`. -/
def circleDomW_BAUGD (j : S.CircleIdx_BAUGD) : Set W.Carrier :=
  letI := inducedMetricSpace S.completion.metric
  Subtype.val '' ball j.1 (200 * S.rho j.1)

theorem circleCutoffW_val_BAUGD (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.circleCutoffW_BAUGD j q.val =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       S.family.circle.cutoff j.1 q) :=
  Subtype.val_injective.extend_apply _ _ q

theorem circleCoordW_val_BAUGD (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.circleCoordW_BAUGD j q.val =
      (letI := inducedMetricSpace S.completion.metric
       letI := S.completion.complete
       S.family.circle.coord_BAUGA j.1 q) :=
  Subtype.val_injective.extend_apply _ _ q

theorem circleCutoffW_of_notMem_BAUGD (j : S.CircleIdx_BAUGD) {p : W.Carrier}
    (hp : ¬ ∃ q : W.pieceInterior ⊤, q.val = p) : S.circleCutoffW_BAUGD j p = 0 := by
  unfold circleCutoffW_BAUGD
  rw [Function.extend_apply' _ _ _ hp]
  rfl

theorem circleCoordW_of_notMem_BAUGD (j : S.CircleIdx_BAUGD) {p : W.Carrier}
    (hp : ¬ ∃ q : W.pieceInterior ⊤, q.val = p) : S.circleCoordW_BAUGD j p = 0 := by
  unfold circleCoordW_BAUGD
  rw [Function.extend_apply' _ _ _ hp]
  rfl

/-- **The circle blocks of `F_∂` on `W`**: `u_j(F_∂ p) = (ρ_j ζ_j(p)) • η_j(p)` and
`v_j(F_∂ p) = ρ_j ζ_j(p)` (both zero at boundary points). -/
theorem circleBlock_boundaryOriginalMap_BAUGD (j : S.CircleIdx_BAUGD) (p : W.Carrier) :
    S.circleVector_BAUGD j (S.boundaryOriginalMap p) =
        (S.rho j.1 * S.circleCutoffW_BAUGD j p) • S.circleCoordW_BAUGD j p ∧
      S.circleMarker_BAUGD j (S.boundaryOriginalMap p) =
        S.rho j.1 * S.circleCutoffW_BAUGD j p := by
  have hne : (.inl j : S.IntTag_BAUGA) ≠ S.scaleTag_BAUGA := by simp [scaleTag_BAUGA]
  have hslot : S.boundaryOriginalMap p (Sum.inl (.inl j)) =
      Subtype.val.extend (fun x => S.interiorMapOn_BAUGA x (.inl j)) 0 p := by
    change S.intSlotW_BAUGA (.inl j) p = _
    simp only [intSlotW_BAUGA, hne, ↓reduceIte]
  by_cases hp : ∃ q : W.pieceInterior ⊤, q.val = p
  · obtain ⟨q, rfl⟩ := hp
    rw [Subtype.val_injective.extend_apply] at hslot
    rw [S.circleCutoffW_val_BAUGD, S.circleCoordW_val_BAUGD]
    simp only [circleVector_BAUGD, circleMarker_BAUGD, blockVectorCLM_apply,
      blockMarkerCLM_apply, hslot]
    exact ⟨rfl, rfl⟩
  · rw [Function.extend_apply' _ _ _ hp] at hslot
    rw [S.circleCutoffW_of_notMem_BAUGD j hp, S.circleCoordW_of_notMem_BAUGD j hp]
    simp only [circleVector_BAUGD, circleMarker_BAUGD, blockVectorCLM_apply,
      blockMarkerCLM_apply, hslot, Pi.zero_apply, mul_zero, zero_smul]
    exact ⟨rfl, rfl⟩

/-- The circle cutoff vanishes off its chart domain. -/
theorem circleCutoffW_eq_zero_BAUGD (j : S.CircleIdx_BAUGD) (p : W.Carrier)
    (hp : p ∉ S.circleDomW_BAUGD j) : S.circleCutoffW_BAUGD j p = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  by_cases hq : ∃ q : W.pieceInterior ⊤, q.val = p
  · obtain ⟨q, rfl⟩ := hq
    rw [S.circleCutoffW_val_BAUGD]
    by_contra h
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    exact hp ⟨q, S.family.circle.tsupport_subset_ball j.1 hj (subset_tsupport _ h), rfl⟩
  · exact S.circleCutoffW_of_notMem_BAUGD j hq

/-- The plateau: on the chart domain, `‖η_j‖ < 6 ⟹ ζ_j = 1`. -/
theorem circleCutoffW_eq_one_BAUGD (j : S.CircleIdx_BAUGD) (p : W.Carrier)
    (hp : p ∈ S.circleDomW_BAUGD j) (hη : ‖S.circleCoordW_BAUGD j p‖ < 6) :
    S.circleCutoffW_BAUGD j p = 1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨q, hq, rfl⟩ := hp
  rw [S.circleCoordW_val_BAUGD] at hη
  rw [S.circleCutoffW_val_BAUGD]
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hd := inv_mul_dist_lt_of_mem_ball_LC87 (X := W.pieceInterior ⊤)
    (ρ := fun x : W.pieceInterior ⊤ => S.rho x) (S.rho_pos j.1) hq
  have hη' := hη
  simp only [CircleFamilyOn.coord_BAUGA, hj, ↓reduceDIte] at hη'
  exact S.family.circle.cutoff_eq_one j.1 hj q hd (hη'.le.trans (by norm_num))

/-- **Comparability on the circle supports**: `ζ_j(p) > 0 ⟹ 3ρ_j/4 ≤ ρ(p) ≤ 5ρ_j/4` (`ρ` is
`Λ`-Lipschitz for `g`; T3B's consumer-ball transport identifies `d_g` with `d_ĝ` on `B(j, K₀ρ_j)`;
`200Λ ≤ 1/4` from the Λ–Δ clause). -/
theorem circle_scale_comparable_BAUGD (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (j : S.CircleIdx_BAUGD) (p : W.Carrier) (hpos : 0 < S.circleCutoffW_BAUGD j p) :
    3 / 4 * S.rho j.1 ≤ S.rho p ∧ S.rho p ≤ 5 / 4 * S.rho j.1 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hΔ : 0 < Δ := by linarith
  by_cases hq : ∃ q : W.pieceInterior ⊤, q.val = p
  swap
  · rw [S.circleCutoffW_of_notMem_BAUGD j hq] at hpos
    exact absurd hpos (lt_irrefl 0)
  obtain ⟨q, rfl⟩ := hq
  rw [S.circleCutoffW_val_BAUGD] at hpos
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  have hqb : q ∈ ball j.1 (200 * S.rho j.1) :=
    S.family.circle.tsupport_subset_ball j.1 hj (subset_tsupport _ hpos.ne')
  have hj1 : ENNReal.ofReal 10 < distanceToBoundary W g j.1 :=
    (S.family.circle.centres_subset hj).1
  have htr := (S.transport_spec.2.1 j.1 hj1).2
  have hK0 := consumerConstant_ge_BAUGA hΔ hV hβ1 hb
  have hrj := S.rho_pos j.1
  have hqK : q ∈ ball j.1 ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * S.rho j.1) :=
    ball_subset_ball (by nlinarith) hqb
  have hjK : j.1 ∈ ball j.1 ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * S.rho j.1) :=
    mem_ball_self (mul_pos (by nlinarith) hrj)
  have hdist : riemannianEDistOf g q.val j.1.val = edist q j.1 := htr q hqK j.1 hjK
  have hedist : edist q j.1 < ENNReal.ofReal (200 * S.rho j.1) :=
    edist_lt_ofReal.mpr (mem_ball.mp hqb)
  have hlip := S.scale_spec.2.1 q.val j.1.val
  have h1 : ENNReal.ofReal |S.rho q.val - S.rho j.1.val| ≤
      ENNReal.ofReal (Λ * (200 * S.rho j.1)) := by
    refine hlip.trans ?_
    rw [hdist, ENNReal.ofReal_mul hΛ]
    exact mul_le_mul_right hedist.le _
  have h2 : |S.rho q.val - S.rho j.1.val| ≤ Λ * (200 * S.rho j.1) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have hΛ' : 200 * Λ ≤ 1 / 4 := by nlinarith
  have h3 : Λ * (200 * S.rho j.1) ≤ 1 / 4 * S.rho j.1 := by nlinarith
  have h4 := abs_le.mp (h2.trans h3)
  constructor <;> linarith [h4.1, h4.2]

/-- **The circle multiplicity**: at every point of `W` at most `N₀` circle cutoffs are positive. -/
theorem circle_count_BAUGD (p : W.Carrier) :
    (Finset.univ.filter fun j : S.CircleIdx_BAUGD => 0 < S.circleCutoffW_BAUGD j p).card ≤
      circleCount_BAUGD := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  by_cases hq : ∃ q : W.pieceInterior ⊤, q.val = p
  swap
  · have h0 : (Finset.univ.filter fun j : S.CircleIdx_BAUGD => 0 < S.circleCutoffW_BAUGD j p) =
        ∅ := by
      refine Finset.filter_false_of_mem fun j _ => ?_
      rw [S.circleCutoffW_of_notMem_BAUGD j hq]
      exact lt_irrefl 0
    rw [h0, Finset.card_empty]
    exact Nat.zero_le _
  obtain ⟨q, rfl⟩ := hq
  have hM := S.family.circle.multiplicity q
  set A : Set (W.pieceInterior ⊤) :=
    S.family.circle.centres ∩ {j | q ∈ tsupport (S.family.circle.cutoff j)} with hA
  let F := Finset.univ.filter fun j : S.CircleIdx_BAUGD => 0 < S.circleCutoffW_BAUGD j q.val
  have hsub : ((F.map ⟨fun j : S.CircleIdx_BAUGD => j.1, Subtype.val_injective⟩ :
      Finset (W.pieceInterior ⊤)) : Set (W.pieceInterior ⊤)) ⊆ A := by
    intro x hx
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image,
      Finset.mem_coe] at hx
    obtain ⟨j, hjF, rfl⟩ := hx
    have hpos : 0 < S.circleCutoffW_BAUGD j q.val := (Finset.mem_filter.mp hjF).2
    rw [S.circleCutoffW_val_BAUGD] at hpos
    exact ⟨(Set.Finite.mem_toFinset _).mp j.2, subset_tsupport _ hpos.ne'⟩
  have hfin : A.Finite := S.family.circle.finite_centres.subset Set.inter_subset_left
  have hcard : (F.card : ℝ) ≤ A.ncard := by
    have := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset, Finset.card_map] at this
    exact_mod_cast this
  exact Nat.le_floor (hcard.trans hM)

/-- The circle reference coordinate `circleEta_BIF` is the circle block coordinate on `W°`. -/
theorem circleEta_eq_circleCoordW_BAUGD (j : S.CircleIdx_BAUGD) (q : W.pieceInterior ⊤) :
    S.circleEta_BIF j.1 q = S.circleCoordW_BAUGD j q.val := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hj := (Set.Finite.mem_toFinset _).mp j.2
  rw [S.circleCoordW_val_BAUGD]
  simp only [circleEta_BIF, CircleFamilyOn.coord_BAUGA, hj, ↓reduceDIte]

end BoundarySupplyCore

namespace BoundarySupply

variable (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
  θ W g δn n B oM)

/-- **`ψ₀` bound to the actual map** (the first component of `BoundaryGaf02Chain.cutoff_bindings`
on the actual slot, with the early constant `b₀ = cutoffZeroConst_BAUGD`). -/
theorem cutoffZero_binding_BAUGD (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) :
    letI := inducedMetricSpace S.completion.metric
    ContDiff ℝ ∞ ((actualSlotsV2_BAUGD S).cutoff 0) ∧
      (∀ z, (actualSlotsV2_BAUGD S).cutoff 0 z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p : W.pieceInterior ⊤, (∃ j ∈ S.stageCentres_BIF 0, dist p j < 200 * S.rho j ∧
          ‖S.circleEta_BIF j p‖ < 6) →
        (actualSlotsV2_BAUGD S).cutoff 0 (S.boundaryOriginalMap p.val) = 1) ∧
      (∀ p : W.Carrier,
        S.boundaryOriginalMap p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 0) →
        ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 0,
          dist q j < 200 * S.rho j ∧ ‖S.circleEta_BIF j q‖ ≤ 13 / 2) ∧
      ∀ p : W.Carrier, ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 0) (S.boundaryOriginalMap p)‖ ≤
        cutoffZeroConst_BAUGD / S.rho p := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hu : ∀ j, ‖S.circleVector_BAUGD j‖ ≤ 1 := fun _ => norm_blockVectorCLM_le _
  have hv : ∀ j, ‖S.circleMarker_BAUGD j‖ ≤ 1 := fun _ => norm_blockMarkerCLM_le _
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := markerLocalitySourceCutoff_row lc87EdgeTransition_contDiff
    (fun _ ht => lc87EdgeTransition_eq_zero ht) (fun _ ht => lc87EdgeTransition_eq_one ht)
    lc87EdgeTransition_mem_Icc cgpProfileBound_spec.1 abs_deriv_lc87EdgeTransition_le_cgp
    circleCount_BAUGD S.circleVector_BAUGD S.circleMarker_BAUGD hu hv
    (fun j : S.CircleIdx_BAUGD => S.rho j.1) (fun j => S.rho_pos _) S.rho S.rho_pos
    S.circleDomW_BAUGD S.circleCoordW_BAUGD S.circleCutoffW_BAUGD S.boundaryOriginalMap
    S.circleCutoffW_eq_zero_BAUGD (fun j p => S.circleBlock_boundaryOriginalMap_BAUGD j p)
    S.circle_count_BAUGD
    (fun j p hp => S.circle_scale_comparable_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb j p hp)
    S.circleCutoffW_eq_one_BAUGD
  refine ⟨h1, h2, fun p hp => ?_, fun p hp => ?_, h6⟩
  · obtain ⟨j, hj, hd, hη⟩ := hp
    have hj' : j ∈ S.family.circle.centres := hj
    let jj : S.CircleIdx_BAUGD := ⟨j, (Set.Finite.mem_toFinset _).mpr hj'⟩
    refine h3 p.val ⟨jj, ⟨p, hd, rfl⟩, ?_⟩
    rw [← S.circleEta_eq_circleCoordW_BAUGD jj p]
    exact hη
  · obtain ⟨jj, ⟨q, hq, rfl⟩, hη⟩ := h4 p hp
    refine ⟨q, rfl, jj.1, (Set.Finite.mem_toFinset _).mp jj.2, hq, ?_⟩
    rw [S.circleEta_eq_circleCoordW_BAUGD jj q]
    exact hη

/-- **Consumer: the chain's `cutoff_bindings.1` on the actual slot** at every `b_cut ≥ b₀`
(verbatim the first conjunct of `BoundaryGaf02Chain.cutoff_bindings` with `Φ = actualSlotsV2_BAUGD S`). -/
theorem cutoffZero_binding_of_le_BAUGD (hΛ : 0 ≤ Λ) (hΔ1 : 1 ≤ Δ)
    (hΛΔ : 1000000 * Δ * Λ < 1 / 100000) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) {bcut : ℝ}
    (hbcut : cutoffZeroConst_BAUGD ≤ bcut) :
    letI := inducedMetricSpace S.completion.metric
    ContDiff ℝ ∞ ((actualSlotsV2_BAUGD S).cutoff 0) ∧
      (∀ z, (actualSlotsV2_BAUGD S).cutoff 0 z ∈ Icc (0 : ℝ) 1) ∧
      (∀ p : W.pieceInterior ⊤, (∃ j ∈ S.stageCentres_BIF 0, dist p j < 200 * S.rho j ∧
          ‖S.circleEta_BIF j p‖ < 6) →
        (actualSlotsV2_BAUGD S).cutoff 0 (S.boundaryOriginalMap p.val) = 1) ∧
      (∀ p : W.Carrier,
        S.boundaryOriginalMap p ∈ tsupport ((actualSlotsV2_BAUGD S).cutoff 0) →
        ∃ q : W.pieceInterior ⊤, q.val = p ∧ ∃ j ∈ S.stageCentres_BIF 0,
          dist q j < 200 * S.rho j ∧ ‖S.circleEta_BIF j q‖ ≤ 13 / 2) ∧
      ∀ p : W.Carrier, ‖fderiv ℝ ((actualSlotsV2_BAUGD S).cutoff 0) (S.boundaryOriginalMap p)‖ ≤
        bcut / S.rho p := by
  have h := S.cutoffZero_binding_BAUGD hΛ hΔ1 hΛΔ hV hβ1 hb
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun p => (h.2.2.2.2 p).trans ?_⟩
  exact div_le_div_of_nonneg_right hbcut (S.rho_pos p).le

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
