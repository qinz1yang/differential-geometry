import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementClosedBCF2K
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedInterior

/-!
# Consumer: closedness of the edge piece for `E = F_∂` (`boundaryOriginalMap`)

The closedness kernel `LocalPacketsOnBFRZ.bcf02_isClosed_edgePiece_BCF2K` applied to the ACTUAL
augmented map of a stored boundary supply `S : BoundarySupplyCore` (BAUG-A's D61-4 public name
`boundaryOriginalMap`, family `S.family`, scale `S.rho`, completion `S.completion`, BCP04.a from
`S.scale_spec`), with `π₂ = id`:
* the `edgeB` block entries of `F_∂` (`edgeBlockU_BCF2K`, `edgeBlockV_BCF2K`) are exactly
  `(ρ_j η_jζ_j, ρ_jζ_j)` (`edgeBlock_boundaryOriginalMap_BCF2K`), so (ERR) holds with any `c₃ > 0`,
  (FM) holds by FC27's plateau, (AM0) because the marker vanishes with the cutoff;
* the height of the SAME map: `s = ℓ_ρ(F_∂)` (scale slot) and `A = u_{E'}(F_∂)` (`E'` slot),
  `T = A/s` (`heightT_BCF2K`); (EZ) at the marker points of `V = {T ≤ 4Δ}` is proved through the
  scalar `bcf02_height_EZ_BCF2K` with `κ = z_{E'} = 1` there (the `edgeB` cutoff `ζ_i = 1` forces
  the height profile and the cutoff-sum ramp to be one) — `s` is the map's own scale slot;
* `BoundarySupplyCore.bcf02_isClosed_edgePiece_original_BCF2K`: for every closed `M₂` with the
  original-coordinate consequences of `M₂`, the edge piece
  `P_e = M₂ ∩ V ∩ ⋃_i {v_i(F_∂) = ρ_i, |u_i(F_∂)| < 4Δρ_i}` (strict, an OPEN base condition) is
  closed, and compact when `M₂` is.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal NNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
open DifferentialGeometry.Analysis DifferentialGeometry

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- `1 − χ_{8,9} = edgeHeightProfile` (the same transition profile). -/
theorem one_sub_cfsRamp_eq_edgeHeightProfile_BCF2K (u : ℝ) :
    1 - cfsRamp lc87EdgeTransition 8 9 u = edgeHeightProfile u := by
  unfold cfsRamp lc87EdgeTransition edgeHeightProfile descendingIntervalProfile
  ring

namespace BoundarySupplyCore

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    W g δn n B oM)

open Classical in
/-- The tangential entry `u_j` of the `edgeB` block of `j` in the target of `F_∂` (zero off the
revised edge centres). -/
def edgeBlockU_BCF2K (j : W.pieceInterior ⊤)
    (y : BlockSpace (fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)) : ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if hj : j ∈ S.family.edgeB.centres then
    (y (Sum.inl (Sum.inr (Sum.inr (Sum.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))))).fst 0
  else 0

open Classical in
/-- The marker entry `v_j` of the `edgeB` block of `j` in the target of `F_∂` (zero off the revised
edge centres). -/
def edgeBlockV_BCF2K (j : W.pieceInterior ⊤)
    (y : BlockSpace (fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)) : ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  if hj : j ∈ S.family.edgeB.centres then
    (y (Sum.inl (Sum.inr (Sum.inr (Sum.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩))))).snd
  else 0

/-- The height of `F_∂` itself: `T = u_{E'}(F_∂)/ℓ_ρ(F_∂)` (the `E'` slot's tangential entry over
the scale slot's marker). -/
def heightT_BCF2K (x : W.pieceInterior ⊤) : ℝ :=
  (S.boundaryOriginalMap x.val (Sum.inl S.edgeTag_BAUGA)).fst 0 /
    (S.boundaryOriginalMap x.val (Sum.inl S.scaleTag_BAUGA)).snd

/-- The vertical cut `V = {T ≤ 4Δ}` of `F_∂`. -/
def heightSet_BCF2K : Set (W.pieceInterior ⊤) :=
  {x | S.heightT_BCF2K x ≤ 4 * Δ}

/-- The edge piece of `F_∂` inside `M₂`: `M₂ ∩ V ∩ ⋃_i {v_i(F_∂) = ρ_i, |u_i(F_∂)| < 4Δρ_i}`. -/
def edgePieceOriginal_BCF2K (M₂ : Set (W.pieceInterior ⊤)) : Set (W.pieceInterior ⊤) :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  {x | x ∈ M₂ ∧ x ∈ S.heightSet_BCF2K ∧ ∃ i ∈ S.family.edgeB.centres,
    S.edgeBlockV_BCF2K i (S.boundaryOriginalMap x.val) = S.rho i ∧
      |S.edgeBlockU_BCF2K i (S.boundaryOriginalMap x.val)| < 4 * Δ * S.rho i}

/-- **The `edgeB` block of `F_∂`**: at an interior point `x` and a revised edge centre `j`, the
block entries of the augmented map are `u_j = ρ_j η_j ζ_j` and `v_j = ρ_j ζ_j`. -/
theorem edgeBlock_boundaryOriginalMap_BCF2K (x : W.pieceInterior ⊤) (j : W.pieceInterior ⊤) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    j ∈ S.family.edgeB.centres →
      S.edgeBlockU_BCF2K j (S.boundaryOriginalMap x.val) =
        S.rho j * (S.family.edgeB.coord_BAUGA j x * S.family.edgeB.cutoff_BAUGA j x) ∧
      S.edgeBlockV_BCF2K j (S.boundaryOriginalMap x.val) =
        S.rho j * S.family.edgeB.cutoff_BAUGA j x := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro hj
  have hslot : ∀ t : S.IntTag_BAUGA,
      S.boundaryOriginalMap x.val (Sum.inl t) = S.interiorMapOn_BAUGA x t := by
    intro t
    change S.interiorMapW_BAUGA x.val t = _
    rw [S.interiorMapW_val_BAUGA x]
  constructor
  · unfold edgeBlockU_BCF2K
    rw [dite_eq_left hj, hslot]
    change ((S.rho j * S.family.edgeB.cutoff_BAUGA j x) •
      planeAxis (S.family.edgeB.coord_BAUGA j x)) 0 = _
    simp [planeAxis_apply]
    ring
  · unfold edgeBlockV_BCF2K
    rw [dite_eq_left hj, hslot]
    rfl

/-- **The height of `F_∂`**: `ℓ_ρ(F_∂) = ρ` (the scale slot `(0, ρ)`) and
`u_{E'}(F_∂) = ρ t_B z_{E'}`, so `T = t_B z_{E'}`. -/
theorem heightT_eq_BCF2K (x : W.pieceInterior ⊤) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    (S.boundaryOriginalMap x.val (Sum.inl S.scaleTag_BAUGA)).snd = S.rho x ∧
      (S.boundaryOriginalMap x.val (Sum.inl S.edgeTag_BAUGA)).fst 0 =
        S.rho x * S.family.edgeBMarker_BAUGA x * S.family.edgeBHeight_BAUGA x := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  constructor
  · change (S.interiorMapW_BAUGA x.val S.scaleTag_BAUGA).snd = _
    rw [S.interiorMapW_val_BAUGA x]
    change S.rho x * 1 = S.rho x
    rw [mul_one]
  · rw [S.boundaryOriginalMap_edgePrime_formula x]
    change ((S.rho x * S.family.edgeBMarker_BAUGA x) •
      planeAxis (S.family.edgeBHeight_BAUGA x)) 0 = _
    simp [planeAxis_apply]

/-- **(EZ) for `F_∂` at the marker points of `V = {T ≤ 4Δ}`**: if the `edgeB` block of a revised
centre `i` has marker `v_i(F_∂ x) = ρ_i` at `x ∈ V`, then `t_B(x) < 4.01Δ`. (`ζ_i(x) = 1`, so the
height profile and the cutoff-sum ramp are one; for `t_B ≥ .3Δ` the `E'` marker is `z_{E'} = 1`
and `T = t_B` with the map's own scale slot `s = ρ`; the scalar `bcf02_height_EZ_BCF2K` closes.) -/
theorem heightEZ_original_BCF2K (hΔ : 1 ≤ Δ) (x i : W.pieceInterior ⊤) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    i ∈ S.family.edgeB.centres → x ∈ S.heightSet_BCF2K →
      S.edgeBlockV_BCF2K i (S.boundaryOriginalMap x.val) = S.rho i →
      S.family.edgeB.smoothing x / S.rho x < 401 / 100 * Δ := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro hi hxV hv
  have hΔ0 : 0 < Δ := by linarith
  have hri := S.rho_pos i
  have hrx := S.rho_pos x
  rw [(S.edgeBlock_boundaryOriginalMap_BCF2K x i hi).2] at hv
  have hζ : S.family.edgeB.cutoff_BAUGA i x = 1 := by
    have h0 : S.rho i * (S.family.edgeB.cutoff_BAUGA i x - 1) = 0 := by
      rw [mul_sub, mul_one, hv, sub_self]
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hri.ne'
    · linarith
  set t := S.family.edgeB.smoothing x / S.rho x with htdef
  by_cases ht : 3 / 10 * Δ ≤ t
  · have hne : S.family.edgeB.cutoff_BAUGA i x ≠ 0 := by rw [hζ]; norm_num
    obtain ⟨-, hball, -, -⟩ := S.family.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ0 hne
    have hxB : x ∈ ball i (100 * Δ * S.rho i) := by
      have h := (inv_mul_lt_iff₀ hri).mp hball
      rw [mem_ball]
      linarith
    have hform := S.family.edgeB.cutoff_eq_formula_BAUGA hi hxB
    rw [hζ] at hform
    have hcp := intervalPlateauProfile_mem_Icc (-9) (-8) 8 9
      (S.family.edgeB.coord_BAUGA i x / Δ)
    have hhp := descendingIntervalProfile_mem_Icc 8 9 (S.family.edgeB.smoothing x / S.rho x / Δ)
    have hform' : 1 = intervalPlateauProfile (-9) (-8) 8 9 (S.family.edgeB.coord_BAUGA i x / Δ) *
        descendingIntervalProfile 8 9 (S.family.edgeB.smoothing x / S.rho x / Δ) := hform
    have hhp1 : edgeHeightProfile (t / Δ) = 1 := by
      change descendingIntervalProfile 8 9 (S.family.edgeB.smoothing x / S.rho x / Δ) = 1
      apply le_antisymm hhp.2
      nlinarith [hcp.1, hcp.2, hhp.1, hhp.2]
    have h89 : 1 - cfsRamp lc87EdgeTransition 8 9 (t / Δ) = 1 := by
      rw [one_sub_cfsRamp_eq_edgeHeightProfile_BCF2K, hhp1]
    have h13 : cfsRamp lc87EdgeTransition (1 / 5) (3 / 10) (t / Δ) = 1 :=
      cfsRamp_eq_one (fun y hy => lc87EdgeTransition_eq_one hy) (by norm_num)
        (by rw [le_div_iff₀ hΔ0]; linarith)
    have hsum : 1 ≤ S.family.edgeBSum_BAUGA x := by
      unfold LocalPacketsOnB.edgeBSum_BAUGA
      have hmem : i ∈ S.family.edgeB.finite_centres.toFinset := (Set.Finite.mem_toFinset _).mpr hi
      have h := Finset.single_le_sum
        (f := fun j : S.family.edgeB.finite_centres.toFinset => S.family.edgeB.cutoff_BAUGA j x)
        (fun j _ => (S.family.edgeB.cutoff_mem_Icc_BAUGA hΔ0 j x).1)
        (Finset.mem_univ (⟨i, hmem⟩ : S.family.edgeB.finite_centres.toFinset))
      have hi1 : S.family.edgeB.cutoff_BAUGA (⟨i, hmem⟩ : S.family.edgeB.finite_centres.toFinset).1
          x = 1 := hζ
      simp only at h
      linarith
    have hramp : cfsRamp lc87EdgeTransition (1 / 2) 1 (S.family.edgeBSum_BAUGA x) = 1 :=
      cfsRamp_eq_one (fun y hy => lc87EdgeTransition_eq_one hy) (by norm_num) hsum
    have hz : S.family.edgeBMarker_BAUGA x = 1 := by
      unfold LocalPacketsOnB.edgeBMarker_BAUGA cgpEdgeH
      change cfsRamp lc87EdgeTransition (1 / 5) (3 / 10) (t / Δ) *
          (1 - cfsRamp lc87EdgeTransition 8 9 (t / Δ)) *
        cfsRamp lc87EdgeTransition (1 / 2) 1 (S.family.edgeBSum_BAUGA x) = 1
      rw [h13, h89, hramp]
      norm_num
    obtain ⟨hs, hA⟩ := S.heightT_eq_BCF2K x
    have hT : S.heightT_BCF2K x ≤ 4 * Δ := hxV
    unfold heightT_BCF2K at hT
    rw [hs, hA, hz] at hT
    have hTt : S.rho x * 1 * S.family.edgeBHeight_BAUGA x / S.rho x ≤ 4 * Δ := hT
    have hht : S.family.edgeBHeight_BAUGA x = t := rfl
    rw [hht] at hTt
    refine bcf02_height_EZ_BCF2K (ρx := S.rho x) (s := S.rho x) (A := S.rho x * 1 * t)
      (κ := 1) (c₃ := 1 / 1000) (β := 1 / 1000) hΔ hrx hrx (by nlinarith) ?_ (by linarith)
      (by norm_num) (by norm_num) (by norm_num) hTt
    have h0 : S.rho x * 1 * t - S.rho x * t * 1 = 0 := by ring
    rw [h0, abs_zero]
    positivity
  · push Not at ht
    linarith

/-- **The block functions and the height of `F_∂` are continuous** on `W°` (BAUG-A's
`boundaryOriginalMap_smooth`, then the coordinate projections). -/
theorem continuous_edgeBlock_BCF2K (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    Continuous S.heightT_BCF2K ∧ ∀ j ∈ S.family.edgeB.centres,
      Continuous (fun x : W.pieceInterior ⊤ =>
        S.edgeBlockV_BCF2K j (S.boundaryOriginalMap x.val)) ∧
      Continuous (fun x : W.pieceInterior ⊤ =>
        S.edgeBlockU_BCF2K j (S.boundaryOriginalMap x.val)) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  have hFc : Continuous fun x : W.pieceInterior ⊤ => S.boundaryOriginalMap x.val :=
    (S.boundaryOriginalMap_smooth hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he).continuous.comp
      continuous_subtype_val
  have hslot : ∀ t, Continuous fun x : W.pieceInterior ⊤ => S.boundaryOriginalMap x.val t :=
    fun t => (PiLp.continuous_apply 2 _ t).comp hFc
  refine ⟨?_, fun j hj => ?_⟩
  · have h1 : Continuous fun x : W.pieceInterior ⊤ =>
        (S.boundaryOriginalMap x.val (Sum.inl S.edgeTag_BAUGA)).fst 0 :=
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
        ((WithLp.continuous_fst (p := 2) (α := ℝ²) (β := ℝ)).comp (hslot _))
    have h2 : Continuous fun x : W.pieceInterior ⊤ =>
        (S.boundaryOriginalMap x.val (Sum.inl S.scaleTag_BAUGA)).snd :=
      (WithLp.continuous_snd (p := 2) (α := ℝ²) (β := ℝ)).comp (hslot _)
    exact h1.div h2 fun x => by
      rw [(S.heightT_eq_BCF2K x).1]
      exact (S.rho_pos x).ne'
  let tj : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count :=
    Sum.inl (Sum.inr (Sum.inr (Sum.inl ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩)))
  have hV' : (fun x : W.pieceInterior ⊤ => S.edgeBlockV_BCF2K j (S.boundaryOriginalMap x.val)) =
      fun x => (S.boundaryOriginalMap x.val tj).snd := by
    funext x
    unfold edgeBlockV_BCF2K
    rw [dite_eq_left hj]
  have hU' : (fun x : W.pieceInterior ⊤ => S.edgeBlockU_BCF2K j (S.boundaryOriginalMap x.val)) =
      fun x => (S.boundaryOriginalMap x.val tj).fst 0 := by
    funext x
    unfold edgeBlockU_BCF2K
    rw [dite_eq_left hj]
  refine ⟨?_, ?_⟩
  · rw [hV']
    exact (WithLp.continuous_snd (p := 2) (α := ℝ²) (β := ℝ)).comp (hslot tj)
  · rw [hU']
    exact (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).comp
      ((WithLp.continuous_fst (p := 2) (α := ℝ²) (β := ℝ)).comp (hslot tj))

end BoundarySupplyCore

/-- **BCF02, step five, for `E = F_∂`** (consumer of
`LocalPacketsOnBFRZ.bcf02_isClosed_edgePiece_BCF2K`): for `Δ ≥ 2`, EGP04's early constants `σ, η`
exist such that for every stored boundary supply `S` with the step-one–three bounds, BAUG-A's
smoothness bounds and EGP04's tail requests, and every closed `M₂ ⊆ W°` with `M₂`'s
original-coordinate consequences (`D ≥ 35`, outside the `.38`-zero balls and the slim regions),
the edge piece of the augmented map `F_∂ = boundaryOriginalMap`,
`M₂ ∩ {T ≤ 4Δ} ∩ ⋃_i {v_i(F_∂) = ρ_i, |u_i(F_∂)| < 4Δρ_i}` (strict, open base condition), is
closed in `(W°, d_ĝ)`, and compact when `M₂` is. -/
theorem BoundarySupplyCore.bcf02_isClosed_edgePiece_original_BCF2K {Δ : ℝ} (hΔ : 2 ≤ Δ) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ ∃ η : ℝ, 0 < η ∧
    ∀ {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
      {βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
      {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]
      {g : SmoothRiemannianMetric W.model W.Carrier} {δn : ℝ} {n : ℕ}
      {B : NearlyCuspidalBoundary W g K δn}
      {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
      (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz W g δn n B oM),
      0 ≤ Λ → μ ≤ 1 / 10 ^ 8 → τ ≤ 1 / 10 ^ 8 → σc ≤ 1 / 1000 → 1140 * Δ ≤ 35 * (n : ℝ) →
      1000 * Δ ≤ T → 0 ≤ σs → σs ≤ 1 / 100 → 0 < b → b < 1 / 1000000 → s < 1 / 1000000 →
      β 2 < 1 / 1000000 → 0 ≤ V → 0 < β 1 → e ≤ 1 / 10 →
      σ⁻¹ ≤ Lmax → b ≤ η → 3 * b ≤ σ → b * (2 * (20 * Δ + 1)) ≤ 1 →
      1000000 * Δ * Λ < 1 / 100000 → μ * Δ < 1 / 10000 →
      letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      ∀ M₂ : Set (W.pieceInterior ⊤), IsClosed M₂ →
        (∀ q ∈ M₂, ENNReal.ofReal 35 ≤ distanceToBoundary W g q ∧
          (letI := S.family.instMetricN; letI := S.family.instChartedN
            letI := S.family.instMetricC
            ∀ z (hz : z ∈ S.family.zero.centres),
              38 / 100 * (S.family.zero.zero z hz).radius ≤ dist q z) ∧
          (∀ k (hk : k ∈ S.family.slim.centres), dist q k < 9 * Δ * S.rho k →
            10 * Δ ≤ |(S.family.slim.centre k hk).coord_BCG2 q|)) →
        IsClosed (S.edgePieceOriginal_BCF2K M₂) ∧
          (IsCompact M₂ → IsCompact (S.edgePieceOriginal_BCF2K M₂)) := by
  obtain ⟨σ, hσ, hσ1, η, hη, hK⟩ := LocalPacketsOnBFRZ.bcf02_isClosed_edgePiece_BCF2K hΔ
  refine ⟨σ, hσ, hσ1, η, hη, ?_⟩
  intro K A β βd εN Λ w σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz W _ g δn n B oM S
    hΛ hμ hτ hσc hn hT hσs hσs1 hb0 hb hs hβ2 hV hβ1 he hσL hbη h3b hbH hLΛ hμΔ
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro M₂ hM hM₂
  have hΔ0 : 0 < Δ := by linarith
  have hΔΛ : 100 * Δ * Λ ≤ 1 / 100 := by nlinarith
  obtain ⟨hTc, hc⟩ :=
    S.continuous_edgeBlock_BCF2K hΛ hΔ0 (by linarith) (by linarith) hΔΛ hV hβ1 hb0 he
  have hVc : IsClosed S.heightSet_BCF2K := isClosed_le hTc continuous_const
  have hblock := fun x j hj => S.edgeBlock_boundaryOriginalMap_BCF2K x j hj
  have hres := hK W g S.completion.metric S.completion.inner_le S.rho S.rho_pos
    S.scale_spec.2.2.2.2 (c₃ := 1 / 1000) hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 (by norm_num)
    hσL hbη h3b hbH hLΛ hμΔ oM S.family (fun x => S.boundaryOriginalMap x.val) id
    S.edgeBlockU_BCF2K S.edgeBlockV_BCF2K
    (fun j hj x => by
      change |S.edgeBlockU_BCF2K j (S.boundaryOriginalMap x.val) - _| < _
      rw [(hblock x j hj).1, sub_self, abs_zero]
      have := S.rho_pos x
      positivity)
    (fun j hj x => by
      change |S.edgeBlockV_BCF2K j (S.boundaryOriginalMap x.val) - _| < _
      rw [(hblock x j hj).2, sub_self, abs_zero]
      have := S.rho_pos x
      positivity)
    (fun j hj x hx hη ht => by
      change S.edgeBlockV_BCF2K j (S.boundaryOriginalMap x.val) = _
      rw [(hblock x j hj).2, S.family.edgeB.cutoff_eq_one_of_le_BCF2K hΔ0 hj (mem_ball.mpr hx)
        (by linarith) (by linarith), mul_one])
    (fun j hj x h0 => by
      change |S.edgeBlockV_BCF2K j (S.boundaryOriginalMap x.val)| ≤ _
      rw [(hblock x j hj).2, h0, mul_zero, abs_zero]
      have := S.rho_pos j
      positivity)
    M₂ S.heightSet_BCF2K (S.edgePieceOriginal_BCF2K M₂) hM hVc
    (fun j hj => ((hc j hj).1).continuousOn) (fun j hj => ((hc j hj).2).continuousOn) hM₂
    (fun x hxV i hi hvi _ => S.heightEZ_original_BCF2K (by linarith) x i hi hxV hvi)
    (fun x hx => hx)
    (fun x hx hxV ⟨j, hj, hvj, huj⟩ => ⟨hx, hxV, j, hj, hvj, by
      have := S.rho_pos j
      change |S.edgeBlockU_BCF2K j (S.boundaryOriginalMap x.val)| < 4 * Δ * S.rho j
      change |S.edgeBlockU_BCF2K j (S.boundaryOriginalMap x.val)| < 3 * Δ * S.rho j at huj
      nlinarith⟩)
  exact ⟨hres.2.1, hres.2.2⟩

end DifferentialGeometry.Geometry.Collapse
