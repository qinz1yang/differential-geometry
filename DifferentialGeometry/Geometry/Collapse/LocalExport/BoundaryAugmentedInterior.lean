import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedInteriorKernels
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundarySupply

/-!
# BCG03: the interior layer `F_int^W` and the augmented map `F_∂` of a `BoundarySupply` (BAUG-A, G3)

Draft 61 §2.1–§2.3, disposition D61-4. The interior part of the augmented map is the SAME active
family's formula (FC01's block map), on the stored family of `S : BoundarySupplyCore`, extended
block by block from `W°` to the original carrier `W`:

* tags `IntTag_BAUGA` = circle ⊕ slim ⊕ `edgeB` ⊕ zero centres ⊕ {scale, `E'`}
  (`scaleTag_BAUGA`, `edgeTag_BAUGA`); radii `ρ(j)` / zero radii / `ρ`; cutoffs = the actual
  circle cutoffs, the actual slim cutoffs (`cutoff_BCNT`), the actual `edgeB` cutoffs
  (`cutoff_BAUGA`), LC31's annular cutoffs `Φ ∘ radial`, `1`, `z_{E'}` (`edgeBMarker_BAUGA`);
  coordinates = circle chart coordinate, `planeAxis ∘ coord_BCG2`, `planeAxis ∘ coord_BAUGA`,
  `planeAxis ∘ radial`, `0`, `planeAxis ∘ t_B` (the `cgpGlobalMap` pattern on the ACTIVE family:
  `edgeB`, never the inherited `edge`; no `CompactSpace`, no closed-family parameter);
* `interiorMapOn_BAUGA` (the formula on `W°`), `interiorMapW_BAUGA` (`F_int^W`: the scale slot is
  `(0, ρ)` with the ORIGINAL `ρ` on `W` — no zero extension of the scale block — and every other
  slot is the zero extension of the `W°` slot), `interiorMapW_val_BAUGA` (`F_int^W = ` the
  formula on `W°`);
* `boundaryOriginalMap` (`F_∂ = boundaryOriginalMap_BAUGA P F_int^W`, the packet's actual collar
  blocks) with the public names of D61-4: `boundaryOriginalMap_interior_projection`,
  `boundaryOriginalMap_boundary_block`,
  `boundaryOriginalMap_eq_interior_extension_off_collar_support`,
  `boundaryOriginalMap_edgePrime_formula`, and (below, once smoothness is proved)
  `boundaryOriginalMap_smooth`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
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

namespace BoundarySupplyCore

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    W g δn n B oM)

/-- The interior tags: circle, slim, `edgeB` and zero centres of the stored family, and the two
special tags (`false` = scale, `true` = `E'`). -/
abbrev IntTag_BAUGA : Type :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  S.family.circle.finite_centres.toFinset ⊕ S.family.slim.finite_centres.toFinset ⊕
    S.family.edgeB.finite_centres.toFinset ⊕ S.family.zero.finite_centres.toFinset ⊕ Bool

/-- The tag of the scale block. -/
abbrev scaleTag_BAUGA : S.IntTag_BAUGA := .inr (.inr (.inr (.inr false)))

/-- The tag of the weak-edge block `E'`. -/
abbrev edgeTag_BAUGA : S.IntTag_BAUGA := .inr (.inr (.inr (.inr true)))

/-- The block radii `R_i` on `W°`. -/
def intRadius_BAUGA : S.IntTag_BAUGA → W.pieceInterior ⊤ → ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  fun t => match t with
  | .inl j => fun _ => S.rho j.1
  | .inr (.inl j) => fun _ => S.rho j.1
  | .inr (.inr (.inl j)) => fun _ => S.rho j.1
  | .inr (.inr (.inr (.inl i))) => fun _ =>
      (S.family.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius
  | .inr (.inr (.inr (.inr _))) => fun x => S.rho x

/-- The block cutoffs `ζ_i` on `W°` (the ACTUAL cutoffs of the stored family). -/
def intCutoff_BAUGA : S.IntTag_BAUGA → W.pieceInterior ⊤ → ℝ :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  fun t => match t with
  | .inl j => S.family.circle.cutoff j.1
  | .inr (.inl j) => S.family.slim.cutoff_BCNT j.1
  | .inr (.inr (.inl j)) => S.family.edgeB.cutoff_BAUGA j.1
  | .inr (.inr (.inr (.inl i))) => fun x => Calculus.annularCutoff Calculus.cutoffProfile
      ((S.family.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial x)
  | .inr (.inr (.inr (.inr false))) => fun _ => 1
  | .inr (.inr (.inr (.inr true))) => S.family.edgeBMarker_BAUGA

/-- The block coordinates `η_i` on `W°` (scalar coordinates on the axis of `ℝ²`). -/
def intCoord_BAUGA : S.IntTag_BAUGA → W.pieceInterior ⊤ → ℝ² :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  fun t => match t with
  | .inl j => S.family.circle.coord_BAUGA j.1
  | .inr (.inl j) => fun x =>
      planeAxis ((S.family.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 x)
  | .inr (.inr (.inl j)) => fun x => planeAxis (S.family.edgeB.coord_BAUGA j.1 x)
  | .inr (.inr (.inr (.inl i))) => fun x =>
      planeAxis ((S.family.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial x)
  | .inr (.inr (.inr (.inr false))) => fun _ => 0
  | .inr (.inr (.inr (.inr true))) => fun x => planeAxis (S.family.edgeBHeight_BAUGA x)

/-- **The interior formula on `W°`**: FC01's block map of the ACTIVE family. -/
def interiorMapOn_BAUGA (x : W.pieceInterior ⊤) : BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) :=
  blockMap S.intRadius_BAUGA S.intCutoff_BAUGA S.intCoord_BAUGA x

open Classical in
/-- The interior slots on the original carrier: the scale slot is `(0, ρ)` with the original `ρ`;
every other slot is the zero extension of its `W°` slot. -/
def intSlotW_BAUGA (t : S.IntTag_BAUGA) (y : W.Carrier) : WithLp 2 (ℝ² × ℝ) :=
  if t = S.scaleTag_BAUGA then WithLp.toLp 2 (0, S.rho y)
  else Subtype.val.extend (fun x => S.interiorMapOn_BAUGA x t) 0 y

/-- **`F_int^W`**: the interior part of the augmented map on the original carrier `W`. -/
def interiorMapW_BAUGA (y : W.Carrier) : BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²) :=
  WithLp.toLp 2 fun t => S.intSlotW_BAUGA t y

/-- **`F_int^W` is the active family's interior formula on `W°`.** -/
theorem interiorMapW_val_BAUGA (x : W.pieceInterior ⊤) :
    S.interiorMapW_BAUGA x.val = S.interiorMapOn_BAUGA x := by
  refine congrArg (WithLp.toLp 2) (funext fun t => ?_)
  by_cases ht : t = S.scaleTag_BAUGA
  · subst ht
    simp only [intSlotW_BAUGA, ↓reduceIte]
    change WithLp.toLp 2 ((0 : ℝ²), S.rho x.val) =
      WithLp.toLp 2 ((S.rho x * 1) • (0 : ℝ²), S.rho x * 1)
    rw [mul_one, smul_zero]
  · simp only [intSlotW_BAUGA, ht, ↓reduceIte]
    exact Subtype.val_injective.extend_apply _ _ x

/-- **The augmented map `F_∂` on the original carrier** (D61-4): interior slots `F_int^W`, the
slot of each boundary component the plane encoding of the packet's ACTUAL collar block. -/
def boundaryOriginalMap (y : W.Carrier) :
    BlockSpace (fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) :=
  boundaryOriginalMap_BAUGA S.packet.toBoundaryCollarPacket S.interiorMapW_BAUGA y

/-- `pr_{H_int} F_∂ = F_int^W`. -/
theorem boundaryOriginalMap_interior_projection (y : W.Carrier) :
    augmentedInteriorProj_BAUGA (S.boundaryOriginalMap y) = S.interiorMapW_BAUGA y :=
  rfl

/-- The slot of `b` is the plane encoding of `P.block b` (collar-band restricted, zero outside). -/
theorem boundaryOriginalMap_boundary_block (y : W.Carrier) (bb : Fin S.packet.cusp.count) :
    S.boundaryOriginalMap y (Sum.inr bb) = planeBlockEmbed_BAUGA (S.packet.block bb y) :=
  rfl

/-- On `Safe_b` the slot of `b` is `(planeAxis η_b, 1)`. -/
theorem boundaryOriginalMap_safe {y : W.Carrier} {bb : Fin S.packet.cusp.count}
    (hy : y ∈ S.packet.safeBand_BAUGA bb) :
    S.boundaryOriginalMap y (Sum.inr bb) =
      WithLp.toLp 2 (planeAxis (S.packet.height bb y), (1 : ℝ)) :=
  boundaryOriginalMap_safe_BAUGA S.packet.toBoundaryCollarPacket S.interiorMapW_BAUGA hy

/-- Off every closed boundary-collar support, `F_∂ = ι_int F_int^W`. -/
theorem boundaryOriginalMap_eq_interior_extension_off_collar_support {y : W.Carrier}
    (hy : y ∉ ⋃ bb, tsupport (S.packet.block bb)) :
    S.boundaryOriginalMap y = augmentedInteriorIncl_BAUGA (S.interiorMapW_BAUGA y) :=
  boundaryOriginalMap_eq_interior_extension_off_collar_support_BAUGA _ _ hy

/-- **(WB) in `F_∂`**: at an interior point the `E'` slot is
`((ρ z_{E'}) planeAxis t_B, ρ z_{E'})`, i.e. `(ρ t_B z_{E'}, ρ z_{E'})` in the plane encoding, with
`t_B = edgeB.smoothing / ρ` and `z_{E'} = h(t_B/Δ) χ_{1/2,1}(Σ ζ_i^B)` of the stored `edgeB`. -/
theorem boundaryOriginalMap_edgePrime_formula (x : W.pieceInterior ⊤) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    S.boundaryOriginalMap x.val (Sum.inl S.edgeTag_BAUGA) =
      WithLp.toLp 2 ((S.rho x * S.family.edgeBMarker_BAUGA x) •
          planeAxis (S.family.edgeBHeight_BAUGA x),
        S.rho x * S.family.edgeBMarker_BAUGA x) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  change S.interiorMapW_BAUGA x.val S.edgeTag_BAUGA = _
  rw [S.interiorMapW_val_BAUGA x]
  rfl

/-- The block constant of the T3B consumer balls, `K₀ = 2010000 + 2000000Δ + 400V + β₁⁻¹ + b⁻¹`,
dominates every interior support radius used below. -/
theorem consumerConstant_ge_BAUGA (hΔ : 0 < Δ) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) :
    2010000 + 2000000 * Δ ≤ 2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹ := by
  have h1 := inv_pos.mpr hβ1
  have h2 := inv_pos.mpr hb
  have := hΔ.le
  nlinarith

/-- **`F_int^W` is smooth on the original carrier `W`** (every interior slot: the zero extension of
its `W°` slot through T3B's transported consumer balls / zero balls, the `E'` slot through
`{D ≥ 10}`, the scale slot `(0, ρ)` directly). -/
theorem contMDiff_interiorMapW_BAUGA (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (he : e ≤ 1 / 10) :
    ContMDiff W.model 𝓘(ℝ, BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)) ∞ S.interiorMapW_BAUGA := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hK0 := consumerConstant_ge_BAUGA hΔ hV hβ1 hb
  have hplane : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ²) ∞ planeAxis := planeAxis.contMDiff
  refine ((PiLp.continuousLinearEquiv 2 ℝ fun _ : S.IntTag_BAUGA => WithLp 2 (ℝ² × ℝ)).symm :
    (∀ _ : S.IntTag_BAUGA, WithLp 2 (ℝ² × ℝ)) →L[ℝ]
      BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)).contMDiff.comp
    (contMDiff_pi_space.2 fun t => ?_)
  by_cases ht : t = S.scaleTag_BAUGA
  · simp only [intSlotW_BAUGA, ht, ↓reduceIte]
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ² ℝ).symm :
      (ℝ² × ℝ) →L[ℝ] WithLp 2 (ℝ² × ℝ)).contMDiff.comp
        (contMDiff_const.prodMk_space S.scale_spec.1)
  simp only [intSlotW_BAUGA, ht, ↓reduceIte]
  rcases t with j | j | j | i | bb
  · -- circle centre
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    have hj1 : ENNReal.ofReal 10 < distanceToBoundary W g j.1 :=
      (S.family.circle.centres_subset hj).1
    have htr := S.transport_spec.2.1 j.1 hj1
    have hrj := S.rho_pos j.1
    have hsupp := S.family.circle.tsupport_subset_ball j.1 hj
    refine contMDiff_extend_zero_of_tsupport_subset_transportBall_BAUGA g S.completion.metric
      (r := 200 * S.rho j.1) (by positivity) (by nlinarith) (by nlinarith) htr.1 htr.2
      ((tsupport_blockSlot_subset_BAUGA (fun _ => S.rho j.1) (S.family.circle.cutoff j.1)
        (S.family.circle.coord_BAUGA j.1)).trans hsupp) ?_
    exact contMDiff_blockSlot_BAUGA isOpen_ball (S.family.circle.contMDiffOn_coord_BAUGA hj)
      (S.family.circle.contMDiff_cutoff j.1 hj) contMDiff_const hsupp
  · -- slim centre
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    have hj1 : ENNReal.ofReal 10 < distanceToBoundary W g j.1 :=
      (S.family.slim.centres_subset hj).1
    have htr := S.transport_spec.2.1 j.1 hj1
    have hrj := S.rho_pos j.1
    have hpos := mul_pos hΔ hrj
    have hS : tsupport (S.family.slim.cutoff_BCNT j.1) ⊆ Metric.ball j.1 (10 ^ 6 * Δ * S.rho j.1) :=
      (S.family.slim.tsupport_cutoff_subset_BCNT j.1).trans
        (closedBall_subset_ball (by nlinarith))
    refine contMDiff_extend_zero_of_tsupport_subset_transportBall_BAUGA g S.completion.metric
      (r := 10 ^ 6 * Δ * S.rho j.1) (by positivity) (by nlinarith) (by nlinarith) htr.1 htr.2
      ((tsupport_blockSlot_subset_BAUGA (fun _ => S.rho j.1) (S.family.slim.cutoff_BCNT j.1)
        (fun x => planeAxis ((S.family.slim.centre j.1 hj).coord_BCG2 x))).trans hS) ?_
    exact contMDiff_blockSlot_BAUGA isOpen_ball
      (hplane.comp_contMDiffOn (S.family.slim.centre j.1 hj).contMDiffOn_coord_BAUGA)
      (S.family.slim.contMDiff_cutoff_BCNT j.1) contMDiff_const hS
  · -- revised edge centre
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    have hj2 : ENNReal.ofReal 20 < distanceToBoundary W g j.1 :=
      S.family.edgeB.centres_subset hj
    have hj1 : ENNReal.ofReal 10 < distanceToBoundary W g j.1 :=
      lt_trans (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by norm_num, by norm_num⟩) hj2
    have htr := S.transport_spec.2.1 j.1 hj1
    have hrj := S.rho_pos j.1
    have hpos := mul_pos hΔ hrj
    have hS := (S.family.tsupport_edgeB_cutoff_subset_BAUGA hΛ hΔ hμ hτ hΔΛ hj).2.2
    refine contMDiff_extend_zero_of_tsupport_subset_transportBall_BAUGA g S.completion.metric
      (r := 100 * Δ * S.rho j.1) (by positivity) (by nlinarith) (by nlinarith) htr.1 htr.2
      ((tsupport_blockSlot_subset_BAUGA (fun _ => S.rho j.1) (S.family.edgeB.cutoff_BAUGA j.1)
        (fun x => planeAxis (S.family.edgeB.coord_BAUGA j.1 x))).trans hS) ?_
    exact contMDiff_blockSlot_BAUGA isOpen_ball
      (hplane.comp_contMDiffOn (S.family.edgeB.contMDiffOn_coord_BAUGA hj))
      (S.family.contMDiff_edgeB_cutoff_BAUGA hΛ hΔ hμ hτ hΔΛ j.1) contMDiff_const hS
  · -- zero centre
    have hi := (Set.Finite.mem_toFinset _).mp i.2
    have hI := S.transport_spec.2.2.2.2.2.1 i.1 hi
    have hcen := S.family.zero.zero_center i.1 hi
    have hr := (S.family.zero.zero i.1 hi).radius_pos
    have hO := Classical.choose_spec (S.family.zero.zero i.1 hi).radial_spec.2.1
    have hspec := (S.family.zero.zero i.1 hi).radial_spec.2.2.2.2.2.2.2.2.2.2.2
    have hts := hspec.choose_spec.2.2.2.2.2.1
    have hball : tsupport (fun x => Calculus.annularCutoff Calculus.cutoffProfile
        ((S.family.zero.zero i.1 hi).radial x)) ⊆
        Metric.ball i.1 (S.family.zero.zero i.1 hi).radius := by
      intro x hx
      have h := (hts hx).2
      have h' : ((S.family.zero.zero i.1 hi).radius)⁻¹ *
          dist x (S.family.zero.zero i.1 hi).center < 9 / 10 + e := h
      rw [hcen, inv_mul_lt_iff₀ hr] at h'
      rw [Metric.mem_ball]
      nlinarith
    have hdom : tsupport (fun x => Calculus.annularCutoff Calculus.cutoffProfile
        ((S.family.zero.zero i.1 hi).radial x)) ⊆
        Classical.choose (S.family.zero.zero i.1 hi).radial_spec.2.1 := by
      refine hts.trans (fun x hx => hO.2.1 ⟨?_, ?_⟩)
      · linarith [hx.1]
      · linarith [hx.2]
    refine contMDiff_extend_zero_of_tsupport_subset_transportBall_BAUGA g S.completion.metric
      (r := (S.family.zero.zero i.1 hi).radius) hr (by linarith) (by linarith) hI.1 hI.2
      ((tsupport_blockSlot_subset_BAUGA (fun _ => (S.family.zero.zero i.1 hi).radius)
        (fun x => Calculus.annularCutoff Calculus.cutoffProfile
          ((S.family.zero.zero i.1 hi).radial x))
        (fun x => planeAxis ((S.family.zero.zero i.1 hi).radial x))).trans hball) ?_
    exact contMDiff_blockSlot_BAUGA hO.1 (hplane.comp_contMDiffOn hO.2.2)
      hspec.choose_spec.2.2.1 contMDiff_const hdom
  · cases bb
    · exact absurd rfl ht
    · -- the weak-edge block E'
      refine contMDiff_extend_zero_of_tsupport_subset_distanceToBoundary_BAUGA g (c := 10)
        (by norm_num) ?_ ?_
      · intro x hx
        have h : ENNReal.ofReal 10 < distanceToBoundary W g x :=
          S.family.tsupport_edgeBMarker_subset_region_BAUGA hΛ hΔ hμ hτ hΔΛ
            ((tsupport_blockSlot_subset_BAUGA (fun y : W.pieceInterior ⊤ => S.rho y)
              S.family.edgeBMarker_BAUGA
              (fun y => planeAxis (S.family.edgeBHeight_BAUGA y))) hx)
        exact h.le
      · have hH : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ S.family.edgeBHeight_BAUGA
            S.family.edgeBDomain_BAUGA := by
          intro x hx
          obtain ⟨k, hk, hxk, hck, hk1, hk2⟩ := hx
          exact (S.family.edgeB.contMDiffAt_height_of_collar_BAUGA hk hxk hck.le hk1.le
            hk2.le).contMDiffWithinAt
        exact contMDiff_blockSlot_BAUGA S.family.isOpen_edgeBDomain_BAUGA
          (hplane.comp_contMDiffOn hH)
          (S.family.contMDiff_edgeBMarker_BAUGA hΛ hΔ hμ hτ hΔΛ) S.family.contMDiff_scale
          (S.family.tsupport_edgeBMarker_subset_domain_BAUGA hΛ hΔ hμ hτ hΔΛ)

/-- **`boundaryOriginalMap_smooth`** (D61-4): the augmented map is smooth on the original
carrier `W`. -/
theorem boundaryOriginalMap_smooth (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (he : e ≤ 1 / 10) :
    ContMDiff W.model 𝓘(ℝ, BlockSpace (fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²)) ∞
      S.boundaryOriginalMap :=
  boundaryOriginalMap_smooth_BAUGA S.packet.toBoundaryCollarPacket S.interiorMapW_BAUGA
    (S.contMDiff_interiorMapW_BAUGA hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he)


/-- **Consumer**: at an interior point off every closed boundary-collar support, the augmented map
is the inclusion of the ACTIVE family's interior formula (`F_∂ = ι_int F_int` there). -/
theorem boundaryOriginalMap_eq_activeFormula_BAUGA {x : W.pieceInterior ⊤}
    (hx : x.val ∉ ⋃ bb, tsupport (S.packet.block bb)) :
    S.boundaryOriginalMap x.val = augmentedInteriorIncl_BAUGA (S.interiorMapOn_BAUGA x) := by
  rw [S.boundaryOriginalMap_eq_interior_extension_off_collar_support hx, S.interiorMapW_val_BAUGA]

end BoundarySupplyCore

end DifferentialGeometry.Geometry.Collapse
