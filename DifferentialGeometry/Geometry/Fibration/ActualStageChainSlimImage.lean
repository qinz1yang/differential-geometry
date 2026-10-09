import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07
import DifferentialGeometry.Geometry.Fibration.ActualSlimSlabs
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimFibreSmoothTypeApplications

/-!
# ZSP04 on the chain object: the compact image of the slim slabs (first paragraph of the proof)

Lane C14-ZSP35. Blueprint `master207B.tex`, ZSP04 (`thm:fibration-actual-compact-slim-piece`,
B:6531–6595), first paragraph of the proof: "Each original closed `3.5·10⁵Δ` slab is compact by
LFR20's whole proper bundle. Their finite union is compact and lies in `X₃` by GAF07. Its image is
thus compact in `B₃`." On `C : Gaf02Chain P …` with `f₃ = π₃ ∘ E`
(`π₃ = (gafStageQ 2).starProjection`):

* `zsp04SlimSlabs_ZSP35 P`: the union `⋃_{i ∈ I_s} {p ∈ B(c_i, 10⁶Δρ(c_i)) | |η_i(p)| ≤ 3.5·10⁵Δ}`;
  `Gaf02Chain.slimSlabImage_ZSP35 C`: its image under `f₃`.
* `ratio_lt_of_full_block_ZSP35` (kernel) and `Gaf02Chain.slim_first_inclusion_ZSP35`: GAF07's first
  inclusion `f₃(slab) ⊆ R₃` at the chain's OWN accuracy `c₃ ≤ 1/512` (the form
  `gaf07_slim_first_inclusion_G47` asks `c₃ < 1/1000`, which the chain does not carry).
* `isOpen_gaf07SlimRatio_ZSP35`: the ratio set `R₃` is open.
* `Gaf02Chain.zsp04_slab_image_ZSP35`: the slabs are compact; the image is compact and lies in `R₃`;
  it has a compact neighbourhood `K ⊆ R₃` (a closed thickening) with compact whole preimage; the
  whole preimage of the image is compact; an empty slim family gives empty slabs and image.

Consumer: `zsp04_slab_image_C14Z_ZSP35` (chain on the final family `LocalChartPacketsC14Z`, with the
original whole slim fibres `S²`/`T²` of `slim_fibre_smooth_type_FPRE` at every slim level
`|a| ≤ 3.5·10⁵Δ`). NOT here: GAF07's embedded base `W₃` (BASES), the one-manifold `K₃ ⊂ B₃`, the
finite set `∂C₃` (ZSP03, `j = 3`) and the bundle `M^slim → D₃`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- **The first-inclusion estimate at the chain's accuracy** (GAF07, B:6086–6089; the form of
`ratio_lt_of_full_block_G47` with `c₃ < 1/100`, so that the chain's own `c₃ ≤ 1/512` applies): at a
full-marker block `(u, v)(F) = (Rη, R)` with `‖η‖ ≤ 3.5ℓ`, a point `E` with `‖E − F‖ < c₃ρ`,
`0 < ρ ≤ 5R/4`, `ℓ ≥ 1` satisfies `v(E) > .9R` and `‖u(E)‖ < 4ℓ v(E)`. -/
theorem ratio_lt_of_full_block_ZSP35 {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (u : H →L[ℝ] W) (v : H →L[ℝ] ℝ) (hu : ‖u‖ ≤ 1)
    (hv : ‖v‖ ≤ 1) {F E : H} {η : W} {R ρ c₃ ℓ : ℝ} (hR : 0 < R) (hℓ : 1 ≤ ℓ)
    (hc₃ : c₃ < 1 / 100) (huF : u F = R • η) (hvF : v F = R) (hη : ‖η‖ ≤ 7 / 2 * ℓ)
    (hE : ‖E - F‖ < c₃ * ρ) (hρ0 : 0 < ρ) (hρ : ρ ≤ 5 * R / 4) :
    9 / 10 * R < v E ∧ ‖u E‖ < 4 * ℓ * v E := by
  have hc0 : 0 < c₃ := by
    by_contra h
    have := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h) hρ0.le
    linarith [norm_nonneg (E - F)]
  have hd : ‖E - F‖ < R / 80 := by
    have h1 : c₃ * ρ ≤ c₃ * (5 * R / 4) := mul_le_mul_of_nonneg_left hρ hc0.le
    have h2 : c₃ * (5 * R / 4) < 1 / 100 * (5 * R / 4) :=
      mul_lt_mul_of_pos_right hc₃ (by linarith)
    linarith
  have hvE : |v E - R| ≤ ‖E - F‖ := by
    rw [← hvF, ← map_sub, ← Real.norm_eq_abs]
    exact (v.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hv)
  have huE : ‖u E - R • η‖ ≤ ‖E - F‖ := by
    rw [← huF, ← map_sub]
    exact (u.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hu)
  have hv1 : R - ‖E - F‖ ≤ v E := by linarith [neg_abs_le (v E - R)]
  have hu1 : ‖u E‖ ≤ R * (7 / 2 * ℓ) + ‖E - F‖ := by
    have h := norm_le_insert' (u E) (R • η)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR] at h
    have h' : R * ‖η‖ ≤ R * (7 / 2 * ℓ) := mul_le_mul_of_nonneg_left hη hR.le
    linarith
  have hkey : ‖E - F‖ * (1 + 4 * ℓ) < ℓ * R / 2 := by
    have h1 : ‖E - F‖ * (1 + 4 * ℓ) ≤ ‖E - F‖ * (5 * ℓ) :=
      mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    have h2 : ‖E - F‖ * (5 * ℓ) < R / 80 * (5 * ℓ) :=
      mul_lt_mul_of_pos_right hd (by linarith)
    nlinarith
  refine ⟨by linarith, ?_⟩
  have h4 : 4 * ℓ * (R - ‖E - F‖) ≤ 4 * ℓ * v E :=
    mul_le_mul_of_nonneg_left hv1 (by linarith)
  nlinarith

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}

/-- ZSP04's union of original closed slim slabs `⋃_{i ∈ I_s} {|η_i| ≤ 3.5·10⁵Δ}` (each inside its
slim chart ball `B(c_i, 10⁶Δρ(c_i))`). -/
def zsp04SlimSlabs_ZSP35 (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc
    Lmax τ γ δ εr e T V) : Set X :=
  ⋃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
    {p | p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1) ∧
      |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤ 35 / 10 * 10 ^ 5 * Δ}

/-- GAF07's slim ratio set is open in the block space. -/
theorem isOpen_gaf07SlimRatio_ZSP35 (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b'
    s' ε γc βc Lmax τ γ δ εr e T V) : IsOpen (gaf07SlimRatio_G47 P) := by
  refine isOpen_iUnion fun i => ?_
  rw [ofPred_and]
  exact (isOpen_lt continuous_const
    (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) _).continuous).inter
    (isOpen_lt (continuous_norm.comp
      (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) _).continuous)
      (continuous_const.mul
        (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) _).continuous))

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **GAF07's first inclusion for the slim stage, at the chain's own accuracy** (no extra numeric
hypothesis): at a slim point with `|η_i(p)| ≤ 3.5·10⁵Δ`, `π₃E p` lies in the ratio set `R₃`. -/
theorem slim_first_inclusion_ZSP35 (C : Gaf02Chain P Kj Ξ Γ S eg c cw)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (10 ^ 6 * Δ * ρ i.1))
    (hη : |(P.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
      35 / 10 * 10 ^ 5 * Δ) :
    (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p) ∈ gaf07SlimRatio_G47 P := by
  obtain ⟨-, hΔ, -⟩ := C.std
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hc2, -⟩ := C.numbers
  have hℓ : (1 : ℝ) ≤ 10 ^ 5 * Δ := by nlinarith
  have hpi' : p ∈ ball i.1 (1000000 * Δ * ρ i.1) := by
    convert hpi using 2
    norm_num
  obtain ⟨-, hu, hv, hsc⟩ := C.slim_full_block_G47 i hpi' (by nlinarith)
  have key := ratio_lt_of_full_block_ZSP35
    (blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)))
    (blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)))
    (norm_blockVectorCLM_le _) (norm_blockMarkerCLM_le _) (hρ i.1) hℓ (by linarith) hu hv
    (by rw [norm_planeAxis]; linarith) (C.stage_error_lt.2.2 p) (hρ p) hsc
  refine mem_iUnion.mpr ⟨i, ?_⟩
  have hm := marker_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i))
    (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i) (C.E p)
  have hw := vector_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i))
    (slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i) (C.E p)
  rw [mem_ofPred_eq, hm, hw]
  exact key

/-- ZSP04's image `f₃(⋃_{i ∈ I_s} {|η_i| ≤ 3.5·10⁵Δ})` of the slim slabs under `f₃ = π₃ ∘ E`. -/
def slimSlabImage_ZSP35 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :=
  (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p)) ''
    zsp04SlimSlabs_ZSP35 P

/-- **ZSP04's compact slab image, on the chain** (B:6564–6574, the first paragraph of the proof
of ZSP04, up to the embedded base `W₃` of BASES): the finite union `⋃_{i ∈ I_s}{|η_i| ≤ 3.5·10⁵Δ}`
of original closed slim slabs is compact; its image under `f₃ = π₃ ∘ E` is compact and lies in
GAF07's slim ratio set `R₃` (so in `B₃ = W₃ ∩ R₃` up to `W₃`); it has a compact neighbourhood
`K ⊆ R₃` (a closed thickening) whose whole `f₃`-preimage is compact; the whole `f₃`-preimage of the
image is compact; and an empty slim family gives empty slabs and an empty image. -/
theorem zsp04_slab_image_ZSP35 (C : Gaf02Chain P Kj Ξ Γ S eg c cw) :
    IsCompact (zsp04SlimSlabs_ZSP35 P) ∧ IsCompact C.slimSlabImage_ZSP35 ∧
    C.slimSlabImage_ZSP35 ⊆ gaf07SlimRatio_G47 P ∧
    (∃ Kb : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsCompact Kb ∧
      C.slimSlabImage_ZSP35 ⊆ interior Kb ∧ Kb ⊆ gaf07SlimRatio_G47 P ∧
      IsCompact ((fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p)) ⁻¹'
        Kb)) ∧
    IsCompact ((fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p)) ⁻¹'
      C.slimSlabImage_ZSP35) ∧
    (P.slim.centres = ∅ → zsp04SlimSlabs_ZSP35 P = ∅ ∧ C.slimSlabImage_ZSP35 = ∅) := by
  obtain ⟨-, hΔ1, -⟩ := C.std
  have hΔ : 0 < Δ := by linarith
  have hS : IsCompact (zsp04SlimSlabs_ZSP35 P) :=
    isCompact_iUnion_slimSlab_GAFS P.toLocalChartFamily hΔ (by nlinarith)
  have hcont : Continuous
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.E p)) :=
    (gafStageQ P.toLocalChartFamily P.zero 2).starProjection.continuous.comp
      C.stage_smooth.2.2.continuous
  have hI : IsCompact C.slimSlabImage_ZSP35 := hS.image hcont
  have hsub : C.slimSlabImage_ZSP35 ⊆ gaf07SlimRatio_G47 P := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hp
    exact C.slim_first_inclusion_ZSP35 i hi.1 hi.2
  obtain ⟨δ', hδ', hth⟩ := hI.exists_cthickening_subset_open (isOpen_gaf07SlimRatio_ZSP35 P) hsub
  have hK : IsCompact (cthickening δ' C.slimSlabImage_ZSP35) := hI.cthickening
  refine ⟨hS, hI, hsub, ⟨cthickening δ' C.slimSlabImage_ZSP35, hK, ?_, hth,
    (C.gaf07_proper_G47 2 univ).2 _ hK⟩, (C.gaf07_proper_G47 2 univ).2 _ hI, fun h0 => ?_⟩
  · exact (self_subset_thickening hδ' _).trans
      (interior_maximal (thickening_subset_cthickening _ _) isOpen_thickening)
  · have hS0 : zsp04SlimSlabs_ZSP35 P = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun p hp => ?_
      obtain ⟨i, -⟩ := mem_iUnion.mp hp
      have hi := (Set.Finite.mem_toFinset _).mp i.2
      have h0' : P.toLocalChartFamily.slim.centres = ∅ := h0
      exact (Set.eq_empty_iff_forall_notMem.mp h0') _ hi
    refine ⟨hS0, ?_⟩
    rw [slimSlabImage_ZSP35, hS0, image_empty]

end Gaf02Chain

section Final

/-- The model of the slim fibres (`dim X - 1`). -/
local notation "𝓘S" => 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ)

variable {vs ζ Λz : ℝ} {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **Consumer: ZSP04's slab image for a chain on the final family** `LocalChartPacketsC14Z`: the
image `f₃(⋃_{i ∈ I_s} {|η_i| ≤ 3.5·10⁵Δ})` is compact, lies in GAF07's ratio set `R₃`, is empty for
an empty slim family, and at every slim centre `j` every original level `{η_j = a}`,
`|a| ≤ 3.5·10⁵Δ`, is the WHOLE image of a smooth embedding of one compact connected surface
homeomorphic to `S²` or `T²` (`slim_fibre_smooth_type_FPRE`). -/
theorem zsp04_slab_image_C14Z_ZSP35
    {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM} (C : Gaf02Chain P.toLocalChartPackets Kj Ξ Γ S eg c cw) :
    IsCompact C.slimSlabImage_ZSP35 ∧
    C.slimSlabImage_ZSP35 ⊆ gaf07SlimRatio_G47 P.toLocalChartPackets ∧
    (P.slim.centres = ∅ → C.slimSlabImage_ZSP35 = ∅) ∧
    ∀ j (hj : j ∈ P.slim.centres),
    ∃ (F : Type) (_ : TopologicalSpace F) (_ : ChartedSpace (Fin (Module.finrank ℝ E3 -
        Module.finrank ℝ ℝ) → ℝ) F),
      IsManifold 𝓘S ∞ F ∧ CompactSpace F ∧ ConnectedSpace F ∧
      (Nonempty (F ≃ₜ Metric.sphere (0 : E3) 1) ∨
        Nonempty (F ≃ₜ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) ∧
      ∀ a : ℝ, |a| ≤ 35 / 10 * 10 ^ 5 * Δ → ∃ ι : F → X, ContMDiff 𝓘S 𝓘(ℝ, E3) ∞ ι ∧
        Topology.IsEmbedding ι ∧ (∀ y, Injective (mfderiv 𝓘S 𝓘(ℝ, E3) ι y)) ∧
        range ι = {x | x ∈ ball j (10 ^ 6 * Δ * ρ j) ∧ (P.slim.centre j hj).coord x = a} := by
  obtain ⟨-, hΔ1, -⟩ := C.std
  have hΔ : 0 < Δ := by linarith
  obtain ⟨-, hI, hsub, -, -, h0⟩ := C.zsp04_slab_image_ZSP35
  refine ⟨hI, hsub, fun h => (h0 h).2, fun j hj => ?_⟩
  obtain ⟨F, tF, cF, hF, hc, hcon, htype, hemb⟩ := P.slim_fibre_smooth_type_FPRE hΔ hj
  exact ⟨F, tF, cF, hF, hc, hcon, htype, fun a ha => hemb a (by nlinarith)⟩

end Final

end DifferentialGeometry.Geometry.Collapse
