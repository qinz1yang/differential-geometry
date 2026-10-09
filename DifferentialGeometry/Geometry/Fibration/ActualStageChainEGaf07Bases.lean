import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf0507Slim
import DifferentialGeometry.Geometry.Fibration.ActualStageChainEGaf07Stage
import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf06Axis
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleConsequences

/-!
# GAF07 on BASES' open bases `B₁ = circleBase_BAS`, `B₃ = slimBase_BAS`

Blueprint `master207B.tex`, GAF07 (`thm:fibration-whole-closed-fiber-bundles`, B:6049–6165).
Lane C14-BASES defines GAF07's open bases on its embedded final bases `W₁`, `W₃`:
`B₁ = W₁ ∩ ⋃_i {v_i > .9R_i, ‖u_i‖ < 4v_i}` (`Gaf02Chain.circleBase_BAS`) and, for the
one-dimensional slim charts, `B₃ = W₃ ∩ ⋃_i {v_i > .9R_i, |axis u_i| < 4·10⁵Δ v_i}`
(`Gaf02Chain.slimBase_BAS`, BASES' axis coordinate). This file proves GAF07's clauses on exactly
these bases (lane C14-GAF-C did the slim stage for the full-norm ratio set; the axis base needs the
axis form of GAF06, `Gaf02Chain.gaf06_slim_axis_final_GAFD`).

* `Gaf02ChainE.circleBase_relOpen_GAFD`, `Gaf02ChainE.slimBase_relOpen_GAFD`: `B_j = W_j ∩ O_j`,
  `O_j` open.
* first inclusion `gaf07_circle_first_inclusion_base_GAFD`, `gaf07_slim_first_inclusion_base_GAFD`
  (`{|η_i| ≤ 3.5ℓ_i} ⊂ X_j`); `X_j ⊂ U_j`: `gaf07_circle_total_subset_base_GAFD`,
  `gaf07_slim_total_subset_base_GAFD`.
* slim, axis base: `gaf07_slim_fibre_mem_Y_axis_GAFD`, `gaf07_slim_whole_fibre_axis_GAFD` (WHOLE
  fibre = whole adjusted level, `≃ₜ` the original level, connected),
  `Gaf02Chain.gaf07_slim_submersion_of_mem_GAFD` (submersion of `g_i` at every point of `Y_i`),
  `gaf07_slim_stage_fibre_GAFD` (whole stage fibre = whole final fibre).
* circle, SMOOTH type: `gaf07_circle_whole_fibre_smooth_GAFD` — every whole fibre over `B₁` is the
  image of a smooth embedding of `Circle` (regular level of `g_i` on `Y_i`, compact and connected,
  classification of compact connected 1-manifolds `nonempty_circle_diffeomorph_regularFiber`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open GC.GraphManifold GC.Endpoint

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}

/-- The axis coordinate is bounded by the norm. -/
theorem norm_axisCoord_le_GAFD (v : ℝ²) : ‖axisCoordCLM_BAS v‖ ≤ ‖v‖ :=
  (axisCoordCLM_BAS.le_opNorm v).trans
    (by nlinarith [norm_axisCoordCLM_le_BAS, norm_nonneg v, norm_nonneg axisCoordCLM_BAS])

/-- **A compact connected regular level of codimension `dim − 1` on an open set is a smooth
circle** (generic; classification of compact connected 1-manifolds): for `g : M → F` smooth, `U`
open, `g` a submersion at every point of `{x ∈ U | g x = a}`, `dim E = dim F + 1`, and that level
compact and connected, it is the image of a smooth embedding of `Circle`. -/
theorem exists_circle_embedding_level_GAFD {E F M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] {U : Set M} (hU : IsOpen U) {f : M → F}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f) {a : F}
    (hreg : ∀ x ∈ U, f x = a → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    (hcpt : IsCompact {x | x ∈ U ∧ f x = a}) (hconn : IsConnected {x | x ∈ U ∧ f x = a}) :
    ∃ γ : Circle → M, IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E) ∞ γ ∧ range γ = {x | x ∈ U ∧ f x = a} := by
  let W : TopologicalSpace.Opens M := ⟨U, hU⟩
  let G : W → F := fun y => f y.1
  have hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ G := hf.comp (contMDiff_subtype_val (I := 𝓘(ℝ, E)))
  have hregG : ∀ y : W, G y = a → Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) G y) := by
    intro y hy
    rw [show G = fun z : W => f z from rfl, DifferentialGeometry.mfderiv_restrict_open f W y]
    exact hreg y.1 y.2 hy
  have himg : (Subtype.val : W → M) '' {y | G y = a} = {x | x ∈ U ∧ f x = a} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hxa⟩
      exact ⟨⟨x, hx⟩, hxa, rfl⟩
  have hcptG : IsCompact {y : W | G y = a} := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]
    exact hcpt
  have hconnG : IsConnected {y : W | G y = a} := by
    have h2 : IsConnected ((Subtype.val : W → M) '' {y | G y = a}) := by
      rw [himg]
      exact hconn
    refine ⟨?_, ?_⟩
    · obtain ⟨x, hx⟩ := h2.nonempty
      obtain ⟨y, hy, -⟩ := hx
      exact ⟨y, hy⟩
    · exact Topology.IsInducing.subtypeVal.isPreconnected_image.mp h2.isPreconnected
  obtain ⟨d⟩ := OneManifold.nonempty_circle_diffeomorph_regularFiber G a hG hregG hdim hcptG
    hconnG
  let _ := regularFiberChartedSpace G a hG hregG
  have hinc := contMDiff_regularFiberInclusion G a hG hregG
  let ι := (Subtype.val : W → M) ∘ (Subtype.val : {y // G y = a} → W)
  have hι : ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) 𝓘(ℝ, E) ∞ ι :=
    (contMDiff_subtype_val (I := 𝓘(ℝ, E))).comp hinc
  have hemb : Topology.IsEmbedding ι :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hinj : ∀ y : {y // G y = a}, Injective (mfderiv
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ F) → ℝ) 𝓘(ℝ, E) ι y) := by
    intro y
    have hFd := (hinc y).mdifferentiableAt (by simp)
    have h2 := (DifferentialGeometry.hasMFDerivAt_subtype_val (I := 𝓘(ℝ, E)) _ y.1).comp y
      hFd.hasMFDerivAt
    rw [h2.mfderiv]
    have hi := mfderiv_regularFiberInclusion_injective G a hG hregG y
    intro u v huv
    exact hi huv
  have hrange : range ι = {x | x ∈ U ∧ f x = a} := by
    rw [← himg]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  obtain ⟨h1, h2⟩ := isSmoothEmbedding_comp_diffeomorph_symm_SSTD _ hι hemb hinj d.symm
  exact ⟨_, h1, h2.trans hrange⟩

namespace Gaf02Chain

variable {P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- **GAF07, submersion of the adjusted slim coordinate on the WHOLE original domain** (B:6118–6121;
BASES-free): with `c₃ < 1/1000`, `g_i` has surjective differential at every point of
`Y_i = {|η_i| < 5·10⁵Δ}` (LFR20.1's right inverse of gauge `≤ 4/3`, `‖Dg_i − Dη_i‖ < c₃`). -/
theorem gaf07_slim_submersion_of_mem_GAFD (C : Gaf02Chain P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hp : p ∈ gaf07SlimY_GAFC P i) :
    Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (C.gaf07SlimCoord_GAFC i) p) := by
  obtain ⟨H, hH0, hH, hgauge⟩ := C.gaf07_slim_gauge_GAFC hc
  obtain ⟨⟨R, hR, hRn⟩, hD⟩ := hgauge i p hp
  exact surjective_of_right_inverse_perturbation_nu_GAFC _ _ R hR
    (fun v => Real.sqrt ((ρ i.1)⁻¹ ^ 2 * g.inner p v v)) hRn hD hH0 (by linarith)

end Gaf02Chain

namespace Gaf02ChainE

variable {P : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ
    εr e T V vs ζ Λz} {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- `π₃` keeps the slim marker and the slim axis coordinate. -/
theorem slim_stageQ_GAFD (i : P.toLocalChartFamily.slim.finite_centres.toFinset)
    (y : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)) :
    gafSlimMarker P.toLocalChartFamily P.zero i
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection y) =
      gafSlimMarker P.toLocalChartFamily P.zero i y ∧
    (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i))
        ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection y) =
      (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) y := by
  have ht := slim_mem_cgpQ3Tags P.toLocalChartFamily P.zero i
  refine ⟨marker_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i)) ht y, ?_⟩
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  exact congrArg axisCoordCLM_BAS
    (vector_stageQ_G47 P.toLocalChartFamily P.zero (st := 2) (t := .inr (.inl i)) ht y)

/-- **`B₁` is relatively open in `W₁`**: `B₁ = W₁ ∩ R₁` with GAF47's open ratio set `R₁`. -/
theorem circleBase_relOpen_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    C.toChain.circleBase_BAS = C.toChain.finalBase_BAS 0 ∩
        gaf07CircleRatio_G47 P.toLocalChartPackets ∧
      IsOpen (gaf07CircleRatio_G47 P.toLocalChartPackets) := by
  refine ⟨?_, isOpen_gaf07CircleRatio_GAFC _⟩
  rw [Gaf02Chain.circleBase_BAS, gaf07CircleRatio_G47]
  simp only [mul_one]
  rfl

/-- **`B₃` is relatively open in `W₃`**: `B₃ = W₃ ∩ O₃`, `O₃` open (the axis ratio set). -/
theorem slimBase_relOpen_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) :
    ∃ O : Set (BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)), IsOpen O ∧
      C.toChain.slimBase_BAS = C.toChain.finalBase_BAS 2 ∩ O :=
  ⟨_, isOpen_iUnion fun k => (isOpen_lt continuous_const
      (gafSlimMarker P.toLocalChartFamily P.zero k).continuous).inter
        (isOpen_lt
          (axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero k)).continuous.norm
          (continuous_const.mul (gafSlimMarker P.toLocalChartFamily P.zero k).continuous)), rfl⟩

/-- **GAF07, first inclusion, circle stage, on BASES' `B₁`** (B:6086–6089): an original point with
`‖η_i(p)‖ ≤ 3.5` has `π₁E(p) ∈ B₁` (GAF02/CGP08 put it in `W₁`, the direct estimate in `R₁`). -/
theorem gaf07_circle_first_inclusion_base_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (hc : c 2 < 1 / 1000) (i : P.toLocalChartFamily.circle.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (200 * ρ i.1))
    (hη : ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ ≤ 7 / 2) :
    (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
      C.toChain.circleBase_BAS := by
  rw [C.circleBase_relOpen_GAFD.1]
  exact ⟨(C.final_mem_circleBase_GAFC i ⟨hpi, by linarith⟩).1,
    C.toChain.gaf07_circle_first_inclusion_G47 hc i hpi hη⟩

/-- **GAF07, first inclusion, slim stage, on BASES' `B₃`** (B:6086–6089): an original point with
`|η_i(p)| ≤ 3.5·10⁵Δ` has `π₃E(p) ∈ B₃` (`W₃` by CGP07 at threshold 5, the axis ratio from the
full-norm estimate). -/
theorem gaf07_slim_first_inclusion_base_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (hc : c 2 < 1 / 1000) (i : P.toLocalChartFamily.slim.finite_centres.toFinset) {p : X}
    (hpi : p ∈ ball i.1 (1000000 * Δ * ρ i.1))
    (hη : |(P.toLocalChartFamily.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| ≤
      7 / 2 * (10 ^ 5 * Δ)) :
    (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈
      C.toChain.slimBase_BAS := by
  obtain ⟨-, hΔ, -⟩ := C.toChain.std
  have hV := C.toChain.slim_mem_patch_of_domain5_BAS i hpi (by nlinarith)
  rw [C.stageMap_two_eq_GAFC] at hV
  refine ⟨⟨_, mem_iUnion.mpr ⟨i, hV⟩, rfl⟩, ?_⟩
  obtain ⟨k, hk⟩ := mem_iUnion.mp (C.toChain.gaf07_slim_first_inclusion_G47 hc i hpi hη)
  refine mem_iUnion.mpr ⟨k, hk.1, ?_⟩
  exact (norm_axisCoord_le_GAFD _).trans_lt hk.2

/-- **GAF07, `X₁ ⊂ U₁`, on BASES' `B₁`** (B:6090–6094): every point of the WHOLE preimage of `B₁`
has, for a witnessing index, `p ∈ B(c_i, 200ρ(c_i))`, `‖η_i(p)‖ < 4.01 < 5`, original cutoff one. -/
theorem gaf07_circle_total_subset_base_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (hc : c 2 < 1 / 1000) (p : X)
    (hp : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E p) ∈
      C.toChain.circleBase_BAS) :
    ∃ i : P.toLocalChartFamily.circle.finite_centres.toFinset, p ∈ ball i.1 (200 * ρ i.1) ∧
      ‖cgpCoord P.toLocalChartFamily P.zero (.inl i) p‖ < 401 / 100 ∧
      P.toLocalChartFamily.circle.cutoff i.1 p = 1 := by
  rw [C.circleBase_relOpen_GAFD.1] at hp
  exact C.toChain.gaf07_circle_total_subset_G47 hc p hp.2

/-- **GAF07, `X₃ ⊂ U₃`, on BASES' axis base `B₃`** (B:6090–6094; axis GAF06 at `τ = 1`): every point
of the WHOLE preimage of `B₃` has, for a witnessing index, `p ∈ B(c_i, 10⁶Δρ(c_i))`,
`|η_i(p)| < 4.01·10⁵Δ < 5·10⁵Δ` and original cutoff one. -/
theorem gaf07_slim_total_subset_base_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (hc : c 2 < 1 / 1000) (p : X)
    (hp : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) ∈
      C.toChain.slimBase_BAS) :
    ∃ i : P.toLocalChartFamily.slim.finite_centres.toFinset,
      p ∈ ball i.1 (1000000 * Δ * ρ i.1) ∧
      |(P.toLocalChartFamily.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p| <
        401 / 100 * (10 ^ 5 * Δ) ∧
      P.toLocalChartFamily.slim.cutoff i.1 p = 1 := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp hp.2
  obtain ⟨hm, hv⟩ := slim_stageQ_GAFD (P := P) i (C.toChain.E p)
  have h1 := hi.1
  have h2 := hi.2
  rw [hm] at h1
  rw [hm, hv] at h2
  exact ⟨i, C.toChain.gaf06_slim_axis_final_GAFD hc i p h1 h2.le⟩

/-- GAF06 (axis form) at a point of a whole slim fibre over the axis ratio piece of `i`:
`p ∈ Y_i`. -/
theorem gaf07_slim_fibre_mem_Y_axis_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset)
    (hm : 9 / 10 * ρ i.1 < gafSlimMarker P.toLocalChartFamily P.zero i w)
    (hr : ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w‖ <
      4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero i w)
    (p : X) (hp : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) = w) :
    p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i := by
  obtain ⟨-, hΔ1, -⟩ := C.toChain.std
  obtain ⟨hmk, hvk⟩ := slim_stageQ_GAFD (P := P) i (C.toChain.E p)
  rw [hp] at hmk hvk
  obtain ⟨hpi, hη, -⟩ := C.toChain.gaf06_slim_axis_final_GAFD hc i p (by rw [← hmk]; exact hm)
    (by rw [← hmk, ← hvk]; exact hr.le)
  exact ⟨hpi, by nlinarith⟩

/-- **GAF07, WHOLE slim fibres over BASES' axis base `B₃`** (B:6104–6149): for `w ∈ W₃` in the axis
ratio piece of `i` (`v_i(w) > .9R_i`, `|axis u_i(w)| < 4·10⁵Δ v_i(w)`), `a = proj₀(R_i⁻¹u_i(w))`
has `|a| < 4·10⁵Δ`; the WHOLE fibre `(π₃E)⁻¹(w)` EQUALS the whole adjusted level
`{p ∈ Y_i | g_i(p) = a}`, is homeomorphic to the original slim level `{p ∈ Y_i | η_i(p) = a}`, and
is connected. -/
theorem gaf07_slim_whole_fibre_axis_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hW : w ∈ C.toChain.finalBase_BAS 2)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset)
    (hm : 9 / 10 * ρ i.1 < gafSlimMarker P.toLocalChartFamily P.zero i w)
    (hr : ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w‖ <
      4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero i w) :
    |EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
        blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)) w)| <
        4 * (10 ^ 5 * Δ) ∧
      (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) ⁻¹' {w} =
        {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧ C.toChain.gaf07SlimCoord_GAFC i p =
          EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
            blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
              (.inr (.inl i)) w)} ∧
      Nonempty ((fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
          (C.toChain.E p)) ⁻¹' {w} ≃ₜ
        {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧
          (P.toLocalChartFamily.slim.centre i.1 ((Set.Finite.mem_toFinset _).mp i.2)).coord p =
            EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
              blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
                (.inr (.inl i)) w)}) ∧
      IsConnected ((fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
        (C.toChain.E p)) ⁻¹' {w}) := by
  have hri := hρ i.1
  have hY := C.gaf07_slim_fibre_mem_Y_axis_GAFD hc w i hm hr
  obtain ⟨p₀, hp₀⟩ := C.gaf07_slim_onto_GAFC w hW
  have hY₀ := hY p₀ hp₀
  have hV₀ := C.toChain.slim_mem_patch_of_domain5_BAS i hY₀.1 hY₀.2
  rw [C.stageMap_two_eq_GAFC, hp₀] at hV₀
  have hv : gafSlimMarker P.toLocalChartFamily P.zero i w = ρ i.1 :=
    C.gaf05_slimPatch_marker_GAFC i w hV₀
  have hcoord := slim_retained_coord_eq_GAFC (P := P) i
  have ha : |EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
      blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i)) w)| <
      4 * (10 ^ 5 * Δ) := by
    have h' : |(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w| <
        4 * (10 ^ 5 * Δ) * ρ i.1 := by
      rw [← Real.norm_eq_abs]
      rw [hv] at hr
      exact hr
    rw [← hcoord w, smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hri),
      inv_mul_lt_iff₀ hri]
    linarith
  have hinj := (C.toChain.cgp07_slim_BAS C.rough i).1.injOn
  have heq : (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection
      (C.toChain.E p)) ⁻¹' {w} =
      {p | p ∈ gaf07SlimY_GAFC P.toLocalChartPackets i ∧ C.toChain.gaf07SlimCoord_GAFC i p =
        EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
          blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
            (.inr (.inl i)) w)} := by
    ext p
    constructor
    · intro hp
      have hp' : (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) = w := hp
      refine ⟨hY p hp', ?_⟩
      change EuclideanSpace.proj (0 : Fin 2) ((ρ i.1)⁻¹ •
        blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inr (.inl i))
          ((gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p))) = _
      rw [hp']
    · rintro ⟨hpY, hpa⟩
      have hVp := C.toChain.slim_mem_patch_of_domain5_BAS i hpY.1 hpY.2
      rw [C.stageMap_two_eq_GAFC] at hVp
      change (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p) = w
      refine hinj hVp hV₀ ?_
      rw [hcoord, hcoord]
      exact hpa
  obtain ⟨⟨φ⟩, hconn, -⟩ := C.toChain.gaf07_slim_level_GAFC hc i ha
  refine ⟨ha, heq, ⟨(Homeomorph.setCongr heq).trans φ.symm⟩, ?_⟩
  rw [heq]
  exact hconn

/-- **GAF07, whole stage fibre = whole final fibre, slim stage** (B:6150–6165): for `w ∈ W₃` in the
axis ratio piece of `i`, `w ∈ V_i⁰` with `Θ₃ w = w` and `f₃⁻¹(w) = (π₃E)⁻¹(w)` as WHOLE subsets. -/
theorem gaf07_slim_stage_fibre_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw) (hc : c 2 < 1 / 1000)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hW : w ∈ C.toChain.finalBase_BAS 2)
    (i : P.toLocalChartFamily.slim.finite_centres.toFinset)
    (hm : 9 / 10 * ρ i.1 < gafSlimMarker P.toLocalChartFamily P.zero i w)
    (hr : ‖(axisCoordCLM_BAS.comp (gafSlimVector P.toLocalChartFamily P.zero i)) w‖ <
      4 * (10 ^ 5 * Δ) * gafSlimMarker P.toLocalChartFamily P.zero i w) :
    ∃ w₀ ∈ C.toChain.slimPatch_BAS i, C.toChain.Θ_BAS 2 w₀ = w ∧
      C.toChain.stageMap_BAS 2 ⁻¹' {w₀} =
        (fun p => (gafStageQ P.toLocalChartFamily P.zero 2).starProjection (C.toChain.E p)) ⁻¹'
          {w} := by
  obtain ⟨p₀, hp₀⟩ := C.gaf07_slim_onto_GAFC w hW
  have hY₀ := C.gaf07_slim_fibre_mem_Y_axis_GAFD hc w i hm hr p₀ hp₀
  have hV₀ := C.toChain.slim_mem_patch_of_domain5_BAS i hY₀.1 hY₀.2
  rw [C.stageMap_two_eq_GAFC, hp₀] at hV₀
  refine ⟨w, hV₀, rfl, ?_⟩
  ext p
  simp only [mem_preimage, mem_singleton_iff, C.stageMap_two_eq_GAFC]

/-- **GAF07, `j = 1`: every WHOLE circle fibre over `B₁` is a SMOOTH circle** (B:6053–6055): for
`w ∈ W₁` in the ratio piece of `i` (TCP01 range of the packet, `c₃ < 1/1000`), `(π₁E)⁻¹(w)` is the
image of a smooth embedding of `Circle` (it is the regular level `{g_i = a}` of the submersion `g_i`
on the open `Y_i`, compact and connected). -/
theorem gaf07_circle_whole_fibre_smooth_GAFD (C : Gaf02ChainE P Kj Ξ Γ S eg c cw)
    (hc : c 2 < 1 / 1000) (hβ : β 2 ≤ 1 / 10000000) (hd : γ + β 2 < 1 / 10)
    (w : BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²))
    (hW : w ∈ C.toChain.finalBase_BAS 0)
    (i : P.toLocalChartFamily.circle.finite_centres.toFinset)
    (hm : 9 / 10 * ρ i.1 < blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²)
      (.inl i) w)
    (hr : ‖blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w‖ <
      4 * blockMarkerCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w) :
    ∃ f : Circle → X, IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, E3) ∞ f ∧
      range f = (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
        (C.toChain.E p)) ⁻¹' {w} := by
  obtain ⟨-, heq, -, hconn⟩ := C.gaf07_circle_whole_fibre_GAFC hc hβ hd w hW i hm hr
  have hFc : IsCompact ((fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
      (C.toChain.E p)) ⁻¹' {w}) :=
    (isClosed_singleton.preimage
      ((gafStageQ P.toLocalChartFamily P.zero 0).starProjection.continuous.comp
        C.toChain.stage_smooth.2.2.continuous)).isCompact
  have hreg : ∀ x ∈ gaf07CircleY_GAFC P.toLocalChartPackets i,
      C.toChain.gaf07CircleCoord_GAFC i x = (ρ i.1)⁻¹ •
        blockVectorCLM (V := fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) (.inl i) w →
      Surjective (mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) (C.toChain.gaf07CircleCoord_GAFC i) x) := by
    intro x hx hxa
    have hxF : x ∈ (fun p => (gafStageQ P.toLocalChartFamily P.zero 0).starProjection
        (C.toChain.E p)) ⁻¹' {w} := by
      rw [heq]
      exact ⟨hx, hxa⟩
    have hxw : (gafStageQ P.toLocalChartFamily P.zero 0).starProjection (C.toChain.E x) = w := hxF
    exact (C.gaf07_circle_submersion_GAFC hc hβ hd i x (by rw [hxw]; exact hm)
      (by rw [hxw]; exact hr)).2
  have key := exists_circle_embedding_level_GAFD (isOpen_gaf07CircleY_GAFC _ i)
    (C.toChain.gaf07_circle_smooth_GAFC i).2 hreg
    (by simp only [finrank_euclideanSpace_fin]) (heq ▸ hFc) (heq ▸ hconn)
  rw [heq]
  exact key

end Gaf02ChainE

end DifferentialGeometry.Geometry.Collapse
