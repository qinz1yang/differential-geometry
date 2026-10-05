import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.ExtPortRegressionXPI
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimBundleRestrict
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0AdaptedV2

/-!
# FC39 external-port regression instance: the adapted edge–rim data V2 (no edge)

External review 63 (D63-7), 67 (D67-6): the adapted edge–rim data V2 over the prepared rows
`⟨extportRowsW_XPI, GF⟩` for EVERY global face family `GF` (in particular the general GFF output
`exists_globalFaceFunctions_GGFF`) and EVERY safe family `safe` (in particular the general SAFE
output). The instance has no edge, so the edge and rim data are EMPTY families; the only
non-trivial datum is the final circle region:

* `extportCirc_XPI GF` — base `GF.base`, domain / projection / trivializations the restriction of
  the row bundle (RIMBOX R1, `CircleBundle.restrictDomain_GRIM` …), two defining functions
  `GF.fn (faceIdx_XPI GF l) ∘ val` (the faces of `circleFaceEquiv_XPI`), no corner (a double zero of
  `GF` would be a registered edge endpoint), the rounding `(‖w‖² − 9/4)(‖w‖² − 4)` whose sublevel is
  exactly the cornered base `val⁻¹ C₁`;
* `extportCircLink_XPI GF` (`ι = val`), `extportFaceLink_XPI GF` (`defining_eq` by `rfl`);
* `extportAdapted_XPI GF safe : AdaptedEdgeRimDataV2 ⟨extportRowsW_XPI, GF⟩ safe`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.ExtPortXPI

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ## The rounding of the circle base -/

/-- The rounding of the circle base `(‖w‖² − 9/4)(‖w‖² − 4)`. -/
def roundBase_XPI (c : circleBaseOpens_XPI) : ℝ :=
  baseRadialFn_XPI (-(9 / 4)) 1 c * baseRadialFn_XPI (-4) 1 c

theorem contMDiff_roundBase_XPI : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ roundBase_XPI :=
  (contMDiff_baseRadialFn_XPI _ _).mul (contMDiff_baseRadialFn_XPI _ _)

theorem roundBase_eq_XPI (c : circleBaseOpens_XPI) :
    roundBase_XPI c = (‖c.val‖ ^ 2 - 9 / 4) * (‖c.val‖ ^ 2 - 4) := by
  change (-(9 / 4) + 1 * ‖c.val‖ ^ 2) * (-4 + 1 * ‖c.val‖ ^ 2) = _
  ring

/-- The rounding is nonpositive exactly on the closed base annulus `C₁`. -/
theorem roundBase_nonpos_iff_XPI {c : circleBaseOpens_XPI} :
    roundBase_XPI c ≤ 0 ↔ c ∈ circleCbase_XPI := by
  rw [roundBase_eq_XPI]
  change _ ↔ 3 / 2 ≤ ‖c.val‖ ∧ ‖c.val‖ ≤ 2
  have h0 := norm_nonneg c.val
  constructor
  · intro h
    by_contra hn
    rw [not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · have h1 : ‖c.val‖ ^ 2 < 9 / 4 := by nlinarith
      nlinarith
    · have h1 : 4 < ‖c.val‖ ^ 2 := by nlinarith
      nlinarith
  · rintro ⟨h1, h2⟩
    have h3 : 9 / 4 ≤ ‖c.val‖ ^ 2 := by nlinarith
    have h4 : ‖c.val‖ ^ 2 ≤ 4 := by nlinarith
    nlinarith

theorem mfderiv_roundBase_self_XPI (c : circleBaseOpens_XPI) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) roundBase_XPI c c.val =
      (2 * ‖c.val‖ ^ 2 - 25 / 4) * (2 * ‖c.val‖ ^ 2) := by
  have hp := hasMFDerivAt_baseRadialFn_XPI (-(9 / 4)) 1 c
  have hq := hasMFDerivAt_baseRadialFn_XPI (-4) 1 c
  have h := (hp.mul hq).mfderiv
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
    (baseRadialFn_XPI (-(9 / 4)) 1 * baseRadialFn_XPI (-4) 1) c c.val = _
  rw [h]
  change baseRadialFn_XPI (-(9 / 4)) 1 c * (1 * ((2 : ℕ) • inner ℝ c.val c.val)) +
    baseRadialFn_XPI (-4) 1 c * (1 * ((2 : ℕ) • inner ℝ c.val c.val)) = _
  rw [real_inner_self_eq_norm_sq, nsmul_eq_mul, Nat.cast_ofNat]
  change ((-(9 / 4) + 1 * ‖c.val‖ ^ 2) * (1 * (2 * ‖c.val‖ ^ 2)) +
    (-4 + 1 * ‖c.val‖ ^ 2) * (1 * (2 * ‖c.val‖ ^ 2)) : ℝ) =
      ((2 * ‖c.val‖ ^ 2 - 25 / 4) * (2 * ‖c.val‖ ^ 2) : ℝ)
  ring

/-- The rounding is regular at its zeros. -/
theorem roundBase_regular_XPI (c : circleBaseOpens_XPI) (h : roundBase_XPI c = 0) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) roundBase_XPI c ≠ 0 := by
  intro h0
  have h1 := mfderiv_roundBase_self_XPI c
  rw [h0] at h1
  change (0 : ℝ) = _ at h1
  rw [roundBase_eq_XPI] at h
  have hpos : 0 < ‖c.val‖ := by
    have hc := c.2
    change 5 / 4 < ‖c.val‖ ∧ ‖c.val‖ < 9 / 4 at hc
    linarith [hc.1]
  have hsq : 0 < ‖c.val‖ ^ 2 := by positivity
  rcases mul_eq_zero.mp h with h2 | h2
  · have h3 : ‖c.val‖ ^ 2 = 9 / 4 := by linarith
    rw [h3] at h1
    norm_num at h1
  · have h3 : ‖c.val‖ ^ 2 = 4 := by linarith
    rw [h3] at h1
    norm_num at h1

/-! ## The labelled defining functions -/

variable (GF : GlobalFaceFunctionsV2 extportRowsW_XPI)

/-- The prepared rows of the instance over a global face family. -/
abbrev preparedOf_XPI : FC39PreparedV2 carrierW_XPI portsE_XPI :=
  ⟨extportRowsW_XPI, GF⟩

/-- The index of the two defining functions: `0` the new slim end, `1` the outer cusp face. -/
def faceIdx_XPI : Fin 2 ≃ GF.Face :=
  circleFaceEquiv_XPI.trans GF.actualFace.symm

theorem actualFace_faceIdx_XPI (l : Fin 2) :
    GF.actualFace (faceIdx_XPI GF l) = circleFaceEquiv_XPI l :=
  GF.actualFace.apply_symm_apply _

/-- On the global-face base, all labelled functions are nonpositive iff the point is in `C₁`. -/
theorem forall_fn_nonpos_iff_XPI {c : extportRowsW_XPI.circle.Base} (hc : c ∈ GF.base) :
    (∀ l, GF.fn (faceIdx_XPI GF l) c ≤ 0) ↔ c ∈ extportRowsW_XPI.circle.cbase := by
  rw [GF.base_eq]
  constructor
  · intro h
    refine ⟨hc, fun f => ?_⟩
    rw [← (faceIdx_XPI GF).apply_symm_apply f]
    exact h _
  · exact fun h l => h.2 _

/-- The cornered base of the final region: the points of `GF.base` over `C₁`. -/
def cornerSet_XPI : Set GF.base :=
  {b | ∀ l, GF.fn (faceIdx_XPI GF l) b.val ≤ 0}

theorem cornerSet_eq_XPI :
    cornerSet_XPI GF = (Subtype.val ⁻¹' extportRowsW_XPI.circle.cbase : Set GF.base) := by
  ext b
  exact forall_fn_nonpos_iff_XPI GF b.2

theorem roundingSet_eq_XPI :
    {b : GF.base | roundBase_XPI b.val ≤ 0} = cornerSet_XPI GF := by
  rw [cornerSet_eq_XPI]
  ext b
  exact roundBase_nonpos_iff_XPI (c := b.val)

theorem isCompact_cornerSet_XPI : IsCompact (cornerSet_XPI GF) := by
  rw [cornerSet_eq_XPI, Subtype.isCompact_iff]
  have himg : Subtype.val '' (Subtype.val ⁻¹' extportRowsW_XPI.circle.cbase : Set GF.base) =
      extportRowsW_XPI.circle.cbase := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, GF.cbase_subset hx⟩, hx, rfl⟩
  rw [himg]
  exact extportRowsW_XPI.circle.cbase_compact

/-! ## The final circle region -/

/-- **The final circle region of the instance over `GF`**: the row bundle restricted to `GF.base`,
the two labelled face functions, no corner, the explicit rounding. -/
def extportCirc_XPI : CircleRegion carrierW_XPI where
  Base := GF.base
  domain := extportRowsW_XPI.circle.restrictDomain_GRIM GF.base
  domain_interior _ hx := extportRowsW_XPI.circle.domain_interior
    (extportRowsW_XPI.circle.restrictDomain_le_GRIM GF.base hx)
  proj := extportRowsW_XPI.circle.restrictProj_GRIM GF.base
  proj_smooth := extportRowsW_XPI.circle.contMDiff_restrictProj_GRIM GF.base
  proj_submersion := extportRowsW_XPI.circle.restrictProj_submersion_GRIM GF.base
  neighborhood := extportRowsW_XPI.circle.restrictNeighborhood_GRIM GF.base
  mem_neighborhood := extportRowsW_XPI.circle.mem_restrictNeighborhood_GRIM GF.base
  trivialization := extportRowsW_XPI.circle.restrictTrivialization_GRIM GF.base
  projection_trivialization := extportRowsW_XPI.circle.restrictProjection_trivialization_GRIM GF.base
  definingCount := 2
  defining l c := GF.fn (faceIdx_XPI GF l) c.val
  defining_smooth l := (GF.smooth _).comp_contMDiff contMDiff_subtype_val fun c => c.2
  defining_regular l c h := by
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact GF.zero_regular _ c.val c.2 h
  depth_le_two _ := (Finset.card_filter_le _ _).trans (by simp)
  defining_independent b _ _ hne h h' :=
    (globalFaces_no_double_zero_XPI GF b.2 ((faceIdx_XPI GF).injective.ne hne) h h').elim
  cornerBase := cornerSet_XPI GF
  cornerBase_eq := rfl
  cornerBase_compact := isCompact_cornerSet_XPI GF
  cornerCount := 0
  cornerChart k := k.elim0
  cornerChart_source k := k.elim0
  cornerChart_disjoint k := k.elim0
  cornerFirst k := k.elim0
  cornerSecond k := k.elim0
  corner_ne k := k.elim0
  cornerScale k := k.elim0
  cornerScale_pos k := k.elim0
  chart_first k := k.elim0
  chart_second k := k.elim0
  chart_other k := k.elim0
  corner_center b _ _ hne h h' :=
    (globalFaces_no_double_zero_XPI GF b.2 ((faceIdx_XPI GF).injective.ne hne) h h').elim
  rounding c := roundBase_XPI c.val
  rounding_smooth := contMDiff_roundBase_XPI.comp contMDiff_subtype_val
  rounding_regular c h := by
    have he := DifferentialGeometry.mfderiv_restrict_open (I := 𝓡 2) (J := 𝓘(ℝ, ℝ))
      (M := extportRowsW_XPI.circle.Base) (N := ℝ) roundBase_XPI GF.base c
    intro h0
    exact roundBase_regular_XPI c.val h (he.symm.trans h0)
  rounding_chart k := k.elim0
  rounding_agree := by
    rw [roundingSet_eq_XPI]
  rounded_compact := by
    rw [roundingSet_eq_XPI]
    exact isCompact_cornerSet_XPI GF

theorem extportCirc_cornerBase_XPI :
    (extportCirc_XPI GF).cornerBase =
      (Subtype.val ⁻¹' extportRowsW_XPI.circle.cbase : Set GF.base) :=
  cornerSet_eq_XPI GF

theorem extportCirc_rounding_XPI :
    {b | (extportCirc_XPI GF).rounding b ≤ 0} = (extportCirc_XPI GF).cornerBase :=
  roundingSet_eq_XPI GF

/-- **The restriction link** (`ι = val`). -/
def extportCircLink_XPI : CircleRestrictionLink extportRowsW_XPI.circle (extportCirc_XPI GF) where
  region_eq := by
    change Subtype.val '' ((extportRowsW_XPI.circle.restrictProj_GRIM GF.base) ⁻¹'
      (extportCirc_XPI GF).cornerBase) = _
    rw [extportCirc_cornerBase_XPI]
    exact extportRowsW_XPI.circle.region_restrict_GRIM GF.base GF.cbase_subset
  ι := Subtype.val
  ι_isOpenEmbedding := extportRowsW_XPI.circle.isOpenEmbedding_val_GRIM GF.base
  ι_smooth := extportRowsW_XPI.circle.contMDiff_val_GRIM GF.base
  ι_mfderiv := extportRowsW_XPI.circle.mfderiv_val_bijective_GRIM GF.base
  domain_eq := extportRowsW_XPI.circle.restrictDomain_eq_GRIM GF.base
  proj_eq := extportRowsW_XPI.circle.restrictProj_eq_GRIM GF.base

/-- **The global face link**: the defining functions ARE the global face functions (`rfl`). -/
def extportFaceLink_XPI :
    GlobalFaceLinkV2 GF (extportCirc_XPI GF) (extportCircLink_XPI GF) where
  range_subset := by
    rintro _ ⟨c, rfl⟩
    exact c.2
  faceIndex := faceIdx_XPI GF
  defining_eq _ _ := rfl

/-! ## The empty edge and rim data -/

/-- The empty edge layer (no handle, no edge circle). -/
def emptyEdges_XPI : EdgeLayer carrierW_XPI where
  handleCount := 0
  handle h := h.elim0
  edgeCircleCount := 0
  edgeCircle j := j.elim0

/-- The edge link of the empty edge layer to the empty component export. -/
def emptyEdgeLink_XPI :
    EdgeComponentsLink extportRowsW_XPI.edge extportRowsW_XPI.edgeModels emptyEdges_XPI where
  handleEquiv := Equiv.refl _
  circleEquiv := Equiv.refl _
  handle_whole h := h.elim0
  circle_whole j := j.elim0
  handle_proj h := h.elim0
  handle_disk h := h.elim0
  handle_rim h := h.elim0
  circle_proj j := j.elim0
  circle_disk j := j.elim0
  circle_rim j := j.elim0

/-- The empty rim chart layer. -/
def emptyRims_XPI : RimChartLayer carrierW_XPI emptyEdges_XPI (extportCirc_XPI GF) where
  handleCorner h := h.elim0
  handleCorner_bijective := ⟨fun a => a.1.elim0, fun k => k.elim0⟩
  rimChart h := h.elim0
  rim_source h := h.elim0
  rim_proj h := h.elim0
  rim_label h := h.elim0
  rim_disjoint h := h.elim0

/-- The corners of the final region and the edge endpoints: both empty. -/
def endOfCorner_XPI : Fin (extportCirc_XPI GF).cornerCount ≃ extportRowsW_XPI.edge.EdgeEnd where
  toFun k := k.elim0
  invFun e := isEmptyElim e
  left_inv k := k.elim0
  right_inv e := isEmptyElim e

/-- **The labelled corner compatibility V2** (all corner clauses vacuous). -/
def extportLabelled_XPI :
    LabelledCornerCompatibilityV2 (preparedOf_XPI GF) emptyEdges_XPI (extportCirc_XPI GF)
      (emptyRims_XPI GF) where
  edgeLink := emptyEdgeLink_XPI
  circleLink := extportCircLink_XPI GF
  globalFaces := extportFaceLink_XPI GF
  endOfCorner := endOfCorner_XPI GF
  corner_center k := k.elim0
  endpoint_label h := h.elim0
  first_label h := h.elim0
  second_label h := h.elim0
  height_eq h := h.elim0
  horizontal_eq h := h.elim0
  target_full h := h.elim0
  target_in_raw_tube h := h.elim0

/-- **The adapted edge–rim data V2 of the instance**, over every global face family `GF` and every
safe family `safe`: empty edge / rim families, the final circle region over `GF.base`. -/
def extportAdapted_XPI (safe : ProducerSafeNeighbourhoods extportRowsW_XPI) :
    AdaptedEdgeRimDataV2 (preparedOf_XPI GF) safe where
  edges := emptyEdges_XPI
  circ := extportCirc_XPI GF
  components := emptyEdgeLink_XPI
  circle := extportCircLink_XPI GF
  rims := emptyRims_XPI GF
  labelled := extportLabelled_XPI GF
  components_eq := rfl
  circle_eq := rfl
  product h := h.elim0
  rim_closure_in_safe h := h.elim0
  rounding_in_safe := by
    have h : symmDiff {c | (extportCirc_XPI GF).rounding c ≤ 0} (extportCirc_XPI GF).cornerBase =
        ∅ := by
      rw [extportCirc_rounding_XPI, symmDiff_self]
      rfl
    rw [h, preimage_empty, image_empty]
    exact empty_subset _

/-- Adapted data exist over every global face family and every safe family of the instance. -/
theorem nonempty_adapted_XPI (safe : ProducerSafeNeighbourhoods extportRowsW_XPI) :
    Nonempty (AdaptedEdgeRimDataV2 (preparedOf_XPI GF) safe) :=
  ⟨extportAdapted_XPI GF safe⟩

end GC.GraphManifold.Assembly.FC39P0.ExtPortXPI
