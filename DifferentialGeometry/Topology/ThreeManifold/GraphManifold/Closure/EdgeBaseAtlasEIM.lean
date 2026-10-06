import Mathlib.Geometry.Manifold.Immersion
import DifferentialGeometry.Topology.Manifold.OneManifold.HalfChart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeBaseAdaptedChartEIM

/-!
# E2 kernel, part 2: the half-line atlas of a smooth domain of a one-manifold (lane S-EDGE-INT)

Draft 74, package E2. Let `Base` be a smooth one-manifold (model `𝓡 1`) and `C ⊆ Base` a set such
that every point of `C` has an ADAPTED chart (a chart `ψ` of the maximal atlas with
`C ∩ ψ.source = {0 ≤ ψ y 0}`, `EdgeBaseAdaptedChartEIM.lean`). Then `↥C` is a smooth manifold with
boundary modelled on `EuclideanHalfSpace 1`:

* `halfChart_EIM`: the chart of `↥C` given by an adapted chart `ψ` (value `halfPt (ψ y 0)`);
* `chartedSpace_EIM` (a definition, not an instance) and `isManifold_EIM`;
* `isImmersion_val_EIM`: the inclusion `↥C → Base` is an immersion (in the adapted chart it is the
  identity of the half-line; no extension across the boundary is needed);
* `isBoundaryPoint_iff_frontier_EIM`: the boundary points of `↥C` are the frontier points of `C`.

Template: `OneManifold/HalfChartAtlasBCF.lean` (the same construction for a subset of a normed
space with half-line graph charts).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Manifold.OneManifold

namespace GC.GraphManifold.Assembly.FC39P0

section Chart

variable {Base : Type*} [TopologicalSpace Base] {C : Set Base}

theorem halfPt_val_of_coord_nonneg_EIM {x : EuclideanSpace ℝ (Fin 1)} (hx : 0 ≤ x 0) :
    (halfPt (x 0)).val = x := by
  change EuclideanSpace.single 0 (max (x 0) 0) = x
  rw [max_eq_left hx]
  exact (val_eq_single x).symm

open scoped Classical in
/-- **The half chart of `↥C` given by an adapted chart `ψ` of `Base`** (`y₀` is the default
value of the inverse off the target). -/
def halfChart_EIM (ψ : OpenPartialHomeomorph Base (EuclideanSpace ℝ (Fin 1)))
    (hψ : ∀ y ∈ ψ.source, (y ∈ C ↔ 0 ≤ ψ y 0)) (y₀ : C) :
    OpenPartialHomeomorph C (EuclideanHalfSpace 1) where
  toFun y := halfPt (ψ y 0)
  invFun z := if h : ψ.symm z.val ∈ C then ⟨ψ.symm z.val, h⟩ else y₀
  source := Subtype.val ⁻¹' ψ.source
  target := {z | z.val ∈ ψ.target}
  map_source' := by
    intro y hy
    have hy' : (y : Base) ∈ ψ.source := hy
    have h0 : 0 ≤ ψ y 0 := (hψ y hy').mp y.2
    change (halfPt (ψ y 0)).val ∈ ψ.target
    rw [halfPt_val_of_coord_nonneg_EIM h0]
    exact ψ.map_source hy'
  map_target' := by
    intro z hz
    have hz' : z.val ∈ ψ.target := hz
    have hs : ψ.symm z.val ∈ ψ.source := ψ.map_target hz'
    have hmem : ψ.symm z.val ∈ C := by
      rw [hψ _ hs, ψ.right_inv hz']
      exact z.2
    dsimp only [mem_preimage]
    rw [dite_eq_left hmem]
    exact hs
  left_inv' := by
    intro y hy
    have hy' : (y : Base) ∈ ψ.source := hy
    have h0 : 0 ≤ ψ y 0 := (hψ y hy').mp y.2
    have hv := halfPt_val_of_coord_nonneg_EIM h0
    have hmem : ψ.symm (halfPt (ψ y 0)).val ∈ C := by
      rw [hv, ψ.left_inv hy']
      exact y.2
    apply Subtype.ext
    simp only [hmem, dite_true]
    rw [hv, ψ.left_inv hy']
  right_inv' := by
    intro z hz
    have hz' : z.val ∈ ψ.target := hz
    have hs : ψ.symm z.val ∈ ψ.source := ψ.map_target hz'
    have hmem : ψ.symm z.val ∈ C := by
      rw [hψ _ hs, ψ.right_inv hz']
      exact z.2
    simp only [hmem, dite_true]
    change halfPt (ψ (ψ.symm z.val) 0) = z
    rw [ψ.right_inv hz']
    exact halfPt_coord z
  open_source := ψ.open_source.preimage continuous_subtype_val
  open_target := ψ.open_target.preimage continuous_subtype_val
  continuousOn_toFun := by
    refine (continuous_halfPt.comp_continuousOn ?_)
    have h1 : ContinuousOn (fun y : C => ψ y) (Subtype.val ⁻¹' ψ.source) :=
      ψ.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hy => hy)
    exact (EuclideanSpace.proj (0 : Fin 1) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).continuous.comp_continuousOn h1
  continuousOn_invFun := by
    refine Topology.IsEmbedding.subtypeVal.isInducing.continuousOn_iff.mpr ?_
    have hc : ContinuousOn (fun z : EuclideanHalfSpace 1 => ψ.symm z.val) {z | z.val ∈ ψ.target} :=
      ψ.continuousOn_symm.comp continuous_subtype_val.continuousOn (fun _ hz => hz)
    refine hc.congr fun z hz => ?_
    have hz' : z.val ∈ ψ.target := hz
    have hmem : ψ.symm z.val ∈ C := by
      rw [hψ _ (ψ.map_target hz'), ψ.right_inv hz']
      exact z.2
    simp only [Function.comp_apply, hmem, dite_true]


section HalfChartLemmas

variable {ψ : OpenPartialHomeomorph Base (EuclideanSpace ℝ (Fin 1))}
  {hψ : ∀ y ∈ ψ.source, (y ∈ C ↔ 0 ≤ ψ y 0)} {y₀ : C}

theorem halfChart_apply_EIM (y : C) :
    halfChart_EIM ψ hψ y₀ y = halfPt (ψ y 0) := rfl

theorem halfChart_source_EIM : (halfChart_EIM ψ hψ y₀).source = Subtype.val ⁻¹' ψ.source := rfl

theorem halfChart_target_EIM : (halfChart_EIM ψ hψ y₀).target = {z | z.val ∈ ψ.target} := rfl

/-- The vector of the chart value of a point of the source is `ψ y`. -/
theorem halfChart_val_EIM {y : C} (hy : (y : Base) ∈ ψ.source) :
    (halfChart_EIM ψ hψ y₀ y).val = ψ y := by
  rw [halfChart_apply_EIM]
  exact halfPt_val_of_coord_nonneg_EIM ((hψ y hy).mp y.2)

/-- The coordinate of the chart value of a point of the source is `ψ y 0`. -/
theorem halfChart_val_zero_EIM {y : C} (hy : (y : Base) ∈ ψ.source) :
    (halfChart_EIM ψ hψ y₀ y).val 0 = ψ y 0 := by
  rw [halfChart_val_EIM hy]

open scoped Classical in
/-- The inverse chart on the target is `ψ.symm` of the vector. -/
theorem halfChart_symm_val_EIM {z : EuclideanHalfSpace 1}
    (hz : z ∈ (halfChart_EIM ψ hψ y₀).target) :
    (((halfChart_EIM ψ hψ y₀).symm z : C) : Base) = ψ.symm z.val := by
  have hz' : z.val ∈ ψ.target := hz
  have hmem : ψ.symm z.val ∈ C := by
    rw [hψ _ (ψ.map_target hz'), ψ.right_inv hz']
    exact z.2
  change ((if h : ψ.symm z.val ∈ C then ⟨ψ.symm z.val, h⟩ else y₀ : C) : Base) = _
  simp only [hmem, dite_true]

end HalfChartLemmas

/-- In an adapted chart, a point of `C` lies in the frontier of `C` iff its coordinate is `0`. -/
theorem mem_frontier_iff_coord_eq_zero_EIM
    {ψ : OpenPartialHomeomorph Base (EuclideanSpace ℝ (Fin 1))}
    (hψ : ∀ y ∈ ψ.source, (y ∈ C ↔ 0 ≤ ψ y 0)) {y : Base} (hy : y ∈ ψ.source) (hyC : y ∈ C) :
    y ∈ frontier C ↔ ψ y 0 = 0 := by
  have h0 : 0 ≤ ψ y 0 := (hψ y hy).mp hyC
  have hproj : Continuous fun v : EuclideanSpace ℝ (Fin 1) => v 0 :=
    (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ).continuous
  constructor
  · intro hfr
    by_contra hne
    have hpos : 0 < ψ y 0 := lt_of_le_of_ne h0 (Ne.symm hne)
    have hopen : IsOpen (ψ.source ∩ ψ ⁻¹' {v | 0 < v 0}) :=
      ψ.continuousOn.isOpen_inter_preimage ψ.open_source (isOpen_lt continuous_const hproj)
    have hsub : ψ.source ∩ ψ ⁻¹' {v | 0 < v 0} ⊆ C :=
      fun w hw => (hψ w hw.1).mpr (le_of_lt hw.2)
    exact hfr.2 (mem_interior.mpr ⟨_, hsub, hopen, hy, hpos⟩)
  · intro h
    refine ⟨subset_closure hyC, fun hint => ?_⟩
    have hW : IsOpen (interior C ∩ ψ.source) := isOpen_interior.inter ψ.open_source
    have himg : IsOpen (ψ '' (interior C ∩ ψ.source)) :=
      ψ.isOpen_image_of_subset_source hW inter_subset_right
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp himg (ψ y) ⟨y, ⟨hint, hy⟩, rfl⟩
    set v : EuclideanSpace ℝ (Fin 1) := ψ y - (ε / 2) • EuclideanSpace.single 0 (1 : ℝ) with hv
    have hvb : v ∈ Metric.ball (ψ y) ε := by
      rw [Metric.mem_ball, dist_eq_norm, hv, sub_sub_cancel_left, norm_neg, norm_smul,
        PiLp.norm_single]
      simp [abs_of_pos hε]
      linarith
    obtain ⟨w, ⟨hwint, hwsrc⟩, hwv⟩ := hball hvb
    have hwC : w ∈ C := interior_subset hwint
    have hnn := (hψ w hwsrc).mp hwC
    rw [hwv, hv] at hnn
    simp [h] at hnn
    linarith

end Chart


section Atlas

variable {Base : Type*} [TopologicalSpace Base] {C : Set Base}
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) Base]

/-- For `x` in the model half-line range, `(𝓡∂ 1).symm x` has underlying vector `x`. -/
theorem val_symm_of_mem_range_EIM {x : EuclideanSpace ℝ (Fin 1)} (hx : x ∈ range (𝓡∂ 1)) :
    ((𝓡∂ 1).symm x).val = x := by
  obtain ⟨p, rfl⟩ := hx
  rw [ModelWithCorners.left_inv]
  rfl

/-- **Smooth coordinate changes** between two adapted half charts. -/
theorem contDiffOn_halfChart_transition_EIM
    {ψ₁ ψ₂ : OpenPartialHomeomorph Base (EuclideanSpace ℝ (Fin 1))}
    (h₁ : ψ₁ ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Base)
    (h₂ : ψ₂ ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Base)
    {hψ₁ : ∀ y ∈ ψ₁.source, (y ∈ C ↔ 0 ≤ ψ₁ y 0)} {hψ₂ : ∀ y ∈ ψ₂.source, (y ∈ C ↔ 0 ≤ ψ₂ y 0)}
    (y₀ y₀' : C) :
    ContDiffOn ℝ ∞ ((𝓡∂ 1) ∘ ((halfChart_EIM ψ₁ hψ₁ y₀).symm ≫ₕ halfChart_EIM ψ₂ hψ₂ y₀') ∘
        (𝓡∂ 1).symm)
      ((𝓡∂ 1).symm ⁻¹' ((halfChart_EIM ψ₁ hψ₁ y₀).symm ≫ₕ halfChart_EIM ψ₂ hψ₂ y₀').source ∩
        range (𝓡∂ 1)) := by
  have hg : ContDiffOn ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 1) => ψ₂ (ψ₁.symm x))
      (ψ₁.target ∩ ψ₁.symm ⁻¹' ψ₂.source) := by
    have h : ContMDiffOn (𝓡 1) (𝓡 1) ∞ (fun x : EuclideanSpace ℝ (Fin 1) => ψ₂ (ψ₁.symm x))
        (ψ₁.target ∩ ψ₁.symm ⁻¹' ψ₂.source) :=
      (contMDiffOn_of_mem_maximalAtlas h₂).comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h₁).mono inter_subset_left) (fun x hx => hx.2)
    exact contMDiffOn_iff_contDiffOn.mp h
  refine (hg.mono ?_).congr ?_
  · rintro x ⟨hx, hxr⟩
    have hval := val_symm_of_mem_range_EIM hxr
    have h1 : ((𝓡∂ 1).symm x) ∈ (halfChart_EIM ψ₁ hψ₁ y₀).target := hx.1
    have h2 : (((halfChart_EIM ψ₁ hψ₁ y₀).symm ((𝓡∂ 1).symm x) : C) : Base) ∈ ψ₂.source := hx.2
    have h1' : ((𝓡∂ 1).symm x).val ∈ ψ₁.target := h1
    rw [hval] at h1'
    refine ⟨h1', ?_⟩
    have := halfChart_symm_val_EIM (y₀ := y₀) (hψ := hψ₁) h1
    rw [hval] at this
    rw [mem_preimage, ← this]
    exact h2
  · rintro x ⟨hx, hxr⟩
    have hval := val_symm_of_mem_range_EIM hxr
    have h1 : ((𝓡∂ 1).symm x) ∈ (halfChart_EIM ψ₁ hψ₁ y₀).target := hx.1
    have h2 : (((halfChart_EIM ψ₁ hψ₁ y₀).symm ((𝓡∂ 1).symm x) : C) : Base) ∈ ψ₂.source := hx.2
    have hs := halfChart_symm_val_EIM (y₀ := y₀) (hψ := hψ₁) h1
    rw [hval] at hs
    change (halfChart_EIM ψ₂ hψ₂ y₀' ((halfChart_EIM ψ₁ hψ₁ y₀).symm ((𝓡∂ 1).symm x))).val = _
    rw [halfChart_val_EIM h2, hs]

end Atlas

section Cover

variable {Base : Type*} [TopologicalSpace Base] {C : Set Base}
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) Base]
  (hadapt : ∀ x : C, ∃ ψ : OpenPartialHomeomorph Base (EuclideanSpace ℝ (Fin 1)),
    ψ ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Base ∧ (x : Base) ∈ ψ.source ∧
      ∀ y ∈ ψ.source, (y ∈ C ↔ 0 ≤ ψ y 0))

/-- The adapted chart chosen at `x`. -/
def adaptedChart_EIM (x : C) : OpenPartialHomeomorph Base (EuclideanSpace ℝ (Fin 1)) :=
  (hadapt x).choose

theorem adaptedChart_mem_EIM (x : C) :
    adaptedChart_EIM hadapt x ∈ IsManifold.maximalAtlas (𝓡 1) ∞ Base :=
  (hadapt x).choose_spec.1

theorem adaptedChart_source_EIM (x : C) : (x : Base) ∈ (adaptedChart_EIM hadapt x).source :=
  (hadapt x).choose_spec.2.1

theorem adaptedChart_iff_EIM (x : C) :
    ∀ ⦃y⦄, y ∈ (adaptedChart_EIM hadapt x).source →
      (y ∈ C ↔ 0 ≤ adaptedChart_EIM hadapt x y 0) :=
  (hadapt x).choose_spec.2.2

/-- **The charted space of `↥C` by the adapted half charts** (a definition, not an instance). -/
abbrev chartedSpace_EIM : ChartedSpace (EuclideanHalfSpace 1) C where
  atlas := range fun x : C =>
    halfChart_EIM (adaptedChart_EIM hadapt x) (adaptedChart_iff_EIM hadapt x) x
  chartAt x := halfChart_EIM (adaptedChart_EIM hadapt x) (adaptedChart_iff_EIM hadapt x) x
  mem_chart_source x := adaptedChart_source_EIM hadapt x
  chart_mem_atlas x := ⟨x, rfl⟩

/-- **`↥C` is a smooth one-manifold with boundary.** -/
theorem isManifold_EIM :
    letI := chartedSpace_EIM hadapt
    IsManifold (𝓡∂ 1) ∞ C := by
  let _ := chartedSpace_EIM hadapt
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
  exact contDiffOn_halfChart_transition_EIM (adaptedChart_mem_EIM hadapt x)
    (adaptedChart_mem_EIM hadapt x') x x'


/-- **The inclusion `↥C → Base` is an immersion.** Route: in the adapted chart the inclusion is the
identity of the half-line (with the trivial complement). -/
theorem isImmersion_val_EIM :
    letI := chartedSpace_EIM hadapt
    Manifold.IsImmersion (𝓡∂ 1) (𝓡 1) ∞ (Subtype.val : C → Base) := by
  let _ := chartedSpace_EIM hadapt
  have : IsManifold (𝓡∂ 1) ∞ C := isManifold_EIM hadapt
  refine Manifold.IsImmersionOfComplement.isImmersion (F := Fin 0 → ℝ) fun x => ?_
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    (ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 1)) (Fin 0 → ℝ))
    (chartAt (EuclideanHalfSpace 1) x) (adaptedChart_EIM hadapt x) (mem_chart_source _ x)
    (adaptedChart_source_EIM hadapt x) (IsManifold.chart_mem_maximalAtlas x)
    (adaptedChart_mem_EIM hadapt x) (fun y hy => hy) ?_
  intro z hz
  have hz' : z ∈ (𝓡∂ 1).symm ⁻¹' (chartAt (EuclideanHalfSpace 1) x).target ∩ range (𝓡∂ 1) := by
    rwa [OpenPartialHomeomorph.extend_target] at hz
  have hzr : z ∈ range (𝓡∂ 1) := hz'.2
  have hval := val_symm_of_mem_range_EIM hzr
  have htgt : ((𝓡∂ 1).symm z).val ∈ (adaptedChart_EIM hadapt x).target := hz'.1
  rw [hval] at htgt
  have hs := halfChart_symm_val_EIM (y₀ := x) (hψ := adaptedChart_iff_EIM hadapt x) hz'.1
  rw [hval] at hs
  simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe_symm,
    OpenPartialHomeomorph.extend_coe, modelWithCornersSelf_coe, id_eq,
    ContinuousLinearEquiv.prodUnique_apply]
  change (adaptedChart_EIM hadapt x)
    ((((chartAt (EuclideanHalfSpace 1) x).symm ((𝓡∂ 1).symm z) : C) : Base)) = z
  have hs' : ((((chartAt (EuclideanHalfSpace 1) x).symm ((𝓡∂ 1).symm z) : C)) : Base) =
      (adaptedChart_EIM hadapt x).symm z := hs
  rw [hs', OpenPartialHomeomorph.right_inv _ htgt]


/-- **Boundary points of `↥C` are the frontier points of `C` in `Base`.** -/
theorem isBoundaryPoint_iff_frontier_EIM :
    letI := chartedSpace_EIM hadapt
    ∀ {y : C}, (𝓡∂ 1).IsBoundaryPoint y ↔ (y : Base) ∈ frontier C := by
  let _ := chartedSpace_EIM hadapt
  have _ : IsManifold (𝓡∂ 1) ∞ C := isManifold_EIM hadapt
  intro y
  have hy : (y : Base) ∈ (adaptedChart_EIM hadapt y).source := adaptedChart_source_EIM hadapt y
  rw [isBoundaryPoint_iff_coord_eq_zero (e := chartAt (EuclideanHalfSpace 1) y)
    (chart_mem_atlas _ y) (mem_chart_source _ y)]
  have h := halfChart_val_zero_EIM (hψ := adaptedChart_iff_EIM hadapt y) (y₀ := y) hy
  change (halfChart_EIM (adaptedChart_EIM hadapt y) (adaptedChart_iff_EIM hadapt y) y y).val 0 = 0 ↔
    _
  rw [h]
  exact (mem_frontier_iff_coord_eq_zero_EIM (adaptedChart_iff_EIM hadapt y) hy y.2).symm

end Cover


end GC.GraphManifold.Assembly.FC39P0
