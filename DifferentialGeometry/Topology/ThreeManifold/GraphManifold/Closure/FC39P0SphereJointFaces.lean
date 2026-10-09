import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointRim

/-!
# FC39 producer, packet P0 (gate 1): the joint S³ configuration, the labelled faces of `C₁`

The labelled local faces of the circle base (`JunctionsV2.local_faces`, §5.6) for the S³ data:

* the labels `sphereFaceLabel : Bool × Bool → CircleFaceLabel` — `(false, σ)` the vertical face
  of the edge component `σ` (`ψ = 1` south, `ψ = 4` north), `(true, σ)` the horizontal residual
  face `σ` (`r = 1` the new slim end, `r = 4` the face of `Z₊`) — with the inverse
  `sphereLabelIndex`; the defining function of a label is CIRC-B's `circFaceFn` of its index
  (`sphereFaceFn`);
* the face sets in the base: `sphere_wholeVertical_eq` (the vertical face of a component is the
  tube over `{ψ = side value, r ∈ [1, 4]}`), `sphere_fibre_subset_tube_iff`,
  `sphere_fibre_subset_level_iff`, and per label `sphere_fibre_subset_face_iff`
  (`fibre c ⊆ face f ↔ φ_f c = 0` on `C₁`);
* `sphere_local_faces`: the field `local_faces`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open DifferentialGeometry.Topology.Manifold Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ## Fibres in tubes and level sets -/

/-- A circle fibre lies in a tube iff its base point lies in the base set. -/
theorem sphere_fibre_subset_tube_iff {c : sphereCircleBaseOpens} {V : Set sphereCircleBaseOpens} :
    sphereCircleBundle.fibre c ⊆ sphereCircleBundle.tube V ↔ c ∈ V := by
  constructor
  · intro h
    have hc : (c.val, (1 : Circle)) ∈ sphereCircleChart.source := by
      rw [sphereCircleChart_source]
      exact ⟨c.2, mem_univ _⟩
    have hmem : sphereCircleChart (c.val, 1) ∈ sphereCircleBundle.fibre c := by
      rw [sphereCircleBundle_fibre]
      exact ⟨1, rfl⟩
    obtain ⟨y, hyV, hy⟩ := h hmem
    have hy' : y = ⟨sphereCircleChart (c.val, 1), sphereCircleChart_mem_domain hc⟩ :=
      Subtype.ext hy
    have hp : sphereCircleProj y = c := by
      rw [hy']
      exact Subtype.ext (sphereCircleProj_chart hc)
    have hyV' : sphereCircleProj y ∈ V := hyV
    rw [hp] at hyV'
    exact hyV'
  · intro hc
    exact image_mono (preimage_mono (singleton_subset_iff.2 hc))

/-- A circle fibre lies in a height level iff the height of its radius is that level. -/
theorem sphere_fibre_subset_level_iff {c : sphereCircleBaseOpens} {h : ℝ} :
    sphereCircleBundle.fibre c ⊆ {x | sphereHeight x = h} ↔
      circHeight (sphereCircleEquiv c.val).2 = h := by
  rw [sphereCircleBundle_fibre]
  constructor
  · intro hs
    have h1 := hs ⟨1, rfl⟩
    change sphereHeight (sphereCircleChart (c.val, 1)) = h at h1
    rwa [sphereHeight_sphereCircleChart] at h1
  · rintro hh _ ⟨s, rfl⟩
    change sphereHeight (sphereCircleChart (c.val, s)) = h
    rw [sphereHeight_sphereCircleChart]
    exact hh

theorem circHeight_eq_residualHeight_iff {r : ℝ} (hr : 0 < r) {σ : Bool} :
    circHeight r = sphereResidualHeight σ ↔ r = circEndVal σ := by
  cases σ
  · exact stereoHeight_eq_neg_three_fifths_iff hr
  · exact stereoHeight_eq_three_fifths_iff hr

/-! ## The vertical faces of the two edge components -/

/-- The base set of the vertical face of the edge component `σ`: `ψ = 1` (`σ = false`) or `ψ = 4`
(`σ = true`), `r ∈ [1, 4]`. -/
def sphereVerticalBase (σ : Bool) : Set sphereCircleBaseOpens :=
  {c | (sphereCircleEquiv c.val).1 = circEndVal σ ∧ (sphereCircleEquiv c.val).2 ∈ Icc (1 : ℝ) 4}

theorem circEndVal_eq_cond (σ : Bool) : circEndVal σ = bif σ then 4 else 1 := by
  cases σ <;> rfl

theorem handleRadiusParam_involutive_JOINT (σ : Bool) (s : ℝ) :
    handleRadiusParam σ (handleRadiusParam σ s) = s := by
  cases σ <;> simp [handleRadiusParam]

/-- **The vertical face of the edge component `σ` is the tube over `sphereVerticalBase σ`.** -/
theorem sphere_wholeVertical_eq (σ : Bool) :
    sphereEdgeBundle.wholeVertical (edgeComponent (finTwoEquiv.symm σ)) =
      sphereCircleBundle.tube (sphereVerticalBase σ) := by
  ext x
  constructor
  · rintro ⟨y, ⟨hyC, hyh⟩, rfl⟩
    change edgeProj y ∈ range (edgeInterval (finTwoEquiv (finTwoEquiv.symm σ))) at hyC
    rw [Equiv.apply_symm_apply] at hyC
    obtain ⟨t, ht⟩ := hyC
    have hrim : y.val ∈ sphereEdgeBundle.rim (edgeInterval σ t) := ⟨y, ⟨ht.symm, hyh⟩, rfl⟩
    rw [sphereRim_fibre _ (range_edgeInterval_subset σ ⟨t, rfl⟩)] at hrim
    refine (sphere_fibre_subset_tube_iff.2 ?_) hrim
    change (sphereCircleEquiv ((sphereRimBase (edgeInterval σ t) : sphereCircleBaseOpens) :
      E2)).1 = circEndVal σ ∧ (sphereCircleEquiv ((sphereRimBase (edgeInterval σ t) :
        sphereCircleBaseOpens) : E2)).2 ∈ Icc (1 : ℝ) 4
    rw [sphereRimBase_interval, ContinuousLinearEquiv.apply_symm_apply]
    exact ⟨(circEndVal_eq_cond σ).symm,
      cycleHandleRadius_mem_Icc_CIRCA (handleRadiusParam_mem_Icc σ t.2)⟩
  · rintro ⟨y, hyV, rfl⟩
    change sphereCircleProj y ∈ sphereVerticalBase σ at hyV
    obtain ⟨hψ, hr⟩ := hyV
    obtain ⟨⟨s, hs⟩, hsr, -⟩ := cycleHandleRadius_inverse hr
    let t : Icc (0 : ℝ) 1 := ⟨handleRadiusParam σ s, handleRadiusParam_mem_Icc σ hs⟩
    have hc : sphereCircleProj y = sphereRimBase (edgeInterval σ t) := by
      apply Subtype.ext
      rw [sphereRimBase_interval]
      apply sphereCircleEquiv.injective
      rw [ContinuousLinearEquiv.apply_symm_apply]
      refine Prod.ext ?_ ?_
      · rw [hψ, circEndVal_eq_cond]
      · change _ = cycleHandleRadius (handleRadiusParam σ (handleRadiusParam σ s))
        rw [handleRadiusParam_involutive_JOINT, hsr]
    have hfib : y.val ∈ sphereCircleBundle.fibre (sphereRimBase (edgeInterval σ t)) :=
      ⟨y, hc, rfl⟩
    rw [← sphereRim_fibre _ (range_edgeInterval_subset σ ⟨t, rfl⟩)] at hfib
    obtain ⟨z, ⟨hz1, hz2⟩, hzy⟩ := hfib
    refine ⟨z, ⟨?_, hz2⟩, hzy⟩
    change edgeProj z ∈ range (edgeInterval (finTwoEquiv (finTwoEquiv.symm σ)))
    rw [Equiv.apply_symm_apply]
    exact ⟨t, hz1.symm⟩

/-! ## The labels -/

/-- The registry of the two actual edge base components. -/
def sphereComponentEquiv : Fin 2 ⊕ Fin 0 ≃ ActualComponent edgeCbase :=
  Equiv.ofBijective edgeComponentFun edgeComponentFun_bijective

/-- The side of an actual edge base component (`false` south, `true` north). -/
def sphereComponentSide (C : ActualComponent edgeCbase) : Bool :=
  Sum.elim (fun i => finTwoEquiv i) (fun j => j.elim0) (sphereComponentEquiv.symm C)

theorem sphereComponentSide_edgeComponent (σ : Bool) :
    sphereComponentSide (edgeComponent (finTwoEquiv.symm σ)) = σ := by
  have h : sphereComponentEquiv.symm (edgeComponent (finTwoEquiv.symm σ)) =
      .inl (finTwoEquiv.symm σ) :=
    sphereComponentEquiv.symm_apply_eq.2 rfl
  rw [sphereComponentSide, h, Sum.elim_inl, Equiv.apply_symm_apply]

theorem edgeComponent_sphereComponentSide (C : ActualComponent edgeCbase) :
    edgeComponent (finTwoEquiv.symm (sphereComponentSide C)) = C := by
  obtain ⟨k, rfl⟩ := sphereComponentEquiv.surjective C
  rcases k with i | j
  · rw [sphereComponentSide, Equiv.symm_apply_apply, Sum.elim_inl, Equiv.symm_apply_apply]
    rfl
  · exact j.elim0

/-- **The labels of the four faces of `C₁`**: `(false, σ)` the vertical face of the edge
component `σ`, `(true, σ)` the residual face `σ`. -/
def sphereFaceLabel :
    Bool × Bool → CircleFaceLabel sphereSlimPieces.ResidualFace sphereEdgeBundle.EdgeBaseComponent
  | (false, σ) => .vertical (edgeComponent (finTwoEquiv.symm σ))
  | (true, σ) => .horizontal (sphereResidual σ)

/-- The index of a label. -/
def sphereLabelIndex :
    CircleFaceLabel sphereSlimPieces.ResidualFace sphereEdgeBundle.EdgeBaseComponent → Bool × Bool
  | .horizontal F => (true, sphereResidualEquiv.symm F)
  | .vertical C => (false, sphereComponentSide C)

theorem sphereLabelIndex_label (k : Bool × Bool) : sphereLabelIndex (sphereFaceLabel k) = k := by
  rcases k with ⟨_ | _, σ⟩
  · change (false, sphereComponentSide (edgeComponent (finTwoEquiv.symm σ))) = (false, σ)
    rw [sphereComponentSide_edgeComponent]
  · change (true, sphereResidualEquiv.symm (sphereResidualEquiv σ)) = (true, σ)
    rw [Equiv.symm_apply_apply]

theorem sphereFaceLabel_index
    (f : CircleFaceLabel sphereSlimPieces.ResidualFace sphereEdgeBundle.EdgeBaseComponent) :
    sphereFaceLabel (sphereLabelIndex f) = f := by
  rcases f with F | C
  · change CircleFaceLabel.horizontal (sphereResidualEquiv (sphereResidualEquiv.symm F)) = _
    rw [Equiv.apply_symm_apply]
  · change CircleFaceLabel.vertical (edgeComponent (finTwoEquiv.symm (sphereComponentSide C))) = _
    exact congrArg CircleFaceLabel.vertical (edgeComponent_sphereComponentSide C)

theorem sphereFaceLabel_injective : Injective sphereFaceLabel := fun k k' h => by
  rw [← sphereLabelIndex_label k, h, sphereLabelIndex_label]

/-- **The defining function of a label**: CIRC-B's `circFaceFn` of its index. -/
def sphereFaceFn
    (f : CircleFaceLabel sphereSlimPieces.ResidualFace sphereEdgeBundle.EdgeBaseComponent) :
    sphereCircleBaseOpens → ℝ :=
  circFaceFn (sphereLabelIndex f).1 (sphereLabelIndex f).2

theorem sphereFaceFn_label (k : Bool × Bool) : sphereFaceFn (sphereFaceLabel k) = circFaceFn k.1 k.2 := by
  rw [sphereFaceFn, sphereLabelIndex_label]

/-- **The face of a label in the base, on `C₁`**: `fibre c ⊆ face (label k) ↔ φ_k c = 0`. -/
theorem sphere_fibre_subset_face_iff {k : Bool × Bool} {c : sphereCircleBaseOpens}
    (hc : c ∈ sphereCircleCbase) :
    sphereCircleBundle.fibre c ⊆ circleFaceSet sphereSlimPieces sphereEdgeBundle (sphereFaceLabel k) ↔
      circFaceFn k.1 k.2 c = 0 := by
  rcases k with ⟨_ | _, σ⟩
  · change sphereCircleBundle.fibre c ⊆
      sphereEdgeBundle.wholeVertical (edgeComponent (finTwoEquiv.symm σ)) ↔ _
    rw [sphere_wholeVertical_eq, sphere_fibre_subset_tube_iff, circFaceFn_eq_zero_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hc.2⟩⟩
  · change sphereCircleBundle.fibre c ⊆ sphereSlimPieces.residualSet (sphereResidual σ) ↔ _
    rw [residualSet_sphereResidual, sphere_fibre_subset_level_iff, circFaceFn_eq_zero_iff]
    exact circHeight_eq_residualHeight_iff (circCoordL_pos true c)

/-! ## `local_faces` -/

theorem mem_sphereCircleCbase_iff_faceFn {c : sphereCircleBaseOpens} :
    c ∈ sphereCircleCbase ↔ ∀ k : Bool × Bool, circFaceFn k.1 k.2 c ≤ 0 := by
  rw [sphereCircleCbase_eq]
  constructor
  · intro h k
    have := h (circFaceEquiv k)
    rwa [circDefining_face] at this
  · intro h l
    rw [← circFaceEquiv.apply_symm_apply l, circDefining_face]
    exact h _

/-- The open set where every defining function not vanishing at `c` stays negative. -/
def sphereFaceNbhd (c : sphereCircleBaseOpens) : TopologicalSpace.Opens sphereCircleBaseOpens :=
  ⟨{c' | ∀ k : Bool × Bool, circFaceFn k.1 k.2 c = 0 ∨ circFaceFn k.1 k.2 c' < 0}, by
    have h : {c' : sphereCircleBaseOpens | ∀ k : Bool × Bool,
        circFaceFn k.1 k.2 c = 0 ∨ circFaceFn k.1 k.2 c' < 0} =
        ⋂ k : Bool × Bool, {c' | circFaceFn k.1 k.2 c = 0 ∨ circFaceFn k.1 k.2 c' < 0} := by
      ext c'
      simp only [mem_iInter, mem_ofPred_eq]
    rw [h]
    refine isOpen_iInter_of_finite fun k => ?_
    by_cases hk : circFaceFn k.1 k.2 c = 0
    · simp only [hk, true_or, ofPred_true]
      exact isOpen_univ
    · simp only [hk, false_or]
      exact isOpen_lt (contMDiff_circFaceFn k.1 k.2).continuous continuous_const⟩

/-- **`local_faces` for the S³ data**: near every frontier point of `C₁` the active labelled faces
(one or two: one per axis), with the defining functions `circFaceFn`. -/
theorem sphere_local_faces : ∀ c ∈ frontier sphereCircleCbase,
    ∃ U : TopologicalSpace.Opens sphereCircleBaseOpens, c ∈ U ∧
      ∃ (L : Finset (CircleFaceLabel sphereSlimPieces.ResidualFace
          sphereEdgeBundle.EdgeBaseComponent))
        (φ : CircleFaceLabel sphereSlimPieces.ResidualFace sphereEdgeBundle.EdgeBaseComponent →
          sphereCircleBaseOpens → ℝ),
        1 ≤ L.card ∧ L.card ≤ 2 ∧
        (∀ f ∈ L, ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ (φ f) U ∧ φ f c = 0 ∧
          {c' | c' ∈ U ∧ c' ∈ sphereCircleCbase ∧ φ f c' = 0} =
            {c' | c' ∈ U ∧ c' ∈ sphereCircleCbase ∧
              sphereCircleBundle.fibre c' ⊆ circleFaceSet sphereSlimPieces sphereEdgeBundle f}) ∧
        (Surjective fun w : TangentSpace (𝓡 2) c =>
          fun f : L => mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (φ f) c w) ∧
        sphereCircleCbase ∩ U = {c' | c' ∈ U ∧ ∀ f ∈ L, φ f c' ≤ 0} := by
  classical
  intro c hc
  have hcC : c ∈ sphereCircleCbase := isCompact_sphereCircleCbase.isClosed.frontier_subset hc
  have hcle := mem_sphereCircleCbase_iff_faceFn.1 hcC
  let K : Finset (Bool × Bool) := Finset.univ.filter fun k => circFaceFn k.1 k.2 c = 0
  have hK : ∀ {k}, k ∈ K ↔ circFaceFn k.1 k.2 c = 0 := by
    intro k
    simp only [K, Finset.mem_filter, Finset.mem_univ, true_and]
  let L := K.image sphereFaceLabel
  have hL : ∀ {f}, f ∈ L ↔ ∃ k, circFaceFn k.1 k.2 c = 0 ∧ sphereFaceLabel k = f := by
    intro f
    simp only [L, Finset.mem_image, hK]
  have hKinj : ∀ {k k'}, k ∈ K → k' ∈ K → k.1 = k'.1 → k = k' := by
    intro k k' hk hk' h1
    have e := circFaceFn_eq_zero_iff.1 (hK.1 hk)
    have e' := circFaceFn_eq_zero_iff.1 (hK.1 hk')
    rw [h1] at e
    have h2 : circEndVal k.2 = circEndVal k'.2 := e.symm.trans e'
    have h2' : k.2 = k'.2 := by
      rcases hk2 : k.2 with _ | _ <;> rcases hk2' : k'.2 with _ | _ <;>
        rw [hk2, hk2'] at h2 <;> norm_num [circEndVal] at h2
    exact Prod.ext h1 h2'
  have hcU : c ∈ sphereFaceNbhd c := fun k => (hcle k).eq_or_lt
  refine ⟨sphereFaceNbhd c, hcU, L, sphereFaceFn, ?_, ?_, ?_, ?_, ?_⟩
  · -- at least one active face
    rw [Finset.card_image_of_injective _ sphereFaceLabel_injective, Nat.one_le_iff_ne_zero,
      Ne, Finset.card_eq_zero]
    intro hK0
    have hall : ∀ k : Bool × Bool, circFaceFn k.1 k.2 c < 0 := by
      intro k
      refine (hcle k).lt_of_ne fun h0 => ?_
      have hk : k ∈ K := hK.2 h0
      rw [hK0] at hk
      exact Finset.notMem_empty k hk
    have hsub : (sphereFaceNbhd c : Set sphereCircleBaseOpens) ⊆ sphereCircleCbase := by
      intro c' hc'
      refine mem_sphereCircleCbase_iff_faceFn.2 fun k => ?_
      rcases hc' k with h | h
      · exact absurd h (hall k).ne
      · exact h.le
    exact hc.2 (interior_maximal hsub (sphereFaceNbhd c).isOpen hcU)
  · -- at most two: one per axis
    refine (Finset.card_image_le).trans ?_
    calc K.card ≤ (Finset.univ : Finset Bool).card :=
          Finset.card_le_card_of_injOn Prod.fst (fun _ _ => Finset.mem_univ _)
            (fun k hk k' hk' h => hKinj hk hk' h)
      _ = 2 := rfl
  · intro f hf
    obtain ⟨k, hk0, rfl⟩ := hL.1 hf
    rw [sphereFaceFn_label]
    refine ⟨(contMDiff_circFaceFn k.1 k.2).contMDiffOn, hk0, ?_⟩
    ext c'
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hU, hC, h0⟩
      exact ⟨hU, hC, (sphere_fibre_subset_face_iff hC).2 h0⟩
    · rintro ⟨hU, hC, h0⟩
      exact ⟨hU, hC, (sphere_fibre_subset_face_iff hC).1 h0⟩
  · -- the active differentials are jointly onto
    intro g
    let gr : L → ℝ := fun f => g f
    let α : Bool × Bool → ℝ := fun k => -circSlackDeriv k.1 k.2 (circCoordL k.1 c.val)
    have hα : ∀ k, α k ≠ 0 := fun k =>
      neg_ne_zero.2 (circSlackDeriv_ne_zero _ _ (circCoordL_pos k.1 c))
    let pick : Bool → ℝ := fun a =>
      if h : ∃ f ∈ L, (sphereLabelIndex f).1 = a then
        gr ⟨h.choose, h.choose_spec.1⟩ / α (sphereLabelIndex h.choose)
      else 0
    refine ⟨sphereCircleEquiv.symm (pick false, pick true), ?_⟩
    funext ⟨f, hf⟩
    obtain ⟨k, hk0, rfl⟩ := hL.1 hf
    have hex : ∃ f ∈ L, (sphereLabelIndex f).1 = k.1 :=
      ⟨sphereFaceLabel k, hf, by rw [sphereLabelIndex_label]⟩
    have hch : sphereLabelIndex hex.choose = k := by
      obtain ⟨hmem, hfst⟩ := hex.choose_spec
      obtain ⟨k', hk'0, hk'eq⟩ := hL.1 hmem
      rw [← hk'eq, sphereLabelIndex_label] at hfst ⊢
      exact hKinj (hK.2 hk'0) (hK.2 hk0) hfst
    have hchoose : hex.choose = sphereFaceLabel k := by
      rw [← sphereFaceLabel_index hex.choose, hch]
    have hpick : pick k.1 = gr ⟨sphereFaceLabel k, hf⟩ / α k := by
      simp only [pick, dite_eq_left hex]
      have e1 : gr ⟨hex.choose, hex.choose_spec.1⟩ = gr ⟨sphereFaceLabel k, hf⟩ :=
        congrArg gr (Subtype.ext hchoose)
      rw [e1, hch]
    change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (sphereFaceFn (sphereFaceLabel k)) c
      (sphereCircleEquiv.symm (pick false, pick true)) = g ⟨sphereFaceLabel k, hf⟩
    rw [sphereFaceFn_label, (hasMFDerivAt_circFaceFn k.1 k.2 c).mfderiv]
    change α k * circCoordL k.1 (sphereCircleEquiv.symm (pick false, pick true)) = _
    rw [circCoordL_symm]
    have hif : (if k.1 then pick true else pick false) = pick k.1 := by
      rcases k.1 with _ | _ <;> rfl
    rw [hif, hpick, mul_div_cancel₀ _ (hα k)]
  · -- the base near `c` is cut out by the active faces
    ext c'
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨hC, hU⟩
      refine ⟨hU, fun f hf => ?_⟩
      obtain ⟨k, -, rfl⟩ := hL.1 hf
      rw [sphereFaceFn_label]
      exact mem_sphereCircleCbase_iff_faceFn.1 hC k
    · rintro ⟨hU, hall⟩
      refine ⟨mem_sphereCircleCbase_iff_faceFn.2 fun k => ?_, hU⟩
      rcases hU k with h | h
      · have := hall (sphereFaceLabel k) (hL.2 ⟨k, h, rfl⟩)
        rwa [sphereFaceFn_label] at this
      · exact h.le

end GC.GraphManifold.Assembly.FC39P0
