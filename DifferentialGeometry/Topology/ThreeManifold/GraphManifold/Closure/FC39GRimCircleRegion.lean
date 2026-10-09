import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimRoundApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GRimBundleRestrict
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Piece
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# FC39 GROUP G, RIMBOX G8a: the final circle region from per-end corner charts

Lane FC39-RIMBOX-ROUND (G8a, split off from lane FC39-G-RIMBOXc's G8; frozen text
`build-logs/scratch/FC39-G-RIMBOX/TargetsHandleChart.lean` (D)). Input: for every actual endpoint `e`
a corner chart `κ e` of the row circle base on `(-3, 3)²` with ONE scale `lam e`, centred at the rim
base point, with target in `safe.cornerBase e ∩ GF.base`, in which the two active global face
functions read `-(lam x)`, `-(lam y)` and the other ones are negative (the corner clauses of G6).
Output: the final circle region

* `Base = ↥GF.base`; domain, projection, trivializations = the restriction of the row circle bundle
  (`CircleBundle.restrict*_GRIM`, G1);
* `defining l = GF.fn (faceIndex l) ∘ val` (`faceIndex = (Finite.equivFin Face).symm`);
* corners indexed by `Fin (Nat.card EdgeEnd)` (`endOfCorner = (Finite.equivFin EdgeEnd).symm`), the
  corner chart of `k` = `κ (endOfCorner k)` co-restricted to `GF.base` (`codRestrictOpens`) and
  restricted to `rimBox 2` (`restrictSource_GRND`), scale `lam (endOfCorner k)`;
* the rounding of the kernel `exists_rounding_relative_normalizedCorners_GRND` (larger charts = the
  co-restricted `κ e` on `rimBox 3`; disjoint targets since the safe corner bases are disjoint,
  `ProducerSafeNeighbourhoods.cornerBase_disjoint_GRND`);

with the restriction link (`ι = val`), the global face link V2 and the six identifications G8 needs.

DEVIATION (strengthening): the frozen hypothesis `hchart` (the labelled tube chart reads `lam • v`) is
not used and is dropped; the verbatim frozen form is kept below as an `example`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

/-! ## Restricting the source of a partial diffeomorphism -/

section Restrict

variable {E₁ E₂ H₁ H₂ M₁ M₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₁] [TopologicalSpace H₂]
  {I₁ : ModelWithCorners ℝ E₁ H₁} {I₂ : ModelWithCorners ℝ E₂ H₂}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [TopologicalSpace M₂] [ChartedSpace H₂ M₂]

/-- The restriction of a partial diffeomorphism to an open part `s` of its source. -/
def restrictSource_GRND (φ : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞) (s : Set M₁) (hs : IsOpen s)
    (hsub : s ⊆ φ.source) : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞ where
  toFun x := φ x
  invFun y := φ.symm y
  source := s
  target := φ.target ∩ φ.symm ⁻¹' s
  map_source' x hx := ⟨φ.toPartialEquiv.map_source (hsub hx), by
    change φ.toPartialEquiv.symm (φ.toPartialEquiv x) ∈ s
    rw [φ.toPartialEquiv.left_inv (hsub hx)]
    exact hx⟩
  map_target' _ hy := hy.2
  left_inv' _ hx := φ.toPartialEquiv.left_inv (hsub hx)
  right_inv' _ hy := φ.toPartialEquiv.right_inv hy.1
  open_source := hs
  open_target := φ.symm.contMDiffOn.continuousOn.isOpen_inter_preimage φ.open_target hs
  contMDiffOn_toFun := φ.contMDiffOn.mono hsub
  contMDiffOn_invFun := φ.symm.contMDiffOn.mono inter_subset_left

theorem restrictSource_apply_GRND (φ : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞) (s : Set M₁)
    (hs : IsOpen s) (hsub : s ⊆ φ.source) (x : M₁) : restrictSource_GRND φ s hs hsub x = φ x :=
  rfl

theorem restrictSource_source_GRND (φ : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞) (s : Set M₁)
    (hs : IsOpen s) (hsub : s ⊆ φ.source) : (restrictSource_GRND φ s hs hsub).source = s :=
  rfl

theorem mem_restrictSource_target_GRND {φ : PartialDiffeomorph I₁ I₂ M₁ M₂ ∞} {s : Set M₁}
    (hs : IsOpen s) (hsub : s ⊆ φ.source) {y : M₂} :
    y ∈ (restrictSource_GRND φ s hs hsub).target ↔ y ∈ φ '' s := by
  constructor
  · rintro ⟨hy, hys⟩
    exact ⟨φ.symm y, hys, φ.toPartialEquiv.right_inv hy⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨φ.toPartialEquiv.map_source (hsub hx), ?_⟩
    change φ.toPartialEquiv.symm (φ.toPartialEquiv x) ∈ s
    rw [φ.toPartialEquiv.left_inv (hsub hx)]
    exact hx

end Restrict

/-! ## Functions on an open subset of the base -/

section OpenBase

/-- The differential of `g ∘ val` on an open subset is the differential of `g`. -/
theorem mfderiv_comp_val_GRND {B : Type*} [TopologicalSpace B]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) B] (O : TopologicalSpace.Opens B) {g : B → ℝ}
    (hg : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ g O) (b : O) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun c : O => g c.val) b = mfderiv (𝓡 2) 𝓘(ℝ, ℝ) g b.val := by
  have hgd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) g b.val :=
    (hg.contMDiffAt (O.isOpen.mem_nhds b.2)).mdifferentiableAt (by simp)
  have hval : ContMDiff (𝓡 2) (𝓡 2) ∞ (Subtype.val : O → B) := contMDiff_subtype_val
  change mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (g ∘ Subtype.val) b = _
  rw [mfderiv_comp b hgd ((hval b).mdifferentiableAt (by simp)),
    DifferentialGeometry.mfderiv_subtype_val O b]
  rfl

end OpenBase

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-- The safe corner bases of distinct endpoints are disjoint (their saturated tubes have disjoint
closures and every base point is a projection). -/
theorem ProducerSafeNeighbourhoods.cornerBase_disjoint_GRND {Rw : FC39RowsV2 W E}
    (safe : ProducerSafeNeighbourhoods Rw) {e e' : Rw.edge.EdgeEnd} (h : e ≠ e') :
    Disjoint (safe.cornerBase e : Set Rw.circle.Base) (safe.cornerBase e') := by
  refine Set.disjoint_left.2 fun c hc hc' => ?_
  obtain ⟨x, rfl⟩ := Rw.circle.proj_surjective_GGFF c
  exact Set.disjoint_left.1 (safe.corner_closure_disjoint h) (subset_closure ⟨x, hc, rfl⟩)
    (subset_closure ⟨x, hc', rfl⟩)

/-- **G8a: the final circle region from per-end corner charts** (frozen text of RIMBOXc's (D), with
the unused hypothesis `hchart` dropped). -/
theorem FC39PreparedV2.exists_circleRegion_of_cornerCharts_GRND (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (lam : Pr.rows.edge.EdgeEnd → ℝ)
    (κ : Pr.rows.edge.EdgeEnd → PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) Pr.rows.circle.Base ∞)
    (hlam : ∀ e, 0 < lam e) (hsrc : ∀ e, (κ e).source = rimBox 3)
    (hcenter : ∀ e, κ e (0, 0) = Pr.rows.junctions.rimBase e.1)
    (htgt : ∀ e, (κ e).target ⊆ (safe.cornerBase e : Set _) ∩
      (Pr.globalFaces.base : Set Pr.rows.circle.Base))
    (hfirst : ∀ e, ∀ v ∈ rimBox 3,
      Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm (.vertical e.component)) (κ e v) =
        -(lam e * v.1))
    (hsecond : ∀ e, ∀ v ∈ rimBox 3,
      Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm
        (.horizontal (Pr.rows.junctions.horizontal e))) (κ e v) = -(lam e * v.2))
    (hother : ∀ e f v, f ≠ Pr.globalFaces.actualFace.symm (.vertical e.component) →
      f ≠ Pr.globalFaces.actualFace.symm (.horizontal (Pr.rows.junctions.horizontal e)) →
      v ∈ rimBox 3 → Pr.globalFaces.fn f (κ e v) < 0) :
    ∃ (circ : CircleRegion W) (L : CircleRestrictionLink Pr.rows.circle circ)
      (G : GlobalFaceLinkV2 Pr.globalFaces circ L)
      (endOfCorner : Fin circ.cornerCount ≃ Pr.rows.edge.EdgeEnd),
      (∀ k, circ.cornerScale k = lam (endOfCorner k)) ∧
      (∀ k v, v ∈ rimBox 2 → L.ι (circ.cornerChart k v) = κ (endOfCorner k) v) ∧
      (∀ k c, c ∈ (circ.cornerChart k).target ↔ L.ι c ∈ κ (endOfCorner k) '' rimBox 2) ∧
      (∀ k, G.faceOfDefining (circ.cornerFirst k) = .vertical (endOfCorner k).component) ∧
      (∀ k, G.faceOfDefining (circ.cornerSecond k) =
        .horizontal (Pr.rows.junctions.horizontal (endOfCorner k))) ∧
      (∀ k, L.ι (circ.cornerChart k (0, 0)) = Pr.rows.junctions.rimBase (endOfCorner k).1) := by
  classical
  have hFfin : Finite Pr.globalFaces.Face := Pr.globalFaces.finite
  have hEfin : Finite Pr.rows.edge.EdgeEnd := Finite.of_equiv _ Pr.rows.edgeModels.endpointEquiv
  have hσ : SigmaCompactSpace Pr.globalFaces.base :=
    Pr.rows.circle.sigmaCompactSpace_opens_GRND Pr.globalFaces.base
  have h23 : rimBox 2 ⊆ rimBox 3 := rimBox_mono (by norm_num)
  have h0 : ((0 : ℝ), (0 : ℝ)) ∈ rimBox 3 := zero_mem_rimBox_GRND (by norm_num)
  -- indices
  let faceIndex : Fin (Nat.card Pr.globalFaces.Face) ≃ Pr.globalFaces.Face :=
    (Finite.equivFin _).symm
  let endOfCorner : Fin (Nat.card Pr.rows.edge.EdgeEnd) ≃ Pr.rows.edge.EdgeEnd :=
    (Finite.equivFin _).symm
  -- defining functions on the base `GF.base`
  let f : Fin (Nat.card Pr.globalFaces.Face) → Pr.globalFaces.base → ℝ :=
    fun l c => Pr.globalFaces.fn (faceIndex l) c.val
  have hf : ∀ l, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f l) := fun l =>
    (Pr.globalFaces.smooth (faceIndex l)).comp_contMDiff contMDiff_subtype_val fun c => c.2
  have hdf : ∀ l (b : Pr.globalFaces.base),
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (f l) b =
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (Pr.globalFaces.fn (faceIndex l)) b.val := fun l b =>
    mfderiv_comp_val_GRND Pr.globalFaces.base (Pr.globalFaces.smooth (faceIndex l)) b
  have hreg : ∀ l b, f l b = 0 → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (f l) b ≠ 0 := fun l b hb => by
    rw [hdf]
    exact Pr.globalFaces.zero_regular _ _ b.2 hb
  -- the cornered base
  have hCB : Subtype.val '' {b : Pr.globalFaces.base | ∀ l, f l b ≤ 0} =
      Pr.rows.circle.cbase := by
    rw [Pr.globalFaces.base_eq]
    ext c
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨b.2, fun F => ?_⟩
      have := hb (faceIndex.symm F)
      simp only [f, Equiv.apply_symm_apply] at this
      exact this
    · rintro ⟨hc, hF⟩
      exact ⟨⟨c, hc⟩, fun l => hF _, rfl⟩
  have hCc : IsCompact {b : Pr.globalFaces.base | ∀ l, f l b ≤ 0} := by
    rw [Subtype.isCompact_iff, hCB]
    exact Pr.rows.circle.cbase_compact
  have hCpre : {b : Pr.globalFaces.base | ∀ l, f l b ≤ 0} =
      Subtype.val ⁻¹' Pr.rows.circle.cbase := by
    rw [← hCB, Subtype.val_injective.preimage_image]
  -- the corner charts
  have hne : ∀ e, Nonempty Pr.globalFaces.base := fun e =>
    ⟨⟨κ e (0, 0), (htgt e ((κ e).toPartialEquiv.map_source (by rw [hsrc e]; exact h0))).2⟩⟩
  let K : Fin (Nat.card Pr.rows.edge.EdgeEnd) →
      PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) Pr.globalFaces.base ∞ := fun k =>
    codRestrictOpens (κ (endOfCorner k)) Pr.globalFaces.base (hne (endOfCorner k))
  have hKsrc : ∀ k, (K k).source = rimBox 3 := fun k =>
    (codRestrictOpens_source _ _ _ fun _ hx => (htgt _ hx).2).trans (hsrc _)
  have hKval : ∀ k v, v ∈ rimBox 3 → ((K k v : Pr.globalFaces.base) : Pr.rows.circle.Base) =
      κ (endOfCorner k) v := fun k v hv =>
    codRestrictOpens_apply _ _ _
      (htgt _ ((κ (endOfCorner k)).toPartialEquiv.map_source (by rw [hsrc]; exact hv))).2
  have hKtgt : ∀ k, (K k).target = Subtype.val ⁻¹' (κ (endOfCorner k)).target := fun k =>
    codRestrictOpens_target _ _ _
  have hKdisj : Pairwise fun k k' => Disjoint (K k).target (K k').target := by
    intro k k' hkk
    rw [hKtgt, hKtgt]
    refine Set.disjoint_left.2 fun c hc hc' => ?_
    exact Set.disjoint_left.1
      (safe.cornerBase_disjoint_GRND (endOfCorner.injective.ne hkk)) (htgt _ hc).1 (htgt _ hc').1
  have h2K : ∀ k, rimBox 2 ⊆ (K k).source := fun k => by rw [hKsrc]; exact h23
  let cc : Fin (Nat.card Pr.rows.edge.EdgeEnd) →
      PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) Pr.globalFaces.base ∞ := fun k =>
    restrictSource_GRND (K k) (rimBox 2) (isOpen_rimBox_GRIM 2) (h2K k)
  -- the active faces of a corner
  let first : Fin (Nat.card Pr.rows.edge.EdgeEnd) → Fin (Nat.card Pr.globalFaces.Face) := fun k =>
    faceIndex.symm (Pr.globalFaces.actualFace.symm (.vertical (endOfCorner k).component))
  let second : Fin (Nat.card Pr.rows.edge.EdgeEnd) → Fin (Nat.card Pr.globalFaces.Face) := fun k =>
    faceIndex.symm (Pr.globalFaces.actualFace.symm
      (.horizontal (Pr.rows.junctions.horizontal (endOfCorner k))))
  have hfirstK : ∀ k v, v ∈ rimBox 3 → f (first k) (K k v) = -(lam (endOfCorner k) * v.1) := by
    intro k v hv
    change Pr.globalFaces.fn (faceIndex (faceIndex.symm _)) (K k v : Pr.rows.circle.Base) = _
    rw [Equiv.apply_symm_apply, hKval k v hv]
    exact hfirst _ v hv
  have hsecondK : ∀ k v, v ∈ rimBox 3 → f (second k) (K k v) = -(lam (endOfCorner k) * v.2) := by
    intro k v hv
    change Pr.globalFaces.fn (faceIndex (faceIndex.symm _)) (K k v : Pr.rows.circle.Base) = _
    rw [Equiv.apply_symm_apply, hKval k v hv]
    exact hsecond _ v hv
  have hotherK : ∀ k l v, l ≠ first k → l ≠ second k → v ∈ rimBox 3 → f l (K k v) < 0 := by
    intro k l v hl1 hl2 hv
    change Pr.globalFaces.fn (faceIndex l) (K k v : Pr.rows.circle.Base) < 0
    rw [hKval k v hv]
    exact hother _ _ v (fun h => hl1 (faceIndex.eq_symm_apply.2 h))
      (fun h => hl2 (faceIndex.eq_symm_apply.2 h)) hv
  have hcenterK : ∀ b l l', l ≠ l' → f l b = 0 → f l' b = 0 → ∃ k, b = cc k (0, 0) := by
    intro b l l' hll hl hl'
    obtain ⟨e, he, -⟩ := Pr.globalFaces.double_registered b.val b.2 (faceIndex l) (faceIndex l')
      (faceIndex.injective.ne hll) hl hl'
    refine ⟨endOfCorner.symm e, Subtype.ext ?_⟩
    change b.val = ((K (endOfCorner.symm e) (0, 0) : Pr.globalFaces.base) : Pr.rows.circle.Base)
    rw [hKval _ _ h0, Equiv.apply_symm_apply, hcenter, he]
  -- the rounding
  obtain ⟨r, hr1, hr2, hr3, hr4, hr5, -⟩ :=
    exists_rounding_relative_normalizedCorners_GRND f hf hreg rfl hCc cc K hKsrc
      (fun _ _ _ => rfl) hKdisj first second (fun k => lam (endOfCorner k))
      (fun k => hlam (endOfCorner k)) hfirstK hsecondK hotherK hcenterK
  -- the circle region
  let circ : CircleRegion W :=
    { Base := Pr.globalFaces.base
      domain := Pr.rows.circle.restrictDomain_GRIM Pr.globalFaces.base
      domain_interior := fun _ hx => Pr.rows.circle.domain_interior hx.fst
      proj := Pr.rows.circle.restrictProj_GRIM Pr.globalFaces.base
      proj_smooth := Pr.rows.circle.contMDiff_restrictProj_GRIM Pr.globalFaces.base
      proj_submersion := Pr.rows.circle.restrictProj_submersion_GRIM Pr.globalFaces.base
      neighborhood := Pr.rows.circle.restrictNeighborhood_GRIM Pr.globalFaces.base
      mem_neighborhood := Pr.rows.circle.mem_restrictNeighborhood_GRIM Pr.globalFaces.base
      trivialization := Pr.rows.circle.restrictTrivialization_GRIM Pr.globalFaces.base
      projection_trivialization :=
        Pr.rows.circle.restrictProjection_trivialization_GRIM Pr.globalFaces.base
      definingCount := Nat.card Pr.globalFaces.Face
      defining := f
      defining_smooth := hf
      defining_regular := hreg
      depth_le_two := fun b => by
        have h1 : (Finset.univ.filter fun l => f l b = 0).card =
            Set.ncard {l | f l b = 0} := by
          rw [← Set.ncard_coe_finset]
          congr 1
          ext l
          simp
        have h2 : faceIndex '' {l | f l b = 0} = {F | Pr.globalFaces.fn F b.val = 0} := by
          ext F
          constructor
          · rintro ⟨l, hl, rfl⟩
            exact hl
          · intro hF
            refine ⟨faceIndex.symm F, ?_, Equiv.apply_symm_apply _ _⟩
            change Pr.globalFaces.fn (faceIndex (faceIndex.symm F)) b.val = 0
            rw [Equiv.apply_symm_apply]
            exact hF
        rw [h1, ← Set.ncard_image_of_injective _ faceIndex.injective, h2]
        exact Pr.globalFaces.depth_le_two b.val b.2
      defining_independent := fun b l l' hll hl hl' => by
        rw [hdf l b, hdf l' b]
        exact Pr.globalFaces.double_independent b.val b.2 (faceIndex l) (faceIndex l')
          (faceIndex.injective.ne hll) hl hl'
      cornerBase := {b | ∀ l, f l b ≤ 0}
      cornerBase_eq := rfl
      cornerBase_compact := hCc
      cornerCount := Nat.card Pr.rows.edge.EdgeEnd
      cornerChart := cc
      cornerChart_source := fun _ => rfl
      cornerChart_disjoint := fun k k' hkk => (hKdisj hkk).mono (fun _ hc => hc.1)
        (fun _ hc => hc.1)
      cornerFirst := first
      cornerSecond := second
      corner_ne := fun k h => by
        have h' := Pr.globalFaces.actualFace.symm.injective (faceIndex.symm.injective h)
        cases h'
      cornerScale := fun k => lam (endOfCorner k)
      cornerScale_pos := fun k => hlam (endOfCorner k)
      chart_first := fun k v hv => hfirstK k v (h23 hv)
      chart_second := fun k v hv => hsecondK k v (h23 hv)
      chart_other := fun k l v hl1 hl2 hv => hotherK k l v hl1 hl2 (h23 hv)
      corner_center := hcenterK
      rounding := r
      rounding_smooth := hr1
      rounding_regular := hr2
      rounding_chart := hr3
      rounding_agree := hr4
      rounded_compact := hr5 }
  let L : CircleRestrictionLink Pr.rows.circle circ :=
    { region_eq := by
        change Subtype.val '' ((Pr.rows.circle.restrictProj_GRIM Pr.globalFaces.base) ⁻¹'
          {b : Pr.globalFaces.base | ∀ l, f l b ≤ 0}) = _
        rw [hCpre]
        exact Pr.rows.circle.region_restrict_GRIM _ Pr.globalFaces.cbase_subset
      ι := Subtype.val
      ι_isOpenEmbedding := Pr.rows.circle.isOpenEmbedding_val_GRIM _
      ι_smooth := Pr.rows.circle.contMDiff_val_GRIM _
      ι_mfderiv := Pr.rows.circle.mfderiv_val_bijective_GRIM _
      domain_eq := Pr.rows.circle.restrictDomain_eq_GRIM _
      proj_eq := Pr.rows.circle.restrictProj_eq_GRIM _ }
  let G : GlobalFaceLinkV2 Pr.globalFaces circ L :=
    { range_subset := by
        rintro _ ⟨c, rfl⟩
        exact c.2
      faceIndex := faceIndex
      defining_eq := fun _ _ => rfl }
  refine ⟨circ, L, G, endOfCorner, fun _ => rfl, fun k v hv => hKval k v (h23 hv),
    fun k c => ?_, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · change c ∈ (cc k).target ↔ (c : Pr.rows.circle.Base) ∈ κ (endOfCorner k) '' rimBox 2
    rw [mem_restrictSource_target_GRND]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, (hKval k v (h23 hv)).symm⟩
    · rintro ⟨v, hv, hvc⟩
      refine ⟨v, hv, Subtype.ext ?_⟩
      rw [hKval k v (h23 hv)]
      exact hvc
  · change Pr.globalFaces.actualFace (faceIndex (faceIndex.symm _)) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · change Pr.globalFaces.actualFace (faceIndex (faceIndex.symm _)) = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · change ((K k (0, 0) : Pr.globalFaces.base) : Pr.rows.circle.Base) = _
    rw [hKval k _ h0, hcenter]

/-- The verbatim frozen form (RIMBOXc's (D), with the unused `hchart`). -/
example (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (lam : Pr.rows.edge.EdgeEnd → ℝ)
    (κ : Pr.rows.edge.EdgeEnd → PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) (ℝ × ℝ) Pr.rows.circle.Base ∞)
    (hlam : ∀ e, 0 < lam e) (hsrc : ∀ e, (κ e).source = rimBox 3)
    (hchart : ∀ e, ∀ v ∈ rimBox 3, Pr.rows.labelledTubes.chart e (κ e v) = lam e • v)
    (hcenter : ∀ e, κ e (0, 0) = Pr.rows.junctions.rimBase e.1)
    (htgt : ∀ e, (κ e).target ⊆ (safe.cornerBase e : Set _) ∩
      (Pr.globalFaces.base : Set Pr.rows.circle.Base))
    (hfirst : ∀ e, ∀ v ∈ rimBox 3,
      Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm (.vertical e.component)) (κ e v) =
        -(lam e * v.1))
    (hsecond : ∀ e, ∀ v ∈ rimBox 3,
      Pr.globalFaces.fn (Pr.globalFaces.actualFace.symm
        (.horizontal (Pr.rows.junctions.horizontal e))) (κ e v) = -(lam e * v.2))
    (hother : ∀ e f v, f ≠ Pr.globalFaces.actualFace.symm (.vertical e.component) →
      f ≠ Pr.globalFaces.actualFace.symm (.horizontal (Pr.rows.junctions.horizontal e)) →
      v ∈ rimBox 3 → Pr.globalFaces.fn f (κ e v) < 0) :
    ∃ (circ : CircleRegion W) (L : CircleRestrictionLink Pr.rows.circle circ)
      (G : GlobalFaceLinkV2 Pr.globalFaces circ L)
      (endOfCorner : Fin circ.cornerCount ≃ Pr.rows.edge.EdgeEnd),
      (∀ k, circ.cornerScale k = lam (endOfCorner k)) ∧
      (∀ k v, v ∈ rimBox 2 → L.ι (circ.cornerChart k v) = κ (endOfCorner k) v) ∧
      (∀ k c, c ∈ (circ.cornerChart k).target ↔ L.ι c ∈ κ (endOfCorner k) '' rimBox 2) ∧
      (∀ k, G.faceOfDefining (circ.cornerFirst k) = .vertical (endOfCorner k).component) ∧
      (∀ k, G.faceOfDefining (circ.cornerSecond k) =
        .horizontal (Pr.rows.junctions.horizontal (endOfCorner k))) ∧
      (∀ k, L.ι (circ.cornerChart k (0, 0)) = Pr.rows.junctions.rimBase (endOfCorner k).1) :=
  (fun _ => Pr.exists_circleRegion_of_cornerCharts_GRND safe lam κ hlam hsrc hcenter htgt hfirst
    hsecond hother) hchart

end GC.GraphManifold.Assembly.FC39P0
