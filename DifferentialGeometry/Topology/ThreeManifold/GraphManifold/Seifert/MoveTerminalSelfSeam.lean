import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveTerminal
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ContractAlongPresentation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.UnionGeometry

/-!
# The centre with a self-seam

The three sides of a pants with one solid arm and one self-seam exhaust its ports. Connectedness
then forces these two pieces to exhaust the closed presentation. Selected contraction glues the
arm while preserving the two sides of the self-seam. The cone order is at least two, and the
corresponding annulus with one cone is good by filled-block detection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count)) (K : Finset (Fin T.pairing.count))
  (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
  (hext : ∀ i, T.externalPiece i ∉ S)

theorem selectedLocal_quotient_smooth :
    letI := T.restrictAlongChartedSpace S K hK hext
    ContMDiff (T.subCarrier S).model (modelWithCornersEuclideanHalfSpace 3) ∞
      (T.restrictAlongPairing S K hK).quotientMap := by
  let := T.restrictAlongChartedSpace S K hK hext
  apply contMDiffOn_univ.mp
  apply T.contMDiffOn_restrictAlong_of_comp S K hK hext (T.subCarrier S).model
    (T.restrictAlongPairing S K hK).quotientMap Set.univ
  · exact (T.restrictAlongPairing S K hK).quotientMap.continuous.continuousOn
  · exact (T.quotient_smooth.comp contMDiff_subtype_val).contMDiffOn

theorem selectedLocal_quotient_mfderiv_bijective (x : (T.subCarrier S).Carrier) :
    letI := T.restrictAlongChartedSpace S K hK hext
    Function.Bijective (mfderiv (T.subCarrier S).model
      (modelWithCornersEuclideanHalfSpace 3)
        (T.restrictAlongPairing S K hK).quotientMap x) := by
  let := T.restrictAlongChartedSpace S K hK hext
  let C := T.restrictAlongCarrier S K hK hext
  let q := (T.restrictAlongPairing S K hK).quotientMap
  let f := T.restrictAlongMap S K hK
  have hq := (T.selectedLocal_quotient_smooth S K hK hext).mdifferentiableAt
    (x := x) (by simp)
  have hf := (T.contMDiff_restrictAlongMap S K hK hext).mdifferentiableAt
    (x := q x) (by simp)
  have hcomp := mfderiv_comp x hf hq
  have hb := T.mfderiv_restrictAlongMap_bijective S K hK hext (q x)
  have hc : Function.Bijective
      (mfderiv (T.subCarrier S).model W.model (f ∘ q) x) :=
    T.mfderiv_sub_cutMap_bijective S x
  rw [hcomp] at hc
  constructor
  · intro v w hvw
    apply hc.1
    change mfderiv C.model W.model f (q x) (mfderiv (T.subCarrier S).model C.model q x v) =
      mfderiv C.model W.model f (q x) (mfderiv (T.subCarrier S).model C.model q x w)
    rw [hvw]
  · intro v
    obtain ⟨w, hw⟩ := hc.2 (mfderiv C.model W.model f (q x) v)
    exact ⟨w, hb.1 hw⟩

theorem selectedLocal_seamPatch_apply {k : Fin T.pairing.count} (hk : k ∈ K)
    {q : (T.restrictAlongPairing S K hK).QuotientSpace}
    (hq : q ∈ (T.restrictAlongSeamPatch S K hK hk).source) :
    T.restrictAlongSeamPatch S K hK hk q = T.restrictAlongMap S K hK q := by
  let f := T.restrictAlongMap S K hK
  let V : TopologicalSpace.Opens W.Carrier := ⟨(T.seam k).target, (T.seam k).open_target⟩
  let U : TopologicalSpace.Opens (T.restrictAlongPairing S K hK).QuotientSpace :=
    ⟨f ⁻¹' V, V.isOpen.preimage (T.continuous_restrictAlongMap S K hK)⟩
  let e : U ≃ₜ V := T.restrictAlongSeamHomeomorph S K hK hk
  have hv : Nonempty V := ⟨⟨T.seamTorus k 1, T.seamTorus_mem_seamCollar k 1⟩⟩
  have hu : Nonempty U := hv.map e.symm
  have hqs : q ∈ U := by
    change q ∈ (T.restrictAlongMap S K hK) ⁻¹' (T.seam k).target
    rwa [← T.restrictAlongSeamPatch_source S K hK hk]
  change (V.openPartialHomeomorphSubtypeCoe hv)
    (e (((U.openPartialHomeomorphSubtypeCoe hu).symm q))) = f q
  change f (((U.openPartialHomeomorphSubtypeCoe hu).symm q)).val = f q
  congr 1
  apply (U.openPartialHomeomorphSubtypeCoe hu).right_inv
  rw [TopologicalSpace.Opens.openPartialHomeomorphSubtypeCoe_target]
  exact hqs

def selectedLocal_seamPatchDiffeomorph {k : Fin T.pairing.count} (hk : k ∈ K) :
    letI := T.restrictAlongChartedSpace S K hK hext
    PartialDiffeomorph (modelWithCornersEuclideanHalfSpace 3) W.model
      (T.restrictAlongPairing S K hK).QuotientSpace W.Carrier ∞ := by
  let := T.restrictAlongChartedSpace S K hK hext
  let e := T.restrictAlongSeamPatch S K hK hk
  refine { e.toPartialEquiv with
    open_source := e.open_source
    open_target := e.open_target
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := ?_ }
  · exact (T.contMDiff_restrictAlongMap S K hK hext).contMDiffOn.congr
      (fun q hq => T.selectedLocal_seamPatch_apply S K hK hk hq)
  · apply T.contMDiffOn_restrictAlong_of_comp S K hK hext W.model
      e.symm e.target e.continuousOn_invFun
    apply contMDiffOn_id.congr
    intro y hy
    change T.restrictAlongMap S K hK (e.symm y) = y
    rw [← T.selectedLocal_seamPatch_apply S K hK hk (e.map_target hy)]
    exact e.right_inv hy

def selectedLocal_seam {k : Fin T.pairing.count} (hk : k ∈ K) :
    letI := T.restrictAlongChartedSpace S K hK hext
    PartialDiffeomorph signedCollarModel (modelWithCornersEuclideanHalfSpace 3)
      (Torus × ℝ) (T.restrictAlongPairing S K hK).QuotientSpace ∞ := by
  let := T.restrictAlongChartedSpace S K hK hext
  exact (T.seam k).trans (T.selectedLocal_seamPatchDiffeomorph S K hK hext hk).symm

theorem selectedLocal_seam_source {k : Fin T.pairing.count} (hk : k ∈ K) :
    letI := T.restrictAlongChartedSpace S K hK hext
    (T.selectedLocal_seam S K hK hext hk).source = signedCollarSource := by
  let := T.restrictAlongChartedSpace S K hK hext
  change (T.seam k).source ∩ (T.seam k) ⁻¹'
    (T.restrictAlongSeamPatch S K hK hk).target = signedCollarSource
  rw [T.restrictAlongSeamPatch_target S K hK hk]
  ext p
  constructor
  · intro hp
    exact (T.seam_source k) ▸ hp.1
  · intro hp
    have hs : p ∈ (T.seam k).source := (T.seam_source k).symm ▸ hp
    exact ⟨hs, (T.seam k).map_source hs⟩

theorem selectedLocal_seam_ambient {k : Fin T.pairing.count} (hk : k ∈ K)
    {p : Torus × ℝ} (hp : p ∈ signedCollarSource) :
    letI := T.restrictAlongChartedSpace S K hK hext
    T.restrictAlongMap S K hK (T.selectedLocal_seam S K hK hext hk p) =
      T.seam k p := by
  let := T.restrictAlongChartedSpace S K hK hext
  let e := T.restrictAlongSeamPatch S K hK hk
  have ht : T.seam k p ∈ e.target := by
    rw [T.restrictAlongSeamPatch_target S K hK hk]
    exact (T.seam k).map_source ((T.seam_source k).symm ▸ hp)
  change T.restrictAlongMap S K hK (e.symm (T.seam k p)) = T.seam k p
  rw [← T.selectedLocal_seamPatch_apply S K hK hk (e.map_target ht)]
  exact e.right_inv ht

theorem selectedLocal_quotient_oriented :
    letI := T.restrictAlongChartedSpace S K hK hext
    letI := T.restrictAlong_isManifold S K hK hext
    ∀ x : (T.subCarrier S).Carrier,
      ∃ L : TangentSpace (T.subCarrier S).model x ≃ₗ[ℝ]
          TangentSpace (modelWithCornersEuclideanHalfSpace 3)
            ((T.restrictAlongPairing S K hK).quotientMap x),
        (∀ v, L v = mfderiv (T.subCarrier S).model
          (modelWithCornersEuclideanHalfSpace 3)
          (T.restrictAlongPairing S K hK).quotientMap x v) ∧
        Orientation.map (Fin 3) L ((T.subCarrier S).orientation.orientation x) =
          (T.restrictAlongCarrier S K hK hext).orientation.orientation
            ((T.restrictAlongPairing S K hK).quotientMap x) := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  intro x
  let q := (T.restrictAlongPairing S K hK).quotientMap
  let f := T.restrictAlongMap S K hK
  let I := modelWithCornersEuclideanHalfSpace 3
  let D := (Manifold.differentialEquivOfBijective (T.subCarrier S).model I q
    (T.selectedLocal_quotient_mfderiv_bijective S K hK hext) x).toLinearEquiv
  let N := (Manifold.differentialEquivOfBijective I W.model f
    (T.mfderiv_restrictAlongMap_bijective S K hK hext) (q x)).toLinearEquiv
  obtain ⟨M, hM, hoM⟩ := T.isOrientedFold_cutMap.restrict T.quotient_smooth (T.subPiece S) x
  have hN : Orientation.map (Fin 3) N
      ((T.restrictAlongCarrier S K hK hext).orientation.orientation (q x)) =
        W.orientation.orientation (f (q x)) :=
    Manifold.orientation_map_manifoldOrientationPullback I W.model
      finrank_euclideanSpace_fin f (T.contMDiff_restrictAlongMap S K hK hext)
      (T.mfderiv_restrictAlongMap_bijective S K hK hext) W.orientation (q x)
  have hDM : D.trans N = M := by
    apply LinearEquiv.ext
    intro v
    have hc := mfderiv_comp x
      ((T.contMDiff_restrictAlongMap S K hK hext).mdifferentiableAt (by simp))
      ((T.selectedLocal_quotient_smooth S K hK hext).mdifferentiableAt (by simp))
    exact (congrArg (fun L => L v) hc).symm.trans (hM v).symm
  refine ⟨D, fun v => rfl, ?_⟩
  apply (Orientation.map (Fin 3) N).injective
  have h1 := orientation_map_trans_fin_three D N ((T.subCarrier S).orientation.orientation x)
  exact h1.symm.trans ((congrArg
    (fun L => Orientation.map (Fin 3) L ((T.subCarrier S).orientation.orientation x))
    hDM).trans (hoM.trans hN.symm))

theorem selectedLocal_interior_local {x : (T.subCarrier S).Carrier}
    (hx : (T.subCarrier S).model.IsInteriorPoint x) :
    letI := T.restrictAlongChartedSpace S K hK hext
    letI := T.restrictAlong_isManifold S K hK hext
    IsLocalDiffeomorphAt (T.subCarrier S).model (modelWithCornersEuclideanHalfSpace 3) ∞
      (T.restrictAlongPairing S K hK).quotientMap x := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  exact isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective
    (T.selectedLocal_quotient_smooth S K hK hext) hx
    (T.selectedLocal_quotient_mfderiv_bijective S K hK hext x)

def selectedLocal_interiorImage :
    TopologicalSpace.Opens (T.restrictAlongPairing S K hK).QuotientSpace := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  exact ⟨(T.restrictAlongPairing S K hK).quotientMap '' (T.subCarrier S).interior,
    isOpen_image_of_isLocalDiffeomorphAt (T.subCarrier S).interior.isOpen
      (fun x hx => T.selectedLocal_interior_local S K hK hext hx)⟩

def selectedLocal_interiorMap (x : (T.subCarrier S).interior) :
    T.selectedLocal_interiorImage S K hK hext :=
  ⟨(T.restrictAlongPairing S K hK).quotientMap x.val, x.val, x.property, rfl⟩

theorem selectedLocal_interiorMap_local :
    letI := T.restrictAlongChartedSpace S K hK hext
    letI := T.restrictAlong_isManifold S K hK hext
    IsLocalDiffeomorph (T.subCarrier S).model (modelWithCornersEuclideanHalfSpace 3) ∞
      (T.selectedLocal_interiorMap S K hK hext) := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  intro x
  have hval := DifferentialGeometry.isLocalDiffeomorph_subtype_val
    (I := (T.subCarrier S).model) (T.subCarrier S).interior x
  have h := hval.comp (modelWithCornersEuclideanHalfSpace 3)
    (T.restrictAlongPairing S K hK).QuotientSpace
    (T.selectedLocal_interior_local S K hK hext x.property)
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (V := T.selectedLocal_interiorImage S K hK hext)
    (f := (T.restrictAlongPairing S K hK).quotientMap ∘
      (Subtype.val : (T.subCarrier S).interior → (T.subCarrier S).Carrier))
    (fun y => ⟨y.val, y.property, rfl⟩) h

theorem selectedLocal_interiorMap_bijective :
    Function.Bijective (T.selectedLocal_interiorMap S K hK hext) := by
  constructor
  · intro x y h
    apply Subtype.ext
    apply (T.restrictAlongGluing S K hK).eq_of_rel_of_notMem
      (fun j hj => ?_) (Quotient.exact (congrArg Subtype.val h))
    have hb : (T.subCarrier S).model.IsBoundaryPoint x.val := by
      change x.val ∈ (T.subCarrier S).model.boundary (T.subCarrier S).Carrier
      rw [T.subCarrier_boundary_along S K hK]
      exact Or.inl (Set.mem_iUnion.mpr ⟨j, hj⟩)
    exact (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint x.val).mp hb x.property
  · rintro ⟨q, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

def selectedLocal_interiorDiffeomorph :
    letI := T.restrictAlongChartedSpace S K hK hext
    letI := T.restrictAlong_isManifold S K hK hext
    (T.subCarrier S).interior ≃ₘ⟮(T.subCarrier S).model,
      (modelWithCornersEuclideanHalfSpace 3)⟯ T.selectedLocal_interiorImage S K hK hext := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  exact (T.selectedLocal_interiorMap_local S K hK hext).diffeomorphOfBijective
    (T.selectedLocal_interiorMap_bijective S K hK hext)

theorem selectedLocal_seam_target_ambient {k : Fin T.pairing.count} (hk : k ∈ K)
    {q : (T.restrictAlongPairing S K hK).QuotientSpace}
    (hq : q ∈ (T.selectedLocal_seam S K hK hext hk).target) :
    letI := T.restrictAlongChartedSpace S K hK hext
    T.restrictAlongMap S K hK q ∈ (T.seam k).target := by
  let := T.restrictAlongChartedSpace S K hK hext
  let e := T.selectedLocal_seam S K hK hext hk
  have hp : e.symm q ∈ signedCollarSource :=
    (T.selectedLocal_seam_source S K hK hext hk) ▸ e.map_target hq
  have ha := T.selectedLocal_seam_ambient S K hK hext hk hp
  change T.restrictAlongMap S K hK (e (e.symm q)) = T.seam k (e.symm q) at ha
  have ha2 : T.restrictAlongMap S K hK q = T.seam k (e.symm q) :=
    (congrArg (T.restrictAlongMap S K hK) (e.toPartialEquiv.right_inv hq)).symm.trans ha
  exact ha2.symm ▸ (T.seam k).map_source ((T.seam_source k).symm ▸ hp)

theorem selectedLocal_seam_interior {k : Fin T.pairing.count} (hk : k ∈ K) :
    letI := T.restrictAlongChartedSpace S K hK hext
    letI := T.restrictAlong_isManifold S K hK hext
    (T.selectedLocal_seam S K hK hext hk).target ⊆
      (T.restrictAlongCarrier S K hK hext).interior := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  intro q hq
  apply T.isInteriorPoint_restrictAlong_of_mem S K hK hext q
  refine ⟨T.seamCollar_subset_region_of_internal S (hK k hk).1 (hK k hk).2
    (T.selectedLocal_seam_target_ambient S K hK hext hk hq), ?_⟩
  · intro ho
    obtain ⟨l, hl, hsurf⟩ := Set.mem_iUnion₂.mp ho
    have hne : l ≠ k := by
      intro he
      exact (Finset.mem_compl.mp hl) (he.symm ▸ hk)
    exact (T.seam_disjoint hne).le_bot
      ⟨T.seamSurface_subset_seamCollar l hsurf,
        T.selectedLocal_seam_target_ambient S K hK hext hk hq⟩

theorem selectedLocal_seam_eq_quotient {k : Fin T.pairing.count} (hk : k ∈ K)
    {p : Torus × ℝ} (hp : p ∈ signedCollarSource) (x : (T.subCarrier S).Carrier)
    (hx : T.cutMap x.val = T.seam k p) :
    letI := T.restrictAlongChartedSpace S K hK hext
    T.selectedLocal_seam S K hK hext hk p =
      (T.restrictAlongPairing S K hK).quotientMap x := by
  let := T.restrictAlongChartedSpace S K hK hext
  have ht := (T.seam k).map_source ((T.seam_source k).symm ▸ hp)
  apply T.restrictAlongMap_injOn_seamCollar S K hK hk
  · change T.restrictAlongMap S K hK
      (T.selectedLocal_seam S K hK hext hk p) ∈ (T.seam k).target
    rw [T.selectedLocal_seam_ambient S K hK hext hk hp]
    exact ht
  · change T.restrictAlongMap S K hK
      ((T.restrictAlongPairing S K hK).quotientMap x) ∈ (T.seam k).target
    rw [T.restrictAlongMap_quotientMap S K hK, hx]
    exact ht
  · rw [T.selectedLocal_seam_ambient S K hK hext hk hp,
      T.restrictAlongMap_quotientMap S K hK, hx]

theorem selectedLocal_boundaryCollar_ambient (a : T.AlongBoundarySide S K)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    letI := T.restrictAlongChartedSpace S K hK hext
    T.restrictAlongMap S K hK (T.restrictAlongBoundaryCollar S K hK hext a p) =
      T.cutMap (T.sideCollar a.val p) := by
  let := T.restrictAlongChartedSpace S K hK hext
  change T.restrictAlongMap S K hK (T.restrictAlongHalfCollar S K hK a p) = _
  rw [T.restrictAlongHalfCollar_apply S K hK a hp,
    T.restrictAlongMap_quotientMap S K hK, T.subCollar_apply S a.val a.property.1 hp]

theorem selectedLocal_external_seam_disjoint (a : T.AlongBoundarySide S K)
    {k : Fin T.pairing.count} (hk : k ∈ K) :
    letI := T.restrictAlongChartedSpace S K hK hext
    Disjoint (T.restrictAlongBoundaryCollar S K hK hext a).target
      (T.selectedLocal_seam S K hK hext hk).target := by
  let := T.restrictAlongChartedSpace S K hK hext
  rw [Set.disjoint_left]
  intro q ha hq
  let d := T.restrictAlongBoundaryCollar S K hK hext a
  let p := d.symm q
  have hp : p ∈ halfCollarSource :=
    (T.restrictAlongHalfCollar_source S K hK a) ▸ d.map_target ha
  have ham : T.restrictAlongMap S K hK q = T.cutMap (T.sideCollar a.val p) :=
    (congrArg (T.restrictAlongMap S K hK) (d.toPartialEquiv.right_inv ha)).symm.trans
      (T.selectedLocal_boundaryCollar_ambient S K hK hext a hp)
  have hside := T.cutMap_mem_sideRegion a.val
    ((T.sideCollar a.val).map_source ((T.sideCollar_source a.val).symm ▸ hp))
  have hseam := T.selectedLocal_seam_target_ambient S K hK hext hk hq
  rw [ham] at hseam
  rcases a with ⟨l | l | e, hs, hn⟩
  · exact (T.seam_disjoint (fun h : l = k => hn (h.symm ▸ hk))).le_bot ⟨hside, hseam⟩
  · exact (T.seam_disjoint (fun h : l = k => hn (h.symm ▸ hk))).le_bot ⟨hside, hseam⟩
  · exact (hext e hs).elim

theorem selectedLocal_external_disjoint :
    Disjoint (⋃ j, (T.restrictAlongGluing S K hK).block j)
      (T.restrictAlongBoundaryTori S K).image := by
  rw [T.restrictAlongBoundaryTori_image_eq_boundary_sdiff S K hK]
  exact Set.disjoint_sdiff_right

def selectedLocal_presentation (hS : S.Nonempty) :
    TorusPresentation (T.restrictAlongCarrier S K hK hext) := by
  let := T.restrictAlongChartedSpace S K hK hext
  let := T.restrictAlong_isManifold S K hK hext
  refine {
    cutCarrier := T.subCarrier S
    components := T.subComponents S hS
    pairing := T.restrictAlongPairing S K hK
    externalCount := Fintype.card (T.AlongBoundarySide S K)
    external := T.restrictAlongBoundaryToriDescended S K hK hext
    cutExternal := T.restrictAlongBoundaryTori S K
    external_exhausted := ?_
    cut_boundary_exhausted := T.subCarrier_boundary_along S K hK
    external_disjoint := T.selectedLocal_external_disjoint S K hK
    reconstruction := Homeomorph.refl _
    quotient_smooth := T.selectedLocal_quotient_smooth S K hK hext
    quotient_oriented := T.selectedLocal_quotient_oriented S K hK hext
    interiorImage := T.selectedLocal_interiorImage S K hK hext
    interiorDiffeomorph := T.selectedLocal_interiorDiffeomorph S K hK hext
    interior_map := fun x => rfl
    seam := fun j => T.selectedLocal_seam S K hK hext (T.alongSeam K j).property
    seam_source := fun j => T.selectedLocal_seam_source S K hK hext
      (T.alongSeam K j).property
    seam_zero := ?_
    seam_positive := ?_
    seam_negative := ?_
    seam_interior := fun j => T.selectedLocal_seam_interior S K hK hext
      (T.alongSeam K j).property
    seam_disjoint := ?_
    marked_collar := ?_
    external_seam_disjoint := fun i j =>
      T.selectedLocal_external_seam_disjoint S K hK hext (T.alongBoundarySide S K i)
        (T.alongSeam K j).property
    leftPiece := fun j => T.restrictLeftPiece S (T.alongKeptIndex S K hK j)
    rightPiece := fun j => T.restrictRightPiece S (T.alongKeptIndex S K hK j)
    left_owned := fun j => T.restrict_left_owned S hS (T.alongKeptIndex S K hK j)
    right_owned := fun j => T.restrict_right_owned S hS (T.alongKeptIndex S K hK j)
    externalPiece := fun i => T.subIndexOf S (T.alongBoundarySide S K i).property.1
    external_owned := ?_ }
  · rw [T.restrictAlongBoundaryToriDescended_image S K hK hext]
    ext q
    exact T.restrictAlong_isBoundaryPoint_iff S K hK hext q
  · intro j t
    apply T.selectedLocal_seam_eq_quotient S K hK hext (T.alongSeam K j).property
      (show (t, (0 : ℝ)) ∈ signedCollarSource by constructor <;> norm_num)
    change T.cutMap (T.pairing.leftParam
      (T.keptSeam S (T.alongKeptIndex S K hK j)).val t) = _
    rw [T.keptSeam_alongKeptIndex S K hK]
    exact (T.seam_zero (T.alongSeam K j).val t).symm
  · intro j t a ha h1
    apply T.selectedLocal_seam_eq_quotient S K hK hext (T.alongSeam K j).property
      (show (t, a) ∈ signedCollarSource by exact ⟨by linarith, h1⟩)
    change T.cutMap (((T.restrictPairing S).rightCollar
      (T.alongKeptIndex S K hK j)
      ((T.restrictAlongPairing S K hK).matching j t, halfPoint a ha)).val) = _
    rw [T.restrictPairing_rightCollar_apply S (T.alongKeptIndex S K hK j)
      (show ((T.restrictAlongPairing S K hK).matching j t, halfPoint a ha) ∈
        halfCollarSource from h1)]
    change T.cutMap (T.pairing.rightCollar
      (T.keptSeam S (T.alongKeptIndex S K hK j)).val
      (T.pairing.matching (T.keptSeam S (T.alongKeptIndex S K hK j)).val t,
        halfPoint a ha)) = _
    rw [T.keptSeam_alongKeptIndex S K hK]
    exact (T.seam_positive (T.alongSeam K j).val t a ha h1).symm
  · intro j t a ha h1
    apply T.selectedLocal_seam_eq_quotient S K hK hext (T.alongSeam K j).property
      (show (t, a) ∈ signedCollarSource by exact ⟨h1, by linarith⟩)
    change T.cutMap (((T.restrictPairing S).leftCollar
      (T.alongKeptIndex S K hK j) (t, halfPoint (-a) (neg_nonneg.mpr ha))).val) = _
    rw [T.restrictPairing_leftCollar_apply S (T.alongKeptIndex S K hK j)
      (show (t, halfPoint (-a) (neg_nonneg.mpr ha)) ∈ halfCollarSource by
        change -a < 1
        linarith)]
    rw [T.keptSeam_alongKeptIndex S K hK]
    exact (T.seam_negative (T.alongSeam K j).val t a ha h1).symm
  · intro i j hij
    rw [Set.disjoint_left]
    intro q hi hj
    apply (T.seam_disjoint (fun h => hij
      (T.alongSeam_injective K (Subtype.ext h)))).le_bot
    exact ⟨T.selectedLocal_seam_target_ambient S K hK hext (T.alongSeam K i).property hi,
      T.selectedLocal_seam_target_ambient S K hK hext (T.alongSeam K j).property hj⟩
  · intro i p hp
    exact (T.restrictAlongHalfCollar_apply S K hK (T.alongBoundarySide S K i) hp).symm
  · intro i q hq
    obtain ⟨t, rfl⟩ := hq
    change (T.subCollar S (T.alongBoundarySide S K i).val
      (T.alongBoundarySide S K i).property.1 (t, halfZero)).val ∈
      T.components.piece (T.subIndex S
        (T.subIndexOf S (T.alongBoundarySide S K i).property.1))
    rw [T.subCollar_apply S (T.alongBoundarySide S K i).val
      (T.alongBoundarySide S K i).property.1 (zero_mem_halfCollarSource t),
      T.subIndex_subIndexOf S]
    exact (T.sideCollar_zero_mem (T.alongBoundarySide S K i).val t).2

variable (hS : S.Nonempty)

theorem selectedLocal_alongSeam_index {k : Fin T.pairing.count} (hk : k ∈ K) :
    T.alongSeam K ((K.orderIsoOfFin rfl).symm ⟨k, hk⟩) = ⟨k, hk⟩ :=
  (K.orderIsoOfFin rfl).apply_symm_apply ⟨k, hk⟩

def selectedLocal_liftSide : (T.selectedLocal_presentation S K hK hext hS).Side → T.Side
  | .inl j => .inl (T.alongSeam K j).val
  | .inr (.inl j) => .inr (.inl (T.alongSeam K j).val)
  | .inr (.inr a) => (T.alongBoundarySide S K a).val

theorem selectedLocal_liftSide_mem (s : (T.selectedLocal_presentation S K hK hext hS).Side) :
    T.sidePiece (T.selectedLocal_liftSide S K hK hext hS s) ∈ S := by
  rcases s with j | j | a
  · exact (hK (T.alongSeam K j).val (T.alongSeam K j).property).1
  · exact (hK (T.alongSeam K j).val (T.alongSeam K j).property).2
  · exact (T.alongBoundarySide S K a).property.1

theorem selectedLocal_sidePiece (s : (T.selectedLocal_presentation S K hK hext hS).Side) :
    (T.selectedLocal_presentation S K hK hext hS).sidePiece s = T.subIndexOf S
      (T.selectedLocal_liftSide_mem S K hK hext hS s) := by
  rcases s with j | j | a
  · apply (T.subIndexOf_eq_iff _ (T.selectedLocal_liftSide_mem S K hK hext hS (.inl j))).mpr
    exact congrArg T.leftPiece (T.keptSeam_alongKeptIndex S K hK j)
  · apply (T.subIndexOf_eq_iff _
      (T.selectedLocal_liftSide_mem S K hK hext hS (.inr (.inl j)))).mpr
    exact congrArg T.rightPiece (T.keptSeam_alongKeptIndex S K hK j)
  · rfl

theorem selectedLocal_liftSide_injective : Function.Injective (T.selectedLocal_liftSide S K hK
  hext hS) := by
  rintro (j | j | a) (j' | j' | a') h
  · have h' : (T.alongSeam K j).val = (T.alongSeam K j').val := Sum.inl_injective h
    exact congrArg Sum.inl (T.alongSeam_injective K (Subtype.ext h'))
  · exact absurd h (by simp [selectedLocal_liftSide])
  · have ha := (T.alongBoundarySide S K a').property.2
    change Sum.inl (T.alongSeam K j).val = (T.alongBoundarySide S K a').val at h
    rw [← h] at ha
    exact (ha (T.alongSeam K j).property).elim
  · exact absurd h (by simp [selectedLocal_liftSide])
  · have h' : (T.alongSeam K j).val = (T.alongSeam K j').val :=
      Sum.inl_injective (Sum.inr_injective h)
    exact congrArg (fun x => Sum.inr (Sum.inl x))
      (T.alongSeam_injective K (Subtype.ext h'))
  · have ha := (T.alongBoundarySide S K a').property.2
    change Sum.inr (Sum.inl (T.alongSeam K j).val) = (T.alongBoundarySide S K a').val at h
    rw [← h] at ha
    exact (ha (T.alongSeam K j).property).elim
  · have ha := (T.alongBoundarySide S K a).property.2
    change (T.alongBoundarySide S K a).val = Sum.inl (T.alongSeam K j').val at h
    rw [h] at ha
    exact (ha (T.alongSeam K j').property).elim
  · have ha := (T.alongBoundarySide S K a).property.2
    change (T.alongBoundarySide S K a).val = Sum.inr (Sum.inl (T.alongSeam K j').val) at h
    rw [h] at ha
    exact (ha (T.alongSeam K j').property).elim
  · have h' : T.alongBoundarySide S K a = T.alongBoundarySide S K a' := Subtype.ext h
    exact congrArg (fun x => Sum.inr (Sum.inr x)) ((Fintype.equivFin _).symm.injective h')

theorem exists_selectedLocal_liftSide_eq (s : T.Side) (hs : T.sidePiece s ∈ S) :
    ∃ s', T.selectedLocal_liftSide S K hK hext hS s' = s := by
  by_cases hk : (fun s : T.Side => match s with
    | .inl k => k ∈ K
    | .inr (.inl k) => k ∈ K
    | .inr (.inr e) => False) s
  · rcases s with k | k | e
    · refine ⟨.inl ((K.orderIsoOfFin rfl).symm ⟨k, hk⟩), ?_⟩
      change Sum.inl (T.alongSeam K ((K.orderIsoOfFin rfl).symm ⟨k, hk⟩)).val = _
      rw [selectedLocal_alongSeam_index]
    · refine ⟨.inr (.inl ((K.orderIsoOfFin rfl).symm ⟨k, hk⟩)), ?_⟩
      change Sum.inr (Sum.inl (T.alongSeam K ((K.orderIsoOfFin rfl).symm ⟨k, hk⟩)).val) = _
      rw [selectedLocal_alongSeam_index]
    · exact hk.elim
  · have hn : (fun s : T.Side => match s with
        | .inl k => k ∉ K
        | .inr (.inl k) => k ∉ K
        | .inr (.inr e) => e ∈ Finset.univ) s := by
      rcases s with k | k | e
      · exact hk
      · exact hk
      · exact Finset.mem_univ e
    refine ⟨.inr (.inr (Fintype.equivFin (T.AlongBoundarySide S K) ⟨s, hs, hn⟩)), ?_⟩
    change (T.alongBoundarySide S K (Fintype.equivFin _ ⟨s, hs, hn⟩)).val = _
    rw [alongBoundarySide_equivFin]

theorem selectedLocal_sideCollar_val (s : (T.selectedLocal_presentation S K hK hext hS).Side)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    ((T.selectedLocal_presentation S K hK hext hS).sideCollar s p).val =
      T.sideCollar (T.selectedLocal_liftSide S K hK hext hS s) p := by
  rcases s with j | j | a
  · change (((T.restrictPairing S).leftCollar (T.alongKeptIndex S K hK j)) p).val = _
    rw [T.restrictPairing_leftCollar_apply S (T.alongKeptIndex S K hK j) hp,
      T.keptSeam_alongKeptIndex S K hK j]
    rfl
  · change (((T.restrictPairing S).rightCollar (T.alongKeptIndex S K hK j)) p).val = _
    rw [T.restrictPairing_rightCollar_apply S (T.alongKeptIndex S K hK j) hp,
      T.keptSeam_alongKeptIndex S K hK j]
    rfl
  · exact T.subCollar_apply S _ (T.alongBoundarySide S K a).property.1 hp

variable {i : Fin T.components.count} (hi : i ∈ S)

def selectedLocal_ownedSideMap (s : (T.selectedLocal_presentation S K hK hext hS).OwnedSide
  (T.subIndexOf S hi)) :
    T.OwnedSide i :=
  ⟨T.selectedLocal_liftSide S K hK hext hS s.val, by
    have h := s.property
    rw [selectedLocal_sidePiece] at h
    exact (T.subIndexOf_eq_iff _ hi).mp h⟩

theorem selectedLocal_ownedSideMap_bijective :
    Function.Bijective (T.selectedLocal_ownedSideMap S K hK hext hS hi) := by
  refine ⟨fun a b h => Subtype.ext (T.selectedLocal_liftSide_injective S K hK hext hS
    (congrArg Subtype.val h)), fun s => ?_⟩
  have hsS : T.sidePiece s.val ∈ S := by rw [s.property]; exact hi
  obtain ⟨s', hs'⟩ := T.exists_selectedLocal_liftSide_eq S K hK hext hS s.val hsS
  refine ⟨⟨s', ?_⟩, Subtype.ext hs'⟩
  rw [selectedLocal_sidePiece]
  refine (T.subIndexOf_eq_iff _ hi).mpr ?_
  rw [hs']
  exact s.property

def selectedLocal_ownedSideEquiv :
    (T.selectedLocal_presentation S K hK hext hS).OwnedSide (T.subIndexOf S hi) ≃ T.OwnedSide i :=
  Equiv.ofBijective _ (T.selectedLocal_ownedSideMap_bijective S K hK hext hS hi)

theorem selectedLocal_liftSide_selectedLocal_ownedSideEquiv_symm (s : T.OwnedSide i) :
    T.selectedLocal_liftSide S K hK hext hS ((T.selectedLocal_ownedSideEquiv S K hK hext hS
      hi).symm s).val = s.val :=
  congrArg Subtype.val ((T.selectedLocal_ownedSideEquiv S K hK hext hS hi).apply_symm_apply s)

theorem selectedLocal_memPiece_iff (x : (T.subCarrier S).Carrier) :
    x ∈ (T.selectedLocal_presentation S K hK hext hS).components.piece (T.subIndexOf S hi) ↔
      x.val ∈ T.components.piece i := by
  change x.val ∈ T.components.piece (T.subIndex S (T.subIndexOf S hi)) ↔ _
  rw [subIndex_subIndexOf]

def selectedLocal_pieceDiffeomorph :
    T.components.piece i ≃ₘ⟮T.cutCarrier.model, (T.selectedLocal_presentation S K hK hext
      hS).cutCarrier.model⟯
      (T.selectedLocal_presentation S K hK hext hS).components.piece (T.subIndexOf S hi) where
  toFun x := ⟨⟨x.val, T.piece_subset_subPiece S hi x.property⟩,
    (T.selectedLocal_memPiece_iff S K hK hext hS hi _).mpr x.property⟩
  invFun y := ⟨y.val.val, (T.selectedLocal_memPiece_iff S K hK hext hS hi _).mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := by
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    exact (ContMDiff.subtypeVal_comp_iff (I := T.cutCarrier.model) (I' := T.cutCarrier.model)
      (T.subPiece S) _).mp contMDiff_subtype_val
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff _ _).mp ?_
    exact (contMDiff_subtype_val (I := T.cutCarrier.model) (U := T.subPiece S)).comp
      (contMDiff_subtype_val (I := (T.selectedLocal_presentation S K hK hext hS).cutCarrier.model)
        (U := (T.selectedLocal_presentation S K hK hext hS).components.piece (T.subIndexOf S hi)))

theorem selectedLocal_pieceDiffeomorph_val (x : T.components.piece i) :
    (T.selectedLocal_pieceDiffeomorph S K hK hext hS hi x).val.val = x.val := rfl

def selectedLocal_transfer :
    PieceTransfer T i (T.selectedLocal_presentation S K hK hext hS) (T.subIndexOf S hi) where
  map := T.selectedLocal_pieceDiffeomorph S K hK hext hS hi
  side := (T.selectedLocal_ownedSideEquiv S K hK hext hS hi).symm
  collar_eq s p hp := by
    apply Subtype.ext
    apply Subtype.ext
    rw [selectedLocal_pieceDiffeomorph_val, T.pieceCollar_apply i _ hp]
    have h1 := TorusPresentation.pieceCollar_apply (T.selectedLocal_presentation S K hK hext hS)
      (T.subIndexOf S hi)
      ((T.selectedLocal_ownedSideEquiv S K hK hext hS hi).symm s) hp
    rw [h1, T.selectedLocal_sideCollar_val S K hK hext hS _ hp,
      selectedLocal_liftSide_selectedLocal_ownedSideEquiv_symm]


theorem selectedLocal_ownedSideEquiv_symm_val (s : T.OwnedSide i)
    (s' : (T.selectedLocal_presentation S K hK hext hS).Side)
    (hs : T.selectedLocal_liftSide S K hK hext hS s' = s.val) :
    ((T.selectedLocal_ownedSideEquiv S K hK hext hS hi).symm s).val = s' := by
  apply T.selectedLocal_liftSide_injective S K hK hext hS
  exact (T.selectedLocal_liftSide_selectedLocal_ownedSideEquiv_symm
    S K hK hext hS hi s).trans hs.symm

end GC.Seifert.TorusPresentation

namespace GC.Seifert

structure SelectedStarGroup {W : CompactCarrier.{u}} (T : TorusPresentation W)
    (d : SeifertData) where
  center : Fin T.components.count
  product : ProductFibredPiece T center d.k
  arm : Fin d.fillingCount → Fin T.pairing.count
  solid : ∀ l, SolidTorusPiece T (T.leftPiece (arm l))
  arm_right : ∀ l, T.rightPiece (arm l) = center
  arm_injective : Function.Injective arm
  solid_ne_center : ∀ l, T.leftPiece (arm l) ≠ center
  slope : ∀ l, torusUnit (T.pairing.matching (arm l)) • meridianSlope =
    PrimitiveSlope.mk (d.fillingSlope l) (d.isPrimitive_fillingSlope l)

namespace SelectedStarGroup

variable {W : CompactCarrier.{u}} {T : TorusPresentation W} {d : SeifertData}
  (G : SelectedStarGroup T d)

def set : Finset (Fin T.components.count) :=
  insert G.center (Finset.univ.image fun l => T.leftPiece (G.arm l))

theorem center_mem : G.center ∈ G.set := Finset.mem_insert_self _ _

theorem solid_mem (l : Fin d.fillingCount) : T.leftPiece (G.arm l) ∈ G.set :=
  Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ l))

theorem mem_set {i : Fin T.components.count} (hi : i ∈ G.set) :
    i = G.center ∨ ∃ l, i = T.leftPiece (G.arm l) := by
  rcases Finset.mem_insert.mp hi with h | h
  · exact Or.inl h
  · obtain ⟨l, -, hl⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨l, hl.symm⟩

theorem side_eq_of_solid (l : Fin d.fillingCount) (s : T.Side)
    (hs : T.sidePiece s = T.leftPiece (G.arm l)) : s = .inl (G.arm l) := by
  have hsub := (G.solid l).card_ownedSide
  have h1 : Subsingleton (T.OwnedSide (T.leftPiece (G.arm l))) :=
    Fintype.card_le_one_iff_subsingleton.mp hsub.le
  exact congrArg Subtype.val (Subsingleton.elim (⟨s, hs⟩ : T.OwnedSide _) ⟨.inl (G.arm l), rfl⟩)

theorem leftPiece_arm_injective : Function.Injective fun l => T.leftPiece (G.arm l) := by
  intro l l' h
  have h1 := G.side_eq_of_solid l' (.inl (G.arm l)) h
  exact G.arm_injective (Sum.inl_injective h1)

def selected : Finset (Fin T.pairing.count) := Finset.univ.image G.arm

theorem arm_mem (l : Fin d.fillingCount) : G.arm l ∈ G.selected :=
  Finset.mem_image_of_mem G.arm (Finset.mem_univ l)

theorem internal {k : Fin T.pairing.count} (hk : k ∈ G.selected) : ∃ l, k = G.arm l := by
  obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hk
  exact ⟨l, he.symm⟩

theorem selected_internal : ∀ k ∈ G.selected, T.leftPiece k ∈ G.set ∧
    T.rightPiece k ∈ G.set := by
  intro k hk
  obtain ⟨l, rfl⟩ := G.internal hk
  exact ⟨G.solid_mem l, (G.arm_right l).symm ▸ G.center_mem⟩

theorem set_nonempty : G.set.Nonempty := ⟨G.center, G.center_mem⟩

def starIndex : Option (Fin d.fillingCount) → Fin G.set.card
  | none => T.subIndexOf G.set G.center_mem
  | some l => T.subIndexOf G.set (G.solid_mem l)

theorem starIndex_bijective : Function.Bijective G.starIndex := by
  constructor
  · rintro (_ | l) (_ | l') h <;> simp only [starIndex] at h
    · rfl
    · exact absurd ((T.subIndexOf_eq_iff _ _).mp h) (G.solid_ne_center l').symm
    · exact absurd ((T.subIndexOf_eq_iff _ _).mp h) (G.solid_ne_center l)
    · exact congrArg some (G.leftPiece_arm_injective ((T.subIndexOf_eq_iff _ _).mp h))
  · intro j
    rcases G.mem_set (T.subIndex_mem G.set j) with h | ⟨l, h⟩
    · refine ⟨none, ?_⟩
      change T.subIndexOf G.set G.center_mem = j
      rw [← T.subIndexOf_subIndex G.set j]
      exact (T.subIndexOf_eq_iff _ _).mpr h.symm
    · refine ⟨some l, ?_⟩
      change T.subIndexOf G.set (G.solid_mem l) = j
      rw [← T.subIndexOf_subIndex G.set j]
      exact (T.subIndexOf_eq_iff _ _).mpr h.symm

def selectedArm (l : Fin d.fillingCount) : {k : Fin T.pairing.count // k ∈ G.selected} :=
  ⟨G.arm l, G.arm_mem l⟩

theorem selectedArm_bijective : Function.Bijective G.selectedArm := by
  refine ⟨fun l l' h => G.arm_injective (congrArg Subtype.val h), fun k => ?_⟩
  obtain ⟨l, hl⟩ := G.internal k.property
  exact ⟨l, Subtype.ext hl.symm⟩

def armSeam : Fin d.fillingCount ≃ Fin G.selected.card :=
  (Equiv.ofBijective G.selectedArm G.selectedArm_bijective).trans
    (G.selected.orderIsoOfFin rfl).toEquiv.symm

theorem alongSeam_armSeam (l : Fin d.fillingCount) :
    (T.alongSeam G.selected (G.armSeam l)).val = G.arm l := by
  change ((G.selected.orderIsoOfFin rfl)
    ((G.selected.orderIsoOfFin rfl).symm (G.selectedArm l))).val = G.arm l
  rw [OrderIso.apply_symm_apply]
  rfl

theorem boundarySide_owned (a : T.AlongBoundarySide G.set G.selected) : T.sidePiece a.val =
  G.center := by
  rcases G.mem_set a.property.1 with h | ⟨l, h⟩
  · exact h
  · have he := G.side_eq_of_solid l a.val h
    have hn := a.property.2
    rw [he] at hn
    exact (hn (G.arm_mem l)).elim

def centerSideMap : Fin d.fillingCount ⊕ T.AlongBoundarySide G.set G.selected → T.OwnedSide G.center
  | .inl l => ⟨.inr (.inl (G.arm l)), G.arm_right l⟩
  | .inr a => ⟨a.val, G.boundarySide_owned a⟩

theorem centerSideMap_bijective : Function.Bijective G.centerSideMap := by
  constructor
  · rintro (l | a) (l' | a') h <;> have h' := congrArg Subtype.val h <;>
      simp only [centerSideMap] at h'
    · exact congrArg Sum.inl (G.arm_injective (Sum.inl_injective (Sum.inr_injective h')))
    · have hn := a'.property.2
      rw [← h'] at hn
      exact (hn (G.arm_mem l)).elim
    · have hn := a.property.2
      rw [h'] at hn
      exact (hn (G.arm_mem l')).elim
    · exact congrArg Sum.inr (Subtype.ext h')
  · rintro ⟨s, hs⟩
    by_cases hk : (fun s : T.Side => match s with
    | .inl k => k ∈ G.selected
    | .inr (.inl k) => k ∈ G.selected
    | .inr (.inr e) => False) s
    · rcases s with k | k | e
      · obtain ⟨l, rfl⟩ := G.internal hk
        exact absurd hs (G.solid_ne_center l)
      · obtain ⟨l, rfl⟩ := G.internal hk
        exact ⟨.inl l, rfl⟩
      · exact hk.elim
    · have hn : (fun s : T.Side => match s with
          | .inl k => k ∉ G.selected
          | .inr (.inl k) => k ∉ G.selected
          | .inr (.inr e) => e ∈ Finset.univ) s := by
        rcases s with k | k | e
        · exact hk
        · exact hk
        · exact Finset.mem_univ e
      exact ⟨.inr ⟨s, hs ▸ G.center_mem, hn⟩, rfl⟩

def centerSideEquiv : Fin d.fillingCount ⊕ T.AlongBoundarySide G.set G.selected ≃ T.OwnedSide
  G.center :=
  Equiv.ofBijective _ G.centerSideMap_bijective

theorem card_boundarySide : Fintype.card (T.AlongBoundarySide G.set G.selected) = d.ports := by
  have h := Fintype.card_congr G.centerSideEquiv
  rw [Fintype.card_sum, Fintype.card_fin, G.product.card_ownedSide] at h
  have h2 := d.ports_add_fillingCount
  omega

def extSide : Fin d.ports ≃ T.AlongBoundarySide G.set G.selected :=
  (finCongr G.card_boundarySide.symm).trans (Fintype.equivFin _).symm

def portEquiv : Fin d.ports ⊕ Fin d.fillingCount ≃ Fin d.k :=
  (Equiv.sumComm _ _).trans ((Equiv.sumCongr (Equiv.refl _) G.extSide).trans
    (G.centerSideEquiv.trans G.product.port.symm))

variable (hext : ∀ i, T.externalPiece i ∉ G.set)

def restrictBlock : SeifertBlock (T.restrictAlongCarrier G.set G.selected G.selected_internal
  hext) d where
  presentation := T.selectedLocal_presentation G.set G.selected G.selected_internal hext
    G.set_nonempty
  piece := Equiv.ofBijective G.starIndex G.starIndex_bijective
  product := G.product.transfer (T.selectedLocal_transfer G.set G.selected G.selected_internal
    hext G.set_nonempty G.center_mem)
  solid l := (G.solid l).transfer (T.selectedLocal_transfer G.set G.selected G.selected_internal
    hext G.set_nonempty (G.solid_mem l))
  port := G.portEquiv
  seam := G.armSeam
  free := finCongr G.card_boundarySide.symm
  free_port r := by
    change ((T.selectedLocal_ownedSideEquiv G.set G.selected G.selected_internal hext
      G.set_nonempty G.center_mem).symm
      (G.product.port (G.product.port.symm (G.centerSideMap (.inr (G.extSide r)))))).val = _
    rw [Equiv.apply_symm_apply]
    refine T.selectedLocal_ownedSideEquiv_symm_val G.set G.selected G.selected_internal hext
      G.set_nonempty G.center_mem _ _ ?_
    rfl
  filled_port l := by
    change ((T.selectedLocal_ownedSideEquiv G.set G.selected G.selected_internal hext
      G.set_nonempty G.center_mem).symm
      (G.product.port (G.product.port.symm (G.centerSideMap (.inl l))))).val = _
    rw [Equiv.apply_symm_apply]
    refine T.selectedLocal_ownedSideEquiv_symm_val G.set G.selected G.selected_internal hext
      G.set_nonempty G.center_mem _ _ ?_
    change Sum.inr (Sum.inl (T.alongSeam G.selected (G.armSeam l)).val) = _
    rw [G.alongSeam_armSeam]
    rfl
  solid_port l := by
    change ((T.selectedLocal_ownedSideEquiv G.set G.selected G.selected_internal hext
      G.set_nonempty (G.solid_mem l)).symm
      ((G.solid l).port 0)).val = _
    refine T.selectedLocal_ownedSideEquiv_symm_val G.set G.selected G.selected_internal hext
      G.set_nonempty (G.solid_mem l) _ _ ?_
    change Sum.inl (T.alongSeam G.selected (G.armSeam l)).val = _
    rw [G.alongSeam_armSeam, G.side_eq_of_solid l _ ((G.solid l).port 0).property]
  slope l := by
    change torusUnit (T.pairing.matching (T.keptSeam G.set
      (T.alongKeptIndex G.set G.selected G.selected_internal (G.armSeam l))).val) •
      meridianSlope = _
    rw [T.keptSeam_alongKeptIndex, G.alongSeam_armSeam]
    exact G.slope l

theorem restrictBlock_external_collar (r : Fin (G.restrictBlock hext).presentation.externalCount)
    (p : Torus × EuclideanHalfSpace 1) :
    (G.restrictBlock hext).presentation.external.collar r p =
      (T.restrictAlongBoundaryToriDescended G.set G.selected G.selected_internal hext).collar
        r p := rfl

theorem exists_restrictBlock_on (S : Finset (Fin T.components.count))
    (K : Finset (Fin T.pairing.count))
    (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
    (hext' : ∀ i, T.externalPiece i ∉ S) (hs : G.set = S) (hk : G.selected = K) :
    ∃ B : SeifertBlock (T.restrictAlongCarrier S K hK hext') d,
      ∃ e : Fin B.presentation.externalCount ≃ Fin (Fintype.card (T.AlongBoundarySide S K)),
        ∀ r p, p ∈ halfCollarSource → B.presentation.external.collar r p =
          (T.restrictAlongBoundaryToriDescended S K hK hext').collar (e r) p := by
  subst S
  subst K
  exact ⟨G.restrictBlock hext', Equiv.refl _, fun r p hp => rfl⟩

end SelectedStarGroup

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W) (hE : E.IsMoveFree)
  (hR : ∀ j, E.kind (E.toTorus.rightPiece j) ≠ 1) (c : Fin E.toTorus.components.count)

def centreSelectedGroup (hc3 : E.kind c = 3) :
    SelectedStarGroup E.toTorus (E.centreData hE hR c) where
  center := c
  product := E.pieceOfKind hc3
  arm l := (E.centreArm hE hR c l).val
  solid l := E.pieceOfKind (E.centreArm hE hR c l).property.2
  arm_right l := (E.centreArm hE hR c l).property.1
  arm_injective l l' h := by
    have h1 := (E.armEquiv c).injective (Subtype.ext h)
    exact Fin.cast_injective (E.centreData_fillingCount hE hR c) h1
  solid_ne_center l := by
    intro he
    have h1 := (E.centreArm hE hR c l).property.2
    rw [he, hc3] at h1
    omega
  slope l := by
    refine (E.armCone_spec hE hR c _).2.2.trans ((PrimitiveSlope.mk_eq_mk_iff _ _).mpr
      (Or.inl ?_))
    exact coneData_fillingSlope _ _ _ _ _ l

theorem centreSelectedGroup_arm_surjective :
    Function.Surjective (E.centreArm hE hR c) := by
  intro a
  refine ⟨((E.armEquiv c).symm a).cast (E.centreData_fillingCount hE hR c).symm, ?_⟩
  change E.armEquiv c ((((E.armEquiv c).symm a).cast
    (E.centreData_fillingCount hE hR c).symm).cast
      (E.centreData_fillingCount hE hR c)) = a
  rw [Fin.cast_cast, Fin.cast_eq_self, Equiv.apply_symm_apply]

theorem centreSelectedGroup_selected_eq_singleton (hc3 : E.kind c = 3)
    {j : Fin E.toTorus.pairing.count} (hj : E.IsArm c j)
    (hu : ∀ a, E.IsArm c a → a = j) :
    (E.centreSelectedGroup hE hR c hc3).selected = {j} := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp ha
    have hjj := hu (E.centreArm hE hR c l).val (E.centreArm hE hR c l).property
    exact Finset.mem_singleton.mpr (he.symm.trans hjj)
  · intro ha
    have haj := Finset.mem_singleton.mp ha
    obtain ⟨l, hl⟩ := E.centreSelectedGroup_arm_surjective hE hR c ⟨j, hj⟩
    apply Finset.mem_image.mpr
    refine ⟨l, Finset.mem_univ l, ?_⟩
    exact (congrArg Subtype.val hl).trans haj.symm

theorem centreSelectedGroup_set_eq_pair (hc3 : E.kind c = 3)
    {j : Fin E.toTorus.pairing.count} (hj : E.IsArm c j)
    (hu : ∀ a, E.IsArm c a → a = j) :
    (E.centreSelectedGroup hE hR c hc3).set = {c, E.toTorus.leftPiece j} := by
  classical
  ext a
  constructor
  · intro ha
    rcases (E.centreSelectedGroup hE hR c hc3).mem_set ha with h | ⟨l, h⟩
    · exact Finset.mem_insert.mpr (Or.inl h)
    · have hjj := hu (E.centreArm hE hR c l).val (E.centreArm hE hR c l).property
      change a = E.toTorus.leftPiece (E.centreArm hE hR c l).val at h
      rw [hjj] at h
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
  · intro ha
    rcases Finset.mem_insert.mp ha with h | h
    · exact h ▸ (E.centreSelectedGroup hE hR c hc3).center_mem
    · have haj := Finset.mem_singleton.mp h
      obtain ⟨l, hl⟩ := E.centreSelectedGroup_arm_surjective hE hR c ⟨j, hj⟩
      have hm := (E.centreSelectedGroup hE hR c hc3).solid_mem l
      change E.toTorus.leftPiece (E.centreArm hE hR c l).val ∈ _ at hm
      rw [hl] at hm
      exact haj ▸ hm

theorem centreSingleArm_internal {j : Fin E.toTorus.pairing.count}
    (hj : E.IsArm c j) :
    ∀ a ∈ ({j} : Finset (Fin E.toTorus.pairing.count)),
      E.toTorus.leftPiece a ∈ ({c, E.toTorus.leftPiece j} : Finset _) ∧
        E.toTorus.rightPiece a ∈ ({c, E.toTorus.leftPiece j} : Finset _) := by
  classical
  intro a ha
  have he := Finset.mem_singleton.mp ha
  subst a
  exact ⟨by simp, by simp [hj.1]⟩

theorem exists_centreSingleArmBlock (hc3 : E.kind c = 3)
    {j : Fin E.toTorus.pairing.count} (hj : E.IsArm c j)
    (hu : ∀ a, E.IsArm c a → a = j)
    (hext : ∀ i, E.toTorus.externalPiece i ∉
      ({c, E.toTorus.leftPiece j} : Finset _)) :
    ∃ B : SeifertBlock (E.toTorus.restrictAlongCarrier
        {c, E.toTorus.leftPiece j} {j} (E.centreSingleArm_internal c hj) hext)
        (E.centreData hE hR c),
      ∃ e : Fin B.presentation.externalCount ≃
          Fin (Fintype.card (E.toTorus.AlongBoundarySide {c, E.toTorus.leftPiece j} {j})),
        ∀ r p, p ∈ halfCollarSource → B.presentation.external.collar r p =
          (E.toTorus.restrictAlongBoundaryToriDescended {c, E.toTorus.leftPiece j} {j}
            (E.centreSingleArm_internal c hj) hext).collar (e r) p := by
  classical
  let G := E.centreSelectedGroup hE hR c hc3
  have hs : G.set = {c, E.toTorus.leftPiece j} :=
    E.centreSelectedGroup_set_eq_pair hE hR c hc3 hj hu
  have hk : G.selected = {j} :=
    E.centreSelectedGroup_selected_eq_singleton hE hR c hc3 hj hu
  exact G.exists_restrictBlock_on {c, E.toTorus.leftPiece j} {j}
    (E.centreSingleArm_internal c hj) hext hs hk

end ElementaryPresentation

end GC.Seifert

namespace GC.Seifert.ElementaryPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}
  (E : ElementaryPresentation (NoCuts.carrier Q))
  {c : Fin E.toTorus.components.count} {j k : Fin E.toTorus.pairing.count}

theorem selfSeam_arm_ne (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) : j ≠ k := by
  intro he
  have h1 := hj.2
  rw [he, hl, hc3] at h1
  omega

theorem selfSeam_solid_ne (hj : E.IsArm c j) (hc3 : E.kind c = 3) :
    E.toTorus.leftPiece j ≠ c := by
  intro he
  have h1 := hj.2
  rw [he, hc3] at h1
  omega

def selfSeamCentreSide (hj : E.IsArm c j)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) :
    Fin 3 → E.toTorus.OwnedSide c :=
  ![⟨.inr (.inl j), hj.1⟩, ⟨.inl k, hl⟩, ⟨.inr (.inl k), hr⟩]

theorem selfSeamCentreSide_injective (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) :
    Function.Injective (E.selfSeamCentreSide hj hl hr) := by
  intro a b hab
  have hval := congrArg Subtype.val hab
  have hne := E.selfSeam_arm_ne hj hc3 hl
  fin_cases a <;> fin_cases b <;> simp [selfSeamCentreSide, hne, Ne.symm hne] at hval ⊢

theorem selfSeamCentreSide_surjective (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) :
    Function.Surjective (E.selfSeamCentreSide hj hl hr) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨E.selfSeamCentreSide_injective hj hc3 hl hr,
      (by rw [Fintype.card_fin, (E.piece c).card_ownedSide, hc3])⟩ |>.2

theorem selfSeam_side_cases (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c)
    (s : E.toTorus.OwnedSide c) :
    s.val = .inr (.inl j) ∨ s.val = .inl k ∨ s.val = .inr (.inl k) := by
  obtain ⟨a, ha⟩ := E.selfSeamCentreSide_surjective hj hc3 hl hr s
  fin_cases a <;> simp [selfSeamCentreSide] at ha <;> subst s <;> simp

theorem selfSeam_all_pieces (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c)
    (i : Fin E.toTorus.components.count) :
    i ∈ ({c, E.toTorus.leftPiece j} : Finset (Fin E.toTorus.components.count)) := by
  classical
  let S : Finset (Fin E.toTorus.components.count) := {c, E.toTorus.leftPiece j}
  have hcS : c ∈ S := by simp [S]
  have hjS : E.toTorus.leftPiece j ∈ S := by simp [S]
  refine E.toTorus.mem_of_not_isCrossing S ⟨c, hcS⟩ (fun a ha => ?_) i
  rcases ha with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha
    · rcases E.selfSeam_side_cases hj hc3 hl hr ⟨.inl a, ha⟩ with h | h | h
      · exact (by simp at h)
      · obtain rfl := Sum.inl_injective h
        exact hb (hr.symm ▸ hcS)
      · exact (by simp at h)
    · have h := congrArg Subtype.val
        (E.side_eq_of_kind_one hj.2 ⟨.inl a, ha⟩ ⟨.inl j, rfl⟩)
      obtain rfl := Sum.inl_injective h
      exact hb (hj.1.symm ▸ hcS)
  · simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with ha | ha
    · rcases E.selfSeam_side_cases hj hc3 hl hr ⟨.inr (.inl a), ha⟩ with h | h | h
      · obtain rfl := Sum.inl_injective (Sum.inr_injective h)
        exact hb hjS
      · exact (by simp at h)
      · obtain rfl := Sum.inl_injective (Sum.inr_injective h)
        exact hb (hl.symm ▸ hcS)
    · have h := congrArg Subtype.val
        (E.side_eq_of_kind_one hj.2 ⟨.inr (.inl a), ha⟩ ⟨.inl j, rfl⟩)
      exact (by simp at h)

theorem selfSeam_all_seams (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c)
    (a : Fin E.toTorus.pairing.count) : a = j ∨ a = k := by
  have ha := E.selfSeam_all_pieces hj hc3 hl hr (E.toTorus.leftPiece a)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with ha | ha
  · rcases E.selfSeam_side_cases hj hc3 hl hr ⟨.inl a, ha⟩ with h | h | h
    · exact (by simp at h)
    · exact Or.inr (Sum.inl_injective h)
    · exact (by simp at h)
  · exact Or.inl (E.eq_of_leftPiece_eq hj.2 ha.symm).symm

theorem selfSeam_arm_unique (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c)
    (a : {a // E.IsArm c a}) : a.val = j := by
  rcases E.selfSeam_all_seams hj hc3 hl hr a.val with ha | ha
  · exact ha
  · have h1 := a.property.2
    rw [ha, hl, hc3] at h1
    omega

theorem selfSeam_armCount (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) :
    E.armCount c = 1 := by
  let : Unique {a // E.IsArm c a} :=
    ⟨⟨j, hj⟩, fun a => Subtype.ext (E.selfSeam_arm_unique hj hc3 hl hr a)⟩
  exact Fintype.card_unique

theorem selfSeam_set_eq_univ (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) :
    ({c, E.toTorus.leftPiece j} : Finset (Fin E.toTorus.components.count)) = Finset.univ := by
  classical
  exact Finset.eq_univ_iff_forall.mpr (E.selfSeam_all_pieces hj hc3 hl hr)

theorem selfSeam_seams_eq_pair (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) :
    (Finset.univ : Finset (Fin E.toTorus.pairing.count)) = {j, k} := by
  classical
  symm
  exact Finset.eq_univ_iff_forall.mpr fun a => by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      E.selfSeam_all_seams hj hc3 hl hr a

theorem selfSeam_counts (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) :
    E.toTorus.components.count = 2 ∧ E.toTorus.pairing.count = 2 := by
  classical
  constructor
  · have h := congrArg Finset.card (E.selfSeam_set_eq_univ hj hc3 hl hr)
    simpa [E.selfSeam_solid_ne hj hc3, Ne.symm (E.selfSeam_solid_ne hj hc3)] using h.symm
  · have h := congrArg Finset.card (E.selfSeam_seams_eq_pair hj hc3 hl hr)
    simpa [E.selfSeam_arm_ne hj hc3 hl] using h

theorem selfSeam_configuration (hE : E.IsMoveFree)
    (hR : ∀ a, E.kind (E.toTorus.rightPiece a) ≠ 1) (hc : 0 < E.armCount c)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) :
    ∃ j, E.IsArm c j ∧ E.kind c = 3 ∧ 2 ≤ E.fillingDistance j true ∧
      E.armCount c = 1 ∧ E.toTorus.components.count = 2 ∧ E.toTorus.pairing.count = 2 := by
  obtain ⟨a⟩ : Nonempty {a // E.IsArm c a} := Fintype.card_pos_iff.mp hc
  obtain ⟨hc3, hd⟩ := E.two_le_fillingDistance hE hR a
  have hn := E.selfSeam_counts a.property hc3 hl hr
  exact ⟨a.val, a.property, hc3, hd, E.selfSeam_armCount a.property hc3 hl hr, hn⟩

theorem selfSeam_centreData_good (hE : E.IsMoveFree)
    (hR : ∀ a, E.kind (E.toTorus.rightPiece a) ≠ 1) (hc : 0 < E.armCount c)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c)
    (V : CompactCarrier.{u}) (B : SeifertBlock V (E.centreData hE hR c)) : B.IsGoodBlock := by
  obtain ⟨j, hj, hc3, hd, hm, hn⟩ := E.selfSeam_configuration hE hR hc hl hr
  apply filledBlockGoodness V (E.centreData hE hR c) B
  · change 0 < 3 - E.armCount c
    omega
  · change ¬ (3 - E.armCount c = 1 ∧ _)
    omega


def selfSeamSet (c : Fin E.toTorus.components.count) (j : Fin E.toTorus.pairing.count) :
    Finset (Fin E.toTorus.components.count) := {c, E.toTorus.leftPiece j}

def selfSeamSelected (j : Fin E.toTorus.pairing.count) : Finset (Fin E.toTorus.pairing.count) :=
  {j}

theorem selfSeam_selected_internal (hj : E.IsArm c j) :
    ∀ a ∈ E.selfSeamSelected j,
      E.toTorus.leftPiece a ∈ E.selfSeamSet c j ∧
        E.toTorus.rightPiece a ∈ E.selfSeamSet c j := by
  classical
  intro a ha
  have he : a = j := Finset.mem_singleton.mp ha
  subst a
  simp [selfSeamSet, hj.1]

def selfSeamQuotientPieceMap (hj : E.IsArm c j)
    (i : Fin E.toTorus.components.count) (hi : i ∈ E.selfSeamSet c j) :
    E.toTorus.components.piece i →
      (E.toTorus.restrictAlongPairing (E.selfSeamSet c j) (E.selfSeamSelected j)
        (E.selfSeam_selected_internal hj)).QuotientSpace :=
  fun x => (E.toTorus.restrictAlongPairing (E.selfSeamSet c j) (E.selfSeamSelected j)
    (E.selfSeam_selected_internal hj)).quotientMap
      ⟨x.val, E.toTorus.piece_subset_subPiece (E.selfSeamSet c j) hi x.property⟩

theorem selfSeamQuotientPieceMap_continuous (hj : E.IsArm c j)
    (i : Fin E.toTorus.components.count) (hi : i ∈ E.selfSeamSet c j) :
    Continuous (E.selfSeamQuotientPieceMap hj i hi) :=
  (E.toTorus.restrictAlongPairing (E.selfSeamSet c j) (E.selfSeamSelected j)
    (E.selfSeam_selected_internal hj)).quotientMap.continuous.comp
      (continuous_subtype_val.subtype_mk fun x =>
        E.toTorus.piece_subset_subPiece (E.selfSeamSet c j) hi x.property)

theorem selfSeam_selected_connected (hj : E.IsArm c j) :
    ConnectedSpace (E.toTorus.restrictAlongPairing (E.selfSeamSet c j)
      (E.selfSeamSelected j) (E.selfSeam_selected_internal hj)).QuotientSpace := by
  classical
  let S := E.selfSeamSet c j
  let K := E.selfSeamSelected j
  let hK := E.selfSeam_selected_internal hj
  let P := E.toTorus.restrictAlongPairing S K hK
  have hcS : c ∈ S := by simp [S, selfSeamSet]
  have hjS : E.toTorus.leftPiece j ∈ S := by simp [S, selfSeamSet]
  let f := E.selfSeamQuotientPieceMap hj c hcS
  let g := E.selfSeamQuotientPieceMap hj (E.toTorus.leftPiece j) hjS
  have hfc : IsConnected (Set.range f) := by
    let := E.toTorus.components.connected c
    exact isConnected_range (E.selfSeamQuotientPieceMap_continuous hj c hcS)
  have hgc : IsConnected (Set.range g) := by
    let := E.toTorus.components.connected (E.toTorus.leftPiece j)
    exact isConnected_range
      (E.selfSeamQuotientPieceMap_continuous hj (E.toTorus.leftPiece j) hjS)
  have hcov : Set.range f ∪ Set.range g = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    obtain ⟨i, hi, hxi⟩ := (E.toTorus.mem_subPiece S).mp x.property
    simp only [S, selfSeamSet, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Or.inl ⟨⟨x.val, hxi⟩, rfl⟩
    · exact Or.inr ⟨⟨x.val, hxi⟩, rfl⟩
  let a : Fin K.card := ⟨0, by simp [K, selfSeamSelected]⟩
  have ha : (E.toTorus.alongSeam K a).val = j := by
    have ha' := (E.toTorus.alongSeam K a).property
    exact Finset.mem_singleton.mp ha'
  let x := P.leftParam a 1
  let y := P.rightParam a (P.matching a 1)
  have hx : x.val.val ∈ E.toTorus.components.piece (E.toTorus.leftPiece j) := by
    apply E.toTorus.left_owned j
    have hh := x.property
    change x.val.val ∈ E.toTorus.pairing.gluing.left
      (E.toTorus.keptSeam S (E.toTorus.alongKeptIndex S K hK a)).val at hh
    simpa only [E.toTorus.keptSeam_alongKeptIndex, ha] using hh
  have hy : y.val.val ∈ E.toTorus.components.piece c := by
    rw [← hj.1]
    apply E.toTorus.right_owned j
    have hh := y.property
    change y.val.val ∈ E.toTorus.pairing.gluing.right
      (E.toTorus.keptSeam S (E.toTorus.alongKeptIndex S K hK a)).val at hh
    simpa only [E.toTorus.keptSeam_alongKeptIndex, ha] using hh
  have hxy : P.quotientMap x.val = P.quotientMap y.val := by
    apply Quotient.sound
    have hh := P.gluing.rel_of_mem_left x.property
    have he := congrArg Subtype.val (P.matching_eq a 1)
    exact he ▸ hh
  have hinter : (Set.range f ∩ Set.range g).Nonempty :=
    ⟨P.quotientMap y.val, ⟨⟨y.val.val, hy⟩, rfl⟩, ⟨⟨x.val.val, hx⟩, hxy⟩⟩
  exact connectedSpace_iff_univ.mpr (hcov ▸ hfc.union hinter hgc)

theorem selfSeam_selected_interior_connected (hj : E.IsArm c j) :
    IsConnected ((E.toTorus.restrictAlongCarrier (E.selfSeamSet c j)
      (E.selfSeamSelected j) (E.selfSeam_selected_internal hj)
      (Grouping.hext_of_externalCount E.toTorus.externalCount_eq_zero
        (E.selfSeamSet c j))).interior :
          Set (E.toTorus.restrictAlongPairing (E.selfSeamSet c j)
            (E.selfSeamSelected j) (E.selfSeam_selected_internal hj)).QuotientSpace) := by
  let C := E.toTorus.restrictAlongCarrier (E.selfSeamSet c j)
    (E.selfSeamSelected j) (E.selfSeam_selected_internal hj)
    (Grouping.hext_of_externalCount E.toTorus.externalCount_eq_zero (E.selfSeamSet c j))
  let : ChartedSpace (EuclideanHalfSpace 3) C.Carrier := C.charts
  let : IsManifold C.model ∞ C.Carrier := C.smooth
  let : ConnectedSpace C.Carrier := E.selfSeam_selected_connected hj
  exact ⟨Manifold.dense_manifold_interior.nonempty,
    Manifold.isPreconnected_manifold_interior⟩


def selfSeamContracted (hj : E.IsArm c j) : TorusPresentation (NoCuts.carrier Q) :=
  E.toTorus.contractAlong (E.selfSeamSet c j) (E.selfSeamSelected j)
    (E.selfSeam_selected_internal hj)
    (Grouping.hext_of_externalCount E.toTorus.externalCount_eq_zero (E.selfSeamSet c j))
    (E.toTorus.cutCarrier_kind_of_pos (Fin.pos j))
    (E.selfSeam_selected_interior_connected hj)

theorem selfSeamContracted_counts (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) :
    (E.selfSeamContracted hj).components.count = 1 ∧
      (E.selfSeamContracted hj).pairing.count = 1 ∧
        (E.selfSeamContracted hj).externalCount = 0 := by
  classical
  have hS : E.selfSeamSet c j = Finset.univ := E.selfSeam_set_eq_univ hj hc3 hl hr
  have hn := E.selfSeam_counts hj hc3 hl hr
  refine ⟨?_, ?_, E.toTorus.externalCount_eq_zero⟩
  · rw [selfSeamContracted, E.toTorus.contractAlong_components_count]
    rw [hS, Finset.card_univ, Fintype.card_fin]
    omega
  · rw [selfSeamContracted, E.toTorus.contractAlong_pairing_count]
    simp [selfSeamSelected, hn.2]

theorem selfSeamContracted_self_seam (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c)
    (a : Fin (E.selfSeamContracted hj).pairing.count) :
    (E.selfSeamContracted hj).leftPiece a = (E.selfSeamContracted hj).rightPiece a := by
  have hn := (E.selfSeamContracted_counts hj hc3 hl hr).1
  exact Fin.cast_injective hn
    (Subsingleton.elim ((E.selfSeamContracted hj).leftPiece a |>.cast hn)
      ((E.selfSeamContracted hj).rightPiece a |>.cast hn))

def selfSeam_surviving_seam (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) : Fin (E.selfSeamContracted hj).pairing.count :=
  Fintype.equivFin (E.toTorus.AlongUnpairedSeam (E.selfSeamSelected j))
    ⟨k, by simpa [selfSeamSelected] using Ne.symm (E.selfSeam_arm_ne hj hc3 hl)⟩

theorem selfSeam_surviving_matching (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) :
    (E.selfSeamContracted hj).pairing.matching (E.selfSeam_surviving_seam hj hc3 hl) =
      E.toTorus.pairing.matching k := by
  change E.toTorus.pairing.matching
    ((Fintype.equivFin (E.toTorus.AlongUnpairedSeam (E.selfSeamSelected j))).symm
      (Fintype.equivFin (E.toTorus.AlongUnpairedSeam (E.selfSeamSelected j))
        ⟨k, by simpa [selfSeamSelected] using Ne.symm (E.selfSeam_arm_ne hj hc3 hl)⟩)).val = _
  rw [Equiv.symm_apply_apply]

def selfSeamBoundarySide (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) (b : Bool) :
    E.toTorus.AlongBoundarySide (E.selfSeamSet c j) (E.selfSeamSelected j) := by
  classical
  have hkj : k ∉ E.selfSeamSelected j := by
    simpa [selfSeamSelected] using Ne.symm (E.selfSeam_arm_ne hj hc3 hl)
  cases b
  · exact ⟨.inr (.inl k), by simp [selfSeamSet, TorusPresentation.sidePiece, hr], hkj⟩
  · exact ⟨.inl k, by simp [selfSeamSet, TorusPresentation.sidePiece, hl], hkj⟩

theorem selfSeamBoundarySide_bijective (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) :
    Function.Bijective (E.selfSeamBoundarySide hj hc3 hl hr) := by
  classical
  constructor
  · intro a b hab
    have hh := congrArg Subtype.val hab
    cases a <;> cases b <;> simp [selfSeamBoundarySide] at hh ⊢
  · rintro ⟨a, ha⟩
    rcases a with a | a | a
    · rcases E.selfSeam_all_seams hj hc3 hl hr a with rfl | rfl
      · exact (ha.2 (by simp [selfSeamSelected])).elim
      · exact ⟨true, rfl⟩
    · rcases E.selfSeam_all_seams hj hc3 hl hr a with rfl | rfl
      · exact (ha.2 (by simp [selfSeamSelected])).elim
      · exact ⟨false, rfl⟩
    · exact Fin.elim0 (a.cast E.toTorus.externalCount_eq_zero)

def selfSeamBoundarySideEquiv (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) :
    Bool ≃ E.toTorus.AlongBoundarySide (E.selfSeamSet c j) (E.selfSeamSelected j) :=
  Equiv.ofBijective _ (E.selfSeamBoundarySide_bijective hj hc3 hl hr)

theorem selfSeamBoundarySide_card (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) :
    Fintype.card (E.toTorus.AlongBoundarySide (E.selfSeamSet c j)
      (E.selfSeamSelected j)) = 2 :=
  (Fintype.card_congr (E.selfSeamBoundarySideEquiv hj hc3 hl hr)).symm


theorem selfSeam_good_blockedPresentation (hE : E.IsMoveFree)
    (hR : ∀ a, E.kind (E.toTorus.rightPiece a) ≠ 1) (hc : 0 < E.armCount c)
    (hj : E.IsArm c j) (hc3 : E.kind c = 3)
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c)
    (B : PieceBlock (E.selfSeamContracted hj) (Fin.last (E.selfSeamSet c j)ᶜ.card))
    (hB : B.data = E.centreData hE hR c) : GoodBlockUnion Q := by
  have hn := (E.selfSeamContracted_counts hj hc3 hl hr).1
  have he : ∀ i : Fin (E.selfSeamContracted hj).components.count,
      Fin.last (E.selfSeamSet c j)ᶜ.card = i := by
    intro i
    exact Fin.cast_injective hn (Subsingleton.elim _ _)
  refine ⟨BlockedPresentation.ofPieceBlocks (E.selfSeamContracted hj)
    (fun i => B.congrIndex (he i)), ?_⟩
  intro i
  have hg : B.block.IsGoodBlock := by
    have hs : GoodData.{u} (E.centreData hE hR c) :=
      E.selfSeam_centreData_good hE hR hc hl hr
    have ht : GoodData.{u} B.data := hB.symm ▸ hs
    exact ht _ B.block
  have hh := he i
  subst i
  exact hg

end GC.Seifert.ElementaryPresentation

namespace GC.Seifert.ElementaryPresentation

variable {Q : ConnectedClosedOrientedManifold.{u} 3}
  (E : ElementaryPresentation (NoCuts.carrier Q))
  {c : Fin E.toTorus.components.count} {j k : Fin E.toTorus.pairing.count}
  (hj : E.IsArm c j) (hc3 : E.kind c = 3)
  (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c)

def selfSeamRegionGeometry : TorusPresentation.AlongPieceGeometry (NoCuts.carrier Q) :=
  E.toTorus.alongRegionGeometry (E.selfSeamSet c j) (E.selfSeamSelected j)
    (E.selfSeam_selected_internal hj)
    (Grouping.hext_of_externalCount E.toTorus.externalCount_eq_zero (E.selfSeamSet c j))
    (E.toTorus.restrictAlong_hconn_complement (E.selfSeamSet c j) (E.selfSeamSelected j)
      (E.selfSeam_selected_internal hj)
      (Grouping.hext_of_externalCount E.toTorus.externalCount_eq_zero (E.selfSeamSet c j))
      (E.selfSeam_selected_interior_connected hj))

def selfSeamRegionTorusCount (a : Fin 1) : ℕ :=
  Function.const (Fin 1) (E.selfSeamRegionGeometry hj).torusCount a

def selfSeamRegionSide (a : Fin 1) (b : Bool) :
    Σ i : Fin 1, Fin (E.selfSeamRegionTorusCount hj i) :=
  ⟨a, Fintype.equivFin
    (E.toTorus.AlongBoundarySide (E.selfSeamSet c j) (E.selfSeamSelected j))
      (E.selfSeamBoundarySide hj hc3 hl hr b)⟩

theorem selfSeamRegionSides_bijective :
    Function.Bijective (Sum.elim
      (fun ab : Fin 1 × Bool => E.selfSeamRegionSide hj hc3 hl hr ab.1 ab.2)
      (fun a : Fin 0 => a.elim0)) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · rintro (⟨a, b⟩ | a) (⟨a', b'⟩ | a') h
    · apply congrArg Sum.inl
      apply Prod.ext (Subsingleton.elim a a')
      have ha : a = a' := Subsingleton.elim a a'
      subst a'
      have hv := sigma_mk_injective h
      exact (E.selfSeamBoundarySide_bijective hj hc3 hl hr).1
        ((Fintype.equivFin _).injective hv)
    · exact a'.elim0
    · exact a.elim0
    · exact a.elim0
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma,
      Fintype.card_fin, Fintype.card_bool, selfSeamRegionTorusCount]
    change 1 * 2 + 0 = ∑ i : Fin 1, Fintype.card (E.toTorus.AlongBoundarySide
      (E.selfSeamSet c j) (E.selfSeamSelected j))
    simp [E.selfSeamBoundarySide_card hj hc3 hl hr]

def selfSeamOneCutSystem : EmbeddedCutSystem (NoCuts.carrier Q) .withBoundary := by
  let G := E.selfSeamRegionGeometry hj
  let S := E.selfSeamSet c j
  let K := E.selfSeamSelected j
  let hK := E.selfSeam_selected_internal hj
  let hext := Grouping.hext_of_externalCount E.toTorus.externalCount_eq_zero S
  let hconn := E.toTorus.restrictAlong_hconn_complement S K hK hext
    (E.selfSeam_selected_interior_connected hj)
  refine {
    count := 1
    count_pos := Nat.one_pos
    Piece := fun i => G.Carrier
    topology := fun i => G.topology
    charts := fun i => G.charts
    manifold := fun i => G.manifold
    compact := fun i => G.compact
    hausdorff := fun i => G.hausdorff
    secondCountable := fun i => G.secondCountable
    connected := fun i => G.connected
    map := fun i => G.map
    smooth := fun i => G.smooth
    mfderiv_bijective := fun i => G.mfderiv_bijective
    covers := ?_
    torusCount := E.selfSeamRegionTorusCount hj
    collar := fun i => G.collar
    collar_source := fun i => G.collar_source
    collar_disjoint := fun i => G.collar_disjoint
    boundary_exhausted := fun i => G.boundary_exhausted
    seamCount := 1
    side := E.selfSeamRegionSide hj hc3 hl hr
    externalCount := 0
    externalSide := fun a => a.elim0
    sides_bijective := E.selfSeamRegionSides_bijective hj hc3 hl hr
    matching := fun a => E.toTorus.pairing.matching k
    seam := fun a => E.toTorus.seam k
    seam_source := fun a => E.toTorus.seam_source k
    seam_neg := ?_
    seam_pos := ?_
    seam_interior := fun a => E.toTorus.seam_interior k
    external_local := fun a => a.elim0
    overlap := ?_ }
  · apply Set.eq_univ_of_forall
    intro y
    let q := E.toTorus.reconstruction.symm y
    obtain ⟨x, hx⟩ := Quotient.exists_rep q
    have hy : E.toTorus.cutMap x = y := by
      change E.toTorus.reconstruction (E.toTorus.pairing.quotientMap x) = y
      change E.toTorus.pairing.quotientMap x = q at hx
      rw [hx]
      exact E.toTorus.reconstruction.apply_symm_apply y
    have hxS : x ∈ E.toTorus.subPiece S := by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (E.toTorus.components.covers ▸ Set.mem_univ x)
      exact E.toTorus.piece_subset_subPiece S (E.selfSeam_all_pieces hj hc3 hl hr i) hi
    exact Set.mem_iUnion.mpr ⟨0, ⟨(E.toTorus.restrictAlongPairing S K hK).quotientMap
      ⟨x, hxS⟩, hy⟩⟩
  · intro a t s hs h1
    have hp : (t, halfPoint (-s) (neg_nonneg.mpr hs)) ∈ halfCollarSource := by
      change -s < 1
      linarith
    change E.toTorus.seam k (t, s) = E.toTorus.restrictAlongMap S K hK
      (E.toTorus.restrictAlongHalfCollar S K hK
        (E.toTorus.alongBoundarySide S K
          (Fintype.equivFin _ (E.selfSeamBoundarySide hj hc3 hl hr true)))
            (t, halfPoint (-s) (neg_nonneg.mpr hs)))
    rw [E.toTorus.alongBoundarySide_equivFin,
      E.toTorus.restrictAlongHalfCollar_apply S K hK _ hp,
      E.toTorus.restrictAlongMap_quotientMap,
      E.toTorus.subCollar_apply S _ _ hp]
    exact E.toTorus.seam_negative k t s hs h1
  · intro a t s hs h1
    have hp : (E.toTorus.pairing.matching k t, halfPoint s hs) ∈ halfCollarSource := h1
    change E.toTorus.seam k (t, s) = E.toTorus.restrictAlongMap S K hK
      (E.toTorus.restrictAlongHalfCollar S K hK
        (E.toTorus.alongBoundarySide S K
          (Fintype.equivFin _ (E.selfSeamBoundarySide hj hc3 hl hr false)))
            (E.toTorus.pairing.matching k t, halfPoint s hs))
    rw [E.toTorus.alongBoundarySide_equivFin,
      E.toTorus.restrictAlongHalfCollar_apply S K hK _ hp,
      E.toTorus.restrictAlongMap_quotientMap,
      E.toTorus.subCollar_apply S _ _ hp]
    exact E.toTorus.seam_positive k t s hs h1
  · intro a b q q' he
    rcases E.toTorus.alongGeometry_overlap S K hK hext
      (E.toTorus.cutCarrier_kind_of_pos (Fin.pos j)) hconn (.inr ()) (.inr ())
      q q' he with hq | ⟨r, t, hrt⟩
    · have hab : a = b := Subsingleton.elim a b
      subst b
      have heq : q = q' := by
        cases hq
        rfl
      exact Or.inl (congrArg (Sigma.mk a) heq)
    · have hrk : r.val = k := by
        rcases E.selfSeam_all_seams hj hc3 hl hr r.val with hj' | hk'
        · exact (r.property (hj' ▸ Finset.mem_singleton_self j)).elim
        · exact hk'
      exact Or.inr ⟨0, t, hrk ▸ hrt⟩


def selfSeamOneIndex : Fin (E.selfSeamOneCutSystem hj hc3 hl hr).count :=
  ⟨0, by change 0 < 1; omega⟩

local instance selfSeamOneCutCharts :
    ChartedSpace (E.selfSeamOneCutSystem hj hc3 hl hr).cutCarrier.kind.Space
      (E.selfSeamOneCutSystem hj hc3 hl hr).cutCarrier.Carrier :=
  (E.selfSeamOneCutSystem hj hc3 hl hr).cutCarrier.charts

local instance selfSeamOneCutSmooth :
    IsManifold (E.selfSeamOneCutSystem hj hc3 hl hr).cutCarrier.model ∞
      (E.selfSeamOneCutSystem hj hc3 hl hr).cutCarrier.Carrier :=
  (E.selfSeamOneCutSystem hj hc3 hl hr).cutCarrier.smooth

def selfSeamOnePieceDiffeomorph :
    (E.selfSeamRegionGeometry hj).Carrier ≃ₘ⟮CarrierModel.withBoundary.model,
      (E.selfSeamOneCutSystem hj hc3 hl hr).cutCarrier.model⟯
        (E.selfSeamOneCutSystem hj hc3 hl hr).components.piece (E.selfSeamOneIndex hj hc3 hl hr) :=
  (E.selfSeamOneCutSystem hj hc3 hl hr).pieceDiffeomorph (E.selfSeamOneIndex hj hc3 hl hr)

local instance selfSeamOnePieceSmooth :
    IsManifold (E.selfSeamOneCutSystem hj hc3 hl hr).cutCarrier.model ∞
      ((E.selfSeamOneCutSystem hj hc3 hl hr).components.piece
        (E.selfSeamOneIndex hj hc3 hl hr)) :=
  (GC.Topology.componentCarrier (E.selfSeamOneCutSystem hj hc3 hl hr).cutCarrier
    (E.selfSeamOneCutSystem hj hc3 hl hr).components
    (E.selfSeamOneIndex hj hc3 hl hr)).smooth

theorem selfSeamOnePieceDiffeomorph_preservesOrientation :
    letI := E.selfSeamOnePieceSmooth hj hc3 hl hr
    (E.selfSeamOnePieceDiffeomorph hj hc3 hl hr).preservesOrientation
      (E.toTorus.restrictAlongCarrier (E.selfSeamSet c j) (E.selfSeamSelected j)
        (E.selfSeam_selected_internal hj)
        (Grouping.hext_of_externalCount E.toTorus.externalCount_eq_zero
          (E.selfSeamSet c j))).orientation
      (GC.Topology.componentCarrier (E.selfSeamOneCutSystem hj hc3 hl hr).cutCarrier
        (E.selfSeamOneCutSystem hj hc3 hl hr).components
        (E.selfSeamOneIndex hj hc3 hl hr)).orientation := by
  let := E.selfSeamOnePieceSmooth hj hc3 hl hr
  let G := E.selfSeamRegionGeometry hj
  let A := E.selfSeamOneCutSystem hj hc3 hl hr
  let S := E.selfSeamSet c j
  let K := E.selfSeamSelected j
  let hK := E.selfSeam_selected_internal hj
  let hext := Grouping.hext_of_externalCount E.toTorus.externalCount_eq_zero S
  let C := E.toTorus.restrictAlongCarrier S K hK hext
  let : ChartedSpace (EuclideanHalfSpace 3) C.Carrier := C.charts
  let : IsManifold C.model ∞ C.Carrier := C.smooth
  have hG : IsOrientedFold (W := NoCuts.carrier Q) (C := C) G.map := by
    intro q
    refine ⟨(Manifold.differentialEquivOfBijective C.model (NoCuts.carrier Q).model
      G.map G.mfderiv_bijective q).toLinearEquiv, fun v => rfl, ?_⟩
    exact Manifold.orientation_map_manifoldOrientationPullback C.model (NoCuts.carrier Q).model
      finrank_euclideanSpace_fin G.map G.smooth G.mfderiv_bijective
      (NoCuts.carrier Q).orientation q
  have hA : IsOrientedFold (W := NoCuts.carrier Q) (C := A.cutCarrier) A.fold := by
    intro q
    exact ⟨(Manifold.differentialEquivOfBijective CarrierModel.withBoundary.model
      (NoCuts.carrier Q).model A.fold A.mfderiv_fold_bijective q).toLinearEquiv,
      fun v => rfl, A.orientation_map_cutOrientation q⟩
  exact preservesOrientation_of_comp (E.selfSeamOnePieceDiffeomorph hj hc3 hl hr)
    G.map (A.fold ∘ Subtype.val)
    (fun q => (A.contMDiff_fold.comp contMDiff_subtype_val).mdifferentiableAt (by simp))
    (fun q => rfl) _ _ (NoCuts.carrier Q).orientation hG (hA.restrict A.contMDiff_fold _)

theorem selfSeamOnePieceDiffeomorph_collar
    (r : Fin (E.selfSeamRegionGeometry hj).torusCount)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
    E.selfSeamOnePieceDiffeomorph hj hc3 hl hr ((E.selfSeamRegionGeometry hj).collar r p) =
      (E.selfSeamOneCutSystem hj hc3 hl hr).toTorusPresentation.pieceCollar
        (E.selfSeamOneIndex hj hc3 hl hr)
        ((E.selfSeamOneCutSystem hj hc3 hl hr).port
          (E.selfSeamOneIndex hj hc3 hl hr) r) p := by
  let A := E.selfSeamOneCutSystem hj hc3 hl hr
  apply Subtype.ext
  rw [TorusPresentation.pieceCollar_apply _ _ _ hp]
  rw [A.sideCollar_eq, A.sideOf_port, A.sideCollar_apply]
  rfl

def selfSeamOnePieceBlock {d : SeifertData}
    (B : SeifertBlock
      (E.toTorus.restrictAlongCarrier (E.selfSeamSet c j) (E.selfSeamSelected j)
        (E.selfSeam_selected_internal hj)
        (Grouping.hext_of_externalCount E.toTorus.externalCount_eq_zero (E.selfSeamSet c j))) d)
    (e : Fin B.presentation.externalCount ≃ Fin (E.selfSeamRegionGeometry hj).torusCount)
    (he : ∀ r p, p ∈ halfCollarSource → B.presentation.external.collar r p =
      (E.selfSeamRegionGeometry hj).collar (e r) p) :
    PieceBlock (E.selfSeamOneCutSystem hj hc3 hl hr).toTorusPresentation
      (E.selfSeamOneIndex hj hc3 hl hr) where
  data := d
  block := B.transport (E.selfSeamOnePieceDiffeomorph hj hc3 hl hr)
    (E.selfSeamOnePieceDiffeomorph_preservesOrientation hj hc3 hl hr)
  port := e.trans ((E.selfSeamOneCutSystem hj hc3 hl hr).port (E.selfSeamOneIndex hj hc3 hl hr))
  collar_eq r p hp := by
    change E.selfSeamOnePieceDiffeomorph hj hc3 hl hr
      (B.presentation.external.collar r p) = _
    rw [he r p hp]
    exact E.selfSeamOnePieceDiffeomorph_collar hj hc3 hl hr (e r) p hp

end GC.Seifert.ElementaryPresentation

namespace GC.Seifert.ElementaryPresentation

theorem seifertFactor_of_centre_selfSeam_proved {Q : ConnectedClosedOrientedManifold.{u} 3}
    (E : ElementaryPresentation (NoCuts.carrier Q)) (hE : E.IsMoveFree)
    (hR : ∀ j, E.kind (E.toTorus.rightPiece j) ≠ 1) {c : Fin E.toTorus.components.count}
    (hc : 0 < E.armCount c) {k : Fin E.toTorus.pairing.count}
    (hl : E.toTorus.leftPiece k = c) (hr : E.toTorus.rightPiece k = c) : SeifertFactor Q := by
  obtain ⟨j, hj, hc3, hd, hm, hn⟩ := E.selfSeam_configuration hE hR hc hl hr
  have hu : ∀ a, E.IsArm c a → a = j :=
    fun a ha => E.selfSeam_arm_unique hj hc3 hl hr ⟨a, ha⟩
  obtain ⟨B, e, he⟩ := E.exists_centreSingleArmBlock hE hR c hc3 hj hu
    (Grouping.hext_of_externalCount E.toTorus.externalCount_eq_zero (E.selfSeamSet c j))
  let P := E.selfSeamOnePieceBlock hj hc3 hl hr B e he
  let A := E.selfSeamOneCutSystem hj hc3 hl hr
  have hP : P.block.IsGoodBlock := E.selfSeam_centreData_good hE hR hc hl hr _ P.block
  have ha : A.count = 1 := rfl
  have hi : ∀ i : Fin A.count, E.selfSeamOneIndex hj hc3 hl hr = i := by
    intro i
    exact Fin.cast_injective ha (Subsingleton.elim _ _)
  refine Or.inr (Or.inr ⟨BlockedPresentation.ofPieceBlocks A.toTorusPresentation
    (fun i => P.congrIndex (hi i)), ?_⟩)
  intro i
  have hh := hi i
  subst i
  exact hP

end GC.Seifert.ElementaryPresentation
