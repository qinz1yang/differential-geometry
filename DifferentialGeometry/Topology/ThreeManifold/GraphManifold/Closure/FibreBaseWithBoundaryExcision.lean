import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RegularFibreTube
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryAtlas
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Tangent
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Maps
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpaceInteriorSmooth
import DifferentialGeometry.Topology.PuncturedConnected

/-!
A fixed interior disc is excised from an actual compact surface, retaining its existing boundary.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.GraphManifold.CompactSurface

variable (B : CompactSurface.{u})
variable (β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model B.kind)
  PlaneLift.{u} B.Carrier ∞)
variable (hβ : {z : PlaneLift.{u} | ‖z.down‖ ≤ 3} ⊆ β.source)

private def punctureSet : Set B.Carrier := (β '' {z : PlaneLift.{u} | ‖z.down‖ < 1})ᶜ

private def retainedSet : Set B.Carrier := (β '' {z : PlaneLift.{u} | ‖z.down‖ ≤ 1})ᶜ

include hβ in
private theorem retained_open : IsOpen (retainedSet B β) := by
  have hc : IsCompact {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} := by
    have he : {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} =
        ULift.up '' closedBall (0 : ℂ) 1 := by
      ext z
      simp only [mem_ofPred_eq, mem_image, mem_closedBall_zero_iff]
      exact ⟨fun hz => ⟨z.down, hz, ULift.up_down z⟩,
        fun ⟨w, hw, he⟩ => he ▸ hw⟩
    rw [he]
    exact (isCompact_closedBall (0 : ℂ) 1).image contMDiff_planeLift_up.continuous
  have hs : {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} ⊆ β.source := by
    intro z hz
    apply hβ
    change ‖z.down‖ ≤ 3
    change ‖z.down‖ ≤ 1 at hz
    linarith
  exact (hc.image_of_continuousOn (β.contMDiffOn.continuousOn.mono hs)).isClosed.isOpen_compl

private theorem retained_subset : retainedSet B β ⊆ punctureSet B β := by
  intro x hx
  rintro ⟨z, hz, he⟩
  apply hx
  refine ⟨z, ?_, he⟩
  change ‖z.down‖ ≤ 1
  change ‖z.down‖ < 1 at hz
  exact le_of_lt hz

private def puncturePlaneCoordinates :
    EuclideanSpace ℝ (Fin 2) ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℂ)⟯ PlaneLift.{u} :=
  Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.toDiffeomorph.trans
    (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ)

private theorem puncturePlaneCoordinates_norm (z : EuclideanSpace ℝ (Fin 2)) :
    ‖(puncturePlaneCoordinates.{u} z).down‖ = ‖z‖ :=
  Complex.orthonormalBasisOneI.repr.symm.norm_map z

private theorem puncture_image_ball :
    (puncturePlaneCoordinates.{u}.toPartialDiffeomorph.trans β) ''
      ball (0 : EuclideanSpace ℝ (Fin 2)) 1 = β '' {z : PlaneLift.{u} | ‖z.down‖ < 1} := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨puncturePlaneCoordinates.{u} z, ?_, rfl⟩
    change ‖(puncturePlaneCoordinates.{u} z).down‖ < 1
    rw [puncturePlaneCoordinates_norm]
    exact mem_ball_zero_iff.mp hz
  · rintro ⟨z, hz, rfl⟩
    refine ⟨puncturePlaneCoordinates.{u}.symm z, ?_, ?_⟩
    · have he := puncturePlaneCoordinates_norm.{u} (puncturePlaneCoordinates.{u}.symm z)
      rw [Diffeomorph.apply_symm_apply] at he
      exact mem_ball_zero_iff.mpr (he ▸ hz)
    · change β (puncturePlaneCoordinates (puncturePlaneCoordinates.{u}.symm z)) = β z
      rw [Diffeomorph.apply_symm_apply]

include hβ in
private theorem puncture_connected : IsConnected (punctureSet B β) := by
  let e := puncturePlaneCoordinates.{u}.toPartialDiffeomorph.trans β
  have hs : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ e.source := by
    intro z hz
    refine ⟨mem_univ z, hβ ?_⟩
    change ‖(puncturePlaneCoordinates.{u} z).down‖ ≤ 3
    rw [puncturePlaneCoordinates_norm]
    exact le_trans (mem_closedBall_zero_iff.mp hz) (by norm_num)
  have : LocallyPathConnectedSpace (SurfaceModel.Space B.kind) := by
    cases B.kind <;> infer_instance
  have : LocallyPathConnectedSpace B.Carrier :=
    ChartedSpace.locallyPathConnectedSpace (SurfaceModel.Space B.kind) B.Carrier
  have hr : (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin 2)) :=
    Module.one_lt_rank_of_one_lt_finrank (by simp)
  have h := (isPathConnected_compl_image_ball e.toOpenPartialHomeomorph hr hs).isConnected
  change IsConnected (e '' ball (0 : EuclideanSpace ℝ (Fin 2)) 1)ᶜ at h
  change IsConnected (β '' {z : PlaneLift.{u} | ‖z.down‖ < 1})ᶜ
  rwa [puncture_image_ball] at h

private def puncturePoint : punctureSet B β :=
  ⟨(puncture_connected B β hβ).nonempty.choose,
    (puncture_connected B β hβ).nonempty.choose_spec⟩

private def retainedPatch : OpenPartialHomeomorph B.Carrier (punctureSet B β) := by
  classical
  exact {
  toFun x := if hx : x ∈ punctureSet B β then ⟨x, hx⟩ else puncturePoint B β hβ
  invFun := Subtype.val
  source := retainedSet B β
  target := Subtype.val ⁻¹' retainedSet B β
  map_source' x hx := by
    change (if hx' : x ∈ punctureSet B β then (⟨x, hx'⟩ : punctureSet B β)
      else puncturePoint B β hβ).val ∈ retainedSet B β
    rw [dite_eq_left (retained_subset B β hx)]
    exact hx
  map_target' x hx := hx
  left_inv' x hx := by
    change (if hx' : x ∈ punctureSet B β then (⟨x, hx'⟩ : punctureSet B β)
      else puncturePoint B β hβ).val = x
    rw [dite_eq_left (retained_subset B β hx)]
  right_inv' x hx := by
    change (if hx' : x.val ∈ punctureSet B β then (⟨x.val, hx'⟩ : punctureSet B β)
      else puncturePoint B β hβ) = x
    rw [dite_eq_left x.property]
  open_source := retained_open B β hβ
  open_target := (retained_open B β hβ).preimage continuous_subtype_val
  continuousOn_toFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (continuous_id.continuousOn : ContinuousOn id (retainedSet B β)).congr
    intro x hx
    change (if hx' : x ∈ punctureSet B β then (⟨x, hx'⟩ : punctureSet B β)
      else puncturePoint B β hβ).val = x
    rw [dite_eq_left (retained_subset B β hx)]
  continuousOn_invFun := continuous_subtype_val.continuousOn }

private theorem retainedPatch_apply (x : B.Carrier) (hx : x ∈ retainedSet B β) :
    (retainedPatch B β hβ x).val = x := by
  classical
  change (if hx' : x ∈ punctureSet B β then (⟨x, hx'⟩ : punctureSet B β)
    else puncturePoint B β hβ).val = x
  rw [dite_eq_left (retained_subset B β hx)]

private def twicePlane : PlaneLift.{u} ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ PlaneLift.{u} :=
  (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).symm.trans
    (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ)
      (Units.mk0 (2 : ℝ) (by norm_num))).toDiffeomorph).trans
        (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ))

private def annulusAmbient :
    PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model B.kind)
      PlaneLift.{u} B.Carrier ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    (twicePlane.toPartialDiffeomorph.trans β) {z | ‖z.down‖ < 3 / 4}
    (isOpen_lt (continuous_norm.comp contMDiff_planeLift_down.continuous) continuous_const)

include hβ in
private theorem annulusAmbient_source :
    (annulusAmbient B β).source = {z : PlaneLift.{u} | ‖z.down‖ < 3 / 4} := by
  ext z
  change ((z ∈ univ ∧ twicePlane z ∈ β.source) ∧ ‖z.down‖ < 3 / 4) ↔ _
  constructor
  · exact And.right
  · intro hz
    refine ⟨⟨mem_univ z, hβ ?_⟩, hz⟩
    change ‖(2 : ℝ) • z.down‖ ≤ 3
    rw [norm_smul, Real.norm_eq_abs]
    rw [show |(2 : ℝ)| = 2 by norm_num]
    change ‖z.down‖ < 3 / 4 at hz
    linarith

include hβ in
private theorem annulusAmbient_membership (z : PlaneLift.{u})
    (hz : z ∈ (annulusAmbient B β).source) :
    z ∈ planarSet 2 ↔ annulusAmbient B β z ∈ punctureSet B β := by
  have hzsmall := hz
  rw [annulusAmbient_source B β hβ] at hzsmall
  have hw : twicePlane z ∈ β.source := hz.1.2
  have hn : ‖(twicePlane z).down‖ = 2 * ‖z.down‖ := by
    change ‖(2 : ℝ) • z.down‖ = _
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
  have hnot : β (twicePlane z) ∈ punctureSet B β ↔ 1 ≤ ‖(twicePlane z).down‖ := by
    constructor
    · intro hx
      by_contra hlt
      exact hx ⟨twicePlane z, lt_of_not_ge hlt, rfl⟩
    · intro hx
      rintro ⟨w, hwsmall, he⟩
      have hwsrc : w ∈ β.source := by
        apply hβ
        change ‖w.down‖ ≤ 3
        change ‖w.down‖ < 1 at hwsmall
        linarith
      have heq := β.injOn hwsrc hw he
      rw [heq] at hwsmall
      exact (not_lt_of_ge hx) hwsmall
  rw [mem_planarSet_iff (Or.inl rfl), mem_planarModel_two]
  change ‖z.down‖ < 3 / 4 at hzsmall
  change (‖z.down‖ ≤ 3 ∧ 1 / 2 ≤ ‖z.down‖) ↔ β (twicePlane z) ∈ punctureSet B β
  rw [hnot, hn]
  constructor
  · intro h
    linarith [h.2]
  · intro h
    constructor <;> linarith

private def annulusPatch :
    OpenPartialHomeomorph (planarSet.{u} 2) (punctureSet B β) :=
  OpenPartialHomeomorph.restrictSubtypes (annulusAmbient B β).toOpenPartialHomeomorph
    (planarSet.{u} 2) (punctureSet B β)
    (planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (1, halfZero))
    (puncturePoint B β hβ) (annulusAmbient_membership B β hβ)

private theorem annulusPatch_apply (z : planarSet.{u} 2)
    (hz : z ∈ (annulusPatch B β hβ).source) :
    (annulusPatch B β hβ z).val = annulusAmbient B β z.val :=
  OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ hz

private theorem annulusPatch_symm_apply (x : punctureSet B β)
    (hx : x ∈ (annulusPatch B β hβ).target) :
    ((annulusPatch B β hβ).symm x).val = (annulusAmbient B β).symm x.val :=
  OpenPartialHomeomorph.restrictSubtypes_symm_apply _ _ _ _ _ _ _ hx

private theorem puncture_cover (x : punctureSet B β) :
    x ∈ (retainedPatch B β hβ).target ∨ x ∈ (annulusPatch B β hβ).target := by
  classical
  by_cases hx : x.val ∈ retainedSet B β
  · exact Or.inl hx
  · have hxclosed : x.val ∈ β '' {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} :=
      Classical.not_not.mp hx
    obtain ⟨z, hz, he⟩ := hxclosed
    have hzge : 1 ≤ ‖z.down‖ := by
      by_contra hlt
      exact x.property ⟨z, lt_of_not_ge hlt, he⟩
    have hz1 : ‖z.down‖ = 1 := le_antisymm hz hzge
    let w := twicePlane.{u}.symm z
    have hn : ‖w.down‖ = 1 / 2 := by
      have heq := congrArg (fun v : PlaneLift.{u} => ‖v.down‖)
        (twicePlane.{u}.apply_symm_apply z)
      change ‖(2 : ℝ) • w.down‖ = ‖z.down‖ at heq
      rw [norm_smul, Real.norm_eq_abs, hz1] at heq
      norm_num at heq
      change 2 * ‖w.down‖ = 1 at heq
      linarith
    have hw : w ∈ (annulusAmbient B β).source := by
      rw [annulusAmbient_source B β hβ]
      change ‖w.down‖ < 3 / 4
      rw [hn]
      norm_num
    have hpoint : annulusAmbient B β w = x.val := by
      change β (twicePlane w) = x.val
      rw [twicePlane.apply_symm_apply]
      exact he
    apply Or.inr
    change x.val ∈ (annulusAmbient B β).target
    exact hpoint ▸ (annulusAmbient B β).map_source hw

private abbrev puncturePatchCarrier : Bool → Type u
  | false => B.Carrier
  | true => planarSet.{u} 2

private abbrev puncturePatchSpace : Bool → Type
  | false => SurfaceModel.Space B.kind
  | true => EuclideanHalfSpace 2

@[instance_reducible]
private instance puncturePatchTopology (a : Bool) :
    TopologicalSpace (puncturePatchCarrier B a) := by
  cases a <;> dsimp [puncturePatchCarrier] <;> infer_instance

@[instance_reducible]
private instance puncturePatchSpaceTopology (a : Bool) :
    TopologicalSpace (puncturePatchSpace B a) := by
  cases a <;> dsimp [puncturePatchSpace] <;> infer_instance

@[instance_reducible]
private instance puncturePatchCharts (a : Bool) :
    ChartedSpace (puncturePatchSpace B a) (puncturePatchCarrier B a) := by
  cases a <;> dsimp [puncturePatchCarrier, puncturePatchSpace] <;> infer_instance

private abbrev puncturePatchModel (a : Bool) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) (puncturePatchSpace B a) := by
  cases a
  · exact SurfaceModel.model B.kind
  · exact 𝓡∂ 2

private instance puncturePatchSmooth (a : Bool) :
    IsManifold (puncturePatchModel B a) ∞ (puncturePatchCarrier B a) := by
  cases a <;> dsimp [puncturePatchModel, puncturePatchCarrier] <;> infer_instance

private def puncturePatch : (a : Bool) →
    OpenPartialHomeomorph (puncturePatchCarrier B a) (punctureSet B β)
  | false => retainedPatch B β hβ
  | true => annulusPatch B β hβ

private def punctureNative (a : Bool) : puncturePatchCarrier B a → B.Carrier := by
  cases a
  · exact id
  · exact fun z => annulusAmbient B β z.val

private theorem puncturePatch_apply (a : Bool) (p : puncturePatchCarrier B a)
    (hp : p ∈ (puncturePatch B β hβ a).source) :
    (puncturePatch B β hβ a p).val = punctureNative B β a p := by
  cases a
  · exact retainedPatch_apply B β hβ p hp
  · exact annulusPatch_apply B β hβ p hp

private theorem punctureNative_smooth (a : Bool) :
    ContMDiffOn (puncturePatchModel B a) (SurfaceModel.model B.kind) ∞
      (punctureNative B β a) (puncturePatch B β hβ a).source := by
  cases a
  · exact contMDiff_id.contMDiffOn
  · exact (annulusAmbient B β).contMDiffOn.comp
      (planarAtlas 2).contMDiff_subtype_val.contMDiffOn (fun z hz => hz)

private theorem puncturePatch_compatible (a b : Bool) :
    ContMDiffOn (puncturePatchModel B a) (puncturePatchModel B b) ∞
      ((puncturePatch B β hβ a).trans (puncturePatch B β hβ b).symm)
      ((puncturePatch B β hβ a).trans (puncturePatch B β hβ b).symm).source := by
  cases b
  · apply ((punctureNative_smooth B β hβ a).mono (fun z hz => hz.1)).congr
    intro z hz
    exact puncturePatch_apply B β hβ a z hz.1
  · apply ((planarAtlas 2).contMDiffOn_iff_subtype_val _ _).mpr
    let S := ((puncturePatch B β hβ a).trans (puncturePatch B β hβ true).symm).source
    have hN : ContMDiffOn (puncturePatchModel B a) (SurfaceModel.model B.kind) ∞
        (punctureNative B β a) S :=
      (punctureNative_smooth B β hβ a).mono (fun z hz => hz.1)
    have hm : MapsTo (punctureNative B β a) S (annulusAmbient B β).target := by
      intro z hz
      have ht := hz.2
      change (puncturePatch B β hβ a z).val ∈ (annulusAmbient B β).target at ht
      rwa [puncturePatch_apply B β hβ a z hz.1] at ht
    have h := (annulusAmbient B β).symm.contMDiffOn.comp hN hm
    apply h.congr
    intro z hz
    change ((annulusPatch B β hβ).symm (puncturePatch B β hβ a z)).val = _
    exact (annulusPatch_symm_apply B β hβ (puncturePatch B β hβ a z) hz.2).trans
      (congrArg (annulusAmbient B β).symm (puncturePatch_apply B β hβ a z hz.1))

private def puncturePlaneSplit :
    EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin 1)) :=
  EuclideanSpace.finAddEquivProd.trans
    ((PiLp.equivOfUnique 2 ℝ (fun _a : Fin 1 => ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 1))))

private def puncturePlaneSplitDiffeomorph :
    (EuclideanSpace ℝ (Fin 2)) ≃ₘ⟮𝓡 2, 𝓘(ℝ).prod (𝓡 1)⟯
      (ℝ × EuclideanSpace ℝ (Fin 1)) where
  toEquiv := puncturePlaneSplit.toEquiv
  contMDiff_toFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact puncturePlaneSplit.contDiff.contMDiff
  contMDiff_invFun := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact puncturePlaneSplit.symm.contDiff.contMDiff

private def punctureHalfLine (a : ℝ) :
    PartialDiffeomorph 𝓘(ℝ) (𝓡∂ 1) ℝ (EuclideanHalfSpace 1) ∞ where
  __ := DifferentialGeometry.Topology.Manifold.halfSpaceInteriorChart a
  contMDiffOn_toFun :=
    DifferentialGeometry.Topology.Manifold.halfSpaceInteriorChart_contMDiffOn a
  contMDiffOn_invFun :=
    (DifferentialGeometry.Topology.Manifold.halfSpaceInteriorChart_symm_contMDiff a).contMDiffOn

private def punctureHalfProduct :
    (EuclideanHalfSpace 1 × EuclideanSpace ℝ (Fin 1)) ≃ₘ⟮(𝓡∂ 1).prod (𝓡 1), 𝓡∂ 2⟯
      EuclideanHalfSpace 2 := by
  let d := DifferentialGeometry.Manifold.modelLinearHomeomorphDiffeomorph
    ((𝓡∂ 1).prod (𝓡 1)) (𝓡∂ 2)
    (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftHomeomorph 0 1)
    (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftCoordinates 0 1)
    (DifferentialGeometry.Manifold.euclideanHalfSpaceProdLeftHomeomorph_model 0 1)
  refine { d.toEquiv with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · rw [chartedSpaceSelf_prod]
    exact d.contMDiff
  · rw [chartedSpaceSelf_prod]
    exact d.symm.contMDiff

private def punctureHalfInterior (a : ℝ) :
    PartialDiffeomorph (𝓡 2) (𝓡∂ 2) (EuclideanSpace ℝ (Fin 2)) (EuclideanHalfSpace 2) ∞ :=
  (puncturePlaneSplitDiffeomorph.toPartialDiffeomorph.trans
    (DifferentialGeometry.Topology.PartialDiffeomorph.prod (punctureHalfLine a)
      (Diffeomorph.refl (𝓡 1) (EuclideanSpace ℝ (Fin 1)) ∞).toPartialDiffeomorph)).trans
        punctureHalfProduct.toPartialDiffeomorph

private theorem punctureHalfInterior_mem (x : EuclideanSpace ℝ (Fin 2)) :
    x ∈ (punctureHalfInterior ((puncturePlaneSplit x).1 - 1)).source := by
  change ((x ∈ univ ∧ (puncturePlaneSplit x).1 ∈ Ioi ((puncturePlaneSplit x).1 - 1) ∧
    (puncturePlaneSplit x).2 ∈ univ) ∧ True)
  refine ⟨⟨mem_univ x, ?_, mem_univ _⟩, trivial⟩
  change (puncturePlaneSplit x).1 - 1 < (puncturePlaneSplit x).1
  linarith

private def punctureHalfChart {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] [IsManifold (𝓡∂ 2) ∞ M] (x : M) :
    PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) M (EuclideanHalfSpace 2) ∞ where
  __ := chartAt (EuclideanHalfSpace 2) x
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

private theorem punctureModelCoordinates (k : SurfaceModel) {M : Type u}
    [TopologicalSpace M] [ChartedSpace (SurfaceModel.Space k) M]
    [IsManifold (SurfaceModel.model k) ∞ M] (x : M) :
    ∃ d : PartialDiffeomorph (SurfaceModel.model k) (𝓡∂ 2) M (EuclideanHalfSpace 2) ∞,
      x ∈ d.source := by
  cases k with
  | closed =>
    let c := PartialDiffeomorph.extendedChart (I := 𝓡 2) x
    exact ⟨c.trans (punctureHalfInterior ((puncturePlaneSplit (c x)).1 - 1)),
      mem_extChartAt_source x, punctureHalfInterior_mem (c x)⟩
  | withBoundary =>
    exact ⟨punctureHalfChart x, mem_chart_source (EuclideanHalfSpace 2) x⟩

private theorem exists_punctureAtlas :
    ∃ A : ChartedSpace (EuclideanHalfSpace 2) (punctureSet B β), letI := A
      IsManifold (𝓡∂ 2) ∞ (punctureSet B β) ∧ ∀ a : Bool,
        ContMDiffOn (puncturePatchModel B a) (𝓡∂ 2) ∞
          (puncturePatch B β hβ a) (puncturePatch B β hβ a).source ∧
        ContMDiffOn (𝓡∂ 2) (puncturePatchModel B a) ∞
          (puncturePatch B β hβ a).symm (puncturePatch B β hβ a).target := by
  apply exists_carrierSurgeryAtlas_of_openCover (𝓡∂ 2) (puncturePatch B β hβ)
  · intro x
    rcases puncture_cover B β hβ x with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  · exact puncturePatch_compatible B β hβ
  · intro a x hx
    cases a
    · exact punctureModelCoordinates B.kind x
    · exact ⟨punctureHalfChart x, mem_chart_source (EuclideanHalfSpace 2) x⟩

@[instance_reducible]
private def punctureCharts : ChartedSpace (EuclideanHalfSpace 2) (punctureSet B β) :=
  Classical.choose (exists_punctureAtlas B β hβ)

private theorem punctureSmooth :
    letI := punctureCharts B β hβ
    IsManifold (𝓡∂ 2) ∞ (punctureSet B β) :=
  (Classical.choose_spec (exists_punctureAtlas B β hβ)).1

private def puncturePD (a : Bool) :
    letI := punctureCharts B β hβ
    PartialDiffeomorph (puncturePatchModel B a) (𝓡∂ 2)
      (puncturePatchCarrier B a) (punctureSet B β) ∞ := by
  letI := punctureCharts B β hβ
  exact { puncturePatch B β hβ a with
    contMDiffOn_toFun := (Classical.choose_spec (exists_punctureAtlas B β hβ)).2 a |>.1
    contMDiffOn_invFun := (Classical.choose_spec (exists_punctureAtlas B β hβ)).2 a |>.2 }

private theorem punctureVal_smooth :
    letI := punctureCharts B β hβ
    ContMDiff (𝓡∂ 2) (SurfaceModel.model B.kind) ∞
      (Subtype.val : punctureSet B β → B.Carrier) := by
  let := punctureCharts B β hβ
  have := punctureSmooth B β hβ
  intro x
  obtain ⟨a, hx⟩ : ∃ a, x ∈ (puncturePatch B β hβ a).target := by
    rcases puncture_cover B β hβ x with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  have hs := (punctureNative_smooth B β hβ a).comp (puncturePD B β hβ a).symm.contMDiffOn
    (fun y hy => (puncturePatch B β hβ a).map_target hy)
  apply (hs.contMDiffAt ((puncturePatch B β hβ a).open_target.mem_nhds hx)).congr_of_eventuallyEq
  filter_upwards [(puncturePatch B β hβ a).open_target.mem_nhds hx] with y hy
  change y.val = punctureNative B β a ((puncturePatch B β hβ a).symm y)
  have he := puncturePatch_apply B β hβ a _ ((puncturePatch B β hβ a).map_target hy)
  rw [(puncturePatch B β hβ a).right_inv hy] at he
  exact he

private theorem punctureNative_mfderiv (a : Bool) (p : puncturePatchCarrier B a)
    (hp : p ∈ (puncturePatch B β hβ a).source) :
    Bijective (mfderiv (puncturePatchModel B a) (SurfaceModel.model B.kind)
      (punctureNative B β a) p) := by
  cases a
  · change Bijective (mfderiv (SurfaceModel.model B.kind) (SurfaceModel.model B.kind) id p)
    rw [mfderiv_id]
    exact bijective_id
  · have hd := (annulusAmbient B β).isLocalDiffeomorphAt 𝓘(ℝ, ℂ)
      (SurfaceModel.model B.kind) ∞ hp
    have hb := (planarAtlas 2).mfderiv_subtypeVal_bijective p
    have hcomp := mfderiv_comp p
      (((annulusAmbient B β).contMDiffOn.contMDiffAt
        ((annulusAmbient B β).open_source.mem_nhds hp)).mdifferentiableAt (by simp))
      (((planarAtlas 2).contMDiff_subtype_val p).mdifferentiableAt (by simp))
    change Bijective (mfderiv (𝓡∂ 2) (SurfaceModel.model B.kind)
      ((annulusAmbient B β) ∘ Subtype.val) p)
    rw [hcomp]
    have he : Bijective (mfderiv 𝓘(ℝ, ℂ) (SurfaceModel.model B.kind)
        (annulusAmbient B β) p.val) := by
      rw [← hd.mfderivToContinuousLinearEquiv_coe (by simp)]
      exact (hd.mfderivToContinuousLinearEquiv (by simp)).bijective
    exact he.comp hb

private theorem punctureVal_mfderiv (x : punctureSet B β) :
    letI := punctureCharts B β hβ
    Bijective (mfderiv (𝓡∂ 2) (SurfaceModel.model B.kind)
      (Subtype.val : punctureSet B β → B.Carrier) x) := by
  let := punctureCharts B β hβ
  have := punctureSmooth B β hβ
  obtain ⟨a, hx⟩ : ∃ a, x ∈ (puncturePatch B β hβ a).target := by
    rcases puncture_cover B β hβ x with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  let d := puncturePD B β hβ a
  let p := d.symm x
  have hp : p ∈ d.source := d.map_target hx
  have heq : (Subtype.val ∘ d) =ᶠ[𝓝 p] punctureNative B β a := by
    filter_upwards [d.open_source.mem_nhds hp] with y hy
    exact puncturePatch_apply B β hβ a y hy
  have hn : Bijective (mfderiv (puncturePatchModel B a) (SurfaceModel.model B.kind)
      (Subtype.val ∘ d) p) := by
    rw [heq.mfderiv_eq]
    exact punctureNative_mfderiv B β hβ a p hp
  have hl := d.isLocalDiffeomorphAt (puncturePatchModel B a) (𝓡∂ 2) ∞ hp
  have hd : Bijective (mfderiv (puncturePatchModel B a) (𝓡∂ 2) d p) := by
    rw [← hl.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (hl.mfderivToContinuousLinearEquiv (by simp)).bijective
  rw [mfderiv_comp p (((punctureVal_smooth B β hβ) (d p)).mdifferentiableAt (by simp))
    ((d.contMDiffOn.contMDiffAt (d.open_source.mem_nhds hp)).mdifferentiableAt (by simp))] at hn
  have h : Bijective (mfderiv (𝓡∂ 2) (SurfaceModel.model B.kind)
      (Subtype.val : punctureSet B β → B.Carrier) (d p)) :=
    (Bijective.of_comp_iff _ hd).mp hn
  have he : d p = x := d.right_inv hx
  exact he ▸ h

include hβ in
private theorem puncture_compact : IsCompact (punctureSet B β) := by
  have hs : {z : PlaneLift.{u} | ‖z.down‖ < 1} ⊆ β.source := by
    intro z hz
    apply hβ
    change ‖z.down‖ ≤ 3
    change ‖z.down‖ < 1 at hz
    linarith
  have ho : IsOpen (β '' {z : PlaneLift.{u} | ‖z.down‖ < 1}) :=
    β.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_lt (continuous_norm.comp contMDiff_planeLift_down.continuous) continuous_const) hs
  exact ho.isClosed_compl.isCompact

private abbrev puncturedSurface : CompactSurface.{u} := by
  have : CompactSpace (punctureSet B β) :=
    isCompact_iff_compactSpace.mp (puncture_compact B β hβ)
  have : ConnectedSpace (punctureSet B β) :=
    isConnected_iff_connectedSpace.mp (puncture_connected B β hβ)
  letI := punctureCharts B β hβ
  have := punctureSmooth B β hβ
  exact { kind := .withBoundary, Carrier := punctureSet B β }

private theorem baseChart_interior (x : B.Carrier) (hx : x ∈ β.target) :
    (SurfaceModel.model B.kind).IsInteriorPoint x := by
  have h := β.isLocalDiffeomorphAt 𝓘(ℝ, ℂ) (SurfaceModel.model B.kind) ∞ (β.map_target hx)
  have hi := (h.isInteriorPoint_iff (by simp : (∞ : ℕ∞ω) ≠ 0)).mp
    BoundarylessManifold.isInteriorPoint
  rwa [β.right_inv hx] at hi

include hβ in
private theorem oldBoundary_retained (x : B.Carrier)
    (hx : (SurfaceModel.model B.kind).IsBoundaryPoint x) : x ∈ retainedSet B β := by
  rintro ⟨z, hz, he⟩
  have hzsrc : z ∈ β.source := by
    apply hβ
    change ‖z.down‖ ≤ 3
    change ‖z.down‖ ≤ 1 at hz
    linarith
  have hi := baseChart_interior B β x (he ▸ β.map_source hzsrc)
  exact ((SurfaceModel.model B.kind).isInteriorPoint_iff_not_isBoundaryPoint x).mp hi hx

private theorem annulus_boundary (z : planarSet.{u} 2)
    (hz : z ∈ (annulusPatch B β hβ).source) :
    (𝓡∂ 2).IsBoundaryPoint z ↔ ‖z.val.down‖ = 1 / 2 := by
  have hn : ‖z.val.down‖ < 3 / 4 := by
    have h := hz
    change z.val ∈ (annulusAmbient B β).source at h
    rwa [annulusAmbient_source B β hβ] at h
  rw [planarSet_isBoundaryPoint_iff]
  simp only [planarFunction, ↓reduceIte, sqDist, sub_zero, mul_eq_zero]
  constructor
  · rintro (he | he)
    · nlinarith [norm_nonneg z.val.down]
    · nlinarith [norm_nonneg z.val.down]
  · intro he
    right
    rw [he]
    norm_num

private theorem puncture_boundary_iff (x : punctureSet B β) :
    letI := punctureCharts B β hβ
    (𝓡∂ 2).IsBoundaryPoint x ↔
      (SurfaceModel.model B.kind).IsBoundaryPoint x.val ∨
        x.val ∈ β '' {z : PlaneLift.{u} | ‖z.down‖ = 1} := by
  let := punctureCharts B β hβ
  have := punctureSmooth B β hβ
  rcases puncture_cover B β hβ x with hx | hx
  · let d := puncturePD B β hβ false
    have hp : x.val ∈ d.source := hx
    have he : d x.val = x := Subtype.ext (retainedPatch_apply B β hβ x.val hx)
    have hl := d.isLocalDiffeomorphAt (SurfaceModel.model B.kind) (𝓡∂ 2) ∞ hp
    have hb := hl.isBoundaryPoint_iff (by simp)
    rw [he] at hb
    have hnot : x.val ∉ β '' {z : PlaneLift.{u} | ‖z.down‖ = 1} := by
      rintro ⟨z, hz, heq⟩
      exact hx ⟨z, le_of_eq hz, heq⟩
    exact hb.symm.trans (or_iff_left hnot).symm
  · let d := puncturePD B β hβ true
    let z := d.symm x
    have hz : z ∈ d.source := d.map_target hx
    have he := annulusPatch_apply B β hβ z hz
    have hzval : x.val = β (twicePlane z.val) := by
      exact (congrArg Subtype.val (d.right_inv hx)).symm.trans he
    have hzsrc : twicePlane z.val ∈ β.source := hz.1.2
    have hnot : ¬ (SurfaceModel.model B.kind).IsBoundaryPoint x.val := by
      exact ((SurfaceModel.model B.kind).isInteriorPoint_iff_not_isBoundaryPoint x.val).mp
        (baseChart_interior B β x.val (hzval.symm ▸ β.map_source hzsrc))
    have hi : x.val ∈ β '' {w : PlaneLift.{u} | ‖w.down‖ = 1} ↔
        ‖z.val.down‖ = 1 / 2 := by
      have hn : ‖(twicePlane z.val).down‖ = 2 * ‖z.val.down‖ := by
        change ‖(2 : ℝ) • z.val.down‖ = _
        rw [norm_smul, Real.norm_eq_abs]
        norm_num
      constructor
      · rintro ⟨w, hw, hwx⟩
        have hwsrc : w ∈ β.source := by
          apply hβ
          change ‖w.down‖ ≤ 3
          change ‖w.down‖ = 1 at hw
          rw [hw]
          norm_num
        have heq := β.injOn hwsrc hzsrc (hwx.trans hzval)
        change ‖w.down‖ = 1 at hw
        rw [heq, hn] at hw
        linarith
      · intro hnorm
        refine ⟨twicePlane z.val, ?_, hzval.symm⟩
        change ‖(twicePlane z.val).down‖ = 1
        rw [hn, hnorm]
        norm_num
    have hl := d.symm.isLocalDiffeomorphAt (𝓡∂ 2) (𝓡∂ 2) ∞ hx
    have hb := hl.isBoundaryPoint_iff (by simp)
    exact hb.trans ((annulus_boundary B β hβ z hz).trans
      (hi.symm.trans (or_iff_right hnot).symm))

private def punctureCircleInv : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle where
  toEquiv := Equiv.inv Circle
  contMDiff_toFun := contMDiff_inv (𝓡 1) ∞
  contMDiff_invFun := contMDiff_inv (𝓡 1) ∞

private def punctureCircleCollarInv :
    (Circle × EuclideanHalfSpace 1) ≃ₘ⟮circleCollarModel, circleCollarModel⟯
      (Circle × EuclideanHalfSpace 1) :=
  punctureCircleInv.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)

private def puncturedCollar :
    letI := punctureCharts B β hβ
    PartialDiffeomorph circleCollarModel (𝓡∂ 2)
      (Circle × EuclideanHalfSpace 1) (punctureSet B β) ∞ := by
  letI := punctureCharts B β hβ
  exact (punctureCircleCollarInv.toPartialDiffeomorph.trans
    (planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2))).trans (puncturePD B β hβ true)

private theorem puncturePlanarCollar_val (p : Circle × EuclideanHalfSpace 1)
    (hp : p ∈ circleCollarSource) :
    (planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2)).val.down =
      (1 / 2 + p.2.val 0 / 4 : ℝ) • (p.1 : ℂ) := by
  have hi : (p.1⁻¹, p.2) ∈ circleCollarSource := hp
  rw [planarCollar_apply_val (Or.inl rfl) (1 : Fin 2) hi]
  change (0 : ℂ) + (1 / 2 + (1 : ℝ) * p.2.val 0 / 4) • conj (↑p.1⁻¹ : ℂ) = _
  rw [Circle.coe_inv_eq_conj, Complex.conj_conj]
  simp only [zero_add, one_mul]

private theorem puncturedCollar_source :
    letI := punctureCharts B β hβ
    (puncturedCollar B β hβ).source = circleCollarSource := by
  let := punctureCharts B β hβ
  ext p
  change ((p ∈ univ ∧ (p.1⁻¹, p.2) ∈ circleCollarSource) ∧
    planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2) ∈
      (annulusPatch B β hβ).source) ↔ p ∈ circleCollarSource
  constructor
  · exact fun h => h.1.2
  · intro hp
    refine ⟨⟨mem_univ p, hp⟩, ?_⟩
    change (planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2)).val ∈
      (annulusAmbient B β).source
    rw [annulusAmbient_source B β hβ]
    change ‖(planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2)).val.down‖ < 3 / 4
    rw [puncturePlanarCollar_val p hp, norm_smul, Real.norm_eq_abs, Circle.norm_coe]
    have hn := p.2.property
    change p.2.val 0 < 1 at hp
    rw [abs_of_nonneg (by linarith : 0 ≤ (1 / 2 + p.2.val 0 / 4 : ℝ))]
    linarith

private theorem puncturedCollar_val (p : Circle × EuclideanHalfSpace 1)
    (hp : p ∈ circleCollarSource) :
    letI := punctureCharts B β hβ
    (puncturedCollar B β hβ p).val =
      β (ULift.up ((1 + p.2.val 0 / 2 : ℝ) • (p.1 : ℂ))) := by
  let := punctureCharts B β hβ
  have hs : p ∈ (puncturedCollar B β hβ).source := puncturedCollar_source B β hβ ▸ hp
  have hz := hs.2
  change (annulusPatch B β hβ
    (planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2))).val = _
  have hv := annulusPatch_apply B β hβ
    (planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2)) hz
  refine hv.trans ?_
  change β (twicePlane (planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2)).val) = _
  congr 1
  apply ULift.ext
  change (2 : ℝ) • (planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1⁻¹, p.2)).val.down = _
  rw [puncturePlanarCollar_val p hp, smul_smul]
  congr 1
  ring

include hβ in
theorem exists_puncture_of_interiorChart :
    ∃ B' : CompactSurface.{u}, ∃ b : C(B'.Carrier, B.Carrier),
    ∃ γ : PartialDiffeomorph circleCollarModel (SurfaceModel.model B'.kind)
      (Circle × EuclideanHalfSpace 1) B'.Carrier ∞,
      B'.kind = .withBoundary ∧
      ContMDiff (SurfaceModel.model B'.kind) (SurfaceModel.model B.kind) ∞ b ∧
      Injective b ∧
      (∀ x, Bijective
        (mfderiv (SurfaceModel.model B'.kind) (SurfaceModel.model B.kind) b x)) ∧
      range b = (β '' {z : PlaneLift.{u} | ‖z.down‖ < 1})ᶜ ∧
      γ.source = circleCollarSource ∧
      (∀ p ∈ circleCollarSource,
        b (γ p) = β (ULift.up ((1 + p.2.val 0 / 2 : ℝ) • (p.1 : ℂ)))) ∧
      b '' (SurfaceModel.model B'.kind).boundary B'.Carrier =
        (SurfaceModel.model B.kind).boundary B.Carrier ∪
          β '' {z : PlaneLift.{u} | ‖z.down‖ = 1} ∧
      Disjoint ((SurfaceModel.model B.kind).boundary B.Carrier)
        (β '' {z : PlaneLift.{u} | ‖z.down‖ = 1}) := by
  let := punctureCharts B β hβ
  have := punctureSmooth B β hβ
  let B' := puncturedSurface B β hβ
  let b : C(B'.Carrier, B.Carrier) := ⟨Subtype.val, continuous_subtype_val⟩
  let γ := puncturedCollar B β hβ
  refine ⟨B', b, γ, rfl, punctureVal_smooth B β hβ, Subtype.val_injective,
    punctureVal_mfderiv B β hβ, ?_, puncturedCollar_source B β hβ, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  · exact puncturedCollar_val B β hβ
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (puncture_boundary_iff B β hβ y).mp hy
    · intro hx
      have hxK : x ∈ punctureSet B β := by
        rcases hx with hx | hx
        · exact retained_subset B β (oldBoundary_retained B β hβ x hx)
        · obtain ⟨z, hz, he⟩ := hx
          rintro ⟨w, hw, hew⟩
          have hzsrc : z ∈ β.source := by
            apply hβ
            change ‖z.down‖ ≤ 3
            change ‖z.down‖ = 1 at hz
            rw [hz]
            norm_num
          have hwsrc : w ∈ β.source := by
            apply hβ
            change ‖w.down‖ ≤ 3
            change ‖w.down‖ < 1 at hw
            linarith
          have heq := β.injOn hwsrc hzsrc (hew.trans he.symm)
          rw [heq] at hw
          exact (ne_of_lt hw) hz
      exact ⟨⟨x, hxK⟩, (puncture_boundary_iff B β hβ ⟨x, hxK⟩).mpr hx, rfl⟩
  · apply Set.disjoint_left.mpr
    intro x hx hxnew
    obtain ⟨z, hz, he⟩ := hxnew
    have hzsrc : z ∈ β.source := by
      apply hβ
      change ‖z.down‖ ≤ 3
      change ‖z.down‖ = 1 at hz
      rw [hz]
      norm_num
    have hi := baseChart_interior B β x (he ▸ β.map_source hzsrc)
    exact ((SurfaceModel.model B.kind).isInteriorPoint_iff_not_isBoundaryPoint x).mp hi hx

private abbrev PunctureE2 := EuclideanSpace ℝ (Fin 2)

private def punctureEmbeddingInterior :
    PartialDiffeomorph (𝓡 2) (𝓡∂ 2) PunctureE2 (EuclideanHalfSpace 2) ∞ where
  toFun := (𝓡∂ 2).symm
  invFun := Subtype.val
  source := {v | 0 < v 0}
  target := {v | 0 < v.val 0}
  map_source' := by
    intro v hv
    change 0 < v 0 at hv
    have hr : v ∈ range (𝓡∂ 2) := by
      rw [range_modelWithCornersEuclideanHalfSpace]
      exact hv.le
    change 0 < ((𝓡∂ 2).symm v).val 0
    rw [show ((𝓡∂ 2).symm v).val = v from (𝓡∂ 2).right_inv hr]
    exact hv
  map_target' := fun v hv => hv
  left_inv' := by
    intro v hv
    change 0 < v 0 at hv
    apply (𝓡∂ 2).right_inv
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact hv.le
  right_inv' := fun v hv => (𝓡∂ 2).left_inv v
  open_source := isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous
  open_target := isOpen_lt continuous_const
    ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val)
  contMDiffOn_toFun := (𝓡∂ 2).contMDiffOn_symm.mono fun v hv => by
    change 0 < v 0 at hv
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact hv.le
  contMDiffOn_invFun := (𝓡∂ 2).contMDiff.contMDiffOn

private theorem punctureEmbeddingInterior_val (v : PunctureE2) (hv : 0 < v 0) :
    (punctureEmbeddingInterior v).val = v := by
  apply (𝓡∂ 2).right_inv
  rw [range_modelWithCornersEuclideanHalfSpace]
  exact hv.le

private def punctureEmbeddingTranslation (v : PunctureE2) :
    PunctureE2 ≃ₘ⟮𝓡 2, 𝓡 2⟯ PunctureE2 where
  toFun z := z + v
  invFun z := z - v
  left_inv z := by simp
  right_inv z := by simp
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

private def punctureEmbeddingSwap : PunctureE2 ≃L[ℝ] PunctureE2 :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)).toContinuousLinearEquiv

private theorem punctureEmbeddingSwap_zero (v : PunctureE2) :
    punctureEmbeddingSwap v 0 = v 1 := by
  simp [punctureEmbeddingSwap, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

private def punctureEmbeddingShift (v : PunctureE2) (hv : v 0 = 0) :
    EuclideanHalfSpace 2 → EuclideanHalfSpace 2 :=
  fun x => ⟨x.val + v, by simpa [hv] using x.property⟩

private theorem punctureEmbeddingShift_smooth (v : PunctureE2) (hv : v 0 = 0) :
    ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ (punctureEmbeddingShift v hv) := by
  apply (ContMDiff.iff_comp_isImmersion ((𝓡∂ 2).isImmersion_coe ∞)).mpr
  refine ⟨(continuous_subtype_val.add continuous_const).subtype_mk _, ?_⟩
  exact (𝓡∂ 2).contMDiff.add contMDiff_const

private def punctureEmbeddingShiftDiffeomorph (v : PunctureE2) (hv : v 0 = 0) :
    EuclideanHalfSpace 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ EuclideanHalfSpace 2 where
  toFun := punctureEmbeddingShift v hv
  invFun := punctureEmbeddingShift (-v) (by change -(v 0) = 0; rw [hv, neg_zero])
  left_inv x := by apply Subtype.ext; exact add_neg_cancel_right x.val v
  right_inv x := by apply Subtype.ext; simp [punctureEmbeddingShift, add_assoc]
  contMDiff_toFun := punctureEmbeddingShift_smooth v hv
  contMDiff_invFun := punctureEmbeddingShift_smooth (-v)
    (by change -(v 0) = 0; rw [hv, neg_zero])

private theorem punctureLiftImmersion
    {M N P : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (𝓡∂ 2) ∞ M] [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace 2) N] [IsManifold (𝓡∂ 2) ∞ N]
    {H : Type} [TopologicalSpace H] (J : ModelWithCorners ℝ PunctureE2 H)
    [TopologicalSpace P] [ChartedSpace H P]
    (d : PartialDiffeomorph (𝓡∂ 2) (𝓡∂ 2) M N ∞)
    (g : N → P) (f : M → P) (p : M) (hp : p ∈ d.source)
    (h : IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 2) J ∞ f p)
    (he : ∀ y ∈ d.source, g (d y) = f y) :
    IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 2) J ∞ g (d p) := by
  let α := d.symm.toOpenPartialHomeomorph.trans h.domChart
  have hαmax : α ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ N := by
    apply α.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
        (d.symm.contMDiffOn.mono (fun y hy => hy.1)) (fun y hy => hy.2)
    · exact d.contMDiffOn.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mono
          (fun y hy => hy.1)) (fun y hy => hy.2)
  have hx : d p ∈ α.source := by
    change d p ∈ d.target ∧ d.symm (d p) ∈ h.domChart.source
    have hleft : d.symm.toPartialEquiv (d.toPartialEquiv p) = p :=
      d.toPartialEquiv.left_inv hp
    rw [hleft]
    exact ⟨d.map_source hp, h.mem_domChart_source⟩
  have hm (y : N) (hy : y ∈ α.source) : g y ∈ h.codChart.source := by
    rw [← d.right_inv hy.1, he _ (d.map_target hy.1)]
    exact h.source_subset_preimage_source hy.2
  refine IsImmersionAtOfComplement.mk_of_charts h.equiv α h.codChart hx
    (by rw [he p hp]; exact h.mem_codChart_source) hαmax h.codChart_mem_maximalAtlas hm ?_
  intro w hw
  have hr : w ∈ (h.domChart.extend (𝓡∂ 2)).target := by
    exact ⟨hw.1, hw.2.1⟩
  change J (h.codChart (g (d ((h.domChart.extend (𝓡∂ 2)).symm w)))) = _
  have hz : (h.domChart.extend (𝓡∂ 2)).symm w ∈ d.source := hw.2.2
  rw [he _ hz]
  exact h.writtenInCharts hr

private theorem punctureAnnulusImmersion_half
    {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 2) N]
    [IsManifold (𝓡∂ 2) ∞ N]
    (D : PartialDiffeomorph 𝓘(ℝ, ℂ) (𝓡∂ 2) PlaneLift.{u} N ∞)
    (x : planarSet.{u} 2) (hx : x.val ∈ D.source) :
    IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 2) (𝓡∂ 2) ∞
      (D ∘ (Subtype.val : planarSet.{u} 2 → PlaneLift.{u})) x := by
  let A := planarAtlas.{u} 2
  let a := A.ambientChart x
  let v : PunctureE2 := WithLp.toLp 2 (fun i => if i = 1 then 1 - a x.val 1 else 0)
  have hv : v 0 = 0 := by simp [v]
  let d := punctureEmbeddingShiftDiffeomorph v hv
  let α₀ := (A.chart x).trans d.toHomeomorph.toOpenPartialHomeomorph
  let s : Set (planarSet.{u} 2) :=
    (α₀.source ∩ Subtype.val ⁻¹' D.source) ∩
      α₀ ⁻¹' {y : EuclideanHalfSpace 2 | 0 < y.val 1}
  have hs0 : IsOpen (α₀.source ∩
      α₀ ⁻¹' {y : EuclideanHalfSpace 2 | 0 < y.val 1}) :=
    α₀.isOpen_inter_preimage (isOpen_lt continuous_const
      ((EuclideanSpace.proj 1).continuous.comp continuous_subtype_val))
  have hs : IsOpen s := by
    simpa only [s, inter_right_comm] using
      hs0.inter (D.open_source.preimage continuous_subtype_val)
  let α := α₀.restr s
  let c := (((D.symm.trans a).trans
    (punctureEmbeddingTranslation v).toPartialDiffeomorph).trans
    punctureEmbeddingSwap.toDiffeomorph.toPartialDiffeomorph).trans punctureEmbeddingInterior
  have hαsource : α.source = s := by
    rw [OpenPartialHomeomorph.restr_source' α₀ s hs, inter_eq_right]
    exact (inter_subset_left.trans inter_subset_left)
  have hxs : x ∈ s := by
    refine ⟨⟨⟨A.mem_source x, mem_univ _⟩, hx⟩, ?_⟩
    change 0 < (A.chart x x).val 1 + v 1
    rw [show (A.chart x x).val = a x.val from
      OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ (A.mem_source x)]
    change 0 < a x.val 1 + (1 - a x.val 1)
    linarith
  have hαmax : α ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ (planarSet.{u} 2) := by
    apply restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡∂ 2)) ?_ hs
    apply α₀.mem_maximalAtlas_of_contMDiffOn
    · exact d.contMDiff.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x)).mono
          (fun y hy => hy.1))
    · exact (contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas x)).comp d.symm.contMDiff.contMDiffOn
          (fun y hy => hy.2)
  have hcmax : c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas (𝓡∂ 2) ∞ N :=
    c.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      c.contMDiffOn_toFun c.contMDiffOn_invFun
  have ha (y : planarSet.{u} 2) (hy : y ∈ s) : (α₀ y).val = a y.val + v := by
    exact congrArg (fun w : PunctureE2 => w + v)
      (OpenPartialHomeomorph.restrictSubtypes_apply a.toOpenPartialHomeomorph
        (planarSet 2) {w : PunctureE2 | 0 ≤ w 0} x (0 : EuclideanHalfSpace 2)
        (A.mem_iff x) y hy.1.1.1)
  have hc (y : planarSet.{u} 2) (hy : y ∈ s) : D y.val ∈ c.source := by
    change (((D y.val ∈ D.target ∧ D.symm (D y.val) ∈ a.source) ∧ True) ∧ True) ∧ _
    have hleft : D.symm.toPartialEquiv (D.toPartialEquiv y.val) = y.val :=
      D.toPartialEquiv.left_inv hy.1.2
    rw [hleft]
    refine ⟨⟨⟨⟨D.map_source hy.1.2, hy.1.1.1⟩, trivial⟩, trivial⟩, ?_⟩
    change 0 < punctureEmbeddingSwap (a (D.symm (D y.val)) + v) 0
    rw [hleft, punctureEmbeddingSwap_zero, ← ha y hy]
    exact hy.2
  have hf (y : planarSet.{u} 2) (hy : y ∈ s) :
      c.toOpenPartialHomeomorph.extend (𝓡∂ 2) (D y.val) =
        punctureEmbeddingSwap ((α.extend (𝓡∂ 2)) y) := by
    change (punctureEmbeddingInterior
      (punctureEmbeddingSwap (a (D.symm (D y.val)) + v))).val =
        punctureEmbeddingSwap ((α₀ y).val)
    have hleft : D.symm.toPartialEquiv (D.toPartialEquiv y.val) = y.val :=
      D.toPartialEquiv.left_inv hy.1.2
    rw [hleft]
    change (punctureEmbeddingInterior (punctureEmbeddingSwap (a y.val + v))).val = _
    rw [punctureEmbeddingInterior_val, ha y hy]
    rw [punctureEmbeddingSwap_zero, ← ha y hy]
    exact hy.2
  refine IsImmersionAtOfComplement.mk_of_charts
    ((ContinuousLinearEquiv.prodUnique ℝ PunctureE2 PUnit.{1}).trans punctureEmbeddingSwap)
    α c.toOpenPartialHomeomorph (hαsource.symm ▸ hxs) (hc x hxs)
    hαmax hcmax (fun y hy => hc y (hαsource ▸ hy)) ?_
  intro w hw
  let y := (α.extend (𝓡∂ 2)).symm w
  have hy : y ∈ s := by
    have h := (α.extend (𝓡∂ 2)).map_target hw
    rwa [OpenPartialHomeomorph.extend_source, hαsource] at h
  change c.toOpenPartialHomeomorph.extend (𝓡∂ 2) (D y.val) = punctureEmbeddingSwap w
  rw [hf y hy]
  exact congrArg punctureEmbeddingSwap ((α.extend (𝓡∂ 2)).right_inv hw)

private theorem punctureAnnulusImmersion_closed
    {N : Type u} [TopologicalSpace N] [ChartedSpace PunctureE2 N]
    [IsManifold (𝓡 2) ∞ N]
    (D : PartialDiffeomorph 𝓘(ℝ, ℂ) (𝓡 2) PlaneLift.{u} N ∞)
    (x : planarSet.{u} 2) (hx : x.val ∈ D.source) :
    IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 2) (𝓡 2) ∞
      (D ∘ (Subtype.val : planarSet.{u} 2 → PlaneLift.{u})) x := by
  let A := planarAtlas.{u} 2
  let a := A.ambientChart x
  let α := (A.chart x).restr (Subtype.val ⁻¹' D.source)
  let c := D.symm.trans a
  have hs : IsOpen (Subtype.val ⁻¹' D.source : Set (planarSet.{u} 2)) :=
    D.open_source.preimage continuous_subtype_val
  have hαsource : α.source = (A.chart x).source ∩ Subtype.val ⁻¹' D.source :=
    OpenPartialHomeomorph.restr_source' _ _ hs
  have hc (y : planarSet.{u} 2) (hy : y ∈ α.source) : D y.val ∈ c.source := by
    rw [hαsource] at hy
    change D.toPartialEquiv y.val ∈ D.target ∧
      D.symm.toPartialEquiv (D.toPartialEquiv y.val) ∈ a.source
    have hleft : D.symm.toPartialEquiv (D.toPartialEquiv y.val) = y.val :=
      D.toPartialEquiv.left_inv hy.2
    rw [hleft]
    exact ⟨D.map_source hy.2, hy.1⟩
  have hf (y : planarSet.{u} 2) (hy : y ∈ α.source) :
      c.toOpenPartialHomeomorph.extend (𝓡 2) (D y.val) = α.extend (𝓡∂ 2) y := by
    rw [hαsource] at hy
    change a.toPartialEquiv (D.symm.toPartialEquiv (D.toPartialEquiv y.val)) =
      (A.chart x y).val
    have hleft : D.symm.toPartialEquiv (D.toPartialEquiv y.val) = y.val :=
      D.toPartialEquiv.left_inv hy.2
    rw [hleft]
    exact (OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ hy.1).symm
  have hxα : x ∈ α.source := hαsource.symm ▸ ⟨A.mem_source x, hx⟩
  refine IsImmersionAtOfComplement.mk_of_charts
    (ContinuousLinearEquiv.prodUnique ℝ PunctureE2 PUnit.{1}) α c.toOpenPartialHomeomorph
    hxα (hc x hxα)
    (restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡∂ 2))
      (IsManifold.chart_mem_maximalAtlas x) hs)
    (c.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      c.contMDiffOn_toFun c.contMDiffOn_invFun) hc ?_
  intro w hw
  have hy := (α.extend (𝓡∂ 2)).map_target hw
  rw [OpenPartialHomeomorph.extend_source] at hy
  change c.toOpenPartialHomeomorph.extend (𝓡 2)
    (D ((α.extend (𝓡∂ 2)).symm w).val) = w
  rw [hf _ hy]
  exact (α.extend (𝓡∂ 2)).right_inv hw

private theorem punctureRetainedImmersion_closed
    {N : Type u} [TopologicalSpace N] [ChartedSpace PunctureE2 N]
    [IsManifold (𝓡 2) ∞ N]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 2) M]
    [IsManifold (𝓡∂ 2) ∞ M]
    (d : PartialDiffeomorph (𝓡 2) (𝓡∂ 2) N M ∞) (g : M → N)
    (x : M) (hx : x ∈ d.target) (he : ∀ y ∈ d.target, d.symm y = g y) :
    IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 2) (𝓡 2) ∞ g x := by
  let c₀ := PartialDiffeomorph.extendedChart (I := 𝓡 2) (g x)
  let v : PunctureE2 := WithLp.toLp 2 (fun i => if i = 0 then 1 - c₀ (g x) 0 else 0)
  let c := c₀.trans (punctureEmbeddingTranslation v).toPartialDiffeomorph
  let α := (d.symm.trans c).trans punctureEmbeddingInterior
  have hpos : 0 < c (g x) 0 := by
    change 0 < c₀ (g x) 0 + (1 - c₀ (g x) 0)
    linarith
  have hxα : x ∈ α.source := by
    change (x ∈ d.target ∧ d.symm x ∈ c.source) ∧ _
    rw [he x hx]
    refine ⟨⟨hx, mem_extChartAt_source (g x), mem_univ _⟩, ?_⟩
    change 0 < c (d.symm x) 0
    rw [he x hx]
    exact hpos
  have hm (y : M) (hy : y ∈ α.source) : g y ∈ c.source := by
    have h := hy.1.2
    change d.symm y ∈ c.source at h
    rwa [he y hy.1.1] at h
  have hf (y : M) (hy : y ∈ α.source) :
      c.toOpenPartialHomeomorph.extend (𝓡 2) (g y) =
        α.toOpenPartialHomeomorph.extend (𝓡∂ 2) y := by
    change c (g y) = (punctureEmbeddingInterior (c (d.symm y))).val
    rw [he y hy.1.1, punctureEmbeddingInterior_val]
    have hp := hy.2
    change 0 < c (d.symm y) 0 at hp
    rwa [he y hy.1.1] at hp
  refine IsImmersionAtOfComplement.mk_of_charts
    (ContinuousLinearEquiv.prodUnique ℝ PunctureE2 PUnit.{1})
    α.toOpenPartialHomeomorph c.toOpenPartialHomeomorph hxα (hm x hxα)
    (α.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      α.contMDiffOn_toFun α.contMDiffOn_invFun)
    (c.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      c.contMDiffOn_toFun c.contMDiffOn_invFun) hm ?_
  intro w hw
  have hy := (α.toOpenPartialHomeomorph.extend (𝓡∂ 2)).map_target hw
  rw [OpenPartialHomeomorph.extend_source] at hy
  change c.toOpenPartialHomeomorph.extend (𝓡 2)
    (g ((α.toOpenPartialHomeomorph.extend (𝓡∂ 2)).symm w)) = w
  rw [hf _ hy]
  exact (α.toOpenPartialHomeomorph.extend (𝓡∂ 2)).right_inv hw

private theorem punctureVal_embedding :
    letI := punctureCharts B β hβ
    IsSmoothEmbedding (𝓡∂ 2) (SurfaceModel.model B.kind) ∞
      (Subtype.val : punctureSet B β → B.Carrier) := by
  cases B with
  | mk B =>
    cases B with
    | mk k Y =>
      cases k with
      | closed =>
        let B : CompactSurface := ⟨⟨.closed, Y⟩⟩
        let := punctureCharts B β hβ
        have := punctureSmooth B β hβ
        refine ⟨IsImmersionOfComplement.isImmersion (F := PUnit.{1}) ?_,
          _root_.Topology.IsEmbedding.subtypeVal⟩
        intro x
        rcases puncture_cover B β hβ x with hx | hx
        · exact punctureRetainedImmersion_closed (puncturePD B β hβ false)
            Subtype.val x hx (fun y hy => rfl)
        · let d := puncturePD B β hβ true
          let p := d.symm x
          have hp : p ∈ d.source := d.map_target hx
          have hm := punctureAnnulusImmersion_closed (annulusAmbient B β) p hp
          have h := punctureLiftImmersion (𝓡 2) d Subtype.val
            (punctureNative B β true) p hp hm (puncturePatch_apply B β hβ true)
          exact (d.right_inv hx) ▸ h
      | withBoundary =>
        let B : CompactSurface := ⟨⟨.withBoundary, Y⟩⟩
        let := punctureCharts B β hβ
        have := punctureSmooth B β hβ
        refine ⟨IsImmersionOfComplement.isImmersion (F := PUnit.{1}) ?_,
          _root_.Topology.IsEmbedding.subtypeVal⟩
        intro x
        rcases puncture_cover B β hβ x with hx | hx
        · let d := puncturePD B β hβ false
          have hm := punctureLiftImmersion (𝓡∂ 2) d Subtype.val id x.val hx
            (IsImmersionOfComplement.id x.val)
            (fun y hy => puncturePatch_apply B β hβ false y hy)
          have he : d x.val = x := Subtype.ext (retainedPatch_apply B β hβ x.val hx)
          exact he ▸ hm
        · let d := puncturePD B β hβ true
          let p := d.symm x
          have hp : p ∈ d.source := d.map_target hx
          have hm := punctureAnnulusImmersion_half (annulusAmbient B β) p hp
          have h := punctureLiftImmersion (𝓡∂ 2) d Subtype.val
            (punctureNative B β true) p hp hm (puncturePatch_apply B β hβ true)
          exact (d.right_inv hx) ▸ h

include hβ in
theorem exists_puncture_of_interiorChart_with_embedding :
    ∃ B' : CompactSurface.{u}, ∃ b : C(B'.Carrier, B.Carrier),
    ∃ γ : PartialDiffeomorph circleCollarModel (SurfaceModel.model B'.kind)
      (Circle × EuclideanHalfSpace 1) B'.Carrier ∞,
      B'.kind = .withBoundary ∧
      ContMDiff (SurfaceModel.model B'.kind) (SurfaceModel.model B.kind) ∞ b ∧
      IsSmoothEmbedding (SurfaceModel.model B'.kind) (SurfaceModel.model B.kind) ∞ b ∧
      Injective b ∧
      (∀ x, Bijective
        (mfderiv (SurfaceModel.model B'.kind) (SurfaceModel.model B.kind) b x)) ∧
      range b = (β '' {z : PlaneLift.{u} | ‖z.down‖ < 1})ᶜ ∧
      γ.source = circleCollarSource ∧
      (∀ p ∈ circleCollarSource,
        b (γ p) = β (ULift.up ((1 + p.2.val 0 / 2 : ℝ) • (p.1 : ℂ)))) ∧
      b '' (SurfaceModel.model B'.kind).boundary B'.Carrier =
        (SurfaceModel.model B.kind).boundary B.Carrier ∪
          β '' {z : PlaneLift.{u} | ‖z.down‖ = 1} ∧
      Disjoint ((SurfaceModel.model B.kind).boundary B.Carrier)
        (β '' {z : PlaneLift.{u} | ‖z.down‖ = 1}) := by
  let := punctureCharts B β hβ
  have := punctureSmooth B β hβ
  let B' := puncturedSurface B β hβ
  let b : C(B'.Carrier, B.Carrier) := ⟨Subtype.val, continuous_subtype_val⟩
  let γ := puncturedCollar B β hβ
  refine ⟨B', b, γ, rfl, punctureVal_smooth B β hβ, punctureVal_embedding B β hβ,
    Subtype.val_injective,
    punctureVal_mfderiv B β hβ, ?_, puncturedCollar_source B β hβ, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  · exact puncturedCollar_val B β hβ
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (puncture_boundary_iff B β hβ y).mp hy
    · intro hx
      have hxK : x ∈ punctureSet B β := by
        rcases hx with hx | hx
        · exact retained_subset B β (oldBoundary_retained B β hβ x hx)
        · obtain ⟨z, hz, he⟩ := hx
          rintro ⟨w, hw, hew⟩
          have hzsrc : z ∈ β.source := by
            apply hβ
            change ‖z.down‖ ≤ 3
            change ‖z.down‖ = 1 at hz
            rw [hz]
            norm_num
          have hwsrc : w ∈ β.source := by
            apply hβ
            change ‖w.down‖ ≤ 3
            change ‖w.down‖ < 1 at hw
            linarith
          have heq := β.injOn hwsrc hzsrc (hew.trans he.symm)
          rw [heq] at hw
          exact (ne_of_lt hw) hz
      exact ⟨⟨x, hxK⟩, (puncture_boundary_iff B β hβ ⟨x, hxK⟩).mpr hx, rfl⟩
  · apply Set.disjoint_left.mpr
    intro x hx hxnew
    obtain ⟨z, hz, he⟩ := hxnew
    have hzsrc : z ∈ β.source := by
      apply hβ
      change ‖z.down‖ ≤ 3
      change ‖z.down‖ = 1 at hz
      rw [hz]
      norm_num
    have hi := baseChart_interior B β x (he ▸ β.map_source hzsrc)
    exact ((SurfaceModel.model B.kind).isInteriorPoint_iff_not_isBoundaryPoint x).mp hi hx

end GC.GraphManifold.CompactSurface
