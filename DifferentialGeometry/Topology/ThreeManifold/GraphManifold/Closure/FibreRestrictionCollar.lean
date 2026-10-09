import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreRestriction
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RegularFibreTube

/-!
A fixed saturated regular-fibre tube gives the actual new radial collar of its base pullback.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.CircleFibration

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}
variable (F : CircleFibration C U)
variable (β : PartialDiffeomorph 𝓘(ℝ, ℂ) (SurfaceModel.model F.base.kind)
  PlaneLift.{u} F.base.Carrier ∞)
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model
  (PlaneLift.{u} × Circle) C.Carrier ∞)
variable (hβ : {z : PlaneLift.{u} | ‖z.down‖ ≤ 3} ⊆ β.source)
variable (hφ : φ.source = β.source ×ˢ univ) (hU : φ.target ⊆ U)
variable (hprojection : ∀ z t, z ∈ β.source →
  ∃ hu : φ (z, t) ∈ U, F.projection ⟨φ (z, t), hu⟩ = β z)
variable (hsaturated : φ.target = Subtype.val '' {x : U | F.projection x ∈ β.target})
variable (B' : CompactSurface.{u}) (b : C(B'.Carrier, F.base.Carrier))
variable (hinj : Injective b)
variable (hsm : ContMDiff (SurfaceModel.model B'.kind) (SurfaceModel.model F.base.kind) ∞ b)
variable (hbij : ∀ y, Bijective (mfderiv (SurfaceModel.model B'.kind)
  (SurfaceModel.model F.base.kind) b y))
variable (γ : PartialDiffeomorph circleCollarModel (SurfaceModel.model B'.kind)
  (Circle × EuclideanHalfSpace 1) B'.Carrier ∞)
variable (hγ : γ.source = circleCollarSource)
variable (hγradial : ∀ p ∈ circleCollarSource,
  b (γ p) = β (ULift.up ((1 + p.2.val 0 / 2) • (p.1 : ℂ))))

private theorem restrictionHalfSource_open : IsOpen halfCollarSource :=
  isOpen_lt ((EuclideanSpace.proj 0).continuous.comp
    (continuous_subtype_val.comp continuous_snd)) continuous_const

private def restrictionRadial (p : Torus × EuclideanHalfSpace 1) : PlaneLift.{u} × Circle :=
  (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)

include hβ hφ in
private theorem restrictionRadial_source {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) : restrictionRadial.{u} p ∈ φ.source := by
  rw [hφ]
  refine ⟨hβ ?_, mem_univ _⟩
  change ‖(1 + p.2.val 0 / 2) • (p.1.1 : ℂ)‖ ≤ 3
  rw [norm_smul, Real.norm_of_nonneg (by linarith [p.2.property]), Circle.norm_coe, mul_one]
  change p.2.val 0 < 1 at hp
  linarith [p.2.property]

private def restrictionCollarPoint (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) : FibrePullbackTotal F B' b := by
  have hs := restrictionRadial_source F β φ hβ hφ hp
  have hu := hU (φ.map_source hs)
  refine ⟨⟨φ (restrictionRadial.{u} p), hu⟩, γ (p.1.1, p.2), ?_⟩
  obtain ⟨hu', he⟩ := hprojection (restrictionRadial.{u} p).1 (restrictionRadial.{u} p).2
    ((hφ ▸ hs).1)
  exact (hγradial (p.1.1, p.2) hp).trans he.symm

private theorem restrictionCollarPoint_projection (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    F.fibrePullbackProjection B' b hinj
      (restrictionCollarPoint F β φ hβ hφ hU hprojection B' b γ hγradial p hp) =
      γ (p.1.1, p.2) := by
  apply hinj
  have hs := restrictionRadial_source F β φ hβ hφ hp
  obtain ⟨hu, he⟩ := hprojection (restrictionRadial.{u} p).1 (restrictionRadial.{u} p).2
    ((hφ ▸ hs).1)
  exact (F.fibrePullbackProjection_square B' b hinj _).trans
    (he.trans (hγradial (p.1.1, p.2) hp).symm)

private def restrictionCollarMap (p : Torus × EuclideanHalfSpace 1) :
    FibrePullbackTotal F B' b := by
  classical
  exact if hp : p ∈ halfCollarSource then
    restrictionCollarPoint F β φ hβ hφ hU hprojection B' b γ hγradial p hp
  else restrictionCollarPoint F β φ hβ hφ hU hprojection B' b γ hγradial
    (1, halfZero) (by change (0 : ℝ) < 1; norm_num)

private theorem restrictionCollarMap_val {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    (restrictionCollarMap F β φ hβ hφ hU hprojection B' b γ hγradial p).val.val =
      φ (restrictionRadial.{u} p) := by
  simp only [restrictionCollarMap, dite_eq_left hp]
  rfl

private theorem restrictionCollarMap_projection {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    F.fibrePullbackProjection B' b hinj
      (restrictionCollarMap F β φ hβ hφ hU hprojection B' b γ hγradial p) =
      γ (p.1.1, p.2) := by
  simp only [restrictionCollarMap, dite_eq_left hp]
  exact restrictionCollarPoint_projection F β φ hβ hφ hU hprojection B' b hinj γ hγradial p hp

private def restrictionCollarInv (x : FibrePullbackTotal F B' b) :
    Torus × EuclideanHalfSpace 1 :=
  let q := γ.symm (F.fibrePullbackProjection B' b hinj x)
  ((q.1, (φ.symm x.val.val).2), q.2)

include hβ hφ hsaturated hγ hγradial in
private theorem restrictionCollar_target_tube {x : FibrePullbackTotal F B' b}
    (hx : F.fibrePullbackProjection B' b hinj x ∈ γ.target) : x.val.val ∈ φ.target := by
  rw [hsaturated]
  refine ⟨x.val, ?_, rfl⟩
  let q := γ.symm (F.fibrePullbackProjection B' b hinj x)
  have hq : q ∈ circleCollarSource := hγ ▸ γ.map_target hx
  have he : b (γ q) = F.projection x.val := by
    exact (congrArg b (γ.toPartialEquiv.right_inv hx)).trans
      (F.fibrePullbackProjection_square B' b hinj x)
  change F.projection x.val ∈ β.target
  rw [← he, hγradial q hq]
  apply β.map_source
  have hs := restrictionRadial_source F β φ hβ hφ
    (p := ((q.1, 1), q.2)) hq
  exact (hφ ▸ hs).1

include hγ in
private theorem restrictionCollarInv_source {x : FibrePullbackTotal F B' b}
    (hx : F.fibrePullbackProjection B' b hinj x ∈ γ.target) :
    restrictionCollarInv F φ B' b hinj γ x ∈ halfCollarSource := by
  have hg : γ.symm (F.fibrePullbackProjection B' b hinj x) ∈ circleCollarSource :=
    hγ ▸ γ.map_target hx
  exact hg

include hγ in
private theorem restrictionCollar_left_inv {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    restrictionCollarInv F φ B' b hinj γ
      (restrictionCollarMap F β φ hβ hφ hU hprojection B' b γ hγradial p) = p := by
  have he : γ.symm.toPartialEquiv (γ (p.1.1, p.2)) = (p.1.1, p.2) :=
    γ.toPartialEquiv.left_inv (hγ.symm ▸ hp : (p.1.1, p.2) ∈ γ.source)
  have ht : φ.symm.toPartialEquiv (φ (restrictionRadial.{u} p)) = restrictionRadial.{u} p :=
    φ.toPartialEquiv.left_inv (restrictionRadial_source F β φ hβ hφ hp)
  simp only [restrictionCollarInv, restrictionCollarMap_projection F β φ hβ hφ hU
    hprojection B' b hinj γ hγradial hp, he,
    restrictionCollarMap_val F β φ hβ hφ hU hprojection B' b γ hγradial hp, ht]
  rfl

include hβ hφ hprojection hsaturated hγ hγradial in
private theorem restrictionCollar_radial_inv {x : FibrePullbackTotal F B' b}
    (hx : F.fibrePullbackProjection B' b hinj x ∈ γ.target) :
    restrictionRadial.{u} (restrictionCollarInv F φ B' b hinj γ x) = φ.symm x.val.val := by
  have ht := restrictionCollar_target_tube F β φ hβ hφ hsaturated
    B' b hinj γ hγ hγradial hx
  have hs := φ.map_target ht
  have hsβ : (φ.symm x.val.val).1 ∈ β.source := (hφ ▸ hs).1
  obtain ⟨hu, he⟩ := hprojection (φ.symm x.val.val).1 (φ.symm x.val.val).2 hsβ
  have hex : (⟨φ (φ.symm x.val.val), hu⟩ : U) = x.val :=
    Subtype.ext (φ.right_inv ht)
  rw [hex] at he
  let q := γ.symm (F.fibrePullbackProjection B' b hinj x)
  have hq : q ∈ circleCollarSource := hγ ▸ γ.map_target hx
  have hr := restrictionRadial_source F β φ hβ hφ (p := ((q.1, 1), q.2)) hq
  have hbq : β (ULift.up ((1 + q.2.val 0 / 2) • (q.1 : ℂ))) = F.projection x.val := by
    rw [← hγradial q hq]
    exact (congrArg b (γ.toPartialEquiv.right_inv hx)).trans
      (F.fibrePullbackProjection_square B' b hinj x)
  apply Prod.ext
  · exact β.injOn ((hφ ▸ hr).1) hsβ (hbq.trans he)
  · rfl

include hγ hsaturated in
private theorem restrictionCollar_right_inv {x : FibrePullbackTotal F B' b}
    (hx : F.fibrePullbackProjection B' b hinj x ∈ γ.target) :
    restrictionCollarMap F β φ hβ hφ hU hprojection B' b γ hγradial
      (restrictionCollarInv F φ B' b hinj γ x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  rw [restrictionCollarMap_val F β φ hβ hφ hU hprojection B' b γ hγradial
    (restrictionCollarInv_source F φ B' b hinj γ hγ hx),
    restrictionCollar_radial_inv F β φ hβ hφ hprojection hsaturated
      B' b hinj γ hγ hγradial hx]
  exact φ.right_inv (restrictionCollar_target_tube F β φ hβ hφ hsaturated
    B' b hinj γ hγ hγradial hx)

private theorem restrictionRadial_smooth :
    ContMDiff halfCollarModel (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ restrictionRadial.{u} := by
  have hr : ContMDiff halfCollarModel 𝓘(ℝ) ∞
      (fun p : Torus × EuclideanHalfSpace 1 => 1 + p.2.val 0 / 2) :=
    contMDiff_const.add
      ((DifferentialGeometry.Topology.Manifold.contMDiff_halfSpaceOneCoordinate.comp
        contMDiff_snd).div_const 2)
  have hz : ContMDiff halfCollarModel 𝓘(ℝ, ℂ) ∞
      (fun p : Torus × EuclideanHalfSpace 1 => (p.1.1 : ℂ)) :=
    contMDiff_circle_coe.comp (contMDiff_fst.comp contMDiff_fst)
  exact (contMDiff_planeLift_up.comp (hr.smul hz)).prodMk
    (contMDiff_snd.comp contMDiff_fst)

private theorem restrictionCollar_continuous :
    ContinuousOn (restrictionCollarMap F β φ hβ hφ hU hprojection B' b γ hγradial)
      halfCollarSource := by
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
  exact (φ.contMDiffOn.continuousOn.comp restrictionRadial_smooth.continuous.continuousOn
    (fun p hp => restrictionRadial_source F β φ hβ hφ hp)).congr
      (fun p hp => (restrictionCollarMap_val F β φ hβ hφ hU hprojection
        B' b γ hγradial hp))

include hβ hφ hsaturated hγ hγradial in
private theorem restrictionCollarInv_continuous :
    ContinuousOn (restrictionCollarInv F φ B' b hinj γ)
      ((F.fibrePullbackProjection B' b hinj) ⁻¹' γ.target) := by
  have hg := γ.symm.contMDiffOn.continuousOn.comp
    (F.fibrePullbackProjection B' b hinj).continuous.continuousOn (fun x hx => hx)
  have ht := φ.symm.contMDiffOn.continuousOn.comp
    (F.fibrePullbackInclusion B' b).continuous.continuousOn
      (fun x hx => restrictionCollar_target_tube F β φ hβ hφ hsaturated
        B' b hinj γ hγ hγradial hx)
  exact (hg.fst.prodMk ht.snd).prodMk hg.snd

private def restrictionCollarHomeomorph :
    OpenPartialHomeomorph (Torus × EuclideanHalfSpace 1) (FibrePullbackTotal F B' b) where
  toFun := restrictionCollarMap F β φ hβ hφ hU hprojection B' b γ hγradial
  invFun := restrictionCollarInv F φ B' b hinj γ
  source := halfCollarSource
  target := (F.fibrePullbackProjection B' b hinj) ⁻¹' γ.target
  map_source' p hp := by
    change F.fibrePullbackProjection B' b hinj
      (restrictionCollarMap F β φ hβ hφ hU hprojection B' b γ hγradial p) ∈ γ.target
    rw [restrictionCollarMap_projection F β φ hβ hφ hU hprojection B' b hinj γ hγradial hp]
    exact γ.map_source (hγ.symm ▸ hp)
  map_target' x hx := restrictionCollarInv_source F φ B' b hinj γ hγ hx
  left_inv' p hp := restrictionCollar_left_inv F β φ hβ hφ hU hprojection
    B' b hinj γ hγ hγradial hp
  right_inv' x hx := restrictionCollar_right_inv F β φ hβ hφ hU hprojection hsaturated
    B' b hinj γ hγ hγradial hx
  open_source := restrictionHalfSource_open
  open_target := γ.open_target.preimage (F.fibrePullbackProjection B' b hinj).continuous
  continuousOn_toFun := restrictionCollar_continuous F β φ hβ hφ hU hprojection B' b γ hγradial
  continuousOn_invFun := restrictionCollarInv_continuous F β φ hβ hφ hsaturated
    B' b hinj γ hγ hγradial

include hβ hφ hsaturated hγ hγradial in
private theorem restrictionCollarInv_smooth :
    letI := F.fibrePullbackChartedSpace B' b hinj hsm
    ContMDiffOn (F.fibreRestrictionCarrier B' b hinj hsm hbij).model halfCollarModel ∞
      (restrictionCollarInv F φ B' b hinj γ)
      ((F.fibrePullbackProjection B' b hinj) ⁻¹' γ.target) := by
  let := F.fibrePullbackChartedSpace B' b hinj hsm
  have hg := γ.symm.contMDiffOn.comp
    (F.fibreRestrictionBaseProjection_smooth B' b hinj hsm hbij).contMDiffOn (fun x hx => hx)
  have ht := φ.symm.contMDiffOn.comp
    (F.fibreRestrictionInclusion_smooth B' b hinj hsm hbij).contMDiffOn
      (fun x hx => restrictionCollar_target_tube F β φ hβ hφ hsaturated
        B' b hinj γ hγ hγradial hx)
  exact fun x hx => ((hg x hx).fst.prodMk (ht x hx).snd).prodMk (hg x hx).snd

private def restrictionOldAmbientCoordinate (y : B'.Carrier) :
    PartialDiffeomorph C.model ((SurfaceModel.model F.base.kind).prod (𝓡 1))
      C.Carrier (F.neighborhood (b y) × Circle) ∞ :=
  let v := (F.trivialization (b y)).symm (⟨b y, F.mem_neighborhood (b y)⟩, 1)
  let W := TopologicalSpace.Opens.comap F.projection (F.neighborhood (b y))
  let incW := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := C.model) W ⟨v⟩
  let incU := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := C.model) U ⟨v.val⟩
  (incU.symm.trans incW.symm).trans (F.trivialization (b y)).toPartialDiffeomorph

private theorem restrictionOldAmbientCoordinate_source (y : B'.Carrier) (x : U)
    (hx : F.projection x ∈ F.neighborhood (b y)) :
    x.val ∈ (restrictionOldAmbientCoordinate F B' b y).source := by
  let v := (F.trivialization (b y)).symm (⟨b y, F.mem_neighborhood (b y)⟩, 1)
  let W := TopologicalSpace.Opens.comap F.projection (F.neighborhood (b y))
  let incW := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := C.model) W ⟨v⟩
  let incU := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := C.model) U ⟨v.val⟩
  have hxU : x.val ∈ incU.target := U.openPartialHomeomorphSubtypeCoe_target ⟨v.val⟩ ▸ x.property
  have heU : incU.symm x.val = x := by
    apply Subtype.ext
    exact incU.right_inv hxU
  change (x.val ∈ incU.target ∧ incU.symm x.val ∈ incW.target) ∧
    incW.symm (incU.symm x.val) ∈ univ
  rw [heU]
  exact ⟨⟨hxU, W.openPartialHomeomorphSubtypeCoe_target ⟨v⟩ ▸ hx⟩, mem_univ _⟩

private theorem restrictionOldAmbientCoordinate_apply (y : B'.Carrier) (x : U)
    (hx : F.projection x ∈ F.neighborhood (b y)) :
    restrictionOldAmbientCoordinate F B' b y x.val =
      F.trivialization (b y) ⟨x, hx⟩ := by
  let v := (F.trivialization (b y)).symm (⟨b y, F.mem_neighborhood (b y)⟩, 1)
  let W := TopologicalSpace.Opens.comap F.projection (F.neighborhood (b y))
  let incW := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := C.model) W ⟨v⟩
  let incU := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := C.model) U ⟨v.val⟩
  have hxU : x.val ∈ incU.target := U.openPartialHomeomorphSubtypeCoe_target ⟨v.val⟩ ▸ x.property
  have heU : incU.symm x.val = x := by
    apply Subtype.ext
    exact incU.right_inv hxU
  have hxW : x ∈ incW.target := W.openPartialHomeomorphSubtypeCoe_target ⟨v⟩ ▸ hx
  have heW : incW.symm x = ⟨x, hx⟩ := by
    apply Subtype.ext
    exact incW.right_inv hxW
  change F.trivialization (b y) (incW.symm (incU.symm x.val)) = _
  rw [heU, heW]

private def restrictionBaseCoordinate (y : B'.Carrier) :
    PartialDiffeomorph circleCollarModel (SurfaceModel.model B'.kind)
      (Circle × EuclideanHalfSpace 1) (F.fibrePullbackNeighborhood B' b y) ∞ :=
  γ.trans (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
    (I := SurfaceModel.model B'.kind) (F.fibrePullbackNeighborhood B' b y)
      ⟨⟨y, F.mem_fibrePullbackNeighborhood B' b y⟩⟩).symm

include hβ hφ hU hprojection hγradial in
private theorem restrictionLocal_apply (y : B'.Carrier) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource)
    (hy : γ (p.1.1, p.2) ∈ F.fibrePullbackNeighborhood B' b y) :
    F.fibreRestrictionPatch B' b hinj hsm hbij y
      (restrictionBaseCoordinate F B' b γ y (p.1.1, p.2),
        (restrictionOldAmbientCoordinate F B' b y (φ (restrictionRadial.{u} p))).2) =
      restrictionCollarMap F β φ hβ hφ hU hprojection B' b γ hγradial p := by
  let x := restrictionCollarMap F β φ hβ hφ hU hprojection B' b γ hγradial p
  let d := F.fibreRestrictionPatch B' b hinj hsm hbij y
  let V := F.fibrePullbackNeighborhood B' b y
  let inc := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal
    (I := SurfaceModel.model B'.kind) V ⟨⟨y, F.mem_fibrePullbackNeighborhood B' b y⟩⟩
  have hinc : γ (p.1.1, p.2) ∈ inc.target :=
    V.openPartialHomeomorphSubtypeCoe_target _ ▸ hy
  have hb : (restrictionBaseCoordinate F B' b γ y (p.1.1, p.2)).val =
      γ (p.1.1, p.2) := inc.right_inv hinc
  have hx : x ∈ d.target := by
    rw [F.fibreRestrictionPatch_target]
    change F.fibrePullbackProjection B' b hinj x ∈ V
    rw [restrictionCollarMap_projection F β φ hβ hφ hU hprojection
      B' b hinj γ hγradial hp]
    exact hy
  have ho : F.projection x.val ∈ F.neighborhood (b y) := by
    rw [← F.fibrePullbackProjection_square B' b hinj x,
      restrictionCollarMap_projection F β φ hβ hφ hU hprojection
        B' b hinj γ hγradial hp]
    exact hy
  have he :
      (restrictionBaseCoordinate F B' b γ y (p.1.1, p.2),
        (restrictionOldAmbientCoordinate F B' b y (φ (restrictionRadial.{u} p))).2) = d.symm x := by
    apply Prod.ext
    · apply Subtype.ext
      exact hb.trans ((restrictionCollarMap_projection F β φ hβ hφ hU hprojection
        B' b hinj γ hγradial hp).symm.trans
          (F.fibrePullbackPatch_symm_fst B' b hinj y x hx).symm)
    · rw [← restrictionCollarMap_val F β φ hβ hφ hU hprojection
        B' b γ hγradial hp,
        restrictionOldAmbientCoordinate_apply F B' b y x.val ho]
      exact (F.fibreRestrictionPatch_symm_fibre B' b hinj hsm hbij y x hx ho).symm
  rw [he]
  exact d.right_inv hx

include hinj hsm hbij hγ in
private theorem restrictionCollar_smooth :
    letI := F.fibrePullbackChartedSpace B' b hinj hsm
    ContMDiffOn halfCollarModel (F.fibreRestrictionCarrier B' b hinj hsm hbij).model ∞
      (restrictionCollarMap F β φ hβ hφ hU hprojection B' b γ hγradial)
      halfCollarSource := by
  let := F.fibrePullbackChartedSpace B' b hinj hsm
  intro p hp
  let y := γ (p.1.1, p.2)
  let α := restrictionBaseCoordinate F B' b γ y
  let L := restrictionOldAmbientCoordinate F B' b y
  let d := F.fibreRestrictionPatch B' b hinj hsm hbij y
  let a : Torus × EuclideanHalfSpace 1 → Circle × EuclideanHalfSpace 1 :=
    fun q => (q.1.1, q.2)
  have ha : ContMDiff halfCollarModel circleCollarModel ∞ a :=
    (contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd
  have hy : y ∈ F.fibrePullbackNeighborhood B' b y :=
    F.mem_fibrePullbackNeighborhood B' b y
  have hα : a p ∈ α.source := by
    constructor
    · change a p ∈ γ.source
      exact hγ.symm ▸ hp
    · change γ (a p) ∈
        ((F.fibrePullbackNeighborhood B' b y).openPartialHomeomorphSubtypeCoe
          ⟨⟨y, hy⟩⟩).target
      exact (F.fibrePullbackNeighborhood B' b y).openPartialHomeomorphSubtypeCoe_target
        ⟨⟨y, hy⟩⟩ ▸ hy
  have hpφ := restrictionRadial_source F β φ hβ hφ hp
  let x := restrictionCollarMap F β φ hβ hφ hU hprojection B' b γ hγradial p
  have ho : F.projection x.val ∈ F.neighborhood (b y) := by
    rw [← F.fibrePullbackProjection_square B' b hinj x,
      restrictionCollarMap_projection F β φ hβ hφ hU hprojection
        B' b hinj γ hγradial hp]
    exact hy
  have hL : φ (restrictionRadial.{u} p) ∈ L.source := by
    rw [← restrictionCollarMap_val F β φ hβ hφ hU hprojection B' b γ hγradial hp]
    exact restrictionOldAmbientCoordinate_source F B' b y x.val ho
  let g : Torus × EuclideanHalfSpace 1 → F.fibrePullbackNeighborhood B' b y × Circle :=
    fun q => (α (a q), (L (φ (restrictionRadial.{u} q))).2)
  have hg : ContMDiffAt halfCollarModel ((SurfaceModel.model B'.kind).prod (𝓡 1)) ∞ g p :=
    ((α.contMDiffOn.contMDiffAt (α.open_source.mem_nhds hα)).comp p (ha p)).prodMk
      ((contMDiff_snd _).comp p ((L.contMDiffOn.contMDiffAt (L.open_source.mem_nhds hL)).comp p
        ((φ.contMDiffOn.contMDiffAt (φ.open_source.mem_nhds hpφ)).comp p
          (restrictionRadial_smooth p))))
  have hd : g p ∈ d.source := by
    rw [F.fibreRestrictionPatch_source]
    exact mem_univ _
  have hs : ContMDiffAt halfCollarModel (F.fibreRestrictionCarrier B' b hinj hsm hbij).model ∞
      (fun q => d (g q)) p := (d.contMDiffOn.contMDiffAt (d.open_source.mem_nhds hd)).comp p hg
  have hn : ∀ᶠ q in 𝓝 p, q ∈ halfCollarSource ∧ a q ∈ α.source :=
    Filter.Eventually.and (restrictionHalfSource_open.mem_nhds hp)
      (ha.continuous.continuousAt.preimage_mem_nhds (α.open_source.mem_nhds hα))
  apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hn] with q hq
  symm
  apply restrictionLocal_apply F β φ hβ hφ hU hprojection B' b hinj hsm hbij γ hγradial y hq.1
  have hh := hq.2.2
  change γ (a q) ∈ ((F.fibrePullbackNeighborhood B' b y).openPartialHomeomorphSubtypeCoe
    ⟨⟨y, hy⟩⟩).target at hh
  rw [(F.fibrePullbackNeighborhood B' b y).openPartialHomeomorphSubtypeCoe_target ⟨⟨y, hy⟩⟩] at hh
  exact hh

def fibreRestrictionRadialCollar :
    PartialDiffeomorph halfCollarModel (F.fibreRestrictionCarrier B' b hinj hsm hbij).model
      (Torus × EuclideanHalfSpace 1) (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier ∞ where
  __ := restrictionCollarHomeomorph F β φ hβ hφ hU hprojection hsaturated B' b hinj γ hγ hγradial
  contMDiffOn_toFun := restrictionCollar_smooth F β φ hβ hφ hU hprojection
    B' b hinj hsm hbij γ hγ hγradial
  contMDiffOn_invFun := restrictionCollarInv_smooth F β φ hβ hφ hsaturated
    B' b hinj hsm hbij γ hγ hγradial

theorem fibreRestrictionRadialCollar_source :
    (F.fibreRestrictionRadialCollar β φ hβ hφ hU hprojection hsaturated
      B' b hinj hsm hbij γ hγ hγradial).source = halfCollarSource := rfl

theorem fibreRestrictionRadialCollar_target :
    (F.fibreRestrictionRadialCollar β φ hβ hφ hU hprojection hsaturated
      B' b hinj hsm hbij γ hγ hγradial).target =
      (F.fibreRestrictionBaseProjection B' b hinj hsm hbij) ⁻¹' γ.target := rfl

theorem fibreRestrictionRadialCollar_inclusion (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    F.fibreRestrictionInclusion B' b hinj hsm hbij
      (F.fibreRestrictionRadialCollar β φ hβ hφ hU hprojection hsaturated
        B' b hinj hsm hbij γ hγ hγradial p) =
      φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2) :=
  restrictionCollarMap_val F β φ hβ hφ hU hprojection B' b γ hγradial hp

theorem fibreRestrictionRadialCollar_projection (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    F.fibreRestrictionBaseProjection B' b hinj hsm hbij
      (F.fibreRestrictionRadialCollar β φ hβ hφ hU hprojection hsaturated
        B' b hinj hsm hbij γ hγ hγradial p) = γ (p.1.1, p.2) :=
  restrictionCollarMap_projection F β φ hβ hφ hU hprojection B' b hinj γ hγradial hp

theorem fibreRestrictionRadialCollar_symm_apply
    (x : (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier) :
    (F.fibreRestrictionRadialCollar β φ hβ hφ hU hprojection hsaturated
      B' b hinj hsm hbij γ hγ hγradial).symm x =
      (((γ.symm (F.fibreRestrictionBaseProjection B' b hinj hsm hbij x)).1,
        (φ.symm (F.fibreRestrictionInclusion B' b hinj hsm hbij x)).2),
        (γ.symm (F.fibreRestrictionBaseProjection B' b hinj hsm hbij x)).2) := rfl

private theorem restrictionHalfZero_boundary (t : Torus) :
    halfCollarModel.IsBoundaryPoint (t, halfZero) := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint]
  intro h
  change (t, halfZero) ∈ halfCollarModel.interior (Torus × EuclideanHalfSpace 1) at h
  rw [ModelWithCorners.interior_prod] at h
  have hh := h.2
  change (modelWithCornersEuclideanHalfSpace 1).IsInteriorPoint halfZero at hh
  rw [ModelWithCorners.IsInteriorPoint, interior_range_modelWithCornersEuclideanHalfSpace] at hh
  change (0 : ℝ) < 0 at hh
  exact lt_irrefl _ hh

theorem fibreRestrictionRadialCollar_zero (t : Torus) :
    F.fibreRestrictionRadialCollar β φ hβ hφ hU hprojection hsaturated
      B' b hinj hsm hbij γ hγ hγradial (t, halfZero) ∈
      (F.fibreRestrictionCarrier B' b hinj hsm hbij).model.boundary
        (F.fibreRestrictionCarrier B' b hinj hsm hbij).Carrier := by
  let Γ := F.fibreRestrictionRadialCollar β φ hβ hφ hU hprojection hsaturated
    B' b hinj hsm hbij γ hγ hγradial
  have hp : (t, halfZero) ∈ Γ.source := by
    change (0 : ℝ) < 1
    norm_num
  exact ((Γ.isLocalDiffeomorphAt halfCollarModel
    (F.fibreRestrictionCarrier B' b hinj hsm hbij).model ∞ hp).isBoundaryPoint_iff
      (by simp)).mp (restrictionHalfZero_boundary t)

end GC.GraphManifold.CircleFibration
