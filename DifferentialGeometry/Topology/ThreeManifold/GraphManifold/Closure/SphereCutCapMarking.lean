import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCutCarrier
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapGlobalOrientation
import DifferentialGeometry.Topology.Manifold.OrientationDiffeomorphTransport

/-!
Actual opposite cap markings for the two sides of one positively folded spherical cut.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance sphereCutMarkingSpherePreconnected : PreconnectedSpace ClosureSphere.{u} := by
  let spherePreconnected : PreconnectedSpace SphereTwo := Subtype.preconnectedSpace
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 1)
  infer_instance

private def sphereCutMarkingNormalReflection :
    (ClosureSphere.{u} × ℝ) ≃ₘ⟮sphereSignedCollarModel, sphereSignedCollarModel⟯
      (ClosureSphere.{u} × ℝ) :=
  (Diffeomorph.refl (𝓡 2) ClosureSphere.{u} ∞).prodCongr
    (ContinuousLinearEquiv.neg ℝ).toDiffeomorph

set_option backward.isDefEq.respectTransparency false in
private theorem sphereCutMarkingNormalReflection_negative
    (O : ManifoldOrientation sphereSignedCollarModel (ClosureSphere.{u} × ℝ) 3) :
    sphereCutMarkingNormalReflection.preservesOrientation O O.opposite := by
  let z : ClosureSphere.{u} := Classical.choice inferInstance
  let p : ClosureSphere.{u} × ℝ := (z, 0)
  apply Diffeomorph.preservesOrientation_of_eq_at sphereCutMarkingNormalReflection O O.opposite p
  let L := (sphereCutMarkingNormalReflection.mfderivToContinuousLinearEquiv
    (by simp) p).toLinearEquiv
  have he : L.toLinearMap =
      (LinearMap.id : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] _).prodMap
        (-LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
    ext v
    change mfderiv sphereSignedCollarModel sphereSignedCollarModel
      (Prod.map id ((ContinuousLinearEquiv.neg ℝ).toDiffeomorph : ℝ → ℝ)) p v = _
    erw [mfderiv_prodMap mdifferentiableAt_id
      ((ContinuousLinearEquiv.neg ℝ).toDiffeomorph.contMDiff.mdifferentiableAt (by simp)),
      mfderiv_id]
    change (v.1, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (-id) p.2 v.2) = (v.1, -v.2)
    rw [((hasMFDerivAt_id p.2).neg).mfderiv]
    rfl
  have hd : LinearMap.det L.toLinearMap < 0 := by
    erw [he, LinearMap.det_prodMap,
      show (-LinearMap.id : ℝ →ₗ[ℝ] ℝ) = (-1 : ℝ) • LinearMap.id by ext; simp,
      LinearMap.det_smul]
    simp
  have hfix : sphereCutMarkingNormalReflection p = p := by
    change (z, -(0 : ℝ)) = (z, 0)
    simp
  rw [hfix]
  change Orientation.map (Fin 3) L (O.orientation p) = -O.orientation p
  exact (Orientation.map_eq_neg_iff_det_neg (O.orientation p) L (by
    change 3 = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)
    simp)).mpr hd


section NativeCut

variable {W : CompactCarrier.{u}}
  (c : SphereCutSignedCollars W)
  (hs : ∀ j, (c j).source = sphereSignedCollarSource)
  (hd : Pairwise fun i j => Disjoint (c i).target (c j).target)
  (hI : ∀ j, (c j).target ⊆ W.interior)
  {n : ℕ} (E : BoundaryTori W n)
  (hE : W.model.boundary W.Carrier = E.image)
  (havoid : ∀ i j, Disjoint (E.collar i).target (c j).target)

private def sphereCutMarkingAction (i : Fin 2) :
    (ClosureSphere.{u} × ℝ) ≃ₘ⟮sphereSignedCollarModel, sphereSignedCollarModel⟯
      (ClosureSphere.{u} × ℝ) :=
  if i = 0 then Diffeomorph.refl sphereSignedCollarModel (ClosureSphere.{u} × ℝ) ∞
  else sphereCutMarkingNormalReflection

private theorem sphereCutMarkingCore_fold (i : Fin 2) (p : ClosureSphere.{u} × ℝ)
    (hp : p ∈ univ ×ˢ Ioo (0 : ℝ) 1) :
    sphereCutFold c
      ((sphereCutMixedBoundary c hs hd hI E hE havoid).sphereCapCoreTransition i p) =
        c 0 (sphereCutMarkingAction i p) := by
  change sphereCutFold c
    (sphereCutFullCollar c hs hd 0 (sphereCutBoundarySide i) (sphereCapPositiveHalf p)) = _
  rw [sphereCapPositiveHalf_apply p.1 p.2 hp.2.1,
    sphereCutFullCollar_fold c hs hd 0 (sphereCutBoundarySide i) _ (by
      change p.2 < 1
      exact hp.2.2)]
  fin_cases i <;> rfl

include hs in
private theorem sphereCutMarkingAction_source (i : Fin 2) (p : ClosureSphere.{u} × ℝ)
    (hp : p ∈ univ ×ˢ Ioo (0 : ℝ) 1) : sphereCutMarkingAction i p ∈ (c 0).source := by
  rw [hs 0]
  fin_cases i
  · simp only [sphereCutMarkingAction]
    change p.1 ∈ univ ∧ -1 < p.2 ∧ p.2 < 1
    exact ⟨mem_univ _, by linarith [hp.2.1], hp.2.2⟩
  · simp only [sphereCutMarkingAction]
    change p.1 ∈ univ ∧ -1 < -p.2 ∧ -p.2 < 1
    exact ⟨mem_univ _, by linarith [hp.2.2], by linarith [hp.2.1]⟩

set_option backward.isDefEq.respectTransparency false in
private theorem sphereCutMarkingCore_derivative (i : Fin 2) (p : ClosureSphere.{u} × ℝ)
    (hp : p ∈ univ ×ˢ Ioo (0 : ℝ) 1) :
    let B := sphereCutMixedBoundary c hs hd hI E hE havoid
    (carrierSurgeryPatchTangentEquiv (B.sphereCapCoreTransition i) (by
      rw [B.sphereCapCoreTransition_source]
      exact hp)).trans
      (sphereCutFoldTangentEquiv c hs hd (B.sphereCapCoreTransition i p)).toLinearEquiv =
        ((sphereCutMarkingAction i).mfderivToContinuousLinearEquiv (by simp) p).toLinearEquiv.trans
          (carrierSurgeryPatchTangentEquiv (c 0) (sphereCutMarkingAction_source c hs i p hp)) := by
  let cutCharts := sphereCutChartedSpace c hs hd
  let cutSmooth := sphereCutIsManifold c hs hd
  let B := sphereCutMixedBoundary c hs hd hI E hE havoid
  have hpB : p ∈ (B.sphereCapCoreTransition i).source := by
    rw [B.sphereCapCoreTransition_source]
    exact hp
  have hf : (sphereCutFold c ∘ (B.sphereCapCoreTransition i)) =ᶠ[𝓝 p]
      (c 0 ∘ sphereCutMarkingAction i) := by
    filter_upwards [(isOpen_univ.prod isOpen_Ioo).mem_nhds hp] with q hq
    exact sphereCutMarkingCore_fold c hs hd hI E hE havoid i q hq
  ext v
  have hleft := mfderiv_comp_apply p
    ((sphereCutFold_smooth c hs hd).mdifferentiableAt (by simp))
    ((B.sphereCapCoreTransition i).mdifferentiableAt (by simp) hpB) v
  have hright := mfderiv_comp_apply p
    ((c 0).mdifferentiableAt (by simp) (sphereCutMarkingAction_source c hs i p hp))
    ((sphereCutMarkingAction i).contMDiff.mdifferentiableAt (by simp)) v
  calc
    _ = mfderiv sphereSignedCollarModel W.model
        (sphereCutFold c ∘ B.sphereCapCoreTransition i) p v := hleft.symm
    _ = mfderiv sphereSignedCollarModel W.model
        (c 0 ∘ sphereCutMarkingAction i) p v := by
          rw [hf.mfderiv_eq]
          rfl
    _ = _ := hright

set_option backward.isDefEq.respectTransparency false in
private theorem sphereCutMarkingCore_orientation (i : Fin 2) (p : ClosureSphere.{u} × ℝ)
    (hp : p ∈ univ ×ˢ Ioo (0 : ℝ) 1) :
    let B := sphereCutMixedBoundary c hs hd hI E hE havoid
    Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv (c 0) (sphereCutMarkingAction_source c hs i p hp))
      (Orientation.map (Fin 3)
        ((sphereCutMarkingAction i).mfderivToContinuousLinearEquiv (by simp) p).toLinearEquiv
        ((B.sphereCapOrientationData.signed i).orientation p)) =
      W.orientation.orientation (c 0 (sphereCutMarkingAction i p)) := by
  let B := sphereCutMixedBoundary c hs hd hI E hE havoid
  have hpB : p ∈ (B.sphereCapCoreTransition i).source := by
    rw [B.sphereCapCoreTransition_source]
    exact hp
  have h := congrArg (Orientation.map (Fin 3)
    (sphereCutFoldTangentEquiv c hs hd (B.sphereCapCoreTransition i p)).toLinearEquiv)
    (B.sphereCapOrientationData.core_transport i p hpB)
  erw [← DifferentialGeometry.orientation_map_trans,
    sphereCutMarkingCore_derivative c hs hd hI E hE havoid i p hp,
    DifferentialGeometry.orientation_map_trans] at h
  have hresult := h.trans (sphereCutFold_orientation_map c hs hd (B.sphereCapCoreTransition i p))
  rw [sphereCutMarkingCore_fold c hs hd hI E hE havoid i p hp] at hresult
  exact hresult

include hs in
set_option backward.isDefEq.respectTransparency false in
private theorem sphereCutMarkingPullback_from_point
    (S : ManifoldOrientation sphereSignedCollarModel (ClosureSphere.{u} × ℝ) 3)
    (p0 : ClosureSphere.{u} × ℝ) (hp0 : p0 ∈ (c 0).source)
    (h0 : Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv (c 0) hp0)
      (S.orientation p0) = W.orientation.orientation (c 0 p0)) :
    ∀ p (hp : p ∈ (c 0).source),
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv (c 0) hp)
        (S.orientation p) = W.orientation.orientation (c 0 p) := by
  let U : Opens (ClosureSphere.{u} × ℝ) := ⟨(c 0).source, (c 0).open_source⟩
  have hpre : IsPreconnected (c 0).source := by
    rw [hs 0]
    exact isPreconnected_univ.prod isPreconnected_Ioo
  let sourcePreconnected : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hpre
  have hsm : ContMDiff sphereSignedCollarModel W.model ∞ (fun p : U => c 0 p.val) := by
    intro p
    rw [contMDiffAt_subtype_iff]
    exact (c 0).contMDiffOn.contMDiffAt ((c 0).open_source.mem_nhds p.property)
  have hbij : ∀ p : U, Bijective (mfderiv sphereSignedCollarModel W.model
      (fun q : U => c 0 q.val) p) := by
    intro p
    rw [DifferentialGeometry.mfderiv_restrict_open]
    exact (carrierSurgeryPatchTangentEquiv (c 0) p.property).bijective
  obtain ⟨P, hP⟩ := exists_manifoldOrientation_pullback sphereSignedCollarModel W.model
    S.dimension_eq (fun p : U => c 0 p.val) hsm hbij W.orientation
  have hL (p : U) : (differentialEquivOfBijective sphereSignedCollarModel W.model
      (fun q : U => c 0 q.val) hbij p).toLinearEquiv =
      carrierSurgeryPatchTangentEquiv (c 0) p.property := by
    apply LinearEquiv.ext
    intro v
    change mfderiv sphereSignedCollarModel W.model (fun q : U => c 0 q.val) p v = _
    rw [DifferentialGeometry.mfderiv_restrict_open]
    rfl
  have he : P = S.restrictOpen U := ManifoldOrientation.eq_of_eq_at P
      (S.restrictOpen U) ⟨p0, hp0⟩ (by
        apply (Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv (c 0) hp0)).injective
        have h := hP ⟨p0, hp0⟩
        rw [hL] at h
        exact h.trans h0.symm)
  intro p hp
  have h := hP ⟨p, hp⟩
  rw [hL, he] at h
  exact h

private theorem sphereCutMarkingAction_zero_derivative (p : ClosureSphere.{u} × ℝ) :
    ((sphereCutMarkingAction 0).mfderivToContinuousLinearEquiv (by simp) p).toLinearEquiv =
      LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) := by
  apply LinearEquiv.ext
  intro v
  change mfderiv sphereSignedCollarModel sphereSignedCollarModel id p v = v
  rw [mfderiv_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem sphereCutCapMarking_signed_opposite :
    let B := sphereCutMixedBoundary c hs hd hI E hE havoid
    B.sphereCapOrientationData.signed (1 : Fin 2) =
      (B.sphereCapOrientationData.signed (0 : Fin 2)).opposite := by
  let B := sphereCutMixedBoundary c hs hd hI E hE havoid
  let S := B.sphereCapOrientationData.signed (0 : Fin 2)
  let z : ClosureSphere.{u} := Classical.choice inferInstance
  let p : ClosureSphere.{u} × ℝ := (z, 1 / 2)
  have hp : p ∈ univ ×ˢ Ioo (0 : ℝ) 1 := by
    constructor <;> norm_num [p]
  have hp0 : p ∈ (c 0).source := by
    rw [hs 0]
    constructor <;> norm_num [p]
  have hcore0 := sphereCutMarkingCore_orientation c hs hd hI E hE havoid 0 p hp
  dsimp only at hcore0
  erw [sphereCutMarkingAction_zero_derivative, Orientation.map_refl] at hcore0
  have hglobal := sphereCutMarkingPullback_from_point c hs S p hp0 hcore0
  apply ManifoldOrientation.eq_of_eq_at (B.sphereCapOrientationData.signed (1 : Fin 2)) S.opposite p
  have hcore1 := sphereCutMarkingCore_orientation c hs hd hI E hE havoid 1 p hp
  have hrp := sphereCutMarkingAction_source c hs 1 p hp
  have hsign := (Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv (c 0) hrp)).injective
    (hcore1.trans (hglobal (sphereCutMarkingAction 1 p) hrp).symm)
  have hreflect := sphereCutMarkingNormalReflection_negative S p
  have hneg : Orientation.map (Fin 3)
      ((sphereCutMarkingAction 1).mfderivToContinuousLinearEquiv (by simp) p).toLinearEquiv
      (S.opposite.orientation p) = S.orientation (sphereCutMarkingAction 1 p) := by
    change Orientation.map (Fin 3)
      (sphereCutMarkingNormalReflection.mfderivToContinuousLinearEquiv (by simp) p).toLinearEquiv
      (-S.orientation p) = S.orientation (sphereCutMarkingNormalReflection p)
    rw [Orientation.map_neg, hreflect]
    exact neg_neg (S.orientation (sphereCutMarkingNormalReflection p))
  exact (Orientation.map (Fin 3)
    ((sphereCutMarkingAction 1).mfderivToContinuousLinearEquiv (by simp) p).toLinearEquiv).injective
      (hsign.trans hneg.symm)

set_option backward.isDefEq.respectTransparency false in
theorem sphereCutCapMarking_ball_opposite :
    let B := sphereCutMixedBoundary c hs hd hI E hE havoid
    B.sphereCapOrientationData.ball (1 : Fin 2) =
      (B.sphereCapOrientationData.ball (0 : Fin 2)).opposite := by
  let B := sphereCutMixedBoundary c hs hd hI E hE havoid
  let ballPreconnected : PreconnectedSpace (ClosedCell 3) := by
    apply Subtype.preconnectedSpace
    have hconv : Convex ℝ ({x : EuclideanSpace ℝ (Fin 3) | ‖x‖ ≤ 1} : Set _) := by
      simpa only [Metric.closedBall, dist_zero_right] using
        (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 : ℝ))
    exact hconv.isPreconnected
  let z : ClosureSphere.{u} := Classical.choice inferInstance
  let p : ClosureSphere.{u} × ℝ := (z, -1 / 2)
  have hp : p ∈ MixedBoundaryCertificate.sphereCapBallTransition.source := by
    rw [MixedBoundaryCertificate.sphereCapBallTransition_source]
    constructor <;> norm_num [p]
  apply ManifoldOrientation.eq_of_eq_at (B.sphereCapOrientationData.ball (1 : Fin 2))
    (B.sphereCapOrientationData.ball (0 : Fin 2)).opposite
    (MixedBoundaryCertificate.sphereCapBallTransition p)
  have h1 := B.sphereCapOrientationData.ball_transport (1 : Fin 2) p hp
  rw [sphereCutCapMarking_signed_opposite c hs hd hI E hE havoid,
    ManifoldOrientation.opposite_orientation, Orientation.map_neg] at h1
  rw [B.sphereCapOrientationData.ball_transport (0 : Fin 2) p hp] at h1
  exact h1.symm

private theorem sphereCutMarkingBoundaryReflection_symm :
    sphereCapBoundaryReflection.{u}.symm = sphereCapBoundaryReflection := by
  have hi : Involutive sphereCapBoundaryReflection.{u} := by
    intro z
    apply ULift.ext
    apply Subtype.ext
    change - -z.down.val = z.down.val
    exact neg_neg _
  apply Diffeomorph.ext
  intro z
  apply sphereCapBoundaryReflection.injective
  exact (sphereCapBoundaryReflection.apply_symm_apply z).trans (hi z).symm

set_option backward.isDefEq.respectTransparency false in
private theorem sphereCutMarking_reparameterization_ne :
    let B := sphereCutMixedBoundary c hs hd hI E hE havoid
    B.sphereCapOrientationData.reparameterization (0 : Fin 2) ≠
      B.sphereCapOrientationData.reparameterization (1 : Fin 2) := by
  let B := sphereCutMixedBoundary c hs hd hI E hE havoid
  dsimp only
  intro he
  have hV : B.sphereCapOrientationData.ball (0 : Fin 2) =
      B.sphereCapOrientationData.ball (1 : Fin 2) := by
    apply ManifoldOrientation.ext
    intro x
    let y := (B.sphereCapOrientationData.reparameterization (0 : Fin 2)).symm x
    have h0 := B.sphereCapOrientationData.standard_transport (0 : Fin 2) y
    have h1 := B.sphereCapOrientationData.standard_transport (1 : Fin 2) y
    rw [← he] at h1
    have h := h0.symm.trans h1
    change (B.sphereCapOrientationData.ball (0 : Fin 2)).orientation
      (B.sphereCapOrientationData.reparameterization (0 : Fin 2) y) =
      (B.sphereCapOrientationData.ball (1 : Fin 2)).orientation
        (B.sphereCapOrientationData.reparameterization (0 : Fin 2) y) at h
    rw [(B.sphereCapOrientationData.reparameterization (0 : Fin 2)).apply_symm_apply x] at h
    exact h
  have hop := sphereCutCapMarking_ball_opposite c hs hd hI E hE havoid
  let x : ClosedCell 3 := ⟨0, by simp⟩
  have h := congrArg (fun O : ManifoldOrientation (𝓡∂ 3) (ClosedCell 3) 3 => O.orientation x)
    (hV.trans hop)
  exact Module.Ray.ne_neg_self (B.sphereCapOrientationData.ball (0 : Fin 2) |>.orientation x) h

theorem sphereCutCapMarking_antipodal :
    let B := sphereCutMixedBoundary c hs hd hI E hE havoid
    (B.sphereCapOrientationData.attaching (0 : Fin 2)).symm.trans
      (B.sphereCapOrientationData.attaching (1 : Fin 2)) = sphereCapBoundaryReflection := by
  let B := sphereCutMixedBoundary c hs hd hI E hE havoid
  dsimp only
  have hne := sphereCutMarking_reparameterization_ne c hs hd hI E hE havoid
  rcases B.sphereCapOrientationData.choices (0 : Fin 2) with h0 | h0
  · rcases B.sphereCapOrientationData.choices (1 : Fin 2) with h1 | h1
    · exact (hne (h0.1.trans h1.1.symm)).elim
    · erw [h0.2, h1.2]
      rfl
  · rcases B.sphereCapOrientationData.choices (1 : Fin 2) with h1 | h1
    · erw [h0.2, h1.2, sphereCutMarkingBoundaryReflection_symm]
      rfl
    · exact (hne (h0.1.trans h1.1.symm)).elim

end NativeCut

end GC.GraphManifold
