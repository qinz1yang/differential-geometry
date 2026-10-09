import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreMarkedRestoration
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgerySeamOrientation

/-!
The chosen physical reversing matching forces the actual marked filling map to be positive.
Both radial halves use the same regular-fibre signed tube.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open GC.Endpoint.CompactCarrier GC.GraphManifold.TorusPairing
open GC.Seifert.ElementaryPresentation
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

def markedRestorationFill
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (PlaneLift.{u} × Circle) M.Carrier ∞)
    (S : CompactCarrier.{u}) (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier)
    (ε : Bool) (y : S.Carrier) : M.Carrier :=
  regularFibreRestorationFill M φ ((markedRestorationSolidMap S g ε).symm y)

theorem markedRestorationSolidMap_collar (S : CompactCarrier.{u})
    (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier)
    (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (ε : Bool)
    (p : Torus × EuclideanHalfSpace 1) :
    markedRestorationSolidMap S g ε (solidCollar.{u} 1 p) =
      (markedSolidBoundary S g ψ).collar 0 (markedRestorationMatching ψ ε p.1, p.2) := by
  rw [markedSolidBoundary_collar]
  cases ε
  · change g (solidCollar.{u} 1 p) = g (solidCollar.{u} 1 (ψ.symm (ψ p.1), p.2))
    rw [ψ.symm_apply_apply]
  · change g (boundedPlugSolidReflection (solidCollar.{u} 1 p)) =
      g (solidCollar.{u} 1 (ψ.symm (boundaryPortMarkedReflection ψ (ψ p.1)), p.2))
    rw [boundedPlugSolidReflection_collar, boundaryPortMarkedReflection_apply,
      ψ.symm_apply_apply, ψ.symm_apply_apply]

theorem markedRestorationFill_smooth
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (PlaneLift.{u} × Circle) M.Carrier ∞)
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    (S : CompactCarrier.{u}) (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier) (ε : Bool) :
    ContMDiff S.model (𝓡 3) ∞ (markedRestorationFill M φ S g ε) :=
  (regularFibreRestorationFill_smooth M φ h3).comp
    (markedRestorationSolidMap S g ε).symm.contMDiff

theorem markedRestorationFill_mfderiv_bijective
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (PlaneLift.{u} × Circle) M.Carrier ∞)
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    (S : CompactCarrier.{u}) (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier)
    (ε : Bool) (y : S.Carrier) :
    Bijective (mfderiv S.model (𝓡 3) (markedRestorationFill M φ S g ε) y) := by
  change Bijective (mfderiv S.model (𝓡 3)
    (regularFibreRestorationFill M φ ∘ (markedRestorationSolidMap S g ε).symm) y)
  rw [mfderiv_comp y
    ((regularFibreRestorationFill_smooth M φ h3).mdifferentiableAt (by simp))
    ((markedRestorationSolidMap S g ε).symm.contMDiff.mdifferentiableAt (by simp))]
  exact (regularFibreRestorationFill_bijective_mfderiv M φ h3 _).comp
    ((markedRestorationSolidMap S g ε).symm.mfderivToContinuousLinearEquiv (by simp) y).bijective

private theorem markedOrientation_point (M : ConnectedClosedOrientedManifold.{u} 3)
    (x y : M.Carrier) (hxy : x = y) :
    M.orientation.orientation x = M.orientation.orientation y := by
  subst y
  rfl

private theorem markedOrientation_comp_inverse {E F H : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup H] [Module ℝ H]
    (L : E ≃ₗ[ℝ] F) (R : F ≃ₗ[ℝ] H)
    (o : Orientation ℝ F (Fin 3)) (o' : Orientation ℝ H (Fin 3))
    (ho : Orientation.map (Fin 3) R o = o') :
    Orientation.map (Fin 3) (L.trans R).symm o' = Orientation.map (Fin 3) L.symm o := by
  rw [LinearEquiv.trans_symm, DifferentialGeometry.orientation_map_trans, ← ho]
  congr 1
  exact (Orientation.map (Fin 3) R).symm_apply_apply o

private theorem markedSigned_inverse_negative {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (B : E ≃ₗ[ℝ] ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ))
    (A : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ) ≃ₗ[ℝ] F)
    (o : Orientation ℝ F (Fin 3)) :
    Orientation.map (Fin 3) ((B.trans surgerySignedNormalReflection).trans A).symm o =
      -Orientation.map (Fin 3) (B.trans A).symm o := by
  have hi : surgerySignedNormalReflection.symm = surgerySignedNormalReflection := by
    ext v <;> simp [surgerySignedNormalReflection]
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_symm,
    DifferentialGeometry.orientation_map_trans, DifferentialGeometry.orientation_map_trans, hi,
    surgerySignedNormalReflection_map, Orientation.map_neg,
    LinearEquiv.trans_symm, DifferentialGeometry.orientation_map_trans]

private theorem markedCollar_derivative
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (PlaneLift.{u} × Circle) M.Carrier ∞)
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    {C : CompactCarrier.{u}}
    (c : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hc : c.source = halfCollarSource) (f : C.Carrier → M.Carrier)
    (hf : ContMDiff C.model (𝓡 3) ∞ f) (σ : ℝ)
    (he : ∀ p ∈ halfCollarSource,
      f (c p) = regularFibreRestorationSignedTube M φ (surgeryHalfSignedCoordinate σ p))
    (t : Torus) :
    (mfderiv C.model (𝓡 3) f (c (t, halfZero))).comp
      (mfderiv halfCollarModel C.model c (t, halfZero)) =
    (mfderiv signedCollarModel (𝓡 3) (regularFibreRestorationSignedTube M φ) (t, 0)).comp
      (mfderiv halfCollarModel signedCollarModel (surgeryHalfSignedCoordinate σ)
        (t, halfZero)) := by
  have hp : (t, halfZero) ∈ c.source := hc.symm ▸ zero_mem_halfCollarSource t
  have ha : surgeryHalfSignedCoordinate σ (t, halfZero) ∈
      (regularFibreRestorationSignedTube M φ).source := by
    rw [regularFibreRestorationSignedTube_source M φ h3]
    change -1 < σ * halfZero.val 0 ∧ σ * halfZero.val 0 < 1
    change -1 < σ * (0 : ℝ) ∧ σ * (0 : ℝ) < 1
    simp
  have hg : f ∘ c =ᶠ[𝓝 (t, halfZero)]
      regularFibreRestorationSignedTube M φ ∘ surgeryHalfSignedCoordinate σ := by
    filter_upwards [surgeryHalfDomain.isOpen.mem_nhds (zero_mem_halfCollarSource t)] with p hp
    exact he p hp
  have hd := hg.mfderiv_eq (I := halfCollarModel) (I' := 𝓡 3)
  have hzero : surgeryHalfSignedCoordinate σ (t, halfZero) = (t, 0) := by
    change (t, σ * (0 : ℝ)) = (t, 0)
    simp
  have hl := mfderiv_comp (t, halfZero) (hf.mdifferentiableAt (by simp))
    (c.mdifferentiableAt (by simp) hp)
  have hr := mfderiv_comp (t, halfZero)
    ((regularFibreRestorationSignedTube M φ).mdifferentiableAt (by simp) ha)
    ((surgeryHalfSignedCoordinate_contMDiff σ).mdifferentiableAt (by simp))
  rw [hl, hr] at hd
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L => L v) hd
  change mfderiv C.model (𝓡 3) f (c (t, halfZero))
      (mfderiv halfCollarModel C.model c (t, halfZero) v) =
    mfderiv signedCollarModel (𝓡 3) (regularFibreRestorationSignedTube M φ)
      (surgeryHalfSignedCoordinate σ (t, halfZero))
      (mfderiv halfCollarModel signedCollarModel (surgeryHalfSignedCoordinate σ)
        (t, halfZero) v) at hv
  change mfderiv C.model (𝓡 3) f (c (t, halfZero))
      (mfderiv halfCollarModel C.model c (t, halfZero) v) =
    mfderiv signedCollarModel (𝓡 3) (regularFibreRestorationSignedTube M φ) (t, 0)
      (mfderiv halfCollarModel signedCollarModel (surgeryHalfSignedCoordinate σ)
        (t, halfZero) v)
  have hz : mfderiv signedCollarModel (𝓡 3) (regularFibreRestorationSignedTube M φ)
      (surgeryHalfSignedCoordinate σ (t, halfZero)) =
    mfderiv signedCollarModel (𝓡 3) (regularFibreRestorationSignedTube M φ) (t, 0) :=
    _root_.mfderiv_congr_point (I := signedCollarModel) (I' := 𝓡 3)
      (f := regularFibreRestorationSignedTube M φ) hzero
  exact hv.trans (congrArg (fun E => E
    (mfderiv halfCollarModel signedCollarModel (surgeryHalfSignedCoordinate σ)
      (t, halfZero) v)) hz)

private theorem markedNative_reversing
    (K S : CompactCarrier.{u}) (hK : K.kind = .withBoundary) (hS : S.kind = .withBoundary)
    [Nonempty K.Carrier] [Nonempty S.Carrier]
    (l : PartialDiffeomorph halfCollarModel K.model
      (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
    (r : PartialDiffeomorph halfCollarModel S.model
      (Torus × EuclideanHalfSpace 1) S.Carrier ∞)
    (hl : l.source = halfCollarSource) (hr : r.source = halfCollarSource)
    (hrev : ReversesBoundaryOrientation (withBoundarySum K S hK hS)
      (l.trans (withBoundarySumLeft K S hK hS))
      (r.trans (withBoundarySumRight K S hK hS))) (t : Torus) :
    Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv l (hl.symm ▸ zero_mem_halfCollarSource t)).symm
      (K.orientation.orientation (l (t, halfZero))) =
    -Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv r (hr.symm ▸ zero_mem_halfCollarSource t)).symm
      (S.orientation.orientation (r (t, halfZero))) := by
  let p := (t, halfZero)
  obtain ⟨L, R, hL, hR, hO⟩ := hrev t
  obtain ⟨A, hA, hAo⟩ := withBoundarySumLeft_positive K S hK hS (l p)
  obtain ⟨B, hB, hBo⟩ := withBoundarySumRight_positive K S hK hS (r p)
  let L0 : TangentSpace halfCollarModel p ≃ₗ[ℝ] TangentSpace K.model (l p) :=
    carrierSurgeryPatchTangentEquiv l (hl.symm ▸ zero_mem_halfCollarSource t)
  let R0 : TangentSpace halfCollarModel p ≃ₗ[ℝ] TangentSpace S.model (r p) :=
    carrierSurgeryPatchTangentEquiv r (hr.symm ▸ zero_mem_halfCollarSource t)
  have hEL : L = L0.trans A := by
    apply LinearEquiv.ext
    intro v
    have hd := mfderiv_comp_apply p
      ((withBoundarySumLeft K S hK hS).mdifferentiableAt (by simp)
        ((withBoundarySumLeft_source K S hK hS).symm ▸ mem_univ _))
      (l.mdifferentiableAt (by simp) (hl.symm ▸ zero_mem_halfCollarSource t)) v
    exact (hL v).trans (hd.trans (hA (L0 v)).symm)
  have hER : R = R0.trans B := by
    apply LinearEquiv.ext
    intro v
    have hd := mfderiv_comp_apply p
      ((withBoundarySumRight K S hK hS).mdifferentiableAt (by simp)
        ((withBoundarySumRight_source K S hK hS).symm ▸ mem_univ _))
      (r.mdifferentiableAt (by simp) (hr.symm ▸ zero_mem_halfCollarSource t)) v
    exact (hR v).trans (hd.trans (hB (R0 v)).symm)
  have hOL := markedOrientation_comp_inverse L0 A _ _ hAo
  have hOR := markedOrientation_comp_inverse R0 B _ _ hBo
  have heL := congrArg (fun E : TangentSpace halfCollarModel p ≃ₗ[ℝ]
      TangentSpace (withBoundarySum K S hK hS).model
        ((l.trans (withBoundarySumLeft K S hK hS)) p) =>
      Orientation.map (Fin 3) E.symm
        ((withBoundarySum K S hK hS).orientation.orientation
          ((l.trans (withBoundarySumLeft K S hK hS)) p))) hEL
  have heR := congrArg (fun E : TangentSpace halfCollarModel p ≃ₗ[ℝ]
      TangentSpace (withBoundarySum K S hK hS).model
        ((r.trans (withBoundarySumRight K S hK hS)) p) =>
      Orientation.map (Fin 3) E.symm
        ((withBoundarySum K S hK hS).orientation.orientation
          ((r.trans (withBoundarySumRight K S hK hS)) p))) hER
  exact hOL.symm.trans (heL.symm.trans (hO.trans
    ((congrArg Neg.neg heR).trans (congrArg Neg.neg hOR))))


theorem markedRestorationFill_positive
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (PlaneLift.{u} × Circle) M.Carrier ∞)
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    (K S : CompactCarrier.{u})
    (hK : K.kind = .withBoundary) (hS : S.kind = .withBoundary)
    [Nonempty K.Carrier] [Nonempty S.Carrier]
    (ι : K.Carrier → M.Carrier) (Γ : BoundaryTori K 1)
    (hι : ContMDiff K.model (𝓡 3) ∞ ι)
    (hΓ : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
      ι (Γ.collar 0 p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
    (hO : ∀ x, ∃ H : TangentSpace K.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι x),
      H.toContinuousLinearMap = mfderiv K.model (𝓡 3) ι x ∧
      Orientation.map (Fin 3) H.toLinearEquiv (K.orientation.orientation x) =
        M.orientation.orientation (ι x))
    (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier)
    (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (ε : Bool)
    (hrev : ReversesBoundaryOrientation (withBoundarySum K S hK hS)
      (boundaryPortLeftCollar K S hK hS Γ)
      (fun p => boundaryPortRightCollar K S hK hS (markedSolidBoundary S g ψ) 0
        (markedRestorationMatching ψ ε p.1, p.2))) :
    ∀ y, ∃ H : TangentSpace S.model y ≃L[ℝ]
        TangentSpace (𝓡 3) (markedRestorationFill M φ S g ε y),
      H.toContinuousLinearMap = mfderiv S.model (𝓡 3) (markedRestorationFill M φ S g ε) y ∧
      Orientation.map (Fin 3) H.toLinearEquiv (S.orientation.orientation y) =
        M.orientation.orientation (markedRestorationFill M φ S g ε y) := by
  let gε := markedRestorationSolidMap S g ε
  let c : PartialDiffeomorph halfCollarModel S.model
      (Torus × EuclideanHalfSpace 1) S.Carrier ∞ :=
    (solidCollar.{u} 1).trans gε.toPartialDiffeomorph
  have hc : c.source = halfCollarSource := by
    ext p
    change (p ∈ halfCollarSource ∧ solidCollar.{u} 1 p ∈ univ) ↔ p ∈ halfCollarSource
    simp
  have he : (fun p => boundaryPortRightCollar K S hK hS (markedSolidBoundary S g ψ) 0
      (markedRestorationMatching ψ ε p.1, p.2)) =
      (c.trans (withBoundarySumRight K S hK hS) :
        Torus × EuclideanHalfSpace 1 → (withBoundarySum K S hK hS).Carrier) := by
    funext p
    change (withBoundarySumRight K S hK hS)
      ((markedSolidBoundary S g ψ).collar 0 (markedRestorationMatching ψ ε p.1, p.2)) =
      (withBoundarySumRight K S hK hS) (gε (solidCollar.{u} 1 p))
    rw [← markedRestorationSolidMap_collar S g ψ ε p]
  have hrev' : ReversesBoundaryOrientation (withBoundarySum K S hK hS)
      ((Γ.collar 0).trans (withBoundarySumLeft K S hK hS))
      (c.trans (withBoundarySumRight K S hK hS)) := by
    rw [he] at hrev
    exact hrev
  let F := markedRestorationFill M φ S g ε
  have hFs : ContMDiff S.model (𝓡 3) ∞ F := markedRestorationFill_smooth M φ h3 S g ε
  have hFb : ∀ x, Bijective (mfderiv S.model (𝓡 3) F x) :=
    markedRestorationFill_mfderiv_bijective M φ h3 S g ε
  obtain ⟨OF, hOF⟩ := exists_manifoldOrientation_pullback S.model (𝓡 3) (by simp)
    F hFs hFb M.orientation
  let p : Torus × EuclideanHalfSpace 1 := (torusBase, halfZero)
  let L : TangentSpace halfCollarModel p ≃ₗ[ℝ] TangentSpace K.model (Γ.collar 0 p) :=
    carrierSurgeryPatchTangentEquiv (Γ.collar 0)
      ((Γ.source_eq 0).symm ▸ zero_mem_halfCollarSource torusBase)
  let R : TangentSpace halfCollarModel p ≃ₗ[ℝ] TangentSpace S.model (c p) :=
    carrierSurgeryPatchTangentEquiv c (hc.symm ▸ zero_mem_halfCollarSource torusBase)
  obtain ⟨H, hH, hHO⟩ := hO (Γ.collar 0 p)
  let J := differentialEquivOfBijective S.model (𝓡 3) F hFb (c p)
  have hp : (torusBase, (0 : ℝ)) ∈ (regularFibreRestorationSignedTube M φ).source := by
    rw [regularFibreRestorationSignedTube_source M φ h3]
    change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
    norm_num
  let A : TangentSpace signedCollarModel (torusBase, (0 : ℝ)) ≃ₗ[ℝ]
      TangentSpace (𝓡 3) (ι (Γ.collar 0 p)) :=
    carrierSurgeryPatchTangentEquiv (regularFibreRestorationSignedTube M φ) hp
  let B := surgeryHalfSignedTangent 1 (by norm_num) p
  have hFcollar : ∀ q ∈ halfCollarSource,
      F (c q) = regularFibreRestorationSignedTube M φ (surgeryHalfSignedCoordinate (-1) q) := by
    intro q hq
    change regularFibreRestorationFill M φ (gε.symm (gε (solidCollar.{u} 1 q))) = _
    rw [gε.symm_apply_apply, regularFibreRestorationFill_collar M φ hq,
      regularFibreRestorationSignedTube_apply]
    congr 2
    apply ULift.ext
    change (1 - q.2.val 0 / 2) • (q.1.1 : ℂ) =
      (1 + (-1 * q.2.val 0) / 2) • (q.1.1 : ℂ)
    congr 1
    ring
  have hKcollar : ∀ q ∈ halfCollarSource,
      ι (Γ.collar 0 q) =
        regularFibreRestorationSignedTube M φ (surgeryHalfSignedCoordinate 1 q) := by
    intro q hq
    rw [hΓ q hq, regularFibreRestorationSignedTube_apply]
    change φ (ULift.up ((1 + q.2.val 0 / 2) • (q.1.1 : ℂ)), q.1.2) =
      φ (ULift.up ((1 + (1 * q.2.val 0) / 2) • (q.1.1 : ℂ)), q.1.2)
    rw [one_mul]
  have hL : L.trans H.toLinearEquiv = B.trans A := by
    have hd := markedCollar_derivative M φ h3 (Γ.collar 0) (Γ.source_eq 0) ι
      hι 1 hKcollar torusBase
    apply LinearEquiv.ext
    intro v
    change H (L v) = A (B v)
    have hv := congrArg (fun E => E v) hd
    change H.toContinuousLinearMap (L v) = A (B v)
    rw [hH]
    exact hv
  have hR : R.trans J.toLinearEquiv =
      (B.trans surgerySignedNormalReflection).trans A := by
    have hd := markedCollar_derivative M φ h3 c hc F hFs (-1) hFcollar torusBase
    have heR : R.trans J.toLinearEquiv =
        (surgeryHalfSignedTangent (-1) (by norm_num) p).trans A := by
      apply LinearEquiv.ext
      intro v
      exact congrArg (fun E => E v) hd
    exact heR.trans (congrArg (fun E => E.trans A) (surgeryHalfSignedTangent_negative p))
  have hpoint : F (c p) = ι (Γ.collar 0 p) := by
    rw [hFcollar p (zero_mem_halfCollarSource torusBase),
      hKcollar p (zero_mem_halfCollarSource torusBase)]
    apply congrArg (regularFibreRestorationSignedTube M φ)
    change (torusBase, (-1 : ℝ) * 0) = (torusBase, (1 : ℝ) * 0)
    simp
  have hJO : Orientation.map (Fin 3) J.toLinearEquiv (OF.orientation (c p)) =
      M.orientation.orientation (ι (Γ.collar 0 p)) := by
    have ho := hOF (c p)
    have hpO : M.orientation.orientation (F (c p)) =
        M.orientation.orientation (ι (Γ.collar 0 p)) :=
      markedOrientation_point M (F (c p)) (ι (Γ.collar 0 p)) hpoint
    exact ho.trans hpO
  have hleft := markedOrientation_comp_inverse L H.toLinearEquiv
    (K.orientation.orientation (Γ.collar 0 p)) (M.orientation.orientation (ι (Γ.collar 0 p))) hHO
  have hright := markedOrientation_comp_inverse R J.toLinearEquiv
    (OF.orientation (c p)) (M.orientation.orientation (ι (Γ.collar 0 p))) hJO
  have hleft' : Orientation.map (Fin 3) (B.trans A).symm
      (M.orientation.orientation (ι (Γ.collar 0 p))) =
      Orientation.map (Fin 3) L.symm (K.orientation.orientation (Γ.collar 0 p)) := by
    exact (congrArg (fun E : TangentSpace halfCollarModel p ≃ₗ[ℝ]
        TangentSpace (𝓡 3) (ι (Γ.collar 0 p)) =>
      Orientation.map (Fin 3) E.symm (M.orientation.orientation (ι (Γ.collar 0 p))))
      hL).symm.trans hleft
  have hright' : Orientation.map (Fin 3) ((B.trans surgerySignedNormalReflection).trans A).symm
      (M.orientation.orientation (ι (Γ.collar 0 p))) =
      Orientation.map (Fin 3) R.symm (OF.orientation (c p)) := by
    exact (congrArg (fun E : TangentSpace halfCollarModel p ≃ₗ[ℝ]
        TangentSpace (𝓡 3) (ι (Γ.collar 0 p)) =>
      Orientation.map (Fin 3) E.symm (M.orientation.orientation (ι (Γ.collar 0 p))))
      hR).symm.trans hright
  have hn := markedNative_reversing K S hK hS (Γ.collar 0) c (Γ.source_eq 0) hc
    hrev' torusBase
  change Orientation.map (Fin 3) L.symm (K.orientation.orientation (Γ.collar 0 p)) =
    -Orientation.map (Fin 3) R.symm (S.orientation.orientation (c p)) at hn
  have hsamePoint : OF.orientation (c p) = S.orientation.orientation (c p) := by
    apply (Orientation.map (Fin 3) R.symm).injective
    have hh := markedSigned_inverse_negative B A (M.orientation.orientation (ι (Γ.collar 0 p)))
    have heO := hright'.symm.trans (hh.trans (congrArg Neg.neg hleft'))
    exact heO.trans (by simpa only [neg_neg] using congrArg Neg.neg hn)
  let : ConnectedSpace S.Carrier := g.surjective.connectedSpace g.continuous
  have hsame : OF = S.orientation := OF.eq_of_eq_at S.orientation (c p) hsamePoint
  intro y
  refine ⟨differentialEquivOfBijective S.model (𝓡 3) F hFb y, rfl, ?_⟩
  have hy := hOF y
  rw [hsame] at hy
  exact hy

end GC.GraphManifold
