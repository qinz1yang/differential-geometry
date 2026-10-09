import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreMarkedRestoration
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgerySeamOrientation

/-!
A genuine positive normal collar germ preserves the already chosen physical boundary reversal.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open GC.Endpoint.CompactCarrier GC.GraphManifold.TorusPairing
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem germScale_derivative {ρ : ℝ} (hρ : 0 < ρ)
    (x : EuclideanHalfSpace 1) (v : TangentSpace (𝓡∂ 1) x) :
    mfderiv (𝓡∂ 1) (𝓡∂ 1) (halfSpaceScale hρ) x v = ρ • v := by
  let A := PiLp.equivOfUnique 2 ℝ (fun k : Fin 1 => ℝ)
  apply A.injective
  have h := (hasMFDerivAt_halfSpaceOneCoordinate x).const_smul ρ
  have he : (fun s : EuclideanHalfSpace 1 => ρ * s.val 0) =
      (fun s : EuclideanHalfSpace 1 => s.val 0) ∘ halfSpaceScale hρ := by
    funext s
    exact (halfSpaceScale_coord hρ s).symm
  change HasMFDerivAt (𝓡∂ 1) 𝓘(ℝ)
    (fun s : EuclideanHalfSpace 1 => ρ * s.val 0) x (ρ • A.toContinuousLinearMap) at h
  rw [he] at h
  have hc := mfderiv_comp_apply x
    (hasMFDerivAt_halfSpaceOneCoordinate (halfSpaceScale hρ x)).mdifferentiableAt
    ((halfSpaceScale hρ).contMDiff.mdifferentiableAt (by simp)) v
  have hv := congrArg (fun L => L v) h.mfderiv
  change A (mfderiv (𝓡∂ 1) (𝓡∂ 1) (halfSpaceScale hρ) x v) = A (ρ • v)
  have hc' : mfderiv (𝓡∂ 1) 𝓘(ℝ)
      ((fun s : EuclideanHalfSpace 1 => s.val 0) ∘ halfSpaceScale hρ) x v =
      A (mfderiv (𝓡∂ 1) (𝓡∂ 1) (halfSpaceScale hρ) x v) := by
    exact hc.trans (congrArg
      (fun L => L (mfderiv (𝓡∂ 1) (𝓡∂ 1) (halfSpaceScale hρ) x v))
      (hasMFDerivAt_halfSpaceOneCoordinate (halfSpaceScale hρ x)).mfderiv)
  exact hc'.symm.trans (hv.trans (A.map_smul ρ v).symm)

private theorem germShrink_positive {ρ : ℝ} (hρ : 0 < ρ) (t : Torus)
    (O : Orientation ℝ (TangentSpace halfCollarModel (t, halfZero)) (Fin 3)) :
    Orientation.map (Fin 3)
      ((halfShrink (IX := torusModel) hρ).mfderivToContinuousLinearEquiv
        (by simp) (t, halfZero)).toLinearEquiv O = O := by
  let L : TangentSpace halfCollarModel (t, halfZero) ≃ₗ[ℝ]
      TangentSpace halfCollarModel (t, halfZero) :=
    ((halfShrink (IX := torusModel) hρ).mfderivToContinuousLinearEquiv
      (by simp) (t, halfZero)).toLinearEquiv
  have he : L.toLinearMap =
      LinearMap.prodMap
        (LinearMap.id : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) →ₗ[ℝ] _)
        (ρ • LinearMap.id : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] _) := by
    ext v
    change mfderiv halfCollarModel halfCollarModel
      (Prod.map id (halfSpaceScale hρ)) (t, halfZero) v = _
    rw [mfderiv_prodMap mdifferentiableAt_id
      ((halfSpaceScale hρ).contMDiff.mdifferentiableAt (by simp)), mfderiv_id]
    change (v.1, mfderiv (𝓡∂ 1) (𝓡∂ 1) (halfSpaceScale hρ) halfZero v.2) = _
    change (v.1, mfderiv (𝓡∂ 1) (𝓡∂ 1) (halfSpaceScale hρ) halfZero v.2) =
      (v.1, ρ • v.2)
    exact Prod.ext rfl (germScale_derivative hρ halfZero v.2)
  apply (Orientation.map_eq_iff_det_pos O L (by
    change 3 = Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1))
    simp)).mpr
  erw [he, LinearMap.det_prodMap, LinearMap.det_smul]
  simpa using hρ

private theorem germOrientation_point (C : CompactCarrier.{u})
    (x y : C.Carrier) (hxy : x = y) :
    C.orientation.orientation x = C.orientation.orientation y := by
  subst y
  rfl

private theorem germRight_transfer (C : CompactCarrier.{u})
    (l r : Torus × EuclideanHalfSpace 1 → C.Carrier)
    (R : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (hR : R.source = halfCollarSource) {ρ : ℝ} (hρ : 0 < ρ)
    (hgerm : ∀ t : Torus, r =ᶠ[𝓝 (t, halfZero)]
      R ∘ halfShrink (IX := torusModel) hρ)
    (hrev : ReversesBoundaryOrientation C l r) : ReversesBoundaryOrientation C l R := by
  intro t
  obtain ⟨A, B, hA, hB, hO⟩ := hrev t
  let N : TangentSpace halfCollarModel (t, halfZero) ≃ₗ[ℝ]
      TangentSpace halfCollarModel (t, halfZero) :=
    ((halfShrink (IX := torusModel) hρ).mfderivToContinuousLinearEquiv
      (by simp) (t, halfZero)).toLinearEquiv
  let B' : TangentSpace halfCollarModel (t, halfZero) ≃ₗ[ℝ]
      TangentSpace C.model (R (t, halfZero)) :=
    carrierSurgeryPatchTangentEquiv R (hR.symm ▸ zero_mem_halfCollarSource t)
  have hfix : halfShrink (IX := torusModel) hρ (t, halfZero) = (t, halfZero) := by
    exact Prod.ext rfl (halfSpaceScale_halfZero hρ)
  have hzero : r (t, halfZero) = R (t, halfZero) :=
    (hgerm t).eq_of_nhds.trans (congrArg R hfix)
  have hder : B = N.trans B' := by
    apply LinearEquiv.ext
    intro v
    have hd := congrArg (fun D => D v) ((hgerm t).mfderiv_eq (I := halfCollarModel) (I' := C.model))
    have hc := mfderiv_comp_apply (t, halfZero)
      (R.mdifferentiableAt (by simp) (by rw [hfix]; exact hR.symm ▸ zero_mem_halfCollarSource t))
      ((halfShrink (IX := torusModel) hρ).contMDiff.mdifferentiableAt (by simp)) v
    change mfderiv halfCollarModel C.model r (t, halfZero) v =
      mfderiv halfCollarModel C.model
        (R ∘ halfShrink (IX := torusModel) hρ) (t, halfZero) v at hd
    have hc' : mfderiv halfCollarModel C.model
        (R ∘ halfShrink (IX := torusModel) hρ) (t, halfZero) v = B' (N v) := by
      exact hc.trans (congrArg (fun D => D (N v))
        (_root_.mfderiv_congr_point (I := halfCollarModel) (I' := C.model) (f := R) hfix))
    exact (hB v).trans (hd.trans hc')
  let o := Orientation.map (Fin 3) B.symm (C.orientation.orientation (r (t, halfZero)))
  have hmap : Orientation.map (Fin 3) B' o = C.orientation.orientation (R (t, halfZero)) := by
    have hn := germShrink_positive hρ t o
    change Orientation.map (Fin 3) N o = o at hn
    have hb : Orientation.map (Fin 3) B o = C.orientation.orientation (r (t, halfZero)) :=
      (Orientation.map (Fin 3) B).apply_symm_apply _
    have ht := DifferentialGeometry.orientation_map_trans N B' o
    have he : Orientation.map (Fin 3) B o =
        Orientation.map (Fin 3) B' (Orientation.map (Fin 3) N o) :=
      (congrArg (fun L : TangentSpace halfCollarModel (t, halfZero) ≃ₗ[ℝ]
        TangentSpace C.model (R (t, halfZero)) => Orientation.map (Fin 3) L o) hder).trans ht
    exact (congrArg (Orientation.map (Fin 3) B') hn).symm.trans
      (he.symm.trans (hb.trans (germOrientation_point C _ _ hzero)))
  have ho : o = Orientation.map (Fin 3) B'.symm
      (C.orientation.orientation (R (t, halfZero))) := by
    exact ((Orientation.map (Fin 3) B').symm_apply_apply o).symm.trans
      (congrArg (Orientation.map (Fin 3) B'.symm) hmap)
  refine ⟨A, B', hA, fun v => rfl, ?_⟩
  exact hO.trans (congrArg Neg.neg ho)

private def germMatched {C : CompactCarrier.{u}}
    (r : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞ :=
  (f.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans r

private theorem germMatched_source {C : CompactCarrier.{u}}
    (r : PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞) (hr : r.source = halfCollarSource)
    (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) :
    (germMatched r f).source = halfCollarSource := by
  ext p
  change (p ∈ univ ∧ (f p.1, p.2) ∈ r.source) ↔ p ∈ halfCollarSource
  rw [hr]
  simp only [mem_univ, true_and]
  rfl

theorem markedCollarGermOrientation
    (K S : CompactCarrier.{u})
    (hK : K.kind = .withBoundary) (hS : S.kind = .withBoundary)
    [Nonempty K.Carrier] [Nonempty S.Carrier]
    (Γ : BoundaryTori K 1) (E : BoundaryTori S 1)
    (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier)
    (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ)
    (hgerm : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource → p.2.val 0 < δ →
      g (solidCollar.{u} 1 (p.1, halfSpaceScale hρ p.2)) = E.collar 0 (ψ p.1, p.2))
    (ε : Bool)
    (hrev : ReversesBoundaryOrientation (withBoundarySum K S hK hS)
      (boundaryPortLeftCollar K S hK hS Γ)
      (fun p => boundaryPortRightCollar K S hK hS E 0
        (markedRestorationMatching ψ ε p.1, p.2))) :
    ReversesBoundaryOrientation (withBoundarySum K S hK hS)
      (boundaryPortLeftCollar K S hK hS Γ)
      (fun p => boundaryPortRightCollar K S hK hS (markedSolidBoundary S g ψ) 0
        (markedRestorationMatching ψ ε p.1, p.2)) := by
  let f := markedRestorationMatching ψ ε
  let R := germMatched (boundaryPortRightCollar K S hK hS (markedSolidBoundary S g ψ) 0) f
  have hR : R.source = halfCollarSource := germMatched_source _
    (boundaryPortRightCollar_source K S hK hS (markedSolidBoundary S g ψ) 0) f
  apply germRight_transfer (withBoundarySum K S hK hS)
    (boundaryPortLeftCollar K S hK hS Γ)
    (fun p => boundaryPortRightCollar K S hK hS E 0 (f p.1, p.2)) R hR hρ
  · intro t
    have hd : {p : Torus × EuclideanHalfSpace 1 | p.2.val 0 < δ} ∈ 𝓝 (t, halfZero) :=
      (isOpen_lt (contMDiff_halfSpaceOneCoordinate.continuous.comp continuous_snd)
        continuous_const).mem_nhds hδ
    filter_upwards [ConeFilling.isOpen_halfCollarSource.mem_nhds
      (zero_mem_halfCollarSource t), hd] with p hp hpδ
    change boundaryPortRightCollar K S hK hS E 0 (f p.1, p.2) =
      boundaryPortRightCollar K S hK hS (markedSolidBoundary S g ψ) 0
        (f p.1, halfSpaceScale hρ p.2)
    rw [boundaryPortRightCollar_apply, boundaryPortRightCollar_apply,
      markedSolidBoundary_collar]
    apply congrArg Sum.inr
    have hg := hgerm (ψ.symm (f p.1), p.2) hp hpδ
    rw [ψ.apply_symm_apply] at hg
    exact hg.symm
  · exact hrev

end GC.GraphManifold
