import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SolidTorus
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Tangent

/-!
# Gluing two solid tori into the three-sphere

The disjoint union of two copies of the standard solid torus maps to the standard three-sphere by
the inclusion on the first copy and by the coordinate swap `(z₁, z₂) ↦ (z₂, z₁)` on the second.
Both maps are smooth embeddings with images `{‖z₁‖ ≤ ‖z₂‖}` and `{‖z₂‖ ≤ ‖z₁‖}`. On the boundary
tori they agree exactly after swapping the two circle factors, and the induced map from the
quotient by this boundary gluing is a homeomorphism onto the three-sphere. We also equip the
disjoint union with the orientation pulled back from the sphere.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold
universe u

abbrev CliffordCut : Type u := solidTorusSet.{u} ⊕ solidTorusSet.{u}

def cliffordFold : CliffordCut.{u} → SphereCarrier.{u} :=
  Sum.elim Subtype.val (fun p => sphereSwap p.val)

@[simp] theorem cliffordFold_inl (p : solidTorusSet.{u}) :
    cliffordFold (Sum.inl p) = p.val := rfl

@[simp] theorem cliffordFold_inr (p : solidTorusSet.{u}) :
    cliffordFold (Sum.inr p) = sphereSwap p.val := rfl

theorem contMDiff_cliffordFold : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ cliffordFold.{u} :=
  ContMDiff.sumElim contMDiff_solidTorus_val (sphereSwap.contMDiff.comp contMDiff_solidTorus_val)

theorem contMDiff_sphereSwap_solidTorus :
    ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (fun p : solidTorusSet.{u} => sphereSwap p.val) :=
  sphereSwap.contMDiff.comp contMDiff_solidTorus_val

theorem injective_sphereSwap_solidTorus :
    Injective (fun p : solidTorusSet.{u} => sphereSwap p.val) :=
  fun _ _ h => Subtype.val_injective (sphereSwap.injective h)

theorem range_solidTorus_val :
    range (Subtype.val : solidTorusSet.{u} → SphereCarrier.{u}) = {p | cliffordHeight p ≤ 0} :=
  Subtype.range_coe

theorem range_sphereSwap_solidTorus :
    range (fun p : solidTorusSet.{u} => sphereSwap p.val) = {p | 0 ≤ cliffordHeight p} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    change 0 ≤ cliffordHeight (sphereSwap q.val)
    rw [cliffordHeight_sphereSwap]
    exact neg_nonneg.mpr q.2
  · intro hp
    have hp' : 0 ≤ cliffordHeight p := hp
    refine ⟨⟨sphereSwap p, ?_⟩, sphereSwap_sphereSwap p⟩
    change cliffordHeight (sphereSwap p) ≤ 0
    rw [cliffordHeight_sphereSwap]
    exact neg_nonpos.mpr hp'

theorem mfderiv_solidTorus_val_bijective (p : solidTorusSet.{u}) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : solidTorusSet.{u} → SphereCarrier.{u}) p) :=
  solidTorusAtlas.mfderiv_subtypeVal_bijective p

theorem mfderiv_cliffordFold_bijective (x : CliffordCut.{u}) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3) cliffordFold x) := by
  have hf : MDifferentiableAt (𝓡∂ 3) (𝓡 3) cliffordFold x :=
    contMDiff_cliffordFold.mdifferentiableAt (by simp)
  rcases x with a | b
  · have hi : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3)
        (Sum.inl : solidTorusSet.{u} → CliffordCut.{u}) a :=
      (ContMDiff.inl : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
        (Sum.inl : solidTorusSet.{u} → CliffordCut.{u})).mdifferentiableAt (by simp)
    have h := mfderiv_comp a hf hi
    rw [hasMFDerivAt_inl.mfderiv] at h
    have hb : Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
        (cliffordFold ∘ (Sum.inl : solidTorusSet.{u} → CliffordCut.{u})) a) :=
      mfderiv_solidTorus_val_bijective a
    rw [h] at hb
    exact hb
  · have hi : MDifferentiableAt (𝓡∂ 3) (𝓡∂ 3)
        (Sum.inr : solidTorusSet.{u} → CliffordCut.{u}) b :=
      (ContMDiff.inr : ContMDiff (𝓡∂ 3) (𝓡∂ 3) ∞
        (Sum.inr : solidTorusSet.{u} → CliffordCut.{u})).mdifferentiableAt (by simp)
    have h := mfderiv_comp b hf hi
    rw [hasMFDerivAt_inr.mfderiv] at h
    have h2 := mfderiv_comp b
      (sphereSwap.contMDiff.mdifferentiableAt (by simp) : MDifferentiableAt (𝓡 3) (𝓡 3)
        sphereSwap b.val)
      (contMDiff_solidTorus_val.mdifferentiableAt (by simp) : MDifferentiableAt (𝓡∂ 3) (𝓡 3)
        Subtype.val b)
    have hswap : Bijective (mfderiv (𝓡 3) (𝓡 3) sphereSwap b.val) := by
      rw [← sphereSwap.mfderivToContinuousLinearEquiv_coe (by simp)]
      exact (sphereSwap.mfderivToContinuousLinearEquiv (by simp) b.val).bijective
    have hb : Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (sphereSwap ∘ Subtype.val) b) := by
      rw [h2, ContinuousLinearMap.coe_comp]
      exact hswap.comp (mfderiv_solidTorus_val_bijective b)
    change Bijective (mfderiv (𝓡∂ 3) (𝓡 3)
      (cliffordFold ∘ (Sum.inr : solidTorusSet.{u} → CliffordCut.{u})) b) at hb
    rw [h] at hb
    exact hb

def cliffordCutOrientation : ManifoldOrientation (𝓡∂ 3) CliffordCut.{u} 3 :=
  Manifold.manifoldOrientationPullback (𝓡∂ 3) (𝓡 3) finrank_euclideanSpace_fin cliffordFold
    contMDiff_cliffordFold mfderiv_cliffordFold_bijective standardThreeSphereLift.orientation

theorem orientation_map_cliffordCutOrientation (x : CliffordCut.{u}) :
    Orientation.map (Fin 3) (Manifold.differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) cliffordFold
      mfderiv_cliffordFold_bijective x).toLinearEquiv (cliffordCutOrientation.orientation x) =
      standardThreeSphereLift.orientation.orientation (cliffordFold x) :=
  Manifold.orientation_map_manifoldOrientationPullback (𝓡∂ 3) (𝓡 3) finrank_euclideanSpace_fin
    cliffordFold contMDiff_cliffordFold mfderiv_cliffordFold_bijective
    standardThreeSphereLift.orientation x

abbrev cliffordCutCarrier : CompactCarrier.{u} where
  kind := .withBoundary
  Carrier := CliffordCut.{u}
  charts := (inferInstance : ChartedSpace (EuclideanHalfSpace 3) CliffordCut.{u})
  smooth := (inferInstance : IsManifold (𝓡∂ 3) ∞ CliffordCut.{u})
  secondCountable := by
    have := secondCountableTopology_sphereCarrier.{u}
    infer_instance
  orientation := cliffordCutOrientation

def cliffordTorusPoint (t : Torus) : solidTorusSet.{u} := solidTorusCollar (t, halfZero)

theorem cliffordTorusPoint_val (t : Torus) :
    (cliffordTorusPoint.{u} t).val = cliffordSeam (t, 0) := by
  change cliffordSeamMap (t, -halfZero.val 0) = cliffordSeamMap (t, 0)
  rw [show halfZero.val 0 = 0 from rfl, neg_zero]

theorem halfZero_mem_halfCollarSource (t : Torus) : (t, halfZero) ∈ halfCollarSource := by
  change (0 : ℝ) < 1
  norm_num

theorem continuous_cliffordTorusPoint : Continuous cliffordTorusPoint.{u} := by
  have hs : ContMDiff torusModel (𝓡∂ 3) ∞
      (fun t : Torus => solidTorusCollar.{u} (t, halfZero)) :=
    solidTorusCollar.contMDiffOn.comp_contMDiff (contMDiff_id.prodMk contMDiff_const)
      halfZero_mem_halfCollarSource
  exact hs.continuous

theorem cliffordTorusPoint_injective : Injective cliffordTorusPoint.{u} := by
  intro t s h
  exact congrArg Prod.fst (solidTorusCollar.{u}.toOpenPartialHomeomorph.injOn
    (halfZero_mem_halfCollarSource t) (halfZero_mem_halfCollarSource s) h)

theorem cliffordHeight_cliffordTorusPoint (t : Torus) :
    cliffordHeight (cliffordTorusPoint.{u} t).val = 0 :=
  cliffordHeight_solidTorusCollar_zero t

theorem exists_cliffordTorusPoint_eq {p : solidTorusSet.{u}} (hp : cliffordHeight p.val = 0) :
    ∃ t, cliffordTorusPoint t = p := by
  have hfirst : sphereFirst p.val ≠ 0 := by
    intro h
    have h₁ := norm_sphereFirst_sq_eq p.val
    rw [h, hp, norm_zero] at h₁
    norm_num at h₁
  have hmem : p ∈ solidTorusCollar.{u}.target := hfirst
  refine ⟨(solidTorusCollar.{u}.symm p).1, ?_⟩
  have hinv : solidTorusCollar.{u}.symm p = ((solidTorusCollar.{u}.symm p).1, halfZero) := by
    refine Prod.ext rfl ?_
    change halfPoint (-cliffordHeight p.val) _ = halfZero
    apply Subtype.ext
    ext i
    rw [Subsingleton.elim i 0]
    change -cliffordHeight p.val = 0
    rw [hp, neg_zero]
  rw [cliffordTorusPoint, ← hinv]
  exact solidTorusCollar.right_inv hmem

theorem seamFirst_zero_eq_seamSecond_zero : seamFirst 0 = seamSecond 0 := by
  rw [seamFirst, seamSecond, seamClamp_of_mem (by norm_num) (by norm_num), add_zero, sub_zero]

theorem sphereSwap_cliffordTorusPoint (t : Torus) :
    sphereSwap (cliffordTorusPoint.{u} t).val = (cliffordTorusPoint.{u} t.swap).val := by
  rw [cliffordTorusPoint_val, cliffordTorusPoint_val]
  apply sphere_ext
  · rw [sphereFirst_sphereSwap, cliffordSeam_apply, cliffordSeam_apply,
      sphereSecond_cliffordSeamMap, sphereFirst_cliffordSeamMap, seamFirst_zero_eq_seamSecond_zero]
    rfl
  · rw [sphereSecond_sphereSwap, cliffordSeam_apply, cliffordSeam_apply,
      sphereFirst_cliffordSeamMap, sphereSecond_cliffordSeamMap, seamFirst_zero_eq_seamSecond_zero]
    rfl

def cliffordLeftTorus (t : Torus) : CliffordCut.{u} := Sum.inl (cliffordTorusPoint t)

def cliffordRightTorus (t : Torus) : CliffordCut.{u} := Sum.inr (cliffordTorusPoint t)

theorem isEmbedding_cliffordLeftTorus : _root_.Topology.IsEmbedding cliffordLeftTorus.{u} :=
  ((continuous_inl.comp continuous_cliffordTorusPoint).isClosedEmbedding
    (Sum.inl_injective.comp cliffordTorusPoint_injective)).isEmbedding

theorem isEmbedding_cliffordRightTorus : _root_.Topology.IsEmbedding cliffordRightTorus.{u} :=
  ((continuous_inr.comp continuous_cliffordTorusPoint).isClosedEmbedding
    (Sum.inr_injective.comp cliffordTorusPoint_injective)).isEmbedding

def cliffordMatching : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus :=
  Diffeomorph.prodComm (𝓡 1) (𝓡 1) Circle Circle ∞

theorem cliffordMatching_apply (t : Torus) : cliffordMatching t = t.swap := rfl

theorem cliffordMatching_symm_apply (t : Torus) : cliffordMatching.symm t = t.swap := rfl

def cliffordLeftParam : Torus ≃ₜ range cliffordLeftTorus.{u} :=
  isEmbedding_cliffordLeftTorus.toHomeomorph

def cliffordRightParam : Torus ≃ₜ range cliffordRightTorus.{u} :=
  isEmbedding_cliffordRightTorus.toHomeomorph

def cliffordAttaching : range cliffordLeftTorus.{u} ≃ₜ range cliffordRightTorus.{u} :=
  cliffordLeftParam.symm.trans (cliffordMatching.toHomeomorph.trans cliffordRightParam)

theorem cliffordAttaching_leftParam (t : Torus) :
    cliffordAttaching.{u} (cliffordLeftParam t) = cliffordRightParam (cliffordMatching t) := by
  simp [cliffordAttaching]

theorem cliffordAttaching_val (t : Torus) (h : cliffordLeftTorus.{u} t ∈ range cliffordLeftTorus) :
    (cliffordAttaching ⟨cliffordLeftTorus t, h⟩ : CliffordCut.{u}) = cliffordRightTorus t.swap := by
  have hl : (⟨cliffordLeftTorus t, h⟩ : range cliffordLeftTorus.{u}) = cliffordLeftParam t :=
    Subtype.ext rfl
  rw [hl, cliffordAttaching_leftParam]
  rfl

theorem cliffordAttaching_symm_val (t : Torus)
    (h : cliffordRightTorus.{u} t ∈ range cliffordRightTorus) :
    (cliffordAttaching.symm ⟨cliffordRightTorus t, h⟩ : CliffordCut.{u}) =
      cliffordLeftTorus t.swap := by
  have hr : (⟨cliffordRightTorus t, h⟩ : range cliffordRightTorus.{u}) =
      cliffordAttaching (cliffordLeftParam t.swap) := by
    rw [cliffordAttaching_leftParam, cliffordMatching_apply, Prod.swap_swap]
    exact Subtype.ext rfl
  rw [hr, Homeomorph.symm_apply_apply]
  rfl

def cliffordGluing : BoundaryGluing CliffordCut.{u} (Fin 1) where
  left _ := range cliffordLeftTorus
  right _ := range cliffordRightTorus
  attaching _ := cliffordAttaching
  isClosed_left _ := isClosed_range_of_continuous_of_compactSpace
    (continuous_inl.comp continuous_cliffordTorusPoint)
  isClosed_right _ := isClosed_range_of_continuous_of_compactSpace
    (continuous_inr.comp continuous_cliffordTorusPoint)
  disjoint_left_right _ := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨s, hs⟩
    cases hs
  disjoint_blocks i j h := (h (Subsingleton.elim i j)).elim

theorem cliffordGluing_rel_left_right (t : Torus) :
    cliffordGluing.{u}.rel (cliffordLeftTorus t) (cliffordRightTorus t.swap) := by
  refine Or.inr ⟨0, Or.inl ⟨t, rfl⟩, ?_⟩
  rw [cliffordGluing.flip_of_mem_left ⟨t, rfl⟩]
  exact (cliffordAttaching_val t _).symm

theorem cliffordFold_eq_of_rel {x y : CliffordCut.{u}} (h : cliffordGluing.rel x y) :
    cliffordFold x = cliffordFold y := by
  rcases h with rfl | ⟨i, hx, rfl⟩
  · rfl
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    rcases hx with hx | hx
    · obtain ⟨t, rfl⟩ := id hx
      rw [cliffordGluing.flip_of_mem_left hx]
      have h1 := cliffordAttaching_val t hx
      calc cliffordFold (cliffordLeftTorus t) = cliffordFold (cliffordRightTorus t.swap) := by
            change (cliffordTorusPoint t).val = sphereSwap (cliffordTorusPoint t.swap).val
            rw [sphereSwap_cliffordTorusPoint, Prod.swap_swap]
        _ = _ := congrArg cliffordFold h1.symm
    · obtain ⟨t, rfl⟩ := id hx
      rw [cliffordGluing.flip_of_mem_right hx]
      have h1 := cliffordAttaching_symm_val t hx
      calc cliffordFold (cliffordRightTorus t) = cliffordFold (cliffordLeftTorus t.swap) :=
            sphereSwap_cliffordTorusPoint t
        _ = _ := congrArg cliffordFold h1.symm

theorem cliffordGluing_rel_inl_inr {a b : solidTorusSet.{u}}
    (h : a.val = sphereSwap b.val) : cliffordGluing.rel (Sum.inl a) (Sum.inr b) := by
  have ha : cliffordHeight a.val = 0 := by
    have h₁ : cliffordHeight a.val ≤ 0 := a.2
    have h₂ : cliffordHeight b.val ≤ 0 := b.2
    have h₃ : cliffordHeight a.val = -cliffordHeight b.val := by
      rw [h, cliffordHeight_sphereSwap]
    linarith
  obtain ⟨t, rfl⟩ := exists_cliffordTorusPoint_eq ha
  have hb : b = cliffordTorusPoint t.swap := by
    apply Subtype.ext
    rw [← sphereSwap_cliffordTorusPoint, h, sphereSwap_sphereSwap]
  rw [hb]
  exact cliffordGluing_rel_left_right t

theorem cliffordGluing_rel_of_cliffordFold_eq {x y : CliffordCut.{u}}
    (h : cliffordFold x = cliffordFold y) : cliffordGluing.rel x y := by
  rcases x with a | a <;> rcases y with b | b
  · exact Or.inl (congrArg Sum.inl (Subtype.ext h))
  · exact cliffordGluing_rel_inl_inr h
  · exact cliffordGluing.isEquivalence_rel.symm (cliffordGluing_rel_inl_inr h.symm)
  · exact Or.inl (congrArg Sum.inr (Subtype.ext (sphereSwap.injective h)))

theorem surjective_cliffordFold : Surjective cliffordFold.{u} := by
  intro p
  by_cases hp : cliffordHeight p ≤ 0
  · exact ⟨Sum.inl ⟨p, hp⟩, rfl⟩
  · have hq : cliffordHeight (sphereSwap p) ≤ 0 := by
      rw [cliffordHeight_sphereSwap]
      linarith [not_le.mp hp]
    exact ⟨Sum.inr ⟨sphereSwap p, hq⟩, sphereSwap_sphereSwap p⟩

def cliffordQuotientMap : Quotient cliffordGluing.{u}.setoid → SphereCarrier.{u} :=
  Quotient.lift cliffordFold (fun _ _ h => cliffordFold_eq_of_rel h)

theorem bijective_cliffordQuotientMap : Bijective cliffordQuotientMap.{u} := by
  constructor
  · intro q q' h
    induction q using Quotient.inductionOn with
    | h x =>
      induction q' using Quotient.inductionOn with
      | h y => exact Quotient.sound (cliffordGluing_rel_of_cliffordFold_eq h)
  · intro p
    obtain ⟨x, hx⟩ := surjective_cliffordFold p
    exact ⟨Quotient.mk _ x, hx⟩

def cliffordReconstruction : Quotient cliffordGluing.{u}.setoid ≃ₜ SphereCarrier.{u} :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ bijective_cliffordQuotientMap)
    (continuous_quot_lift _ contMDiff_cliffordFold.continuous)

theorem cliffordReconstruction_mk (x : CliffordCut.{u}) :
    cliffordReconstruction (Quotient.mk _ x) = cliffordFold x := rfl

end GC.GraphManifold
