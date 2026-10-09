import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreExcision
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCapCoordinates
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreRestriction
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.Manifold.HalfSpaceCenteredChart

/-!
An actual regular tube is excised from a compact carrier while retaining all its old boundary.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.GraphManifold.CircleFibration

section Parameter

variable {E F G H H' H'' M P N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace P] [ChartedSpace H' P]
  [TopologicalSpace N] [ChartedSpace H'' N]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {Z : ModelWithCorners ℝ G H''} [IsManifold J ∞ P]

private theorem boundedParameterImmersion
    (e : PartialDiffeomorph I J M P ∞) (f : P → N)
    (hf : ContMDiff J Z ∞ f) (θ : H ≃ₘ⟮I, J⟯ H') (L : E ≃L[ℝ] F)
    (hθ : ∀ y, J (θ y) = L (I y)) {p : M} (hp : p ∈ e.source)
    (h : IsImmersionAtOfComplement PUnit.{1} I Z ∞ (f ∘ e) p) :
    IsImmersionAtOfComplement PUnit.{1} J Z ∞ f (e p) := by
  let α := (e.symm.toOpenPartialHomeomorph.trans h.domChart).trans
    θ.toHomeomorph.toOpenPartialHomeomorph
  have hαsource : α.source = e.target ∩ e.symm ⁻¹' h.domChart.source := by
    simp [α]
  have hαmax : α ∈ IsManifold.maximalAtlas J ∞ P := by
    apply α.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn J J ∞ (θ ∘ h.domChart ∘ e.symm) α.source
      rw [hαsource]
      exact θ.contMDiff.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).comp
          (e.symm.contMDiffOn.mono inter_subset_left) inter_subset_right)
    · change ContMDiffOn J J ∞ (e ∘ h.domChart.symm ∘ θ.symm) α.target
      have ht : α.target = θ.symm ⁻¹'
          (h.domChart.target ∩ h.domChart.symm ⁻¹' e.source) := by simp [α]
      rw [ht]
      exact (e.contMDiffOn.comp
        ((contMDiffOn_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas).mono
          inter_subset_left) inter_subset_right).comp θ.symm.contMDiff.contMDiffOn
            (fun y hy => hy)
  have hleft : e.symm.toPartialEquiv (e.toPartialEquiv p) = p := e.left_inv hp
  have hxα : e p ∈ α.source := by
    rw [hαsource]
    refine ⟨e.map_source hp, ?_⟩
    change e.symm (e p) ∈ h.domChart.source
    rw [hleft]
    exact h.mem_domChart_source
  refine IsImmersionAtOfComplement.mk_of_continuousAt (hf (e p)).continuousAt
    (((L.symm).prodCongr (ContinuousLinearEquiv.refl ℝ PUnit.{1})).trans h.equiv)
    α h.codChart hxα h.mem_codChart_source hαmax h.codChart_mem_maximalAtlas ?_
  intro v hv
  have hy := (α.extend J).map_target hv
  rw [OpenPartialHomeomorph.extend_source, hαsource] at hy
  let y := (α.extend J).symm v
  have hye : y ∈ e.target := hy.1
  have hym : e.symm y ∈ h.domChart.source := hy.2
  have hvα : (α.extend J) y = v := (α.extend J).right_inv hv
  have hvL : (h.domChart.extend I) (e.symm y) = L.symm v := by
    apply L.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact (hθ (h.domChart (e.symm y))).symm.trans hvα
  have hvt : L.symm v ∈ (h.domChart.extend I).target := by
    rw [← hvL]
    exact (h.domChart.extend I).map_source
      (by rwa [OpenPartialHomeomorph.extend_source])
  have hinv : (h.domChart.extend I).symm (L.symm v) = e.symm y := by
    rw [← hvL]
    exact (h.domChart.extend I).left_inv
      (by rwa [OpenPartialHomeomorph.extend_source])
  have hright : e.toPartialEquiv (e.symm.toPartialEquiv y) = y := e.right_inv hye
  have hw := h.writtenInCharts hvt
  change (h.codChart.extend Z) (f (e ((h.domChart.extend I).symm (L.symm v)))) =
    h.equiv (L.symm v, 0) at hw
  rw [hinv, hright] at hw
  exact hw

end Parameter

private abbrev BoundedE3 := EuclideanSpace ℝ (Fin 3)

variable (C : CompactCarrier.{u})
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model
  (PlaneLift.{u} × Circle) C.Carrier ∞)
variable (hφ : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)

private def boundedExcisionSet : Set C.Carrier :=
  (φ '' {z : PlaneLift.{u} × Circle | ‖z.1.down‖ < 1})ᶜ

private def boundedRetainedSet : Set C.Carrier :=
  (φ '' {z : PlaneLift.{u} × Circle | ‖z.1.down‖ ≤ 1})ᶜ

include hφ in
private theorem boundedRetained_open : IsOpen (boundedRetainedSet C φ) := by
  have hc : IsCompact {z : PlaneLift.{u} × Circle | ‖z.1.down‖ ≤ 1} := by
    have hz : IsCompact {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} := by
      have he : {z : PlaneLift.{u} | ‖z.down‖ ≤ 1} =
          ULift.up '' closedBall (0 : ℂ) 1 := by
        ext z
        simp only [mem_ofPred_eq, mem_image, mem_closedBall_zero_iff]
        exact ⟨fun hp => ⟨z.down, hp, ULift.up_down z⟩,
          fun ⟨w, hw, he⟩ => he ▸ hw⟩
      rw [he]
      exact (isCompact_closedBall (0 : ℂ) 1).image contMDiff_planeLift_up.continuous
    simpa only [Set.prod_univ, Set.preimage, Set.mem_ofPred_eq] using
      hz.prod (isCompact_univ : IsCompact (Set.univ : Set Circle))
  have hs : {z : PlaneLift.{u} × Circle | ‖z.1.down‖ ≤ 1} ⊆ φ.source := by
    intro z hz
    apply hφ
    change ‖z.1.down‖ ≤ 3
    change ‖z.1.down‖ ≤ 1 at hz
    linarith
  exact (hc.image_of_continuousOn (φ.contMDiffOn.continuousOn.mono hs)).isClosed.isOpen_compl

private theorem boundedRetained_subset : boundedRetainedSet C φ ⊆ boundedExcisionSet C φ := by
  intro x hx
  rintro ⟨z, hz, he⟩
  apply hx
  refine ⟨z, ?_, he⟩
  change ‖z.1.down‖ ≤ 1
  change ‖z.1.down‖ < 1 at hz
  exact le_of_lt hz

private def boundedExcisionPoint : boundedExcisionSet C φ := by
  let p : PlaneLift.{u} × Circle := (ULift.up (2 : ℂ), 1)
  have hp : p ∈ φ.source := hφ (by change ‖(2 : ℂ)‖ ≤ 3; norm_num)
  refine ⟨φ p, ?_⟩
  rintro ⟨q, hq, he⟩
  have hqs : q ∈ φ.source := hφ (by
    change ‖q.1.down‖ ≤ 3
    change ‖q.1.down‖ < 1 at hq
    linarith)
  have heq := φ.injOn hqs hp he
  change ‖q.1.down‖ < 1 at hq
  rw [heq] at hq
  change ‖(2 : ℂ)‖ < 1 at hq
  norm_num at hq

private def boundedRetainedPatch : OpenPartialHomeomorph C.Carrier (boundedExcisionSet C φ) := by
  classical
  exact {
  toFun x := if hx : x ∈ boundedExcisionSet C φ then ⟨x, hx⟩ else boundedExcisionPoint C φ hφ
  invFun := Subtype.val
  source := boundedRetainedSet C φ
  target := Subtype.val ⁻¹' boundedRetainedSet C φ
  map_source' x hx := by
    change (if hx' : x ∈ boundedExcisionSet C φ then (⟨x, hx'⟩ : boundedExcisionSet C φ)
      else boundedExcisionPoint C φ hφ).val ∈ boundedRetainedSet C φ
    rw [dite_eq_left (boundedRetained_subset C φ hx)]
    exact hx
  map_target' x hx := hx
  left_inv' x hx := by
    change (if hx' : x ∈ boundedExcisionSet C φ then (⟨x, hx'⟩ : boundedExcisionSet C φ)
      else boundedExcisionPoint C φ hφ).val = x
    rw [dite_eq_left (boundedRetained_subset C φ hx)]
  right_inv' x hx := by
    change (if hx' : x.val ∈ boundedExcisionSet C φ then (⟨x.val, hx'⟩ : boundedExcisionSet C φ)
      else boundedExcisionPoint C φ hφ) = x
    rw [dite_eq_left x.property]
  open_source := boundedRetained_open C φ hφ
  open_target := (boundedRetained_open C φ hφ).preimage continuous_subtype_val
  continuousOn_toFun := by
    apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply (continuous_id.continuousOn : ContinuousOn id (boundedRetainedSet C φ)).congr
    intro x hx
    change (if hx' : x ∈ boundedExcisionSet C φ then (⟨x, hx'⟩ : boundedExcisionSet C φ)
      else boundedExcisionPoint C φ hφ).val = x
    rw [dite_eq_left (boundedRetained_subset C φ hx)]
  continuousOn_invFun := continuous_subtype_val.continuousOn }

private theorem boundedRetainedPatch_apply (x : C.Carrier) (hx : x ∈ boundedRetainedSet C φ) :
    (boundedRetainedPatch C φ hφ x).val = x := by
  classical
  change (if hx' : x ∈ boundedExcisionSet C φ then (⟨x, hx'⟩ : boundedExcisionSet C φ)
    else boundedExcisionPoint C φ hφ).val = x
  rw [dite_eq_left (boundedRetained_subset C φ hx)]

private def twicePlane : PlaneLift.{u} ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ PlaneLift.{u} :=
  (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).symm.trans
    (((ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℂ)
      (Units.mk0 (2 : ℝ) (by norm_num))).toDiffeomorph).trans
        (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ))

private def boundedTwiceTube :
    (PlaneLift.{u} × Circle) ≃ₘ⟮(𝓘(ℝ, ℂ).prod (𝓡 1)),
      (𝓘(ℝ, ℂ).prod (𝓡 1))⟯ (PlaneLift.{u} × Circle) :=
  twicePlane.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)

private def annulusAmbient :
    PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model
      (PlaneLift.{u} × Circle) C.Carrier ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    (boundedTwiceTube.toPartialDiffeomorph.trans φ) {z | ‖z.1.down‖ < 3 / 4}
    (isOpen_lt
      ((continuous_norm.comp contMDiff_planeLift_down.continuous).comp continuous_fst)
      continuous_const)

include hφ in
private theorem annulusAmbient_source :
    (annulusAmbient C φ).source = {z : PlaneLift.{u} × Circle | ‖z.1.down‖ < 3 / 4} := by
  ext z
  change ((z ∈ univ ∧ boundedTwiceTube z ∈ φ.source) ∧ ‖z.1.down‖ < 3 / 4) ↔ _
  constructor
  · exact And.right
  · intro hz
    refine ⟨⟨mem_univ z, hφ ?_⟩, hz⟩
    change ‖(2 : ℝ) • z.1.down‖ ≤ 3
    rw [norm_smul, Real.norm_eq_abs]
    rw [show |(2 : ℝ)| = 2 by norm_num]
    change ‖z.1.down‖ < 3 / 4 at hz
    linarith

include hφ in
private theorem annulusAmbient_membership (z : PlaneLift.{u} × Circle)
    (hz : z ∈ (annulusAmbient C φ).source) :
    z ∈ productSet 2 ↔ annulusAmbient C φ z ∈ boundedExcisionSet C φ := by
  have hzsmall := hz
  rw [annulusAmbient_source C φ hφ] at hzsmall
  have hw : boundedTwiceTube z ∈ φ.source := hz.1.2
  have hn : ‖(boundedTwiceTube z).1.down‖ = 2 * ‖z.1.down‖ := by
    change ‖(2 : ℝ) • z.1.down‖ = _
    rw [norm_smul, Real.norm_eq_abs]
    norm_num
  have hnot : φ (boundedTwiceTube z) ∈ boundedExcisionSet C φ ↔
      1 ≤ ‖(boundedTwiceTube z).1.down‖ := by
    constructor
    · intro hx
      by_contra hlt
      exact hx ⟨boundedTwiceTube z, lt_of_not_ge hlt, rfl⟩
    · intro hx
      rintro ⟨w, hwsmall, he⟩
      have hwsrc : w ∈ φ.source := by
        apply hφ
        change ‖w.1.down‖ ≤ 3
        change ‖w.1.down‖ < 1 at hwsmall
        linarith
      have heq := φ.injOn hwsrc hw he
      rw [heq] at hwsmall
      exact (not_lt_of_ge hx) hwsmall
  change (z.1 ∈ planarSet 2) ↔ _
  rw [mem_planarSet_iff (Or.inl rfl), mem_planarModel_two]
  change ‖z.1.down‖ < 3 / 4 at hzsmall
  change (‖z.1.down‖ ≤ 3 ∧ 1 / 2 ≤ ‖z.1.down‖) ↔ φ (boundedTwiceTube z) ∈ boundedExcisionSet C φ
  rw [hnot, hn]
  constructor
  · intro h
    linarith [h.2]
  · intro h
    constructor <;> linarith

private def annulusPatch :
    OpenPartialHomeomorph (productSet.{u} 2) (boundedExcisionSet C φ) :=
  OpenPartialHomeomorph.restrictSubtypes (annulusAmbient C φ).toOpenPartialHomeomorph
    (productSet.{u} 2) (boundedExcisionSet C φ)
    (productCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) ((1, 1), halfZero))
    (boundedExcisionPoint C φ hφ) (annulusAmbient_membership C φ hφ)

private theorem annulusPatch_apply (z : productSet.{u} 2)
    (hz : z ∈ (annulusPatch C φ hφ).source) :
    (annulusPatch C φ hφ z).val = annulusAmbient C φ z.val :=
  OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ hz

private theorem annulusPatch_symm_apply (x : boundedExcisionSet C φ)
    (hx : x ∈ (annulusPatch C φ hφ).target) :
    ((annulusPatch C φ hφ).symm x).val = (annulusAmbient C φ).symm x.val :=
  OpenPartialHomeomorph.restrictSubtypes_symm_apply _ _ _ _ _ _ _ hx

private theorem boundedExcision_cover (x : boundedExcisionSet C φ) :
    x ∈ (boundedRetainedPatch C φ hφ).target ∨ x ∈ (annulusPatch C φ hφ).target := by
  classical
  by_cases hx : x.val ∈ boundedRetainedSet C φ
  · exact Or.inl hx
  · have hxclosed : x.val ∈ φ '' {z : PlaneLift.{u} × Circle | ‖z.1.down‖ ≤ 1} :=
      Classical.not_not.mp hx
    obtain ⟨z, hz, he⟩ := hxclosed
    have hzge : 1 ≤ ‖z.1.down‖ := by
      by_contra hlt
      exact x.property ⟨z, lt_of_not_ge hlt, he⟩
    have hz1 : ‖z.1.down‖ = 1 := le_antisymm hz hzge
    let w := boundedTwiceTube.{u}.symm z
    have hn : ‖w.1.down‖ = 1 / 2 := by
      have heq := congrArg (fun v : PlaneLift.{u} × Circle => ‖v.1.down‖)
        (boundedTwiceTube.{u}.apply_symm_apply z)
      change ‖(2 : ℝ) • w.1.down‖ = ‖z.1.down‖ at heq
      rw [norm_smul, Real.norm_eq_abs, hz1] at heq
      norm_num at heq
      change 2 * ‖w.1.down‖ = 1 at heq
      linarith
    have hw : w ∈ (annulusAmbient C φ).source := by
      rw [annulusAmbient_source C φ hφ]
      change ‖w.1.down‖ < 3 / 4
      rw [hn]
      norm_num
    have hpoint : annulusAmbient C φ w = x.val := by
      change φ (boundedTwiceTube w) = x.val
      rw [boundedTwiceTube.apply_symm_apply]
      exact he
    apply Or.inr
    change x.val ∈ (annulusAmbient C φ).target
    exact hpoint ▸ (annulusAmbient C φ).map_source hw

private abbrev boundedExcisionPatchCarrier : Bool → Type u
  | false => C.Carrier
  | true => productSet.{u} 2

private abbrev boundedExcisionPatchSpace : Bool → Type
  | false => C.kind.Space
  | true => EuclideanHalfSpace 3

@[instance_reducible]
private instance boundedExcisionPatchTopology (a : Bool) :
    TopologicalSpace (boundedExcisionPatchCarrier C a) := by
  cases a <;> dsimp [boundedExcisionPatchCarrier] <;> infer_instance

@[instance_reducible]
private instance boundedExcisionPatchSpaceTopology (a : Bool) :
    TopologicalSpace (boundedExcisionPatchSpace C a) := by
  cases a <;> dsimp [boundedExcisionPatchSpace] <;> infer_instance

@[instance_reducible]
private instance boundedExcisionPatchCharts (a : Bool) :
    ChartedSpace (boundedExcisionPatchSpace C a) (boundedExcisionPatchCarrier C a) := by
  cases a <;> dsimp [boundedExcisionPatchCarrier, boundedExcisionPatchSpace] <;> infer_instance

private abbrev boundedExcisionPatchModel (a : Bool) :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 3)) (boundedExcisionPatchSpace C a) := by
  cases a
  · exact C.model
  · exact 𝓡∂ 3

private instance boundedExcisionPatchSmooth (a : Bool) :
    IsManifold (boundedExcisionPatchModel C a) ∞ (boundedExcisionPatchCarrier C a) := by
  cases a <;> dsimp [boundedExcisionPatchModel, boundedExcisionPatchCarrier] <;> infer_instance

private def boundedExcisionPatch : (a : Bool) →
    OpenPartialHomeomorph (boundedExcisionPatchCarrier C a) (boundedExcisionSet C φ)
  | false => boundedRetainedPatch C φ hφ
  | true => annulusPatch C φ hφ

private def boundedExcisionNative (a : Bool) : boundedExcisionPatchCarrier C a → C.Carrier := by
  cases a
  · exact id
  · exact fun z => annulusAmbient C φ z.val

private theorem boundedExcisionPatch_apply (a : Bool) (p : boundedExcisionPatchCarrier C a)
    (hp : p ∈ (boundedExcisionPatch C φ hφ a).source) :
    (boundedExcisionPatch C φ hφ a p).val = boundedExcisionNative C φ a p := by
  cases a
  · exact boundedRetainedPatch_apply C φ hφ p hp
  · exact annulusPatch_apply C φ hφ p hp

private theorem boundedExcisionNative_smooth (a : Bool) :
    ContMDiffOn (boundedExcisionPatchModel C a) (C.model) ∞
      (boundedExcisionNative C φ a) (boundedExcisionPatch C φ hφ a).source := by
  cases a
  · exact contMDiff_id.contMDiffOn
  · exact (annulusAmbient C φ).contMDiffOn.comp
      (productAtlas 2).contMDiff_subtype_val.contMDiffOn (fun z hz => hz)

private theorem boundedExcisionPatch_compatible (a b : Bool) :
    ContMDiffOn (boundedExcisionPatchModel C a) (boundedExcisionPatchModel C b) ∞
      ((boundedExcisionPatch C φ hφ a).trans (boundedExcisionPatch C φ hφ b).symm)
      ((boundedExcisionPatch C φ hφ a).trans (boundedExcisionPatch C φ hφ b).symm).source := by
  cases b
  · apply ((boundedExcisionNative_smooth C φ hφ a).mono (fun z hz => hz.1)).congr
    intro z hz
    exact boundedExcisionPatch_apply C φ hφ a z hz.1
  · apply ((productAtlas 2).contMDiffOn_iff_subtype_val _ _).mpr
    let S := ((boundedExcisionPatch C φ hφ a).trans (boundedExcisionPatch C φ hφ true).symm).source
    have hN : ContMDiffOn (boundedExcisionPatchModel C a) (C.model) ∞
        (boundedExcisionNative C φ a) S :=
      (boundedExcisionNative_smooth C φ hφ a).mono (fun z hz => hz.1)
    have hm : MapsTo (boundedExcisionNative C φ a) S (annulusAmbient C φ).target := by
      intro z hz
      have ht := hz.2
      change (boundedExcisionPatch C φ hφ a z).val ∈ (annulusAmbient C φ).target at ht
      rwa [boundedExcisionPatch_apply C φ hφ a z hz.1] at ht
    have h := (annulusAmbient C φ).symm.contMDiffOn.comp hN hm
    apply h.congr
    intro z hz
    change ((annulusPatch C φ hφ).symm (boundedExcisionPatch C φ hφ a z)).val = _
    exact (annulusPatch_symm_apply C φ hφ (boundedExcisionPatch C φ hφ a z) hz.2).trans
      (congrArg (annulusAmbient C φ).symm (boundedExcisionPatch_apply C φ hφ a z hz.1))

private def boundedExcisionHalfChart {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M] (x : M) :
    PartialDiffeomorph (𝓡∂ 3) (𝓡∂ 3) M (EuclideanHalfSpace 3) ∞ where
  __ := chartAt (EuclideanHalfSpace 3) x
  contMDiffOn_toFun := contMDiffOn_chart
  contMDiffOn_invFun := contMDiffOn_chart_symm

private theorem exists_boundedExcisionAtlas :
    ∃ A : ChartedSpace (EuclideanHalfSpace 3) (boundedExcisionSet C φ), letI := A
      IsManifold (𝓡∂ 3) ∞ (boundedExcisionSet C φ) ∧ ∀ a : Bool,
        ContMDiffOn (boundedExcisionPatchModel C a) (𝓡∂ 3) ∞
          (boundedExcisionPatch C φ hφ a) (boundedExcisionPatch C φ hφ a).source ∧
        ContMDiffOn (𝓡∂ 3) (boundedExcisionPatchModel C a) ∞
          (boundedExcisionPatch C φ hφ a).symm (boundedExcisionPatch C φ hφ a).target := by
  apply exists_carrierSurgeryAtlas_of_openCover (𝓡∂ 3) (boundedExcisionPatch C φ hφ)
  · intro x
    rcases boundedExcision_cover C φ hφ x with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  · exact boundedExcisionPatch_compatible C φ hφ
  · intro a x hx
    cases a
    · exact exists_sphereCapCarrierCoordinates C x
    · exact ⟨boundedExcisionHalfChart x, mem_chart_source (EuclideanHalfSpace 3) x⟩

@[instance_reducible]
private def boundedExcisionCharts : ChartedSpace (EuclideanHalfSpace 3) (boundedExcisionSet C φ) :=
  Classical.choose (exists_boundedExcisionAtlas C φ hφ)

private theorem boundedExcisionSmooth :
    letI := boundedExcisionCharts C φ hφ
    IsManifold (𝓡∂ 3) ∞ (boundedExcisionSet C φ) :=
  (Classical.choose_spec (exists_boundedExcisionAtlas C φ hφ)).1

private def boundedExcisionPD (a : Bool) :
    letI := boundedExcisionCharts C φ hφ
    PartialDiffeomorph (boundedExcisionPatchModel C a) (𝓡∂ 3)
      (boundedExcisionPatchCarrier C a) (boundedExcisionSet C φ) ∞ := by
  letI := boundedExcisionCharts C φ hφ
  exact { boundedExcisionPatch C φ hφ a with
    contMDiffOn_toFun := (Classical.choose_spec (exists_boundedExcisionAtlas C φ hφ)).2 a |>.1
    contMDiffOn_invFun := (Classical.choose_spec (exists_boundedExcisionAtlas C φ hφ)).2 a |>.2 }

private theorem boundedExcisionVal_smooth :
    letI := boundedExcisionCharts C φ hφ
    ContMDiff (𝓡∂ 3) (C.model) ∞
      (Subtype.val : boundedExcisionSet C φ → C.Carrier) := by
  let := boundedExcisionCharts C φ hφ
  have := boundedExcisionSmooth C φ hφ
  intro x
  obtain ⟨a, hx⟩ : ∃ a, x ∈ (boundedExcisionPatch C φ hφ a).target := by
    rcases boundedExcision_cover C φ hφ x with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  have hs := (boundedExcisionNative_smooth C φ hφ a).comp
    (boundedExcisionPD C φ hφ a).symm.contMDiffOn
    (fun y hy => (boundedExcisionPatch C φ hφ a).map_target hy)
  apply (hs.contMDiffAt
    ((boundedExcisionPatch C φ hφ a).open_target.mem_nhds hx)).congr_of_eventuallyEq
  filter_upwards [(boundedExcisionPatch C φ hφ a).open_target.mem_nhds hx] with y hy
  change y.val = boundedExcisionNative C φ a ((boundedExcisionPatch C φ hφ a).symm y)
  have he := boundedExcisionPatch_apply C φ hφ a _ ((boundedExcisionPatch C φ hφ a).map_target hy)
  rw [(boundedExcisionPatch C φ hφ a).right_inv hy] at he
  exact he

private theorem boundedExcisionNative_mfderiv (a : Bool) (p : boundedExcisionPatchCarrier C a)
    (hp : p ∈ (boundedExcisionPatch C φ hφ a).source) :
    Bijective (mfderiv (boundedExcisionPatchModel C a) (C.model)
      (boundedExcisionNative C φ a) p) := by
  cases a
  · change Bijective (mfderiv (C.model) (C.model) id p)
    rw [mfderiv_id]
    exact bijective_id
  · have hd := (annulusAmbient C φ).isLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1))
      (C.model) ∞ hp
    have hb := (productAtlas 2).mfderiv_subtypeVal_bijective p
    have hcomp := mfderiv_comp p
      (((annulusAmbient C φ).contMDiffOn.contMDiffAt
        ((annulusAmbient C φ).open_source.mem_nhds hp)).mdifferentiableAt (by simp))
      (((productAtlas 2).contMDiff_subtype_val p).mdifferentiableAt (by simp))
    change Bijective (mfderiv (𝓡∂ 3) (C.model)
      ((annulusAmbient C φ) ∘ Subtype.val) p)
    rw [hcomp]
    have he : Bijective (mfderiv (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model
        (annulusAmbient C φ) p.val) := by
      rw [← hd.mfderivToContinuousLinearEquiv_coe (by simp)]
      exact (hd.mfderivToContinuousLinearEquiv (by simp)).bijective
    exact he.comp hb

private theorem boundedExcisionVal_mfderiv (x : boundedExcisionSet C φ) :
    letI := boundedExcisionCharts C φ hφ
    Bijective (mfderiv (𝓡∂ 3) (C.model)
      (Subtype.val : boundedExcisionSet C φ → C.Carrier) x) := by
  let := boundedExcisionCharts C φ hφ
  have := boundedExcisionSmooth C φ hφ
  obtain ⟨a, hx⟩ : ∃ a, x ∈ (boundedExcisionPatch C φ hφ a).target := by
    rcases boundedExcision_cover C φ hφ x with hx | hx
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩
  let d := boundedExcisionPD C φ hφ a
  let p := d.symm x
  have hp : p ∈ d.source := d.map_target hx
  have heq : (Subtype.val ∘ d) =ᶠ[𝓝 p] boundedExcisionNative C φ a := by
    filter_upwards [d.open_source.mem_nhds hp] with y hy
    exact boundedExcisionPatch_apply C φ hφ a y hy
  have hn : Bijective (mfderiv (boundedExcisionPatchModel C a) (C.model)
      (Subtype.val ∘ d) p) := by
    rw [heq.mfderiv_eq]
    exact boundedExcisionNative_mfderiv C φ hφ a p hp
  have hl := d.isLocalDiffeomorphAt (boundedExcisionPatchModel C a) (𝓡∂ 3) ∞ hp
  have hd : Bijective (mfderiv (boundedExcisionPatchModel C a) (𝓡∂ 3) d p) := by
    rw [← hl.mfderivToContinuousLinearEquiv_coe (by simp)]
    exact (hl.mfderivToContinuousLinearEquiv (by simp)).bijective
  rw [mfderiv_comp p (((boundedExcisionVal_smooth C φ hφ) (d p)).mdifferentiableAt (by simp))
    ((d.contMDiffOn.contMDiffAt (d.open_source.mem_nhds hp)).mdifferentiableAt (by simp))] at hn
  have h : Bijective (mfderiv (𝓡∂ 3) (C.model)
      (Subtype.val : boundedExcisionSet C φ → C.Carrier) (d p)) :=
    (Bijective.of_comp_iff _ hd).mp hn
  have he : d p = x := d.right_inv hx
  exact he ▸ h

include hφ in
private theorem boundedExcision_compact : IsCompact (boundedExcisionSet C φ) := by
  have hs : {z : PlaneLift.{u} × Circle | ‖z.1.down‖ < 1} ⊆ φ.source := by
    intro z hz
    apply hφ
    change ‖z.1.down‖ ≤ 3
    change ‖z.1.down‖ < 1 at hz
    linarith
  have ho : IsOpen (φ '' {z : PlaneLift.{u} × Circle | ‖z.1.down‖ < 1}) :=
    φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      (isOpen_lt
      ((continuous_norm.comp contMDiff_planeLift_down.continuous).comp continuous_fst)
      continuous_const) hs
  exact ho.isClosed_compl.isCompact

private theorem baseChart_interior (x : C.Carrier) (hx : x ∈ φ.target) :
    (C.model).IsInteriorPoint x := by
  have h := φ.isLocalDiffeomorphAt (𝓘(ℝ, ℂ).prod (𝓡 1)) (C.model) ∞ (φ.map_target hx)
  have hi := (h.isInteriorPoint_iff (by simp : (∞ : ℕ∞ω) ≠ 0)).mp
    BoundarylessManifold.isInteriorPoint
  rwa [φ.right_inv hx] at hi

include hφ in
private theorem oldBoundary_boundedRetained (x : C.Carrier)
    (hx : (C.model).IsBoundaryPoint x) : x ∈ boundedRetainedSet C φ := by
  rintro ⟨z, hz, he⟩
  have hzsrc : z ∈ φ.source := by
    apply hφ
    change ‖z.1.down‖ ≤ 3
    change ‖z.1.down‖ ≤ 1 at hz
    linarith
  have hi := baseChart_interior C φ x (he ▸ φ.map_source hzsrc)
  exact ((C.model).isInteriorPoint_iff_not_isBoundaryPoint x).mp hi hx

private theorem annulus_boundary (z : productSet.{u} 2)
    (hz : z ∈ (annulusPatch C φ hφ).source) :
    (𝓡∂ 3).IsBoundaryPoint z ↔ ‖z.val.1.down‖ = 1 / 2 := by
  have hn : ‖z.val.1.down‖ < 3 / 4 := by
    have h := hz
    change z.val ∈ (annulusAmbient C φ).source at h
    rwa [annulusAmbient_source C φ hφ] at h
  rw [productSet_isBoundaryPoint_iff 2]
  simp only [planarFunction, ↓reduceIte, sqDist, sub_zero, mul_eq_zero]
  constructor
  · rintro (he | he)
    · nlinarith [norm_nonneg z.val.1.down]
    · nlinarith [norm_nonneg z.val.1.down]
  · intro he
    right
    rw [he]
    norm_num

private theorem boundedExcision_boundary_iff (x : boundedExcisionSet C φ) :
    letI := boundedExcisionCharts C φ hφ
    (𝓡∂ 3).IsBoundaryPoint x ↔
      (C.model).IsBoundaryPoint x.val ∨
        x.val ∈ φ '' {z : PlaneLift.{u} × Circle | ‖z.1.down‖ = 1} := by
  let := boundedExcisionCharts C φ hφ
  have := boundedExcisionSmooth C φ hφ
  rcases boundedExcision_cover C φ hφ x with hx | hx
  · let d := boundedExcisionPD C φ hφ false
    have hp : x.val ∈ d.source := hx
    have he : d x.val = x := Subtype.ext (boundedRetainedPatch_apply C φ hφ x.val hx)
    have hl := d.isLocalDiffeomorphAt (C.model) (𝓡∂ 3) ∞ hp
    have hb := hl.isBoundaryPoint_iff (by simp)
    rw [he] at hb
    have hnot : x.val ∉ φ '' {z : PlaneLift.{u} × Circle | ‖z.1.down‖ = 1} := by
      rintro ⟨z, hz, heq⟩
      exact hx ⟨z, le_of_eq hz, heq⟩
    exact hb.symm.trans (or_iff_left hnot).symm
  · let d := boundedExcisionPD C φ hφ true
    let z := d.symm x
    have hz : z ∈ d.source := d.map_target hx
    have he := annulusPatch_apply C φ hφ z hz
    have hzval : x.val = φ (boundedTwiceTube z.val) := by
      exact (congrArg Subtype.val (d.right_inv hx)).symm.trans he
    have hzsrc : boundedTwiceTube z.val ∈ φ.source := hz.1.2
    have hnot : ¬ (C.model).IsBoundaryPoint x.val := by
      exact ((C.model).isInteriorPoint_iff_not_isBoundaryPoint x.val).mp
        (baseChart_interior C φ x.val (hzval.symm ▸ φ.map_source hzsrc))
    have hi : x.val ∈ φ '' {w : PlaneLift.{u} × Circle | ‖w.1.down‖ = 1} ↔
        ‖z.val.1.down‖ = 1 / 2 := by
      have hn : ‖(boundedTwiceTube z.val).1.down‖ = 2 * ‖z.val.1.down‖ := by
        change ‖(2 : ℝ) • z.val.1.down‖ = _
        rw [norm_smul, Real.norm_eq_abs]
        norm_num
      constructor
      · rintro ⟨w, hw, hwx⟩
        have hwsrc : w ∈ φ.source := by
          apply hφ
          change ‖w.1.down‖ ≤ 3
          change ‖w.1.down‖ = 1 at hw
          rw [hw]
          norm_num
        have heq := φ.injOn hwsrc hzsrc (hwx.trans hzval)
        change ‖w.1.down‖ = 1 at hw
        rw [heq, hn] at hw
        linarith
      · intro hnorm
        refine ⟨boundedTwiceTube z.val, ?_, hzval.symm⟩
        change ‖(boundedTwiceTube z.val).1.down‖ = 1
        rw [hn, hnorm]
        norm_num
    have hl := d.symm.isLocalDiffeomorphAt (𝓡∂ 3) (𝓡∂ 3) ∞ hx
    have hb := hl.isBoundaryPoint_iff (by simp)
    exact hb.trans ((annulus_boundary C φ hφ z hz).trans
      (hi.symm.trans (or_iff_right hnot).symm))


private def boundedTranslation (v : BoundedE3) : BoundedE3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ BoundedE3 where
  toFun z := z + v
  invFun z := z - v
  left_inv z := by simp
  right_inv z := by simp
  contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
  contMDiff_invFun := (contDiff_id.sub contDiff_const).contMDiff

private def boundedSwap : BoundedE3 ≃L[ℝ] BoundedE3 :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 3) 1)).toContinuousLinearEquiv

private theorem boundedSwap_zero (v : BoundedE3) : boundedSwap v 0 = v 1 := by
  simp [boundedSwap, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

private theorem boundedHalfInterior_val (v : BoundedE3) (hv : 0 < v 0) :
    (halfSpaceThreeInteriorPartialDiffeomorph 0 v).val = v := by
  apply halfSpaceThreeSplit.injective
  apply Prod.ext
  · change max ((halfSpaceThreeSplit v).1 - 0) 0 = (halfSpaceThreeSplit v).1
    have h : 0 ≤ (halfSpaceThreeSplit v).1 := hv.le
    rw [sub_zero, max_eq_left h]
  · change (halfSpaceThreeSplit (halfSpaceThreeSplit.symm
      (max ((halfSpaceThreeSplit v).1 - 0) 0, (halfSpaceThreeSplit v).2))).2 = _
    rw [ContinuousLinearEquiv.apply_symm_apply]

private theorem annulusImmersion_closed
    {N : Type u} [TopologicalSpace N] [ChartedSpace BoundedE3 N] [IsManifold (𝓡 3) ∞ N]
    (D : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
      (PlaneLift.{u} × Circle) N ∞) (x : productSet.{u} 2) (hx : x.val ∈ D.source) :
    IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 3) (𝓡 3) ∞ (D ∘ Subtype.val) x := by
  let A := productAtlas.{u} 2
  let a := A.ambientChart x
  let s : Set (productSet.{u} 2) := (A.chart x).source ∩ Subtype.val ⁻¹' D.source
  have hs : IsOpen s := (A.chart x).open_source.inter
    (D.open_source.preimage continuous_subtype_val)
  let α := (A.chart x).restr s
  let c := D.symm.trans a
  have hαsource : α.source = s := by
    rw [OpenPartialHomeomorph.restr_source' (A.chart x) s hs, inter_eq_right]
    exact inter_subset_left
  have hxs : x ∈ s := ⟨A.mem_source x, hx⟩
  have hαmax : α ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ (productSet.{u} 2) :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡∂ 3))
      (IsManifold.chart_mem_maximalAtlas x) hs
  have hcmax : c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas (𝓡 3) ∞ N :=
    c.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      c.contMDiffOn_toFun c.contMDiffOn_invFun
  have hc (y : productSet.{u} 2) (hy : y ∈ s) : D y.val ∈ c.source := by
    change D y.val ∈ D.target ∧ D.symm (D y.val) ∈ a.source
    have hleft : D.symm.toPartialEquiv (D.toPartialEquiv y.val) = y.val :=
      D.toPartialEquiv.left_inv hy.2
    rw [hleft]
    exact ⟨D.map_source hy.2, hy.1⟩
  have hf (y : productSet.{u} 2) (hy : y ∈ s) :
      c.toOpenPartialHomeomorph.extend (𝓡 3) (D y.val) = (α.extend (𝓡∂ 3)) y := by
    change a (D.symm (D y.val)) = (A.chart x y).val
    have hleft : D.symm.toPartialEquiv (D.toPartialEquiv y.val) = y.val :=
      D.toPartialEquiv.left_inv hy.2
    rw [hleft]
    exact (OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ hy.1).symm
  refine IsImmersionAtOfComplement.mk_of_charts
    (ContinuousLinearEquiv.prodUnique ℝ BoundedE3 PUnit.{1})
    α c.toOpenPartialHomeomorph (hαsource.symm ▸ hxs) (hc x hxs)
    hαmax hcmax (fun y hy => hc y (hαsource ▸ hy)) ?_
  intro w hw
  let y := (α.extend (𝓡∂ 3)).symm w
  have hy : y ∈ s := by
    have h := (α.extend (𝓡∂ 3)).map_target hw
    rwa [OpenPartialHomeomorph.extend_source, hαsource] at h
  change c.toOpenPartialHomeomorph.extend (𝓡 3) (D y.val) = w
  rw [hf y hy]
  exact (α.extend (𝓡∂ 3)).right_inv hw


private theorem annulusImmersion_half
    {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
    [IsManifold (𝓡∂ 3) ∞ N]
    (D : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡∂ 3)
      (PlaneLift.{u} × Circle) N ∞) (x : productSet.{u} 2) (hx : x.val ∈ D.source) :
    IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 3) (𝓡∂ 3) ∞ (D ∘ Subtype.val) x := by
  let A := productAtlas.{u} 2
  let a := A.ambientChart x
  let v : BoundedE3 := WithLp.toLp 2 (fun i => if i = 1 then 1 - a x.val 1 else 0)
  have hv : v 0 = 0 := by simp [v]
  let d : EuclideanHalfSpace 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ EuclideanHalfSpace 3 :=
    EuclideanHalfSpace.tangentialShiftDiffeomorph 2 v hv
  let α₀ := (A.chart x).trans d.toHomeomorph.toOpenPartialHomeomorph
  let s : Set (productSet.{u} 2) := (α₀.source ∩
    α₀ ⁻¹' {y : EuclideanHalfSpace 3 | 0 < y.val 1}) ∩ Subtype.val ⁻¹' D.source
  have hs : IsOpen s := (α₀.isOpen_inter_preimage
    (isOpen_lt continuous_const
      ((EuclideanSpace.proj 1).continuous.comp continuous_subtype_val))).inter
      (D.open_source.preimage continuous_subtype_val)
  let α := α₀.restr s
  let c := (((D.symm.trans a).trans
    (boundedTranslation v).toPartialDiffeomorph).trans
    boundedSwap.toDiffeomorph.toPartialDiffeomorph).trans
      (halfSpaceThreeInteriorPartialDiffeomorph 0)
  have hαsource : α.source = s := by
    rw [OpenPartialHomeomorph.restr_source' α₀ s hs, inter_eq_right]
    exact fun y hy => hy.1.1
  have hxs : x ∈ s := by
    refine ⟨⟨⟨A.mem_source x, mem_univ _⟩, ?_⟩, hx⟩
    change 0 < (A.chart x x).val 1 + v 1
    rw [show (A.chart x x).val = a x.val from
      OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ (A.mem_source x)]
    change 0 < a x.val 1 + (1 - a x.val 1)
    linarith
  have hαmax : α ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ (productSet.{u} 2) := by
    apply restr_mem_maximalAtlas (contDiffGroupoid ∞ (𝓡∂ 3)) ?_ hs
    apply α₀.mem_maximalAtlas_of_contMDiffOn
    · change ContMDiffOn (𝓡∂ 3) (𝓡∂ 3) ∞ (d ∘ A.chart x) α₀.source
      exact d.contMDiff.comp_contMDiffOn
        ((contMDiffOn_of_mem_maximalAtlas
          (IsManifold.chart_mem_maximalAtlas x)).mono (fun y hy => hy.1))
    · change ContMDiffOn (𝓡∂ 3) (𝓡∂ 3) ∞ ((A.chart x).symm ∘ d.symm) α₀.target
      exact (contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.chart_mem_maximalAtlas x)).comp d.symm.contMDiff.contMDiffOn
        (fun y hy => hy.2)
  have hcmax : c.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ N :=
    c.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      c.contMDiffOn_toFun c.contMDiffOn_invFun
  have ha (y : productSet.{u} 2) (hy : y ∈ s) :
      (α₀ y).val = a y.val + v := by
    change (A.chart x y).val + v = a y.val + v
    exact congrArg (fun w : BoundedE3 => w + v)
      (OpenPartialHomeomorph.restrictSubtypes_apply _ _ _ _ _ _ _ hy.1.1.1)
  have hc (y : productSet.{u} 2) (hy : y ∈ s) : D y.val ∈ c.source := by
    change (((D y.val ∈ D.target ∧ D.symm (D y.val) ∈ a.source) ∧
      a (D.symm (D y.val)) ∈ univ) ∧
      boundedTranslation v (a (D.symm (D y.val))) ∈ univ) ∧
      boundedSwap (boundedTranslation v (a (D.symm (D y.val)))) ∈
        (halfSpaceThreeInteriorPartialDiffeomorph 0).source
    have hleft : D.symm.toPartialEquiv (D.toPartialEquiv y.val) = y.val :=
      D.toPartialEquiv.left_inv hy.2
    rw [hleft]
    refine ⟨⟨⟨⟨D.map_source hy.2, hy.1.1.1⟩, mem_univ _⟩, mem_univ _⟩, ?_⟩
    apply (halfSpaceThreeInteriorChart_mem_source 0 _).mpr
    change 0 < boundedSwap (a y.val + v) 0
    rw [boundedSwap_zero, ← ha y hy]
    exact hy.1.2
  have hf (y : productSet.{u} 2) (hy : y ∈ s) :
      c.toOpenPartialHomeomorph.extend (𝓡∂ 3) (D y.val) =
        boundedSwap ((α.extend (𝓡∂ 3)) y) := by
    change ((halfSpaceThreeInteriorPartialDiffeomorph 0)
      (boundedSwap (a (D.symm (D y.val)) + v))).val = boundedSwap ((α₀ y).val)
    have hleft : D.symm.toPartialEquiv (D.toPartialEquiv y.val) = y.val :=
      D.toPartialEquiv.left_inv hy.2
    rw [hleft, boundedHalfInterior_val, ha y hy]
    rw [boundedSwap_zero, ← ha y hy]
    exact hy.1.2
  refine IsImmersionAtOfComplement.mk_of_charts
    ((ContinuousLinearEquiv.prodUnique ℝ BoundedE3 PUnit.{1}).trans boundedSwap)
    α c.toOpenPartialHomeomorph (hαsource.symm ▸ hxs) (hc x hxs)
    hαmax hcmax (fun y hy => hc y (hαsource ▸ hy)) ?_
  intro w hw
  let y := (α.extend (𝓡∂ 3)).symm w
  have hy : y ∈ s := by
    have h := (α.extend (𝓡∂ 3)).map_target hw
    rwa [OpenPartialHomeomorph.extend_source, hαsource] at h
  change c.toOpenPartialHomeomorph.extend (𝓡∂ 3) (D y.val) = boundedSwap w
  rw [hf y hy]
  exact congrArg boundedSwap ((α.extend (𝓡∂ 3)).right_inv hw)


private theorem retainedInverseImmersion_closed
    {M N : Type u} [TopologicalSpace M] [ChartedSpace BoundedE3 M] [IsManifold (𝓡 3) ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
    [IsManifold (𝓡∂ 3) ∞ N]
    (e : PartialDiffeomorph (𝓡 3) (𝓡∂ 3) M N ∞) (x : N) (hx : x ∈ e.target) :
    IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 3) (𝓡 3) ∞ e.symm x := by
  let a₀ := PartialDiffeomorph.extendedChart (I := 𝓡 3) (e.symm x)
  let v : BoundedE3 := WithLp.toLp 2 (fun i => if i = 0 then 1 - a₀ (e.symm x) 0 else 0)
  let a := a₀.trans (boundedTranslation v).toPartialDiffeomorph
  let α := (e.symm.trans a).trans (halfSpaceThreeInteriorPartialDiffeomorph 0)
  have hxa : e.symm x ∈ a.source := ⟨mem_extChartAt_source _, mem_univ _⟩
  have ha0 : 0 < a (e.symm x) 0 := by
    change 0 < a₀ (e.symm x) 0 + (1 - a₀ (e.symm x) 0)
    linarith
  have hxα : x ∈ α.source := by
    refine ⟨⟨hx, hxa⟩, ?_⟩
    exact (halfSpaceThreeInteriorChart_mem_source 0 (a (e.symm x))).mpr ha0
  have hαmax : α.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas (𝓡∂ 3) ∞ N :=
    α.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      α.contMDiffOn_toFun α.contMDiffOn_invFun
  have hamax : a.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas (𝓡 3) ∞ M :=
    a.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      a.contMDiffOn_toFun a.contMDiffOn_invFun
  have hf (y : N) (hy : y ∈ α.source) :
      a.toOpenPartialHomeomorph.extend (𝓡 3) (e.symm y) =
        α.toOpenPartialHomeomorph.extend (𝓡∂ 3) y := by
    change a (e.symm y) = (halfSpaceThreeInteriorPartialDiffeomorph 0 (a (e.symm y))).val
    apply (boundedHalfInterior_val _ ?_).symm
    exact (halfSpaceThreeInteriorChart_mem_source 0 (a (e.symm y))).mp hy.2
  refine IsImmersionAtOfComplement.mk_of_charts
    (ContinuousLinearEquiv.prodUnique ℝ BoundedE3 PUnit.{1})
    α.toOpenPartialHomeomorph a.toOpenPartialHomeomorph hxα hxa hαmax hamax
    (fun y hy => hy.1.2) ?_
  intro w hw
  let y := (α.toOpenPartialHomeomorph.extend (𝓡∂ 3)).symm w
  have hy : y ∈ α.source := by
    have h := (α.toOpenPartialHomeomorph.extend (𝓡∂ 3)).map_target hw
    rw [OpenPartialHomeomorph.extend_source] at h
    exact h
  change a.toOpenPartialHomeomorph.extend (𝓡 3) (e.symm y) = w
  rw [hf y hy]
  exact (α.toOpenPartialHomeomorph.extend (𝓡∂ 3)).right_inv hw

private theorem retainedImmersion_model (k : CarrierModel)
    {M N : Type u} [TopologicalSpace M] [ChartedSpace k.Space M]
    [IsManifold k.model ∞ M]
    [TopologicalSpace N] [ChartedSpace (EuclideanHalfSpace 3) N]
    [IsManifold (𝓡∂ 3) ∞ N]
    (e : PartialDiffeomorph k.model (𝓡∂ 3) M N ∞) (f : N → M)
    (hf : ContMDiff (𝓡∂ 3) k.model ∞ f)
    (he : ∀ y ∈ e.target, f y = e.symm y) (x : N) (hx : x ∈ e.target) :
    IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 3) k.model ∞ f x := by
  cases k
  · apply (retainedInverseImmersion_closed e x hx).congr_of_eventuallyEq
    filter_upwards [e.open_target.mem_nhds hx] with y hy
    exact (he y hy).symm
  · let p := e.symm x
    have hp : p ∈ e.source := e.map_target hx
    have hid : IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 3) (𝓡∂ 3) ∞ id p :=
      IsImmersionOfComplement.id p
    have hcomp : IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 3) (𝓡∂ 3) ∞ (f ∘ e) p := by
      apply hid.congr_of_eventuallyEq
      filter_upwards [e.open_source.mem_nhds hp] with y hy
      exact ((he (e y) (e.map_source hy)).trans (e.left_inv hy)).symm
    have h := boundedParameterImmersion e f hf (Diffeomorph.refl (𝓡∂ 3) _ ∞)
      (ContinuousLinearEquiv.refl ℝ BoundedE3) (fun y => rfl) hp hcomp
    have hright : e p = x := e.right_inv hx
    exact hright ▸ h

private theorem annulusImmersion_model (k : CarrierModel)
    {N : Type u} [TopologicalSpace N] [ChartedSpace k.Space N] [IsManifold k.model ∞ N]
    (D : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) k.model
      (PlaneLift.{u} × Circle) N ∞) (x : productSet.{u} 2) (hx : x.val ∈ D.source) :
    IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 3) k.model ∞ (D ∘ Subtype.val) x := by
  cases k
  · exact annulusImmersion_closed D x hx
  · exact annulusImmersion_half D x hx

private theorem boundedExcisionVal_immersion (x : boundedExcisionSet C φ) :
    letI := boundedExcisionCharts C φ hφ
    IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 3) C.model ∞
      (Subtype.val : boundedExcisionSet C φ → C.Carrier) x := by
  let := boundedExcisionCharts C φ hφ
  have := boundedExcisionSmooth C φ hφ
  rcases boundedExcision_cover C φ hφ x with hx | hx
  · apply retainedImmersion_model C.kind (boundedExcisionPD C φ hφ false) Subtype.val
      (boundedExcisionVal_smooth C φ hφ) ?_ x hx
    intro y hy
    rfl
  · let e := boundedExcisionPD C φ hφ true
    let p := e.symm x
    have hp : p ∈ e.source := e.map_target hx
    have hn := annulusImmersion_model C.kind (annulusAmbient C φ) p hp
    have hc : IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 3) C.model ∞
        (Subtype.val ∘ e) p := by
      apply hn.congr_of_eventuallyEq
      filter_upwards [e.open_source.mem_nhds hp] with y hy
      exact (annulusPatch_apply C φ hφ y hy).symm
    have h := boundedParameterImmersion e Subtype.val (boundedExcisionVal_smooth C φ hφ)
      (Diffeomorph.refl (𝓡∂ 3) _ ∞) (ContinuousLinearEquiv.refl ℝ BoundedE3)
      (fun y => rfl) hp hc
    have hright : e p = x := e.right_inv hx
    exact hright ▸ h


@[instance_reducible]
def fibreExcisionBoundaryCarrier : CompactCarrier.{u} := by
  let := boundedExcisionCharts C φ hφ
  have := boundedExcisionSmooth C φ hφ
  let : CompactSpace (boundedExcisionSet C φ) :=
    isCompact_iff_compactSpace.mp (boundedExcision_compact C φ hφ)
  exact
    { kind := .withBoundary
      Carrier := boundedExcisionSet C φ
      orientation := manifoldOrientationPullback (𝓡∂ 3) C.model (by simp) Subtype.val
        (boundedExcisionVal_smooth C φ hφ) (boundedExcisionVal_mfderiv C φ hφ) C.orientation }

def fibreExcisionBoundaryInclusion : (fibreExcisionBoundaryCarrier C φ hφ).Carrier → C.Carrier :=
  Subtype.val

theorem fibreExcisionBoundaryInclusion_smoothEmbedding :
    IsSmoothEmbedding (fibreExcisionBoundaryCarrier C φ hφ).model C.model ∞
      (fibreExcisionBoundaryInclusion C φ hφ) := by
  let := boundedExcisionCharts C φ hφ
  have := boundedExcisionSmooth C φ hφ
  exact ⟨IsImmersionOfComplement.isImmersion (F := PUnit.{1})
      (fun x => boundedExcisionVal_immersion C φ hφ x),
    Topology.IsEmbedding.subtypeVal⟩

def fibreExcisionBoundaryRetained :
    PartialDiffeomorph C.model (fibreExcisionBoundaryCarrier C φ hφ).model
      C.Carrier (fibreExcisionBoundaryCarrier C φ hφ).Carrier ∞ :=
  boundedExcisionPD C φ hφ false

theorem fibreExcisionBoundaryRetained_source :
    (fibreExcisionBoundaryRetained C φ hφ).source =
      (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ := rfl

theorem fibreExcisionBoundaryRetained_target :
    (fibreExcisionBoundaryRetained C φ hφ).target =
      fibreExcisionBoundaryInclusion C φ hφ ⁻¹'
        (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ := rfl

theorem fibreExcisionBoundaryRetained_inclusion (x : C.Carrier)
    (hx : x ∈ (fibreExcisionBoundaryRetained C φ hφ).source) :
    fibreExcisionBoundaryInclusion C φ hφ (fibreExcisionBoundaryRetained C φ hφ x) = x :=
  boundedRetainedPatch_apply C φ hφ x hx

private def boundedTorusInv : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus where
  toFun t := (t.1⁻¹, t.2)
  invFun t := (t.1⁻¹, t.2)
  left_inv t := by simp
  right_inv t := by simp
  contMDiff_toFun := ((contMDiff_inv (𝓡 1) ∞).comp contMDiff_fst).prodMk contMDiff_snd
  contMDiff_invFun := ((contMDiff_inv (𝓡 1) ∞).comp contMDiff_fst).prodMk contMDiff_snd

private def boundedCollarInv :
    (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
      (Torus × EuclideanHalfSpace 1) :=
  boundedTorusInv.prodCongr (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)

def fibreExcisionBoundaryCollar :
    PartialDiffeomorph halfCollarModel (fibreExcisionBoundaryCarrier C φ hφ).model
      (Torus × EuclideanHalfSpace 1) (fibreExcisionBoundaryCarrier C φ hφ).Carrier ∞ :=
  (boundedCollarInv.toPartialDiffeomorph.trans
    (productCollar.{u} 2 (Or.inl rfl) (1 : Fin 2))).trans (boundedExcisionPD C φ hφ true)

private theorem innerProductCollar_val (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    (productCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) ((p.1.1⁻¹, p.1.2), p.2)).val =
      (ULift.up ((1 / 2 + p.2.val 0 / 4 : ℝ) • (p.1.1 : ℂ)), p.1.2) := by
  apply Prod.ext
  · apply ULift.ext
    change (planarCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) (p.1.1⁻¹, p.2)).val.down = _
    rw [planarCollar_apply_val (Or.inl rfl) (1 : Fin 2) hp]
    change (0 : ℂ) + (1 / 2 + (1 : ℝ) * p.2.val 0 / 4) • conj (↑p.1.1⁻¹ : ℂ) = _
    rw [Circle.coe_inv_eq_conj, Complex.conj_conj]
    simp only [zero_add, one_mul]
  · rfl

theorem fibreExcisionBoundaryCollar_source :
    (fibreExcisionBoundaryCollar C φ hφ).source = halfCollarSource := by
  let := boundedExcisionCharts C φ hφ
  ext p
  change ((p ∈ univ ∧ ((p.1.1⁻¹, p.1.2), p.2) ∈ halfCollarSource) ∧
    productCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) ((p.1.1⁻¹, p.1.2), p.2) ∈
      (annulusPatch C φ hφ).source) ↔ p ∈ halfCollarSource
  constructor
  · exact fun h => h.1.2
  · intro hp
    refine ⟨⟨mem_univ p, hp⟩, ?_⟩
    change (productCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) ((p.1.1⁻¹, p.1.2), p.2)).val ∈
      (annulusAmbient C φ).source
    rw [annulusAmbient_source C φ hφ, innerProductCollar_val p hp]
    change ‖(1 / 2 + p.2.val 0 / 4 : ℝ) • (p.1.1 : ℂ)‖ < 3 / 4
    rw [norm_smul, Real.norm_eq_abs, Circle.norm_coe]
    have hn := p.2.property
    change p.2.val 0 < 1 at hp
    rw [abs_of_nonneg (by linarith : 0 ≤ (1 / 2 + p.2.val 0 / 4 : ℝ))]
    linarith

theorem fibreExcisionBoundaryCollar_inclusion (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) :
    fibreExcisionBoundaryInclusion C φ hφ (fibreExcisionBoundaryCollar C φ hφ p) =
      φ (ULift.up ((1 + p.2.val 0 / 2 : ℝ) • (p.1.1 : ℂ)), p.1.2) := by
  let := boundedExcisionCharts C φ hφ
  have hs : p ∈ (fibreExcisionBoundaryCollar C φ hφ).source :=
    fibreExcisionBoundaryCollar_source C φ hφ ▸ hp
  have hz := hs.2
  change (annulusPatch C φ hφ
    (productCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) ((p.1.1⁻¹, p.1.2), p.2))).val = _
  have hv := annulusPatch_apply C φ hφ
    (productCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) ((p.1.1⁻¹, p.1.2), p.2)) hz
  refine hv.trans ?_
  change φ (boundedTwiceTube
    (productCollar.{u} 2 (Or.inl rfl) (1 : Fin 2) ((p.1.1⁻¹, p.1.2), p.2)).val) = _
  rw [innerProductCollar_val p hp]
  congr 1
  apply Prod.ext
  · apply ULift.ext
    change (2 : ℝ) • ((1 / 2 + p.2.val 0 / 4 : ℝ) • (p.1.1 : ℂ)) = _
    rw [smul_smul]
    congr 1
    ring
  · rfl


private theorem unitTube_image :
    φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ = 1} =
      range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2)) := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    let t : Circle := ⟨p.1.down, mem_sphere_zero_iff_norm.mpr hp⟩
    exact ⟨(t, p.2), rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨(ULift.up (t.1 : ℂ), t.2), Circle.norm_coe t.1, rfl⟩

theorem fibreExcisionBoundaryCollar_zero (t : Torus) :
    (fibreExcisionBoundaryCarrier C φ hφ).model.IsBoundaryPoint
      (fibreExcisionBoundaryCollar C φ hφ (t, halfZero)) := by
  let := boundedExcisionCharts C φ hφ
  have := boundedExcisionSmooth C φ hφ
  apply (boundedExcision_boundary_iff C φ hφ _).mpr
  apply Or.inr
  refine ⟨(ULift.up (t.1 : ℂ), t.2), Circle.norm_coe t.1, ?_⟩
  have he := fibreExcisionBoundaryCollar_inclusion C φ hφ (t, halfZero)
    (by change (0 : ℝ) < 1; norm_num)
  change φ (ULift.up (t.1 : ℂ), t.2) =
    fibreExcisionBoundaryInclusion C φ hφ (fibreExcisionBoundaryCollar C φ hφ (t, halfZero))
  simpa only [halfZero, halfPoint_val_zero, zero_div, add_zero, one_smul] using he.symm

theorem fibreExcisionBoundaryInclusion_boundary :
    fibreExcisionBoundaryInclusion C φ hφ ''
        (fibreExcisionBoundaryCarrier C φ hφ).model.boundary
          (fibreExcisionBoundaryCarrier C φ hφ).Carrier =
      C.model.boundary C.Carrier ∪
        range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2)) := by
  let := boundedExcisionCharts C φ hφ
  have := boundedExcisionSmooth C φ hφ
  rw [← unitTube_image C φ]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (boundedExcision_boundary_iff C φ hφ y).mp hy
  · intro hx
    have hxK : x ∈ boundedExcisionSet C φ := by
      rcases hx with hx | hx
      · exact boundedRetained_subset C φ (oldBoundary_boundedRetained C φ hφ x hx)
      · obtain ⟨z, hz, he⟩ := hx
        rintro ⟨w, hw, hew⟩
        have hzsrc : z ∈ φ.source := by
          apply hφ
          change ‖z.1.down‖ ≤ 3
          change ‖z.1.down‖ = 1 at hz
          rw [hz]
          norm_num
        have hwsrc : w ∈ φ.source := by
          apply hφ
          change ‖w.1.down‖ ≤ 3
          change ‖w.1.down‖ < 1 at hw
          linarith
        have heq := φ.injOn hwsrc hzsrc (hew.trans he.symm)
        rw [heq] at hw
        exact (ne_of_lt hw) hz
    exact ⟨⟨x, hxK⟩, (boundedExcision_boundary_iff C φ hφ ⟨x, hxK⟩).mpr hx, rfl⟩

include hφ in
theorem fibreExcisionBoundary_old_disjoint :
    Disjoint (C.model.boundary C.Carrier)
      (range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2))) := by
  rw [← unitTube_image C φ]
  apply Set.disjoint_left.mpr
  intro x hx hxnew
  obtain ⟨z, hz, he⟩ := hxnew
  have hzsrc : z ∈ φ.source := by
    apply hφ
    change ‖z.1.down‖ ≤ 3
    change ‖z.1.down‖ = 1 at hz
    rw [hz]
    norm_num
  have hi := baseChart_interior C φ x (he ▸ φ.map_source hzsrc)
  exact (C.model.isInteriorPoint_iff_not_isBoundaryPoint x).mp hi hx


theorem exists_fibreExcisionWithBoundary
    (C : CompactCarrier.{u})
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model
      (PlaneLift.{u} × Circle) C.Carrier ∞)
    (hφ : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source) :
    ∃ (K : CompactCarrier.{u}) (ι : K.Carrier → C.Carrier)
      (Γ : PartialDiffeomorph halfCollarModel K.model
        (Torus × EuclideanHalfSpace 1) K.Carrier ∞)
      (O : PartialDiffeomorph C.model K.model C.Carrier K.Carrier ∞),
      K.kind = .withBoundary ∧
      IsSmoothEmbedding K.model C.model ∞ ι ∧
      range ι = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ ∧
      (∀ x, Function.Bijective (mfderiv K.model C.model ι x)) ∧
      (∀ x, ∃ D : TangentSpace K.model x ≃L[ℝ] TangentSpace C.model (ι x),
        D.toContinuousLinearMap = mfderiv K.model C.model ι x ∧
        Orientation.map (Fin 3) D.toLinearEquiv (K.orientation.orientation x) =
          C.orientation.orientation (ι x)) ∧
      Γ.source = halfCollarSource ∧
      (∀ t, K.model.IsBoundaryPoint (Γ (t, halfZero))) ∧
      (∀ p, p ∈ halfCollarSource →
        ι (Γ p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2)) ∧
      ι '' K.model.boundary K.Carrier = C.model.boundary C.Carrier ∪
        range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2)) ∧
      Disjoint (C.model.boundary C.Carrier)
        (range (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2))) ∧
      O.source = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ ∧
      (∀ x, x ∈ O.source → ι (O x) = x) ∧
      O.target = ι ⁻¹' (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1})ᶜ := by
  let := boundedExcisionCharts C φ hφ
  have := boundedExcisionSmooth C φ hφ
  let K := fibreExcisionBoundaryCarrier C φ hφ
  let ι := fibreExcisionBoundaryInclusion C φ hφ
  let Γ := fibreExcisionBoundaryCollar C φ hφ
  let O := fibreExcisionBoundaryRetained C φ hφ
  refine ⟨K, ι, Γ, O, rfl, fibreExcisionBoundaryInclusion_smoothEmbedding C φ hφ,
    Subtype.range_coe, boundedExcisionVal_mfderiv C φ hφ, ?_,
    fibreExcisionBoundaryCollar_source C φ hφ, fibreExcisionBoundaryCollar_zero C φ hφ,
    fibreExcisionBoundaryCollar_inclusion C φ hφ,
    fibreExcisionBoundaryInclusion_boundary C φ hφ,
    fibreExcisionBoundary_old_disjoint C φ hφ, rfl,
    fibreExcisionBoundaryRetained_inclusion C φ hφ, rfl⟩
  intro x
  refine ⟨differentialEquivOfBijective (𝓡∂ 3) C.model Subtype.val
    (boundedExcisionVal_mfderiv C φ hφ) x, rfl, ?_⟩
  exact orientation_map_manifoldOrientationPullback (𝓡∂ 3) C.model (by simp)
    Subtype.val (boundedExcisionVal_smooth C φ hφ) (boundedExcisionVal_mfderiv C φ hφ)
    C.orientation x

end GC.GraphManifold.CircleFibration
