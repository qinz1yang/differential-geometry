import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryPortPairing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreExcision
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingDisc
import DifferentialGeometry.Topology.Manifold.ClosedOrientedPullback
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Orientation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgery

/-!
Restoration of the same regular-fibre tube by its actual radius-three filling disc.
The solid and retained collars use opposite radial halves of the same signed tube.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open GC.Endpoint.CompactCarrier GC.GraphManifold.TorusPairing
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

def regularFibreRestorationSolid
    (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3) : CompactCarrier.{u} :=
  { kind := .withBoundary
    Carrier := solidSet.{u}
    charts := inferInstance
    smooth := inferInstance
    orientation := O }

instance restorationSolid_nonempty (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3) :
    Nonempty (regularFibreRestorationSolid O).Carrier := inferInstanceAs (Nonempty solidSet.{u})

def regularFibreRestorationBoundary
    (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3) :
    BoundaryTori (regularFibreRestorationSolid O) 1 where
  collar j := solidCollar.{u} 1
  source_eq j := rfl
  boundary_zero j t := by
    change (𝓡∂ 3).IsBoundaryPoint (solidCollar.{u} 1 (t, halfZero))
    rw [solidSet_isBoundaryPoint_iff, solidCollar_zero_val]
    simp [Circle.norm_coe]
  disjoint i j hij := False.elim (hij (Subsingleton.elim i j))

theorem regularFibreRestorationBoundary_exhausted
    (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3) :
    (regularFibreRestorationSolid O).model.boundary (regularFibreRestorationSolid O).Carrier =
      (regularFibreRestorationBoundary O).image := by
  change (𝓡∂ 3).boundary solidSet = _
  rw [solidSet_boundary_eq 1]
  ext x
  change x ∈ range (fun t => solidCollar.{u} 1 (t, halfZero)) ↔
    x ∈ ⋃ j : Fin 1, range (fun t => solidCollar.{u} 1 (t, halfZero))
  constructor
  · rintro ⟨t, ht⟩
    exact mem_iUnion.mpr ⟨0, t, ht⟩
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    exact hj

private def restorationScale :
    (PlaneLift.{u} × Circle) ≃ₘ⟮𝓘(ℝ, ℂ).prod (𝓡 1),
      𝓘(ℝ, ℂ).prod (𝓡 1)⟯ (PlaneLift.{u} × Circle) where
  toFun x := (ULift.up ((1 / 3 : ℝ) • x.1.down), x.2)
  invFun x := (ULift.up ((3 : ℝ) • x.1.down), x.2)
  left_inv x := by
    apply Prod.ext
    · apply ULift.ext
      simp
    · rfl
  right_inv x := by
    apply Prod.ext
    · apply ULift.ext
      simp
    · rfl
  contMDiff_toFun := (contMDiff_planeLift_up.comp
    ((((1 / 3 : ℝ) • (ContinuousLinearMap.id ℝ ℂ)).contDiff.contMDiff).comp
      (contMDiff_planeLift_down.comp contMDiff_fst))).prodMk
      contMDiff_snd
  contMDiff_invFun := (contMDiff_planeLift_up.comp
    ((((3 : ℝ) • (ContinuousLinearMap.id ℝ ℂ)).contDiff.contMDiff).comp
      (contMDiff_planeLift_down.comp contMDiff_fst))).prodMk contMDiff_snd

variable (M : ConnectedClosedOrientedManifold.{u} 3)
variable (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
  (PlaneLift.{u} × Circle) M.Carrier ∞)
variable (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)

def regularFibreRestorationFill (x : solidSet.{u}) : M.Carrier :=
  φ (ULift.up (x.val.1.down / 3), x.val.2)

private theorem restorationScale_norm (x : solidSet.{u}) :
    ‖(restorationScale x.val).1.down‖ ≤ 1 := by
  change ‖(1 / 3 : ℝ) • x.val.1.down‖ ≤ 1
  rw [norm_smul]
  norm_num
  have hx := (mem_solidSet_iff x.val).mp x.property
  change ‖x.val.1‖ ≤ 3 at hx
  linarith

include h3

private theorem restorationFill_source (x : solidSet.{u}) :
    restorationScale x.val ∈ φ.source :=
  h3 ((restorationScale_norm x).trans (by norm_num))

omit h3 in
private theorem restorationFill_eq :
    regularFibreRestorationFill M φ =
      φ ∘ restorationScale ∘ (Subtype.val : solidSet.{u} → PlaneLift.{u} × Circle) := by
  funext x
  change φ (ULift.up (x.val.1.down / 3), x.val.2) =
    φ (ULift.up ((1 / 3 : ℝ) • x.val.1.down), x.val.2)
  congr 2
  apply ULift.ext
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

theorem regularFibreRestorationFill_smooth :
    ContMDiff (𝓡∂ 3) (𝓡 3) ∞ (regularFibreRestorationFill M φ) := by
  rw [restorationFill_eq]
  exact φ.contMDiffOn.comp_contMDiff
    (restorationScale.contMDiff.comp solidAtlas.contMDiff_subtype_val)
    (restorationFill_source M φ h3)

theorem regularFibreRestorationFill_injective :
    Injective (regularFibreRestorationFill M φ) := by
  intro x y hxy
  apply Subtype.ext
  apply restorationScale.injective
  apply φ.injOn (restorationFill_source M φ h3 x) (restorationFill_source M φ h3 y)
  simpa only [restorationFill_eq, Function.comp_apply] using hxy

omit h3 in
theorem regularFibreRestorationFill_range :
    range (regularFibreRestorationFill M φ) =
      φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 1} := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨restorationScale x.val, restorationScale_norm x,
      (congrFun (restorationFill_eq M φ) x).symm⟩
  · rintro ⟨p, hp, rfl⟩
    have hx : restorationScale.symm p ∈ solidSet := by
      rw [mem_solidSet_iff]
      change ‖(3 : ℝ) • p.1.down‖ ≤ 3
      rw [norm_smul]
      norm_num
      change ‖p.1‖ ≤ 1 at hp
      linarith
    refine ⟨⟨restorationScale.symm p, hx⟩, ?_⟩
    change φ (ULift.up (((3 : ℝ) • p.1.down) / 3), p.2) = φ p
    congr 2
    apply ULift.ext
    simp [Complex.real_smul]

omit h3 in
theorem regularFibreRestorationFill_collar {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    regularFibreRestorationFill M φ (solidCollar.{u} 1 p) =
      φ (ULift.up ((1 - p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2) := by
  unfold regularFibreRestorationFill
  rw [solidCollar_apply_val 1 hp]
  congr 2
  apply ULift.ext
  change (seamRadius 1 (-p.2.val 0) • (p.1.1 : ℂ)) / 3 = _
  simp only [seamRadius, Nat.cast_one, inv_one, Real.rpow_one]
  rw [Complex.real_smul]
  rw [Complex.real_smul]
  push_cast
  ring

theorem regularFibreRestorationFill_bijective_mfderiv (x : solidSet.{u}) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (regularFibreRestorationFill M φ) x) := by
  let f := restorationScale ∘ (Subtype.val : solidSet.{u} → PlaneLift.{u} × Circle)
  have hfs : ContMDiff (𝓡∂ 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) ∞ f :=
    restorationScale.contMDiff.comp solidAtlas.contMDiff_subtype_val
  have hs : Bijective (mfderiv (𝓡∂ 3) (𝓘(ℝ, ℂ).prod (𝓡 1)) f x) := by
    rw [mfderiv_comp x (restorationScale.contMDiff.mdifferentiableAt (by simp))
      (solidAtlas.contMDiff_subtype_val.mdifferentiableAt (by simp))]
    exact ((restorationScale.mfderivToContinuousLinearEquiv (by simp) x.val).bijective).comp
      (solidAtlas.mfderiv_subtypeVal_bijective x)
  have he : regularFibreRestorationFill M φ = φ ∘ f := restorationFill_eq M φ
  rw [he]
  rw [mfderiv_comp x (φ.mdifferentiableAt (by simp) (restorationFill_source M φ h3 x))
    (hfs.mdifferentiableAt (by simp))]
  exact (carrierSurgeryPatchTangentEquiv φ
    (restorationFill_source M φ h3 x)).bijective.comp hs

variable (K : CompactCarrier.{u}) (ι : K.Carrier → M.Carrier)
variable (Γ : BoundaryTori K 1) (hK : K.kind = .withBoundary)
variable (hι : IsSmoothEmbedding K.model (𝓡 3) ∞ ι)
variable (hr : range ι = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ)
variable (hΓ : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
  ι (Γ.collar 0 p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
variable (O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3)
variable [Nonempty K.Carrier]

private abbrev restorationGluing :=
  boundaryPortGluing (regularFibreRestorationSolid O) K rfl hK
    (regularFibreRestorationBoundary O) Γ (Diffeomorph.refl torusModel Torus ∞)

private def restorationFold :
    (regularFibreRestorationSolid O).Carrier ⊕ K.Carrier → M.Carrier :=
  Sum.elim (regularFibreRestorationFill M φ) ι

include hΓ in
omit h3 [Nonempty K.Carrier] in
private theorem restorationFold_zero (t : Torus) :
    restorationFold M φ K ι O (Sum.inl (solidCollar.{u} 1 (t, halfZero))) =
      restorationFold M φ K ι O (Sum.inr (Γ.collar 0 (t, halfZero))) := by
  change regularFibreRestorationFill M φ (solidCollar.{u} 1 (t, halfZero)) =
    ι (Γ.collar 0 (t, halfZero))
  rw [regularFibreRestorationFill_collar M φ (zero_mem_halfCollarSource t),
    hΓ (t, halfZero) (zero_mem_halfCollarSource t)]
  simp only [show halfZero.val 0 = 0 from rfl, zero_div, sub_zero, add_zero]

include hι hr hΓ in
omit [Nonempty K.Carrier] in
private theorem restorationFold_cross {x : solidSet.{u}} {y : K.Carrier}
    (he : regularFibreRestorationFill M φ x = ι y) :
    ∃ t : Torus, x = solidCollar.{u} 1 (t, halfZero) ∧ y = Γ.collar 0 (t, halfZero) := by
  let p := restorationScale x.val
  have hp : ‖p.1.down‖ ≤ 1 := restorationScale_norm x
  have hn : ¬ ‖p.1.down‖ < 1 := by
    intro hn
    have hy : ι y ∈ (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ :=
      hr ▸ mem_range_self y
    apply hy
    refine ⟨p, hn, ?_⟩
    exact (congrFun (restorationFill_eq M φ) x).symm.trans he
  have hnorm : ‖p.1.down‖ = 1 := le_antisymm hp (le_of_not_gt hn)
  let t : Torus := (unitOf p.1.down, p.2)
  have ht : (ULift.up ((1 : ℝ) • (t.1 : ℂ)), t.2) = p := by
    apply Prod.ext
    · apply ULift.ext
      change (1 : ℝ) • (unitOf p.1.down : ℂ) = p.1.down
      rw [← hnorm]
      exact norm_smul_unitOf p.1.down
    · rfl
  have hx : x = solidCollar.{u} 1 (t, halfZero) := by
    apply regularFibreRestorationFill_injective M φ h3
    rw [regularFibreRestorationFill_collar M φ (zero_mem_halfCollarSource t)]
    simpa only [show halfZero.val 0 = 0 from rfl, zero_div, sub_zero, ht] using
      (show regularFibreRestorationFill M φ x = φ p from
        congrFun (restorationFill_eq M φ) x)
  refine ⟨t, hx, hι.isEmbedding.injective ?_⟩
  rw [hΓ (t, halfZero) (zero_mem_halfCollarSource t)]
  rw [← he, hx, regularFibreRestorationFill_collar M φ (zero_mem_halfCollarSource t)]
  simp only [show halfZero.val 0 = 0 from rfl, zero_div, sub_zero, add_zero]

set_option backward.isDefEq.respectTransparency false in
omit h3 [Nonempty K.Carrier] in
private theorem restorationGluing_attaching (t : Torus) :
    ((restorationGluing K Γ hK O).attaching 0
      ⟨Sum.inl (solidCollar.{u} 1 (t, halfZero)),
        ⟨t, rfl⟩⟩).val =
      Sum.inr (Γ.collar 0 (t, halfZero)) := by
  let E := regularFibreRestorationBoundary O
  have hi : _root_.Topology.IsEmbedding
      (Sum.inl : solidSet.{u} → solidSet.{u} ⊕ K.Carrier) := _root_.Topology.IsEmbedding.inl
  let e := (hi.comp (E.torusMap_isEmbedding 0)).toHomeomorph
  change Sum.inr (Γ.collar 0
    (e.symm ⟨Sum.inl (solidCollar.{u} 1 (t, halfZero)), ⟨t, rfl⟩⟩, halfZero)) = _
  have he : (⟨Sum.inl (solidCollar.{u} 1 (t, halfZero)), ⟨t, rfl⟩⟩ :
      range (fun t => Sum.inl (E.torusMap 0 t))) = e t := Subtype.ext rfl
  rw [he, Homeomorph.symm_apply_apply]

include hΓ in
omit h3 [Nonempty K.Carrier] in
private theorem restorationGluing_attaching_fold
    (z : (restorationGluing K Γ hK O).left 0) :
    restorationFold M φ K ι O z.val =
      restorationFold M φ K ι O ((restorationGluing K Γ hK O).attaching 0 z).val := by
  obtain ⟨t, ht⟩ := z.property
  have hz : z = ⟨Sum.inl (solidCollar.{u} 1 (t, halfZero)), by
      exact ⟨t, rfl⟩⟩ := Subtype.ext ht.symm
  rw [hz, restorationGluing_attaching]
  exact restorationFold_zero M φ K ι Γ hΓ O t

include hΓ in
omit h3 [Nonempty K.Carrier] in
private theorem restorationFold_respects {x y :
    (regularFibreRestorationSolid O).Carrier ⊕ K.Carrier}
    (hxy : (restorationGluing K Γ hK O).rel x y) :
    restorationFold M φ K ι O x = restorationFold M φ K ι O y := by
  rcases hxy with rfl | ⟨j, hx, rfl⟩
  · rfl
  have hj : j = 0 := Subsingleton.elim j 0
  subst j
  rcases hx with hx | hx
  · rw [(restorationGluing K Γ hK O).flip_of_mem_left hx]
    exact restorationGluing_attaching_fold M φ K ι Γ hK hΓ O ⟨x, hx⟩
  · rw [(restorationGluing K Γ hK O).flip_of_mem_right hx]
    have he := restorationGluing_attaching_fold M φ K ι Γ hK hΓ O
      (((restorationGluing K Γ hK O).attaching 0).symm ⟨x, hx⟩)
    simpa only [Homeomorph.apply_symm_apply] using he.symm

private def restorationQuotientFold : Quotient (restorationGluing K Γ hK O).setoid →
    M.Carrier := Quotient.lift (restorationFold M φ K ι O)
      (fun x y (hxy : (restorationGluing K Γ hK O).rel x y) =>
        restorationFold_respects M φ K ι Γ hK hΓ O hxy)

omit h3 [Nonempty K.Carrier] in
private theorem restorationGluing_zero_eq (t : Torus) :
    (Quotient.mk'' (Sum.inl (solidCollar.{u} 1 (t, halfZero))) :
      Quotient (restorationGluing K Γ hK O).setoid) =
        Quotient.mk'' (Sum.inr (Γ.collar 0 (t, halfZero))) := by
  apply Quotient.sound
  change (restorationGluing K Γ hK O).rel _ _
  have he := (restorationGluing K Γ hK O).rel_of_mem_left
    (show Sum.inl (solidCollar.{u} 1 (t, halfZero)) ∈
      (restorationGluing K Γ hK O).left 0 from ⟨t, rfl⟩)
  exact (restorationGluing_attaching K Γ hK O t) ▸ he

include hι hr hΓ in
omit [Nonempty K.Carrier] in
private theorem restorationQuotientFold_injective :
    Injective (restorationQuotientFold M φ K ι Γ hK hΓ O) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      intro hxy
      cases x with
      | inl x =>
        cases y with
        | inl y =>
          have he := regularFibreRestorationFill_injective M φ h3 hxy
          exact congrArg Quotient.mk'' (congrArg Sum.inl he)
        | inr y =>
          obtain ⟨t, rfl, rfl⟩ := restorationFold_cross M φ h3 K ι Γ hι hr hΓ hxy
          exact restorationGluing_zero_eq K Γ hK O t
      | inr x =>
        cases y with
        | inl y =>
          obtain ⟨t, rfl, rfl⟩ := restorationFold_cross M φ h3 K ι Γ hι hr hΓ hxy.symm
          exact (restorationGluing_zero_eq K Γ hK O t).symm
        | inr y =>
          exact congrArg Quotient.mk'' (congrArg Sum.inr (hι.isEmbedding.injective hxy))

include hr hΓ in
omit h3 [Nonempty K.Carrier] in
private theorem restorationQuotientFold_surjective :
    Surjective (restorationQuotientFold M φ K ι Γ hK hΓ O) := by
  classical
  intro y
  by_cases hy : y ∈ φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1}
  · have hy' : y ∈ range (regularFibreRestorationFill M φ) := by
      rw [regularFibreRestorationFill_range M φ]
      obtain ⟨p, hp, he⟩ := hy
      exact ⟨p, (show ‖p.1.down‖ < 1 from hp).le, he⟩
    obtain ⟨x, rfl⟩ := hy'
    exact ⟨Quotient.mk'' (Sum.inl x), rfl⟩
  · have hy' : y ∈ range ι := hr.symm ▸ hy
    obtain ⟨x, rfl⟩ := hy'
    exact ⟨Quotient.mk'' (Sum.inr x), rfl⟩

include hι hΓ in
omit [Nonempty K.Carrier] in
private theorem restorationQuotientFold_continuous :
    Continuous (restorationQuotientFold M φ K ι Γ hK hΓ O) := by
  exact ((regularFibreRestorationFill_smooth M φ h3).continuous.sumElim
    hι.contMDiff.continuous).quotient_lift
      (fun x y (hxy : (restorationGluing K Γ hK O).rel x y) =>
        restorationFold_respects M φ K ι Γ hK hΓ O hxy)

private def restorationQuotientHomeomorph :
    Quotient (restorationGluing K Γ hK O).setoid ≃ₜ M.Carrier :=
  (Equiv.ofBijective (restorationQuotientFold M φ K ι Γ hK hΓ O)
    ⟨restorationQuotientFold_injective M φ h3 K ι Γ hK hι hr hΓ O,
      restorationQuotientFold_surjective M φ K ι Γ hK hr hΓ O⟩).toHomeomorphOfContinuousClosed
    (restorationQuotientFold_continuous M φ h3 K ι Γ hK hι hΓ O)
    (restorationQuotientFold_continuous M φ h3 K ι Γ hK hι hΓ O).isClosedMap

private theorem restorationSolid_orientation_exists :
    ∃ O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3,
      ∀ x, Orientation.map (Fin 3)
        (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) (regularFibreRestorationFill M φ)
          (regularFibreRestorationFill_bijective_mfderiv M φ h3) x).toLinearEquiv
        (O.orientation x) = M.orientation.orientation (regularFibreRestorationFill M φ x) :=
  exists_manifoldOrientation_pullback (𝓡∂ 3) (𝓡 3) (by simp)
    (regularFibreRestorationFill M φ) (regularFibreRestorationFill_smooth M φ h3)
    (regularFibreRestorationFill_bijective_mfderiv M φ h3) M.orientation

private theorem restorationSigned_mem (p : Torus × ℝ) (hp : p ∈ signedCollarSource) :
    p ∈ (CircleFibration.fibreExcisionPolar.trans φ).source := by
  have hs : -1 < p.2 ∧ p.2 < 1 := hp
  refine ⟨by change -2 < p.2; linarith, h3 ?_⟩
  change ‖(1 + p.2 / 2) • (p.1.1 : ℂ)‖ ≤ 3
  rw [norm_smul, Circle.norm_coe, mul_one, Real.norm_of_nonneg (by linarith)]
  linarith

def regularFibreRestorationSignedTube :
    PartialDiffeomorph signedCollarModel (𝓡 3) (Torus × ℝ) M.Carrier ∞ :=
  PartialDiffeomorph.restrict (CircleFibration.fibreExcisionPolar.trans φ)
    signedCollarSource isOpen_signedCollarSource

theorem regularFibreRestorationSignedTube_source :
    (regularFibreRestorationSignedTube M φ).source = signedCollarSource := by
  ext p
  change (p ∈ (CircleFibration.fibreExcisionPolar.trans φ).source ∧
    p ∈ signedCollarSource) ↔ p ∈ signedCollarSource
  exact ⟨And.right, fun hp => ⟨restorationSigned_mem M φ h3 p hp, hp⟩⟩

omit h3 in
theorem regularFibreRestorationSignedTube_apply (p : Torus × ℝ) :
    regularFibreRestorationSignedTube M φ p =
      φ (ULift.up ((1 + p.2 / 2) • (p.1.1 : ℂ)), p.1.2) := rfl

private theorem restorationCollar_derivative {C : CompactCarrier.{u}}
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
  have ha : (t, (0 : ℝ)) ∈ (regularFibreRestorationSignedTube M φ).source := by
    rw [regularFibreRestorationSignedTube_source M φ h3]
    change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
    norm_num
  have hzero : surgeryHalfSignedCoordinate σ (t, halfZero) = (t, 0) := by
    change (t, σ * halfZero.val 0) = (t, 0)
    simp only [show halfZero.val 0 = 0 from rfl, mul_zero]
  have hg : f ∘ c =ᶠ[𝓝 (t, halfZero)]
      regularFibreRestorationSignedTube M φ ∘ surgeryHalfSignedCoordinate σ := by
    filter_upwards [surgeryHalfDomain.isOpen.mem_nhds (zero_mem_halfCollarSource t)] with p hp
    exact he p hp
  have hd := hg.mfderiv_eq (I := halfCollarModel) (I' := 𝓡 3)
  rw [mfderiv_comp (t, halfZero) (hf.mdifferentiableAt (by simp))
    (c.mdifferentiableAt (by simp) hp),
    mfderiv_comp (t, halfZero)
      ((regularFibreRestorationSignedTube M φ).mdifferentiableAt (by simp) (hzero.symm ▸ ha))
      ((surgeryHalfSignedCoordinate_contMDiff σ).mdifferentiableAt (by simp)), hzero] at hd
  exact hd

omit h3 in
private theorem restorationOrientation_inverse {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E ≃ₗ[ℝ] F) (o : Orientation ℝ E (Fin 3)) (o' : Orientation ℝ F (Fin 3))
    (h : Orientation.map (Fin 3) L o = o') : Orientation.map (Fin 3) L.symm o' = o := by
  rw [← h]
  exact (Orientation.map (Fin 3) L).symm_apply_apply o

omit h3 in
private theorem restorationSigned_inverse_negative
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (B : E ≃ₗ[ℝ] ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ))
    (D : ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × ℝ) ≃ₗ[ℝ] F)
    (o : Orientation ℝ F (Fin 3)) :
    Orientation.map (Fin 3) ((B.trans surgerySignedNormalReflection).trans D).symm o =
      -Orientation.map (Fin 3) (B.trans D).symm o := by
  have hi : surgerySignedNormalReflection.symm = surgerySignedNormalReflection := by
    ext v <;> simp [surgerySignedNormalReflection]
  rw [LinearEquiv.trans_symm, LinearEquiv.trans_symm,
    DifferentialGeometry.orientation_map_trans, DifferentialGeometry.orientation_map_trans, hi,
    surgerySignedNormalReflection_map, Orientation.map_neg,
    LinearEquiv.trans_symm, DifferentialGeometry.orientation_map_trans]

omit h3 in
private theorem restorationOrientation_comp_inverse {E F H : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    [AddCommGroup H] [Module ℝ H]
    (L : E ≃ₗ[ℝ] F) (R : F ≃ₗ[ℝ] H)
    (o : Orientation ℝ F (Fin 3)) (o' : Orientation ℝ H (Fin 3))
    (h : Orientation.map (Fin 3) R o = o') :
    Orientation.map (Fin 3) L.symm o = Orientation.map (Fin 3) (L.trans R).symm o' := by
  rw [LinearEquiv.trans_symm, DifferentialGeometry.orientation_map_trans,
    restorationOrientation_inverse R o o' h]

set_option backward.isDefEq.respectTransparency false in
include hι hΓ in
omit [Nonempty K.Carrier] in
private theorem restorationNative_reversing
    (hFO : ∀ x, Orientation.map (Fin 3)
      (differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) (regularFibreRestorationFill M φ)
        (regularFibreRestorationFill_bijective_mfderiv M φ h3) x).toLinearEquiv
      (O.orientation x) = M.orientation.orientation (regularFibreRestorationFill M φ x))
    (hKO : ∀ x, ∃ H : TangentSpace K.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι x),
      H.toContinuousLinearMap = mfderiv K.model (𝓡 3) ι x ∧
      Orientation.map (Fin 3) H.toLinearEquiv (K.orientation.orientation x) =
        M.orientation.orientation (ι x)) (t : Torus) :
    Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv (solidCollar.{u} 1)
      (zero_mem_halfCollarSource t)).symm (O.orientation (solidCollar.{u} 1 (t, halfZero))) =
    -Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv (Γ.collar 0)
      ((Γ.source_eq 0).symm ▸ zero_mem_halfCollarSource t)).symm
      (K.orientation.orientation (Γ.collar 0 (t, halfZero))) := by
  let p := (t, halfZero)
  let l := carrierSurgeryPatchTangentEquiv (solidCollar.{u} 1) (zero_mem_halfCollarSource t)
  let r := carrierSurgeryPatchTangentEquiv (Γ.collar 0)
    ((Γ.source_eq 0).symm ▸ zero_mem_halfCollarSource t)
  let F := differentialEquivOfBijective (𝓡∂ 3) (𝓡 3) (regularFibreRestorationFill M φ)
    (regularFibreRestorationFill_bijective_mfderiv M φ h3) (solidCollar.{u} 1 p)
  obtain ⟨H, hH, hHO⟩ := hKO (Γ.collar 0 p)
  have hp : (t, (0 : ℝ)) ∈ (regularFibreRestorationSignedTube M φ).source := by
    rw [regularFibreRestorationSignedTube_source M φ h3]
    change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
    norm_num
  let A := carrierSurgeryPatchTangentEquiv (regularFibreRestorationSignedTube M φ) hp
  let B := surgeryHalfSignedTangent 1 (by norm_num) p
  have hl : l.trans F.toLinearEquiv =
      (surgeryHalfSignedTangent (-1) (by norm_num) p).trans A := by
    have hd := restorationCollar_derivative M φ h3 (C := regularFibreRestorationSolid O)
      (solidCollar.{u} 1) rfl (regularFibreRestorationFill M φ)
      (regularFibreRestorationFill_smooth M φ h3) (-1) (fun q hq => by
        rw [regularFibreRestorationFill_collar M φ hq,
          regularFibreRestorationSignedTube_apply]
        congr 2
        apply ULift.ext
        change (1 - q.2.val 0 / 2) • (q.1.1 : ℂ) =
          (1 + (-1 * q.2.val 0) / 2) • (q.1.1 : ℂ)
        congr 1
        ring) t
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun L => L v) hd
  have hr' : r.trans H.toLinearEquiv = B.trans A := by
    have hd := restorationCollar_derivative M φ h3 (Γ.collar 0) (Γ.source_eq 0) ι
      hι.contMDiff 1 (fun q hq => by
        rw [hΓ q hq, regularFibreRestorationSignedTube_apply]
        change φ (ULift.up ((1 + q.2.val 0 / 2) • (q.1.1 : ℂ)), q.1.2) =
          φ (ULift.up ((1 + (1 * q.2.val 0) / 2) • (q.1.1 : ℂ)), q.1.2)
        rw [one_mul]) t
    apply LinearEquiv.ext
    intro v
    change H (r v) = A (B v)
    rw [← ContinuousLinearEquiv.coe_coe, hH]
    exact congrArg (fun L => L v) hd
  have hpoint : regularFibreRestorationFill M φ (solidCollar.{u} 1 p) = ι (Γ.collar 0 p) :=
    restorationFold_zero M φ K ι Γ hΓ O t
  change Orientation.map (Fin 3) l.symm (O.orientation (solidCollar.{u} 1 p)) =
    -Orientation.map (Fin 3) r.symm (K.orientation.orientation (Γ.collar 0 p))
  rw [restorationOrientation_comp_inverse l F.toLinearEquiv _ _
    (hFO (solidCollar.{u} 1 p)), restorationOrientation_comp_inverse r H.toLinearEquiv _ _ hHO,
    hpoint, hl, hr', surgeryHalfSignedTangent_negative]
  exact restorationSigned_inverse_negative B A (M.orientation.orientation (ι (Γ.collar 0 p)))

set_option backward.isDefEq.respectTransparency false in
omit h3 in
private theorem restorationSum_reversing
    (hnative : ∀ t : Torus,
      Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv (solidCollar.{u} 1)
        (zero_mem_halfCollarSource t)).symm (O.orientation (solidCollar.{u} 1 (t, halfZero))) =
      -Orientation.map (Fin 3) (carrierSurgeryPatchTangentEquiv (Γ.collar 0)
        ((Γ.source_eq 0).symm ▸ zero_mem_halfCollarSource t)).symm
        (K.orientation.orientation (Γ.collar 0 (t, halfZero)))) :
    ReversesBoundaryOrientation (withBoundarySum (regularFibreRestorationSolid O) K rfl hK)
      (boundaryPortLeftCollar (regularFibreRestorationSolid O) K rfl hK
        (regularFibreRestorationBoundary O))
      (fun p => boundaryPortRightCollar (regularFibreRestorationSolid O) K rfl hK Γ 0 p) := by
  intro t
  let V := regularFibreRestorationSolid O
  let S := withBoundarySum V K rfl hK
  let p := (t, halfZero)
  let l := carrierSurgeryPatchTangentEquiv (solidCollar.{u} 1) (zero_mem_halfCollarSource t)
  let r := carrierSurgeryPatchTangentEquiv (Γ.collar 0)
    ((Γ.source_eq 0).symm ▸ zero_mem_halfCollarSource t)
  let L := withBoundarySumLeft V K rfl hK
  let R := withBoundarySumRight V K rfl hK
  obtain ⟨A, hA, hAO⟩ := withBoundarySumLeft_positive V K rfl hK (solidCollar.{u} 1 p)
  obtain ⟨B, hB, hBO⟩ := withBoundarySumRight_positive V K rfl hK (Γ.collar 0 p)
  have hl : (boundaryPortLeftCollar V K rfl hK (regularFibreRestorationBoundary O) :
      Torus × EuclideanHalfSpace 1 → S.Carrier) = L ∘ solidCollar.{u} 1 := rfl
  have hr' : (fun p => boundaryPortRightCollar V K rfl hK Γ 0 p) = R ∘ Γ.collar 0 := rfl
  have hLs : solidCollar.{u} 1 p ∈ L.source := by
    change _ ∈ (withBoundarySumLeft V K rfl hK).source
    rw [withBoundarySumLeft_source]
    trivial
  have hRs : Γ.collar 0 p ∈ R.source := by
    change _ ∈ (withBoundarySumRight V K rfl hK).source
    rw [withBoundarySumRight_source]
    trivial
  refine ⟨l.trans A, r.trans B, ?_, ?_, ?_⟩
  · intro v
    rw [hl, mfderiv_comp p
      (L.mdifferentiableAt (by simp) hLs)
      ((solidCollar.{u} 1).mdifferentiableAt (by simp) (zero_mem_halfCollarSource t))]
    exact hA (l v)
  · intro v
    rw [hr', mfderiv_comp p
      (R.mdifferentiableAt (by simp) hRs)
      ((Γ.collar 0).mdifferentiableAt (by simp)
        ((Γ.source_eq 0).symm ▸ zero_mem_halfCollarSource t))]
    exact hB (r v)
  · change Orientation.map (Fin 3) (l.trans A).symm
      (S.orientation.orientation (L (solidCollar.{u} 1 p))) =
      -Orientation.map (Fin 3) (r.trans B).symm
        (S.orientation.orientation (R (Γ.collar 0 p)))
    rw [← restorationOrientation_comp_inverse l A _ _ hAO,
      ← restorationOrientation_comp_inverse r B _ _ hBO]
    exact hnative t

private instance restorationSumCharts :
    ChartedSpace (withBoundarySum (regularFibreRestorationSolid O) K rfl hK).kind.Space
      ((regularFibreRestorationSolid O).Carrier ⊕ K.Carrier) :=
  (withBoundarySum (regularFibreRestorationSolid O) K rfl hK).charts

private instance restorationSumSmooth :
    IsManifold (withBoundarySum (regularFibreRestorationSolid O) K rfl hK).model ∞
      ((regularFibreRestorationSolid O).Carrier ⊕ K.Carrier) :=
  (withBoundarySum (regularFibreRestorationSolid O) K rfl hK).smooth

include hι hK in
private theorem restorationFold_smooth :
    ContMDiff (withBoundarySum (regularFibreRestorationSolid O) K rfl hK).model (𝓡 3) ∞
      (restorationFold M φ K ι O) := by
  have hf := regularFibreRestorationFill_smooth M φ h3
  have hi := hι.contMDiff
  cases K with
  | mk k A OK =>
    cases hK
    exact hf.sumElim hi

variable (hb : K.model.boundary K.Carrier = Γ.image)
variable (hbij : ∀ x, Bijective (mfderiv K.model (𝓡 3) ι x))
variable (hO : ∀ x, ∃ H : TangentSpace K.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι x),
  H.toContinuousLinearMap = mfderiv K.model (𝓡 3) ι x ∧
  Orientation.map (Fin 3) H.toLinearEquiv (K.orientation.orientation x) =
    M.orientation.orientation (ι x))

include hO in
omit h3 [Nonempty K.Carrier] in
private theorem restorationRetained_orientation (x : K.Carrier) :
    Orientation.map (Fin 3) (differentialEquivOfBijective K.model (𝓡 3) ι hbij x).toLinearEquiv
      (K.orientation.orientation x) = M.orientation.orientation (ι x) := by
  obtain ⟨H, hH, hHO⟩ := hO x
  have he : H = differentialEquivOfBijective K.model (𝓡 3) ι hbij x := by
    apply DFunLike.ext
    intro v
    change H.toContinuousLinearMap v = mfderiv K.model (𝓡 3) ι x v
    rw [hH]
  rw [← he]
  exact hHO

set_option backward.isDefEq.respectTransparency false in
include hι hr hΓ hb hbij hO in
private theorem restoration_complete :
    ∃ O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3,
    let V := regularFibreRestorationSolid O
    let E := regularFibreRestorationBoundary O
    let S := withBoundarySum V K rfl hK
    ∃ hrev : ReversesBoundaryOrientation S
      (boundaryPortLeftCollar V K rfl hK E)
      (fun p => boundaryPortRightCollar V K rfl hK Γ 0 p),
    let P := boundaryPortPairing V K rfl hK E Γ (Diffeomorph.refl torusModel Torus ∞) hrev
    S.model.boundary S.Carrier = (⋃ j, P.gluing.block j) ∧
    ∃ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (ρ : P.QuotientSpace ≃ₜ Q.Carrier)
      (e : Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier),
      e.preservesOrientation Q.orientation M.orientation ∧
      ContMDiff S.model (𝓡 3) ∞ (ρ ∘ P.quotientMap) ∧
      (∀ x : solidSet.{u}, e (ρ (P.quotientMap (Sum.inl x))) =
        regularFibreRestorationFill M φ x) ∧
      (∀ x : K.Carrier, e (ρ (P.quotientMap (Sum.inr x))) = ι x) := by
  obtain ⟨O, hFO⟩ := restorationSolid_orientation_exists M φ h3
  let V := regularFibreRestorationSolid O
  let E := regularFibreRestorationBoundary O
  let S := withBoundarySum V K rfl hK
  have hKO (x : K.Carrier) : ∃ H : TangentSpace K.model x ≃L[ℝ] TangentSpace (𝓡 3) (ι x),
      H.toContinuousLinearMap = mfderiv K.model (𝓡 3) ι x ∧
      Orientation.map (Fin 3) H.toLinearEquiv (K.orientation.orientation x) =
        M.orientation.orientation (ι x) :=
    ⟨differentialEquivOfBijective K.model (𝓡 3) ι hbij x, rfl,
      restorationRetained_orientation M K ι hbij hO x⟩
  have hn := restorationNative_reversing M φ h3 K ι Γ hι hΓ O hFO hKO
  have hrev := restorationSum_reversing K Γ hK O hn
  let P := boundaryPortPairing V K rfl hK E Γ (Diffeomorph.refl torusModel Torus ∞) hrev
  have hbP : S.model.boundary S.Carrier = ⋃ j, P.gluing.block j := by
    have he : (boundaryPortRemaining V K rfl hK (n := 0) Γ).image = ∅ := by
      ext x
      simp only [BoundaryTori.image, iUnion_of_empty, mem_empty_iff_false]
    have h := boundaryPortPairing_boundary V K rfl hK E Γ
      (Diffeomorph.refl torusModel Torus ∞) hrev (regularFibreRestorationBoundary_exhausted O) hb
    rw [he, union_empty] at h
    exact h
  let h : P.QuotientSpace ≃ₜ M.Carrier :=
    restorationQuotientHomeomorph M φ h3 K ι Γ hK hι hr hΓ O
  let Q := ConnectedClosedOrientedManifold.pullback M h
  let ρ : P.QuotientSpace ≃ₜ Q.Carrier := Homeomorph.refl P.QuotientSpace
  let e : Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier :=
    (ConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph M h).val
  have heq (x : S.Carrier) : e (ρ (P.quotientMap x)) = restorationFold M φ K ι O x := rfl
  have hq : (ρ ∘ P.quotientMap : S.Carrier → Q.Carrier) =
      e.symm ∘ restorationFold M φ K ι O := by
    funext x
    exact (e.symm_apply_apply (ρ (P.quotientMap x))).symm.trans
      (congrArg e.symm (heq x))
  refine ⟨O, hrev, hbP, Q, ρ, e, ?_, ?_, ?_, ?_⟩
  · exact (ConnectedClosedOrientedManifold.pullbackOrientedDiffeomorph M h).property
  · rw [hq]
    exact e.symm.contMDiff.comp (restorationFold_smooth M φ h3 K ι hK hι O)
  · intro x
    exact heq (Sum.inl x)
  · intro x
    exact heq (Sum.inr x)

include hι hr hΓ hb hbij hO in
omit [Nonempty K.Carrier] in
theorem exists_regularFibreRestoration :
    letI : Nonempty K.Carrier := ⟨Γ.collar 0 (torusBase, halfZero)⟩
    ∃ O : ManifoldOrientation (𝓡∂ 3) solidSet.{u} 3,
    let V := regularFibreRestorationSolid O
    let E := regularFibreRestorationBoundary O
    let S := withBoundarySum V K rfl hK
    ∃ hrev : ReversesBoundaryOrientation S
      (boundaryPortLeftCollar V K rfl hK E)
      (fun p => boundaryPortRightCollar V K rfl hK Γ 0 p),
    let P := boundaryPortPairing V K rfl hK E Γ (Diffeomorph.refl torusModel Torus ∞) hrev
    ∃ (Q : ConnectedClosedOrientedManifold.{u} 3)
      (ρ : P.QuotientSpace ≃ₜ Q.Carrier)
      (e : Q.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ M.Carrier),
      e.preservesOrientation Q.orientation M.orientation ∧
      ContMDiff S.model (𝓡 3) ∞ (ρ ∘ P.quotientMap) ∧
      (∀ x : solidSet.{u}, e (ρ (P.quotientMap (Sum.inl x))) =
        regularFibreRestorationFill M φ x) ∧
      (∀ x : K.Carrier, e (ρ (P.quotientMap (Sum.inr x))) = ι x) := by
  let : Nonempty K.Carrier := ⟨Γ.collar 0 (torusBase, halfZero)⟩
  obtain ⟨O, hrev, hwhole⟩ := restoration_complete M φ h3 K ι Γ hK hι hr hΓ hb hbij hO
  exact ⟨O, hrev, hwhole.2⟩

end GC.GraphManifold
