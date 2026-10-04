import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugSideCover
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Interior
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FibreCoordinate

/-!
The complete bounded side solid map is a genuine diffeomorphism onto its actual capped component.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.ElementaryPresentation

open SplitTube

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  (hlin : E.IsLinearSeam j)
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))
  (hc : E.toTorus.components.count = 2) (hn : E.toTorus.pairing.count = 1)
  {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
  (havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target)

abbrev boundedPlugSideComponent (t : Bool) :=
  (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece
    (boundedPlugSideSolidIndex t)

def boundedPlugSideComponentMap (t : Bool) (x : solidSet.{u}) :
    E.boundedPlugSideComponent h hlin d hs hI heq hc hn hρ hρ1 havρ t :=
  ⟨E.boundedPlugSideCanonicalMap h hlin d hs hI hρ hρ1 havρ t (x.val.1.down, x.val.2),
    E.boundedPlugSideCanonicalMap_mem_component h hlin d hs hI heq hc hn hρ hρ1 havρ t
      ((mem_solidSet_iff x.val).mp x.property)⟩

theorem boundedPlugSideComponentMap_apply (t : Bool) (x : solidSet.{u}) :
    (E.boundedPlugSideComponentMap h hlin d hs hI heq hc hn hρ hρ1 havρ t x).val =
      E.boundedPlugSideCanonicalMap h hlin d hs hI hρ hρ1 havρ t
        (x.val.1.down, x.val.2) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugSideComponentMap_bijective (t : Bool) :
    Bijective (E.boundedPlugSideComponentMap h hlin d hs hI heq hc hn hρ hρ1 havρ t) := by
  constructor
  · intro x y he
    have hmap := congrArg Subtype.val he
    have hh := E.boundedPlugSideCappedMap_injOn h hlin d hs hI
      (E.toTorus.external.shrink hρ hρ1) _ havρ heq t
      ((mem_solidSet_iff x.val).mp x.property) ((mem_solidSet_iff y.val).mp y.property) hmap
    apply Subtype.ext
    exact Prod.ext (ULift.ext (congrArg Prod.fst hh)) (congrArg (fun p : ℂ × Circle => p.2) hh)
  · intro y
    obtain ⟨q, hq, hm⟩ := (E.boundedPlugSideCanonicalMap_image h hlin d hs hI heq
      hc hn hρ hρ1 havρ t).symm.subset y.property
    refine ⟨⟨(ULift.up q.1, q.2), (mem_solidSet_iff _).mpr hq⟩, ?_⟩
    exact Subtype.ext hm

private def boundedPlugSolidDown :
    (PlaneLift.{u} × Circle) ≃ₘ⟮(𝓘(ℝ, ℂ)).prod (𝓡 1),
      (𝓘(ℝ, ℂ)).prod (𝓡 1)⟯ ℂ × Circle :=
  (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).symm.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)

private theorem boundedPlugSolidDown_apply (x : PlaneLift.{u} × Circle) :
    boundedPlugSolidDown x = (x.1.down, x.2) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugSideComponentMap_local_interior (t : Bool) (x : solidSet.{u})
    (hx : ‖x.val.1.down‖ < 3) :
    IsLocalDiffeomorphAt (𝓡∂ 3)
      (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.model ∞
      (E.boundedPlugSideComponentMap h hlin d hs hI heq hc hn hρ hρ1 havρ t) x := by
  have hopen : IsOpen {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 3} :=
    isOpen_lt (continuous_norm.comp
      ((Homeomorph.ulift : PlaneLift.{u} ≃ₜ ℂ).continuous.comp continuous_fst)) continuous_const
  have hi : x.val ∈ interior solidSet := mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (hopen.mem_nhds hx) fun p hp => (mem_solidSet_iff p).mpr hp.le)
  have hv := solidAtlas.isLocalDiffeomorphAt_subtype_val hi
  have hd := hv.comp _ _ (boundedPlugSolidDown.isLocalDiffeomorph x.val)
  have hm := E.boundedPlugSideCappedMap_local h hlin d hs hI
    (E.toTorus.external.shrink hρ hρ1)
    (E.toTorus.external_exhausted.trans
      (E.toTorus.external.shrink_image hρ hρ1).symm) havρ heq t (x.val.1.down, x.val.2) hx
  have ha := hd.comp _ _ hm
  exact isLocalDiffeomorphAt_subtypeCodRestrict
    (fun y : solidSet => E.boundedPlugSideCanonicalMap_mem_component h hlin d hs hI heq
      hc hn hρ hρ1 havρ t ((mem_solidSet_iff y.val).mp y.property)) ha
private def boundedPlugSideBoundaryCoordinates (_t : Bool) :
    (Torus × EuclideanHalfSpace 1) ≃ₘ⟮halfCollarModel, halfCollarModel⟯
      Torus × EuclideanHalfSpace 1 :=
  (germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
    (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁).prodCongr
      (halfSpaceScale (inv_pos.mpr hρ))

private theorem boundedPlugSideBoundaryCoordinates_apply (t : Bool)
    (p : Torus × EuclideanHalfSpace 1) :
    E.boundedPlugSideBoundaryCoordinates h hlin hρ t p =
      (germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
        (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁ p.1,
        halfPoint (ρ⁻¹ * p.2.val 0) (mul_nonneg (inv_nonneg.mpr hρ.le) p.2.property)) := by
  refine Prod.ext rfl ?_
  exact (halfPoint_eq_self _ _ (halfSpaceScale_coord (inv_pos.mpr hρ) p.2).symm).symm

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugSideCanonicalMap_solidCollar (t : Bool)
    (p : Torus × EuclideanHalfSpace 1) (hp1 : p.2.val 0 < 1)
    (hpρ : p.2.val 0 < ρ) (hp3 : p.2.val 0 < 1 / 3)
    (hpδ : p.2.val 0 < (E.splitData h).δ) :
    E.boundedPlugSideCanonicalMap h hlin d hs hI hρ hρ1 havρ t
      ((solidCollar.{u} 1 p).val.1.down, (solidCollar.{u} 1 p).val.2) =
        (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapRetained.collar
          (E.fibrePlugSideExternalEquiv h hc hn t)
            (E.boundedPlugSideBoundaryCoordinates h hlin hρ t p) := by
  have hsc : p ∈ halfCollarSource := hp1
  have hs0 : 0 ≤ ρ⁻¹ * p.2.val 0 := mul_nonneg (inv_nonneg.mpr hρ.le) p.2.property
  have hs1 : ρ⁻¹ * p.2.val 0 < 1 := by
    rw [inv_mul_lt_iff₀ hρ]
    simpa only [mul_one] using hpρ
  have hsρ : ρ * (ρ⁻¹ * p.2.val 0) = p.2.val 0 := by
    rw [← mul_assoc, mul_inv_cancel₀ hρ.ne', one_mul]
  have hh := E.boundedPlugSideCappedMap_retained_collar h hlin d hs hI hc hn
    hρ hρ1 havρ t p.1 hs0 hs1 (hsρ.symm ▸ hp3) (hsρ.symm ▸ hpδ)
  rw [hsρ] at hh
  rw [solidCollar_apply_val 1 hsc, seamRadius_one]
  rw [E.boundedPlugSideBoundaryCoordinates_apply h hlin hρ]
  have hr : 3 + 3 * -(p.2.val 0) / 2 = 3 - 3 * p.2.val 0 / 2 := by ring
  simpa only [hr] using hh

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugSideComponentMap_local_boundary (t : Bool) (p : Torus) :
    IsLocalDiffeomorphAt (𝓡∂ 3)
      (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.model ∞
      (E.boundedPlugSideComponentMap h hlin d hs hI heq hc hn hρ hρ1 havρ t)
        (solidCollar.{u} 1 (p, halfZero)) := by
  let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ
  let R := E.boundedPlugSideBoundaryCoordinates h hlin hρ t
  let T := B.sphereCapRetained.collar (E.fibrePlugSideExternalEquiv h hc hn t)
  let f : solidSet.{u} → B.sphereCapCarrier.Carrier := fun x =>
    E.boundedPlugSideCanonicalMap h hlin d hs hI hρ hρ1 havρ t (x.val.1.down, x.val.2)
  have hpR : R (p, halfZero) ∈ T.source := by
    rw [B.sphereCapRetained.source_eq]
    change (R (p, halfZero)).2.val 0 < 1
    rw [E.boundedPlugSideBoundaryCoordinates_apply h hlin hρ]
    change ρ⁻¹ * (0 : ℝ) < 1
    simp
  have hR := R.isLocalDiffeomorph (p, halfZero)
  have hT := T.isLocalDiffeomorphAt halfCollarModel B.sphereCapCarrier.model ∞ hpR
  have hh := hR.comp _ _ hT
  have he : (f ∘ (solidCollar.{u} 1)) =ᶠ[𝓝 (p, halfZero)] (T ∘ R) := by
    have hc0 : Continuous fun y : Torus × EuclideanHalfSpace 1 => y.2.val 0 :=
      (EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd)
    have hN := ((isOpen_lt hc0 continuous_const).mem_nhds
      (show (p, halfZero).2.val 0 < min 1 (min ρ (min (1 / 3) (E.splitData h).δ)) by
        change (0 : ℝ) < min 1 (min ρ (min (1 / 3) (E.splitData h).δ))
        exact lt_min zero_lt_one (lt_min hρ (lt_min (by norm_num) (E.splitData h).hδ))))
    filter_upwards [hN] with y hy
    have hy1 := (lt_min_iff.mp hy).1
    have hyρ := (lt_min_iff.mp (lt_min_iff.mp hy).2).1
    have hy3 := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hy).2).2).1
    have hyδ := (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hy).2).2).2
    exact E.boundedPlugSideCanonicalMap_solidCollar h hlin d hs hI hc hn hρ hρ1 havρ
      t y hy1 hyρ hy3 hyδ
  have hcomp := DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq he hh
  have hsc := (solidCollar.{u} 1).isLocalDiffeomorphAt halfCollarModel (𝓡∂ 3) ∞
    (zero_mem_halfCollarSource p)
  have hf := DifferentialGeometry.isLocalDiffeomorphAt_of_comp hcomp hsc
  exact isLocalDiffeomorphAt_subtypeCodRestrict
    (fun y : solidSet => E.boundedPlugSideCanonicalMap_mem_component h hlin d hs hI heq
      hc hn hρ hρ1 havρ t ((mem_solidSet_iff y.val).mp y.property)) hf

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugSideComponentMap_local (t : Bool) :
    IsLocalDiffeomorph (𝓡∂ 3)
      (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.model ∞
      (E.boundedPlugSideComponentMap h hlin d hs hI heq hc hn hρ hρ1 havρ t) := by
  intro x
  rcases lt_or_eq_of_le ((mem_solidSet_iff x.val).mp x.property) with hx | hx
  · exact E.boundedPlugSideComponentMap_local_interior h hlin d hs hI heq hc hn hρ hρ1 havρ
      t x hx
  · let θ : Circle := unitOf x.val.1.down
    have he : solidCollar.{u} 1 ((θ, x.val.2), halfZero) = x := by
      apply Subtype.ext
      rw [solidCollar_zero_val]
      refine Prod.ext (ULift.ext ?_) rfl
      exact hx ▸ norm_smul_unitOf x.val.1.down
    rw [← he]
    exact E.boundedPlugSideComponentMap_local_boundary h hlin d hs hI heq hc hn hρ hρ1 havρ
      t (θ, x.val.2)
def boundedPlugSideSolidDiffeomorph (t : Bool) :
    solidSet.{u} ≃ₘ⟮𝓡∂ 3,
      (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.model⟯
        E.boundedPlugSideComponent h hlin d hs hI heq hc hn hρ hρ1 havρ t :=
  IsLocalDiffeomorph.diffeomorphOfBijective
    (E.boundedPlugSideComponentMap_local h hlin d hs hI heq hc hn hρ hρ1 havρ t)
    (E.boundedPlugSideComponentMap_bijective h hlin d hs hI heq hc hn hρ hρ1 havρ t)

theorem boundedPlugSideSolidDiffeomorph_apply (t : Bool) (x : solidSet.{u}) :
    (E.boundedPlugSideSolidDiffeomorph h hlin d hs hI heq hc hn hρ hρ1 havρ t x).val =
      E.boundedPlugSideCanonicalMap h hlin d hs hI hρ hρ1 havρ t
        (x.val.1.down, x.val.2) := rfl

def boundedPlugSideDiffeomorph (t : Bool) :
    ((discPlanarBase.{u} 1).surface.Carrier × Circle) ≃ₘ⟮
      (SurfaceModel.model (discPlanarBase.{u} 1).surface.kind).prod (𝓡 1),
      (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.model⟯
        E.boundedPlugSideComponent h hlin d hs hI heq hc hn hρ hρ1 havρ t :=
  solidDiffeomorph.trans (E.boundedPlugSideSolidDiffeomorph h hlin d hs hI heq
    hc hn hρ hρ1 havρ t)

theorem boundedPlugSideDiffeomorph_apply (t : Bool)
    (x : (discPlanarBase.{u} 1).surface.Carrier × Circle) :
    (E.boundedPlugSideDiffeomorph h hlin d hs hI heq hc hn hρ hρ1 havρ t x).val =
      E.boundedPlugSideCanonicalMap h hlin d hs hI hρ hρ1 havρ t
        (x.1.val.down, x.2) := rfl

theorem boundedPlugSideDiffeomorph_retained_collar (t : Bool) (p : Torus) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s < 1) (hs3 : ρ * s < 1 / 3)
    (hsδ : ρ * s < (E.splitData h).δ) :
    (E.boundedPlugSideDiffeomorph h hlin d hs hI heq hc hn hρ hρ1 havρ t
      ((discPlanarBase.{u} 1).collar 0
        (p.1, halfPoint (ρ * s) (mul_nonneg hρ.le hs0)), p.2)).val =
          (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapRetained.collar
            (E.fibrePlugSideExternalEquiv h hc hn t)
              (germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
                (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁ p,
                  halfPoint s hs0) := by
  have hρs1 : ρ * s < 1 := lt_of_lt_of_le hs3 (by norm_num)
  rw [E.boundedPlugSideDiffeomorph_apply]
  change E.boundedPlugSideCanonicalMap h hlin d hs hI hρ hρ1 havρ t
    ((discCollar.{u} 1 (p.1, halfPoint (ρ * s) (mul_nonneg hρ.le hs0))).val.down, p.2) = _
  rw [discCollar_apply_val 1 hρs1, seamRadius_one]
  have hh := E.boundedPlugSideCappedMap_retained_collar h hlin d hs hI hc hn
    hρ hρ1 havρ t p hs0 hs1 hs3 hsδ
  change E.boundedPlugSideCanonicalMap h hlin d hs hI hρ hρ1 havρ t
    ((3 + 3 * -(ρ * s) / 2) • (p.1 : ℂ), p.2) = _
  have hr : 3 + 3 * -(ρ * s) / 2 = 3 - 3 * (ρ * s) / 2 := by ring
  simpa only [hr] using hh

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugSideSolidDiffeomorph_orientation_dichotomy (t : Bool) :
    let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ
    let O := B.sphereCapCarrier.orientation.restrictOpen
      (E.boundedPlugSideComponent h hlin d hs hI heq hc hn hρ hρ1 havρ t)
    let f := E.boundedPlugSideSolidDiffeomorph h hlin d hs hI heq hc hn hρ hρ1 havρ t
    f.preservesOrientation (solidAtlas.orientation planeCircleOrientation) O ∨
      f.preservesOrientation (solidAtlas.orientation planeCircleOrientation).opposite O := by
  exact GC.Seifert.preservesOrientation_or_opposite
    (E.boundedPlugSideSolidDiffeomorph h hlin d hs hI heq hc hn hρ hρ1 havρ t) _ _
def boundedPlugSolidReflection : solidSet.{u} ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ solidSet.{u} :=
  (solidDiffeomorph.symm.trans
    ((Diffeomorph.refl (𝓡∂ 2) discSet.{u} ∞).prodCongr circleInvDiffeo)).trans solidDiffeomorph

theorem boundedPlugSolidReflection_apply (x : solidSet.{u}) :
    (boundedPlugSolidReflection x).val = (x.val.1, x.val.2⁻¹) := rfl

theorem boundedPlugSolidReflection_collar (p : Torus × EuclideanHalfSpace 1) :
    boundedPlugSolidReflection.{u} (solidCollar 1 p) =
      solidCollar 1 ((p.1.1, p.1.2⁻¹), p.2) := rfl

private def boundedPlugProductOrientation :
    ManifoldOrientation ((𝓡∂ 2).prod (𝓡 1)) (discSet.{u} × Circle) 3 :=
  productOrientation (𝓡∂ 2) (𝓡 1) (by norm_num) (by norm_num)
    (discAtlas.orientation (uliftOrientation 𝓘(ℝ, ℂ) ℂ planeOrientation)) circleOrientation

set_option backward.isDefEq.respectTransparency false in
theorem boundedPlugSolidReflection_negative :
    boundedPlugSolidReflection.{u}.preservesOrientation
      (solidAtlas.orientation planeCircleOrientation)
        (solidAtlas.orientation planeCircleOrientation).opposite := by
  let P := boundedPlugProductOrientation.{u}
  let O := solidAtlas.{u}.orientation planeCircleOrientation
  let R := (Diffeomorph.refl (𝓡∂ 2) discSet.{u} ∞).prodCongr circleInvDiffeo
  have hR : R.preservesOrientation P P.opposite := by
    have hh := Diffeomorph.prodCongr_preservesOrientation (by norm_num : 1 ≤ 2) le_rfl
      (Diffeomorph.refl (𝓡∂ 2) discSet.{u} ∞) circleInvDiffeo
      (Diffeomorph.preservesOrientation_refl
        (discAtlas.orientation (uliftOrientation 𝓘(ℝ, ℂ) ℂ planeOrientation)))
      GC.Seifert.circleInvDiffeo_preservesOrientation
    rw [← GC.Seifert.productOrientation_opposite_right] at hh
    exact hh
  have : ConnectedSpace discSet.{u} := discSurface.{u}.connected
  rcases GC.Seifert.preservesOrientation_or_opposite solidDiffeomorph.{u} P O with hS | hS
  · exact Diffeomorph.preservesOrientation_trans
      (Diffeomorph.preservesOrientation_trans (Diffeomorph.preservesOrientation_symm hS) hR)
        (Diffeomorph.preservesOrientation_opposite hS)
  · have hR' : R.preservesOrientation P.opposite P := by
      have hh := Diffeomorph.preservesOrientation_opposite hR
      simpa only [ManifoldOrientation.opposite_opposite] using hh
    have hS' : solidDiffeomorph.{u}.preservesOrientation P O.opposite := by
      have hh := Diffeomorph.preservesOrientation_opposite hS
      simpa only [ManifoldOrientation.opposite_opposite] using hh
    exact Diffeomorph.preservesOrientation_trans
      (Diffeomorph.preservesOrientation_trans (Diffeomorph.preservesOrientation_symm hS) hR') hS'

set_option backward.isDefEq.respectTransparency false in
theorem exists_boundedPlugSidePositiveDiffeomorph (t : Bool) :
    ∃ (ε : Bool) (f : solidSet.{u} ≃ₘ⟮𝓡∂ 3,
      (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.model⟯
        E.boundedPlugSideComponent h hlin d hs hI heq hc hn hρ hρ1 havρ t),
      f.preservesOrientation (solidAtlas.orientation planeCircleOrientation)
        ((E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.orientation.restrictOpen
          (E.boundedPlugSideComponent h hlin d hs hI heq hc hn hρ hρ1 havρ t)) ∧
      (∀ x : solidSet.{u}, (f x).val =
        E.boundedPlugSideCanonicalMap h hlin d hs hI hρ hρ1 havρ t
          (x.val.1.down, if ε then x.val.2⁻¹ else x.val.2)) ∧
      ∀ p : Torus, ∀ s : ℝ, ∀ hs0 : 0 ≤ s, s < 1 → ρ * s < 1 / 3 →
        ρ * s < (E.splitData h).δ →
        (f (solidCollar 1 (p, halfPoint (ρ * s) (mul_nonneg hρ.le hs0)))).val =
          (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapRetained.collar
            (E.fibrePlugSideExternalEquiv h hc hn t)
              (germHol ((E.boundedSplitCharts h hlin).e₀ * (E.boundedSplitCharts h hlin).d)
                (E.boundedSplitCharts h hlin).e₁ (E.boundedSplitCharts h hlin).he₁
                  (p.1, if ε then p.2⁻¹ else p.2), halfPoint s hs0) := by
  let f := E.boundedPlugSideSolidDiffeomorph h hlin d hs hI heq hc hn hρ hρ1 havρ t
  rcases E.boundedPlugSideSolidDiffeomorph_orientation_dichotomy h hlin d hs hI heq
    hc hn hρ hρ1 havρ t with hf | hf
  · refine ⟨false, f, hf, fun x => rfl, ?_⟩
    intro p s hs0 hs1 hs3 hsδ
    exact E.boundedPlugSideDiffeomorph_retained_collar h hlin d hs hI heq hc hn
      hρ hρ1 havρ t p hs0 hs1 hs3 hsδ
  · refine ⟨true, boundedPlugSolidReflection.trans f,
      Diffeomorph.preservesOrientation_trans boundedPlugSolidReflection_negative hf,
      fun x => rfl, ?_⟩
    intro p s hs0 hs1 hs3 hsδ
    change (f (boundedPlugSolidReflection
      (solidCollar 1 (p, halfPoint (ρ * s) (mul_nonneg hρ.le hs0))))).val = _
    rw [boundedPlugSolidReflection_collar]
    exact E.boundedPlugSideDiffeomorph_retained_collar h hlin d hs hI heq hc hn
      hρ hρ1 havρ t (p.1, p.2⁻¹) hs0 hs1 hs3 hsδ

end GC.Seifert.ElementaryPresentation
