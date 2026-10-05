import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RestoredTorusFactorRegularity
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryCappingCommutation
import DifferentialGeometry.Topology.Manifold.ImmersionInterior

/-!
The actual uncapped quotient factor is locally a diffeomorphism on its physical puncture interior.
The two original folds and the same signed seam supply all local comparisons.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open GC.Endpoint.CompactCarrier GC.GraphManifold.RelativeSphereCapping
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold

private theorem restoredBoundary_cast_collar {P : CompactCarrier.{u}} {n m : ℕ}
    (hn : n = m) (E : BoundaryTori P n) (i : Fin m)
    (p : Torus × EuclideanHalfSpace 1) :
    (hn ▸ E).collar i p = E.collar (Fin.cast hn.symm i) p := by
  cases hn
  rfl

variable (M : ConnectedClosedOrientedManifold.{u} 3) (N : CompactCarrier.{u})
  [N.model.Boundaryless]
  (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) (𝓡 3)
    (PlaneLift.{u} × Circle) M.Carrier ∞)
  (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
  (K C S : CompactCarrier.{u})
  (hK : K.kind = .withBoundary) (hC : C.kind = .withBoundary)
  (hS : S.kind = .withBoundary)
  [Nonempty K.Carrier] [Nonempty C.Carrier] [Nonempty S.Carrier]
  (ι : K.Carrier → M.Carrier) (Γ : BoundaryTori K 1)
  (hι : IsSmoothEmbedding K.model (𝓡 3) ∞ ι)
  (hbij : ∀ x, Bijective (mfderiv K.model (𝓡 3) ι x))
  (hb : K.model.boundary K.Carrier = Γ.image)
  (hΓ : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
    ι (Γ.collar 0 p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
  (B : MixedBoundaryCertificate C) (ht : B.torusCount = 1)
  (Ki : RelativeSphereCapping C S B)
  (g : solidSet.{u} ≃ₘ⟮𝓡∂ 3, S.model⟯ S.Carrier)
  (ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (ε : Bool)
  (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
  (hgc : ∀ p : Torus × EuclideanHalfSpace 1, p ∈ halfCollarSource →
    g (solidCollar 1 (p.1, halfSpaceScale hσ p.2)) =
      (boundaryCappingRetained C S B ht Ki).collar 0 (ψ p.1, halfSpaceScale hσ p.2))

variable
  (hr0 : ReversesBoundaryOrientation (withBoundarySum K C hK hC)
    (boundaryPortLeftCollar K C hK hC Γ)
    (fun p => boundaryPortRightCollar K C hK hC (boundaryCappingTori C B ht) 0
      ((markedRestorationMatching ψ ε) p.1, p.2)))
  (hr1 : ReversesBoundaryOrientation (withBoundarySum K S hK hS)
    (boundaryPortLeftCollar K S hK hS Γ)
    (fun p => boundaryPortRightCollar K S hK hS (boundaryCappingRetained C S B ht Ki) 0
      ((markedRestorationMatching ψ ε) p.1, p.2)))

variable (H : (boundaryCappingCappedPairing K C S hK hS B ht Ki Γ
      (markedRestorationMatching ψ ε) hr1).QuotientSpace ≃ₜ M.Carrier)
  (c : OrientedBallChart M.toClosedOrientedManifold)
  (e : (boundaryCappingUncappedPairing K C hK hC B ht Γ
      (markedRestorationMatching ψ ε) hr0).QuotientSpace ≃ₜ c.Punctured)
  (hleft : ∀ x : K.Carrier, H ((boundaryCappingCappedPairing K C S hK hS B ht Ki Γ
      (markedRestorationMatching ψ ε) hr1).quotientMap (Sum.inl x)) = ι x)
  (hright : ∀ y : S.Carrier, H ((boundaryCappingCappedPairing K C S hK hS B ht Ki Γ
      (markedRestorationMatching ψ ε) hr1).quotientMap (Sum.inr y)) =
      markedRestorationFill M φ S g ε y)
  (hcore : ∀ x, (e x).val =
    H (boundaryCappingCore K C S hK hC hS B ht Ki Γ (markedRestorationMatching ψ ε) hr0 hr1 x))
  (hsphere : ∀ (i : Fin B.sphereCount) (z : ClosureSphere.{u}),
    e ((boundaryCappingUncappedPairing K C hK hC B ht Γ
      (markedRestorationMatching ψ ε) hr0).quotientMap
        (Sum.inr (B.sphere i (Ki.attaching i z, halfZero)))) =
      c.boundaryMap z.down)
  (L : C((boundaryCappingUncappedPairing K C hK hC B ht Γ
      (markedRestorationMatching ψ ε) hr0).QuotientSpace, N.Carrier)) (A : K.Carrier → N.Carrier)
  (J : C.Carrier → N.Carrier)
  (hA : ContMDiff K.model N.model ∞ A) (hJ : ContMDiff C.model N.model ∞ J)
  (hAd : ∀ x, K.model.IsInteriorPoint x → Injective (mfderiv K.model N.model A x))
  (hJd : ∀ x, C.model.IsInteriorPoint x → Injective (mfderiv C.model N.model J x))
  (hLA : ∀ x, L ((boundaryCappingUncappedPairing K C hK hC B ht Γ
      (markedRestorationMatching ψ ε) hr0).quotientMap (Sum.inl x)) = A x)
  (hLJ : ∀ x, L ((boundaryCappingUncappedPairing K C hK hC B ht Γ
      (markedRestorationMatching ψ ε) hr0).quotientMap (Sum.inr x)) = J x)
  (q : PartialDiffeomorph signedCollarModel N.model (Torus × ℝ) N.Carrier ∞)
  (hq : q.source = signedCollarSource)
  (α : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus) (a : ℝ) (ha : 0 < a)
  (η : ℝ) (hη : 0 < η)
  (hAL : ∀ (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < η →
    A (Γ.collar 0 (t, halfPoint s hs)) = q (α t, -(s / a)))
  (hJR : ∀ (t : Torus) (s : ℝ) (hs : 0 ≤ s), s < η →
    J ((boundaryCappingTori C B ht).collar 0 ((markedRestorationMatching ψ ε) t, halfPoint s hs)) =
      q (α t, s / a))

include h3 hι hbij hb hΓ hσ1 hgc hleft hright hcore hsphere
  hA hJ hAd hJd hLA hLJ hq ha hη hAL hJR in
theorem restoredFactorInterior_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) N.model ∞
      (fun x : c.toBallChart.interior =>
        L (e.symm (c.toBallChart.interiorToPunctured x))) := by
  classical
  let F : M.Carrier → N.Carrier := fun y =>
    if hy : y ∉ c.chart '' Metric.ball 0 1 then L (e.symm ⟨y, hy⟩)
    else A (Γ.torusMap 0 torusBase)
  have hFe (x : (boundaryCappingUncappedPairing K C hK hC B ht Γ
      (markedRestorationMatching ψ ε) hr0).QuotientSpace) : F (e x).val = L x := by
    dsimp only [F]
    rw [dite_eq_left (e x).property]
    exact congrArg L (e.symm_apply_apply x)
  have heleft (x : K.Carrier) : (e ((boundaryCappingUncappedPairing K C hK hC B ht Γ
      (markedRestorationMatching ψ ε) hr0).quotientMap (Sum.inl x))).val = ι x := by
    rw [hcore, boundaryCappingCore_left, hleft]
  have heright (x : C.Carrier) : (e ((boundaryCappingUncappedPairing K C hK hC B ht Γ
      (markedRestorationMatching ψ ε) hr0).quotientMap (Sum.inr x))).val =
      markedRestorationFill M φ S g ε (Ki.core x) := by
    rw [hcore, boundaryCappingCore_right, hright]
  have hFA (x : K.Carrier) : F (ι x) = A x := by
    rw [← heleft, hFe, hLA]
  have hFJ (x : C.Carrier) : F ((markedRestorationFill M φ S g ε) (Ki.core x)) = J x := by
    rw [← heright, hFe, hLJ]
  have hret (t : Torus) (p : EuclideanHalfSpace 1)
      (hp : (t, p) ∈ halfCollarSource) :
      (boundaryCappingRetained C S B ht Ki).collar 0 (t, p) =
        Ki.core ((boundaryCappingTori C B ht).collar 0 (t, p)) := by
    unfold boundaryCappingRetained boundaryCappingTori
    rw [restoredBoundary_cast_collar, restoredBoundary_cast_collar]
    exact Ki.retained_collar (Fin.cast ht.symm 0) (t, p) hp
  have htor (t : Torus) : IsLocalDiffeomorphAt (𝓡 3) N.model ∞ F
      (regularFibreRestorationSignedTube M φ (t, 0)) := by
    apply restoredTorusFactor_isLocalDiffeomorphAt M φ h3 K ι Γ hΓ S g ψ ε
      (boundaryCappingRetained C S B ht Ki) σ hσ hσ1 hgc F q hq α a ha
      (min η σ) (lt_min hη hσ)
    · intro v s hs hsη
      rw [hFA]
      exact hAL v s hs (hsη.trans_le (min_le_left η σ))
    · intro v s hs hsη
      have hp : ((markedRestorationMatching ψ ε) v, halfPoint s hs) ∈ halfCollarSource := by
        change s < 1
        exact (hsη.trans_le (min_le_right η σ)).trans_le hσ1
      rw [hret _ _ hp, hFJ]
      exact hJR v s hs (hsη.trans_le (min_le_left η σ))
  have hDc : ContMDiff C.model (𝓡 3) ∞ ((markedRestorationFill M φ S g ε) ∘ Ki.core) :=
    (markedRestorationFill_smooth M φ h3 S g ε).comp Ki.core_embedding.contMDiff
  have hDinj (x : C.Carrier) (hx : C.model.IsInteriorPoint x) :
      Injective (mfderiv C.model (𝓡 3) ((markedRestorationFill M φ S g ε) ∘ Ki.core) x) := by
    rw [mfderiv_comp x
      ((markedRestorationFill_smooth M φ h3 S g ε).mdifferentiableAt (by simp))
      (Ki.core_embedding.contMDiff.mdifferentiableAt (by simp))]
    exact (markedRestorationFill_mfderiv_bijective M φ h3 S g ε _).injective.comp
      (Ki.core_positive x hx).choose.injective
  have hTint (x : C.Carrier) (hx : x ∈ B.tori.image) :
      ∃ t : Torus, (boundaryCappingTori C B ht).torusMap 0 t = x := by
    obtain ⟨i, t, htix⟩ := mem_iUnion.mp hx
    refine ⟨t, ?_⟩
    unfold boundaryCappingTori
    have hie : i = Fin.cast ht.symm 0 := by
      apply Fin.ext
      have hv : i.val < 1 := i.isLt.trans_le ht.le
      simp only [Fin.val_cast, Fin.val_zero]
      omega
    subst i
    change (ht ▸ B.tori).collar 0 (t, halfZero) = x
    rw [restoredBoundary_cast_collar]
    exact htix
  have htorCore (t : Torus) : (markedRestorationFill M φ S g ε) (Ki.core
      ((boundaryCappingTori C B ht).torusMap 0 ((markedRestorationMatching ψ ε) t))) =
      regularFibreRestorationSignedTube M φ (t, 0) := by
    rw [BoundaryTori.torusMap, ← hret _ _ (zero_mem_halfCollarSource _)]
    have hh := restoredTorusCollar_negative M φ S g ψ ε
      (boundaryCappingRetained C S B ht Ki) σ hσ hσ1 hgc t 0 (le_refl 0) hσ
    simpa only [neg_zero, show halfPoint 0 (le_refl 0) = halfZero from rfl] using hh
  intro x
  have hFx : IsLocalDiffeomorphAt (𝓡 3) N.model ∞ F x.val := by
    obtain ⟨z, hz⟩ := e.surjective (c.toBallChart.interiorToPunctured x)
    obtain ⟨w, hw⟩ := (boundaryCappingUncappedPairing K C hK hC B ht Γ
      (markedRestorationMatching ψ ε) hr0).surgery_quotientMap_surjective z
    have hval : (e ((boundaryCappingUncappedPairing K C hK hC B ht Γ
      (markedRestorationMatching ψ ε) hr0).quotientMap w)).val = x.val :=
      congrArg Subtype.val ((congrArg e hw).trans hz)
    rcases w with y | y
    · have hyval : ι y = x.val := (heleft y).symm.trans hval
      by_cases hy : K.model.IsInteriorPoint y
      · have hdι := isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv
          hι.contMDiff hy rfl (hbij y).injective
        have hdA := isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv
          hA hy rfl (hAd y hy)
        have hcomp : IsLocalDiffeomorphAt K.model N.model ∞ (F ∘ ι) y := by
          simpa only [show F ∘ ι = A from funext hFA] using hdA
        simpa only [hyval] using isLocalDiffeomorphAt_of_comp hcomp hdι
      · have hbnd := (K.model.isBoundaryPoint_iff_not_isInteriorPoint y).mpr hy
        have hym : y ∈ Γ.image := hb ▸ hbnd
        obtain ⟨i, t, hty⟩ := mem_iUnion.mp hym
        have hi : i = 0 := Subsingleton.elim i 0
        subst i
        have hzero := restoredTorusCollar_positive M φ K ι Γ hΓ t 0
          (le_refl 0) (by norm_num)
        have hp : ι y = regularFibreRestorationSignedTube M φ (t, 0) := by
          rw [← hty]
          simpa only [BoundaryTori.torusMap,
            show halfPoint 0 (le_refl 0) = halfZero from rfl] using hzero
        rw [← hyval, hp]
        exact htor t
    · have hyval : markedRestorationFill M φ S g ε (Ki.core y) = x.val :=
        (heright y).symm.trans hval
      by_cases hy : C.model.IsInteriorPoint y
      · have hdD := isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv
          hDc hy rfl (hDinj y hy)
        have hdJ := isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv
          hJ hy rfl (hJd y hy)
        have hcomp : IsLocalDiffeomorphAt C.model N.model ∞
            (F ∘ (markedRestorationFill M φ S g ε ∘ Ki.core)) y := by
          simpa only [show F ∘ (markedRestorationFill M φ S g ε ∘ Ki.core) = J
            from funext hFJ] using hdJ
        simpa only [Function.comp_apply, hyval] using isLocalDiffeomorphAt_of_comp hcomp hdD
      · have hbnd := (C.model.isBoundaryPoint_iff_not_isInteriorPoint y).mpr hy
        have hym : y ∈ B.tori.image ∪ B.sphereImage := B.boundary_eq ▸ hbnd
        rcases hym with hym | hym
        · obtain ⟨t, hty⟩ := hTint y hym
          have hh := htorCore ((markedRestorationMatching ψ ε).symm t)
          rw [(markedRestorationMatching ψ ε).apply_symm_apply, hty] at hh
          rw [← hyval, hh]
          exact htor ((markedRestorationMatching ψ ε).symm t)
        · obtain ⟨i, z, hzy⟩ := mem_iUnion.mp hym
          have hz' := hsphere i ((Ki.attaching i).symm z)
          rw [(Ki.attaching i).apply_symm_apply] at hz'
          have hy' : e ((boundaryCappingUncappedPairing K C hK hC B ht Γ
      (markedRestorationMatching ψ ε) hr0).quotientMap (Sum.inr y)) =
              c.boundaryMap ((Ki.attaching i).symm z).down := by
            rw [← hzy]
            exact hz'
          have hboundary : x.val = c.chart ((Ki.attaching i).symm z).down := by
            rw [← hval, hy']
            rfl
          exact False.elim (x.property ⟨((Ki.attaching i).symm z).down,
            Metric.sphere_subset_closedBall (((Ki.attaching i).symm z).down.property),
            hboundary.symm⟩)
  have hval := (DifferentialGeometry.isLocalDiffeomorph_subtype_val
    (I := 𝓡 3) c.toBallChart.interior) x
  have hcomp := hval.comp N.model N.Carrier hFx
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq _ hcomp
  exact Filter.Eventually.of_forall (fun y => by
    change L (e.symm (c.toBallChart.interiorToPunctured y)) = F y.val
    dsimp only [F]
    have hy : y.val ∉ c.chart '' Metric.ball 0 1 :=
      (c.toBallChart.interiorToPunctured y).property
    rw [dite_eq_left hy]
    rfl)

include h3 hι hbij hb hΓ hσ1 hgc hleft hright hcore hsphere
  hA hJ hAd hJd hLA hLJ hq ha hη hAL hJR in
theorem restoredFactorInterior_radial_isLocalDiffeomorphAt
    (hrad : ∀ t : Torus,
      φ (ULift.up ((5 / 4 : ℝ) • (t.1 : ℂ)), t.2) ∈ c.toBallChart.interior)
    (t : Torus) :
    IsLocalDiffeomorphAt (𝓡 3) N.model ∞
      (fun x : c.toBallChart.interior =>
        L (e.symm (c.toBallChart.interiorToPunctured x)))
      ⟨φ (ULift.up ((5 / 4 : ℝ) • (t.1 : ℂ)), t.2), hrad t⟩ := by
  exact restoredFactorInterior_isLocalDiffeomorph M N φ h3 K C S hK hC hS
    ι Γ hι hbij hb hΓ B ht Ki g ψ ε σ hσ hσ1 hgc hr0 hr1 H c e
    hleft hright hcore hsphere L A J hA hJ hAd hJd hLA hLJ q hq α a ha η hη hAL hJR _

end GC.GraphManifold
