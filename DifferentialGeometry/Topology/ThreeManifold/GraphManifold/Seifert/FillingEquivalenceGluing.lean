import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingProductCharts

/-!
# Comparing actual torus quotients across universes

The cut-carrier diffeomorphism preserves the actual gluing relation and agrees with signed
seams on a common positive germ. Its quotient homeomorphism is smooth in both directions.
The comparison constructions generalize the proved selected-filling comparison interfaces.
-/

set_option autoImplicit false

noncomputable section
open Set Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

universe u v
namespace GC.Seifert.TorusPresentation
variable {W : CompactCarrier.{u}} {W' : CompactCarrier.{v}}

theorem fillingContMDiff_of_cutMap_seams (T : TorusPresentation W) (f : W.Carrier → W'.Carrier)
    (hcut : ContMDiff T.cutCarrier.model W'.model ∞ (f ∘ T.cutMap))
    (hseam : ∀ k t, ContMDiffAt signedCollarModel W'.model ∞
      (f ∘ T.seam k) (t, 0)) : ContMDiff W.model W'.model ∞ f := by
  intro w
  obtain ⟨x, rfl⟩ := T.cutMap_surjective w
  by_cases hx : T.cutCarrier.model.IsInteriorPoint x
  · let xi : T.cutCarrier.interior := ⟨x, hx⟩
    have hxi : ContMDiffAt T.cutCarrier.model W'.model ∞
        (fun y => f (T.interiorDiffeomorph y).val) xi := by
      have h := hcut.comp (contMDiff_subtype_val (U := T.cutCarrier.interior))
      have he : (fun y => f (T.interiorDiffeomorph y).val) =
          (f ∘ T.cutMap) ∘ Subtype.val := by
        funext y
        rw [T.interior_map]
        rfl
      rw [he]
      exact h xi
    have hs := (T.interiorDiffeomorph.symm_apply_apply xi).symm ▸ hxi
    have hs := hs.comp (T.interiorDiffeomorph xi)
      T.interiorDiffeomorph.symm.contMDiffAt
    have he : (fun y => f (T.interiorDiffeomorph
        (T.interiorDiffeomorph.symm y)).val) = (fun y : T.interiorImage => f y.val) := by
      funext y
      rw [Diffeomorph.apply_symm_apply]
    change ContMDiffAt W.model W'.model ∞
      (fun y => f (T.interiorDiffeomorph (T.interiorDiffeomorph.symm y)).val) _ at hs
    rw [he] at hs
    have hs' := contMDiffAt_subtype_iff.mp hs
    simpa [xi, T.interior_map, TorusPresentation.cutMap] using hs'
  · have hb : x ∈ T.cutCarrier.model.boundary T.cutCarrier.Carrier :=
      (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint x).mpr hx
    rw [T.cut_boundary_exhausted] at hb
    rcases hb with hb | hb
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hb
      have he : ∃ t, T.cutMap x = T.seam k (t, 0) := by
        rcases hk with hl | hr
        · refine ⟨(T.pairing.leftParam k).symm ⟨x, hl⟩, ?_⟩
          rw [T.seam_zero, Homeomorph.apply_symm_apply]
          rfl
        · refine ⟨(T.pairing.matching k).symm
            ((T.pairing.rightParam k).symm ⟨x, hr⟩), ?_⟩
          rw [T.seam_zero]
          change T.reconstruction (T.pairing.quotientMap x) = _
          rw [T.quotientMap_leftParam_eq_rightParam_matching,
            Diffeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
      obtain ⟨t, ht⟩ := he
      rw [ht]
      exact smoothAt_of_partial_comp (T.seam k) f
        (by rw [T.seam_source]; exact ⟨by norm_num, by norm_num⟩) (hseam k t)
    · obtain ⟨r, t, ht⟩ := mem_iUnion.mp hb
      have ht' : T.cutMap x = T.external.collar r (t, halfZero) := by
        rw [← ht]
        exact T.marked_collar r (t, halfZero) (zero_mem_halfCollarSource t)
      rw [ht']
      apply smoothAt_of_partial_comp (T.external.collar r) f
        (by rw [T.external.source_eq]; exact zero_mem_halfCollarSource t)
      have h := hcut.comp_contMDiffOn (T.cutExternal.collar r).contMDiffOn
      have he : EqOn (f ∘ T.external.collar r)
          ((f ∘ T.cutMap) ∘ T.cutExternal.collar r) halfCollarSource := by
        intro p hp
        exact congrArg f (T.marked_collar r p hp).symm
      have h' := h.congr (fun p hp => he ((T.cutExternal.source_eq r) ▸ hp))
      rw [T.cutExternal.source_eq r] at h'
      exact h'.contMDiffAt ((T.external.source_eq r) ▸
        (T.external.collar r).open_source.mem_nhds
          ((T.external.source_eq r).symm ▸ zero_mem_halfCollarSource t))

theorem fillingCutRelation_iff_of_params (T : TorusPresentation W) (D : TorusPresentation W')
    (F : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (e : Fin T.pairing.count ≃ Fin D.pairing.count)
    (A : Fin T.pairing.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (hl : ∀ k t, F (T.pairing.leftParam k t).val = (D.pairing.leftParam (e k) (A k t)).val)
    (hr : ∀ k t, F (T.pairing.rightParam k (T.pairing.matching k t)).val =
      (D.pairing.rightParam (e k) (D.pairing.matching (e k) (A k t))).val)
    (x y : T.cutCarrier.Carrier) :
    T.pairing.gluing.rel x y ↔ D.pairing.gluing.rel (F x) (F y) := by
  rw [GC.Seifert.TorusPairing.rel_iff_params T.pairing,
    GC.Seifert.TorusPairing.rel_iff_params D.pairing]
  constructor
  · rintro (rfl | ⟨k, t, ht | ht⟩)
    · exact Or.inl rfl
    · rcases ht with ⟨rfl, rfl⟩
      exact Or.inr ⟨e k, A k t, Or.inl ⟨hl k t, hr k t⟩⟩
    · rcases ht with ⟨rfl, rfl⟩
      exact Or.inr ⟨e k, A k t, Or.inr ⟨hl k t, hr k t⟩⟩
  · rintro (hxy | ⟨k, t, ht | ht⟩)
    · exact Or.inl (F.injective hxy)
    · let l := e.symm k
      let r := (A l).symm t
      have hel : e l = k := e.apply_symm_apply k
      have har : A l r = t := (A l).apply_symm_apply t
      have hle := hl l r
      have hre := hr l r
      rw [hel, har] at hle hre
      exact Or.inr ⟨l, r, Or.inl
        ⟨F.injective (ht.1.trans hle.symm), F.injective (ht.2.trans hre.symm)⟩⟩
    · let l := e.symm k
      let r := (A l).symm t
      have hel : e l = k := e.apply_symm_apply k
      have har : A l r = t := (A l).apply_symm_apply t
      have hle := hl l r
      have hre := hr l r
      rw [hel, har] at hle hre
      exact Or.inr ⟨l, r, Or.inr
        ⟨F.injective (ht.1.trans hle.symm), F.injective (ht.2.trans hre.symm)⟩⟩

def fillingCutComparisonHomeomorph (T : TorusPresentation W) (D : TorusPresentation W')
    (F : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ D.pairing.gluing.rel (F x) (F y)) :
    W.Carrier ≃ₜ W'.Carrier :=
  (T.reconstruction.symm.trans (Homeomorph.Quotient.congr
    (rY := D.pairing.gluing.setoid) F.toHomeomorph hrel)).trans
    D.reconstruction

theorem fillingCutComparisonHomeomorph_cutMap (T : TorusPresentation W) (D : TorusPresentation W')
    (F : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ D.pairing.gluing.rel (F x) (F y))
    (x : T.cutCarrier.Carrier) :
    T.fillingCutComparisonHomeomorph D F hrel (T.cutMap x) = D.cutMap (F x) := by
  change D.reconstruction ((Homeomorph.Quotient.congr
    (rY := D.pairing.gluing.setoid) F.toHomeomorph hrel)
    (T.reconstruction.symm (T.reconstruction (T.pairing.quotientMap x)))) = _
  rw [Homeomorph.symm_apply_apply]
  rfl

def fillingCutComparisonDiffeomorph (T : TorusPresentation W) (D : TorusPresentation W')
    (F : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ D.pairing.gluing.rel (F x) (F y))
    (hseam : ∀ k t, ContMDiffAt signedCollarModel W'.model ∞
      (T.fillingCutComparisonHomeomorph D F hrel ∘ T.seam k) (t, 0))
    (hback : ∀ k t, ContMDiffAt signedCollarModel W.model ∞
      ((T.fillingCutComparisonHomeomorph D F hrel).symm ∘ D.seam k) (t, 0)) :
    W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier where
  toFun := T.fillingCutComparisonHomeomorph D F hrel
  invFun := (T.fillingCutComparisonHomeomorph D F hrel).symm
  left_inv := (T.fillingCutComparisonHomeomorph D F hrel).symm_apply_apply
  right_inv := (T.fillingCutComparisonHomeomorph D F hrel).apply_symm_apply
  contMDiff_toFun := T.fillingContMDiff_of_cutMap_seams _ (by
    change ContMDiff T.cutCarrier.model W'.model ∞
      (T.fillingCutComparisonHomeomorph D F hrel ∘ T.cutMap)
    have he : T.fillingCutComparisonHomeomorph D F hrel ∘ T.cutMap = D.cutMap ∘ F := by
      funext x
      exact T.fillingCutComparisonHomeomorph_cutMap D F hrel x
    rw [he]
    exact D.quotient_smooth.comp F.contMDiff) hseam
  contMDiff_invFun := D.fillingContMDiff_of_cutMap_seams _ (by
    change ContMDiff D.cutCarrier.model W.model ∞
      ((T.fillingCutComparisonHomeomorph D F hrel).symm ∘ D.cutMap)
    have he : (T.fillingCutComparisonHomeomorph D F hrel).symm ∘ D.cutMap =
        T.cutMap ∘ F.symm := by
      funext y
      apply (T.fillingCutComparisonHomeomorph D F hrel).injective
      rw [Function.comp_apply, Homeomorph.apply_symm_apply,
        Function.comp_apply, T.fillingCutComparisonHomeomorph_cutMap,
        Diffeomorph.apply_symm_apply]
    rw [he]
    exact T.quotient_smooth.comp F.symm.contMDiff) hback

theorem fillingCutComparisonHomeomorph_seam_of_collars (T : TorusPresentation W)
    (D : TorusPresentation W')
    (F : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ D.pairing.gluing.rel (F x) (F y))
    (e : Fin T.pairing.count ≃ Fin D.pairing.count)
    (A : Fin T.pairing.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (δ : ℝ) (hδ : δ ≤ 1)
    (hl : ∀ k t r (hr0 : 0 ≤ r), r < δ →
      F (T.pairing.leftCollar k (t, halfPoint r hr0)) =
        D.pairing.leftCollar (e k) (A k t, halfPoint r hr0))
    (hr : ∀ k t r (hr0 : 0 ≤ r), r < δ →
      F (T.pairing.rightCollar k (T.pairing.matching k t, halfPoint r hr0)) =
        D.pairing.rightCollar (e k)
          (D.pairing.matching (e k) (A k t), halfPoint r hr0))
    (k : Fin T.pairing.count) (t : Torus) {s : ℝ} (hs : |s| < δ) :
    T.fillingCutComparisonHomeomorph D F hrel (T.seam k (t, s)) = D.seam (e k) (A k t, s) := by
  have hs1 : |s| < 1 := lt_of_lt_of_le hs hδ
  by_cases hpos : 0 ≤ s
  · rw [T.seam_positive k t s hpos (lt_of_le_of_lt (le_abs_self s) hs1),
      D.seam_positive (e k) (A k t) s hpos (lt_of_le_of_lt (le_abs_self s) hs1)]
    change T.fillingCutComparisonHomeomorph D F hrel (T.cutMap _) = D.cutMap _
    rw [T.fillingCutComparisonHomeomorph_cutMap,
      hr k t s hpos (lt_of_le_of_lt (le_abs_self s) hs)]
  · have hneg : s ≤ 0 := le_of_not_ge hpos
    have hslo : -1 < s := (abs_lt.mp hs1).1
    rw [T.seam_negative k t s hneg hslo, D.seam_negative (e k) (A k t) s hneg hslo]
    change T.fillingCutComparisonHomeomorph D F hrel (T.cutMap _) = D.cutMap _
    rw [T.fillingCutComparisonHomeomorph_cutMap,
      hl k t (-s) (neg_nonneg.mpr hneg) (lt_of_le_of_lt (neg_le_abs s) hs)]

def fillingCutComparisonDiffeomorph_of_seamGerms (T : TorusPresentation W)
    (D : TorusPresentation W')
    (F : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (hrel : ∀ x y, T.pairing.gluing.rel x y ↔ D.pairing.gluing.rel (F x) (F y))
    (e : Fin T.pairing.count ≃ Fin D.pairing.count)
    (A : Fin T.pairing.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (δ : ℝ) (hδ : 0 < δ)
    (heq : ∀ k t s, |s| < δ →
      T.fillingCutComparisonHomeomorph D F hrel (T.seam k (t, s)) =
        D.seam (e k) (A k t, s)) : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier := by
  have hnhds (t : Torus) : {p : Torus × ℝ | |p.2| < δ} ∈ nhds (t, 0) :=
    (isOpen_lt continuous_snd.abs continuous_const).mem_nhds (by simpa using hδ)
  apply T.fillingCutComparisonDiffeomorph D F hrel
  · intro k t
    have ha : ContMDiff signedCollarModel signedCollarModel ∞
        (fun p : Torus × ℝ => (A k p.1, p.2)) :=
      ((A k).contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    have hs := (D.seam (e k)).contMDiffOn.contMDiffAt
      ((D.seam (e k)).open_source.mem_nhds (by
        rw [D.seam_source]
        exact ⟨by norm_num, by norm_num⟩ : (A k t, 0) ∈ (D.seam (e k)).source))
    have h := hs.comp (t, 0) (ha (t, 0))
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hnhds t] with p hp
    exact heq k p.1 p.2 hp
  · intro k t
    let l := e.symm k
    have ha : ContMDiff signedCollarModel signedCollarModel ∞
        (fun p : Torus × ℝ => ((A l).symm p.1, p.2)) :=
      ((A l).symm.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    have hs := (T.seam l).contMDiffOn.contMDiffAt
      ((T.seam l).open_source.mem_nhds (by
        rw [T.seam_source]
        exact ⟨by norm_num, by norm_num⟩ : ((A l).symm t, 0) ∈ (T.seam l).source))
    have h := hs.comp (t, 0) (ha (t, 0))
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [hnhds t] with p hp
    have hg := heq l ((A l).symm p.1) p.2 hp
    rw [Diffeomorph.apply_symm_apply, show e l = k from e.apply_symm_apply k] at hg
    exact (congrArg (T.fillingCutComparisonHomeomorph D F hrel).symm hg).symm.trans
      ((T.fillingCutComparisonHomeomorph D F hrel).symm_apply_apply _)


theorem fillingComparison_preservesOrientation (T : TorusPresentation W)
    (D : TorusPresentation W')
    (H : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (F : W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier)
    (hcomm : ∀ x, F (T.cutMap x) = D.cutMap (H x))
    (hH : H.preservesOrientation T.cutCarrier.orientation D.cutCarrier.orientation) :
    F.preservesOrientation W.orientation W'.orientation := by
  intro w
  obtain ⟨x, rfl⟩ := T.cutMap_surjective w
  have ht := T.quotient_oriented x
  change ∃ L : TangentSpace T.cutCarrier.model x ≃ₗ[ℝ]
    TangentSpace W.model (T.cutMap x),
    (∀ v, L v = mfderiv T.cutCarrier.model W.model T.cutMap x v) ∧
      Orientation.map (Fin 3) L (T.cutCarrier.orientation.orientation x) =
        W.orientation.orientation (T.cutMap x) at ht
  obtain ⟨LT, hLT, hoT⟩ := ht
  have hd := D.quotient_oriented (H x)
  change ∃ L : TangentSpace D.cutCarrier.model (H x) ≃ₗ[ℝ]
    TangentSpace W'.model (D.cutMap (H x)),
    (∀ v, L v = mfderiv D.cutCarrier.model W'.model D.cutMap (H x) v) ∧
      Orientation.map (Fin 3) L (D.cutCarrier.orientation.orientation (H x)) =
        W'.orientation.orientation (D.cutMap (H x)) at hd
  rw [← hcomm x] at hd
  obtain ⟨LD, hLD, hoD⟩ := hd
  let LF := (F.mfderivToContinuousLinearEquiv (by simp) (T.cutMap x)).toLinearEquiv
  let LH := (H.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  have hfn : F ∘ T.cutMap = D.cutMap ∘ H := funext hcomm
  have hder := mfderiv_comp x (F.mdifferentiable (by simp) (T.cutMap x))
    (T.quotient_smooth.mdifferentiable (by simp) x)
  have hder' := mfderiv_comp x (D.quotient_smooth.mdifferentiable (by simp) (H x))
    (H.mdifferentiable (by simp) x)
  change mfderiv T.cutCarrier.model W'.model (D.cutMap ∘ H) x =
    (mfderiv D.cutCarrier.model W'.model D.cutMap (H x)).comp
      (mfderiv T.cutCarrier.model D.cutCarrier.model H x) at hder'
  rw [← hfn] at hder'
  have he : LT.trans LF = LH.trans LD := by
    ext v
    change LF (LT v) = LD (LH v)
    rw [hLT, hLD]
    exact (congrArg (fun L => L v) hder).symm.trans
      (congrArg (fun L => L v) hder')
  change Orientation.map (Fin 3) LF (W.orientation.orientation (T.cutMap x)) = _
  change Orientation.map (Fin 3) LT (T.cutCarrier.orientation.orientation x) =
    W.orientation.orientation (T.cutMap x) at hoT
  rw [← hoT]
  exact (orientation_map_trans_fin_three LT LF
    (T.cutCarrier.orientation.orientation x)).symm.trans
    ((congrArg (fun L => Orientation.map (Fin 3) L
      (T.cutCarrier.orientation.orientation x)) he).trans
      ((orientation_map_trans_fin_three LH LD
        (T.cutCarrier.orientation.orientation x)).trans
          ((congrArg (Orientation.map (Fin 3) LD) (hH x)).trans hoD)))

section CollarGerms

variable (T : TorusPresentation W) (D : TorusPresentation W')
    (H : T.cutCarrier.Carrier ≃ₘ⟮T.cutCarrier.model, D.cutCarrier.model⟯ D.cutCarrier.Carrier)
    (e : Fin T.pairing.count ≃ Fin D.pairing.count)
    (A : Fin T.pairing.count → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hl : ∀ k t r (hr0 : 0 ≤ r), r < δ →
      H (T.pairing.leftCollar k (t, halfPoint r hr0)) =
        D.pairing.leftCollar (e k) (A k t, halfPoint r hr0))
    (hr : ∀ k t r (hr0 : 0 ≤ r), r < δ →
      H (T.pairing.rightCollar k (T.pairing.matching k t, halfPoint r hr0)) =
        D.pairing.rightCollar (e k)
          (D.pairing.matching (e k) (A k t), halfPoint r hr0))

include hδ hl hr in
theorem fillingRelation_of_collarGerms (x y : T.cutCarrier.Carrier) :
    T.pairing.gluing.rel x y ↔ D.pairing.gluing.rel (H x) (H y) := by
  have hz : halfPoint 0 (le_refl 0) = halfZero := by
    apply Subtype.ext
    ext i
    rfl
  apply T.fillingCutRelation_iff_of_params D H e A
  · intro k t
    have hh := hl k t 0 (le_refl 0) hδ
    rwa [hz, T.pairing.left_zero, D.pairing.left_zero] at hh
  · intro k t
    have hh := hr k t 0 (le_refl 0) hδ
    rwa [hz, T.pairing.right_zero, D.pairing.right_zero] at hh

include hδ hδ1 hl hr in
def fillingComparisonDiffeomorph_of_collarGerms :
    W.Carrier ≃ₘ⟮W.model, W'.model⟯ W'.Carrier :=
  T.fillingCutComparisonDiffeomorph_of_seamGerms D H
    (T.fillingRelation_of_collarGerms D H e A δ hδ hl hr) e A δ hδ
    (fun k t s hs => T.fillingCutComparisonHomeomorph_seam_of_collars D H
      (T.fillingRelation_of_collarGerms D H e A δ hδ hl hr) e A δ hδ1 hl hr k t (s := s) hs)

include hδ hδ1 hl hr in
theorem fillingComparisonDiffeomorph_cutMap (x : T.cutCarrier.Carrier) :
    T.fillingComparisonDiffeomorph_of_collarGerms D H e A δ hδ hδ1 hl hr (T.cutMap x) =
      D.cutMap (H x) :=
  T.fillingCutComparisonHomeomorph_cutMap D H
    (T.fillingRelation_of_collarGerms D H e A δ hδ hl hr) x

include hδ hδ1 hl hr in
theorem fillingComparisonDiffeomorph_oriented
    (hH : H.preservesOrientation T.cutCarrier.orientation D.cutCarrier.orientation) :
    (T.fillingComparisonDiffeomorph_of_collarGerms D H e A δ hδ hδ1 hl hr).preservesOrientation
      W.orientation W'.orientation :=
  T.fillingComparison_preservesOrientation D H
    (T.fillingComparisonDiffeomorph_of_collarGerms D H e A δ hδ hδ1 hl hr)
    (T.fillingComparisonDiffeomorph_cutMap D H e A δ hδ hδ1 hl hr) hH

include hδ hδ1 hl hr in
theorem fillingComparisonDiffeomorph_free_germ
    (eE : Fin T.externalCount ≃ Fin D.externalCount)
    (ψE : Fin T.externalCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus))
    (hE : ∀ r p, p ∈ halfCollarSource → p.2.val 0 < δ →
      H (T.cutExternal.collar r p) = D.cutExternal.collar (eE r) (ψE r p.1, p.2))
    (r : Fin T.externalCount) (p : Torus × EuclideanHalfSpace 1)
    (hp : p ∈ halfCollarSource) (hlt : p.2.val 0 < δ) :
    T.fillingComparisonDiffeomorph_of_collarGerms D H e A δ hδ hδ1 hl hr
      (T.external.collar r p) = D.external.collar (eE r) (ψE r p.1, p.2) := by
  have hψ : (ψE r p.1, p.2) ∈ halfCollarSource := hp
  rw [← T.marked_collar r p hp]
  change T.fillingComparisonDiffeomorph_of_collarGerms D H e A δ hδ hδ1 hl hr
    (T.cutMap (T.cutExternal.collar r p)) = _
  rw [T.fillingComparisonDiffeomorph_cutMap, hE r p hp hlt]
  exact D.marked_collar (eE r) (ψE r p.1, p.2) hψ

end CollarGerms

end GC.Seifert.TorusPresentation
