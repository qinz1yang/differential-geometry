import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BaseMorse
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionBoundarySource
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingCompositionInterior

/-!
# Smooth embeddings into the core followed by the inclusion of the core

Lane P1X (P1 wiring), the composition lemma that closes P1W's local `sorry`
`isSmoothEmbedding_core_val_comp`: a smooth embedding `g : X → D.core` followed by
`Subtype.val : D.core → B` is a smooth embedding into the base `B`, which may have boundary.

The tree's composition lemmas for immersions need a boundaryless target model, so the proof goes
through the plane. At `x`, the ambient chart `A` of the core atlas at `g x` turns the inclusion of
the core into an immersion `core → ℝ²` whose normal form in the core's own chart is the identity
(`isImmersionAtOfComplement_ambientChart_val`); `comp_of_smoothBoundary` (bordered `X`) or
`comp_of_isInteriorPoint` (closed `X`) compose it with `g`. The result is transported back into
`B` (`isImmersionAtOfComplement_of_ambientChart`): since `val (g x)` is an interior point of `B`,
the chart `A ≫ β ≫ T ≫ J.symm` lies in the maximal atlas of `B` for a linear automorphism `T`
moving the normal-form value into `interior (range J)`; when the domain chart sends `x` to `0`,
both charts are first translated along a range-preserving direction of the model
(`translateModel`).
-/

set_option autoImplicit false

noncomputable section
open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section Translate

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (v : E)

def translateModel (hv : ∀ u, u ∈ range I ↔ u + v ∈ range I) : OpenPartialHomeomorph H H where
  toFun y := I.symm (I y + v)
  invFun y := I.symm (I y - v)
  source := univ
  target := univ
  map_source' _ _ := mem_univ _
  map_target' _ _ := mem_univ _
  left_inv' y _ := by
    rw [I.right_inv ((hv _).mp (mem_range_self y)), add_sub_cancel_right, I.left_inv]
  right_inv' y _ := by
    have h : I y - v ∈ range I := (hv _).mpr (by rw [sub_add_cancel]; exact mem_range_self y)
    rw [I.right_inv h, sub_add_cancel, I.left_inv]
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := (I.continuous_symm.comp (I.continuous.add continuous_const)).continuousOn
  continuousOn_invFun := (I.continuous_symm.comp (I.continuous.sub continuous_const)).continuousOn

variable (hv : ∀ u, u ∈ range I ↔ u + v ∈ range I)

include hv in
theorem contMDiff_translateModel : ContMDiff I I ∞ (translateModel I v hv) :=
  (I.contMDiffOn_symm (n := ∞)).comp_contMDiff
    ((contDiff_id.add contDiff_const).contMDiff.comp I.contMDiff)
    (fun y => (hv _).mp (mem_range_self y))

include hv in
theorem contMDiff_translateModel_symm : ContMDiff I I ∞ (translateModel I v hv).symm :=
  (I.contMDiffOn_symm (n := ∞)).comp_contMDiff
    ((contDiff_id.sub contDiff_const).contMDiff.comp I.contMDiff)
    (fun y => (hv _).mpr (by rw [sub_add_cancel]; exact mem_range_self y))

include hv in
theorem translateModel_apply (y : H) : I (translateModel I v hv y) = I y + v :=
  I.right_inv ((hv _).mp (mem_range_self y))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

include hv in
theorem trans_translateModel_mem_maximalAtlas {φ : OpenPartialHomeomorph M H}
    (hφ : φ ∈ IsManifold.maximalAtlas I ∞ M) :
    φ.trans (translateModel I v hv) ∈ IsManifold.maximalAtlas I ∞ M := by
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn I I ∞ (translateModel I v hv ∘ φ) _
    refine (contMDiff_translateModel I v hv).comp_contMDiffOn
      ((contMDiffOn_of_mem_maximalAtlas hφ).mono ?_)
    rw [OpenPartialHomeomorph.trans_source]
    exact inter_subset_left
  · change ContMDiffOn I I ∞ (φ.symm ∘ (translateModel I v hv).symm) _
    refine (contMDiffOn_symm_of_mem_maximalAtlas hφ).comp
      (contMDiff_translateModel_symm I v hv).contMDiffOn ?_
    intro y hy
    rw [OpenPartialHomeomorph.trans_target] at hy
    exact hy.2

omit [ChartedSpace H M] [IsManifold I ∞ M] in
include hv in
theorem trans_translateModel_source (φ : OpenPartialHomeomorph M H) :
    (φ.trans (translateModel I v hv)).source = φ.source := by
  rw [OpenPartialHomeomorph.trans_source]
  change φ.source ∩ φ ⁻¹' univ = φ.source
  simp

omit [ChartedSpace H M] [IsManifold I ∞ M] in
include hv in
theorem trans_translateModel_extend (φ : OpenPartialHomeomorph M H) (y : M) :
    (φ.trans (translateModel I v hv)).extend I y = φ.extend I y + v :=
  translateModel_apply I v hv (φ y)

end Translate

section Transfer

variable {E E' F H G M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [Nontrivial E']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

def interiorModelInverse (J : ModelWithCorners ℝ E' G) :
    PartialDiffeomorph 𝓘(ℝ, E') J E' G ∞ where
  toFun := J.symm
  invFun := J
  source := interior (range J)
  target := J ⁻¹' interior (range J)
  map_source' v hv := by
    change J (J.symm v) ∈ interior (range J)
    rwa [J.right_inv (interior_subset hv)]
  map_target' _ hy := hy
  left_inv' _ hv := J.right_inv (interior_subset hv)
  right_inv' y _ := J.left_inv y
  open_source := isOpen_interior
  open_target := isOpen_interior.preimage J.continuous
  contMDiffOn_toFun := (J.contMDiffOn_symm (n := ∞)).mono interior_subset
  contMDiffOn_invFun := J.contMDiff.contMDiffOn

def translationDiffeomorph (c : E') : PartialDiffeomorph 𝓘(ℝ, E') 𝓘(ℝ, E') E' E' ∞ where
  toFun z := z + c
  invFun z := z - c
  source := univ
  target := univ
  map_source' _ _ := mem_univ _
  map_target' _ _ := mem_univ _
  left_inv' z _ := add_sub_cancel_right z c
  right_inv' z _ := sub_add_cancel z c
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := (contDiff_id.add contDiff_const).contMDiff.contMDiffOn
  contMDiffOn_invFun := (contDiff_id.sub contDiff_const).contMDiff.contMDiffOn

def partialDiffeomorphOfMemMaximalAtlas {β : OpenPartialHomeomorph N G}
    (hβ : β ∈ IsManifold.maximalAtlas J ∞ N) : PartialDiffeomorph J J N G ∞ where
  toPartialEquiv := β.toPartialEquiv
  open_source := β.open_source
  open_target := β.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hβ
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hβ

theorem exists_mem_interior_range_ne_zero (J : ModelWithCorners ℝ E' G) :
    ∃ w ∈ interior (range J), w ≠ 0 := by
  obtain ⟨p, hp⟩ := J.nonempty_interior
  by_cases hp0 : p = 0
  · have h1 : ∀ᶠ y in 𝓝[≠] p, y ∈ interior (range J) :=
      nhdsWithin_le_nhds (isOpen_interior.mem_nhds hp)
    have h2 : ∀ᶠ y in 𝓝[≠] p, y ≠ p := self_mem_nhdsWithin
    obtain ⟨y, hy1, hy2⟩ := (h1.and h2).exists
    exact ⟨y, hy1, hp0 ▸ hy2⟩
  · exact ⟨p, hp, hp0⟩

omit [IsManifold I ∞ M] in
theorem isImmersionAtOfComplement_of_ambientChart_of_charts {f : M → N} {x : M}
    (hf : Continuous f) (A : PartialDiffeomorph J 𝓘(ℝ, E') N E' ∞) (hxA : f x ∈ A.source)
    {φ : OpenPartialHomeomorph M H}
    (hφ : φ ∈ IsManifold.maximalAtlas I ∞ M) (hxφ : x ∈ φ.source)
    (β : PartialDiffeomorph 𝓘(ℝ, E') 𝓘(ℝ, E') E' E' ∞) (hxβ : A (f x) ∈ β.source)
    (equiv : (E × F) ≃L[ℝ] E') (hnf : ∀ y ∈ φ.source, β (A (f y)) = equiv (φ.extend I y, 0))
    (hne : φ.extend I x ≠ 0) : IsImmersionAtOfComplement F I J ∞ f x := by
  obtain ⟨w₀, hw₀, hw₀0⟩ := exists_mem_interior_range_ne_zero J
  have hz : equiv (φ.extend I x, 0) ≠ 0 := by
    intro h
    apply hne
    have h' : (φ.extend I x, (0 : F)) = 0 := equiv.injective (h.trans (map_zero equiv).symm)
    exact (Prod.ext_iff.mp h').1
  obtain ⟨T, hT⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq (R := ℝ) hz hw₀0
  let b := ((A.trans β).trans T.toDiffeomorph.toPartialDiffeomorph).trans (interiorModelInverse J)
  have hbint : ∀ y, f y ∈ b.source → T (β (A (f y))) ∈ interior (range J) := fun y hy => hy.2
  have hbx : f x ∈ b.source := by
    refine ⟨⟨⟨hxA, hxβ⟩, mem_univ _⟩, ?_⟩
    change T (β (A (f x))) ∈ interior (range J)
    rw [hnf x hxφ, hT]
    exact hw₀
  have hbmax : b.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas J ∞ N :=
    b.toOpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn b.contMDiffOn_toFun
      b.contMDiffOn_invFun
  let s : Set M := φ.source ∩ f ⁻¹' b.source
  have hs : IsOpen s := φ.open_source.inter (b.open_source.preimage hf)
  let d := φ.restr s
  have hdsource : d.source = φ.source ∩ s := by
    rw [OpenPartialHomeomorph.restr_source, hs.interior_eq]
  have hdmax : d ∈ IsManifold.maximalAtlas I ∞ M :=
    restr_mem_maximalAtlas (contDiffGroupoid ∞ I) hφ hs
  have hformula (y : M) (hy : y ∈ φ.source) (hyb : f y ∈ b.source) :
      b.toOpenPartialHomeomorph.extend J (f y) = T (equiv (φ.extend I y, 0)) := by
    change J (J.symm (T (β (A (f y))))) = _
    rw [J.right_inv (interior_subset (hbint y hyb)), hnf y hy]
  refine IsImmersionAtOfComplement.mk_of_charts (equiv.trans T) d b.toOpenPartialHomeomorph
    (by rw [hdsource]; exact ⟨hxφ, hxφ, hbx⟩) hbx hdmax hbmax
    (fun y hy => by rw [hdsource] at hy; exact hy.2.2) ?_
  intro u hu
  let y := (d.extend I).symm u
  have hy : y ∈ d.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (d.extend I).map_target hu
  rw [hdsource] at hy
  change b.toOpenPartialHomeomorph.extend J (f y) = T (equiv (u, 0))
  rw [hformula y hy.1 hy.2.2]
  exact congrArg (fun z => T (equiv (z, 0))) ((d.extend I).right_inv hu)

theorem isImmersionAtOfComplement_of_ambientChart {f : M → N} {x : M} (hf : Continuous f)
    (A : PartialDiffeomorph J 𝓘(ℝ, E') N E' ∞) (hxA : f x ∈ A.source)
    (h : IsImmersionAtOfComplement F I 𝓘(ℝ, E') ∞ (fun y => A (f y)) x)
    (hv : ∃ v : E, v ≠ 0 ∧ ∀ u, u ∈ range I ↔ u + v ∈ range I) :
    IsImmersionAtOfComplement F I J ∞ f x := by
  set φ := h.domChart with hφdef
  have hφ : φ ∈ IsManifold.maximalAtlas I ∞ M := h.domChart_mem_maximalAtlas
  have hxφ : x ∈ φ.source := h.mem_domChart_source
  let β := partialDiffeomorphOfMemMaximalAtlas h.codChart_mem_maximalAtlas
  have hxβ : A (f x) ∈ β.source := h.mem_codChart_source
  have hnf : ∀ y ∈ φ.source, β (A (f y)) = h.equiv (φ.extend I y, 0) := by
    intro y hy
    have hy' : y ∈ (φ.extend I).source := by rwa [OpenPartialHomeomorph.extend_source]
    have hw := h.writtenInCharts ((φ.extend I).map_source hy')
    rw [← hφdef] at hw
    simp only [Function.comp_apply, (φ.extend I).left_inv hy'] at hw
    exact hw
  by_cases h0 : φ.extend I x = 0
  · obtain ⟨v, hv0, hv⟩ := hv
    have hnf' : ∀ y ∈ (φ.trans (translateModel I v hv)).source,
        (β.trans (translationDiffeomorph (h.equiv (v, 0)))) (A (f y)) =
          h.equiv ((φ.trans (translateModel I v hv)).extend I y, 0) := by
      intro y hy
      rw [trans_translateModel_source] at hy
      rw [trans_translateModel_extend]
      change β (A (f y)) + h.equiv (v, 0) = _
      rw [hnf y hy, ← map_add, Prod.mk_add_mk, add_zero]
    refine isImmersionAtOfComplement_of_ambientChart_of_charts hf A hxA
      (trans_translateModel_mem_maximalAtlas I v hv hφ)
      (by rw [trans_translateModel_source]; exact hxφ)
      (β.trans (translationDiffeomorph (h.equiv (v, 0)))) ⟨hxβ, mem_univ _⟩ h.equiv hnf' ?_
    rw [trans_translateModel_extend, h0, zero_add]
    exact hv0
  · exact isImmersionAtOfComplement_of_ambientChart_of_charts hf A hxA hφ hxφ β hxβ h.equiv hnf h0

end Transfer

section Core

variable {B : CompactSurface.{u}} (D : BaseMorseData B)

theorem isImmersionAtOfComplement_ambientChart_val (y : D.core.Carrier) :
    IsImmersionAtOfComplement PUnit.{1} (𝓡∂ 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞
      (fun z : D.core.Carrier => D.coreAtlas.ambientChart y z.val) y := by
  set C := D.coreAtlas
  refine IsImmersionAtOfComplement.mk_of_charts
    (ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 2)) PUnit.{1})
    (C.chart y) (OpenPartialHomeomorph.refl _) (C.mem_source y) (mem_univ _)
    (IsManifold.chart_mem_maximalAtlas y)
    (IsManifold.chart_mem_maximalAtlas (0 : EuclideanSpace ℝ (Fin 2)))
    (fun _ _ => mem_univ _) ?_
  intro u hu
  let z := ((C.chart y).extend (𝓡∂ 2)).symm u
  have hz : z ∈ (C.chart y).source := by
    simpa only [OpenPartialHomeomorph.extend_source] using
      ((C.chart y).extend (𝓡∂ 2)).map_target hu
  have h1 := OpenPartialHomeomorph.restrictSubtypes_apply
    (C.ambientChart y).toOpenPartialHomeomorph _ _ y (0 : EuclideanHalfSpace 2) (C.mem_iff y) z hz
  have h2 : ((C.chart y).extend (𝓡∂ 2)) z = u := ((C.chart y).extend (𝓡∂ 2)).right_inv hu
  change C.ambientChart y z.val = u
  exact h1.symm.trans h2

theorem isInteriorPoint_core_val (y : D.core.Carrier) :
    (SurfaceModel.model B.kind).IsInteriorPoint y.val :=
  D.isInteriorPoint_of_pos (D.level_zero_pos.trans_le y.2)

theorem exists_translation_surfaceModel (k : SurfaceModel) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧
      ∀ u, u ∈ range (SurfaceModel.model k) ↔ u + v ∈ range (SurfaceModel.model k) := by
  cases k with
  | closed =>
    refine ⟨EuclideanSpace.single 0 1, ?_, fun u => ?_⟩
    · intro h
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 0) h
      simp at this
    · simp
  | withBoundary =>
    refine ⟨EuclideanSpace.single 1 1, ?_, fun u => ?_⟩
    · intro h
      have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w 1) h
      simp at this
    · change u ∈ range (𝓡∂ 2) ↔ u + EuclideanSpace.single 1 1 ∈ range (𝓡∂ 2)
      rw [range_modelWithCornersEuclideanHalfSpace]
      simp

theorem isSmoothEmbedding_val_comp_of_core {k : SurfaceModel} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (SurfaceModel.Space k) X] [IsManifold (SurfaceModel.model k) ∞ X]
    {g : X → D.core.Carrier}
    (hg : IsSmoothEmbedding (SurfaceModel.model k) (SurfaceModel.model D.core.kind) ∞ g) :
    IsSmoothEmbedding (SurfaceModel.model k) (SurfaceModel.model B.kind) ∞
      (fun x => (g x).val) := by
  refine ⟨?_, Topology.IsEmbedding.subtypeVal.comp hg.isEmbedding⟩
  obtain ⟨F, hFadd, hFspace, hF⟩ := hg.isImmersion
  let _ := hFadd
  let _ := hFspace
  have hcont : Continuous fun x => (g x).val :=
    continuous_subtype_val.comp hg.isEmbedding.continuous
  refine IsImmersionOfComplement.isImmersion (F := F × PUnit.{1}) fun x => ?_
  have hFc : CompleteSpace F := completeSpace_of_continuousLinearEquiv_prod (hF x).equiv
  have hval := isImmersionAtOfComplement_ambientChart_val D (g x)
  have hxA : (g x).val ∈ (D.coreAtlas.ambientChart (g x)).source := D.coreAtlas.mem_source (g x)
  have hv := exists_translation_surfaceModel k
  refine isImmersionAtOfComplement_of_ambientChart hcont (D.coreAtlas.ambientChart (g x)) hxA ?_ hv
  cases k with
  | closed =>
    exact IsImmersionAtOfComplement.comp_of_isInteriorPoint (f := g)
      (g := fun z : D.core.Carrier => D.coreAtlas.ambientChart (g x) z.val) (hF x) hval (by simp)
      (BoundarylessManifold.isInteriorPoint (I := 𝓡 2))
  | withBoundary =>
    exact IsImmersionAtOfComplement.comp_of_smoothBoundary (f := g)
      (g := fun z : D.core.Carrier => D.coreAtlas.ambientChart (g x) z.val) (hF x) hval

end Core

end GC.Seifert
