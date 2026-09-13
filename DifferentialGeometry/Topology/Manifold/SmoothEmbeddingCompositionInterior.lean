import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false
noncomputable section
open Function Set Topology Filter
open scoped Manifold ContDiff Topology

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} [IsManifold I n M] {e e' : OpenPartialHomeomorph M H} {x : M}

lemma mem_interior_range_of_mem_interior_range_of_mem_maximalAtlas (hn : n ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M)
    (hex : x ∈ e.source) (hex' : x ∈ e'.source)
    (hx : e.extend I x ∈ interior (e.extend I).target) :
    e'.extend I x ∈ interior (e'.extend I).target := by
  let φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.source := contDiffOn_extendCoordChange he he'
  suffices h : Function.Surjective (fderivWithin 𝕜 φ φ.source (e.extend I x)) →
      e'.extend I x ∈ interior (range I) by
    refine e'.mem_interior_extend_target (by simp [hex']) <| h ?_
    exact (isInvertible_fderivWithin_extendCoordChange hn he he' <| by simp [hex, hex']).surjective
  intro hφx'
  wlog _ : IsRCLikeNormedField 𝕜
  · simp [I.range_eq_univ_of_not_isRCLikeNormedField ‹_›]
  let _ := IsRCLikeNormedField.rclike 𝕜
  let _ : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have hφx : φ.source ∈ 𝓝 (e.extend I x) := by
    simp_rw [φ, extendCoordChange, PartialEquiv.trans_source, PartialEquiv.symm_source,
      Filter.inter_mem_iff, mem_interior_iff_mem_nhds.1 hx, true_and, e'.extend_source]
    exact e.extend_preimage_mem_nhds hex <| e'.open_source.mem_nhds hex'
  rw [← ContinuousLinearMap.coe_restrictScalars' (R := ℝ),
    (hφ.differentiableOn hn _ (by simp [φ, hex, hex'])).restrictScalars_fderivWithin (𝕜 := ℝ)
      (uniqueDiffWithinAt_of_mem_nhds hφx), fderivWithin_of_mem_nhds <| hφx] at hφx'
  have hφx_eq : e'.extend I x = φ (e.extend I x) := by simp [φ, hex]
  rw [hφx_eq]
  replace hφ := ((hφ.restrict_scalars ℝ).differentiableOn hn).differentiableAt hφx
  exact hφ.mem_interior_convex_of_surjective_fderiv hφx I.convex_range I.isClosed_range
    I.nonempty_interior (φ.mapsTo.mono_right <| by simp [φ, inter_assoc]) hφx'

lemma mem_interior_range_iff_of_mem_maximalAtlas (hn : n ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I n M) (he' : e' ∈ IsManifold.maximalAtlas I n M)
    (hex : x ∈ e.source) (hex' : x ∈ e'.source) :
    e.extend I x ∈ interior (e.extend I).target ↔
      e'.extend I x ∈ interior (e'.extend I).target := by
  constructor
  · exact mem_interior_range_of_mem_interior_range_of_mem_maximalAtlas (I := I) hn he he' hex hex'
  · exact mem_interior_range_of_mem_interior_range_of_mem_maximalAtlas (I := I) hn he' he hex' hex

lemma isInteriorPoint_iff_of_mem_maximalAtlas (hn : n ≠ 0)
    (he : e ∈ IsManifold.maximalAtlas I n M) (hx : x ∈ e.source) :
    I.IsInteriorPoint x ↔ e.extend I x ∈ interior (e.extend I).target := by
  rw [isInteriorPoint_iff]
  exact mem_interior_range_iff_of_mem_maximalAtlas (I := I) hn (IsManifold.chart_mem_maximalAtlas x) he
    (mem_chart_source H x) hx

end ModelWithCorners

namespace Manifold

section CompInterior

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' E'' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [CompleteSpace F']
  {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G} {J' : ModelWithCorners 𝕜 E'' G'}
  [J'.Boundaryless]
  {n : ℕ∞ω} {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {f : M → N} {g : N → N'} {x : M}

theorem IsImmersionAtOfComplement.comp_of_isInteriorPoint
    (hf : IsImmersionAtOfComplement F I J n f x)
    (hg : IsImmersionAtOfComplement F' J J' n g (f x))
    (hn : n ≠ 0) (hxI : I.IsInteriorPoint x) :
    IsImmersionAtOfComplement (F × F') I J' n (g ∘ f) x := by
  classical
  set A := hf.domChart with hA
  set B := hf.codChart with hB
  set C := hg.domChart with hC
  set D := hg.codChart with hD
  set ef : (E × F) ≃L[𝕜] E' := hf.equiv with hef
  set eg : (E' × F') ≃L[𝕜] E'' := hg.equiv with heg
  have hfOn : ContMDiffOn I J n f A.source := by
    rw [hA]; exact hf.contMDiffOn_domChart
  have hgOn : ContMDiffOn J J' n g C.source := by
    rw [hC]; exact hg.contMDiffOn_domChart
  set s₀ : Set M := A.source ∩ f ⁻¹' C.source with hs₀
  have hs₀open : IsOpen s₀ := by
    rw [hs₀]
    exact hfOn.continuousOn.isOpen_inter_preimage A.open_source C.open_source
  have hxs₀ : x ∈ s₀ := by
    rw [hs₀]; exact ⟨hf.mem_domChart_source, hg.mem_domChart_source⟩
  set A' : OpenPartialHomeomorph M H := A.restr s₀ with hA'
  have hA'mem : A' ∈ IsManifold.maximalAtlas I n M := by
    rw [hA', hA, hs₀]
    exact restr_mem_maximalAtlas (contDiffGroupoid n I) hf.domChart_mem_maximalAtlas hs₀open
  have hA'src : A'.source = s₀ := by
    rw [hA', OpenPartialHomeomorph.restr_source' A s₀ hs₀open, hs₀, Set.inter_eq_right]
    intro z hz
    exact hz.1
  set T : Set E := (A'.extend I).target with hT
  set v₀ : E := (A'.extend I) x with hv₀
  have hAx : (A.extend I) x = v₀ := by
    rw [hv₀, hA']
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.restr_apply,
      Function.comp_apply]
  have hAextimage : (A.extend I) '' s₀ = T := by
    rw [hT, hA', OpenPartialHomeomorph.extend_target_eq_image_source, hA'src]
    exact Set.image_congr fun y _ => by
      simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.restr_apply,
        Function.comp_apply]
  have hTmem : T ∈ 𝓝 v₀ := by
    have hinterA : (A.extend I) x ∈ interior (range I) := by
      have hpref : (chartAt H x).extend I x ∈ interior ((chartAt H x).extend I).target :=
        ModelWithCorners.isInteriorPoint_iff.mp hxI
      have hAint : (A.extend I) x ∈ interior ((A.extend I).target) :=
        ModelWithCorners.mem_interior_range_of_mem_interior_range_of_mem_maximalAtlas (I := I) hn
          (IsManifold.chart_mem_maximalAtlas x) hf.domChart_mem_maximalAtlas
          (mem_chart_source H x) hf.mem_domChart_source hpref
      exact OpenPartialHomeomorph.interior_extend_target_subset_interior_range A hAint
    have := A.extend_image_nhds_mem_nhds_of_mem_interior_range hf.mem_domChart_source hinterA
      (hs₀open.mem_nhds hxs₀)
    rwa [hAextimage, hAx] at this
  obtain ⟨W, hWsub, hWopen, hv₀W⟩ := mem_nhds_iff.mp hTmem
  have hv₀T : v₀ ∈ T := hWsub hv₀W
  have hgfOn : ContMDiffOn I J' n (g ∘ f) s₀ := by
    refine hgOn.comp (hfOn.mono inter_subset_left) (fun z hz => ?_)
    rw [hs₀] at hz
    exact hz.2
  set Φ : E → E'' := fun v => (D.extend J') ((g ∘ f) ((A'.extend I).symm v)) with hΦ
  have hΦcont : ContDiffOn 𝕜 n Φ T := by
    have hsymm : ContMDiffOn 𝓘(𝕜, E) I n (fun v : E => (A'.extend I).symm v) T := by
      rw [hT, OpenPartialHomeomorph.extend_target']
      exact contMDiffOn_extend_symm hA'mem
    have hmid : ContMDiffOn I 𝓘(𝕜, E'') n (fun z => (D.extend J') ((g ∘ f) z)) s₀ :=
      (D.contMDiffOn_extend (by rw [hD]; exact hg.codChart_mem_maximalAtlas)).comp hgfOn
        (fun z hz => by
          rw [hs₀] at hz
          exact hg.source_subset_preimage_source hz.2)
    have hcomp : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E'') n
        (fun v : E => (D.extend J') ((g ∘ f) ((A'.extend I).symm v))) T :=
      hmid.comp hsymm (fun v hv => by
        have hvs : (A'.extend I).symm v ∈ (A'.extend I).source :=
          ((A'.extend I).symm).map_source (by rwa [hT] at hv)
        rw [OpenPartialHomeomorph.extend_source, hA'src] at hvs
        exact hvs)
    exact (contMDiffOn_iff_contDiffOn).mp hcomp
  set τ : PartialEquiv E' E' := J.extendCoordChange B C with hτ
  have hcoord : (B.extend J) (f x) = ef (v₀, 0) := by
    have hxT : (A.extend I) x ∈ (A.extend I).target :=
      (A.extend I).map_source (by rw [OpenPartialHomeomorph.extend_source]; exact hf.mem_domChart_source)
    have h := hf.writtenInCharts hxT
    simp only [Function.comp_apply] at h
    rw [(A.extend I).left_inv (by rw [OpenPartialHomeomorph.extend_source]; exact hf.mem_domChart_source)] at h
    rw [hAx] at h
    rw [hef]
    exact h
  have hp₀mem : ef (v₀, 0) ∈ τ.source := by
    rw [← hcoord, hτ, hB, hC,
      ← OpenPartialHomeomorph.extend_image_source_inter (I := J) (f := hf.codChart) (f' := hg.domChart)]
    exact mem_image_of_mem _ ⟨hf.source_subset_preimage_source hf.mem_domChart_source,
      hg.mem_domChart_source⟩
  set Dτ : E' →L[𝕜] E' := fderivWithin 𝕜 τ τ.source (ef (v₀, 0)) with hDτ
  have hDτinv : Dτ.IsInvertible := by
    rw [hDτ, hτ, hB, hC]
    exact J.isInvertible_fderivWithin_extendCoordChange hn hf.codChart_mem_maximalAtlas
      hg.domChart_mem_maximalAtlas hp₀mem
  set Hτ : E' ≃L[𝕜] E' := Classical.choose hDτinv with hHτ
  have hHτcoe : (Hτ : E' →L[𝕜] E') = Dτ := Classical.choose_spec hDτinv
  have hΦderiv : HasFDerivAt Φ
      (((eg.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E' F')).comp Dτ).comp
        (ef.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E F))) v₀ := by
    have hL2 := IsImmersionAtOfComplement.hasFDerivWithinAt_writtenInCharts_comp hf hg hs₀open hxs₀
      (by intro z hz; rw [hs₀] at hz; exact hz) hn
    rw [← hA, ← hB, ← hC, ← hD, ← hef, ← heg, ← hτ, ← hDτ, ← hv₀, ← hA', ← hT] at hL2
    exact hL2.hasFDerivAt hTmem
  set e_comp : (E × (F × F')) ≃L[𝕜] E'' :=
    (ContinuousLinearEquiv.prodAssoc 𝕜 E F F').symm.trans
      (((ef.trans Hτ).prodCongr (ContinuousLinearEquiv.refl 𝕜 F')).trans eg) with hecomp
  set Θ : E × (F × F') → E'' := fun p => Φ p.1 + e_comp (0, p.2) with hΘ
  have hΘcont : ContDiffOn 𝕜 n Θ (T ×ˢ univ) := by
    have h1 : ContDiffOn 𝕜 n (fun p : E × (F × F') => Φ p.1) (T ×ˢ univ) :=
      hΦcont.comp contDiffOn_fst (fun p hp => hp.1)
    have h2 : ContDiffOn 𝕜 n (fun p : E × (F × F') => e_comp (0, p.2)) (T ×ˢ univ) :=
      (e_comp.toContinuousLinearMap.comp
        ((ContinuousLinearMap.inr 𝕜 E (F × F')).comp
          (ContinuousLinearMap.snd 𝕜 E (F × F')))).contDiff.contDiffOn
    simpa only [hΘ, Pi.add_apply] using h1.add h2
  have hval : ∀ (a : E) (u : F) (z : F'),
      (e_comp : E × (F × F') →L[𝕜] E'') (a, (u, z)) =
        (eg : (E' × F') →L[𝕜] E'')
          ((Hτ : E' →L[𝕜] E') ((ef : (E × F) →L[𝕜] E') (a, u)), z) := by
    intro a u z
    simp only [hecomp, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.prodAssoc_symm_apply, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.refl_apply]
  have hlin : (((eg.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E' F')).comp Dτ).comp
        (ef.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E F))).comp
          (ContinuousLinearMap.fst 𝕜 E (F × F')) +
      (e_comp.toContinuousLinearMap.comp ((ContinuousLinearMap.inr 𝕜 E (F × F')).comp
        (ContinuousLinearMap.snd 𝕜 E (F × F')))) = (e_comp : E × (F × F') →L[𝕜] E'') := by
    apply ContinuousLinearMap.ext
    rintro ⟨a, u, z⟩
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply]
    simp only [hval]
    rw [← hHτcoe, ← map_add]
    simp only [Prod.mk_add_mk, zero_add]
    rw [← (Hτ : E' →L[𝕜] E').map_add, ← (ef : (E × F) →L[𝕜] E').map_add]
    simp only [Prod.mk_add_mk, add_zero, zero_add]
  have hΘderiv : HasFDerivAt Θ (e_comp : E × (F × F') →L[𝕜] E'') (v₀, 0) := by
    have h1 : HasFDerivAt (fun p : E × (F × F') => Φ p.1)
        ((((eg.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E' F')).comp Dτ).comp
          (ef.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E F))).comp
            (ContinuousLinearMap.fst 𝕜 E (F × F'))) (v₀, 0) :=
      (hΦderiv.comp (v₀, 0) (ContinuousLinearMap.fst 𝕜 E (F × F')).hasFDerivAt).congr_of_eventuallyEq
        (Filter.EventuallyEq.of_eq (funext fun p => rfl))
    have hpair : HasFDerivAt (fun p : E × (F × F') => ((0 : E), p.2))
        ((ContinuousLinearMap.inr 𝕜 E (F × F')).comp
          (ContinuousLinearMap.snd 𝕜 E (F × F'))) (v₀, 0) :=
      ((hasFDerivAt_prodMk_right (0 : E) (0 : F × F')).comp (v₀, 0)
        (ContinuousLinearMap.snd 𝕜 E (F × F')).hasFDerivAt).congr_of_eventuallyEq
        (Filter.EventuallyEq.of_eq (funext fun p => rfl))
    have h2 : HasFDerivAt (fun p : E × (F × F') => e_comp (0, p.2))
        (e_comp.toContinuousLinearMap.comp ((ContinuousLinearMap.inr 𝕜 E (F × F')).comp
          (ContinuousLinearMap.snd 𝕜 E (F × F')))) (v₀, 0) :=
      (e_comp.toContinuousLinearMap.hasFDerivAt.comp (v₀, 0) hpair).congr_of_eventuallyEq
        (Filter.EventuallyEq.of_eq (funext fun p => rfl))
    have hsum : HasFDerivAt (fun p : E × (F × F') => Φ p.1 + e_comp (0, p.2))
        ((((eg.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E' F')).comp Dτ).comp
          (ef.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E F))).comp
            (ContinuousLinearMap.fst 𝕜 E (F × F')) +
          (e_comp.toContinuousLinearMap.comp ((ContinuousLinearMap.inr 𝕜 E (F × F')).comp
            (ContinuousLinearMap.snd 𝕜 E (F × F'))))) (v₀, 0) :=
      (h1.add h2).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (funext fun p => rfl))
    rw [hlin] at hsum
    exact hsum.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (funext fun p => rfl))
  obtain ⟨e, hve, hesub, hecont, heinv, heeq⟩ :=
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv_of_ne_zero hn
      (hΘcont.mono (Set.prod_mono hWsub (Subset.refl univ))) (hWopen.prod isOpen_univ)
      ⟨hv₀W, mem_univ _⟩ hΘderiv
  have hAext : ⇑(A.extend I) = I ∘ ⇑A := OpenPartialHomeomorph.extend_coe A
  let U : Set E := {v : E | (v, 0) ∈ e.source}
  have hUopen : IsOpen U := e.open_source.preimage (continuous_id.prodMk continuous_const)
  have hv₀U : v₀ ∈ U := hve
  let s : Set M := A.source ∩ (A.extend I) ⁻¹' U ∩ s₀
  have hsopen : IsOpen s := by
    have h1 : IsOpen (A.source ∩ ⇑A ⁻¹' (I ⁻¹' U)) :=
      A.isOpen_inter_preimage (I.continuous.isOpen_preimage U hUopen)
    have h2 : A.source ∩ ⇑A ⁻¹' (I ⁻¹' U) = A.source ∩ ⇑(A.extend I) ⁻¹' U := by
      rw [hAext, Set.preimage_comp]
    rw [h2] at h1
    exact h1.inter hs₀open
  have hxs : x ∈ s :=
    ⟨⟨hf.mem_domChart_source, by simp only [Set.mem_preimage]; rw [hAx]; exact hv₀U⟩, hxs₀⟩
  have hss₀ : s ⊆ s₀ := inter_subset_right
  have hsA : s ⊆ A.source := fun y hy => hy.1.1
  have hsub : s ⊆ A.source ∩ f ⁻¹' C.source := fun y hy => by
    rw [← hs₀] at ⊢
    exact hss₀ hy
  have hAsource : (A.restr s).source = A.source ∩ s :=
    OpenPartialHomeomorph.restr_source' A s hsopen
  let Jop : OpenPartialHomeomorph G' E'' := J'.toHomeomorph.toOpenPartialHomeomorph
  let eop : OpenPartialHomeomorph (E × (F × F')) E'' :=
    e_comp.toHomeomorph.toOpenPartialHomeomorph
  let Y : OpenPartialHomeomorph G' G' := Jop.trans ((e.symm.trans eop).trans Jop.symm)
  let Sig : OpenPartialHomeomorph N' G' := D.trans Y
  have hJ'right : ∀ u : E'', J' (J'.symm u) = u := fun u =>
    J'.right_inv (by rw [J'.range_eq_univ]; exact mem_univ u)
  have hYapply : ∀ g ∈ Y.source, Y g = J'.symm (e_comp (e.symm (J' g))) := by
    intro g hg
    simp only [Y, OpenPartialHomeomorph.trans_apply, Jop, eop,
      Homeomorph.toOpenPartialHomeomorph_apply, Homeomorph.toOpenPartialHomeomorph_symm_apply,
      ModelWithCorners.toHomeomorph_apply, ModelWithCorners.toHomeomorph_symm_apply,
      ContinuousLinearEquiv.coe_toHomeomorph]
  have hJop_apply : ∀ g : G', Jop g = J' g := by
    intro g
    simp only [Jop, Homeomorph.toOpenPartialHomeomorph_apply, ModelWithCorners.toHomeomorph_apply]
  have heop_source : eop.source = univ := Homeomorph.toOpenPartialHomeomorph_source _
  have hYsource : Y.source = {g : G' | J' g ∈ e.target} := by
    have hZ : ((e.symm.trans eop).trans Jop.symm).source = e.target := by
      rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.symm_source,
        Homeomorph.toOpenPartialHomeomorph_source, Homeomorph.toOpenPartialHomeomorph_target]
      simp only [Set.preimage_univ, Set.inter_univ]
    have hYsrc : Y.source = Jop.source ∩ Jop ⁻¹' ((e.symm.trans eop).trans Jop.symm).source := by
      simp only [Y, OpenPartialHomeomorph.trans_source]
    rw [hYsrc, hZ, Homeomorph.toOpenPartialHomeomorph_source]
    ext g
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_univ, true_and,
      hJop_apply]
  have himg : Y.target = Y '' Y.source := (PartialEquiv.image_source_eq_target Y.toPartialEquiv).symm
  have hYsymm_apply : ∀ g ∈ Y.target, J' (Y.symm g) = e (e_comp.symm (J' g)) := by
    intro g hg
    have hgS : Y.symm g ∈ Y.source := Y.map_target hg
    have h2 : g = J'.symm (e_comp (e.symm (J' (Y.symm g)))) := by
      have h := hYapply (Y.symm g) hgS
      simpa only [Y.right_inv hg] using h
    have h3 : e_comp (e.symm (J' (Y.symm g))) = J' g := by
      have h := congrArg J' h2
      simpa only [hJ'right] using h.symm
    have h4 : e.symm (J' (Y.symm g)) = e_comp.symm (J' g) := by
      have h := congrArg e_comp.symm h3
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
    have hmem : J' (Y.symm g) ∈ e.target := by
      have h : Y.symm g ∈ ({g : G' | J' g ∈ e.target} : Set G') := hYsource ▸ hgS
      exact h
    rw [← h4]
    exact (e.right_inv hmem).symm
  have hYmem : Y ∈ contDiffGroupoid n J' := by
    unfold contDiffGroupoid
    rw [mem_groupoid_of_pregroupoid]
    constructor
    · have hbase : ContDiffOn 𝕜 n (fun u : E'' => e_comp (e.symm u)) e.target :=
        e_comp.toContinuousLinearMap.contDiff.comp_contDiffOn heinv
      refine (hbase.mono ?_).congr (fun u hu => ?_)
      · intro u hu
        have hmem : J'.symm u ∈ Y.source := hu.1
        rw [hYsource] at hmem
        have hmem' : J' (J'.symm u) ∈ e.target := hmem
        rwa [hJ'right] at hmem'
      · simpa only [Function.comp_apply, hJ'right] using
          congrArg J' (hYapply (J'.symm u) hu.1)
    · have hbase : ContDiffOn 𝕜 n (fun u : E'' => e (e_comp.symm u))
          (e_comp.symm ⁻¹' e.source) :=
        hecont.comp (e_comp.symm.toContinuousLinearMap.contDiff.contDiffOn)
          (fun _ h => h)
      refine (hbase.mono ?_).congr (fun u hu => ?_)
      · intro u hu
        have hmem : J'.symm u ∈ Y.target := hu.1
        rw [himg] at hmem
        obtain ⟨g', hg'src, hg'eq⟩ := hmem
        have h1 : e_comp (e.symm (J' g')) = u := by
          have h : J' (Y g') = u := by
            have h0 := congrArg J' hg'eq
            simpa only [hJ'right] using h0
          rw [hYapply g' hg'src, hJ'right] at h
          exact h
        have h2 : e.symm (J' g') = e_comp.symm u := by
          have h := congrArg e_comp.symm h1
          simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
        simp only [Set.mem_preimage]
        rw [← h2]
        exact e.map_target (by rw [hYsource] at hg'src; exact hg'src)
      · simpa only [Function.comp_apply, hJ'right] using hYsymm_apply (J'.symm u) hu.1
  have hSigMem : Sig ∈ IsManifold.maximalAtlas J' n N' := by
    rw [IsManifold.mem_maximalAtlas_iff]
    exact StructureGroupoid.trans_mem_maximalAtlas (contDiffGroupoid n J') hg.codChart_mem_maximalAtlas hYmem
  have hSigext : ∀ n ∈ Sig.source, (Sig.extend J') n = e_comp (e.symm ((D.extend J') n)) := by
    intro n hn
    have hn' : D n ∈ Y.source := hn.2
    calc (Sig.extend J') n = J' (Y (D n)) := by
          simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply, Sig,
            OpenPartialHomeomorph.trans_apply]
      _ = J' (J'.symm (e_comp (e.symm (J' (D n))))) := by rw [hYapply (D n) hn']
      _ = e_comp (e.symm (J' (D n))) := hJ'right _
      _ = e_comp (e.symm ((D.extend J') n)) := by
          simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply]
  have hSigextg : ∀ y ∈ (g ∘ f) ⁻¹' Sig.source,
      (Sig.extend J') (g (f y)) = e_comp (e.symm ((D.extend J') (g (f y)))) :=
    fun y hy => hSigext (g (f y)) hy
  have hA'y : ∀ y ∈ s, y ∈ A'.source := by
    intro y hy
    rw [hA'src]
    exact hss₀ hy
  have hA'ext : ∀ y ∈ s, (A'.extend I) y = (A.extend I) y := by
    intro y hy
    simp only [OpenPartialHomeomorph.extend_coe, hA', OpenPartialHomeomorph.restr_apply,
      Function.comp_apply]
  have hΦeq : ∀ y ∈ s, (D.extend J') ((g ∘ f) y) = Φ ((A.extend I) y) := by
    intro y hy
    have h2 : (A'.extend I).symm ((A.extend I) y) = y := by
      rw [← hA'ext y hy]
      exact (A'.extend I).left_inv (by rw [OpenPartialHomeomorph.extend_source]; exact hA'y y hy)
    rw [hΦ]
    simp only [h2]
  have hΦΘ : ∀ y ∈ s, Φ ((A.extend I) y) = e (((A.extend I) y), 0) := by
    intro y hy
    have hz : e_comp ((0 : E), (0 : F × F')) = (0 : E'') := by
      have h0 : ((0 : E), (0 : F × F')) = (0 : E × (F × F')) := rfl
      rw [h0, map_zero]
    have h2 : Θ (((A.extend I) y), 0) = Φ ((A.extend I) y) := by
      simp only [hΘ, hz, add_zero]
    rw [heeq (((A.extend I) y, 0)), h2]
  have hvU : ∀ y ∈ s, ((A.extend I) y, 0) ∈ e.source := by
    intro y hy
    exact hy.1.2
  have hsig_of_mem : ∀ y ∈ s, (g ∘ f) y ∈ Sig.source := by
    intro y hy
    have hD : f y ∈ C.source := (hs₀ ▸ hss₀ hy).2
    refine ⟨hg.source_subset_preimage_source hD, ?_⟩
    rw [hYsource]
    simp only [OpenPartialHomeomorph.symm_symm, Set.mem_preimage]
    have h1 : (D.extend J') ((g ∘ f) y) = J' (D ((g ∘ f) y)) := by
      simp only [OpenPartialHomeomorph.extend_coe, Function.comp_apply]
    have hgoal : J' (D ((g ∘ f) y)) ∈ e.target := by
      rw [← h1, hΦeq y hy, hΦΘ y hy]
      exact e.map_source (hvU y hy)
    exact hgoal
  have hwritten : Set.EqOn ((Sig.extend J') ∘ (g ∘ f) ∘ ((A.restr s).extend I).symm)
      (e_comp ∘ (fun v : E => (v, 0))) ((A.restr s).extend I).target := by
    intro v hv
    have hvs : ((A.restr s).extend I).symm v ∈ (A.restr s).source := by
      have h := (((A.restr s).extend I).symm).map_source hv
      rwa [PartialEquiv.symm_target, OpenPartialHomeomorph.extend_source] at h
    rw [hAsource] at hvs
    have hy : ((A.restr s).extend I).symm v ∈ s := hvs.2
    have hvE : ((A.restr s).extend I) (((A.restr s).extend I).symm v) = v :=
      PartialEquiv.right_inv _ hv
    have hAag : ∀ z ∈ (A.restr s).source, (A.extend I) z = ((A.restr s).extend I) z := by
      intro z hz
      simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.restr_apply,
        Function.comp_apply]
    have h2 : (A.extend I) (((A.restr s).extend I).symm v) = v := by
      rw [hAag _ (by rw [hAsource]; exact hvs), hvE]
    have hΦv : Φ v = e (v, 0) := by
      rw [← h2, hΦΘ _ hy]
    have hvU' : (v, 0) ∈ e.source := by
      rw [← h2]
      exact hvU _ hy
    simp only [Function.comp_apply]
    have h3 : (D.extend J') (g (f (((A.restr s).extend I).symm v))) = Φ v := by
      have h3' : (D.extend J') ((g ∘ f) (((A.restr s).extend I).symm v))
          = Φ ((A.extend I) (((A.restr s).extend I).symm v)) := hΦeq _ hy
      rw [h2] at h3'
      exact h3'
    rw [hSigextg _ (hsig_of_mem _ hy), h3, hΦv]
    exact congrArg e_comp (e.left_inv hvU')
  refine IsImmersionAtOfComplement.mk_of_charts e_comp (A.restr s) Sig ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hAsource]
    exact ⟨hf.mem_domChart_source, hxs⟩
  · exact hsig_of_mem x hxs
  · exact restr_mem_maximalAtlas (contDiffGroupoid n I) hf.domChart_mem_maximalAtlas hsopen
  · exact hSigMem
  · intro y hy
    rw [hAsource] at hy
    exact hsig_of_mem y hy.2
  · exact hwritten

end CompInterior

section CompBoundarylessManifold

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type v} {E' E'' F F' : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [CompleteSpace F']
  {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G} {J' : ModelWithCorners 𝕜 E'' G'}
  [J'.Boundaryless]
  {n : ℕ∞ω} {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {f : M → N} {g : N → N'}

theorem IsImmersionOfComplement.comp_of_boundarylessManifold [BoundarylessManifold I M]
    (hf : IsImmersionOfComplement F I J n f) (hg : IsImmersionOfComplement F' J J' n g)
    (hn : n ≠ 0) : IsImmersionOfComplement (F × F') I J' n (g ∘ f) := by
  exact fun x => IsImmersionAtOfComplement.comp_of_isInteriorPoint (hf x) (hg (f x)) hn
    (BoundarylessManifold.isInteriorPoint (I := I) (x := x))

end CompBoundarylessManifold

section CompBoundarylessUniverse

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type v} {E' E'' F F' : Type u}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [CompleteSpace E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G} {J' : ModelWithCorners 𝕜 E'' G'}
  [J'.Boundaryless]
  {n : ℕ∞ω} {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {f : M → N} {g : N → N'}

theorem IsImmersion.comp_of_boundarylessManifold [BoundarylessManifold I M]
    (hf : IsImmersion I J n f) (hg : IsImmersion J J' n g) (hn : n ≠ 0) :
    IsImmersion I J' n (g ∘ f) := by
  obtain ⟨F, hFc, hFs, hf⟩ := hf
  obtain ⟨F', hF'c, hF's, hg⟩ := hg
  let _ := hFc
  let _ := hFs
  let _ := hF'c
  let _ := hF's
  by_cases hM : IsEmpty M
  · exact ⟨PUnit, inferInstance, inferInstance, fun x => (hM.false x).elim⟩
  · have hne : Nonempty M := not_isEmpty_iff.mp hM
    let x : M := Classical.choice hne
    have : CompleteSpace F := completeSpace_of_continuousLinearEquiv_prod (hf x).equiv
    have : CompleteSpace F' := completeSpace_of_continuousLinearEquiv_prod (hg (f x)).equiv
    exact ⟨F × F', inferInstance, inferInstance,
      IsImmersionOfComplement.comp_of_boundarylessManifold hf hg hn⟩

theorem IsSmoothEmbedding.comp_of_boundarylessManifold [BoundarylessManifold I M]
    (hg : IsSmoothEmbedding J J' n g) (hf : IsSmoothEmbedding I J n f) (hn : n ≠ 0) :
    IsSmoothEmbedding I J' n (g ∘ f) :=
  ⟨IsImmersion.comp_of_boundarylessManifold hf.isImmersion hg.isImmersion hn,
    hg.isEmbedding.comp hf.isEmbedding⟩

end CompBoundarylessUniverse

example :
    IsImmersionAt (𝓡∂ 1) 𝓘(ℝ) ∞
      (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) (⟨1 / 2, by norm_num⟩ : Set.Icc (0 : ℝ) 1) :=
  ⟨_, inferInstance, inferInstance,
    IsImmersionAtOfComplement.comp_of_isInteriorPoint
      (f := id) (g := Subtype.val) (F := PUnit) (F' := Unit)
      (IsImmersionOfComplement.id (I := 𝓡∂ 1) (M := Set.Icc (0 : ℝ) 1)
        (⟨1 / 2, by norm_num⟩ : Set.Icc (0 : ℝ) 1))
      (isImmersionOfComplement_subtypeVal_Icc (x := 0) (y := 1)
        (⟨1 / 2, by norm_num⟩ : Set.Icc (0 : ℝ) 1))
      (by simp) (Icc_isInteriorPoint_interior ⟨by norm_num, by norm_num⟩)⟩

end Manifold
