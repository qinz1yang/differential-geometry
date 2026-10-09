/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.SmoothEmbedding
import DifferentialGeometry.Analysis.Calculus.Inverse.LocalInverse

set_option autoImplicit false
noncomputable section
open Function Set Manifold
open scoped Manifold ContDiff Topology

namespace Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E'' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {J' : ModelWithCorners 𝕜 E'' G'}
  {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω} {f : M → N} {g : N → N'} {x : M}

theorem IsImmersionAtOfComplement.writtenInCharts_comp
    (hf : IsImmersionAtOfComplement F I J n f x)
    (hg : IsImmersionAtOfComplement F' J J' n g (f x))
    {s : Set M} (hsopen : IsOpen s)
    (hsub : s ⊆ hf.domChart.source ∩ f ⁻¹' hg.domChart.source)
    {v : E} (hv : v ∈ ((hf.domChart.restr s).extend I).target) :
    (hg.codChart.extend J') ((g ∘ f) (((hf.domChart.restr s).extend I).symm v)) =
      hg.equiv (J.extendCoordChange hf.codChart hg.domChart (hf.equiv (v, 0)), 0) := by
  set A := hf.domChart with hA
  set B := hf.codChart with hB
  set C := hg.domChart with hC
  set D := hg.codChart with hD
  set y : M := ((A.restr s).extend I).symm v with hy
  have hys : y ∈ (A.restr s).source := by
    have h1 : ((A.restr s).extend I).symm v ∈ (((A.restr s).extend I).symm).target :=
      (((A.restr s).extend I).symm).map_source hv
    rw [PartialEquiv.symm_target, OpenPartialHomeomorph.extend_source] at h1
    exact h1
  have hys' : y ∈ A.source ∩ s := by
    rwa [A.restr_source' s hsopen] at hys
  have hysA : y ∈ A.source := hys'.1
  have hysAe : y ∈ (A.extend I).source := by rwa [OpenPartialHomeomorph.extend_source]
  have hysT : (A.extend I) y ∈ (A.extend I).target := (A.extend I).map_source hysAe
  have hyv : (A.extend I) y = v := by
    have h1 : ((A.restr s).extend I) y = v := PartialEquiv.right_inv _ hv
    rwa [OpenPartialHomeomorph.extend_coe] at h1
  have hfyB : f y ∈ B.source := hf.source_subset_preimage_source hysA
  have hfyBs : f y ∈ (B.extend J).source := by
    rwa [OpenPartialHomeomorph.extend_source]
  have hfyC : f y ∈ C.source := (hsub hys'.2).2
  have hfyCe : f y ∈ (C.extend J).source := by rwa [OpenPartialHomeomorph.extend_source]
  have hteq : J.extendCoordChange B C ((B.extend J) (f y)) = (C.extend J) (f y) := by
    simp only [ModelWithCorners.extendCoordChange, PartialEquiv.trans_apply]
    rw [PartialEquiv.left_inv _ hfyBs]
  have hCtarget : (C.extend J) (f y) ∈ (C.extend J).target :=
    (C.extend J).map_source hfyCe
  have hg' : (D.extend J') (g (f y)) = hg.equiv ((C.extend J) (f y), 0) := by
    have h := hg.writtenInCharts hCtarget
    simp only [Function.comp_apply] at h
    rwa [(C.extend J).left_inv hfyCe] at h
  have hf' : (B.extend J) (f y) = hf.equiv ((A.extend I) y, 0) := by
    have h := hf.writtenInCharts hysT
    simp only [Function.comp_apply] at h
    rwa [(A.extend I).left_inv hysAe] at h
  calc (D.extend J') ((g ∘ f) y)
      = hg.equiv ((C.extend J) (f y), 0) := by
        simp only [Function.comp_apply]
        exact hg'
  _ = hg.equiv (J.extendCoordChange B C ((B.extend J) (f y)), 0) := by rw [hteq]
  _ = hg.equiv (J.extendCoordChange B C (hf.equiv (v, 0)), 0) := by rw [hf', hyv]

theorem IsImmersionAtOfComplement.hasFDerivWithinAt_writtenInCharts_comp
    (hf : IsImmersionAtOfComplement F I J n f x)
    (hg : IsImmersionAtOfComplement F' J J' n g (f x))
    {s : Set M} (hsopen : IsOpen s) (hxs : x ∈ s)
    (hsub : s ⊆ hf.domChart.source ∩ f ⁻¹' hg.domChart.source)
    (hn : n ≠ 0) :
    HasFDerivWithinAt
      (fun v : E => (hg.codChart.extend J') ((g ∘ f) (((hf.domChart.restr s).extend I).symm v)))
      ((hg.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E' F')).comp
        ((fderivWithin 𝕜 (J.extendCoordChange hf.codChart hg.domChart)
            (J.extendCoordChange hf.codChart hg.domChart).source
            (hf.equiv (((hf.domChart.restr s).extend I) x, 0))).comp
          (hf.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E F))))
      (((hf.domChart.restr s).extend I).target) (((hf.domChart.restr s).extend I) x) := by
  set A := hf.domChart with hA
  set B := hf.codChart with hB
  set C := hg.domChart with hC
  set T := ((A.restr s).extend I).target with hT
  set v₀ : E := ((A.restr s).extend I) x with hv₀
  have hxsrc : x ∈ A.source ∩ s := ⟨hf.mem_domChart_source, hxs⟩
  have hxAe : x ∈ (A.extend I).source := by
    rw [A.extend_source]
    exact hf.mem_domChart_source
  have hvT : v₀ ∈ T := by
    rw [hv₀, hT]
    exact (A.restr s).extend I |>.map_source (by
      rw [(A.restr s).extend_source, A.restr_source' s hsopen]
      exact hxsrc)
  have hv₁ : (A.extend I) x = v₀ := rfl
  have hfxB : f x ∈ B.source := hf.source_subset_preimage_source hf.mem_domChart_source
  have hfxC : f x ∈ C.source := (hsub hxs).2
  have hmemτ : (B.extend J) (f x) ∈ (J.extendCoordChange B C).source := by
    rw [← OpenPartialHomeomorph.extend_image_source_inter (I := J) (f := B) (f' := C)]
    exact mem_image_of_mem _ ⟨hfxB, hfxC⟩
  have hcoord : (B.extend J) (f x) = hf.equiv (v₀, 0) := by
    have h := hf.writtenInCharts ((A.extend I).map_source hxAe)
    simp only [Function.comp_apply] at h
    rw [(A.extend I).left_inv hxAe] at h
    rw [hv₁] at h
    exact h
  have hu₀ : hf.equiv (v₀, 0) ∈ (J.extendCoordChange B C).source := by
    rwa [hcoord] at hmemτ
  have hBmem : B ∈ IsManifold.maximalAtlas J n N := hf.codChart_mem_maximalAtlas
  have hCmem : C ∈ IsManifold.maximalAtlas J n N := hg.domChart_mem_maximalAtlas
  have hτd : HasFDerivWithinAt (J.extendCoordChange B C)
      (fderivWithin 𝕜 (J.extendCoordChange B C) (J.extendCoordChange B C).source
        (hf.equiv (v₀, 0))) (J.extendCoordChange B C).source (hf.equiv (v₀, 0)) :=
    (((J.contDiffOn_extendCoordChange hBmem hCmem).contDiffWithinAt hu₀).differentiableWithinAt
      hn).hasFDerivWithinAt
  have hinner : HasFDerivWithinAt (fun v : E => hf.equiv (v, 0))
      (hf.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E F)) T v₀ := by
    fun_prop
  have hmaps : MapsTo (fun v : E => hf.equiv (v, 0)) T (J.extendCoordChange B C).source := by
    intro v hv
    have hys : ((A.restr s).extend I).symm v ∈ (A.restr s).source := by
      have h1 : ((A.restr s).extend I).symm v ∈ (((A.restr s).extend I).symm).target :=
        (((A.restr s).extend I).symm).map_source hv
      rw [PartialEquiv.symm_target, OpenPartialHomeomorph.extend_source] at h1
      exact h1
    have hys' : ((A.restr s).extend I).symm v ∈ A.source ∩ s := by
      rwa [A.restr_source' s hsopen] at hys
    have hyAe : ((A.restr s).extend I).symm v ∈ (A.extend I).source := by
      rw [A.extend_source]
      exact hys'.1
    have hvy : (A.extend I) (((A.restr s).extend I).symm v) = v := by
      have h1 : ((A.restr s).extend I) (((A.restr s).extend I).symm v) = v :=
        PartialEquiv.right_inv _ hv
      rwa [OpenPartialHomeomorph.extend_coe] at h1
    have hcoord' : (B.extend J) (f (((A.restr s).extend I).symm v)) = hf.equiv (v, 0) := by
      have h := hf.writtenInCharts ((A.extend I).map_source hyAe)
      simp only [Function.comp_apply] at h
      rw [(A.extend I).left_inv hyAe, hvy] at h
      exact h
    change hf.equiv (v, 0) ∈ (J.extendCoordChange B C).source
    rw [← hcoord', ← OpenPartialHomeomorph.extend_image_source_inter (I := J) (f := B) (f' := C)]
    exact mem_image_of_mem _ ⟨hf.source_subset_preimage_source hys'.1, (hsub hys'.2).2⟩
  have hmid : HasFDerivWithinAt (fun v : E => (J.extendCoordChange B C) (hf.equiv (v, 0)))
      ((fderivWithin 𝕜 (J.extendCoordChange B C) (J.extendCoordChange B C).source
        (hf.equiv (v₀, 0))).comp
        (hf.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E F))) T v₀ :=
    HasFDerivWithinAt.comp (f := fun v : E => hf.equiv (v, 0)) (x := v₀) hτd hinner hmaps
  have houter : HasFDerivWithinAt (fun u : E' => hg.equiv (u, 0))
      (hg.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E' F'))
      Set.univ ((J.extendCoordChange B C) (hf.equiv (v₀, 0))) := by
    fun_prop
  refine (HasFDerivWithinAt.comp (f := fun v : E => (J.extendCoordChange B C) (hf.equiv (v, 0)))
    (x := v₀) houter hmid (fun _ _ => trivial)).congr (fun v hv => ?_) ?_
  · simpa only [Function.comp_apply] using
      (hf.writtenInCharts_comp hg hsopen hsub (v := v) hv)
  · simpa only [Function.comp_apply] using
      (hf.writtenInCharts_comp hg hsopen hsub (v := v₀) hvT)

theorem IsImmersionAtOfComplement.contMDiffOn_domChart
    (hf : IsImmersionAtOfComplement F I J n f x) :
    ContMDiffOn I J n f hf.domChart.source := by
  intro y hy
  set A := hf.domChart with hA
  set B := hf.codChart with hB
  set ef := hf.equiv with hef
  have hmemA : A ∈ IsManifold.maximalAtlas I n M := hf.domChart_mem_maximalAtlas
  have hmemB : B ∈ IsManifold.maximalAtlas J n N := hf.codChart_mem_maximalAtlas
  have hkey : ∀ z ∈ A.source, J (B (f z)) = ef (((A.extend I) z), 0) := by
    intro z hz
    have hz' : (A.extend I) z ∈ (A.extend I).target :=
      (A.extend I).map_source (by rwa [OpenPartialHomeomorph.extend_source])
    have h := hf.writtenInCharts hz'
    simp only [Function.comp_apply] at h
    rw [(A.extend I).left_inv (by rwa [OpenPartialHomeomorph.extend_source])] at h
    simpa only [OpenPartialHomeomorph.extend_coe, Function.comp_apply] using h
  have h1 : ContMDiffWithinAt I 𝓘(𝕜, E) n (A.extend I) A.source y :=
    (A.contMDiffOn_extend hmemA) y hy
  have h2 : ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') n (fun v : E => ef (v, 0))
      ((A.extend I) '' A.source) ((A.extend I) y) := by
    rw [contMDiffWithinAt_iff_contDiffWithinAt]
    exact (ef.toContinuousLinearMap.comp (ContinuousLinearMap.inl 𝕜 E F)).contDiff.contDiffWithinAt
  have h3 : ContMDiffWithinAt 𝓘(𝕜, E') J n J.symm (range J) (ef (((A.extend I) y), 0)) :=
    (J.contMDiffOn_symm (n := n)) _ ⟨B (f y), hkey y hy⟩
  have h4 : ContMDiffWithinAt 𝓘(𝕜, E) J n (fun v : E => J.symm (ef (v, 0)))
      ((A.extend I) '' A.source) ((A.extend I) y) :=
    h3.comp ((A.extend I) y) h2 (by
      intro v hv
      obtain ⟨z, hz, rfl⟩ := hv
      exact ⟨B (f z), hkey z hz⟩)
  have hJy : J.symm (ef (((A.extend I) y), 0)) = B (f y) := by
    rw [← hkey y hy]
    exact J.left_inv _
  have h5 : ContMDiffWithinAt J J n B.symm B.target (J.symm (ef (((A.extend I) y), 0))) := by
    rw [hJy]
    exact (contMDiffOn_symm_of_mem_maximalAtlas hmemB) _
      (B.map_source (hf.source_subset_preimage_source hy))
  have h45 : ContMDiffWithinAt 𝓘(𝕜, E) J n (fun v : E => B.symm (J.symm (ef (v, 0))))
      ((A.extend I) '' A.source) ((A.extend I) y) :=
    h5.comp ((A.extend I) y) h4 (by
      intro v hv
      obtain ⟨z, hz, rfl⟩ := hv
      simp only []
      rw [← hkey z hz, J.left_inv]
      exact B.map_source (hf.source_subset_preimage_source hz))
  have h6 : ContMDiffWithinAt I J n (fun z => B.symm (J.symm (ef ((A.extend I) z, 0))))
      A.source y :=
    h45.comp y h1 (by
      intro z hz
      exact ⟨z, hz, rfl⟩)
  refine h6.congr (fun z hz => ?_) ?_
  · rw [← hkey z hz, J.left_inv]
    exact (B.left_inv (hf.source_subset_preimage_source hz)).symm
  · rw [← hkey y hy, J.left_inv]
    exact (B.left_inv (hf.source_subset_preimage_source hy)).symm

theorem StructureGroupoid.trans_mem_maximalAtlas {H : Type*} [TopologicalSpace H]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (G : StructureGroupoid H)
    {e : OpenPartialHomeomorph M H} (he : e ∈ G.maximalAtlas M)
    {φ : OpenPartialHomeomorph H H} (hφ : φ ∈ G) : e.trans φ ∈ G.maximalAtlas M := by
  intro e' he'
  obtain ⟨h1, h2⟩ := (mem_maximalAtlas_iff.mp he) e' he'
  constructor
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact G.trans (G.symm hφ) h1
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact G.trans h2 hφ

theorem completeSpace_of_continuousLinearEquiv_prod {𝕜 : Type*} [RCLike 𝕜] {E F E' : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
    (e : (E × F) ≃L[𝕜] E') : CompleteSpace F := by
  have hEF : CompleteSpace (E × F) := by
    rw [completeSpace_iff_isComplete_univ,
      ← (ContinuousLinearEquiv.isUniformEmbedding e).isComplete_iff (s := Set.univ),
      Set.image_univ, Set.range_eq_univ.mpr e.surjective,
      ← completeSpace_iff_isComplete_univ]
    exact ‹CompleteSpace E'›
  have hclosed : IsClosed (Set.range (fun f : F => (((0 : E), f) : E × F))) := by
    have hset : Set.range (fun f : F => (((0 : E), f) : E × F)) = Prod.fst ⁻¹' ({0} : Set E) := by
      ext p
      constructor
      · rintro ⟨f, rfl⟩
        simp
      · intro hp
        exact ⟨p.2, Prod.ext hp.symm rfl⟩
    rw [hset]
    exact isClosed_singleton.preimage continuous_fst
  have hiso : Isometry (fun f : F => (((0 : E), f) : E × F)) := by
    rw [isometry_iff_dist_eq]
    intro x y
    simp [dist_eq_norm]
  have hcomp : IsComplete (Set.range (fun f : F => (((0 : E), f) : E × F))) := hclosed.isComplete
  have hfin : IsComplete (Set.univ : Set F) :=
    (hiso.isUniformEmbedding.isComplete_iff (s := Set.univ)).mp (by
      simpa only [Set.image_univ] using hcomp)
  rwa [completeSpace_iff_isComplete_univ]

section Comp

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' E'' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [CompleteSpace F']
  {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G} {J' : ModelWithCorners 𝕜 E'' G'}
  [I.Boundaryless] [J'.Boundaryless]
  {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}
  {f : M → N} {g : N → N'} {x : M}

theorem IsImmersionAtOfComplement.comp
    (hf : IsImmersionAtOfComplement F I J n f x)
    (hg : IsImmersionAtOfComplement F' J J' n g (f x))
    (hn : n ≠ 0) :
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
  have hTopen : IsOpen T := by
    rw [hT]; exact OpenPartialHomeomorph.isOpen_extend_target A'
  set v₀ : E := (A'.extend I) x with hv₀
  have hv₀T : v₀ ∈ T := by
    rw [hv₀, hT]
    refine (A'.extend I).map_source ?_
    rw [OpenPartialHomeomorph.extend_source, hA'src]
    exact hxs₀
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
  have hAx : (A.extend I) x = v₀ := by
    rw [hv₀, hA']
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.restr_apply,
      Function.comp_apply]
  set τ : PartialEquiv E' E' := J.extendCoordChange B C with hτ
  have hcoord : (B.extend J) (f x) = ef (v₀, 0) := by
    have hxT : (A.extend I) x ∈ (A.extend I).target :=
      (A.extend I).map_source (by rw [OpenPartialHomeomorph.extend_source]; exact
        hf.mem_domChart_source)
    have h := hf.writtenInCharts hxT
    simp only [Function.comp_apply] at h
    rw [(A.extend I).left_inv (by rw [OpenPartialHomeomorph.extend_source]; exact
      hf.mem_domChart_source)] at h
    rw [hAx] at h
    rw [hef]
    exact h
  have hp₀mem : ef (v₀, 0) ∈ τ.source := by
    rw [← hcoord, hτ, hB, hC,
      ← OpenPartialHomeomorph.extend_image_source_inter (I := J) (f := hf.codChart) (f' :=
        hg.domChart)]
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
    exact hL2.hasFDerivAt (hTopen.mem_nhds hv₀T)
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
      (hΦderiv.comp (v₀, 0) (ContinuousLinearMap.fst 𝕜 E (F ×
        F')).hasFDerivAt).congr_of_eventuallyEq
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
    DifferentialGeometry.Analysis.exists_localInverse_of_hasFDerivAt_equiv_of_ne_zero hn hΘcont
      (hTopen.prod isOpen_univ) ⟨hv₀T, mem_univ _⟩ hΘderiv
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
  have himg : Y.target = Y '' Y.source := (PartialEquiv.image_source_eq_target
    Y.toPartialEquiv).symm
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
    exact StructureGroupoid.trans_mem_maximalAtlas (contDiffGroupoid n J')
      hg.codChart_mem_maximalAtlas hYmem
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

end Comp

section CompResults

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' E'' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [CompleteSpace F']
  {H G G' : Type*} [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G} {J' : ModelWithCorners 𝕜 E'' G'}
  [I.Boundaryless] [J'.Boundaryless]
  {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω} {f : M → N} {g : N → N'} {x : M}

theorem IsImmersionOfComplement.comp (hf : IsImmersionOfComplement F I J n f)
    (hg : IsImmersionOfComplement F' J J' n g) (hn : n ≠ 0) :
    IsImmersionOfComplement (F × F') I J' n (g ∘ f) :=
  fun x => IsImmersionAtOfComplement.comp (hf x) (hg (f x)) hn

end CompResults

section CompSameUniverse

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
  [I.Boundaryless] [J'.Boundaryless]
  {M N N' : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω} {f : M → N} {g : N → N'}

theorem IsImmersion.comp (hf : IsImmersion I J n f) (hg : IsImmersion J J' n g)
    (hn : n ≠ 0) : IsImmersion I J' n (g ∘ f) := by
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
      IsImmersionOfComplement.comp hf hg hn⟩

theorem IsSmoothEmbedding.comp (hg : IsSmoothEmbedding J J' n g) (hf : IsSmoothEmbedding I J n f)
    (hn : n ≠ 0) : IsSmoothEmbedding I J' n (g ∘ f) :=
  ⟨IsImmersion.comp hf.isImmersion hg.isImmersion hn, hg.isEmbedding.comp hf.isEmbedding⟩

end CompSameUniverse

end Manifold
