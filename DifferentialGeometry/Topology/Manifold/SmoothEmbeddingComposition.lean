import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

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

end Manifold
