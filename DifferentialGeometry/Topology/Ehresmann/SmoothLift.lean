import DifferentialGeometry.Bundle.RightInverse
import DifferentialGeometry.Topology.Ehresmann.HorizontalLift
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false

noncomputable section

open scoped ContDiff Manifold Topology
open Bundle
open DifferentialGeometry.Geometry.VectorBundle

namespace DifferentialGeometry.Topology.Ehresmann

variable {E E' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I ∞ M] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] in
private theorem smooth_frame_section
    (e : Trivialization E (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [MemTrivializationAtlas e] {U : Set M} (hU : U ⊆ e.baseSet)
    {g : M → E} (hg : ContMDiffOn I 𝓘(ℝ, E) ∞ g U) :
    ContMDiffOn I I.tangent ∞
      (fun x ↦ (⟨x, e.symmL ℝ x (g x)⟩ : TangentBundle I M)) U := by
  rw [e.contMDiffOn_iff (fun x hx ↦ e.mem_source.mpr (hU hx))]
  refine ⟨contMDiffOn_id, hg.congr ?_⟩
  intro x hx
  rw [e.symmL_apply (hU hx), e.apply_mk_symm (hU hx)]

theorem exists_local_smoothDerivativeLift_of_surjective
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (Z : (y : N) → TangentSpace J y)
    (hZ : ContMDiff J J.tangent ∞
      (fun y ↦ (⟨y, Z y⟩ : TangentBundle J N)))
    (x₀ : M) (hsurj : Function.Surjective (mfderiv I J f x₀)) :
    ∃ U ∈ 𝓝 x₀, ∃ X : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent ∞
        (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) U ∧
      (∀ x ∈ U, mfderiv I J f x (X x) = Z (f x)) ∧
      (∀ x ∈ U, Z (f x) = 0 → X x = 0) := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let e' := trivializationAt E' (TangentSpace J : N → Type _) (f x₀)
  let U := e.baseSet ∩ f ⁻¹' e'.baseSet
  have he₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have he'₀ : f x₀ ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt' (f x₀)
  have hU : U ∈ 𝓝 x₀ := Filter.inter_mem
    (e.open_baseSet.mem_nhds he₀)
    (hf.continuous.continuousAt.preimage_mem_nhds (e'.open_baseSet.mem_nhds he'₀))
  let A : M → E →L[ℝ] E' := fun x ↦
    (e'.continuousLinearMapAt ℝ (f x)).comp
      ((mfderiv I J f x).comp (e.symmL ℝ x))
  have hA : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E') ∞ A U := by
    apply contMDiffOn_clm_apply_iff.mpr
    intro v
    have hs := smooth_frame_section e (U := U) Set.inter_subset_left
      (contMDiffOn_const (c := v))
    have hd := (hf.contMDiff_tangentMap (m := ∞) (by simp)).comp_contMDiffOn hs
    have hc := (e'.contMDiffOn (IB := J) (n := ∞)).comp hd
      (fun x hx ↦ e'.mem_source.mpr hx.2)
    exact (contMDiff_snd.comp_contMDiffOn hc).congr (fun x hx ↦
      e'.continuousLinearMapAt_apply_of_mem ℝ hx.2 _)
  have hAsurj : Function.Surjective (A x₀) := by
    let p := e.continuousLinearEquivAt ℝ x₀ he₀
    let q := e'.continuousLinearEquivAt ℝ (f x₀) he'₀
    have h := q.surjective.comp (hsurj.comp p.symm.surjective)
    simpa only [A, p, q, Function.comp_def, ContinuousLinearMap.coe_comp,
      Trivialization.coe_continuousLinearEquivAt_eq,
      Trivialization.symm_continuousLinearEquivAt_eq] using h
  obtain ⟨V, hV, hVU, R, hR, hright⟩ := exists_contMDiffOn_rightInverse hA hU
    (ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hAsurj)
  let z : M → E' := fun x ↦ e'.continuousLinearMapAt ℝ (f x) (Z (f x))
  have hz : ContMDiffOn I 𝓘(ℝ, E') ∞ z V := by
    have hc := (e'.contMDiffOn (IB := J) (n := ∞)).comp
      (hZ.comp hf).contMDiffOn (fun x hx ↦ e'.mem_source.mpr (hVU hx).2)
    exact (contMDiff_snd.comp_contMDiffOn hc).congr (fun x hx ↦
      e'.continuousLinearMapAt_apply_of_mem ℝ (hVU hx).2 _)
  refine ⟨V, hV, (fun x ↦ e.symmL ℝ x (R x (z x))),
    smooth_frame_section e (fun x hx ↦ (hVU hx).1) (hR.clm_apply hz), ?_, ?_⟩
  · intro x hx
    have he'x := (hVU hx).2
    apply (e'.continuousLinearEquivAt ℝ (f x) he'x).injective
    simpa only [A, z, ContinuousLinearMap.comp_apply,
      Trivialization.coe_continuousLinearEquivAt_eq] using hright x hx (z x)
  · intro x hx hzero
    simp [z, hzero]

theorem exists_smoothDerivativeLift_of_surjective
    [T2Space M] [SigmaCompactSpace M]
    (f : M → N) (hf : ContMDiff I J ∞ f)
    (hsurj : ∀ x, Function.Surjective (mfderiv I J f x))
    (Z : (y : N) → TangentSpace J y)
    (hZ : ContMDiff J J.tangent ∞
      (fun y ↦ (⟨y, Z y⟩ : TangentBundle J N))) :
    ∃ X : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ x, mfderiv I J f x (X x) = Z (f x)) ∧
      tsupport X ⊆ f ⁻¹' tsupport Z :=
  exists_smoothDerivativeLift_of_local f hf.continuous Z
    (fun x ↦ exists_local_smoothDerivativeLift_of_surjective f hf Z hZ x (hsurj x))

end DifferentialGeometry.Topology.Ehresmann
