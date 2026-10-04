import DifferentialGeometry.Bundle.RightInverse
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Finite-order local lifts through a submersion point

If `f : M → N` is `C^m` and its derivative at `x₀` is surjective, then near `x₀` every `C^n`
vector field `Z` on `N` (`n + 1 ≤ m`) has a `C^n` local lift `X` with `df (X x) = Z (f x)`.
This is the order-`n` version of the tree's `C^∞` lemma
`Ehresmann.exists_local_smoothDerivativeLift_of_surjective`
(`Topology/Ehresmann/SmoothLift.lean`), with the same proof: a local frame of `TM` and of `TN`,
the derivative in these frames is a `C^n` family of surjective linear maps, and a `C^n` local
right inverse (`exists_contMDiffOn_rightInverse`) solves the lifting equation.

Statement S1 of `build-logs/resume/sheet-W5-FLOW.md` is the case of a vector-space target and a
constant field `Z = z` (`exists_local_derivativeLift_Cn`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff Manifold Topology
open Bundle
open DifferentialGeometry.Geometry.VectorBundle

namespace DifferentialGeometry.Analysis.ODE

variable {E E' : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I ∞ M] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] in
/-- A section of `TM` written in a tangent-bundle trivialization by a `C^n` coordinate function is
`C^n` on any subset of the base of the trivialization. -/
theorem contMDiffOn_trivialization_symmL_section {n : ℕ∞}
    (e : Trivialization E (Bundle.TotalSpace.proj : TangentBundle I M → M))
    [MemTrivializationAtlas e] {U : Set M} (hU : U ⊆ e.baseSet)
    {g : M → E} (hg : ContMDiffOn I 𝓘(ℝ, E) n g U) :
    ContMDiffOn I I.tangent n
      (fun x ↦ (⟨x, e.symmL ℝ x (g x)⟩ : TangentBundle I M)) U := by
  rw [e.contMDiffOn_iff (fun x hx ↦ e.mem_source.mpr (hU hx))]
  refine ⟨contMDiffOn_id, hg.congr ?_⟩
  intro x hx
  rw [e.symmL_apply (hU hx), e.apply_mk_symm (hU hx)]

/-- **Finite-order local derivative lift.** If `f : M → N` is `C^m`, `Z` is a `C^n` vector field
on `N` with `n + 1 ≤ m`, and `mfderiv f x₀` is surjective, then on a neighbourhood of `x₀` there
is a `C^n` vector field `X` with `df (X x) = Z (f x)`, vanishing where `Z ∘ f` vanishes. -/
theorem exists_local_derivativeLift_of_surjective_Cn {n : ℕ∞} {m : WithTop ℕ∞}
    (hmn : (n : WithTop ℕ∞) + 1 ≤ m)
    (f : M → N) (hf : ContMDiff I J m f)
    (Z : (y : N) → TangentSpace J y)
    (hZ : ContMDiff J J.tangent n
      (fun y ↦ (⟨y, Z y⟩ : TangentBundle J N)))
    (x₀ : M) (hsurj : Function.Surjective (mfderiv I J f x₀)) :
    ∃ U ∈ 𝓝 x₀, ∃ X : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent n
        (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) U ∧
      (∀ x ∈ U, mfderiv I J f x (X x) = Z (f x)) ∧
      (∀ x ∈ U, Z (f x) = 0 → X x = 0) := by
  let e := trivializationAt E (TangentSpace I : M → Type _) x₀
  let e' := trivializationAt E' (TangentSpace J : N → Type _) (f x₀)
  let U := e.baseSet ∩ f ⁻¹' e'.baseSet
  have h1m : (1 : WithTop ℕ∞) ≤ m := le_trans le_add_self hmn
  have he₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  have he'₀ : f x₀ ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt' (f x₀)
  have hU : U ∈ 𝓝 x₀ := Filter.inter_mem
    (e.open_baseSet.mem_nhds he₀)
    (hf.continuous.continuousAt.preimage_mem_nhds (e'.open_baseSet.mem_nhds he'₀))
  let A : M → E →L[ℝ] E' := fun x ↦
    (e'.continuousLinearMapAt ℝ (f x)).comp
      ((mfderiv I J f x).comp (e.symmL ℝ x))
  have hA : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E') n A U := by
    apply contMDiffOn_clm_apply_iff.mpr
    intro v
    have hs := contMDiffOn_trivialization_symmL_section e (U := U) Set.inter_subset_left
      (contMDiffOn_const (c := v)) (n := n)
    have hd := (hf.contMDiff_tangentMap (m := n) hmn).comp_contMDiffOn hs
    have hc := (e'.contMDiffOn (IB := J) (n := n)).comp hd
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
  have hz : ContMDiffOn I 𝓘(ℝ, E') n z V := by
    have hc := (e'.contMDiffOn (IB := J) (n := n)).comp
      (hZ.comp (hf.of_le (le_trans le_self_add hmn))).contMDiffOn
      (fun x hx ↦ e'.mem_source.mpr (hVU hx).2)
    exact (contMDiff_snd.comp_contMDiffOn hc).congr (fun x hx ↦
      e'.continuousLinearMapAt_apply_of_mem ℝ (hVU hx).2 _)
  refine ⟨V, hV, (fun x ↦ e.symmL ℝ x (R x (z x))),
    contMDiffOn_trivialization_symmL_section e (fun x hx ↦ (hVU hx).1) (hR.clm_apply hz), ?_, ?_⟩
  · intro x hx
    have he'x := (hVU hx).2
    apply (e'.continuousLinearEquivAt ℝ (f x) he'x).injective
    simpa only [A, z, ContinuousLinearMap.comp_apply,
      Trivialization.coe_continuousLinearEquivAt_eq] using hright x hx (z x)
  · intro x hx hzero
    simp [z, hzero]

/-- **Statement S1 of W5-FLOW: finite-order local lift of a constant vector.** If `f : M → G'` is
`C^m` into a finite-dimensional vector space and `mfderiv f x₀` is surjective, then for every
`z : G'` there is, near `x₀`, a `C^n` vector field `X` (`n + 1 ≤ m`) with `df (X x) = z`. -/
theorem exists_local_derivativeLift_Cn
    {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G'] [FiniteDimensional ℝ G']
    {n : ℕ∞} {m : WithTop ℕ∞} (hmn : (n : WithTop ℕ∞) + 1 ≤ m)
    {f : M → G'} (hf : ContMDiff I 𝓘(ℝ, G') m f) (z : G')
    {x₀ : M} (hsurj : Function.Surjective (mfderiv I 𝓘(ℝ, G') f x₀)) :
    ∃ U ∈ 𝓝 x₀, ∃ X : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent n (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) U ∧
      ∀ x ∈ U, mfderiv I 𝓘(ℝ, G') f x (X x) = z := by
  have hZ : ContMDiff 𝓘(ℝ, G') 𝓘(ℝ, G').tangent n
      (fun y : G' ↦ (⟨y, (z : TangentSpace 𝓘(ℝ, G') y)⟩ : TangentBundle 𝓘(ℝ, G') G')) := by
    intro y₀
    exact (contMDiffAt_vectorSpace_iff_contDiffAt
      (V := fun y : G' => (z : TangentSpace 𝓘(ℝ, G') y))).2 contDiffAt_const
  obtain ⟨U, hU, X, hX, hlift, -⟩ := exists_local_derivativeLift_of_surjective_Cn hmn f hf
    (fun y : G' => (z : TangentSpace 𝓘(ℝ, G') y)) hZ x₀ hsurj
  exact ⟨U, hU, X, hX, hlift⟩

end DifferentialGeometry.Analysis.ODE
