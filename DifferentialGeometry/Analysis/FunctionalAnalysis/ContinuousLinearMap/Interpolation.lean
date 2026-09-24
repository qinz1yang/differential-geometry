import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.LinearAlgebra.Basis.Basic

noncomputable section

open Set

theorem LinearIndependent.exists_continuousLinearMap_apply_eq
    {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [Module 𝕜 E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E]
    [AddCommGroup F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [Module 𝕜 F] [ContinuousSMul 𝕜 F] [Finite ι]
    {v : ι → E} (hv : LinearIndependent 𝕜 v) (w : ι → F) :
    ∃ A : E →L[𝕜] F, ∀ i, A (v i) = w i := by
  classical
  let _ : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let _ : Fintype ι := Fintype.ofFinite ι
  let S := Submodule.span 𝕜 (range v)
  let b : Module.Basis ι 𝕜 S := Module.Basis.span hv
  let _ : FiniteDimensional 𝕜 S := Module.Finite.of_basis b
  have hext (i : ι) : ∃ g : E →L[𝕜] 𝕜, ∀ z : S, g z = b.coord i z := by
    obtain ⟨g, hg⟩ := StrongDual.exists_extension S (b.coord i).toContinuousLinearMap
    exact ⟨g, hg⟩
  choose g hg using hext
  refine ⟨∑ i, (g i).smulRight (w i), ?_⟩
  intro j
  have hgj (i : ι) : g i (v j) = if i = j then 1 else 0 := by
    have h := hg i (b j)
    have hcoe : ((b j : S) : E) = v j := Module.Basis.coe_span_apply hv j
    rw [hcoe] at h
    simpa only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, eq_comm] using h
  simp [hgj]
