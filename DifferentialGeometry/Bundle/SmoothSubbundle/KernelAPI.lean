import DifferentialGeometry.Bundle.SmoothSubbundle.Kernel

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold

universe u uE uH uM uF uG uV₁ uV₂

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {n : WithTop ℕ∞}
variable {F₁ : Type uF} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
variable {F₂ : Type uG} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
variable {V₁ : M → Type uV₁} [TopologicalSpace (TotalSpace F₁ V₁)]
variable [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)]
variable [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁]
variable {V₂ : M → Type uV₂} [TopologicalSpace (TotalSpace F₂ V₂)]
variable [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)]
variable [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂]

namespace ContMDiffVectorSubbundle

variable [FiniteDimensional 𝕜 F₁] [FiniteDimensional 𝕜 F₂]
variable [VectorBundle 𝕜 F₁ V₁] [ContMDiffVectorBundle n F₁ V₁ I]
variable [VectorBundle 𝕜 F₂ V₂] [ContMDiffVectorBundle n F₂ V₂ I]
variable [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]

theorem exists_smooth_kernel
    (A : ∀ x, V₁ x →L[𝕜] V₂ x)
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)))
    (k : ℕ) (hker : ∀ x, Module.finrank 𝕜 (A x).ker = k) :
    ∃ S : ContMDiffVectorSubbundle (I := I) (F := F₁) (V := V₁) (n := n),
      S.rank = k ∧ ∀ x, S.fiber x = (A x).ker := by
  let S := ContMDiffVectorSubbundle.kernel A hA k hker
  refine ⟨S, ?_, ?_⟩
  · exact ContMDiffVectorSubbundle.kernel_rank A hA k hker
  · intro x
    exact ContMDiffVectorSubbundle.kernel_fiber A hA k hker x

theorem exists_smooth_subbundle_of_locally_eq_kernel
    (S : ∀ x, Submodule 𝕜 (V₁ x)) (k : ℕ)
    (hlocal : ∀ x₀, ∃ (W : Set M) (A : ∀ x, V₁ x →L[𝕜] V₂ x),
      IsOpen W ∧ x₀ ∈ W ∧
      ContMDiffOn I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
        (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)) W ∧
      (∀ x ∈ W, Module.finrank 𝕜 (A x).ker = k) ∧
      ∀ x ∈ W, S x = (A x).ker) :
    ∃ T : ContMDiffVectorSubbundle (I := I) (F := F₁) (V := V₁) (n := n),
      T.rank = k ∧ ∀ x, T.fiber x = S x := by
  let T : ContMDiffVectorSubbundle (I := I) (F := F₁) (V := V₁) (n := n) :=
    { fiber := S
      rank := k
      exists_isSubbundleFrameOn := fun x₀ => by
        obtain ⟨W, A, hW, hx₀W, hA, hker, hS⟩ := hlocal x₀
        obtain ⟨U, s, hU, hx₀U, hUW, hs⟩ :=
          exists_kernel_frameOn A W hW hA k hker x₀ hx₀W
        refine ⟨U, s, hU, hx₀U, hs.linearIndependent, ?_, hs.contMDiffOn⟩
        intro x hx
        rw [hs.spans hx, hS x (hUW hx)] }
  exact ⟨T, rfl, fun _ => rfl⟩

theorem exists_smooth_kernel_frame
    (A : ∀ x, V₁ x →L[𝕜] V₂ x)
    (hA : ContMDiff I (I.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[𝕜] F₂) x (A x)))
    (k : ℕ) (hker : ∀ x, Module.finrank 𝕜 (A x).ker = k) (x : M) :
    ∃ (U : Set M) (s : Fin k → (y : M) → V₁ y),
      IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, LinearIndependent 𝕜 (s · y)) ∧
      (∀ y ∈ U, Submodule.span 𝕜 (Set.range (s · y)) = (A y).ker) ∧
      (∀ i, ContMDiffOn I (I.prod 𝓘(𝕜, F₁)) n
        (fun y => TotalSpace.mk' F₁ y (s i y)) U) := by
  let S := ContMDiffVectorSubbundle.kernel A hA k hker
  have hSrank : S.rank = k := ContMDiffVectorSubbundle.kernel_rank A hA k hker
  have hgoal : ∃ (U : Set M) (s : Fin S.rank → (y : M) → V₁ y),
      IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, LinearIndependent 𝕜 (s · y)) ∧
      (∀ y ∈ U, Submodule.span 𝕜 (Set.range (s · y)) = S.fiber y) ∧
      (∀ i, ContMDiffOn I (I.prod 𝓘(𝕜, F₁)) n
        (fun y => TotalSpace.mk' F₁ y (s i y)) U) := by
    obtain ⟨U, s, hU, hx, hframe⟩ := S.exists_frame x
    refine ⟨U, s, hU, hx, ?_, ?_, ?_⟩
    · intro y hy
      exact hframe.linearIndependent hy
    · intro y hy
      exact hframe.spans hy
    · intro i
      exact hframe.contMDiffOn i
  simpa [S, hSrank, ContMDiffVectorSubbundle.kernel_fiber] using hgoal

end ContMDiffVectorSubbundle
