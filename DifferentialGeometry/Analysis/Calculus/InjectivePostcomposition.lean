import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Later adjustments: no merging, same fibers and kernels (CGP08 kernel)

Blueprint 207B, CGP08 (`thm:fibration-final-bases-no-merging`, B:4259–4316).

* `injOn_iUnion_of_retained_blocks`: the later adjustments retain every earlier-family block, and
  each marked patch `V_i⁰` is cut out by a condition on its own block; if that block is injective on
  `V_i⁰` (CGP07), the later map is injective on the union of the patches ("if two points from
  different earlier patches have the same later image, … CGP07 makes the two points equal").
* `fiber_eq_of_injOn_comp`, `ker_fderiv_comp_eq_of_injective`, `ker_mfderiv_comp_eq_of_injective`:
  on the carrier `D_j` the final map factors as an injective map (with injective differential)
  after `f_j`, so the final and stage-`j` maps have the same fibers and kernels.
-/

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

/-- CGP08, no merging of earlier patches under a later adjustment that retains their blocks. -/
theorem injOn_iUnion_of_retained_blocks {ι α γ β : Type*} (W : Set α) (V : ι → Set α)
    (b : ι → γ → β) (bα : ι → α → β) (T : ι → Set β) (Ψ : α → γ)
    (hpatch : ∀ i w, w ∈ V i ↔ w ∈ W ∧ bα i w ∈ T i)
    (hret : ∀ i, ∀ w ∈ W, b i (Ψ w) = bα i w)
    (hinj : ∀ i, Set.InjOn (bα i) (V i)) : Set.InjOn Ψ (⋃ i, V i) := by
  intro w₁ h₁ w₂ h₂ heq
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h₁
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp h₂
  have hW₁ := ((hpatch i w₁).mp hi).1
  have hW₂ := ((hpatch k w₂).mp hk).1
  have hblock : bα i w₂ = bα i w₁ := by
    rw [← hret i w₂ hW₂, ← heq, hret i w₁ hW₁]
  have hi₂ : w₂ ∈ V i := (hpatch i w₂).mpr ⟨hW₂, hblock ▸ ((hpatch i w₁).mp hi).2⟩
  exact hinj i hi hi₂ hblock.symm

/-- CGP08: an injective postcomposition does not change fibers on the carrier. -/
theorem fiber_eq_of_injOn_comp {α β γ : Type*} {f : α → β} {Ψ : β → γ} {D : Set α}
    (hΨ : Set.InjOn Ψ (f '' D)) {x y : α} (hx : x ∈ D) (hy : y ∈ D) :
    Ψ (f x) = Ψ (f y) ↔ f x = f y :=
  ⟨fun h => hΨ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ h, fun h => by rw [h]⟩

theorem ker_comp_eq_of_injective {R E F G : Type*} [Semiring R] [AddCommMonoid E]
    [AddCommMonoid F] [AddCommMonoid G] [Module R E] [Module R F] [Module R G]
    (A : F →ₗ[R] G) (B : E →ₗ[R] F) (hA : Function.Injective A) :
    LinearMap.ker (A.comp B) = LinearMap.ker B := by
  ext v
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  exact ⟨fun h => hA (h.trans (map_zero A).symm), fun h => by rw [h, map_zero]⟩

/-- CGP08: kernels agree after an injective-differential postcomposition (normed spaces). -/
theorem ker_fderiv_comp_eq_of_injective {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {Ψ : F → G} {x : E} (hf : DifferentiableAt ℝ f x)
    (hΨ : DifferentiableAt ℝ Ψ (f x)) (hinj : Function.Injective (fderiv ℝ Ψ (f x))) :
    LinearMap.ker (fderiv ℝ (Ψ ∘ f) x : E →ₗ[ℝ] G) = LinearMap.ker (fderiv ℝ f x : E →ₗ[ℝ] F) := by
  rw [fderiv_comp x hΨ hf]
  exact ker_comp_eq_of_injective (fderiv ℝ Ψ (f x) : F →ₗ[ℝ] G) _ hinj

open scoped Manifold in
/-- CGP08: kernels agree after an injective-differential postcomposition (manifolds). -/
theorem ker_mfderiv_comp_eq_of_injective {E F G HE HF HG M N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [TopologicalSpace HE] [TopologicalSpace HF]
    [TopologicalSpace HG] {I : ModelWithCorners ℝ E HE} {J : ModelWithCorners ℝ F HF}
    {K : ModelWithCorners ℝ G HG} [TopologicalSpace M] [ChartedSpace HE M]
    [TopologicalSpace N] [ChartedSpace HF N] [TopologicalSpace P] [ChartedSpace HG P]
    {f : M → N} {Ψ : N → P} {x : M} (hf : MDifferentiableAt I J f x)
    (hΨ : MDifferentiableAt J K Ψ (f x)) (hinj : Function.Injective (mfderiv J K Ψ (f x))) :
    LinearMap.ker (mfderiv I K (Ψ ∘ f) x : TangentSpace I x →ₗ[ℝ] TangentSpace K ((Ψ ∘ f) x)) =
      LinearMap.ker (mfderiv I J f x : TangentSpace I x →ₗ[ℝ] TangentSpace J (f x)) := by
  rw [mfderiv_comp x hΨ hf]
  exact ker_comp_eq_of_injective
    (mfderiv J K Ψ (f x) : TangentSpace J (f x) →ₗ[ℝ] TangentSpace K (Ψ (f x))) _ hinj

end DifferentialGeometry.Analysis
