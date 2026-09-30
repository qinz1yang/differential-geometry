import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

open scoped Manifold

namespace LinearMap

variable {K : Type*} [NontriviallyNormedField K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners K E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F A : Type*} [NormedAddCommGroup F] [NormedSpace K F]
  {V : M → Type*} [TopologicalSpace (Bundle.TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module K (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [AddCommGroup A] [Module K A]

theorem tensorialAt_apply {x : M} (L : V x →ₗ[K] A) :
    TensorialAt I F (fun σ : (p : M) → V p => L (σ x)) x := by
  refine ⟨?_, ?_⟩
  · intro f σ _ _
    exact (congrArg L (show (f • σ) x = f x • σ x from rfl)).trans
      (L.map_smul (f x) (σ x))
  · intro σ τ _ _
    simpa only [Pi.add_apply] using L.map_add (σ x) (τ x)

end LinearMap
