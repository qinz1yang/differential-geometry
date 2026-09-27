import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology

universe u v w x

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {X : Type x} [TopologicalSpace X]

theorem ContinuousWithinAt.eventually_finrank_range_ge
    [FiniteDimensional 𝕜 E]
    {A : X → E →L[𝕜] F} {s : Set X} {x : X}
    (hA : ContinuousWithinAt A s x) :
    ∀ᶠ y in 𝓝[s] x,
      Module.finrank 𝕜 (A x).range ≤ Module.finrank 𝕜 (A y).range := by
  have hopen := isOpen_setOfPred_nat_le_rank (𝕜 := 𝕜) (E := E) (F := F)
    (Module.finrank 𝕜 (A x).range)
  have hmem : A x ∈ {f : E →L[𝕜] F |
      (Module.finrank 𝕜 (A x).range : Cardinal) ≤ (f : E →ₗ[𝕜] F).rank} := by
    change (Module.finrank 𝕜 (A x).range : Cardinal) ≤ Module.rank 𝕜 (A x).range
    rw [Module.finrank_eq_rank']
  have hev := hA.eventually (hopen.mem_nhds hmem)
  filter_upwards [hev] with y hy
  change (Module.finrank 𝕜 (A x).range : Cardinal) ≤ Module.rank 𝕜 (A y).range at hy
  rw [← Module.finrank_eq_rank'] at hy
  exact_mod_cast hy

theorem ContinuousAt.eventually_finrank_range_ge
    [FiniteDimensional 𝕜 E]
    {A : X → E →L[𝕜] F} {x : X} (hA : ContinuousAt A x) :
    ∀ᶠ y in 𝓝 x,
      Module.finrank 𝕜 (A x).range ≤ Module.finrank 𝕜 (A y).range := by
  simpa only [nhdsWithin_univ] using
    hA.continuousWithinAt.eventually_finrank_range_ge (s := Set.univ)
