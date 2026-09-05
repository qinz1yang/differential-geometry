import DifferentialGeometry.Analysis.Calculus.CompactCutoff
import DifferentialGeometry.Bundle.Section

noncomputable section

open Bundle Filter Set
open scoped Manifold Topology ContDiff

namespace ContMDiffSection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
variable {n : ℕ∞}

theorem exists_compactly_supported_eq_nhdsSet
    (S : Cₛ^n⟮I; F, V⟯) {K : Set M} (hK : IsCompact K) :
    ∃ T : Cₛ^n⟮I; F, V⟯,
      IsCompact (closure {x : M | T x ≠ 0}) ∧ ∀ᶠ x in 𝓝ˢ K, T x = S x := by
  classical
  obtain ⟨χ, hχ_smooth, hχ_compact, hχ_one⟩ :=
    DifferentialGeometry.Analysis.exists_bump_nhds (I := I) hK
  let T : Cₛ^n⟮I; F, V⟯ :=
    ⟨fun x => χ x • S x,
      (hχ_smooth.of_le (by exact_mod_cast le_top)).smul_section S.contMDiff⟩
  refine ⟨T, ?_, ?_⟩
  · apply hχ_compact.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx
    change χ x ≠ 0
    intro hzero
    apply hx
    change χ x • S x = 0
    rw [hzero, zero_smul]
  · filter_upwards [hχ_one] with x hx
    change χ x • S x = S x
    rw [hx, Pi.one_apply, one_smul]

end ContMDiffSection
