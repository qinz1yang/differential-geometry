import DifferentialGeometry.Analysis.Calculus.CompactCutoff
import Mathlib.Topology.Compactness.SigmaCompact

noncomputable section

open Set Filter Topology Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis

set_option autoImplicit false

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

include I

noncomputable def manifoldCompactExhaustion : CompactExhaustion M :=
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  CompactExhaustion.choice M

noncomputable def compactExhaustionCutoff
    (K : CompactExhaustion M) (n : ℕ) : M → ℝ :=
  Classical.choose (exists_mfd_bump (I := I) (M := M)
    (K.isCompact n)
    isOpen_interior
    (K.subset_interior_succ n))

theorem compactExhaustionCutoff_spec (K : CompactExhaustion M) (n : ℕ) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (compactExhaustionCutoff (I := I) (M := M) K n) ∧
      HasCompactSupport (compactExhaustionCutoff (I := I) (M := M) K n) ∧
      (∀ x ∈ K n, compactExhaustionCutoff (I := I) (M := M) K n x = 1) ∧
      tsupport (compactExhaustionCutoff (I := I) (M := M) K n) ⊆
        interior (K (n + 1)) ∧
      Set.range (compactExhaustionCutoff (I := I) (M := M) K n) ⊆ Set.Icc 0 1 := by
  classical
  let hB := exists_mfd_bump (I := I) (M := M)
    (K.isCompact n)
    isOpen_interior
    (K.subset_interior_succ n)
  let χ := Classical.choose hB
  have hχ := Classical.choose_spec hB
  change ContMDiff I 𝓘(ℝ, ℝ) ∞ χ ∧ HasCompactSupport χ ∧
    (∀ x ∈ K n, χ x = 1) ∧
    tsupport χ ⊆ interior (K (n + 1)) ∧
    Set.range χ ⊆ Set.Icc 0 1
  rcases hχ with ⟨hχsmooth, hχsupport, hχone, hχsubset, hχrange⟩
  refine ⟨hχsmooth, hχsupport, ?_, hχsubset, hχrange⟩
  intro x hx
  have hxmem : {y : M | χ y = (1 : M → ℝ) y} ∈ 𝓝 x :=
    (mem_nhdsSet_iff_forall.mp hχone) x hx
  change x ∈ {y : M | χ y = (1 : M → ℝ) y}
  exact mem_of_mem_nhds hxmem

theorem compactExhaustionCutoff_eventually_one_on_compact
    (K : CompactExhaustion M) (s : Set M) (hs : IsCompact s) :
    ∀ᶠ n in atTop, ∀ x ∈ s,
      compactExhaustionCutoff (I := I) (M := M) K n x = 1 := by
  obtain ⟨n₀, hn₀⟩ :=
    K.exists_superset_of_isCompact hs
  filter_upwards [eventually_ge_atTop n₀] with n hn x hx
  exact (compactExhaustionCutoff_spec (I := I) (M := M) K n).2.2.1 x
    ((K.subset hn) (hn₀ hx))

end DifferentialGeometry.Analysis
