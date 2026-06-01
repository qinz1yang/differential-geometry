import DifferentialGeometry.Integral.Measure.Glue
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth strict cutoff function on a closed manifold

Given a closed smooth manifold `M` (compact, Hausdorff, σ-compact, boundaryless,
modelled on a finite-dimensional inner product space `E`) and the canonical
chart-atlas partition of unity `chartAtlasPOU I M`, this file constructs, for
each index `α : M`, a smooth real-valued function `chartStrictCutoff α : M → ℝ`
satisfying

* `chartStrictCutoff α` is smooth;
* `tsupport (chartStrictCutoff α) ⊆ (chartAt H α).source`;
* `chartStrictCutoff α x = 1` for every
  `x ∈ tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)`;
* `0 ≤ chartStrictCutoff α x ≤ 1` for every `x : M`.

The construction is the standard smooth Urysohn separation, in the
"vanishing in a neighborhood" form: the complement `(chartAt H α).sourceᶜ` is
closed, and the topological support `tsupport (ρ_α)` is closed; by the
partition-of-unity subordination, the two sets are disjoint. Mathlib's
`exists_contMDiffMap_zero_one_nhds_of_isClosed` produces a smooth function that
vanishes in an *open neighborhood* of the complement, hence its own
topological support is contained in the chart source.
-/

noncomputable section

open Set Topology Bundle Manifold Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M] [I.Boundaryless]

open DifferentialGeometry.Integral.Measure

/-- The complement of the chart source is closed. -/
private lemma isClosed_compl_chartAt_source_aux (α : M) :
    IsClosed ((chartAt H α).sourceᶜ) :=
  (chartAt H α).open_source.isClosed_compl

/-- The chart-atlas partition-of-unity index `α` (as a real-valued function on
`M`) has closed topological support. -/
private lemma isClosed_tsupport_chartAtlasPOU_aux (α : M) :
    IsClosed (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  isClosed_tsupport _

/-- `tsupport (chartAtlasPOU I M α)` is contained in the chart `α` source. -/
private lemma tsupport_chartAtlasPOU_subset_aux (α : M) :
    tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) ⊆
      (chartAt H α).source :=
  (chartAtlasPOU_isSubordinate I M) α

/-- The complement of the chart `α` source and `tsupport (chartAtlasPOU I M α)`
are disjoint. -/
private lemma disjoint_complSource_tsupport_chartAtlasPOU_aux (α : M) :
    Disjoint ((chartAt H α).sourceᶜ)
      (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :=
  Set.disjoint_compl_left_iff_subset.mpr
    (tsupport_chartAtlasPOU_subset_aux (I := I) α)

/-- Bundled `C^∞` smooth strict cutoff at chart-atlas index `α`. It is a smooth
function `M → ℝ` valued in `[0, 1]`, equal to `0` on an *open neighborhood* of
`(chartAt H α).sourceᶜ` and equal to `1` on an open neighborhood of
`tsupport (chartAtlasPOU I M α)`. -/
private def chartStrictCutoffBundled (α : M) : C^∞⟮I, M; ℝ⟯ :=
  ((Classical.choose
    (exists_contMDiffMap_zero_one_nhds_of_isClosed (I := I) (M := M)
      (n := (⊤ : ℕ∞))
      (isClosed_compl_chartAt_source_aux (M := M) α)
      (isClosed_tsupport_chartAtlasPOU_aux (I := I) α)
      (disjoint_complSource_tsupport_chartAtlasPOU_aux (I := I) α))) :
        C^∞⟮I, M; ℝ⟯)

private lemma chartStrictCutoffBundled_spec (α : M) :
    (∀ᶠ x in 𝓝ˢ ((chartAt H α).sourceᶜ),
      ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 0) ∧
    (∀ᶠ x in 𝓝ˢ (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
      ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x = 1) ∧
    ∀ x, ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x ∈
        Set.Icc (0 : ℝ) 1 :=
  Classical.choose_spec
    (exists_contMDiffMap_zero_one_nhds_of_isClosed (I := I) (M := M)
      (n := (⊤ : ℕ∞))
      (isClosed_compl_chartAt_source_aux (M := M) α)
      (isClosed_tsupport_chartAtlasPOU_aux (I := I) α)
      (disjoint_complSource_tsupport_chartAtlasPOU_aux (I := I) α))

/-- The smooth strict cutoff function `M → ℝ` associated to chart-atlas index
`α`. Equals `0` on a neighborhood of the complement of the chart `α` source,
equals `1` on `tsupport (chartAtlasPOU I M α)`, and is `[0, 1]`-valued and
smooth. Its topological support is contained in the chart `α` source. -/
def chartStrictCutoff (α : M) : M → ℝ :=
  ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ)

private lemma chartStrictCutoff_eq_bundled (α : M) :
    chartStrictCutoff (I := I) α =
      ((chartStrictCutoffBundled (I := I) α : C^∞⟮I, M; ℝ⟯) : M → ℝ) :=
  rfl

/-- The smooth strict cutoff function is smooth. -/
theorem chartStrictCutoff_contMDiff (α : M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (chartStrictCutoff (I := I) α) :=
  (chartStrictCutoffBundled (I := I) α).contMDiff

/-- The smooth strict cutoff at `α` is non-negative. -/
theorem chartStrictCutoff_nonneg (α : M) (x : M) :
    0 ≤ chartStrictCutoff (I := I) α x :=
  ((chartStrictCutoffBundled_spec (I := I) α).2.2 x).1

/-- The smooth strict cutoff at `α` is bounded above by `1`. -/
theorem chartStrictCutoff_le_one (α : M) (x : M) :
    chartStrictCutoff (I := I) α x ≤ 1 :=
  ((chartStrictCutoffBundled_spec (I := I) α).2.2 x).2

/-- The smooth strict cutoff vanishes in an open neighborhood of the
complement of the chart `α` source. -/
theorem chartStrictCutoff_eventually_zero_nhdsSet_compl_source (α : M) :
    ∀ᶠ x in 𝓝ˢ ((chartAt H α).sourceᶜ), chartStrictCutoff (I := I) α x = 0 :=
  (chartStrictCutoffBundled_spec (I := I) α).1

/-- The smooth strict cutoff equals `1` in an open neighborhood of
`tsupport (chartAtlasPOU I M α)`. -/
theorem chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU (α : M) :
    ∀ᶠ x in 𝓝ˢ (tsupport ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)),
      chartStrictCutoff (I := I) α x = 1 :=
  (chartStrictCutoffBundled_spec (I := I) α).2.1

/-- The smooth strict cutoff equals `1` on `tsupport (chartAtlasPOU I M α)`. -/
theorem chartStrictCutoff_eq_one_on_tsupport_chartAtlasPOU (α : M) {x : M}
    (hx : x ∈ tsupport
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ)) :
    chartStrictCutoff (I := I) α x = 1 :=
  (chartStrictCutoff_eventually_one_nhdsSet_tsupport_chartAtlasPOU
    (I := I) α).self_of_nhdsSet _ hx

/-- The smooth strict cutoff at `α` vanishes outside the chart `α` source. -/
theorem chartStrictCutoff_eq_zero_of_notMem_chartAt_source (α : M) {x : M}
    (hx : x ∉ (chartAt H α).source) :
    chartStrictCutoff (I := I) α x = 0 := by
  have hmem : x ∈ ((chartAt H α).sourceᶜ) := hx
  exact (chartStrictCutoff_eventually_zero_nhdsSet_compl_source
    (I := I) α).self_of_nhdsSet _ hmem

/-- The topological support of the smooth strict cutoff is contained in the
chart `α` source.

Proof: by `chartStrictCutoff_eventually_zero_nhdsSet_compl_source`, there is an
open neighborhood `U ⊇ (chartAt H α).sourceᶜ` on which the cutoff vanishes;
hence `support (cutoff) ⊆ Uᶜ`, and `Uᶜ` is closed, so
`tsupport (cutoff) = closure (support (cutoff)) ⊆ Uᶜ ⊆ ((chartAt H α).sourceᶜ)ᶜ
= (chartAt H α).source`. -/
theorem chartStrictCutoff_tsupport_subset (α : M) :
    tsupport (chartStrictCutoff (I := I) α) ⊆ (chartAt H α).source := by
  classical
  have hev : ∀ᶠ x in 𝓝ˢ ((chartAt H α).sourceᶜ),
      chartStrictCutoff (I := I) α x = 0 :=
    chartStrictCutoff_eventually_zero_nhdsSet_compl_source (I := I) α
  rw [eventually_nhdsSet_iff_exists] at hev
  obtain ⟨U, hUopen, hUsub, hUzero⟩ := hev
  have hUcomp : IsClosed (Uᶜ) := hUopen.isClosed_compl
  have hsupp_sub : Function.support (chartStrictCutoff (I := I) α) ⊆ Uᶜ := by
    intro x hx
    by_contra hxU
    have hxU' : x ∈ U := by
      simpa using hxU
    exact hx (hUzero x hxU')
  have htsupp_sub : tsupport (chartStrictCutoff (I := I) α) ⊆ Uᶜ :=
    closure_minimal hsupp_sub hUcomp
  have hUcomp_sub : Uᶜ ⊆ (chartAt H α).source := by
    intro x hx
    by_contra hx_not
    have : x ∈ U := hUsub hx_not
    exact hx this
  exact htsupp_sub.trans hUcomp_sub

end Chart
end Sobolev
end Analysis
end DifferentialGeometry
