import DifferentialGeometry.Analysis.Sobolev.Tensor.NormBasics

/-!
# Chart-locality and chart-reduction lemmas for the tensor `W^{2k, 2}` space

For a closed Riemannian manifold `(M, g)` modelled on a finite-dimensional real
inner product space `E` and fixed ranks `(r, s)`, the companion files
`Analysis/Sobolev/Tensor/Defs.lean` and `Analysis/Sobolev/Tensor/NormBasics.lean`
introduce the tensor Sobolev space `W^{2k, 2}`: a smooth compactly-supported
`(r, s)`-tensor section `T` is in `W^{2k, 2}` (`MemWtwokTwo g k T`) when, for
**every** chart base point `α : M` of the canonical atlas and every pair of
component multi-indices `(Idx, Jdx)`, the scalar chart component
`tensorChartComp g r s T α Idx Jdx` lies in the Euclidean iterated Sobolev space
`W^{2k, 2}` (`MemWkp (2 * k) 2`).

This file delivers the **chart-reduction** lemmas that the chart-local tensor
elliptic-regularity development consumes: it produces chart-local `W^{2k, 2}`
estimates, and needs to assemble a global `MemWtwokTwo` membership and a global
`wtwokTwoNormReal` bound.

## What is automatic vs. what is genuine content

Because `MemWtwokTwo` is **defined** by a `∀ α : M` quantifier over the whole
manifold, and `wtwokTwoNorm` is a `tsum` over the **canonical** atlas
`chartAtlasPOU`, the predicate and the norm are atlas-canonical *by
construction* — there is no classical "atlas-independence equivalence theorem"
to prove for the tensor space (unlike the scalar `wkpNormChartGen`, which is
parametrised by an arbitrary subordinate partition of unity). The genuine,
needed content is:

* **Finite-cover reduction.** On a compact manifold the canonical partition of
  unity has locally finite supports, so only finitely many chart base points
  contribute; for the rest every chart component is the zero function. This is
  surfaced here as the reusable `tensorChartComp` vanishing lemma, the
  finite-`Finset` characterisation of `MemWtwokTwo`, and the finite-`Finset`
  decomposition of `wtwokTwoNorm`.
* **Chart-local ⇒ membership and its converse.** The bridge between chart-local
  `W^{2k, 2}` regularity of the components and global `MemWtwokTwo` membership.
* **Component transition behaviour.** On a chart overlap the two component
  families describe the same section; the precise statement is the
  reconstruction identity restricted to the overlap.
* **Norm comparison.** A two-sided comparison between the global
  `wtwokTwoNormReal` and the finite sum, over the canonical finite cover, of the
  chart-local component `wkpNorm`s.

## Main results

* `tensorChartComp_eq_zero_of_notMem_finset` — off the canonical finite cover
  every chart component is the zero function.
* `wtwokTwoNorm_chartTerm_eq_zero_of_notMem_finset` — hence its per-chart norm
  contribution vanishes.
* `MemWtwokTwo_iff_forall_finset` — the `∀ α : M` membership quantifier reduces
  to a `∀ α ∈ chartAtlasPOU_finset` quantifier over the finite cover.
* `MemWtwokTwo_of_forall_finset_memWkp` — chart-local ⇒ membership: if each
  component on each chart of the finite cover is in `MemWkp (2k) 2`, the section
  is in `W^{2k, 2}`.
* `MemWtwokTwo.memWkp_chartComp` — the converse (definitional unfolding).
* `wtwokTwoNorm_eq_finset_sum` — the chart-aggregating `tsum` is a `Finset` sum
  over the canonical finite cover.
* `tensorChartComp_eqOn_overlap` — the component-transition statement: on a
  chart overlap the component families reconstruct the same chart-pushed tensor.
* `wtwokTwoNormReal_le_finset_sum`, `wtwokTwoNormReal_ge_finset_sum` — the
  two-sided comparison of the global real-valued norm with the finite-cover sum
  of chart-local component `wkpNorm`s.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- Off the canonical finite cover the partition-of-unity weight vanishes
identically; hence every scalar chart component of any tensor section is the
zero function there. This is the reusable chart-reduction lemma: the
`∀ α : M`-indexed data of `MemWtwokTwo` / `wtwokTwoNorm` is supported on the
finite set `chartAtlasPOU_finset I M`. -/
theorem tensorChartComp_eq_zero_of_notMem_finset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx = (fun _ => (0 : ℝ)) := by
  have hρ_zero : ∀ x : M, (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x = 0 :=
    fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
  funext y
  by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
  · rw [tensorChartComp_apply_of_mem (I := I) (M := M) g r s T α Idx Jdx hy]
    unfold tensorChartComponentPou
    rw [hρ_zero]
    ring
  · exact tensorChartComp_apply_of_notMem (I := I) (M := M) g r s T α Idx Jdx hy

/-- Off the canonical finite cover the per-chart contribution to the tensor
Sobolev norm vanishes: it is a finite double sum, over the component
multi-indices, of the Euclidean Sobolev norm of the zero function. -/
theorem wtwokTwoNorm_chartTerm_eq_zero_of_notMem_finset
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M)) :
    (∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  rw [tensorChartComp_eq_zero_of_notMem_finset (I := I) (M := M) g r s T hα Idx Jdx]
  exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

/-- For a chart base point off the canonical finite cover, every chart component
is automatically in `MemWkp (2k) 2` (it is the zero function). -/
theorem memWkp_tensorChartComp_of_notMem_finset
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∉ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) := by
  rw [tensorChartComp_eq_zero_of_notMem_finset (I := I) (M := M) g r s T hα Idx Jdx]
  exact MemWkp_zero_fun (d := Module.finrank ℝ E) (by norm_num)
    (chartTargetEuclid_isOpen (I := I) (M := M) α)

/-- **Finite-cover reduction of membership.** A smooth compactly-supported
`(r, s)`-tensor section is in `W^{2k, 2}` iff, for every chart base point `α`
**in the canonical finite cover** `chartAtlasPOU_finset I M` and every pair of
component multi-indices, the scalar chart component lies in `MemWkp (2k) 2`.

The `∀ α : M` quantifier of `MemWtwokTwo` reduces to a finite quantifier: charts
off the finite cover contribute only the zero function (see
`tensorChartComp_eq_zero_of_notMem_finset`), which is trivially in every
Euclidean iterated Sobolev space. -/
theorem MemWtwokTwo_iff_forall_finset
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    MemWtwokTwo (I := I) (M := M) g k T ↔
      ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
          (Jdx : Fin s → Fin (Module.finrank ℝ E)),
          MemWkp (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) := by
  constructor
  · intro hT α _ Idx Jdx
    exact hT α Idx Jdx
  · intro hT α Idx Jdx
    by_cases hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)
    · exact hT α hα Idx Jdx
    · exact memWkp_tensorChartComp_of_notMem_finset
        (I := I) (M := M) g k T hα Idx Jdx

/-- **Chart-local ⇒ membership.** If, for every chart base point `α` in the
canonical finite cover `chartAtlasPOU_finset I M` and every pair of component
multi-indices, the scalar chart component `tensorChartComp g r s T α Idx Jdx`
lies in the Euclidean iterated Sobolev space `MemWkp (2k) 2` of its chart
target, then `T` is in the tensor Sobolev space `W^{2k, 2}`.

This is the bridge consumed by the chart-local tensor elliptic-regularity
development: it proves chart-local `W^{2k, 2}` regularity for the finitely many
charts of a cover and concludes global `MemWtwokTwo` membership. -/
theorem MemWtwokTwo_of_forall_finset_memWkp
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s)
    (hT : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        MemWkp (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α)) :
    MemWtwokTwo (I := I) (M := M) g k T :=
  (MemWtwokTwo_iff_forall_finset (I := I) (M := M) g k T).mpr hT

/-- **Membership ⇒ chart-local** (the converse of
`MemWtwokTwo_of_forall_finset_memWkp`). A `W^{2k, 2}`-tensor section has each
scalar chart component, on each chart of the canonical finite cover, in the
Euclidean iterated Sobolev space `MemWkp (2k) 2`. This is essentially the
definition of `MemWtwokTwo` restricted to the finite cover. -/
theorem MemWtwokTwo.memWkp_chartComp_finset
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T)
    {α : M} (_hα : α ∈ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  hT α Idx Jdx

/-- **Membership ⇒ chart-local** in its strongest form: a `W^{2k, 2}`-tensor
section has *every* scalar chart component, on *every* chart, in the Euclidean
iterated Sobolev space `MemWkp (2k) 2`. This is exactly the definition of
`MemWtwokTwo`; it is recorded as the global converse channel. -/
theorem MemWtwokTwo.memWkp_chartComp
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    MemWkp (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α) :=
  hT α Idx Jdx

/-- **Finite-cover decomposition of the tensor Sobolev norm.** The chart-aggregating
`tsum` of `wtwokTwoNorm g k T` equals the finite sum, over the canonical finite
cover `chartAtlasPOU_finset I M`, of the per-chart contribution (itself a finite
double sum over component multi-indices of scalar Euclidean Sobolev norms).

Charts off the finite cover contribute zero by
`wtwokTwoNorm_chartTerm_eq_zero_of_notMem_finset`. -/
theorem wtwokTwoNorm_eq_finset_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g k T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
              (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
              (chartTargetEuclid (I := I) (M := M) α) := by
  unfold wtwokTwoNorm
  rw [tsum_eq_sum]
  intro α hα
  exact wtwokTwoNorm_chartTerm_eq_zero_of_notMem_finset
    (I := I) (M := M) g k T hα

/-- The per-chart contribution to the tensor Sobolev norm, for a chart base
point `α`: a finite double sum over component multi-indices of scalar Euclidean
iterated Sobolev norms `wkpNorm (2k) 2`. Recorded as a named abbreviation for
the chart-reduction lemmas and the norm comparisons. -/
def wtwokTwoChartTerm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) (α : M) : ℝ≥0∞ :=
  ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
    ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α)

@[simp] lemma wtwokTwoChartTerm_def
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) (α : M) :
    wtwokTwoChartTerm (I := I) (M := M) g k T α =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
            (chartTargetEuclid (I := I) (M := M) α) := rfl

/-- The per-chart contribution is finite for a `W^{2k, 2}`-tensor section: it is
a finite double sum of finite Euclidean iterated Sobolev norms. -/
theorem wtwokTwoChartTerm_lt_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) (α : M) :
    wtwokTwoChartTerm (I := I) (M := M) g k T α < ⊤ := by
  rw [wtwokTwoChartTerm_def]
  refine ENNReal.sum_lt_top.mpr ?_
  intro Idx _
  refine ENNReal.sum_lt_top.mpr ?_
  intro Jdx _
  exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E) (hT α Idx Jdx)

/-- The per-chart contribution is not `⊤` for a `W^{2k, 2}`-tensor section. -/
theorem wtwokTwoChartTerm_ne_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) (α : M) :
    wtwokTwoChartTerm (I := I) (M := M) g k T α ≠ ⊤ :=
  (wtwokTwoChartTerm_lt_top (I := I) (M := M) g hT α).ne

/-- `wtwokTwoNorm` rewritten with the named per-chart abbreviation
`wtwokTwoChartTerm`: a finite sum over the canonical finite cover. -/
theorem wtwokTwoNorm_eq_finset_sum_chartTerm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g k T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        wtwokTwoChartTerm (I := I) (M := M) g k T α := by
  rw [wtwokTwoNorm_eq_finset_sum (I := I) (M := M) g k T]
  rfl

/-- A single chart's contribution is bounded by the whole tensor Sobolev norm,
for every chart base point in the canonical finite cover. -/
theorem wtwokTwoChartTerm_le_wtwokTwoNorm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)) :
    wtwokTwoChartTerm (I := I) (M := M) g k T α ≤
      wtwokTwoNorm (I := I) (M := M) g k T := by
  rw [wtwokTwoNorm_eq_finset_sum_chartTerm (I := I) (M := M) g k T]
  exact Finset.single_le_sum
    (f := fun α => wtwokTwoChartTerm (I := I) (M := M) g k T α)
    (fun α _ => zero_le _) hα

/-- A single scalar chart-component `wkpNorm` is bounded by the whole tensor
Sobolev norm, for every chart base point in the canonical finite cover. The
basic chart-local lower bound consumed when assembling component estimates. -/
theorem wkpNorm_tensorChartComp_le_wtwokTwoNorm
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) {α : M}
    (hα : α ∈ chartAtlasPOU_finset (I := I) (M := M))
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) ≤
      wtwokTwoNorm (I := I) (M := M) g k T := by
  refine le_trans ?_ (wtwokTwoChartTerm_le_wtwokTwoNorm (I := I) (M := M) g k T hα)
  rw [wtwokTwoChartTerm_def]
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun Idx => ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
      wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α))
    (fun Idx _ => zero_le _) (Finset.mem_univ Idx))
  exact Finset.single_le_sum
    (f := fun Jdx => wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
      (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (chartTargetEuclid (I := I) (M := M) α))
    (fun Jdx _ => zero_le _) (Finset.mem_univ Jdx)

/-- **Component transition on an overlap.** On the chart target of `α`, the
chart-pushed POU-weighted tensor `tensorChartPushed g r s T α` is the finite sum
of the scalar chart components of `α` against the chart-frame basis. Hence the
component family `{tensorChartComp g r s T α Idx Jdx}_{Idx, Jdx}` determines the
section over the chart of `α`; on an overlap `α`, `β` the two families
reconstruct sections that are pushed-forward images of the same underlying
section `T`, so they carry equivalent information. The reconstruction identity
is the precise transition statement consumed downstream. -/
theorem tensorChartComp_reconstruct
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    tensorChartPushed (I := I) (M := M) g r s T α y =
      ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
          tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y •
            tensorChartBasisElement (E := E) r s Idx Jdx :=
  tensorChartPushed_eq_sum_tensorChartComp (I := I) (M := M) g r s T α y

/-- **Component transition: a vanishing component family forces a vanishing
chart-pushed tensor.** If, on the chart target of `α`, every scalar chart
component of `T` vanishes, then the chart-pushed POU-weighted tensor of `T`
vanishes on that chart target. The qualitative form of the transition law used
by the elliptic-regularity development: chart-local vanishing of the components
propagates to the section. -/
theorem tensorChartPushed_eqOn_zero_of_tensorChartComp_eqOn_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M)
    (h : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      Set.EqOn (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (fun _ => (0 : ℝ)) (chartTargetEuclid (I := I) (M := M) α)) :
    Set.EqOn (tensorChartPushed (I := I) (M := M) g r s T α)
      (fun _ => (0 : TensorRSModel r s ℝ E))
      (chartTargetEuclid (I := I) (M := M) α) := by
  intro y hy
  rw [tensorChartComp_reconstruct (I := I) (M := M) g r s T α y]
  refine Finset.sum_eq_zero ?_
  intro Idx _
  refine Finset.sum_eq_zero ?_
  intro Jdx _
  rw [h Idx Jdx hy, zero_smul]

/-- The real-valued tensor Sobolev norm equals the real value of the finite sum,
over the canonical finite cover, of the per-chart contributions. The exact
`ℝ≥0∞`-level identity `wtwokTwoNorm_eq_finset_sum_chartTerm`, transported through
`ENNReal.toReal`. -/
theorem wtwokTwoNormReal_eq_finset_sum_toReal
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNormReal (I := I) (M := M) g k T =
      (∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal := by
  unfold wtwokTwoNormReal
  rw [wtwokTwoNorm_eq_finset_sum_chartTerm (I := I) (M := M) g k T]

/-- **Norm comparison (upper bound).** The real-valued tensor Sobolev norm is
bounded above by the finite sum, over the canonical finite cover, of the
real values of the per-chart contributions.

For a `W^{2k, 2}`-tensor section the per-chart contributions are finite, so this
is in fact the equality `wtwokTwoNormReal = ∑ (chartTerm α).toReal`; the
inequality form is the convenient shape for assembling a global bound from
chart-local estimates. -/
theorem wtwokTwoNormReal_le_finset_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) :
    wtwokTwoNormReal (I := I) (M := M) g k T ≤
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal := by
  rw [wtwokTwoNormReal_eq_finset_sum_toReal (I := I) (M := M) g k T]
  rw [ENNReal.toReal_sum]
  intro α _
  exact wtwokTwoChartTerm_ne_top (I := I) (M := M) g hT α

/-- **Norm comparison (lower bound).** The real-valued tensor Sobolev norm is
bounded below by the finite sum, over the canonical finite cover, of the real
values of the per-chart contributions.

Together with `wtwokTwoNormReal_le_finset_sum` this gives the two-sided
comparison; in fact both are the equality `wtwokTwoNormReal = ∑ (chartTerm α).toReal`.
-/
theorem wtwokTwoNormReal_ge_finset_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) :
    ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal ≤
      wtwokTwoNormReal (I := I) (M := M) g k T := by
  rw [wtwokTwoNormReal_eq_finset_sum_toReal (I := I) (M := M) g k T]
  rw [ENNReal.toReal_sum]
  intro α _
  exact wtwokTwoChartTerm_ne_top (I := I) (M := M) g hT α

/-- **Two-sided norm comparison.** The real-valued tensor Sobolev norm equals
the finite sum, over the canonical finite cover, of the real values of the
per-chart contributions. This packages `wtwokTwoNormReal_le_finset_sum` and
`wtwokTwoNormReal_ge_finset_sum`: it is the precise channel by which the
chart-local elliptic-regularity development assembles a global
`wtwokTwoNormReal` value (or bound) from its chart-local component estimates. -/
theorem wtwokTwoNormReal_eq_finset_sum
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) :
    wtwokTwoNormReal (I := I) (M := M) g k T =
      ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M),
        (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal :=
  le_antisymm
    (wtwokTwoNormReal_le_finset_sum (I := I) (M := M) g hT)
    (wtwokTwoNormReal_ge_finset_sum (I := I) (M := M) g hT)

/-- A single chart's contribution, in real-valued form, is bounded by the whole
real-valued tensor Sobolev norm. The real-valued companion of
`wtwokTwoChartTerm_le_wtwokTwoNorm`, consumed when converting a chart-local
estimate into a global one. -/
theorem wtwokTwoChartTerm_toReal_le_wtwokTwoNormReal
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) {α : M}
    (hα : α ∈ chartAtlasPOU_finset (I := I) (M := M)) :
    (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal ≤
      wtwokTwoNormReal (I := I) (M := M) g k T := by
  unfold wtwokTwoNormReal
  refine ENNReal.toReal_le_toReal
    (wtwokTwoChartTerm_ne_top (I := I) (M := M) g hT α)
    (wtwokTwoNorm_ne_top (I := I) (M := M) g hT) |>.mpr ?_
  exact wtwokTwoChartTerm_le_wtwokTwoNorm (I := I) (M := M) g k T hα

/-- The real-valued tensor Sobolev norm is bounded above by the cardinality of
the canonical finite cover times the maximal per-chart contribution: if every
per-chart contribution is bounded (in real-valued form) by a constant `C`, then
the global norm is bounded by `card · C`.

This is the form of the norm comparison consumed when the chart-local elliptic
regularity yields a *uniform* chart-local estimate `chartTerm α ≤ C` over the
finite cover and needs a single global bound. -/
theorem wtwokTwoNormReal_le_card_mul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T)
    {C : ℝ}
    (hbound : ∀ α ∈ chartAtlasPOU_finset (I := I) (M := M),
      (wtwokTwoChartTerm (I := I) (M := M) g k T α).toReal ≤ C) :
    wtwokTwoNormReal (I := I) (M := M) g k T ≤
      (chartAtlasPOU_finset (I := I) (M := M)).card * C := by
  rw [wtwokTwoNormReal_eq_finset_sum (I := I) (M := M) g hT]
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_const, nsmul_eq_mul]

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
