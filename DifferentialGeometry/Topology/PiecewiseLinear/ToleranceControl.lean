/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Tolerance selection, carrier control and relative closedness

An approximation statement in the piecewise linear chain is controlled by a positive error
function, and the geometric construction that realises it is controlled by a locally finite
family of margins that is only produced *after* the error function is fixed.  This file
collects the purely topological tools that such a control argument needs.

* `exists_continuous_pos_lt_forall_lt_of_locallyFinite` selects one continuous positive
  tolerance below a prescribed continuous positive bound and below every margin of a locally
  finite family.  The quantifier order is `∀ family, ∀ margins, ∃ tolerance`.
* `exists_continuous_pos_lt_of_forall_eventually_le` produces a continuous positive minorant of
  a strongly positive function, that is of a function bounded below by a positive constant near
  every point.  This is what turns the book's strongly positive error into the continuous error
  used by the approximation statements of this development.
* `dist_lt_of_image_subset_of_diam_lt` is the carrier estimate: once the two maps send each
  piece of a cover into a common small carrier, the pointwise distance bound is automatic.
* `isLocallyClosed_of_forall_exists_isCompact_mem_nhdsWithin` together with
  `IsLocallyClosed.exists_isOpen_isClosed_preimage_val` turns local compactness of a subset of a
  Hausdorff space into an ambient open set in which the subset is relatively closed.

The sets of the locally finite family are **not** assumed closed: local finiteness alone bounds
the constraint below by a positive constant near every point, which is all the partition of
unity argument consumes.  Local finiteness itself cannot be dropped: for `A n = {1 / (n + 1)}`
in `ℝ` with margins `a n = 1 / (n + 1)` the constraint forces `ψ 0 ≤ 0`.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

/-- A finite family of positive reals admits a positive strict lower bound. -/
private theorem exists_pos_forall_mem_lt {ι : Type*} {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (s : Finset ι) : ∃ c : ℝ, 0 < c ∧ ∀ i ∈ s, c < a i := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨1, one_pos, by simp⟩
  | @insert j s _ ih =>
      obtain ⟨c, hc, hcs⟩ := ih
      have hmin : 0 < min c (a j) := lt_min hc (ha j)
      refine ⟨min c (a j) / 2, by linarith, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with hij | hi
      · subst hij
        exact (half_lt_self hmin).trans_le (min_le_right _ _)
      · exact (half_lt_self hmin).trans ((min_le_left _ _).trans_lt (hcs i hi))

/-- **Tolerance selection.**  Let `A` be a locally finite family of subsets of a normal
paracompact space, let `a i > 0` be a margin attached to `A i`, and let `φ` be continuous and
positive.  Then there is a continuous positive `ψ` with `ψ x < φ x` everywhere and `ψ x < a i`
at every point of `A i`.

The margins are quantified before the tolerance, so this is the form needed when the family
`A` is produced by an earlier step of a geometric construction.  The book's bound `φ / 4` is
the instance with `φ` replaced by `fun x => φ x / 4`.  The sets `A i` need not be closed. -/
theorem exists_continuous_pos_lt_forall_lt_of_locallyFinite {ι X : Type*} [TopologicalSpace X]
    [NormalSpace X] [ParacompactSpace X] {A : ι → Set X} (hA : LocallyFinite A) {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) {φ : X → ℝ} (hφ : Continuous φ) (hφpos : ∀ x, 0 < φ x) :
    ∃ ψ : X → ℝ, Continuous ψ ∧ (∀ x, 0 < ψ x) ∧ (∀ x, ψ x < φ x) ∧
      ∀ i, ∀ x ∈ A i, ψ x < a i := by
  classical
  have hconv : ∀ x : X,
      Convex ℝ (Ioo (0 : ℝ) (φ x) ∩ ⋂ i ∈ {i | x ∈ A i}, Iio (a i)) := fun x =>
    (convex_Ioo 0 (φ x)).inter (convex_iInter₂ fun i _ => convex_Iio (a i))
  have hlocal : ∀ x : X, ∃ c : ℝ,
      ∀ᶠ y in 𝓝 x, c ∈ Ioo (0 : ℝ) (φ y) ∩ ⋂ i ∈ {i | y ∈ A i}, Iio (a i) := by
    intro x
    obtain ⟨V, hV, hVfin⟩ := hA x
    obtain ⟨c, hc, hcs⟩ := exists_pos_forall_mem_lt ha hVfin.toFinset
    have hpos : 0 < min (φ x / 2) c := lt_min (by linarith [hφpos x]) hc
    have hW : {y | φ x / 2 < φ y} ∈ 𝓝 x :=
      (isOpen_lt continuous_const hφ).mem_nhds (half_lt_self (hφpos x))
    refine ⟨min (φ x / 2) c, ?_⟩
    filter_upwards [hV, hW] with y hyV hyW
    refine ⟨⟨hpos, (min_le_left _ _).trans_lt hyW⟩, mem_iInter₂.mpr fun i hi => ?_⟩
    exact (min_le_right _ _).trans_lt (hcs i (hVfin.mem_toFinset.mpr ⟨y, hi, hyV⟩))
  obtain ⟨g, hg⟩ := exists_continuous_forall_mem_convex_of_local_const hconv hlocal
  exact ⟨g, g.continuous, fun x => (hg x).1.1, fun x => (hg x).1.2,
    fun i x hx => mem_iInter₂.mp (hg x).2 i hx⟩

/-- A strongly positive function on a normal paracompact space has a continuous positive
minorant.  Strong positivity is the hypothesis that near every point the function is bounded
below by a positive constant; positivity of `ρ` itself is a consequence, not an extra
assumption. -/
theorem exists_continuous_pos_lt_of_forall_eventually_le {X : Type*} [TopologicalSpace X]
    [NormalSpace X] [ParacompactSpace X] {ρ : X → ℝ}
    (hρ : ∀ x : X, ∃ c : ℝ, 0 < c ∧ ∀ᶠ y in 𝓝 x, c ≤ ρ y) :
    ∃ ψ : X → ℝ, Continuous ψ ∧ (∀ x, 0 < ψ x) ∧ ∀ x, ψ x < ρ x := by
  have hconv : ∀ x : X, Convex ℝ (Ioo (0 : ℝ) (ρ x)) := fun x => convex_Ioo 0 (ρ x)
  have hlocal : ∀ x : X, ∃ c : ℝ, ∀ᶠ y in 𝓝 x, c ∈ Ioo (0 : ℝ) (ρ y) := by
    intro x
    obtain ⟨c, hc, hcy⟩ := hρ x
    refine ⟨c / 2, ?_⟩
    filter_upwards [hcy] with y hy
    exact ⟨by linarith, (half_lt_self hc).trans_le hy⟩
  obtain ⟨g, hg⟩ := exists_continuous_forall_mem_convex_of_local_const hconv hlocal
  exact ⟨g, g.continuous, fun x => (hg x).1, fun x => (hg x).2⟩

/-- **Carrier control.**  If the pieces `P i` cover `K`, if both `F` and `h` send `P i` into a
bounded carrier `W i`, and if the diameter of `W i` undercuts the tolerance at every point of
`P i`, then `F` approximates `h` on `K` within that tolerance.

Boundedness of `W i` cannot be dropped: `Metric.diam` of an unbounded set is `0`, so the
diameter hypothesis would be vacuous while the conclusion fails. -/
theorem dist_lt_of_image_subset_of_diam_lt {ι X Y : Type*} [PseudoMetricSpace Y] {K : Set X}
    {P : ι → Set X} {W : ι → Set Y} {F h : X → Y} {φ : X → ℝ} (hcover : K ⊆ ⋃ i, P i)
    (hW : ∀ i, Bornology.IsBounded (W i)) (hh : ∀ i, h '' P i ⊆ W i)
    (hF : ∀ i, F '' P i ⊆ W i) (hdiam : ∀ i, ∀ x ∈ P i, Metric.diam (W i) < φ x) :
    ∀ x ∈ K, dist (F x) (h x) < φ x := by
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover hx)
  exact (Metric.dist_le_diam_of_mem (hW i) (hF i ⟨x, hi, rfl⟩)
    (hh i ⟨x, hi, rfl⟩)).trans_lt (hdiam i x hi)

/-- A subset of a Hausdorff space each of whose points has a compact relative neighbourhood
inside the subset is locally closed.  This is the form produced by a locally finite tower of
compact pieces, whose successive pieces are relative neighbourhoods of one another. -/
theorem isLocallyClosed_of_forall_exists_isCompact_mem_nhdsWithin {X : Type*}
    [TopologicalSpace X] [T2Space X] {K : Set X}
    (hK : ∀ x ∈ K, ∃ N ⊆ K, IsCompact N ∧ N ∈ 𝓝[K] x) : IsLocallyClosed K := by
  refine ((isLocallyClosed_tfae K).out 3 0).mp fun x hx => ?_
  obtain ⟨N, hNK, hNc, hNnhds⟩ := hK x hx
  obtain ⟨V, hVopen, hxV, hVsub⟩ := mem_nhdsWithin.mp hNnhds
  refine ⟨V, hxV, hVopen, fun y hy => hNK ?_⟩
  have hclosure : closure (V ∩ K) ⊆ N := by
    rw [← hNc.isClosed.closure_eq]
    exact closure_mono hVsub
  exact hclosure (hVopen.inter_closure hy)

/-- A locally closed set is relatively closed in an ambient open set, in the shape consumed by
the approximation statements of this development.  The witness is the coborder. -/
theorem IsLocallyClosed.exists_isOpen_isClosed_preimage_val {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsLocallyClosed K) :
    ∃ U : Set X, IsOpen U ∧ K ⊆ U ∧ IsClosed (((↑) : U → X) ⁻¹' K) :=
  ⟨coborder K, hK.isOpen_coborder, subset_coborder, isClosed_preimage_val_coborder⟩

end DifferentialGeometry.Topology.PiecewiseLinear
