import DifferentialGeometry.Analysis.InnerProductSpace.ProjectedGraphRank
import DifferentialGeometry.Analysis.Calculus.GraphCoverage
import DifferentialGeometry.Analysis.ParameterSelection.AcyclicBounds
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Abstract chapter 14 rows on graphs and parameters: FC06, FC25, FC46 (row-named wrappers)

Blueprint `master207B.tex`: FC06 (`lem:fibration-rank-margin`, 311–350), FC25
(`lem:fibration-truncated-coverage`, 1577–1624), FC46 (`lem:fibration-parameter-selection`,
9979–9997). Each theorem has the row's hypotheses in the row's notation; the proofs are the
existing kernels.

* `fc06_row`: `T z = (z, G z)` in the orthogonal decomposition `F ⊕ K` (any finite-dimensional
  `F`, the row has `F = ℝ²`), `‖T‖ ≤ b`, `‖L‖ ≤ ℓ`, `|L* z| ≥ a|z|`, `‖D − TL‖ ≤ e < a`: the
  projection `P = π_{im T} D` is onto `im T`, `‖D − P‖ ≤ e` and
  `(a − e)|v| ≤ |Pv| ≤ (bℓ + e)|v|` on `(ker P)⊥`.
* `fc25_row`: a set `X ⊆ E ⊕ V` close to the graph `Φ(u) = (u, h(u))` in both directions, with
  `‖D²Φ‖ ≤ B` near `B̄(u₀, R)`, is within Hausdorff distance `3(2e + BR²/2)` of the tangent plane
  `x + im DΦ(u₀)` on the ball `B̄(x, R)`.
* `fc46_row`: finite acyclic parameter selection with upper-bound nodes, lower-bound nodes and
  mixed nodes with a supplied nonempty admissible interval.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace DifferentialGeometry.Analysis

section FC06

variable {V F K : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- FC06 (`lem:fibration-rank-margin`). -/
theorem fc06_row (G : F →L[ℝ] K) (T : F →L[ℝ] WithLp 2 (F × K))
    (hgraph : ∀ z, T z = WithLp.toLp 2 (z, G z)) {b ℓ a e : ℝ} (hT : ‖T‖ ≤ b)
    (L : V →L[ℝ] F) (hL : ‖L‖ ≤ ℓ) (ha : 0 < a) (hLadj : ∀ z, a * ‖z‖ ≤ ‖L.adjoint z‖)
    (D : V →L[ℝ] WithLp 2 (F × K)) (herror : ‖D - T.comp L‖ ≤ e) (he : e < a) :
    let P := T.range.orthogonalProjectionOnto.comp D
    Function.Surjective P ∧ ‖D - T.range.subtypeL.comp P‖ ≤ e ∧
      ∀ v ∈ P.kerᗮ, (a - e) * ‖v‖ ≤ ‖P v‖ ∧ ‖P v‖ ≤ (b * ℓ + e) * ‖v‖ := by
  have hTlower : ∀ z, ‖z‖ ≤ ‖T z‖ := by
    intro z
    have h := WithLp.norm_fst_le (x := T z)
    rw [hgraph z] at h ⊢
    exact h
  exact ContinuousLinearMap.projected_range_surjective_of_approximation T L D ha he hLadj
    hTlower hT hL herror

end FC06

section FC25

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- FC25 (`lem:fibration-truncated-coverage`): graph coverage with identical truncation radii, for
`X ⊆ E ⊕ V` (the row has `E = ℝᵏ`, `V` finite-dimensional Euclidean), `x ∈ X` with first
coordinate `u₀`, and `Φ(u) = (u, h(u))`. -/
theorem fc25_row (h : E → V) (X : Set (WithLp 2 (E × V))) (x : WithLp 2 (E × V)) (hx : x ∈ X)
    {R B e : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (he : 0 ≤ e)
    (hreg : ∀ u ∈ closedBall x.fst R, ContDiffAt ℝ 2 (fun w => WithLp.toLp 2 (w, h w)) u)
    (hsecond : ∀ u ∈ closedBall x.fst R,
      ‖iteratedFDeriv ℝ 2 (fun w => WithLp.toLp 2 (w, h w)) u‖ ≤ B)
    (hforward : ∀ y ∈ X ∩ closedBall x R, dist y (WithLp.toLp 2 (y.fst, h y.fst)) ≤ e)
    (hbackward : ∀ u ∈ closedBall x.fst R,
      ∃ xu ∈ X, xu.fst = u ∧ dist xu (WithLp.toLp 2 (u, h u)) ≤ e) :
    hausdorffDist (X ∩ closedBall x R)
      ((fun v => x + fderiv ℝ (fun w => WithLp.toLp 2 (w, h w)) x.fst v) '' (univ : Set E) ∩
        closedBall x R) ≤ 3 * (2 * e + B * R ^ 2 / 2) := by
  have h' := GC.MetricGeometry.hausdorffDist_graph_tangent_closedBall_le
    (fun w => WithLp.toLp 2 (w, h w)) (WithLp.fstL 2 ℝ E V) (fun z => WithLp.norm_fst_le (x := z))
    (fun u => by simp) X x hx hR hB he (by simpa using hreg) (by simpa using hsecond)
    (by simpa using hforward)
    (fun u hu => by
      obtain ⟨xu, hxu, -, hd⟩ := hbackward u (by simpa using hu)
      exact ⟨xu, hxu, hd⟩)
  simpa using h'

end FC25

section FC46

open ParameterSelection

/-- FC46 (`lem:fibration-parameter-selection`): parameters ordered by an acyclic relation `r`
(`r j i`: `j` is chosen before `i`); at each node, after positive predecessor values `v` are
fixed, the admissible set is either `{x > 0 | x < b, b ∈ U}` for finitely many positive upper
bounds, or `{x > 0 | b < x, b ∈ L}` for finitely many lower bounds, or contains a specified
nonempty interval `(lo, hi)`, `0 ≤ lo < hi`. Then all constraints have a simultaneous solution. -/
theorem fc46_row {ι : Type*} [Finite ι] {r : ι → ι → Prop}
    (hr : ∀ i, ¬ Relation.TransGen r i i) (A : ∀ i, (∀ j, r j i → ℝ) → Set ℝ)
    (hA : ∀ i (v : ∀ j, r j i → ℝ), (∀ j hj, 0 < v j hj) →
      (∃ U : Finset ℝ, (∀ b ∈ U, 0 < b) ∧ A i v = {x | 0 < x ∧ ∀ b ∈ U, x < b}) ∨
      (∃ L : Finset ℝ, A i v = {x | 0 < x ∧ ∀ b ∈ L, b < x}) ∨
      (∃ lo hi : ℝ, 0 ≤ lo ∧ lo < hi ∧ Ioo lo hi ⊆ A i v)) :
    ∃ f : ι → ℝ, (∀ i, 0 < f i) ∧ ∀ i, f i ∈ A i (fun j _ => f j) := by
  refine exists_positive_parameters_of_acyclic hr A fun i v hv => ?_
  rcases hA i v hv with ⟨U, hU, hUA⟩ | ⟨L, hLA⟩ | ⟨lo, hi, hlo, hlohi, hI⟩
  · exact Or.inl ⟨U, hU, hUA.ge⟩
  · refine Or.inr (Or.inr (exists_pos_mem_of_lower_bounds (insert 0 L) ?_))
    intro x hx
    rw [hLA]
    exact ⟨hx 0 (Finset.mem_insert_self 0 L), fun b hb => hx b (Finset.mem_insert_of_mem hb)⟩
  · exact Or.inr (Or.inr ⟨(lo + hi) / 2, hI ⟨by linarith, by linarith⟩,
      mem_Ioi.mpr (by linarith)⟩)

end FC46

end DifferentialGeometry.Analysis
