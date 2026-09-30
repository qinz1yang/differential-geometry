# Factor-dimension mathematical and executable review

This is an assistant self-review, not independent mathematical or human
approval. Read `factor_dimension.md` for the exact quantified contracts.
The supplemental checker compiles the following six uses and checks actual
compiled supplier dependencies. The combined gate checks every owned
constant, including generated helpers, for standard-axiom-only closure.

Reviewed points: Pythagorean rather than max product metric; onto rather
than embedding-only splitting; actual closed slice; coincident segment
endpoints; k=0 and delta=1; grid delta>1; k<=n before natural subtraction;
k=n giving the singleton factor; exact cardinality without ceiling loss;
source constants fixed before the mesh; a line based away from q;
actual pointed Euclidean conclusion. The curvature-to-covering producer
and general one-dimensional model recognition are explicitly outstanding.
No authored mathematical leaf present at the start of this step is changed.

```lean
import DifferentialGeometry.Geometry.Metric.Approximation.FactorSplitting

open Set Filter MeasureTheory
open GC.MetricGeometry

example : ∃ G : Finset (EuclideanSpace ℝ (Fin 0)),
    1 ≤ (G.card : ℝ) ∧ (∀ x ∈ G, ‖x‖ ≤ 0) ∧
    (G : Set (EuclideanSpace ℝ (Fin 0))).Pairwise (fun a b => 1 ≤ dist a b) := by
  simpa using EuclideanSpace.exists_separated_grid 0 (by norm_num : (0 : ℝ) < 1)

example (k : ℕ) : ∃ G : Finset (EuclideanSpace ℝ (Fin k)),
    ((2 : ℝ)⁻¹) ^ k ≤ (G.card : ℝ) ∧ (∀ x ∈ G, ‖x‖ ≤ Real.sqrt k) ∧
    (G : Set (EuclideanSpace ℝ (Fin k))).Pairwise (fun a b => 2 ≤ dist a b) :=
  EuclideanSpace.exists_separated_grid k (by norm_num)

example {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin 0) × Y))
    (p : X) (q : Y) (hp : e p = WithLp.toLp 2 (0, q))
    {R C : ℝ} (hC : 0 < C)
    (hnets : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ S : Finset X,
      (S.card : ℝ) ≤ C * ε ^ (-(0 : ℝ)) ∧
      (∀ x ∈ S, dist x p ≤ R + Real.sqrt 0 + 1) ∧
      ∀ x : X, dist x p ≤ R + Real.sqrt 0 + 1 → ∃ y ∈ S, dist x y ≤ ε) :
    ∃ F : Finset Y, (F.card : ℝ) ≤ C ∧ (∀ y ∈ F, dist y q ≤ R) ∧
      ∀ y : Y, dist y q ≤ R → ∃ z ∈ F, dist y z < 1 := by
  simpa using e.exists_finset_net_euclidean_factor (n := 0) (R := R) (by omega)
    p q hp (δ := 1) (by norm_num) (by norm_num) hC (by simpa using hnets)

example {X : Type*} [MetricSpace X] {a b : X} (hab : a ≠ b)
    {f : Icc (0 : ℝ) 1 → X}
    (hd : ∀ s t, dist (f s) (f t) = dist a b * dist s t) :
    1 ≤ dimH (univ : Set X) :=
  Metric.one_le_dimH_of_nonconstant_segment hab hd

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (k : ℕ)
    (e : X ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Y))
    (p : X) (q : Y) (hp : e p = WithLp.toLp 2 (0, q))
    (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (hnets : ∀ S : ℝ, 0 < S → ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ F : Finset X,
        (F.card : ℝ) ≤ C * ε ^ (-(k : ℝ)) ∧
        (∀ x ∈ F, dist x p ≤ S) ∧
        ∀ x : X, dist x p ≤ S → ∃ y ∈ F, dist x y ≤ ε) :
    ∃ f : X ≃ᵢ EuclideanSpace ℝ (Fin k), f p = 0 :=
  e.exists_pointed_isometryEquiv_euclidean_of_splitting p q hp hsegments hnets

example {X : ℕ → Type*} {Y Z : Type*}
    [∀ i, MetricSpace (X i)] [MetricSpace Y] [MetricSpace Z]
    {p : ∀ i, X i} {q : Y} (h : PointedGHConverges p q)
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-(2 : ℝ)) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    (e : Y ≃ᵢ WithLp 2 (ℝ × Z)) (z : Z) :
    dimH (univ : Set Z) ≤ 1 := by
  simpa using h.dimH_real_factor_le (n := 2) (by omega) hcover e z

run_cmd Lean.logInfo "FACTOR_DIMENSION_REVIEW_PASS"
```

The last example intentionally has no marking equation between e and q.
The generic full-rank example allows k=0 and k=2 without extra assumptions.
The existence of an onto splitting, its factor point, and the covering
bounds remain explicit hypotheses; the examples do not manufacture them.
