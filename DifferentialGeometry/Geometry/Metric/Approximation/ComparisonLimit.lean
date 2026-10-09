import DifferentialGeometry.Geometry.Metric.Approximation.FiniteConfiguration
import DifferentialGeometry.Geometry.Metric.Approximation.DimensionLimit
import DifferentialGeometry.Geometry.Comparison.FourPoint
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FinCases

open Filter Set
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v
variable {X : ℕ → Type u} {Y : Type v}
variable [∀ i, MetricSpace (X i)] [MetricSpace Y]
variable {p : ∀ i, X i} {q : Y} {κ : ℕ → ℝ}

theorem PointedGHConverges.fourPointComparison_zero_of_eventual_comparison
    (h : PointedGHConverges p q) (hκ : ∀ i, 0 ≤ κ i)
    (hκzero : Tendsto κ atTop (𝓝 0))
    (hcompare : ∀ R : ℝ, 0 < R →
      ∀ᶠ i in atTop, fourPointComparison (κ i) (Metric.ball (p i) R)) :
    fourPointComparison 0 (univ : Set Y) := by
  intro x hx a ha b hb c hc hax hbx hcx
  let y : Fin 4 → Y := ![x, a, b, c]
  let M := 1 + dist x q + dist a q + dist b q + dist c q
  have hM : 1 ≤ M := by
    dsimp [M]
    linarith [dist_nonneg (x := x) (y := q), dist_nonneg (x := a) (y := q),
      dist_nonneg (x := b) (y := q), dist_nonneg (x := c) (y := q)]
  have hy : ∀ i, dist (y i) q ≤ M := by
    intro i
    fin_cases i <;> simp [y, M] <;>
      linarith [dist_nonneg (x := x) (y := q), dist_nonneg (x := a) (y := q),
        dist_nonneg (x := b) (y := q), dist_nonneg (x := c) (y := q)]
  let ε : ℕ → ℝ := fun j => (1 / 8) * (1 / ((j : ℝ) + 1))
  have hεpos : ∀ j, 0 < ε j := by intro j; dsimp [ε]; positivity
  have hεsmall : ∀ j, ε j < 1 / 4 := by
    intro j
    have hden : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hdiv : 1 / ((j : ℝ) + 1) ≤ 1 := by
      exact (div_le_one (by positivity)).2 hden
    dsimp [ε]
    linarith
  have hεzero : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0))
  obtain ⟨φ, hφ, hP, z, hrad, hinside, herror, hdist⟩ :=
    h.exists_subsequence_lift_configuration hM y hy ε hεpos hεsmall hεzero
      (fun _ i => fourPointComparison (κ i) (Metric.ball (p i) (M + 3)))
      (fun _ => hcompare (M + 3) (by linarith))
  have hzmem (j : ℕ) (i : Fin 4) :
      (z j i).val ∈ Metric.ball (p (φ j)) (M + 3) := by
    change dist (z j i).val (p (φ j)) < M + 3
    linarith [hinside j i]
  have hxa : 0 < dist (y 0) (y 1) := by simpa [y] using dist_pos.mpr hax.symm
  have hxb : 0 < dist (y 0) (y 2) := by simpa [y] using dist_pos.mpr hbx.symm
  have hxc : 0 < dist (y 0) (y 3) := by simpa [y] using dist_pos.mpr hcx.symm
  have hpos1 := (hdist 0 1).eventually (Ioi_mem_nhds hxa)
  have hpos2 := (hdist 0 2).eventually (Ioi_mem_nhds hxb)
  have hpos3 := (hdist 0 3).eventually (Ioi_mem_nhds hxc)
  have hsource : ∀ᶠ j in atTop,
      comparisonAngleNegCurvature (κ (φ j))
          (dist (z j 0).val (z j 1).val) (dist (z j 0).val (z j 2).val)
          (dist (z j 1).val (z j 2).val) +
        comparisonAngleNegCurvature (κ (φ j))
          (dist (z j 0).val (z j 2).val) (dist (z j 0).val (z j 3).val)
          (dist (z j 2).val (z j 3).val) +
        comparisonAngleNegCurvature (κ (φ j))
          (dist (z j 0).val (z j 3).val) (dist (z j 0).val (z j 1).val)
          (dist (z j 3).val (z j 1).val) ≤ 2 * Real.pi := by
    filter_upwards [hpos1, hpos2, hpos3] with j hj1 hj2 hj3
    exact hP j (z j 0).val (hzmem j 0) (z j 1).val (hzmem j 1)
      (z j 2).val (hzmem j 2) (z j 3).val (hzmem j 3)
      (dist_pos.mp hj1).symm (dist_pos.mp hj2).symm (dist_pos.mp hj3).symm
  have hk := hκzero.comp hφ.tendsto_atTop
  have hang12 := tendsto_comparisonAngleNegCurvature_zero
    hk (hdist 0 1) (hdist 0 2) (hdist 1 2) (Eventually.of_forall (fun j => hκ (φ j))) hxa hxb
  have hang23 := tendsto_comparisonAngleNegCurvature_zero
    hk (hdist 0 2) (hdist 0 3) (hdist 2 3) (Eventually.of_forall (fun j => hκ (φ j))) hxb hxc
  have hang31 := tendsto_comparisonAngleNegCurvature_zero
    hk (hdist 0 3) (hdist 0 1) (hdist 3 1) (Eventually.of_forall (fun j => hκ (φ j))) hxc hxa
  have hsum := le_of_tendsto ((hang12.add hang23).add hang31) hsource
  simpa [y, comparisonAngleNegCurvature] using hsum

theorem PointedGHConverges.fourPointComparison_zero_of_growing_balls
    (h : PointedGHConverges p q) (hκ : ∀ i, 0 ≤ κ i)
    (hκzero : Tendsto κ atTop (𝓝 0)) {ρ : ℕ → ℝ}
    (hρ : Tendsto ρ atTop atTop)
    (hcompare : ∀ᶠ i in atTop, fourPointComparison (κ i) (Metric.ball (p i) (ρ i))) :
    fourPointComparison 0 (univ : Set Y) := by
  apply h.fourPointComparison_zero_of_eventual_comparison hκ hκzero
  intro R _
  filter_upwards [hcompare, hρ.eventually (eventually_ge_atTop R)] with i hi hRi
  exact hi.mono (Metric.ball_subset_ball hRi)

theorem PointedGHConverges.quadratic_side_comparison_of_eventual_comparison
    (h : PointedGHConverges p q) (hκ : ∀ i, 0 ≤ κ i)
    (hκzero : Tendsto κ atTop (𝓝 0))
    (hcompare : ∀ R : ℝ, 0 < R →
      ∀ᶠ i in atTop, fourPointComparison (κ i) (Metric.ball (p i) R))
    {a b z v : Y} {t : ℝ} (ht : t ∈ Icc 0 1)
    (haz : dist a z = t * dist a b) (hzb : dist z b = (1 - t) * dist a b) :
    (1 - t) * dist v a ^ 2 + t * dist v b ^ 2 -
      t * (1 - t) * dist a b ^ 2 ≤ dist v z ^ 2 :=
  quadratic_side_comparison_of_fourPointComparison
    (h.fourPointComparison_zero_of_eventual_comparison hκ hκzero hcompare)
    (mem_univ a) (mem_univ b) (mem_univ z) (mem_univ v) ht haz hzb

theorem exists_geodesic_pointedGHConverges_of_covering_and_comparison
    (p : ∀ i, X i) {d : ℝ} (hd : 0 ≤ d)
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-d) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    (hcurves : ∀ i, ∀ a b : X i, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0))
    (hcompare : ∀ R : ℝ, 0 < R →
      ∀ᶠ i in atTop, fourPointComparison (κ i) (Metric.ball (p i) R)) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        dimH (univ : Set Y) ≤ ENNReal.ofReal d ∧
        fourPointComparison 0 (univ : Set Y) ∧
        (∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t) ∧
        (∀ a b z v : Y, ∀ t ∈ Icc (0 : ℝ) 1,
          dist a z = t * dist a b → dist z b = (1 - t) * dist a b →
          (1 - t) * dist v a ^ 2 + t * dist v b ^ 2 -
            t * (1 - t) * dist a b ^ 2 ≤ dist v z ^ 2) := by
  obtain ⟨Y, m, q, φ, hφ, hproper, hconv, hdim, hsegments⟩ :=
    exists_geodesic_pointedGHConverges_dimH_le_of_eventual_polynomial_nets p hd hcover hcurves
  let := m
  have hcomp : fourPointComparison 0 (univ : Set Y) :=
    hconv.fourPointComparison_zero_of_eventual_comparison (fun i => hκ (φ i))
      (hκzero.comp hφ.tendsto_atTop)
      (fun R hR => hφ.tendsto_atTop.eventually (hcompare R hR))
  refine ⟨Y, m, q, φ, hφ, hproper, hconv, hdim, hcomp, hsegments, ?_⟩
  intro a b z v t ht haz hzb
  exact quadratic_side_comparison_of_fourPointComparison hcomp
    (mem_univ a) (mem_univ b) (mem_univ z) (mem_univ v) ht haz hzb

end GC.MetricGeometry
