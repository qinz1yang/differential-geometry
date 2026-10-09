import DifferentialGeometry.Geometry.Comparison.OrthogonalLineCoordinates
import DifferentialGeometry.Geometry.Metric.Approximation.PrefixCoordinateConvergence

open Set Filter Metric
open scoped Topology
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v

theorem exists_oriented_product_with_converging_distance_coordinates
    {A : ℕ → Type v} [∀ i, MetricSpace (A i)]
    {Y : Type u} [MetricSpace Y] [ProperSpace Y] {k : ℕ}
    {o : ∀ i, A i} {p : Y} {L E : ℕ → Fin k → ℝ} {R ε η : ℕ → ℝ}
    (hs : fourPointComparison 0 (univ : Set Y))
    (hsegments : ∀ a b : Y, ∃ g : Icc (0 : ℝ) 1 → Y,
      Continuous g ∧ g ⟨0, by norm_num⟩ = a ∧ g ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (g s) (g t) = dist a b * dist s t)
    (γ : Fin k → ℝ → Y) (hγ : ∀ j, Isometry (γ j)) (hγ0 : ∀ j, γ j 0 = p)
    (hangle : ∀ j l, j ≠ l → germComparisonAngle 0 (γ j) (γ l) = Real.pi / 2)
    (f : ∀ i, PointedBallApprox (o i) p (R i) (ε i))
    (hR : Tendsto R atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (a : ∀ i, Fin k → A i) (ha : ∀ i j, dist (o i) (a i j) = L i j)
    (hL : ∀ i j, 0 ≤ L i j) (hE : ∀ i j, 0 ≤ E i j)
    (hEzero : ∀ j, Tendsto (fun i => E i j) atTop (𝓝 0))
    (hηzero : Tendsto η atTop (𝓝 0))
    (Q : ∀ i j, Icc (-(L i j)) (L i j) → A i)
    (hLip : ∀ i j, LipschitzWith 1 (Q i j))
    (hbase : ∀ i j, Q i j ⟨0, ⟨by linarith [hL i j], hL i j⟩⟩ = o i)
    (hcal : ∀ i j, ∀ t : Icc (0 : ℝ) (L i j),
      t.val - η i ≤ L i j - dist (Q i j ⟨t.val, ⟨by linarith [t.property.1, hL i j], t.property.2⟩⟩) (a i j) ∧
      L i j - dist (Q i j ⟨-t.val, ⟨by linarith [t.property.2], by linarith [t.property.1, hL i j]⟩⟩) (a i j) ≤
        -t.val + E i j + η i)
    (hconv : ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
      S ≤ R i ∧ ∀ j, S ≤ L i j ∧
      ∀ t : Icc (-(L i j)) (L i j), |t.val| ≤ S →
        ∀ ht : dist (Q i j t) (o i) ≤ R i,
          dist ((f i).toFun ⟨Q i j t, ht⟩) (γ j t.val) < ζ) :
    ∃ (Z : Type u) (m : MetricSpace Z), letI := m
      ∃ (z : Z) (e : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × Z)),
        e p = WithLp.toLp 2 (0, z) ∧
        (∀ j t, e (γ j t) = WithLp.toLp 2 (PiLp.single 2 j t, z)) ∧
        (∀ j x, lineCoordinate (γ j) x = (e x).fst j) ∧
        (∀ j x, Tendsto (fun T : ℝ => dist x (γ j T) - T) atTop (𝓝 (-(e x).fst j))) ∧
        (∀ S : ℝ, 0 < S → ∀ ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
          S ≤ R i ∧ ∀ j, ∀ x : BallCarrier (o i) (R i), dist x.val (o i) ≤ S →
            |dist (o i) (a i j) - dist x.val (a i j) - (e ((f i).toFun x)).fst j| < ζ) ∧
        ProperSpace Z ∧ CompleteSpace Z ∧ fourPointComparison 0 (univ : Set Z) ∧
        (∀ a b : Z, ∃ g : Icc (0 : ℝ) 1 → Z,
          Continuous g ∧ g ⟨0, by norm_num⟩ = a ∧ g ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (g s) (g t) = dist a b * dist s t) := by
  obtain ⟨Z, m, z, e, he0, heaxis, hcoord, hbuse, hpZ, hcZ, hsZ, hsegZ⟩ :=
    exists_oriented_euclidean_coordinates p hs hsegments γ hγ hγ0 hangle
  let := m
  refine ⟨Z, m, z, e, he0, heaxis, hcoord, hbuse, ?_, hpZ, hcZ, hsZ, hsegZ⟩
  intro S hS ζ hζ
  have hj (j : Fin k) : ∀ᶠ i in atTop,
      S ≤ R i ∧ ∀ x : BallCarrier (o i) (R i), dist x.val (o i) ≤ S →
        |dist (o i) (a i j) - dist x.val (a i j) - (e ((f i).toFun x)).fst j| < ζ := by
    have hline := eventually_distance_coordinate_error_lt_of_converging_prefixes
      (lineSplitting hs (hγ j) hsegments) (lineSplitting_apply_line hs (hγ j) hsegments)
      (hγ0 j) f hR hε (fun i => a i j) (fun i => ha i j) (fun i => hL i j)
      (fun i => hE i j) (hEzero j) hηzero (fun i => Q i j)
      (fun i => hLip i j) (fun i => hbase i j) (fun i => hcal i j)
      (fun T δ hδ => (hconv T δ hδ).mono fun i hi => ⟨hi.1, (hi.2 j).1, (hi.2 j).2⟩)
      S hS ζ hζ
    simpa only [lineSplitting_fst, hcoord] using hline
  filter_upwards [hR.eventually_ge_atTop S, eventually_all.mpr hj] with i hi hjall
  exact ⟨hi, fun j => (hjall j).2⟩

end GC.MetricGeometry
