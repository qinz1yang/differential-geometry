import DifferentialGeometry.Geometry.Metric.Approximation.CoveringLimit
import DifferentialGeometry.Geometry.Metric.Approximation.PointedPrecompactness
import DifferentialGeometry.Geometry.Metric.Approximation.MidpointTransfer
import DifferentialGeometry.Topology.MetricSpace.PolynomialCovering

open Filter Set
open scoped MeasureTheory

namespace GC.MetricGeometry

universe u v
variable {X : ℕ → Type u} {Y : Type v}
variable [∀ i, MetricSpace (X i)] [MetricSpace Y]
variable {p : ∀ i, X i} {q : Y} {d : ℝ}

private theorem polynomial_nets_closedBall (h : PointedGHConverges p q)
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-d) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ T : Finset Y,
      (∀ y ∈ T, y ∈ Metric.closedBall q R) ∧ (T.card : ℝ) ≤ C * δ ^ (-d) ∧
      ∀ y ∈ Metric.closedBall q R, ∃ z ∈ T, dist y z ≤ δ := by
  obtain ⟨C, hC, hnet⟩ := hcover (R + 1) (by linarith)
  refine ⟨C * 4 ^ d, by positivity, fun δ hδ hδone => ?_⟩
  obtain ⟨T, hcard, hTin, hTnet⟩ :=
    h.exists_internal_finset_net_of_polynomial_covering hR hδ hδone hnet
  exact ⟨T, hTin, hcard, fun y hy => by
    obtain ⟨z, hz, hyz⟩ := hTnet y hy
    exact ⟨z, hz, hyz.le⟩⟩

private theorem iUnion_closedBall_nat_add_one (q : Y) :
    (⋃ i : ℕ, Metric.closedBall q ((i : ℝ) + 1)) = univ := by
  apply eq_univ_of_forall
  intro y
  obtain ⟨i, hi⟩ := exists_nat_gt (dist y q)
  exact mem_iUnion.mpr ⟨i, by change dist y q ≤ (i : ℝ) + 1; linarith⟩

theorem PointedGHConverges.hausdorffMeasure_univ_zero_of_polynomial_covering
    [MeasurableSpace Y] [BorelSpace Y] (h : PointedGHConverges p q) (hd : 0 ≤ d)
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-d) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    {s : ℝ} (hs : d < s) :
    MeasureTheory.Measure.hausdorffMeasure s (univ : Set Y) = 0 := by
  rw [← iUnion_closedBall_nat_add_one q]
  exact MeasureTheory.Measure.hausdorffMeasure_iUnion_zero_of_polynomial_nets
    (fun i : ℕ => Metric.closedBall q ((i : ℝ) + 1)) hd
    (fun i => polynomial_nets_closedBall h hcover (by positivity)) hs

theorem PointedGHConverges.dimH_le_of_polynomial_covering
    (h : PointedGHConverges p q) (hd : 0 ≤ d)
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-d) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η) :
    dimH (univ : Set Y) ≤ ENNReal.ofReal d := by
  rw [← iUnion_closedBall_nat_add_one q]
  exact dimH_iUnion_le_of_polynomial_nets
    (fun i : ℕ => Metric.closedBall q ((i : ℝ) + 1)) hd
    (fun i => polynomial_nets_closedBall h hcover (by positivity))

private theorem eventual_finite_nets_of_polynomial_covering
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-d) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η) :
    ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ N I : ℕ, ∀ i : ℕ, I ≤ i →
      ∃ F : Finset (X i), F.card ≤ N ∧
        (∀ x ∈ F, dist x (p i) ≤ R) ∧
        ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η := by
  intro R hR η hη
  obtain ⟨C, _, hC⟩ := hcover R hR
  let δ := min η 1
  have hδ : 0 < δ := lt_min hη zero_lt_one
  obtain ⟨I, hI⟩ := eventually_atTop.mp (hC δ hδ (min_le_right _ _))
  refine ⟨Nat.ceil (C * δ ^ (-d)), I, fun i hi => ?_⟩
  obtain ⟨F, hcard, hFin, hnet⟩ := hI i hi
  refine ⟨F, ?_, hFin, fun x hx => ?_⟩
  · exact_mod_cast hcard.trans (Nat.le_ceil (C * δ ^ (-d)))
  · obtain ⟨y, hy, hxy⟩ := hnet x hx
    exact ⟨y, hy, hxy.trans (min_le_left _ _)⟩

theorem exists_pointedGHConverges_dimH_le_of_eventual_polynomial_nets
    (p : ∀ i, X i) (hd : 0 ≤ d)
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-d) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        dimH (univ : Set Y) ≤ ENNReal.ofReal d := by
  obtain ⟨Y, m, q, φ, hφ, hproper, hconv⟩ :=
    exists_pointedGHConverges_of_eventual_finite_nets p
      (eventual_finite_nets_of_polynomial_covering hcover)
  let := m
  refine ⟨Y, m, q, φ, hφ, hproper, hconv, hconv.dimH_le_of_polynomial_covering hd ?_⟩
  intro R hR
  obtain ⟨C, hC, hnet⟩ := hcover R hR
  exact ⟨C, hC, fun η hη hηone => hφ.tendsto_atTop.eventually (hnet η hη hηone)⟩

theorem exists_geodesic_pointedGHConverges_dimH_le_of_eventual_polynomial_nets
    (p : ∀ i, X i) (hd : 0 ≤ d)
    (hcover : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        ∀ᶠ i in atTop, ∃ F : Finset (X i), (F.card : ℝ) ≤ C * η ^ (-d) ∧
          (∀ x ∈ F, dist x (p i) ≤ R) ∧
          ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    (hcurves : ∀ i, ∀ a b : X i, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X i, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε)) :
    ∃ (Y : Type) (m : MetricSpace Y),
      letI := m
      ∃ (q : Y) (φ : ℕ → ℕ), StrictMono φ ∧ ProperSpace Y ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        dimH (univ : Set Y) ≤ ENNReal.ofReal d ∧
        ∀ a b : Y, ∃ f : Icc (0 : ℝ) 1 → Y, Continuous f ∧
          f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
          ∀ s t, dist (f s) (f t) = dist a b * dist s t := by
  obtain ⟨Y, m, q, φ, hφ, hproper, hconv, hdim⟩ :=
    exists_pointedGHConverges_dimH_le_of_eventual_polynomial_nets p hd hcover
  let := m
  let := hproper
  exact ⟨Y, m, q, φ, hφ, hproper, hconv, hdim,
    hconv.exists_metric_segment_of_source_curves (fun i => hcurves (φ i))⟩

private theorem polynomial_nets_closedBall_of_ceil_covering
    (h : PointedGHConverges p q) (n : ℕ) (B : ℝ → ℝ)
    (hB : ∀ R : ℝ, 0 < R → 0 ≤ B R)
    (hcover : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ᶠ i in atTop, ∃ F : Finset (X i), F.card ≤ (1 + Nat.ceil (B R / η)) ^ n ∧
        (∀ x ∈ F, dist x (p i) ≤ R) ∧
        ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    {R : ℝ} (hR : 0 < R) :
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ T : Finset Y,
      (∀ y ∈ T, y ∈ Metric.closedBall q R) ∧
      (T.card : ℝ) ≤ (2 + 4 * B (R + 1)) ^ n * δ ^ (-(n : ℝ)) ∧
      ∀ y ∈ Metric.closedBall q R, ∃ z ∈ T, dist y z ≤ δ := by
  intro δ hδ hδone
  obtain ⟨T, hcard, hTin, hTnet⟩ :=
    h.exists_internal_finset_net_of_ceil_covering n hR hδ hδone (hB (R + 1) (by linarith))
      (hcover (R + 1) (by linarith) (δ / 4) (by positivity) (by linarith))
  exact ⟨T, hTin, hcard, fun y hy => by
    obtain ⟨z, hz, hyz⟩ := hTnet y hy
    exact ⟨z, hz, hyz.le⟩⟩

theorem PointedGHConverges.hausdorffMeasure_univ_zero_of_ceil_covering
    [MeasurableSpace Y] [BorelSpace Y]
    (h : PointedGHConverges p q) (n : ℕ) (B : ℝ → ℝ)
    (hB : ∀ R : ℝ, 0 < R → 0 ≤ B R)
    (hcover : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ᶠ i in atTop, ∃ F : Finset (X i), F.card ≤ (1 + Nat.ceil (B R / η)) ^ n ∧
        (∀ x ∈ F, dist x (p i) ≤ R) ∧
        ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η)
    {s : ℝ} (hs : (n : ℝ) < s) :
    MeasureTheory.Measure.hausdorffMeasure s (univ : Set Y) = 0 := by
  rw [← iUnion_closedBall_nat_add_one q]
  apply MeasureTheory.Measure.hausdorffMeasure_iUnion_zero_of_polynomial_nets
    (fun i : ℕ => Metric.closedBall q ((i : ℝ) + 1)) (Nat.cast_nonneg n) _ hs
  intro i
  have hBi := hB ((i : ℝ) + 1 + 1) (by positivity)
  refine ⟨(2 + 4 * B ((i : ℝ) + 1 + 1)) ^ n, by positivity, ?_⟩
  exact polynomial_nets_closedBall_of_ceil_covering h n B hB hcover (by positivity)

theorem PointedGHConverges.dimH_le_of_ceil_covering
    (h : PointedGHConverges p q) (n : ℕ) (B : ℝ → ℝ)
    (hB : ∀ R : ℝ, 0 < R → 0 ≤ B R)
    (hcover : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → η ≤ 1 →
      ∀ᶠ i in atTop, ∃ F : Finset (X i), F.card ≤ (1 + Nat.ceil (B R / η)) ^ n ∧
        (∀ x ∈ F, dist x (p i) ≤ R) ∧
        ∀ x : X i, dist x (p i) ≤ R → ∃ y ∈ F, dist x y ≤ η) :
    dimH (univ : Set Y) ≤ n := by
  rw [← iUnion_closedBall_nat_add_one q]
  have hn : ENNReal.ofReal (n : ℝ) = n := by simp
  rw [← hn]
  apply dimH_iUnion_le_of_polynomial_nets
    (fun i : ℕ => Metric.closedBall q ((i : ℝ) + 1)) (Nat.cast_nonneg n)
  intro i
  have hBi := hB ((i : ℝ) + 1 + 1) (by positivity)
  refine ⟨(2 + 4 * B ((i : ℝ) + 1 + 1)) ^ n, by positivity, ?_⟩
  exact polynomial_nets_closedBall_of_ceil_covering h n B hB hcover (by positivity)

end GC.MetricGeometry
