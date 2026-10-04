import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SurfaceEntropyContinuity
import DifferentialGeometry.Geometry.Comparison.Distance.Continuity
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness

/-!
# Diameter from a lower bound on ball volumes

Chapter 7, packet P8, surface lemma U1, route (a), lane a4 (review 17 §4.5).
`riemannianEDistOf_toReal_lt_of_ball_volume`: on a compact connected manifold, if every `g`-ball of
radius `r` has volume at least `v > 0`, then every distance is less than `2 r · Area / v`.

For `x`, `y` at distance `L`, the distance from `x` is continuous and takes every value in `[0, L]`
on the connected manifold, so there are points `z₀, …, z_m` with `d(x, z_i) = 2 r i`,
`m = ⌊L / (2r)⌋`. These points are `2r`-separated, hence their `r`-balls are pairwise disjoint and
`(m + 1) v ≤ Area`, while `L < 2 r (m + 1)`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Integral.Measure
open MeasureTheory Filter Topology Set
open scoped Manifold ContDiff ENNReal

namespace GC.Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]

private local instance packingMeasurable : MeasurableSpace M := borel M
private local instance packingBorel : BorelSpace M := ⟨rfl⟩

theorem riemannianEDistOf_toReal_lt_of_ball_volume (g : SmoothRiemannianMetric I M) {r v : ℝ}
    (hr : 0 < r) (hv : 0 < v)
    (hball : ∀ z, ENNReal.ofReal v ≤
      riemannianVolumeMeasure I M g {w | riemannianEDistOf g z w < ENNReal.ofReal r})
    (x y : M) : (riemannianEDistOf g x y).toReal < 2 * r * (surfaceArea g / v) := by
  let μ := riemannianVolumeMeasure I M g
  let _ : IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  have hcont : ∀ z, Continuous (fun w => riemannianEDistOf g z w) := fun z =>
    DifferentialGeometry.Geometry.Riemannian.continuous_riemannianEDist g z
  have hfin : ∀ z w, riemannianEDistOf g z w ≠ ⊤ := fun z w => riemannianEDistOf_ne_top g z w
  set L := (riemannianEDistOf g x y).toReal with hL
  have hxy : riemannianEDistOf g x y = ENNReal.ofReal L := (ENNReal.ofReal_toReal (hfin x y)).symm
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  set m := ⌊L / (2 * r)⌋₊ with hm
  have hmle : (m : ℝ) ≤ L / (2 * r) := Nat.floor_le (by positivity)
  have hmlt : L / (2 * r) < m + 1 := Nat.lt_floor_add_one _
  have hz : ∀ i : Fin (m + 1), ∃ z, riemannianEDistOf g x z = ENNReal.ofReal (2 * r * i) := by
    intro i
    have hi : (i : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp i.2
    have hle : 2 * r * i ≤ L := by
      rw [le_div_iff₀ (by positivity)] at hmle
      nlinarith
    have hmem : ENNReal.ofReal (2 * r * i) ∈
        Icc (riemannianEDistOf g x x) (riemannianEDistOf g x y) := by
      rw [riemannianEDistOf_self, hxy]
      exact ⟨zero_le, ENNReal.ofReal_le_ofReal hle⟩
    obtain ⟨z, hz⟩ := intermediate_value_univ x y (hcont x) hmem
    exact ⟨z, hz⟩
  choose z hzd using hz
  let B : Fin (m + 1) → Set M := fun i => {w | riemannianEDistOf g (z i) w < ENNReal.ofReal r}
  have hBmeas : ∀ i, MeasurableSet (B i) := fun i =>
    (isOpen_lt (hcont (z i)) continuous_const).measurableSet
  have hsep : ∀ i j : Fin (m + 1), (i : ℕ) < j → ∀ w, w ∈ B i → w ∈ B j → False := by
    intro i j hij w hwi hwj
    have hdi : (riemannianEDistOf g (z i) w).toReal < r :=
      (ENNReal.lt_ofReal_iff_toReal_lt (hfin _ _)).mp hwi
    have hdj : (riemannianEDistOf g w (z j)).toReal < r := by
      rw [riemannianEDistOf_comm]
      exact (ENNReal.lt_ofReal_iff_toReal_lt (hfin _ _)).mp hwj
    have h1 := riemannianEDistOf_toReal_triangle g x (z i) (z j) (hfin _ _) (hfin _ _)
    have h2 := riemannianEDistOf_toReal_triangle g (z i) w (z j) (hfin _ _) (hfin _ _)
    rw [hzd i, hzd j, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)] at h1
    have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    nlinarith
  have hdisj : Pairwise (Function.onFun Disjoint B) := by
    intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro w hwi hwj
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
    · exact hsep i j h w hwi hwj
    · exact hsep j i h w hwj hwi
  have hsum : ((m + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal v ≤ μ univ := by
    calc ((m + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal v = ∑ _i : Fin (m + 1), ENNReal.ofReal v := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑ i, μ (B i) := Finset.sum_le_sum fun i _ => hball (z i)
      _ = μ (⋃ i, B i) := by rw [measure_iUnion hdisj hBmeas, tsum_fintype]
      _ ≤ μ univ := measure_mono (subset_univ _)
  have hreal : ((m : ℝ) + 1) * v ≤ surfaceArea g := by
    have h := ENNReal.toReal_mono (measure_ne_top μ univ) hsum
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hv.le] at h
    simpa only [surfaceArea, measureReal_def, Nat.cast_add, Nat.cast_one] using h
  have h1 : L < 2 * r * (m + 1) := by
    rw [div_lt_iff₀ (by positivity)] at hmlt
    linarith
  have h2 : (m : ℝ) + 1 ≤ surfaceArea g / v := by
    rw [le_div_iff₀ hv]
    exact hreal
  calc L < 2 * r * (m + 1) := h1
    _ ≤ 2 * r * (surfaceArea g / v) := by gcongr

end GC.Geometry
