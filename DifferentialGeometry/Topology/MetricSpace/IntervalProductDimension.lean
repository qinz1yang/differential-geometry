import DifferentialGeometry.Topology.MetricSpace.PositiveHausdorffCover
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false

open Set Metric Filter Topology
open scoped ENNReal NNReal MeasureTheory

namespace MeasureTheory.Measure

private theorem interval_prod_null_of_positive_covers
    {Y : Type*} [MetricSpace Y] [MeasurableSpace (ℝ × Y)] [BorelSpace (ℝ × Y)]
    {A : Set Y} {B s : ℝ} (hB : 0 ≤ B) (hs : 0 < s)
    (hcover : ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∃ U : ℕ → Set Y, ∃ r : ℕ → ℝ,
        A ⊆ ⋃ i, U i ∧ (∀ i, 0 < r i ∧ r i ≤ δ ∧ ediam (U i) ≤ ENNReal.ofReal (r i)) ∧
        (∑' i, (ENNReal.ofReal (r i)) ^ s) ≤ ENNReal.ofReal ε) :
    hausdorffMeasure (s + 1) ((Icc 0 B) ×ˢ A) = 0 := by
  classical
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδpos (k : ℕ) : 0 < δ k := by dsimp [δ]; positivity
  have hδone (k : ℕ) : δ k ≤ 1 := by
    dsimp [δ]
    exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  choose U r hc hr hsum using fun k => hcover (δ k) (δ k) (hδpos k) (hδpos k)
  let N (k i : ℕ) : ℕ := ⌊B / r k i⌋₊ + 1
  let V (k : ℕ) (a : Σ i : ℕ, Fin (N k i)) : Set (ℝ × Y) :=
    (Icc ((a.2.val : ℝ) * r k a.1) (((a.2.val : ℝ) + 1) * r k a.1)) ×ˢ U k a.1
  have hVdiam (k : ℕ) (a : Σ i : ℕ, Fin (N k i)) :
      ediam (V k a) ≤ ENNReal.ofReal (r k a.1) := by
    apply ediam_le
    intro x hx y hy
    rw [Prod.edist_eq]
    refine max_le_iff.mpr ⟨?_, (edist_le_ediam_of_mem hx.2 hy.2).trans (hr k a.1).2.2⟩
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.dist_eq]
    apply abs_le.mpr
    constructor <;> nlinarith only [hx.1.1, hx.1.2, hy.1.1, hy.1.2]
  have hVcover (k : ℕ) : (Icc 0 B) ×ˢ A ⊆ ⋃ a, V k a := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hc k hy)
    let j : ℕ := ⌊t / r k i⌋₊
    have hjN : j < N k i := Nat.lt_succ_of_le (Nat.floor_mono
      (div_le_div_of_nonneg_right ht.2 (hr k i).1.le))
    apply mem_iUnion.mpr
    refine ⟨⟨i, ⟨j, hjN⟩⟩, ⟨?_, hi⟩⟩
    constructor
    · exact (le_div_iff₀ (hr k i).1).mp (Nat.floor_le (div_nonneg ht.1 (hr k i).1.le))
    · exact ((div_lt_iff₀ (hr k i).1).mp (Nat.lt_floor_add_one (t / r k i))).le
  have hN (k i : ℕ) : (N k i : ℝ) * r k i ≤ B + 1 := by
    have hf := Nat.floor_le (div_nonneg hB (hr k i).1.le)
    have hh := (le_div_iff₀ (hr k i).1).mp hf
    have hh' := (hr k i).2.1.trans (hδone k)
    dsimp [N]
    push_cast
    nlinarith
  have hcost (k : ℕ) :
      (∑' a, ediam (V k a) ^ (s + 1)) ≤
        ENNReal.ofReal (B + 1) * ENNReal.ofReal (δ k) := by
    calc
      (∑' a, ediam (V k a) ^ (s + 1)) ≤
          ∑' a : Σ i : ℕ, Fin (N k i), (ENNReal.ofReal (r k a.1)) ^ (s + 1) :=
        ENNReal.tsum_le_tsum fun a => ENNReal.rpow_le_rpow (hVdiam k a) (by linarith)
      _ = ∑' i, (N k i : ℝ≥0∞) * (ENNReal.ofReal (r k i)) ^ (s + 1) := by
        rw [ENNReal.tsum_sigma']
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ ∑' i, ENNReal.ofReal (B + 1) * (ENNReal.ofReal (r k i)) ^ s := by
        apply ENNReal.tsum_le_tsum
        intro i
        calc
          (N k i : ℝ≥0∞) * (ENNReal.ofReal (r k i)) ^ (s + 1) =
              ENNReal.ofReal ((N k i : ℝ) * r k i) * (ENNReal.ofReal (r k i)) ^ s := by
            rw [ENNReal.rpow_add_of_nonneg _ _ hs.le zero_le_one, ENNReal.rpow_one,
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
            ac_rfl
          _ ≤ ENNReal.ofReal (B + 1) * (ENNReal.ofReal (r k i)) ^ s :=
            mul_le_mul_left (ENNReal.ofReal_le_ofReal (hN k i)) _
      _ = ENNReal.ofReal (B + 1) * ∑' i, (ENNReal.ofReal (r k i)) ^ s := ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (B + 1) * ENNReal.ofReal (δ k) := mul_le_mul_right (hsum k) _
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hrad : Tendsto (fun k => ENNReal.ofReal (δ k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hδlim
  have hcostlim : Tendsto (fun k => ENNReal.ofReal (B + 1) * ENNReal.ofReal (δ k))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hrad (Or.inr ENNReal.ofReal_ne_top)
  have hlim : Tendsto (fun k => ∑' a, ediam (V k a) ^ (s + 1)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcostlim
      (fun _ => bot_le) hcost
  apply le_antisymm _ bot_le
  calc
    hausdorffMeasure (s + 1) ((Icc 0 B) ×ˢ A) ≤
        liminf (fun k => ∑' a, ediam (V k a) ^ (s + 1)) atTop :=
      hausdorffMeasure_le_liminf_tsum (s + 1) _ _ hrad V
        (Eventually.of_forall fun k a => (hVdiam k a).trans
          (ENNReal.ofReal_le_ofReal (hr k a.1).2.1)) (Eventually.of_forall hVcover)
    _ = 0 := hlim.liminf_eq

end MeasureTheory.Measure

private theorem dimH_interval_prod_le_of_null_rule
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace (ℝ × Y)] [BorelSpace (ℝ × Y)]
    (A : Set Y) {B : ℝ}
    (hnull : ∀ s : ℝ, 0 < s → MeasureTheory.Measure.hausdorffMeasure s A = 0 →
      MeasureTheory.Measure.hausdorffMeasure (s + 1) ((Icc 0 B) ×ˢ A) = 0) :
    dimH ((Icc 0 B) ×ˢ A) ≤ dimH A + 1 := by
  apply dimH_le
  intro d hd
  by_contra! hlt
  let s : ℝ≥0 := d - 1
  have hds : dimH A < (s : ℝ≥0∞) := by
    dsimp [s]
    rw [ENNReal.coe_sub, ENNReal.coe_one]
    exact (ENNReal.cancel_of_ne ENNReal.one_ne_top).lt_tsub_iff_right.mpr hlt
  have hs : 0 < (s : ℝ) := by
    have hh : (0 : ℝ≥0∞) < (s : ℝ≥0∞) := lt_of_le_of_lt bot_le hds
    exact_mod_cast hh
  have hd1 : (1 : ℝ≥0) ≤ d := by
    have hh : (1 : ℝ≥0∞) < d := (le_add_left le_rfl).trans_lt hlt
    exact_mod_cast hh.le
  have hsd : (s : ℝ) + 1 = (d : ℝ) := by
    dsimp [s]
    rw [NNReal.coe_sub hd1, NNReal.coe_one]
    ring
  have hz := hnull s hs (hausdorffMeasure_of_dimH_lt hds)
  rw [hsd] at hz
  exact ENNReal.zero_ne_top (hz.symm.trans hd)

namespace MeasureTheory.Measure

theorem hausdorffMeasure_Icc_prod_eq_zero
    {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MeasurableSpace (ℝ × Y)] [BorelSpace (ℝ × Y)]
    {A : Set Y} {B s : ℝ} (hB : 0 ≤ B) (hs : 0 < s)
    (hzero : hausdorffMeasure s A = 0) :
    hausdorffMeasure (s + 1) ((Icc 0 B) ×ˢ A) = 0 := by
  apply interval_prod_null_of_positive_covers hB hs
  intro δ ε hδ hε
  exact exists_cover_by_positive_radii_of_hausdorffMeasure_zero hs hzero hδ hε

end MeasureTheory.Measure

theorem dimH_Icc_prod_le_add_one
    {Y : Type*} [MetricSpace Y] (A : Set Y) {B : ℝ} (hB : 0 ≤ B) :
    dimH ((Icc 0 B) ×ˢ A) ≤ dimH A + 1 := by
  borelize Y
  borelize (ℝ × Y)
  apply dimH_interval_prod_le_of_null_rule A
  intro s hs hzero
  exact MeasureTheory.Measure.hausdorffMeasure_Icc_prod_eq_zero hB hs hzero
