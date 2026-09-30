import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.SpecificLimits.Basic

open scoped Topology ENNReal MeasureTheory
open Set Filter Metric

namespace MeasureTheory.Measure

theorem hausdorffMeasure_zero_of_polynomial_nets
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {A : Set X} {n C s : ℝ} (hn : 0 ≤ n) (hC : 0 < C)
    (hnets : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ F : Finset X,
      (∀ x ∈ F, x ∈ A) ∧ (F.card : ℝ) ≤ C * δ ^ (-n) ∧
      ∀ x ∈ A, ∃ y ∈ F, dist x y ≤ δ)
    (hs : n < s) : hausdorffMeasure s A = 0 := by
  classical
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδpos : ∀ k, 0 < δ k := fun k => by dsimp [δ]; positivity
  have hδle : ∀ k, δ k ≤ 1 := fun k => by
    dsimp [δ]
    exact (div_le_one (by positivity)).2 (by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  choose F hF using fun k => hnets (δ k) (hδpos k) (hδle k)
  let t : ∀ k : ℕ, F k → Set X := fun k y => A ∩ closedBall (y : X) (δ k)
  have ht : ∀ k (y : F k), ediam (t k y) ≤ ENNReal.ofReal (2 * δ k) := by
    intro k y
    apply ediam_le_of_forall_dist_le
    intro a ha b hb
    calc
      dist a b ≤ dist a y + dist b y := dist_triangle_right a b y
      _ ≤ δ k + δ k := add_le_add ha.2 hb.2
      _ = 2 * δ k := by ring
  have hcover : ∀ k, A ⊆ ⋃ y : F k, t k y := by
    intro k x hx
    obtain ⟨y, hy, hxy⟩ := (hF k).2.2 x hx
    exact mem_iUnion.2 ⟨⟨y, hy⟩, hx, hxy⟩
  have hspos : 0 < s := hn.trans_lt hs
  have hsum : ∀ k,
      (∑ y : F k, ediam (t k y) ^ s) ≤
        ENNReal.ofReal (C * 2 ^ s) * ENNReal.ofReal (δ k) ^ (s - n) := by
    intro k
    calc
      (∑ y : F k, ediam (t k y) ^ s) ≤
          ∑ _y : F k, ENNReal.ofReal (2 * δ k) ^ s :=
        Finset.sum_le_sum fun y _ => ENNReal.rpow_le_rpow (ht k y) hspos.le
      _ = ENNReal.ofReal ((F k).card * (2 * δ k) ^ s) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hspos.le]
        simp [ENNReal.ofReal_mul, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal ((C * δ k ^ (-n)) * (2 * δ k) ^ s) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (hF k).2.1 (by positivity))
      _ = ENNReal.ofReal (C * 2 ^ s) * ENNReal.ofReal (δ k) ^ (s - n) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (hδpos k).le (sub_pos.2 hs).le,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [Real.mul_rpow (by positivity) (hδpos k).le,
          show s - n = -n + s by ring, Real.rpow_add (hδpos k)]
        ring
  have hδlim : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hrad : Tendsto (fun k => ENNReal.ofReal (2 * δ k)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (hδlim.const_mul 2)
  have hbound : Tendsto
      (fun k => ENNReal.ofReal (C * 2 ^ s) * ENNReal.ofReal (δ k) ^ (s - n))
      atTop (𝓝 0) := by
    exact (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.ofReal_ne_top
      (sub_pos.2 hs)).comp
        (by simpa only [Function.comp_def, ENNReal.ofReal_zero] using
          ENNReal.continuous_ofReal.continuousAt.tendsto.comp hδlim)
  have hlim : Tendsto (fun k => ∑ y : F k, ediam (t k y) ^ s) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
      (fun _ => bot_le) hsum
  apply le_antisymm _ bot_le
  calc
    hausdorffMeasure s A ≤ liminf (fun k => ∑ y : F k, ediam (t k y) ^ s) atTop :=
      hausdorffMeasure_le_liminf_sum s A _ hrad t
        (Eventually.of_forall ht) (Eventually.of_forall hcover)
    _ = 0 := hlim.liminf_eq

end MeasureTheory.Measure

theorem dimH_le_of_polynomial_nets
    {X : Type*} [MetricSpace X] {A : Set X} {n C : ℝ}
    (hn : 0 ≤ n) (hC : 0 < C)
    (hnets : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ F : Finset X,
      (∀ x ∈ F, x ∈ A) ∧ (F.card : ℝ) ≤ C * δ ^ (-n) ∧
      ∀ x ∈ A, ∃ y ∈ F, dist x y ≤ δ) :
    dimH A ≤ ENNReal.ofReal n := by
  borelize X
  apply dimH_le
  intro d hd
  by_cases hdn : (d : ℝ) ≤ n
  · simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hdn
  · have hzero := MeasureTheory.Measure.hausdorffMeasure_zero_of_polynomial_nets
      hn hC hnets (lt_of_not_ge hdn)
    rw [hzero] at hd
    exact False.elim (ENNReal.zero_ne_top hd)

namespace MeasureTheory.Measure

theorem hausdorffMeasure_univ_zero_of_polynomial_nets
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {n C s : ℝ} (hn : 0 ≤ n) (hC : 0 < C)
    (hnets : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ F : Finset X,
      (F.card : ℝ) ≤ C * δ ^ (-n) ∧ ∀ x : X, ∃ y ∈ F, dist x y ≤ δ)
    (hs : n < s) : hausdorffMeasure s (univ : Set X) = 0 := by
  apply hausdorffMeasure_zero_of_polynomial_nets hn hC _ hs
  intro δ hδ hδ1
  obtain ⟨F, hcard, hcover⟩ := hnets δ hδ hδ1
  exact ⟨F, fun _ _ => mem_univ _, hcard, fun x _ => hcover x⟩

theorem hausdorffMeasure_zero_of_subtype_polynomial_nets
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {A : Set X} {n C s : ℝ} (hn : 0 ≤ n) (hC : 0 < C)
    (hnets : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ F : Finset A,
      (F.card : ℝ) ≤ C * δ ^ (-n) ∧ ∀ x : A, ∃ y ∈ F, dist x y ≤ δ)
    (hs : n < s) : hausdorffMeasure s A = 0 := by
  have hzero := hausdorffMeasure_univ_zero_of_polynomial_nets hn hC hnets hs
  have heq := (isometry_subtype_coe (s := A)).hausdorffMeasure_image
    (Or.inl (hn.trans hs.le)) (univ : Set A)
  simpa only [image_univ, Subtype.range_coe] using heq.trans hzero

theorem hausdorffMeasure_iUnion_zero_of_polynomial_nets
    {X ι : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Countable ι]
    (A : ι → Set X) {n s : ℝ} (hn : 0 ≤ n)
    (hnets : ∀ i, ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ F : Finset X,
        (∀ x ∈ F, x ∈ A i) ∧ (F.card : ℝ) ≤ C * δ ^ (-n) ∧
        ∀ x ∈ A i, ∃ y ∈ F, dist x y ≤ δ)
    (hs : n < s) : hausdorffMeasure s (⋃ i, A i) = 0 := by
  apply measure_iUnion_null
  intro i
  obtain ⟨C, hC, hi⟩ := hnets i
  exact hausdorffMeasure_zero_of_polynomial_nets hn hC hi hs

theorem hausdorffMeasure_iUnion_zero_of_subtype_zero
    {X ι : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Countable ι]
    (A : ι → Set X) {s : ℝ} (hs : 0 ≤ s)
    (hzero : ∀ i, hausdorffMeasure s (univ : Set (A i)) = 0) :
    hausdorffMeasure s (⋃ i, A i) = 0 := by
  apply measure_iUnion_null
  intro i
  have heq := (isometry_subtype_coe (s := A i)).hausdorffMeasure_image
    (Or.inl hs) (univ : Set (A i))
  simpa only [image_univ, Subtype.range_coe] using heq.trans (hzero i)

end MeasureTheory.Measure

theorem dimH_univ_le_of_polynomial_nets
    {X : Type*} [MetricSpace X] {n C : ℝ} (hn : 0 ≤ n) (hC : 0 < C)
    (hnets : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ F : Finset X,
      (F.card : ℝ) ≤ C * δ ^ (-n) ∧ ∀ x : X, ∃ y ∈ F, dist x y ≤ δ) :
    dimH (univ : Set X) ≤ ENNReal.ofReal n := by
  apply dimH_le_of_polynomial_nets hn hC
  intro δ hδ hδ1
  obtain ⟨F, hcard, hcover⟩ := hnets δ hδ hδ1
  exact ⟨F, fun _ _ => mem_univ _, hcard, fun x _ => hcover x⟩

theorem dimH_le_of_subtype_polynomial_nets
    {X : Type*} [MetricSpace X] {A : Set X} {n C : ℝ}
    (hn : 0 ≤ n) (hC : 0 < C)
    (hnets : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ F : Finset A,
      (F.card : ℝ) ≤ C * δ ^ (-n) ∧ ∀ x : A, ∃ y ∈ F, dist x y ≤ δ) :
    dimH A ≤ ENNReal.ofReal n := by
  have heq := (isometry_subtype_coe (s := A)).dimH_image (univ : Set A)
  simp only [image_univ, Subtype.range_coe] at heq
  exact heq.trans_le (dimH_univ_le_of_polynomial_nets hn hC hnets)

theorem dimH_iUnion_le_of_polynomial_nets
    {X ι : Type*} [MetricSpace X] [Countable ι]
    (A : ι → Set X) {n : ℝ} (hn : 0 ≤ n)
    (hnets : ∀ i, ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ F : Finset X,
        (∀ x ∈ F, x ∈ A i) ∧ (F.card : ℝ) ≤ C * δ ^ (-n) ∧
        ∀ x ∈ A i, ∃ y ∈ F, dist x y ≤ δ) :
    dimH (⋃ i, A i) ≤ ENNReal.ofReal n := by
  rw [dimH_iUnion]
  apply iSup_le
  intro i
  obtain ⟨C, hC, hi⟩ := hnets i
  exact dimH_le_of_polynomial_nets hn hC hi
