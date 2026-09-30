import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false

open Set Metric
open scoped NNReal ENNReal

namespace MeasureTheory

noncomputable def euclideanHausdorffFactor (n : ℕ) : ℝ≥0 :=
  Measure.addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin n)))
    μH[Module.finrank ℝ (EuclideanSpace ℝ (Fin n))]

theorem euclideanHausdorffFactor_pos (n : ℕ) : 0 < euclideanHausdorffFactor n :=
  Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

noncomputable def normalizedHausdorffMeasure (n : ℕ) {X : Type*}
    [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] : Measure X :=
  euclideanHausdorffFactor n • μH[n]

@[simp] theorem normalizedHausdorffMeasure_euclidean (n : ℕ) :
    (normalizedHausdorffMeasure n : Measure (EuclideanSpace ℝ (Fin n))) = volume := by
  have h := Measure.isAddLeftInvariant_eq_smul
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (μH[Module.finrank ℝ (EuclideanSpace ℝ (Fin n))])
  simpa only [normalizedHausdorffMeasure, euclideanHausdorffFactor,
    finrank_euclideanSpace, Fintype.card_fin] using h.symm

theorem normalizedHausdorffMeasure_image_le
    {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {K : ℝ≥0} {f : X → Y} {s : Set X} (hf : LipschitzOnWith K f s) (n : ℕ) :
    normalizedHausdorffMeasure n (f '' s) ≤ (K : ℝ≥0∞) ^ n * normalizedHausdorffMeasure n s := by
  have h := hf.hausdorffMeasure_image_le (show (0 : ℝ) ≤ n by positivity)
  simp only [ENNReal.rpow_natCast] at h
  simp only [normalizedHausdorffMeasure, Measure.smul_apply]
  exact (mul_le_mul_right h _).trans_eq (mul_left_comm _ _ _)

theorem volume_euclidean_coordinate_cube (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    volume {w : EuclideanSpace ℝ (Fin n) | ∀ j, |w j - v j| ≤ r} =
      ENNReal.ofReal (2 * r) ^ n := by
  let S : Set (Fin n → ℝ) := Icc (fun j => v j - r) (fun j => v j + r)
  have hset : {w : EuclideanSpace ℝ (Fin n) | ∀ j, |w j - v j| ≤ r} = WithLp.ofLp ⁻¹' S := by
    ext w
    simp only [mem_ofPred_eq, mem_preimage, S, mem_Icc, Pi.le_def]
    constructor
    · intro h
      exact ⟨fun j => by linarith [(abs_le.mp (h j)).1],
        fun j => by linarith [(abs_le.mp (h j)).2]⟩
    · rintro ⟨hlo, hhi⟩ j
      exact abs_le.mpr ⟨by linarith [hlo j], by linarith [hhi j]⟩
  have hS : MeasurableSet S := measurableSet_Icc
  rw [hset, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage hS.nullMeasurableSet,
    Real.volume_Icc_pi]
  have heq (j : Fin n) : (v j + r) - (v j - r) = 2 * r := by ring
  simp only [heq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end MeasureTheory
