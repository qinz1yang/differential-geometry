import DifferentialGeometry.Geometry.Comparison.MaximalPairedChart
import DifferentialGeometry.Geometry.Comparison.PairedChartDistortion

set_option autoImplicit false

open Set Metric Real
open scoped Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [Nontrivial X]

theorem exists_centered_distance_chart_in_open_set
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω O : Set X} (hcomp : fourPointComparison 1 Ω) (hOΩ : O ⊆ Ω)
    (hO : IsOpen O) (hOne : O.Nonempty)
    (hcomplete : ∀ z ∈ Ω, ∃ R : ℝ, 0 < R ∧ IsComplete (closedBall z R))
    {n : ℕ} (hn : 1 ≤ n) (hdim : dimH Ω ≤ n) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ ∃ q ∈ O, ∃ a : Fin m → X, range a ⊆ Ω ∧
      ∃ r : ℝ, ∃ hr : 0 < r, ball q r ⊆ O ∧
      ∃ U : Set (PiLp 2 (fun _ : Fin m => ℝ)), IsOpen U ∧
      ∃ e : ball q r ≃ₜ U,
        (∀ z, (e z : PiLp 2 (fun _ : Fin m => ℝ)) =
          distanceCoordinates 2 a (z : X) - distanceCoordinates 2 a q) ∧
        (e ⟨q, mem_ball_self hr⟩ : PiLp 2 (fun _ : Fin m => ℝ)) = 0 ∧
        (∀ x y, (pairedChartDistortion n)⁻¹ * dist x y ≤ dist (e x) (e y)) ∧
        (∀ x y, dist (e x) (e y) ≤ pairedChartDistortion n * dist x y) := by
  obtain ⟨m, hm1, hmn, q, hq, a, ha, r, hr, hBO, U, hU, e, he, hlo, hLip⟩ :=
    exists_distance_chart_in_open_set hcurves hcomp hOΩ hO hOne hcomplete hn hdim
  let F : ball q r → PiLp 2 (fun _ : Fin m => ℝ) := fun z =>
    distanceCoordinates 2 a (z : X) - distanceCoordinates 2 a q
  have hdist (x y : ball q r) : dist (F x) (F y) = dist (e x) (e y) := by
    change dist (distanceCoordinates 2 a (x : X) - distanceCoordinates 2 a q)
      (distanceCoordinates 2 a (y : X) - distanceCoordinates 2 a q) =
      dist (e x : PiLp 2 (fun _ : Fin m => ℝ)) (e y : PiLp 2 (fun _ : Fin m => ℝ))
    rw [dist_sub_right, he, he]
  let L : ℝ≥0 := ⟨pairedChartDistortion n, (pairedChartDistortion_pos n).le⟩
  have hL : 0 < L := pairedChartDistortion_pos n
  have hlow (x y : ball q r) : ((L⁻¹ : ℝ≥0) : ℝ) * dist x y ≤ dist (F x) (F y) := by
    rw [hdist]
    exact (mul_le_mul_of_nonneg_right (inverse_pairedChartDistortion_le_quality (n := n)
      (show 1 ≤ m + 1 by omega)) dist_nonneg).trans (hlo x y)
  have hFLip : LipschitzWith L F := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [hdist]
    exact (hLip.dist_le_mul x y).trans (mul_le_mul_of_nonneg_right
      (show (NNReal.sqrt m : ℝ) ≤ pairedChartDistortion n by
        simpa using sqrt_le_pairedChartDistortion hmn)
      dist_nonneg)
  have hopen : IsOpenMap F := by
    have h := (Homeomorph.subRight (distanceCoordinates 2 a q)).isOpenMap.comp
      (hU.isOpenMap_subtype_val.comp e.isOpenMap)
    convert h using 1
    funext z
    exact congrArg (fun w => w - distanceCoordinates 2 a q) (he z).symm
  obtain ⟨f, hf, hfLip, _⟩ := exists_homeomorph_range_of_lipschitz_lower_bound hFLip
    (inv_pos.mpr hL) hlow
  refine ⟨m, hm1, hmn, q, hq, a, ha, r, hr, hBO, range F, hopen.isOpen_range, f, hf, ?_, ?_, ?_⟩
  · rw [hf]
    exact sub_self _
  · intro x y
    change (pairedChartDistortion n)⁻¹ * dist x y ≤ dist (f x : PiLp 2 (fun _ : Fin m => ℝ)) (f y : PiLp 2 (fun _ : Fin m => ℝ))
    rw [hf, hf]
    exact hlow x y
  · intro x y
    exact hfLip.dist_le_mul x y

end DifferentialGeometry.Geometry.Comparison.Toponogov
