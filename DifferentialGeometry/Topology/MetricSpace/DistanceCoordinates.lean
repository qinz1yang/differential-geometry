import Mathlib.Analysis.Normed.Lp.PiLp
import DifferentialGeometry.Analysis.NormedSpace.OpenImageDimension

set_option autoImplicit false

open Set
open scoped ENNReal NNReal

namespace Metric

variable {X ι : Type*} [MetricSpace X]

noncomputable def distanceCoordinates (p : ℝ≥0∞) (a : ι → X) (x : X) :
    PiLp p (fun _ : ι => ℝ) := WithLp.toLp p (fun i => dist x (a i))

@[simp] theorem distanceCoordinates_apply (p : ℝ≥0∞) (a : ι → X) (x : X) (i : ι) :
    distanceCoordinates p a x i = dist x (a i) := rfl

variable [Fintype ι]

theorem lipschitzWith_distanceCoordinates (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ι → X) :
    LipschitzWith ((Fintype.card ι : ℝ≥0) ^ (1 / p).toReal) (distanceCoordinates p a) := by
  have h : LipschitzWith 1 (fun x : X => fun i => dist x (a i)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul]
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    simpa using dist_dist_dist_le x (a i) y (a i)
  change LipschitzWith _ (WithLp.toLp p ∘ (fun x : X => fun i => dist x (a i)))
  simpa only [mul_one] using (PiLp.lipschitzWith_toLp p (fun _ : ι => ℝ)).comp h

theorem lipschitzWith_distanceCoordinates_one (a : ι → X) :
    LipschitzWith (Fintype.card ι) (distanceCoordinates 1 a) := by
  simpa using lipschitzWith_distanceCoordinates 1 a

theorem lipschitzWith_distanceCoordinates_two (a : ι → X) :
    LipschitzWith (NNReal.sqrt (Fintype.card ι)) (distanceCoordinates 2 a) := by
  simpa [NNReal.sqrt_eq_rpow, ENNReal.toReal_div] using lipschitzWith_distanceCoordinates 2 a

end Metric

namespace Metric

variable {X ι : Type*} [MetricSpace X] [Fintype ι]

theorem card_le_dimH_of_distanceCoordinates_image_has_interior
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ι → X) {s : Set X}
    (himage : (interior (distanceCoordinates p a '' s)).Nonempty) :
    (Fintype.card ι : ℝ≥0∞) ≤ dimH s := by
  have hfin : Module.finrank ℝ (PiLp p (fun _ : ι => ℝ)) = Fintype.card ι :=
    (WithLp.linearEquiv p ℝ (ι → ℝ)).finrank_eq.trans (Module.finrank_pi ℝ)
  simpa only [hfin] using (lipschitzWith_distanceCoordinates p a).lipschitzOnWith.finrank_le_dimH_of_image_has_interior himage

theorem card_le_of_distanceCoordinates_image_contains_ball
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ι → X) {s : Set X}
    {y : PiLp p (fun _ : ι => ℝ)} {r : ℝ} {n : ℕ}
    (hr : 0 < r) (hball : ball y r ⊆ distanceCoordinates p a '' s)
    (hdim : dimH s ≤ n) : Fintype.card ι ≤ n := by
  have hfin : Module.finrank ℝ (PiLp p (fun _ : ι => ℝ)) = Fintype.card ι :=
    (WithLp.linearEquiv p ℝ (ι → ℝ)).finrank_eq.trans (Module.finrank_pi ℝ)
  simpa only [hfin] using (lipschitzWith_distanceCoordinates p a).lipschitzOnWith.finrank_le_of_image_contains_ball hr hball hdim

end Metric
