import DifferentialGeometry.Geometry.Metric.Approximation.EuclideanProductScale
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
One quality threshold rescales and recentres every original Euclidean-product splitting in a
bounded scale and displacement range. The choice precedes the rank, spaces, map and centre,
and its output retains every original coordinate with only the specified scalar and translation.
-/

set_option autoImplicit false

noncomputable section

namespace GC.MetricGeometry

universe u v

def rawScaleQuality (δ C : ℝ) : ℝ :=
  min (δ / 12) (1 / (2 * (C + 2 * δ⁻¹ + 2)))

theorem rawScaleQuality_pos {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) :
    0 < rawScaleQuality δ C := by
  unfold rawScaleQuality
  positivity

theorem rawScaleQuality_budgets {δ C ε c : ℝ} (hδ : 0 < δ) (hδone : δ < 1)
    (hC : 0 ≤ C) (hε : 0 < ε) (hεq : ε ≤ rawScaleQuality δ C)
    (hc : (1 / 2 : ℝ) ≤ c) (hc2 : c ≤ 2) :
    3 * c * ε ≤ δ ∧ C + δ⁻¹ / c + 2 * ε ≤ ε⁻¹ := by
  have hc0 : 0 < c := by linarith
  have heδ : ε ≤ δ / 12 := hεq.trans (min_le_left _ _)
  have hD : 0 < 2 * (C + 2 * δ⁻¹ + 2) := by positivity
  have heD : ε ≤ 1 / (2 * (C + 2 * δ⁻¹ + 2)) :=
    hεq.trans (min_le_right _ _)
  have hinv : 2 * (C + 2 * δ⁻¹ + 2) ≤ ε⁻¹ := by
    have hm : ε * (2 * (C + 2 * δ⁻¹ + 2)) ≤ 1 := (le_div_iff₀ hD).mp heD
    have hh : 2 * (C + 2 * δ⁻¹ + 2) ≤ 1 / ε :=
      (le_div_iff₀ hε).mpr (by nlinarith only [hm])
    simpa only [one_div] using hh
  have hci : δ⁻¹ / c ≤ 2 * δ⁻¹ := by
    apply (div_le_iff₀ hc0).mpr
    nlinarith [inv_pos.mpr hδ]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hc2 hε.le]
  · have he1 : ε ≤ 1 := by linarith
    linarith [inv_pos.mpr hδ]

theorem exists_uniform_rescaled_raw_splitting {δ C : ℝ}
    (hδ : 0 < δ) (hδone : δ < 1) (hC : 0 ≤ C) :
    ∃ η : ℝ, 0 < η ∧
      ∀ {X : Type u} {A : Type v} [mX : MetricSpace X] [mA : MetricSpace A]
        (k : ℕ) (p : X) (q : A) (a : X) {ε c : ℝ},
        (1 / 2 : ℝ) ≤ c → c ≤ 2 → dist a p ≤ C → ε ≤ η →
        ∀ f : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), q)) ε,
        ∃ hc : 0 < c,
        ∃ F : @KleinerLottApprox X (WithLp 2 (EuclideanSpace ℝ (Fin k) × A))
          (mX.rescale c hc) (MetricSpace.scaledProduct inferInstance mA c hc)
          a (WithLp.toLp 2 (0, (f.toFun a).snd)) δ,
          ∀ x, @KleinerLottApprox.toFun X (WithLp 2 (EuclideanSpace ℝ (Fin k) × A))
            (mX.rescale c hc) (MetricSpace.scaledProduct inferInstance mA c hc)
            a (WithLp.toLp 2 (0, (f.toFun a).snd)) δ F x = WithLp.toLp 2
              (c • ((f.toFun x).fst - (f.toFun a).fst), (f.toFun x).snd) := by
  refine ⟨rawScaleQuality δ C, rawScaleQuality_pos hδ hC, ?_⟩
  intro X A mX mA k p q a ε c hc hc2 ha hε f
  have hc0 : 0 < c := by linarith
  obtain ⟨hbudget, hdomain⟩ := rawScaleQuality_budgets hδ hδone hC f.error_pos hε hc hc2
  let F := f.recenterRescaleNormedProduct a hc0 hbudget hδone
    (by linarith only [ha, hdomain])
  exact ⟨hc0, F, fun x => f.recenterRescaleNormedProduct_apply a hc0 hbudget hδone
    (by linarith only [ha, hdomain]) x⟩

end GC.MetricGeometry
