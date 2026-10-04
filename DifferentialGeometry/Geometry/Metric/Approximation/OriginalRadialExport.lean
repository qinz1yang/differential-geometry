import DifferentialGeometry.Geometry.Metric.Approximation.OriginalRadialSplitting
import DifferentialGeometry.Geometry.Metric.Approximation.ZeroStratumSmallCoreCover
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleComposition

/-!
# The original radial splitting on selected closed shells

This is the splitting clause of LC80 item 3, with the original selected center and scale.
The output uses ρ(q)⁻¹ times the original distance, with its exact centered radial coordinate.
-/

set_option autoImplicit false

open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace GC.MetricGeometry

universe u v

theorem original_radial_selected_shell_export {n : ℕ} (hn : 1 ≤ n)
    {β : ℝ} (hβ : 0 < β) (hβone : β < 1) :
    ∃ δstar Λstar : ℝ, 0 < δstar ∧ 0 < Λstar ∧
      ∀ (X : Type u) [m : MetricSpace X] [CompleteSpace X],
      (∀ x y : X, ∃ c : Icc (0 : ℝ) 1 → X,
        Continuous c ∧ c ⟨0, by norm_num⟩ = x ∧ c ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (c s) (c t) = dist x y * dist s t) →
      dimH (univ : Set X) ≤ n →
      ∀ (C : X → Type v) [∀ i, MetricSpace (C i)] (o : ∀ i, C i)
        (r ρ : X → ℝ) (hr : ∀ i, 0 < r i) (hρ : ∀ q, 0 < ρ q) (J : Set X),
      (∀ i ∈ J, Nonempty (RadialConeData (o i))) →
      (∀ i ∈ J, fourPointComparison ((1 / 60) ^ 2 * (r i)⁻¹ ^ 2)
        (ball i (21 * r i))) →
      (∀ i ∈ J, ∃ δ : ℝ, δ < δstar ∧ Nonempty (@KleinerLottApprox X (C i)
        (m.rescale (r i)⁻¹ (inv_pos.mpr (hr i))) inferInstance i (o i) δ)) →
      (∀ i ∈ J, ∀ q : X, dist i q ≤ 10 * r i → Λstar ≤ r i / ρ q) →
      ∀ i ∈ J, ∀ q : X, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
      ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
        ∃ (z : Z) (F : @KleinerLottApprox X
          (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
          (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
          q (WithLp.toLp 2 (0, z)) β),
          ∀ x : X, (@KleinerLottApprox.toFun X
            (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
            (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q))) inferInstance
            q (WithLp.toLp 2 (0, z)) β F x).fst = WithLp.toLp 2
            (Function.const (Fin 1) ((ρ q)⁻¹ * (dist i x - dist i q))) := by
  obtain ⟨δstar, Λstar, hδstar, hΛstar, hproduce⟩ :=
    exists_original_radial_splitting_parameter.{u, v} hn hβ hβone
  refine ⟨δstar, Λstar, hδstar, hΛstar, ?_⟩
  intro X m hcomplete hsegments hdim C mC o r ρ hr hρ J hcones hcomparison hmodels hscales
    i hi q hqlo hqhi
  obtain ⟨H⟩ := hcones i hi
  obtain ⟨δ, hδ, ⟨F⟩⟩ := hmodels i hi
  have hri : 0 < (r i)⁻¹ := inv_pos.mpr (hr i)
  have hlam : 0 < r i / ρ q := div_pos (hr i) (hρ q)
  have hcomplete' : @CompleteSpace X (m.rescale (r i)⁻¹ hri).toUniformSpace :=
    (MetricSpace.rescale_completeSpace_iff m (r i)⁻¹ hri).mpr hcomplete
  have hdim' : @dimH X (m.rescale (r i)⁻¹ hri).toEMetricSpace univ ≤ n := by
    rw [MetricSpace.rescale_dimH]; exact hdim
  have hcomp : @fourPointComparison X (m.rescale (r i)⁻¹ hri) ((1 / 60) ^ 2)
      (@ball X (m.rescale (r i)⁻¹ hri).toPseudoMetricSpace i 21) := by
    have hb := MetricSpace.rescale_ball m (r i)⁻¹ hri i (21 * r i)
    have hc : (r i)⁻¹ * (21 * r i) = 21 := by field_simp [(hr i).ne']
    rw [hc] at hb
    rw [hb, fourPointComparison_rescale_iff (m := m) hri (by positivity)]
    exact hcomparison i hi
  have hlo : 1 / 10 ≤ @dist X (m.rescale (r i)⁻¹ hri).toDist i q := by
    rw [MetricSpace.rescale_dist, le_inv_mul_iff₀ (hr i)]
    linarith only [hqlo]
  have hhi : @dist X (m.rescale (r i)⁻¹ hri).toDist i q ≤ 10 := by
    rw [MetricSpace.rescale_dist, inv_mul_le_iff₀ (hr i)]
    simpa only [mul_comm (r i)] using hqhi
  have hpack := @hproduce X (m.rescale (r i)⁻¹ hri) hcomplete'
    (rescale_segments m hri hsegments) hdim' (C i) (mC i) i (o i) H δ F hδ hcomp q hlo hhi
    (r i / ρ q) hlam (hscales i hi q hqhi)
  have heq : (m.rescale (r i)⁻¹ hri).rescale (r i / ρ q) hlam =
      m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρ q)) := by
    rw [MetricSpace.rescale_mul]
    congr 1
    field_simp [(hr i).ne', (hρ q).ne']
  have hcoord (x : X) : (r i / ρ q) *
      (@dist X (m.rescale (r i)⁻¹ hri).toDist i x -
        @dist X (m.rescale (r i)⁻¹ hri).toDist i q) =
      (ρ q)⁻¹ * (dist i x - dist i q) := by
    simp only [MetricSpace.rescale_dist]
    field_simp [(hr i).ne', (hρ q).ne']
  simp only [hcoord] at hpack
  rw [heq] at hpack
  exact hpack

end GC.MetricGeometry
