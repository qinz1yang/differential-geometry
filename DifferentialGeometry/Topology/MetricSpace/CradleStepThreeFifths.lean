import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Tactic.Linarith

set_option autoImplicit false


open Set Metric

namespace Metric

theorem exists_cradle_step_on_segment_three_fifths {X : Type*} [MetricSpace X]
    {x u v : X} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hshort : dist x u ≤ dist x v)
    (hlower : 3 * ℓ / 5 ≤ dist x u + dist x v)
    (hupper : dist x u + dist x v < ℓ)
    (γ : Icc (0 : ℝ) (dist x v) → X) (hγ : Isometry γ)
    (hγ0 : γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x)
    (hγv : γ ⟨dist x v, ⟨dist_nonneg, le_rfl⟩⟩ = v) :
    let h := (3 * ℓ / 5 - dist x u) / 3
    ∃ x' ∈ range γ, dist x x' = h ∧ dist x' v = dist x v - h ∧
      ℓ / 30 < h ∧ h ≤ ℓ / 5 ∧ h < dist x v ∧
      dist x u + h < 3 * ℓ / 5 ∧ dist x' u + h < 3 * ℓ / 5 ∧
      dist x' u + dist x' v ≤ dist x u + dist x v ∧
      x' ∈ ball u ℓ ∩ ball v ℓ := by
  dsimp only
  let h := (3 * ℓ / 5 - dist x u) / 3
  have ha : 0 ≤ dist x u := dist_nonneg
  have hb : 0 ≤ dist x v := dist_nonneg
  have hhlo : ℓ / 30 < h := by dsimp only [h]; linarith
  have hhhi : h ≤ ℓ / 5 := by dsimp only [h]; linarith
  have hhpos : 0 < h := (by positivity : (0 : ℝ) < ℓ / 30).trans hhlo
  have hhless : h < dist x v := by dsimp only [h]; linarith
  let t : Icc (0 : ℝ) (dist x v) := ⟨h, hhpos.le, hhless.le⟩
  let x' := γ t
  have hxx' : dist x x' = h := by
    have he := hγ.dist_eq (⟨0, ⟨le_rfl, hb⟩⟩ : Icc (0 : ℝ) (dist x v)) t
    rw [hγ0] at he
    simpa only [t, x', Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hhpos] using he
  have hx'v : dist x' v = dist x v - h := by
    have he := hγ.dist_eq t (⟨dist x v, ⟨hb, le_rfl⟩⟩ : Icc (0 : ℝ) (dist x v))
    rw [hγv] at he
    change dist x' v = |h - dist x v| at he
    rw [abs_of_neg (sub_neg.mpr hhless)] at he
    linarith
  have hcx : dist x' u ≤ dist x u + h := by
    have ht := dist_triangle x' x u
    rw [dist_comm x' x, hxx'] at ht
    linarith
  have hshort₁ : dist x u + h < 3 * ℓ / 5 := by dsimp only [h]; linarith
  have hshort₂ : dist x' u + h < 3 * ℓ / 5 := by
    have harith : dist x u + 2 * h < 3 * ℓ / 5 := by dsimp only [h]; linarith
    linarith
  refine ⟨x', ⟨t, rfl⟩, hxx', hx'v, hhlo, hhhi, hhless, hshort₁, hshort₂, ?_, ?_⟩
  · rw [hx'v]
    linarith
  · constructor
    · change dist x' u < ℓ
      linarith
    · change dist x' v < ℓ
      rw [hx'v]
      linarith


end Metric
