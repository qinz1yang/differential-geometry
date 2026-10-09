import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-!
A cross with a deleted horizontal gap gives explicit cloud data at every positive threshold.
The complex plane carries its Euclidean real Hilbert norm, with its canonical orthonormal
coordinate identification recording the ordinary real plane without a change of metric.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace GC.MetricGeometry.CloudCounterexample

def crossHeight (δ : ℝ) : ℝ := min (δ / 10) (1 / 100)
def crossSmall (δ : ℝ) : ℝ := δ * crossHeight δ / (100 * (1 + δ))
def crossExtent (δ : ℝ) : ℝ := 2 + δ⁻¹
def crossPoint : ℂ := (3 / 4 : ℝ)
def crossCentres : Set ℂ := {0, crossPoint}
def crossSet (δ : ℝ) : Set ℂ :=
  Complex.ofReal '' Icc (-crossExtent δ) (3 / 4 - crossHeight δ) ∪
    Complex.ofReal '' Icc (3 / 4 + crossHeight δ) (crossExtent δ) ∪
      (fun t : ℝ => crossPoint + t * Complex.I) '' Icc (-crossHeight δ) (crossHeight δ)
def crossRadius (δ : ℝ) (z : ℂ) : ℝ := max (crossSmall δ) (1 - 2 * ‖z‖)
def horizontalLine : Submodule ℝ ℂ := Submodule.span ℝ {(1 : ℂ)}
def verticalLine : Submodule ℝ ℂ := Submodule.span ℝ {Complex.I}
def crossPlane (x : crossCentres) : Submodule ℝ ℂ :=
  if (x : ℂ) = 0 then horizontalLine else verticalLine
noncomputable def horizontalNormal : ℂ →L[ℝ] ℂ := horizontalLineᗮ.starProjection
noncomputable def verticalNormal : ℂ →L[ℝ] ℂ := verticalLineᗮ.starProjection
noncomputable def realPlaneIso : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr

theorem cross_parameters {δ : ℝ} (hδ : 0 < δ) :
    0 < crossHeight δ ∧ crossHeight δ ≤ δ / 10 ∧ crossHeight δ ≤ 1 / 100 ∧
      0 < crossSmall δ ∧ crossSmall δ < 1 / 10000 ∧ crossSmall δ / δ < crossHeight δ ∧
      0 < crossExtent δ ∧ crossHeight δ < 3 / 4 ∧ 3 / 4 + crossHeight δ < crossExtent δ := by
  have hh : 0 < crossHeight δ := lt_min (by positivity) (by norm_num)
  have hhδ : crossHeight δ ≤ δ / 10 := min_le_left _ _
  have hh1 : crossHeight δ ≤ 1 / 100 := min_le_right _ _
  have hden : 0 < 100 * (1 + δ) := by positivity
  have hs : 0 < crossSmall δ := div_pos (mul_pos hδ hh) hden
  have hslt : crossSmall δ < crossHeight δ / 100 := by
    dsimp only [crossSmall]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hratio : crossSmall δ / δ = crossHeight δ / (100 * (1 + δ)) := by
    dsimp only [crossSmall]
    field_simp
  refine ⟨hh, hhδ, hh1, hs, by linarith, ?_, ?_, by linarith, ?_⟩
  · rw [hratio]
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  · dsimp only [crossExtent]
    positivity
  · have hi : 0 < δ⁻¹ := inv_pos.mpr hδ
    dsimp only [crossExtent]
    linarith

theorem crossSet_compact (δ : ℝ) : IsCompact (crossSet δ) := by
  apply IsCompact.union
  · exact (isCompact_Icc.image Complex.continuous_ofReal).union
      (isCompact_Icc.image Complex.continuous_ofReal)
  · exact isCompact_Icc.image
      (continuous_const.add (Complex.continuous_ofReal.mul_const Complex.I))

theorem crossCentres_subset {δ : ℝ} (hδ : 0 < δ) : crossCentres ⊆ crossSet δ := by
  intro z hz
  simp only [crossCentres, mem_insert_iff, mem_singleton_iff] at hz
  rcases hz with hz | hz
  · subst z
    refine Or.inl (Or.inl ⟨0, ?_, by simp⟩)
    have h := cross_parameters hδ
    exact ⟨by linarith [h.2.2.2.2.2.2.1], by linarith [h.2.2.2.2.2.2.2.1]⟩
  · subst z
    refine Or.inr ⟨0, ?_, by simp⟩
    have hh := (cross_parameters hδ).1
    exact ⟨by linarith, hh.le⟩

theorem crossRadius_bounds {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    crossSmall δ ≤ crossRadius δ z ∧ crossRadius δ z ≤ 1 := by
  refine ⟨le_max_left _ _, max_le ?_ ?_⟩
  · linarith [(cross_parameters hδ).2.2.2.2.1]
  · nlinarith [norm_nonneg z]

theorem crossRadius_lipschitz (δ : ℝ) : LipschitzWith 2 (crossRadius δ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have hmax := abs_max_sub_max_le_max (crossSmall δ) (1 - 2 * ‖x‖)
    (crossSmall δ) (1 - 2 * ‖y‖)
  have heq : (1 - 2 * ‖x‖) - (1 - 2 * ‖y‖) = -2 * (‖x‖ - ‖y‖) := by ring
  have hnorm := abs_norm_sub_norm_le x y
  have hb : |max (crossSmall δ) (1 - 2 * ‖x‖) -
      max (crossSmall δ) (1 - 2 * ‖y‖)| ≤ 2 * ‖x - y‖ := by
    calc
      _ ≤ |(1 - 2 * ‖x‖) - (1 - 2 * ‖y‖)| := by simpa using hmax
      _ = 2 * |‖x‖ - ‖y‖| := by rw [heq, abs_mul]; norm_num
      _ ≤ 2 * ‖x - y‖ := mul_le_mul_of_nonneg_left hnorm (by norm_num)
  simpa only [crossRadius, NNReal.coe_ofNat, dist_eq_norm] using hb

theorem crossRadius_zero {δ : ℝ} (hδ : 0 < δ) : crossRadius δ 0 = 1 := by
  have hs := (crossRadius_bounds hδ (0 : ℂ)).2
  simp only [crossRadius, norm_zero, mul_zero, sub_zero] at hs ⊢
  exact max_eq_right (le_trans (le_max_left _ _) hs)

theorem crossRadius_point {δ : ℝ} (hδ : 0 < δ) :
    crossRadius δ crossPoint = crossSmall δ := by
  have hs := (cross_parameters hδ).2.2.2.1
  have hn : ‖crossPoint‖ = (3 / 4 : ℝ) := by
    norm_num [crossPoint, Complex.norm_real]
  rw [crossRadius, hn]
  exact max_eq_left (by linarith)

theorem cross_radius_inequality {δ : ℝ} (hδ : 0 < δ) (x y : ℂ) :
    |crossRadius δ y - crossRadius δ x| ≤ 2 * (dist x y + crossRadius δ x) := by
  have h := (crossRadius_lipschitz δ).dist_le_mul y x
  rw [Real.dist_eq, dist_comm y x] at h
  have hr := (cross_parameters hδ).2.2.2.1.trans_le (crossRadius_bounds hδ x).1
  change |crossRadius δ y - crossRadius δ x| ≤ (2 : ℝ) * dist x y at h
  linarith

theorem mem_horizontalLine {z : ℂ} : z ∈ horizontalLine ↔ z.im = 0 := by
  rw [horizontalLine, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    rw [← ha]
    simp
  · intro hz
    refine ⟨z.re, ?_⟩
    apply Complex.ext <;> simp [hz]

theorem mem_verticalLine {z : ℂ} : z ∈ verticalLine ↔ z.re = 0 := by
  rw [verticalLine, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    rw [← ha]
    simp
  · intro hz
    refine ⟨z.im, ?_⟩
    apply Complex.ext <;> simp [hz]

theorem crossPlane_finrank (x : crossCentres) : Module.finrank ℝ (crossPlane x) = 1 := by
  by_cases hx : (x : ℂ) = 0
  · rw [crossPlane, ite_eq_left hx]
    exact finrank_span_singleton (by norm_num : (1 : ℂ) ≠ 0)
  · rw [crossPlane, ite_eq_right hx]
    exact finrank_span_singleton Complex.I_ne_zero

theorem cross_packet_bounds {δ : ℝ} (hδ : 0 < δ) :
    IsCompact (crossSet δ) ∧ crossCentres ⊆ crossSet δ ∧
      0 < crossSmall δ ∧ crossSmall δ < 1 / 10000 ∧
      (∀ z : ℂ, crossSmall δ ≤ crossRadius δ z ∧ crossRadius δ z ≤ 1) ∧
      LipschitzWith 2 (crossRadius δ) ∧ crossRadius δ 0 = 1 ∧
      crossRadius δ crossPoint = crossSmall δ ∧
      ∀ x ∈ crossSet δ, ∀ y ∈ crossSet δ,
        |crossRadius δ y - crossRadius δ x| ≤ 2 * (dist x y + crossRadius δ x) := by
  have h := cross_parameters hδ
  exact ⟨crossSet_compact δ, crossCentres_subset hδ, h.2.2.2.1, h.2.2.2.2.1,
    crossRadius_bounds hδ, crossRadius_lipschitz δ, crossRadius_zero hδ,
    crossRadius_point hδ, fun x hx y hy => cross_radius_inequality hδ x y⟩

end GC.MetricGeometry.CloudCounterexample
