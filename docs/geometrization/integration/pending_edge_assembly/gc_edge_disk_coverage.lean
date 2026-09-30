import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.L2Product
import DifferentialGeometry.Analysis.Calculus.Cutoff.EdgeNetworkProfiles
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false
open Set Metric DifferentialGeometry.Analysis
namespace GC.MetricGeometry

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

def edgeDiskDomain (p : X) (Δ : ℝ) (f : ball p (100 * Δ) → ℝ) (P ρ : X → ℝ) : Set X :=
  {x | ∃ hx : x ∈ ball p (100 * Δ), |f ⟨x, hx⟩| < 4 * Δ ∧ P x / ρ x ≤ 4 * Δ}

theorem ball_subset_edgeDiskDomain_and_cutoff_one {p : X} {q : Y} {Δ b μ : ℝ} {Λ : NNReal}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), q)) b)
    (hΔ : 1 ≤ Δ) (hb : b < 1 / 100) (hμ : μ ≤ 1 / 1000000)
    (hsource : 100 * Δ < b⁻¹)
    (ρ P : X → ℝ) (hρ : LipschitzWith Λ ρ) (hρpos : ∀ x, 0 < ρ x)
    (hρp : ρ p = 1) (hscale : Δ * (Λ : ℝ) ≤ 1 / 1000000)
    (A : Set X) (hpA : p ∈ A)
    (hP : ∀ x ∈ ball p (100 * Δ), |P x - infDist x A| ≤ μ * Δ)
    (f : ball p (100 * Δ) → ℝ)
    (hf : ∀ x, |f x - (F.toFun x.val).fst| ≤ μ * Δ) :
    let ζ := (Subtype.val : ball p (100 * Δ) → X).extend
      (fun x => edgeCoordinateProfile (f x / Δ) * edgeHeightProfile (P x.val / (Δ * ρ x.val))) 0
    ball p (3 * Δ) ⊆ edgeDiskDomain p Δ f P ρ ∧ EqOn ζ 1 (ball p (3 * Δ)) := by
  have hΔpos : 0 < Δ := by linarith only [hΔ]
  have hμΔ : μ * Δ ≤ Δ / 1000000 := by
    nlinarith only [mul_le_mul_of_nonneg_right hμ hΔpos.le]
  have bounds (x : X) (hx : x ∈ ball p (3 * Δ)) :
      ∃ hxD : x ∈ ball p (100 * Δ),
        |f ⟨x, hxD⟩| < 31 / 10 * Δ ∧ P x / ρ x < 31 / 10 * Δ := by
    have hxD : x ∈ ball p (100 * Δ) :=
      (show dist x p < 3 * Δ from hx).trans (by linarith only [hΔpos])
    have hxF : x ∈ ball p b⁻¹ := hxD.trans hsource
    have hu : |(F.toFun x).fst| ≤ dist x p + b := by
      have hd := (abs_le.mp (F.radial_error x hxF)).2
      have hh := WithLp.dist_fst_le (F.toFun x) (WithLp.toLp 2 ((0 : ℝ), q))
      change dist (F.toFun x).fst (0 : ℝ) ≤ _ at hh
      rw [Real.dist_eq, sub_zero] at hh
      linarith only [hd, hh]
    have hfbound : |f ⟨x, hxD⟩| < 31 / 10 * Δ := by
      have hh : |f ⟨x, hxD⟩| ≤ |f ⟨x, hxD⟩ - (F.toFun x).fst| + |(F.toFun x).fst| := by
        calc
          _ = |(f ⟨x, hxD⟩ - (F.toFun x).fst) + (F.toFun x).fst| := by rw [sub_add_cancel]
          _ ≤ _ := abs_add_le _ _
      have he := hf ⟨x, hxD⟩
      change dist x p < 3 * Δ at hx
      linarith only [hh, he, hu, hx, hμΔ, hb, hΔ]
    have hrho : 99 / 100 < ρ x := by
      have hh := hρ.dist_le_mul x p
      rw [Real.dist_eq, hρp] at hh
      have hd := mul_le_mul_of_nonneg_left (show dist x p ≤ 3 * Δ from hx.le) Λ.coe_nonneg
      nlinarith only [(abs_le.mp hh).1, hd, hscale]
    have hPbound : P x / ρ x < 31 / 10 * Δ := by
      apply (div_lt_iff₀ (hρpos x)).mpr
      have hi : infDist x A ≤ dist x p := infDist_le_dist_of_mem hpA
      have he := (abs_le.mp (hP x hxD)).2
      have hr := mul_lt_mul_of_pos_left hrho (show 0 < 31 / 10 * Δ by positivity)
      change dist x p < 3 * Δ at hx
      nlinarith only [hi, he, hr, hx, hμΔ, hΔpos]
    exact ⟨hxD, hfbound, hPbound⟩
  constructor
  · intro x hx
    obtain ⟨hxD, hfbound, hPbound⟩ := bounds x hx
    exact ⟨hxD, hfbound.trans (by linarith only [hΔpos]),
      hPbound.le.trans (by linarith only [hΔpos])⟩
  · intro x hx
    obtain ⟨hxD, hfbound, hPbound⟩ := bounds x hx
    have harg : f ⟨x, hxD⟩ / Δ ∈ Icc (-8 : ℝ) 8 := by
      constructor
      · apply (le_div_iff₀ hΔpos).mpr
        linarith only [(abs_lt.mp hfbound).1, hΔpos]
      · apply (div_le_iff₀ hΔpos).mpr
        linarith only [(abs_lt.mp hfbound).2, hΔpos]
    have hheight : P x / (Δ * ρ x) ≤ 8 := by
      rw [mul_comm Δ, ← div_div]
      apply (div_le_iff₀ hΔpos).mpr
      linarith only [hPbound, hΔpos]
    have heval := Subtype.val_injective.extend_apply
      (fun y : ball p (100 * Δ) => edgeCoordinateProfile (f y / Δ) *
        edgeHeightProfile (P y.val / (Δ * ρ y.val))) (0 : X → ℝ) ⟨x, hxD⟩
    change ((Subtype.val : ball p (100 * Δ) → X).extend _ (0 : X → ℝ)) x = 1
    rw [heval, (edgeProfiles_plateaus.1 harg),
      show edgeHeightProfile (P x / (Δ * ρ x)) = 1 from
        descendingIntervalProfile_one (by norm_num) hheight, mul_one]

end GC.MetricGeometry
