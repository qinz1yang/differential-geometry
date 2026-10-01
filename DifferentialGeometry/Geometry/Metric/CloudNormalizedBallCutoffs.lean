import DifferentialGeometry.Analysis.Calculus.Cutoff.LocalizedNormalizedBallCutoffs
import DifferentialGeometry.Geometry.Metric.AffineScaleCover
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff

namespace GC.MetricGeometry
universe u

theorem exists_uniform_cloud_normalized_ballCutoff_bounds
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        (S T : Set H), S ⊆ T → TotallyBounded S → ∀ (r : H → ℝ)
        (P : S → Submodule ℝ H) [∀ x : S, FiniteDimensional ℝ (P x)],
        (∀ x : S, Module.finrank ℝ (P x) ≤ k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ (1 / (100 * (C + 1))) / (2 * (2 * (C + 1))) →
        (∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x)) →
        (∀ x : S, hausdorffEDist (T ∩ ball (x : H) (r x / δ))
          ((AffineSubspace.mk' (x : H) (P x) : Set H) ∩ ball (x : H) (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        let ℓ : ℝ := 1 / (100 * (C + 1))
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (ℓ * r i)) ∧
          ((⋃ x ∈ S, ball x (ℓ * r x)) ⊆ ⋃ i ∈ I, ball i (5 * ℓ * r i)) ∧
          ∀ m : ℕ, ∀ x₀ ∈ I, ∀ v ∈ ball x₀ (5 * ℓ * r x₀),
            ∀ j ≤ m, ∀ z ∈ ball v (ℓ * r x₀),
              (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ j
                (fun y => ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
                  (∑ a ∈ hI.toFinset,
                    ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)) z‖) ≤
                      B m / (r x₀) ^ j := by
  classical
  let ℓ : ℝ := 1 / (100 * (C + 1))
  let A : ℝ := 2 * (C + 1)
  let D : ℝ := 20 * A + 6
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  let N : ℕ := ⌈(1 + 2 * A * D) ^ k⌉₊
  let Λ : ℝ≥0 := ⟨A / (10 * ℓ), by positivity⟩
  choose B hB hbound using fun m : ℕ =>
    exists_bound_iteratedFDeriv_normalized_ballCutoffs_of_active_card_le.{u,u} m N Λ
  refine ⟨B, hB, ?_⟩
  intro H _ _ S T hST hS r P _ hdim rmin R δ hrmin hlower hupper hδ hδsmall hscale hcloud
  obtain ⟨I, hIS, hI, hdisj, hcover, hcount⟩ :=
    GC.MetricGeometry.exists_finite_disjoint_scale_cover_of_hausdorffEDist_le
      S T hST hS r P hrmin hlower hupper hC hδ hδsmall hscale hcloud
  refine ⟨I, hI, hIS, hdisj, hcover, ?_⟩
  intro m x₀ hx₀ v hv j hj z hz
  have hr (i : H) (hi : i ∈ S) : 0 < r i := hrmin.trans_le (hlower i hi)
  have hr₀ : 0 < r x₀ := hr x₀ (hIS hx₀)
  let xref : S := ⟨x₀, hIS hx₀⟩
  have hbase : 1 ≤ 1 + 2 * A * D := by
    have hnonneg : 0 ≤ 2 * A * D := by positivity
    linarith
  have hcardReal := (hcount xref v hv).trans (pow_le_pow_right₀ hbase (hdim xref))
  have hcardNat :
      (I ∩ {i : H | (closedBall i (20 * ℓ * r i) ∩ ball v (ℓ * r x₀)).Nonempty}).ncard ≤ N := by
    have hceil : (1 + 2 * A * D) ^ k ≤ (N : ℝ) := Nat.le_ceil _
    exact_mod_cast hcardReal.trans hceil
  have htwenty (i : H) : 2 * (10 * ℓ * r i) = 20 * ℓ * r i := by ring
  have hactive :
      (((hI.toFinset : Set H) ∩
        {i | (closedBall i (2 * (10 * ℓ * r i)) ∩ ball v (ℓ * r x₀)).Nonempty}).ncard ≤ N) := by
    simpa only [hI.coe_toFinset, htwenty] using hcardNat
  have hbudget : C * ℓ ≤ 1 / 100 := by
    dsimp [ℓ]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (C + 1))).mpr
    nlinarith
  have hscale_active (i : H) (hi : i ∈ hI.toFinset)
      (hmeet : (closedBall i (2 * (10 * ℓ * r i)) ∩ ball v (ℓ * r x₀)).Nonempty) :
      r x₀ ≤ (Λ : ℝ) * (10 * ℓ * r i) := by
    have hiS : i ∈ S := hIS (hI.mem_toFinset.mp hi)
    have hmeeting : (closedBall i (20 * ℓ * r i) ∩ ball v (ℓ * r x₀)).Nonempty := by
      simpa only [htwenty] using hmeet
    have hlocal := Metric.coarse_scale_comparison_of_support_meeting
      hr₀ (hr i hiS) hC hℓ.le hbudget
      (by
        have h := (abs_le.mp (hscale x₀ (hIS hx₀) i hiS)).2
        simpa only [dist_comm x₀ i] using h)
      ((abs_le.mp (hscale i hiS x₀ (hIS hx₀))).2) hv hmeeting
    have hlo : r x₀ ≤ A * r i := by
      have h := (div_le_iff₀ hA).mp hlocal.1
      nlinarith
    have heq : (Λ : ℝ) * (10 * ℓ * r i) = A * r i := by
      change A / (10 * ℓ) * (10 * ℓ * r i) = A * r i
      field_simp [hℓ.ne']
    rw [heq]
    exact hlo
  have hplateau (y : H) (hy : y ∈ ball v (ℓ * r x₀)) :
      ∃ i ∈ hI.toFinset, dist y i ≤ 10 * ℓ * r i := by
    refine ⟨x₀, hI.mem_toFinset.mpr hx₀, ?_⟩
    have ht := dist_triangle y v x₀
    have hv' : dist v x₀ < 5 * ℓ * r x₀ := hv
    have hy' : dist y v < ℓ * r x₀ := hy
    have hpos := mul_pos hℓ hr₀
    linarith
  have h := hbound m H H hI.toFinset (fun i => i) (fun i => 10 * ℓ * r i)
    (ball v (ℓ * r x₀)) isOpen_ball hactive
    (fun i hi => by have hrᵢ := hr i (hIS (hI.mem_toFinset.mp hi)); positivity)
    (r x₀) hr₀ hscale_active hplateau j hj z hz
  exact h

end GC.MetricGeometry
