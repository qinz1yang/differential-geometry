import DifferentialGeometry.Analysis.InnerProductSpace.LocalizedWeightedSpectral
import DifferentialGeometry.Analysis.InnerProductSpace.ActiveWeightedSpectralRegularity
import DifferentialGeometry.Geometry.Metric.CloudNormalizedBallCutoffs
import DifferentialGeometry.Geometry.Metric.CloudPlaneCoherence
import DifferentialGeometry.Analysis.Calculus.Cutoff.NormalizedBallPartition

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff
namespace GC.MetricGeometry
universe u

theorem exists_uniform_cloud_spectral_projection_jets
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℕ → ℝ≥0,
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ ≤ (1 / (100 * (C + 1))) / (2 * (2 * (C + 1))) →
        (∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x)) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        let ℓ : ℝ := 1 / (100 * (C + 1))
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (ℓ * r i)) ∧
          ((⋃ x ∈ S, ball x (ℓ * r x)) ⊆ ⋃ i ∈ I, ball i (5 * ℓ * r i)) ∧
          (∀ m : ℕ, ∀ x₀ ∈ I, ∀ v ∈ ball x₀ (5 * ℓ * r x₀),
            ∀ j ≤ m, ∀ z ∈ ball v (ℓ * r x₀),
              (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ j
                (fun y => ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
                  (∑ a ∈ hI.toFinset,
                    ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)) z‖) ≤
                      (B m : ℝ) / (r x₀) ^ j) ∧
          let w : H → H → ℝ := fun i y =>
            ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)
          let Q : H → Submodule ℝ H := fun y =>
            ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
              (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
          ∀ x₀ ∈ I, ∀ v ∈ ball x₀ (5 * ℓ * r x₀),
            ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) (ball v (ℓ * r x₀)) ∧
            (∀ z ∈ ball v (ℓ * r x₀),
              Module.finrank ℝ (Q z) = Module.finrank ℝ H - k ∧
              ‖(Q z).starProjection - (P x₀)ᗮ.starProjection‖ ≤
                24 * (2 * (C + 1) + 1) * δ) ∧
            ∀ m : ℕ, ∀ j ≤ m, ∀ z ∈ ball v (ℓ * r x₀),
              ‖iteratedFDeriv ℝ j (fun y =>
                (⨆ μ ∈ ball (1 : ℝ) (1 / 2),
                  Module.End.eigenspace
                    (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ).starProjection -
                    (P x₀)ᗮ.starProjection) z‖ ≤
                max 4 ((resolventDerivativeBound 4 (B m) j : ℝ) / 2) *
                  (6 * (2 * (C + 1) + 1)) * δ / (r x₀) ^ j := by
  classical
  obtain ⟨B, hB, hbound⟩ := exists_uniform_cloud_normalized_ballCutoff_bounds.{u} k C hC
  refine ⟨fun m => ⟨B m, hB m⟩, ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall hscale hcloud
  let ℓ : ℝ := 1 / (100 * (C + 1))
  let A : ℝ := 2 * (C + 1)
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hA : 2 ≤ A := by dsimp [A]; linarith
  have hℓsmall : ℓ ≤ 1 / 100 := by
    dsimp [ℓ]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (C + 1))).mpr
    nlinarith
  have hδbudget : δ * (2 * A) ≤ ℓ :=
    (le_div_iff₀ (by positivity : 0 < 2 * A)).mp hδsmall
  have hgap : 6 * (A + 1) * δ < 1 / 4 := by
    have hfactor : 6 * (A + 1) ≤ 9 * A := by linarith
    have h := mul_le_mul_of_nonneg_right hfactor hδ.le
    nlinarith
  obtain ⟨I, hI, hIS, hdisj, hcover, hweights⟩ :=
    hbound H S T hST hS r (fun x : S => P x)
      (fun x => (hdim x x.property).le)
      rmin R δ hrmin hlower hupper hδ hδsmall hscale (fun x => hcloud x x.property)
  refine ⟨I, hI, hIS, hdisj, hcover, hweights, ?_⟩
  dsimp only
  let w : H → H → ℝ := fun i y =>
    ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
      (∑ a ∈ hI.toFinset, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)
  intro x₀ hx₀ v hv
  have hr (i : H) (hi : i ∈ S) : 0 < r i := hrmin.trans_le (hlower i hi)
  have hr₀ : 0 < r x₀ := hr x₀ (hIS hx₀)
  have hρ (i : H) (hi : i ∈ hI.toFinset) : 0 < 10 * ℓ * r i := by
    have hp := hr i (hIS (hI.mem_toFinset.mp hi))
    positivity
  have hplateau (y : H) (hy : y ∈ ball v (ℓ * r x₀)) :
      ∃ i ∈ hI.toFinset, dist y i ≤ 10 * ℓ * r i := by
    refine ⟨x₀, hI.mem_toFinset.mpr hx₀, ?_⟩
    have ht := dist_triangle y v x₀
    have hv' : dist v x₀ < 5 * ℓ * r x₀ := hv
    have hy' : dist y v < ℓ * r x₀ := hy
    have hpos := mul_pos hℓ hr₀
    linarith
  have hw (i : H) : ContDiffOn ℝ ∞ (w i) (ball v (ℓ * r x₀)) :=
    (contDiffOn_normalized_ballCutoff_of_cover hI.toFinset (fun i => i)
      (fun i => 10 * ℓ * r i) hρ hplateau i)
  have hclose (i : H) (hi : i ∈ hI.toFinset)
      (ha : ∃ y ∈ ball v (ℓ * r x₀), w i y ≠ 0) :
      ‖(P i)ᗮ.starProjection - (P x₀)ᗮ.starProjection‖ ≤ 6 * (A + 1) * δ := by
    obtain ⟨y, hy, hne⟩ := ha
    have hin : y ∈ ball i (2 * (10 * ℓ * r i)) := by
      by_contra hnot
      apply hne
      change ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y / _ = 0
      rw [ballCutoff_eq_zero_of_not_mem_ball (hρ i hi).le (by linarith [hρ i hi]) hnot,
        zero_div]
    have hmeet : (closedBall i (20 * ℓ * r i) ∩ ball v (ℓ * r x₀)).Nonempty := by
      refine ⟨y, ?_, hy⟩
      have hrad : 2 * (10 * ℓ * r i) = 20 * ℓ * r i := by ring
      rw [← hrad]
      exact ball_subset_closedBall hin
    have hiS := hIS (hI.mem_toFinset.mp hi)
    exact (normal_projection_coherence_of_cloud_support_meeting S T hST r
      (fun x : S => P x) C hC δ hδ hr hscale (fun x => hcloud x x.property)
      hδsmall ⟨x₀, hIS hx₀⟩ ⟨i, hiS⟩ ((hdim x₀ (hIS hx₀)).trans (hdim i hiS).symm)
      v hv hmeet).2
  have hreg := real_weighted_spectral_projection_regular_rank hI.toFinset w
    (fun i _ => hw i)
    (fun y _ i _ => normalized_ballCutoff_nonneg hI.toFinset (fun a => a)
      (fun a => 10 * ℓ * r a) i y)
    (fun y hy => sum_normalized_ballCutoffs_eq_one_of_cover hI.toFinset (fun a => a)
      (fun a => 10 * ℓ * r a) hρ (hplateau y hy))
    (fun i => (P i)ᗮ.starProjection) (fun i _ => (P i)ᗮ.starProjection_isSymmetric)
    (P x₀)ᗮ hgap (fun y hy i hi hne => hclose i hi ⟨y, hy, hne⟩)
  refine ⟨hreg.1, ?_, ?_⟩
  · intro z hz
    obtain ⟨hrank, hnorm⟩ := hreg.2 z hz
    have hdimadd := (P x₀).finrank_add_finrank_orthogonal
    have hdim₀ := hdim x₀ (hIS hx₀)
    refine ⟨hrank.trans (by omega), ?_⟩
    have heq : 4 * (6 * (A + 1) * δ) = 24 * (2 * (C + 1) + 1) * δ := by
      dsimp [A]
      ring
    exact hnorm.trans_eq heq
  · intro m j hj z hz
    have hD (q : ℕ) (_hq : 1 ≤ q) (hqm : q ≤ m) :
        (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ q (w i) z‖) ≤
          (⟨B m, hB m⟩ : ℝ≥0) * ((r x₀)⁻¹) ^ q := by
      simpa only [w, ℓ, NNReal.coe_mk, div_eq_mul_inv, inv_pow] using
        hweights m x₀ hx₀ v hv q hqm z hz
    have h := norm_iteratedFDeriv_real_starProjection_eigenspace_ball_sum_smul_sub_le_of_active_close
      hI.toFinset isOpen_ball (fun i _ => (hw i).of_le (by simp))
      (fun y _ i _ => normalized_ballCutoff_nonneg hI.toFinset (fun a => a)
        (fun a => 10 * ℓ * r a) i y)
      (fun y hy => sum_normalized_ballCutoffs_eq_one_of_cover hI.toFinset (fun a => a)
        (fun a => 10 * ℓ * r a) hρ (hplateau y hy))
      (fun i => (P i)ᗮ.starProjection) (fun i _ => (P i)ᗮ.starProjection_isSymmetric)
      (P x₀)ᗮ (by positivity : 0 ≤ 6 * (A + 1) * δ) hgap.le
      (inv_nonneg.mpr hr₀.le) hclose hz ⟨B m, hB m⟩ hD j hj
    simpa only [w, ℓ, A, div_eq_mul_inv, inv_pow, mul_assoc] using h

end GC.MetricGeometry
