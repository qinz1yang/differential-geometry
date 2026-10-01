import DifferentialGeometry.Geometry.Metric.CloudSpectralJets
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.LocalizedWeightedDisplacement
import DifferentialGeometry.Analysis.Calculus.ContDiff.BufferedBall

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff
namespace GC.MetricGeometry
universe u

theorem exists_uniform_cloud_displacement_jets
    (k : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ B E : ℕ → ℝ≥0,
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
          let Ω : Set H := ⋃ i ∈ I, ball i (6 * ℓ * r i)
          ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) Ω ∧
          (∀ z ∈ Ω, Module.finrank ℝ (Q z) = Module.finrank ℝ H - k) ∧
          ContDiffOn ℝ ∞ (fun y => (Q y).starProjection
            (y - ∑ i ∈ hI.toFinset, w i y • i)) Ω ∧
          ∀ x₀ ∈ I, ∀ v ∈ ball x₀ (5 * ℓ * r x₀),
            ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) (ball v (ℓ * r x₀)) ∧
            (∀ z ∈ ball v (ℓ * r x₀),
              Module.finrank ℝ (Q z) = Module.finrank ℝ H - k ∧
              ‖(Q z).starProjection - (P x₀)ᗮ.starProjection‖ ≤
                24 * (2 * (C + 1) + 1) * δ) ∧
            ∀ m : ℕ, ∀ j ≤ m, ∀ z ∈ ball v (ℓ * r x₀),
              (‖iteratedFDeriv ℝ j (fun y =>
                (⨆ μ ∈ ball (1 : ℝ) (1 / 2),
                  Module.End.eigenspace
                    (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ).starProjection -
                    (P x₀)ᗮ.starProjection) z‖ ≤
                max 4 ((resolventDerivativeBound 4 (B m) j : ℝ) / 2) *
                  (6 * (2 * (C + 1) + 1)) * δ / (r x₀) ^ j) ∧
              ‖iteratedFDeriv ℝ j (fun y => (Q y).starProjection
                (y - ∑ i ∈ hI.toFinset, w i y • i) -
                  (P x₀)ᗮ.starProjection (y - x₀)) z‖ ≤
                    (E m : ℝ) * δ * r x₀ * ((r x₀)⁻¹) ^ j := by
  classical
  obtain ⟨B, hbound⟩ := exists_uniform_cloud_spectral_projection_jets.{u} k C hC
  let ℓ : ℝ := 1 / (100 * (C + 1))
  let A : ℝ := 2 * (C + 1)
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  let D : ℝ≥0 := ⟨(20 * A + 6) * ℓ, by positivity⟩
  let R₀ : ℝ≥0 := ⟨6 * ℓ, by positivity⟩
  let F : ℕ → ℕ → ℝ≥0 := fun m j =>
    ⟨max 4 ((resolventDerivativeBound 4 (B m) j : ℝ) / 2) * (6 * (A + 1)), by positivity⟩
  let M : ℕ → ℝ≥0 := fun m => ∑ j ∈ Finset.range (m + 1), F m j
  let E : ℕ → ℝ≥0 := fun m => 2 ^ m * M m * (max R₀ 1 + D * B m) + B m
  refine ⟨B, E, ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall hscale hcloud
  obtain ⟨I, hI, hIS, hdisj, hcover, hweights, hspectral⟩ :=
    hbound H S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hδsmall hscale hcloud
  refine ⟨I, hI, hIS, hdisj, hcover, hweights, ?_⟩
  dsimp only
  let w : H → H → ℝ := fun i y =>
    ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
      (∑ a ∈ hI.toFinset, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)
  let Q : H → Submodule ℝ H := fun y =>
    ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
      (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
  let Ω : Set H := ⋃ i ∈ I, ball i (6 * ℓ * r i)
  have hrall (i : H) (hi : i ∈ I) : 0 < r i := hrmin.trans_le (hlower i (hIS hi))
  have hballcover (i : H) (hi : i ∈ I) :
      ball i (6 * ℓ * r i) = ⋃ v ∈ ball i (5 * ℓ * r i), ball v (ℓ * r i) := by
    rw [Metric.biUnion_ball_of_mem_ball_eq_ball_add i
      (by have hp := hrall i hi; positivity) (mul_pos hℓ (hrall i hi))]
    congr 1
    ring
  have hlocalpoint (z : H) (hz : z ∈ Ω) :
      ∃ i ∈ I, ∃ v ∈ ball i (5 * ℓ * r i), z ∈ ball v (ℓ * r i) := by
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.mp hz
    rw [hballcover i hi] at hzi
    obtain ⟨v, hv, hzv⟩ := mem_iUnion₂.mp hzi
    exact ⟨i, hi, v, hv, hzv⟩
  have hQglobal : ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) Ω := by
    intro z hz
    obtain ⟨i, hi, v, hv, hzv⟩ := hlocalpoint z hz
    exact ((hspectral i hi v hv).1.contDiffAt (isOpen_ball.mem_nhds hzv)).contDiffWithinAt
  have hrankglobal (z : H) (hz : z ∈ Ω) :
      Module.finrank ℝ (Q z) = Module.finrank ℝ H - k := by
    obtain ⟨i, hi, v, hv, hzv⟩ := hlocalpoint z hz
    exact ((hspectral i hi v hv).2.1 z hzv).1
  have hρglobal (i : H) (hi : i ∈ hI.toFinset) : 0 < 10 * ℓ * r i := by
    have hp := hrall i (hI.mem_toFinset.mp hi)
    positivity
  have hplateauglobal (y : H) (hy : y ∈ Ω) :
      ∃ i ∈ hI.toFinset, dist y i ≤ 10 * ℓ * r i := by
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
    refine ⟨i, hI.mem_toFinset.mpr hi, ?_⟩
    have hd : dist y i < 6 * ℓ * r i := hyi
    have hp := mul_pos hℓ (hrall i hi)
    linarith
  have hwglobal (i : H) : ContDiffOn ℝ ∞ (w i) Ω :=
    contDiffOn_normalized_ballCutoff_of_cover hI.toFinset (fun i => i)
      (fun i => 10 * ℓ * r i) hρglobal hplateauglobal i
  have hηglobal : ContDiffOn ℝ ∞ (fun y => (Q y).starProjection
      (y - ∑ i ∈ hI.toFinset, w i y • i)) Ω :=
    hQglobal.clm_apply (contDiffOn_id.sub
      (ContDiffOn.sum (fun i _ => (hwglobal i).smul_const i)))
  refine ⟨hQglobal, hrankglobal, hηglobal, ?_⟩
  intro x₀ hx₀ v hv
  obtain ⟨hQ, hrank, hjets⟩ := hspectral x₀ hx₀ v hv
  refine ⟨hQ, hrank, ?_⟩
  have hr (i : H) (hi : i ∈ S) : 0 < r i := hrmin.trans_le (hlower i hi)
  have hr₀ := hr x₀ (hIS hx₀)
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
    contDiffOn_normalized_ballCutoff_of_cover hI.toFinset (fun i => i)
      (fun i => 10 * ℓ * r i) hρ hplateau i
  have hw1 (y : H) (hy : y ∈ ball v (ℓ * r x₀)) : ∑ i ∈ hI.toFinset, w i y = 1 :=
    sum_normalized_ballCutoffs_eq_one_of_cover hI.toFinset (fun i => i)
      (fun i => 10 * ℓ * r i) hρ (hplateau y hy)
  have hbudget : C * ℓ ≤ 1 / 100 := by
    dsimp [ℓ]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_iff₀ (by positivity : 0 < 100 * (C + 1))).mpr
    nlinarith
  have hcenters (i : H) (hi : i ∈ hI.toFinset)
      (ha : ∃ y ∈ ball v (ℓ * r x₀), w i y ≠ 0) :
      ‖i - x₀‖ ≤ D * r x₀ ∧ ‖(P x₀)ᗮ.starProjection (i - x₀)‖ ≤ δ * r x₀ := by
    obtain ⟨y, hy, hne⟩ := ha
    have hin : y ∈ ball i (2 * (10 * ℓ * r i)) := by
      by_contra hnot
      apply hne
      change ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y / _ = 0
      rw [ballCutoff_eq_zero_of_not_mem_ball (hρ i hi).le (by linarith [hρ i hi]) hnot, zero_div]
    have hmeet : (closedBall i (20 * ℓ * r i) ∩ ball v (ℓ * r x₀)).Nonempty := by
      refine ⟨y, ?_, hy⟩
      have hrad : 2 * (10 * ℓ * r i) = 20 * ℓ * r i := by ring
      rw [← hrad]
      exact ball_subset_closedBall hin
    have hiS := hIS (hI.mem_toFinset.mp hi)
    have hlocal := Metric.coarse_scale_comparison_of_support_meeting hr₀ (hr i hiS)
      hC hℓ.le hbudget
      (by simpa only [dist_comm x₀ i] using (abs_le.mp (hscale x₀ (hIS hx₀) i hiS)).2)
      (abs_le.mp (hscale i hiS x₀ (hIS hx₀))).2 hv hmeet
    refine ⟨?_, ?_⟩
    · change ‖i - x₀‖ ≤ ((20 * A + 6) * ℓ) * r x₀
      simpa only [dist_eq_norm, A] using hlocal.2.2
    · exact (normal_projection_coherence_of_cloud_support_meeting S T hST r
        (fun x : S => P x) C hC δ hδ hr hscale (fun x => hcloud x x.property)
        hδsmall ⟨x₀, hIS hx₀⟩ ⟨i, hiS⟩ ((hdim x₀ (hIS hx₀)).trans (hdim i hiS).symm)
        v hv hmeet).1
  intro m j hj z hz
  refine ⟨hjets m j hj z hz, ?_⟩
  have hF (q : ℕ) (hq : q ≤ m) : F m q ≤ M m :=
    Finset.single_le_sum (fun a _ => (show 0 ≤ F m a from bot_le)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hq))
  have hweightjet (q : ℕ) (hq : q ≤ m) :
      (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ q (w i) z‖) ≤ B m * ((r x₀)⁻¹) ^ q := by
    simpa only [w, ℓ, div_eq_mul_inv, inv_pow] using hweights m x₀ hx₀ v hv q hq z hz
  have hQjet (q : ℕ) (hq : q ≤ m) :
      ‖iteratedFDeriv ℝ q (fun y => (Q y).starProjection - (P x₀)ᗮ.starProjection) z‖ ≤
        M m * δ * ((r x₀)⁻¹) ^ q := by
    have h := hjets m q hq z hz
    have h' : ‖iteratedFDeriv ℝ q (fun y => (Q y).starProjection - (P x₀)ᗮ.starProjection) z‖ ≤
        F m q * δ * ((r x₀)⁻¹) ^ q := by
      have hFc : (F m q : ℝ) =
          max 4 ((resolventDerivativeBound 4 (B m) q : ℝ) / 2) * (6 * (A + 1)) := by
        rfl
      rw [hFc]
      simpa only [Q, w, ℓ, A, div_eq_mul_inv, inv_pow, mul_assoc] using h
    exact h'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr (hF q hq)) hδ.le)
      (pow_nonneg (inv_nonneg.mpr hr₀.le) _))
  have hzdist : ‖z - x₀‖ ≤ R₀ * r x₀ := by
    have ht := dist_triangle z v x₀
    have hv' : dist v x₀ < 5 * ℓ * r x₀ := hv
    have hz' : dist z v < ℓ * r x₀ := hz
    change ‖z - x₀‖ ≤ (6 * ℓ) * r x₀
    rw [← dist_eq_norm]
    linarith
  have h := norm_iteratedFDeriv_weighted_displacement_sub_translate_le_of_active_bounds
    hI.toFinset isOpen_ball (fun i _ => (hw i).of_le (by simp)) hw1
    (hQ.of_le (by simp)) (P x₀)ᗮ.starProjection (fun i => i) x₀ hz hr₀ hδ.le
    (M m) (B m) D R₀ 1 hweightjet hQjet
    (fun i hi ha => (hcenters i hi ha).1)
    (fun i hi ha => by simpa using (hcenters i hi ha).2) hzdist j hj
  apply h.trans
  have hpow : (2 : ℝ) ^ j ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hj
  have hcoef : ((2 : ℝ) ^ j * M m * (max (R₀ : ℝ) 1 + D * B m) + (1 : ℝ≥0) * B m) ≤ E m := by
    simp only [E, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat,
      NNReal.coe_max, NNReal.coe_one, one_mul]
    gcongr
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hδ.le) hr₀.le)
    (pow_nonneg (inv_nonneg.mpr hr₀.le) _)

end GC.MetricGeometry
