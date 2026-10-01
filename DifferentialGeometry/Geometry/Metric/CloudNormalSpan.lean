import DifferentialGeometry.Geometry.Metric.AffineScaleCover
import DifferentialGeometry.Analysis.InnerProductSpace.LocalizedNormalSpectralSection
import DifferentialGeometry.Geometry.Metric.CloudPlaneCoherence
import DifferentialGeometry.Analysis.Calculus.Cutoff.NormalizedBallPartition

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal
namespace GC.MetricGeometry

open Classical in
theorem common_normal_span_of_cloud_selection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (S T I : Set H) (hST : S ⊆ T) (hI : I.Finite) (hIS : I ⊆ S)
    (r : H → ℝ) (P : H → Submodule ℝ H) (k : ℕ)
    (hdim : ∀ x ∈ S, Module.finrank ℝ (P x) ≤ k)
    (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hr : ∀ x ∈ S, 0 < r x)
    (hscale : ∀ x ∈ S, ∀ y ∈ S, |r y - r x| ≤ C * (dist x y + r x))
    (hcloud : ∀ x ∈ S,
      hausdorffEDist (T ∩ ball x (r x / δ))
        ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
          ENNReal.ofReal (δ * r x)) :
    let ℓ : ℝ := 1 / (100 * (C + 1))
    let A : ℝ := 2 * (C + 1)
    let N : ℕ := ⌈(1 + 2 * A * (20 * A + 6)) ^ k⌉₊
    δ ≤ ℓ / (2 * A) →
    I.PairwiseDisjoint (fun i => ball i (ℓ * r i)) →
    let w : H → H → ℝ := fun i y =>
      ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
        (∑ a ∈ hI.toFinset, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)
    let Q : H → H →L[ℝ] H := fun y =>
      (⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
        (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ).starProjection
    ∀ x₀ ∈ I, ∀ v ∈ ball x₀ (5 * ℓ * r x₀),
      let U := ball v (ℓ * r x₀)
      let J := hI.toFinset.filter (fun i => ∃ y ∈ U, w i y ≠ 0)
      let V : Submodule ℝ H := J.sup (fun i => (ℝ ∙ (i - x₀)) ⊔ P i)
      J.card ≤ N ∧ Module.finrank ℝ V ≤ N * (k + 1) ∧
        ∀ z ∈ U, (∀ u ∈ Vᗮ, Q z u = u) ∧
          Vᗮ.starProjection (Q z (z - ∑ i ∈ hI.toFinset, w i z • i)) =
            Vᗮ.starProjection (z - x₀) := by
  classical
  dsimp only
  let ℓ : ℝ := 1 / (100 * (C + 1))
  let A : ℝ := 2 * (C + 1)
  let D : ℝ := 20 * A + 6
  let N : ℕ := ⌈(1 + 2 * A * D) ^ k⌉₊
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  intro hδsmall hdisj
  let w : H → H → ℝ := fun i y =>
    ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y /
      (∑ a ∈ hI.toFinset, ballCutoff a (10 * ℓ * r a) (2 * (10 * ℓ * r a)) y)
  intro x₀ hx₀ v hv
  let U := ball v (ℓ * r x₀)
  let J := hI.toFinset.filter (fun i => ∃ y ∈ U, w i y ≠ 0)
  let K : Set H := I ∩ {i | (closedBall i (20 * ℓ * r i) ∩ U).Nonempty}
  have hr₀ := hr x₀ (hIS hx₀)
  have hρ (i : H) (hi : i ∈ hI.toFinset) : 0 < 10 * ℓ * r i := by
    have hp := hr i (hIS (hI.mem_toFinset.mp hi))
    positivity
  have hplateau (y : H) (hy : y ∈ U) : ∃ i ∈ hI.toFinset, dist y i ≤ 10 * ℓ * r i := by
    refine ⟨x₀, hI.mem_toFinset.mpr hx₀, ?_⟩
    have ht := dist_triangle y v x₀
    have hv' : dist v x₀ < 5 * ℓ * r x₀ := hv
    have hy' : dist y v < ℓ * r x₀ := hy
    have hpos := mul_pos hℓ hr₀
    linarith
  have hw1 (y : H) (hy : y ∈ U) : ∑ i ∈ hI.toFinset, w i y = 1 :=
    sum_normalized_ballCutoffs_eq_one_of_cover hI.toFinset (fun i => i)
      (fun i => 10 * ℓ * r i) hρ (hplateau y hy)
  have hJK : (J : Set H) ⊆ K := by
    intro i hi
    obtain ⟨hiI, y, hy, hne⟩ := Finset.mem_filter.mp hi
    have hin : y ∈ ball i (2 * (10 * ℓ * r i)) := by
      by_contra hnot
      apply hne
      change ballCutoff i (10 * ℓ * r i) (2 * (10 * ℓ * r i)) y / _ = 0
      rw [ballCutoff_eq_zero_of_not_mem_ball (hρ i hiI).le (by linarith [hρ i hiI]) hnot, zero_div]
    refine ⟨hI.mem_toFinset.mp hiI, y, ?_, hy⟩
    have heq : 2 * (10 * ℓ * r i) = 20 * ℓ * r i := by ring
    rw [← heq]
    exact ball_subset_closedBall hin
  have hflat (i : H) (hi : i ∈ I) (hnear : dist i x₀ < r x₀ / δ) :
      infDist i (AffineSubspace.mk' x₀ (P x₀) : Set H) ≤ δ * r x₀ := by
    have he : infEDist i (AffineSubspace.mk' x₀ (P x₀) : Set H) ≤ ENNReal.ofReal (δ * r x₀) :=
      (infEDist_anti inter_subset_left).trans
        ((infEDist_le_hausdorffEDist_of_mem
          (show i ∈ T ∩ ball x₀ (r x₀ / δ) from ⟨hST (hIS hi), hnear⟩)).trans
            (hcloud x₀ (hIS hx₀)))
    simpa only [Metric.infDist, ENNReal.toReal_ofReal (mul_pos hδ hr₀).le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  have hpack := neighborhood_support_packing_of_coarse_control I hI r (P x₀) C hC
    δ hδ hδsmall x₀ v (r x₀) hr₀ (fun i hi => hr i (hIS hi))
    (fun i hi => by simpa only [dist_comm x₀ i] using
      (abs_le.mp (hscale x₀ (hIS hx₀) i (hIS hi))).2)
    (fun i hi => (abs_le.mp (hscale i (hIS hi) x₀ (hIS hx₀))).2)
    hdisj hflat hv
  have hbase : 1 ≤ 1 + 2 * A * D := by
    have hnonneg : 0 ≤ 2 * A * D := by positivity
    linarith
  have hcardReal : (K.ncard : ℝ) ≤ (1 + 2 * A * D) ^ k :=
    hpack.trans (pow_le_pow_right₀ hbase (hdim x₀ (hIS hx₀)))
  have hcardNat : K.ncard ≤ N := by
    have hceil : (1 + 2 * A * D) ^ k ≤ (N : ℝ) := Nat.le_ceil _
    exact_mod_cast hcardReal.trans hceil
  have hJcard : J.card ≤ N := by
    have h := (Set.ncard_le_ncard hJK (hI.subset (fun _ hi => hi.1))).trans hcardNat
    simpa only [Set.ncard_coe_finset] using h
  have hstructure := Submodule.localized_weighted_normal_spectral_section
    hI.toFinset U w hw1 P (fun i => i) x₀
  refine ⟨hJcard, ?_, hstructure.2⟩
  apply hstructure.1.trans
  calc
    (∑ i ∈ J, (Module.finrank ℝ (P i) + 1)) ≤ ∑ _i ∈ J, (k + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.add_le_add_right (hdim i (hIS (hI.mem_toFinset.mp (Finset.mem_filter.mp hi).1))) 1
    _ = J.card * (k + 1) := by simp
    _ ≤ N * (k + 1) := Nat.mul_le_mul_right _ hJcard

end GC.MetricGeometry
