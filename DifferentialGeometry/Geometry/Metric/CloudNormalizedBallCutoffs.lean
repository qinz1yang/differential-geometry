import DifferentialGeometry.Analysis.Calculus.Cutoff.LocalizedNormalizedBallCutoffs
import DifferentialGeometry.Geometry.Metric.AffineScaleCover
import Mathlib.Algebra.Order.Floor.Semiring
import DifferentialGeometry.Geometry.Metric.LargeCloudCover

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff

namespace GC.MetricGeometry
section

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

end
end GC.MetricGeometry

namespace GC.MetricGeometry
section

universe u

theorem exists_uniform_large_cloud_normalized_ballCutoff_bounds
    (k : ℕ) (b B : ℝ) (hb : 1 ≤ b) (hB : 1 ≤ B) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : S → Submodule ℝ H)
          [∀ x : S, FiniteDimensional ℝ (P x)],
        (∀ x : S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ →
        δ * ((80 * B + 31) * b + 2) < 1 →
        (∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * b * max (r y) (r x) →
          r x / B ≤ r y ∧ r y ≤ B * r x) →
        (∀ x : S, hausdorffEDist (T ∩ ball (x : H) (r x / δ))
          ((AffineSubspace.mk' (x : H) (P x) : Set H) ∩ ball (x : H) (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (r i)) ∧
          (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
          ((⋃ x ∈ S, ball x (8 * b * r x)) ⊆ ⋃ i ∈ I, ball i (20 * b * r i)) ∧
          let w : H → H → ℝ := fun i y =>
            ballCutoff i (40 * b * r i) (2 * (40 * b * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (40 * b * r a) (2 * (40 * b * r a)) y)
          (∀ m, ∀ x : S, ∀ j ≤ m, ∀ z ∈ ball (x : H) (8 * b * r x),
            (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w i) z‖) ≤ C m / (r x) ^ j) ∧
          (∀ m, ∀ i ∈ I, ∀ j ≤ m, ∀ z ∈ ball i (30 * b * r i),
            (∑ a ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w a) z‖) ≤ C m / (r i) ^ j) := by
  classical
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  let D : ℝ := 80 * B + 31
  let N : ℕ := ⌈(1 + 2 * B * D * b) ^ k⌉₊
  let Λ : ℝ≥0 := ⟨B / (40 * b), by positivity⟩
  choose C hC hbound using fun m : ℕ =>
    exists_bound_iteratedFDeriv_normalized_ballCutoffs_of_active_card_le.{u,u} m N Λ
  refine ⟨C,hC,?_⟩
  intro H _ _ S T hST hS r P _ hdim rmin R δ hrmin hlower hupper
    hδ hδinterior hscale hcloud
  obtain ⟨I,hIS,hI,hdisj,hcover,htube,hlocal⟩ :=
    exists_large_cloud_cover_of_hausdorffEDist_le S T hST hS r P k hdim
      rmin R b B δ hrmin hlower hupper hb hB hδ hδinterior hscale hcloud
  refine ⟨I,hI,hIS,hdisj,hcover,htube,?_⟩
  have hr (i : H) (hi : i ∈ S) : 0 < r i := hrmin.trans_le (hlower i hi)
  have htwice (i : H) : 2 * (40 * b * r i)=80 * b * r i := by ring
  have hlocalbound (m : ℕ) (x : S) (U : Set H) (hU : IsOpen U)
      (hUsub : U ⊆ ball (x : H) (30 * b * r x))
      (hplateau : ∀ y ∈ U, ∃ i ∈ hI.toFinset, dist y i ≤ 40 * b * r i)
      (j : ℕ) (hjm : j ≤ m) (z : H) (hz : z ∈ U) :
      (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ j
        (fun y => ballCutoff i (40 * b * r i) (2 * (40 * b * r i)) y /
          (∑ a ∈ hI.toFinset, ballCutoff a (40 * b * r a) (2 * (40 * b * r a)) y)) z‖)
        ≤ C m / (r x) ^ j := by
    let J : Set H := I ∩ {i | (closedBall i (80 * b * r i) ∩ ball (x : H) (30 * b * r x)).Nonempty}
    have hcard : J.ncard ≤ N := by
      have hh := (hlocal x).1
      have hc : (1 + 2 * B * D * b) ^ k ≤ (N : ℝ) := Nat.le_ceil _
      exact_mod_cast hh.trans hc
    have hsubset : ((hI.toFinset : Set H) ∩
        {i | (closedBall i (2 * (40 * b * r i)) ∩ U).Nonempty}) ⊆ J := by
      intro i hi
      obtain ⟨y,hy,hyU⟩ := hi.2
      refine ⟨hI.mem_toFinset.mp hi.1,y,?_,hUsub hyU⟩
      simpa only [htwice] using hy
    have hactive : ((hI.toFinset : Set H) ∩
        {i | (closedBall i (2 * (40 * b * r i)) ∩ U).Nonempty}).ncard ≤ N :=
      (Set.ncard_le_ncard hsubset (hI.subset (fun _ hi => hi.1))).trans hcard
    have hsc (i : H) (hi : i ∈ hI.toFinset)
        (hmeet : (closedBall i (2 * (40 * b * r i)) ∩ U).Nonempty) :
        r x ≤ (Λ : ℝ) * (40 * b * r i) := by
      have hj : i ∈ J := hsubset ⟨hi,hmeet⟩
      have hlo := ((hlocal x).2 i hj).1
      have hh := (div_le_iff₀ hBpos).mp hlo
      have heq : (Λ : ℝ) * (40 * b * r i)=B * r i := by
        change B / (40 * b) * (40 * b * r i)=B * r i
        field_simp [hbpos.ne']
      rw [heq]
      nlinarith
    exact hbound m H H hI.toFinset (fun i => i) (fun i => 40 * b * r i) U hU hactive
      (fun i hi => by have hi' := hr i (hIS (hI.mem_toFinset.mp hi)); positivity)
      (r x) (hr x x.property) hsc hplateau j hjm z hz
  constructor
  · intro m x j hj z hz
    apply hlocalbound m x (ball (x : H) (8 * b * r x)) isOpen_ball ?_ ?_ j hj z hz
    · intro y hy
      have hxpos := hr x x.property
      change dist y (x : H) < 30 * b * r x
      have hy' : dist y (x : H) < 8 * b * r x := hy
      nlinarith [mul_pos hbpos hxpos]
    · intro y hy
      obtain ⟨i,hi,hri,hdist⟩ := hcover x x.property
      refine ⟨i,hI.mem_toFinset.mpr hi,?_⟩
      have ht := dist_triangle y (x : H) i
      have hy' : dist y (x : H) < 8 * b * r x := hy
      have hmul := mul_le_mul_of_nonneg_left hri (by positivity : 0 ≤ 8 * b)
      have hi' := hr i (hIS hi)
      have hbmul := mul_le_mul_of_nonneg_right hb hi'.le
      nlinarith
  · intro m i hi j hj z hz
    apply hlocalbound m ⟨i,hIS hi⟩ (ball i (30 * b * r i)) isOpen_ball
      (fun _ hy => hy) ?_ j hj z hz
    intro y hy
    refine ⟨i,hI.mem_toFinset.mpr hi,?_⟩
    have hi' := hr i (hIS hi)
    have hy' : dist y i < 30 * b * r i := hy
    nlinarith [mul_pos hbpos hi']

end
end GC.MetricGeometry
