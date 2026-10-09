import DifferentialGeometry.Geometry.Metric.CloudSpectralJets
import DifferentialGeometry.Geometry.Metric.LargeCloudCover

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Analysis
open scoped BigOperators NNReal ContDiff
namespace GC.MetricGeometry
universe u

theorem exists_uniform_large_cloud_spectral_projection_jets
    (k : ℕ) (b B : ℝ) (hb : 1 ≤ b) (hB : 1 ≤ B) :
    ∃ C : ℕ → ℝ≥0,
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
        [FiniteDimensional ℝ H] (S T : Set H), S ⊆ T → TotallyBounded S →
        ∀ (r : H → ℝ) (P : H → Submodule ℝ H),
        (∀ x ∈ S, Module.finrank ℝ (P x) = k) →
        ∀ rmin R δ : ℝ, 0 < rmin →
        (∀ x ∈ S, rmin ≤ r x) → (∀ x ∈ S, r x ≤ R) →
        0 < δ → δ * ((80 * B + 31) * b + 2) < 1 →
        (∀ x ∈ S, ∀ y ∈ S, dist y x ≤ 128 * b * max (r y) (r x) →
          r x / B ≤ r y ∧ r y ≤ B * r x) →
        (∀ x ∈ S, hausdorffEDist (T ∩ ball x (r x / δ))
          ((AffineSubspace.mk' x (P x) : Set H) ∩ ball x (r x / δ)) ≤
            ENNReal.ofReal (δ * r x)) →
        ∃ (I : Set H) (hI : I.Finite), I ⊆ S ∧
          I.PairwiseDisjoint (fun i => ball i (r i)) ∧
          (∀ x ∈ S, ∃ i ∈ I, r x ≤ 2 * r i ∧ dist x i < 3 * r i) ∧
          ((⋃ x ∈ S, ball x (8 * b * r x)) ⊆ ⋃ i ∈ I, ball i (20 * b * r i)) ∧
          let w : H → H → ℝ := fun i y => ballCutoff i (40 * b * r i) (2 * (40 * b * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (40 * b * r a) (2 * (40 * b * r a)) y)
          let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
              (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
          (∀ m, ∀ x ∈ S, ∀ j ≤ m, ∀ z ∈ ball x (8 * b * r x),
            (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w i) z‖) ≤ (C m : ℝ) / (r x) ^ j) ∧
          (∀ m, ∀ i ∈ I, ∀ j ≤ m, ∀ z ∈ ball i (30 * b * r i),
            (∑ a ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w a) z‖) ≤ (C m : ℝ) / (r i) ^ j) ∧
          (∀ x ∈ S, ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) (ball x (8 * b * r x)) ∧
              (∀ z ∈ ball x (8 * b * r x), Module.finrank ℝ (Q z) = Module.finrank ℝ H - k ∧
                ‖(Q z).starProjection - (P x)ᗮ.starProjection‖ ≤ 24 * (B + 1) * δ) ∧
              ∀ m : ℕ, ∀ j ≤ m, ∀ z ∈ ball x (8 * b * r x),
                ‖iteratedFDeriv ℝ j (fun y => (Q y).starProjection - (P x)ᗮ.starProjection) z‖ ≤
                  max 4 ((resolventDerivativeBound 4 (C m) j : ℝ) / 2) *
                    (6 * (B + 1)) * δ / (r x) ^ j) ∧
          (∀ i ∈ I, ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) (ball i (30 * b * r i)) ∧
              (∀ z ∈ ball i (30 * b * r i), Module.finrank ℝ (Q z) = Module.finrank ℝ H - k ∧
                ‖(Q z).starProjection - (P i)ᗮ.starProjection‖ ≤ 24 * (B + 1) * δ) ∧
              ∀ m : ℕ, ∀ j ≤ m, ∀ z ∈ ball i (30 * b * r i),
                ‖iteratedFDeriv ℝ j (fun y => (Q y).starProjection - (P i)ᗮ.starProjection) z‖ ≤
                  max 4 ((resolventDerivativeBound 4 (C m) j : ℝ) / 2) *
                    (6 * (B + 1)) * δ / (r i) ^ j) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_uniform_large_cloud_normalized_ballCutoff_bounds.{u} k b B hb hB
  refine ⟨fun m => ⟨C m, hC m⟩, ?_⟩
  intro H _ _ _ S T hST hS r P hdim rmin R δ hrmin hlower hupper hδ hinterior hscale hcloud
  obtain ⟨I, hI, hIS, hdisj, hcover, htube, hcore, hselected⟩ :=
    hbound H S T hST hS r (fun x : S => P x) (fun x => hdim x x.property)
      rmin R δ hrmin hlower hupper hδ hinterior hscale (fun x => hcloud x x.property)
  refine ⟨I, hI, hIS, hdisj, hcover, htube, ?_⟩
  dsimp only
  let w : H → H → ℝ := fun i y => ballCutoff i (40 * b * r i) (2 * (40 * b * r i)) y /
              (∑ a ∈ hI.toFinset, ballCutoff a (40 * b * r a) (2 * (40 * b * r a)) y)
  let Q : H → Submodule ℝ H := fun y => ⨆ μ ∈ ball (1 : ℝ) (1 / 2), Module.End.eigenspace
              (∑ i ∈ hI.toFinset, w i y • (P i)ᗮ.starProjection).toLinearMap μ
  have hr (x : H) (hx : x ∈ S) : 0 < r x := hrmin.trans_le (hlower x hx)
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hρ (i : H) (hi : i ∈ hI.toFinset) : 0 < 40 * b * r i := by
    have hh := hr i (hIS (hI.mem_toFinset.mp hi))
    positivity
  have hgap : 6 * (B + 1) * δ < 1 / 4 := by
    have hbudget : 24 * (B + 1) ≤ (80 * B + 31) * b + 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hb (by linarith : 0 ≤ 80 * B + 31)]
    have hh := (mul_le_mul_of_nonneg_left hbudget hδ.le).trans_lt hinterior
    nlinarith
  have hgeometry := large_cloud_selected_center_geometry S T hST r
    (fun x : S => P x) k (fun x => hdim x x.property) I hIS hI hdisj hr
    b B δ hb hB hδ hinterior hscale (fun x => hcloud x x.property)
  have hlocal (x : H) (hx : x ∈ S) (U : Set H) (hU : IsOpen U)
      (hUsub : U ⊆ ball x (30 * b * r x))
      (hplateau : ∀ y ∈ U, ∃ i ∈ hI.toFinset, dist y i ≤ 40 * b * r i)
      (hweights : ∀ m, ∀ j ≤ m, ∀ z ∈ U,
        (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ j (w i) z‖) ≤ C m / (r x) ^ j) :
      ContDiffOn ℝ ∞ (fun y => (Q y).starProjection) (U) ∧
              (∀ z ∈ U, Module.finrank ℝ (Q z) = Module.finrank ℝ H - k ∧
                ‖(Q z).starProjection - (P x)ᗮ.starProjection‖ ≤ 24 * (B + 1) * δ) ∧
              ∀ m : ℕ, ∀ j ≤ m, ∀ z ∈ U,
                ‖iteratedFDeriv ℝ j (fun y => (Q y).starProjection - (P x)ᗮ.starProjection) z‖ ≤
                  max 4 ((resolventDerivativeBound 4 (⟨C m, hC m⟩ : ℝ≥0) j : ℝ) / 2) *
                    (6 * (B + 1)) * δ / (r x) ^ j := by
    have hw (i : H) : ContDiffOn ℝ ∞ (w i) U :=
      contDiffOn_normalized_ballCutoff_of_cover hI.toFinset (fun i => i)
        (fun i => 40 * b * r i) hρ hplateau i
    have hclose (i : H) (hi : i ∈ hI.toFinset)
        (ha : ∃ y ∈ U, w i y ≠ 0) :
        ‖(P i)ᗮ.starProjection - (P x)ᗮ.starProjection‖ ≤ 6 * (B + 1) * δ := by
      obtain ⟨y, hy, hne⟩ := ha
      have hin : y ∈ ball i (2 * (40 * b * r i)) := by
        by_contra hnot
        apply hne
        change ballCutoff i (40 * b * r i) (2 * (40 * b * r i)) y / _ = 0
        rw [ballCutoff_eq_zero_of_not_mem_ball (hρ i hi).le (by linarith [hρ i hi]) hnot, zero_div]
      have hclosed : y ∈ closedBall i (80 * b * r i) := by
        have heq : 2 * (40 * b * r i) = 80 * b * r i := by ring
        rw [← heq]
        exact ball_subset_closedBall hin
      exact ((hgeometry ⟨x, hx⟩).2 i
        ⟨hI.mem_toFinset.mp hi, y, hclosed, hUsub hy⟩).2.2.2.2
    have hnonneg (y : H) (i : H) : 0 ≤ w i y :=
      normalized_ballCutoff_nonneg hI.toFinset (fun a => a) (fun a => 40 * b * r a) i y
    have hsum (y : H) (hy : y ∈ U) : ∑ i ∈ hI.toFinset, w i y = 1 :=
      sum_normalized_ballCutoffs_eq_one_of_cover hI.toFinset (fun a => a)
        (fun a => 40 * b * r a) hρ (hplateau y hy)
    have hreg := real_weighted_spectral_projection_regular_rank hI.toFinset w
      (fun i _ => hw i) (fun y _ i _ => hnonneg y i) hsum
      (fun i => (P i)ᗮ.starProjection) (fun i _ => (P i)ᗮ.starProjection_isSymmetric)
      (P x)ᗮ hgap (fun y hy i hi hne => hclose i hi ⟨y, hy, hne⟩)
    refine ⟨hreg.1, ?_, ?_⟩
    · intro z hz
      obtain ⟨hrank, hnorm⟩ := hreg.2 z hz
      have hd := (P x).finrank_add_finrank_orthogonal
      have hk := hdim x hx
      refine ⟨hrank.trans (by omega), ?_⟩
      exact hnorm.trans_eq (by ring)
    · intro m j hj z hz
      have hD (q : ℕ) (_hq : 1 ≤ q) (hqm : q ≤ m) :
          (∑ i ∈ hI.toFinset, ‖iteratedFDeriv ℝ q (w i) z‖) ≤
            (⟨C m, hC m⟩ : ℝ≥0) * ((r x)⁻¹) ^ q := by
        simpa only [NNReal.coe_mk, div_eq_mul_inv, inv_pow] using hweights m q hqm z hz
      have h := norm_iteratedFDeriv_real_starProjection_eigenspace_ball_sum_smul_sub_le_of_active_close
        hI.toFinset hU (fun i _ => (hw i).of_le (by simp))
        (fun y _ i _ => hnonneg y i) hsum
        (fun i => (P i)ᗮ.starProjection) (fun i _ => (P i)ᗮ.starProjection_isSymmetric)
        (P x)ᗮ (by positivity : 0 ≤ 6 * (B + 1) * δ) hgap.le
        (inv_nonneg.mpr (hr x hx).le) hclose hz ⟨C m, hC m⟩ hD j hj
      simpa only [Q, div_eq_mul_inv, inv_pow, mul_assoc] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m x hx j hj z hz
    exact hcore m ⟨x, hx⟩ j hj z hz
  · exact hselected
  · intro x hx
    refine hlocal x hx (ball x (8 * b * r x)) isOpen_ball ?_ ?_ ?_
    · intro y hy
      have hp := mul_pos hbpos (hr x hx)
      change dist y x < 30 * b * r x
      have hy' : dist y x < 8 * b * r x := hy
      nlinarith
    · intro y hy
      obtain ⟨i, hi, hrad, hdist⟩ := hcover x hx
      refine ⟨i, hI.mem_toFinset.mpr hi, ?_⟩
      have hy' : dist y x < 8 * b * r x := hy
      have htri := dist_triangle y x i
      have hri := hr i (hIS hi)
      have hrb := mul_le_mul_of_nonneg_left hrad (by positivity : 0 ≤ 8 * b)
      nlinarith [mul_le_mul_of_nonneg_right hb hri.le]
    · exact fun m j hj z hz => hcore m ⟨x, hx⟩ j hj z hz
  · intro i hi
    refine hlocal i (hIS hi) (ball i (30 * b * r i)) isOpen_ball Subset.rfl ?_ ?_
    · intro y hy
      refine ⟨i, hI.mem_toFinset.mpr hi, ?_⟩
      have hp := mul_pos hbpos (hr i (hIS hi))
      have hy' : dist y i < 30 * b * r i := hy
      nlinarith
    · exact fun m j hj z hz => hselected m i hi j hj z hz

end GC.MetricGeometry
