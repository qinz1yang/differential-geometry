import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Coordinates.BarycentricChain
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Coordinates.BarycentricWeights
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Instances.Real.Lemmas

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Topology Filter

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq ι] in
theorem centroid_sub_eq_inv_smul_sum (s : Finset ι) (hs : s.Nonempty) (v : ι → E) (y : E) :
    s.centroid ℝ v - y = (s.card : ℝ)⁻¹ • ∑ i ∈ s, (v i - y) := by
  simpa only [vsub_eq_sub] using
    (s.centroid_vsub_const ℝ hs).trans
      (centroid_eq_card_inv_smul_sum s hs (fun i => v i -ᵥ y))

omit [DecidableEq ι] in
theorem dist_centroid_le (s : Finset ι) (hs : s.Nonempty) (v : ι → E) (y : E) {D : ℝ}
    (hD : ∀ i ∈ s, dist (v i) y ≤ D) : dist (s.centroid ℝ v) y ≤ D := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs)
  rw [dist_eq_norm, centroid_sub_eq_inv_smul_sum s hs v y, norm_smul,
    Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  calc
    (s.card : ℝ)⁻¹ * ‖∑ i ∈ s, (v i - y)‖ ≤
        (s.card : ℝ)⁻¹ * ∑ i ∈ s, ‖v i - y‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ (s.card : ℝ)⁻¹ * ∑ _i ∈ s, D := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i hi => by simpa only [dist_eq_norm] using hD i hi))
      (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = D := by rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

omit [DecidableEq ι] in
theorem dist_centroids_le_of_subset {s t : Finset ι} (hs : s.Nonempty) (hst : s ⊆ t)
    (v : ι → E) {D : ℝ} (hD : ∀ i ∈ t, ∀ j ∈ t, dist (v i) (v j) ≤ D) :
    dist (s.centroid ℝ v) (t.centroid ℝ v) ≤
      (((t.card : ℝ) - (s.card : ℝ)) / (t.card : ℝ)) * D := by
  classical
  have ht : t.Nonempty := hs.mono hst
  have hs0 : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs)
  let c := s.centroid ℝ v
  have hzero : ∑ i ∈ s, (v i - c) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
    dsimp only [c]
    rw [centroid_eq_card_inv_smul_sum s hs v, smul_inv_smul₀ hs0, sub_self]
  have hsum : ∑ i ∈ t, (v i - c) = ∑ i ∈ t \ s, (v i - c) := by
    have h := Finset.sum_sdiff (f := fun i => v i - c) hst
    simpa only [hzero, add_zero] using h.symm
  have hc (i : ι) (hi : i ∈ t) : ‖v i - c‖ ≤ D := by
    rw [← dist_eq_norm, dist_comm]
    exact dist_centroid_le s hs v (v i) (fun j hj => hD j (hst hj) i hi)
  rw [dist_comm, dist_eq_norm, centroid_sub_eq_inv_smul_sum t ht v c, hsum,
    norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  calc
    (t.card : ℝ)⁻¹ * ‖∑ i ∈ t \ s, (v i - c)‖ ≤
        (t.card : ℝ)⁻¹ * ∑ i ∈ t \ s, ‖v i - c‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ (t.card : ℝ)⁻¹ * ∑ _i ∈ t \ s, D := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i hi => hc i (Finset.mem_sdiff.mp hi).1))
      (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (((t.card : ℝ) - (s.card : ℝ)) / (t.card : ℝ)) * D := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff,
        Finset.inter_eq_left.mpr hst, Nat.cast_sub (Finset.card_le_card hst)]
      ring

omit [DecidableEq ι] in
theorem dist_centroids_le_meshFactor {s t : Finset ι} (hs : s.Nonempty) (hst : s ⊆ t)
    (v : ι → E) {D : ℝ} (hD : ∀ i ∈ t, ∀ j ∈ t, dist (v i) (v j) ≤ D)
    {d : ℕ} (hd : t.card ≤ d + 1) :
    dist (s.centroid ℝ v) (t.centroid ℝ v) ≤ (d : ℝ) / (d + 1) * D := by
  classical
  have ht : t.Nonempty := hs.mono hst
  have hs1 : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have htpos : (0 : ℝ) < t.card := Nat.cast_pos.mpr (Finset.card_pos.mpr ht)
  have htd : (t.card : ℝ) ≤ d + 1 := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d + 1 := by positivity
  have hfactor : ((t.card : ℝ) - (s.card : ℝ)) / (t.card : ℝ) ≤ (d : ℝ) / (d + 1) := by
    apply (div_le_div_iff₀ htpos hdpos).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) hdpos.le]
  obtain ⟨i, hi⟩ := ht
  have hD0 : 0 ≤ D := by simpa only [dist_self] using hD i hi i hi
  exact (dist_centroids_le_of_subset hs hst v hD).trans (mul_le_mul_of_nonneg_right hfactor hD0)

omit [DecidableEq ι] in
theorem isFaceChain.dist_centroids_le {C : Finset (Finset ι)} (hC : isFaceChain C)
    (v : ι → E) {T : Finset ι} {d : ℕ} (hd : T.card ≤ d + 1)
    (hT : ∀ s ∈ C, s ⊆ T) {D : ℝ}
    (hD : ∀ i ∈ T, ∀ j ∈ T, dist (v i) (v j) ≤ D)
    {s t : Finset ι} (hs : s ∈ C) (ht : t ∈ C) :
    dist (s.centroid ℝ v) (t.centroid ℝ v) ≤ (d : ℝ) / (d + 1) * D := by
  classical
  rcases hC.2 s hs t ht with hst | hts
  · exact dist_centroids_le_meshFactor (hC.1 s hs) hst v
      (fun i hi j hj => hD i (hT t ht hi) j (hT t ht hj))
      ((Finset.card_le_card (hT t ht)).trans hd)
  · rw [dist_comm]
    exact dist_centroids_le_meshFactor (hC.1 t ht) hts v
      (fun i hi j hj => hD i (hT s hs hi) j (hT s hs hj))
      ((Finset.card_le_card (hT s hs)).trans hd)

omit [DecidableEq ι] in
theorem isFaceChain.diam_convexHull_centroids_le {C : Finset (Finset ι)} (hC : isFaceChain C)
    (v : ι → E) {T : Finset ι} {d : ℕ} (hd : T.card ≤ d + 1)
    (hT : ∀ s ∈ C, s ⊆ T) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ i ∈ T, ∀ j ∈ T, dist (v i) (v j) ≤ D) :
    diam (convexHull ℝ ((fun s : Finset ι => s.centroid ℝ v) '' (C : Set (Finset ι)))) ≤
      (d : ℝ) / (d + 1) * D := by
  classical
  rw [convexHull_diam]
  apply diam_le_of_forall_dist_le (mul_nonneg (by positivity) hD0)
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
  exact hC.dist_centroids_le v hd hT hD hs ht

omit [DecidableEq ι] in
theorem isFaceChain.diam_convexHull_centroids_le_finrank [FiniteDimensional ℝ E]
    {C : Finset (Finset ι)} (hC : isFaceChain C) (v : ι → E) {T : Finset ι}
    (hv : AffineIndependent ℝ (fun i : T => v i)) (hT : ∀ s ∈ C, s ⊆ T)
    {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ i ∈ T, ∀ j ∈ T, dist (v i) (v j) ≤ D) :
    diam (convexHull ℝ ((fun s : Finset ι => s.centroid ℝ v) '' (C : Set (Finset ι)))) ≤
      (Module.finrank ℝ E : ℝ) / (Module.finrank ℝ E + 1) * D := by
  classical
  apply hC.diam_convexHull_centroids_le v _ hT hD0 hD
  simpa only [Fintype.card_coe] using hv.card_le_finrank_succ.trans
    (Nat.add_le_add_right (Submodule.finrank_le _) 1)

theorem tendsto_barycentric_mesh_bound (d : ℕ) (D : ℝ) :
    Tendsto (fun n : ℕ => ((d : ℝ) / (d + 1)) ^ n * D) atTop (𝓝 0) := by
  have hr0 : (0 : ℝ) ≤ (d : ℝ) / (d + 1) := by positivity
  have hr1 : (d : ℝ) / (d + 1) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    linarith
  simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const D

theorem tendsto_mesh_of_barycentric_contraction (d : ℕ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, a (n + 1) ≤ (d : ℝ) / (d + 1) * a n) :
    Tendsto a atTop (𝓝 0) := by
  have hbound (n : ℕ) : a n ≤ ((d : ℝ) / (d + 1)) ^ n * a 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        a (n + 1) ≤ (d : ℝ) / (d + 1) * a n := hstep n
        _ ≤ (d : ℝ) / (d + 1) * (((d : ℝ) / (d + 1)) ^ n * a 0) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = ((d : ℝ) / (d + 1)) ^ (n + 1) * a 0 := by rw [pow_succ]; ring
  exact squeeze_zero ha hbound (tendsto_barycentric_mesh_bound d (a 0))

theorem exists_barycentric_mesh_bound_lt (d : ℕ) (D : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ((d : ℝ) / (d + 1)) ^ n * D < ε :=
  eventually_atTop.mp ((tendsto_barycentric_mesh_bound d D).eventually (gt_mem_nhds hε))

end DifferentialGeometry.Topology.Engulfing
