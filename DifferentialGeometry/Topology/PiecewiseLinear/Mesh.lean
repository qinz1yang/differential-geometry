/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Derived
import DifferentialGeometry.Topology.PiecewiseLinear.Star
import DifferentialGeometry.Topology.SimplicialComplex.GeometricCompactness
import Mathlib.Analysis.Normed.Module.Convex

open Set Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dist_centroid_le_of_mem (s : Finset E) (hs : s.Nonempty) {p : E}
    (hp : p ∈ convexHull ℝ (s : Set E)) :
    dist p (s.centroid ℝ id) ≤ ((s.card - 1 : ℝ) / s.card) * diam (s : Set E) := by
  classical
  obtain ⟨v, hv, hle⟩ := (convexOn_dist (s.centroid ℝ id)
    (convex_convexHull ℝ (s : Set E))).exists_ge_of_mem_convexHull (subset_convexHull ℝ _) hp
  refine hle.trans ?_
  have hcard : (0 : ℝ) < s.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hs)
  have hbd : Bornology.IsBounded (s : Set E) := s.finite_toSet.isBounded
  have hb : s.centroid ℝ id = (s.card : ℝ)⁻¹ • ∑ u ∈ s, u := by
    rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
      (Finset.sum_centroidWeights_eq_one_of_nonempty ℝ _ hs), Finset.smul_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [Finset.centroidWeights_apply]; rfl
  have hv' : v = (s.card : ℝ)⁻¹ • ∑ _u ∈ s, v := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hcard.ne',
      one_smul]
  have hvs : v ∈ s := Finset.mem_coe.mp hv
  rw [dist_eq_norm, hb]
  conv_lhs => rw [hv']
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, norm_inv, Real.norm_natCast]
  calc (s.card : ℝ)⁻¹ * ‖∑ u ∈ s, (v - u)‖
      ≤ (s.card : ℝ)⁻¹ * ∑ u ∈ s, ‖v - u‖ := by
        gcongr
        exact norm_sum_le _ _
    _ = (s.card : ℝ)⁻¹ * ∑ u ∈ s.erase v, ‖v - u‖ := by
        rw [← Finset.add_sum_erase s _ hvs, sub_self, norm_zero, zero_add]
    _ ≤ (s.card : ℝ)⁻¹ * ∑ _u ∈ s.erase v, diam (s : Set E) := by
        gcongr with u hu
        rw [← dist_eq_norm]
        exact dist_le_diam_of_mem hbd hv (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hu))
    _ = ((s.card - 1 : ℝ) / s.card) * diam (s : Set E) := by
        rw [Finset.sum_const, Finset.card_erase_of_mem hvs, nsmul_eq_mul,
          Nat.cast_sub (Finset.card_pos.mpr hs), Nat.cast_one, div_eq_inv_mul]
        ring

theorem dist_centroid_centroid_le {s t : Finset E} (hst : s ⊆ t) (hs : s.Nonempty) :
    dist (s.centroid ℝ id) (t.centroid ℝ id) ≤ ((t.card - 1 : ℝ) / t.card) * diam (t : Set E) :=
  dist_centroid_le_of_mem t (hs.mono hst)
    (convexHull_mono (Finset.coe_subset.mpr hst) (s.centroid_mem_convexHull hs))

theorem card_ratio_le {k N : ℕ} (hk : 0 < k) (hkN : k ≤ N + 1) :
    ((k - 1 : ℝ) / k) ≤ (N : ℝ) / (N + 1) := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hkN' : (k : ℝ) ≤ N + 1 := by exact_mod_cast hkN
  rw [div_le_div_iff₀ hk' (by positivity)]
  nlinarith

theorem IsFlag.card_le {K : Geometry.SimplicialComplex ℝ E} {d : Finset (Finset E)}
    (hd : IsFlag K d) {u : Finset E} (htop : ∀ s ∈ d, s ⊆ u) : d.card ≤ u.card := by
  classical
  have hmaps : Set.MapsTo Finset.card (d : Set (Finset E)) ((Finset.Icc 1 u.card : Finset ℕ) : Set
      ℕ) := by
    intro s hs
    rw [Finset.coe_Icc, mem_Icc]
    exact ⟨Finset.card_pos.mpr (K.nonempty_of_mem_faces (hd.mem_faces hs)),
      Finset.card_le_card (htop s hs)⟩
  have hinj : (d : Set (Finset E)).InjOn Finset.card := by
    intro s hs t ht h
    rcases hd.subset_or_subset hs ht with hst | hts
    · exact Finset.eq_of_subset_of_card_le hst h.ge
    · exact (Finset.eq_of_subset_of_card_le hts h.le).symm
  have := Finset.card_le_card_of_injOn Finset.card hmaps hinj
  simpa using this

section Derived

variable (K : Geometry.SimplicialComplex ℝ E) {c : Finset E → E}
  (hc : ∀ s ∈ K.faces, c s ∈ openSimplex s)

include hc

theorem card_le_of_mem_derived_faces [DecidableEq E] {N : ℕ} (hK : ∀ s ∈ K.faces, s.card ≤ N + 1)
    {f : Finset E} (hf : f ∈ (derived K hc).faces) : f.card ≤ N + 1 := by
  obtain ⟨d, hd, hne, rfl⟩ := hf
  obtain ⟨u, hu, htop⟩ := hd.exists_top hne
  exact Finset.card_image_le.trans ((hd.card_le htop).trans (hK u (hd.mem_faces hu)))

theorem finite_derived_faces [DecidableEq E] [Finite K.faces] : (derived K hc).faces.Finite := by
  have hfin : K.faces.Finite := Set.toFinite _
  have hsub : (derived K hc).faces ⊆
      (fun d : Finset (Finset E) => d.image c) '' {d | (d : Set (Finset E)) ⊆ K.faces} := by
    rintro f ⟨d, hd, -, rfl⟩
    exact ⟨d, hd.coe_subset_faces, rfl⟩
  refine Set.Finite.subset (Set.Finite.image _ ?_) hsub
  exact hfin.finite_subsets.preimage Finset.coe_injective.injOn

end Derived

instance [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] :
    Finite (barycentricSubdivision K).faces :=
  (finite_derived_faces K (centroid_mem_openSimplex_of_mem_faces K)).to_subtype

theorem card_le_of_mem_barycentricSubdivision_faces [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {N : ℕ} (hK : ∀ s ∈ K.faces, s.card ≤ N + 1)
    {f : Finset E} (hf : f ∈ (barycentricSubdivision K).faces) : f.card ≤ N + 1 :=
  card_le_of_mem_derived_faces K (centroid_mem_openSimplex_of_mem_faces K) hK hf

theorem exists_diam_le_of_mem_barycentricSubdivision_faces [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {N : ℕ} (hK : ∀ s ∈ K.faces, s.card ≤ N + 1)
    {f : Finset E} (hf : f ∈ (barycentricSubdivision K).faces) :
    ∃ u ∈ K.faces, diam (convexHull ℝ (f : Set E)) ≤
      ((N : ℝ) / (N + 1)) * diam (convexHull ℝ (u : Set E)) := by
  obtain ⟨d, hd, hne, rfl⟩ := hf
  obtain ⟨u, hu, htop⟩ := hd.exists_top hne
  refine ⟨u, hd.mem_faces hu, ?_⟩
  rw [convexHull_diam, convexHull_diam]
  have hbd : Bornology.IsBounded (u : Set E) := u.finite_toSet.isBounded
  have hN : (0 : ℝ) ≤ N / (N + 1) := by positivity
  refine diam_le_of_forall_dist_le (mul_nonneg hN diam_nonneg) ?_
  intro x hx y hy
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
  have key : ∀ s ∈ d, ∀ t ∈ d, s ⊆ t →
      dist (s.centroid ℝ id) (t.centroid ℝ id) ≤ (N / (N + 1)) * diam (u : Set E) := by
    intro s hs t ht hst
    have htK := hd.mem_faces ht
    calc dist (s.centroid ℝ id) (t.centroid ℝ id)
        ≤ ((t.card - 1 : ℝ) / t.card) * diam (t : Set E) :=
          dist_centroid_centroid_le hst (K.nonempty_of_mem_faces (hd.mem_faces hs))
      _ ≤ (N / (N + 1)) * diam (u : Set E) :=
          mul_le_mul (card_ratio_le (Finset.card_pos.mpr (K.nonempty_of_mem_faces htK)) (hK t htK))
            (diam_mono (Finset.coe_subset.mpr (htop t ht)) hbd) diam_nonneg hN
  rcases hd.subset_or_subset hs ht with hst | hts
  · exact key s hs t ht hst
  · rw [dist_comm]
    exact key t ht s hs hts

noncomputable def iteratedBarycentricSubdivision [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) : ℕ → Geometry.SimplicialComplex ℝ E
  | 0 => K
  | m + 1 => barycentricSubdivision (iteratedBarycentricSubdivision K m)

theorem iteratedBarycentricSubdivision_isSubdivision [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) (m : ℕ) :
    IsSubdivision (iteratedBarycentricSubdivision K m) K := by
  induction m with
  | zero => exact IsSubdivision.refl K
  | succ m ih => exact (barycentricSubdivision_isSubdivision _).trans ih

instance [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (m : ℕ) :
    Finite (iteratedBarycentricSubdivision K m).faces := by
  induction m with
  | zero => exact inferInstanceAs (Finite K.faces)
  | succ m _ =>
    exact inferInstanceAs (Finite (barycentricSubdivision (iteratedBarycentricSubdivision K
        m)).faces)

theorem card_le_of_mem_iteratedBarycentricSubdivision_faces [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {N : ℕ} (hK : ∀ s ∈ K.faces, s.card ≤ N + 1) (m : ℕ) :
    ∀ f ∈ (iteratedBarycentricSubdivision K m).faces, f.card ≤ N + 1 := by
  induction m with
  | zero => exact hK
  | succ m ih => exact fun f hf => card_le_of_mem_barycentricSubdivision_faces _ ih hf

theorem diam_le_of_mem_iteratedBarycentricSubdivision_faces [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {N : ℕ} (hK : ∀ s ∈ K.faces, s.card ≤ N + 1) {M : ℝ}
    (hM : ∀ s ∈ K.faces, diam (convexHull ℝ (s : Set E)) ≤ M) (m : ℕ) :
    ∀ f ∈ (iteratedBarycentricSubdivision K m).faces,
      diam (convexHull ℝ (f : Set E)) ≤ ((N : ℝ) / (N + 1)) ^ m * M := by
  induction m with
  | zero =>
    intro f hf
    rw [pow_zero, one_mul]
    exact hM f hf
  | succ m ih =>
    intro f hf
    obtain ⟨u, hu, hle⟩ := exists_diam_le_of_mem_barycentricSubdivision_faces _
      (card_le_of_mem_iteratedBarycentricSubdivision_faces K hK m) hf
    have hN : (0 : ℝ) ≤ N / (N + 1) := by positivity
    calc diam (convexHull ℝ (f : Set E))
        ≤ ((N : ℝ) / (N + 1)) * diam (convexHull ℝ (u : Set E)) := hle
      _ ≤ ((N : ℝ) / (N + 1)) * (((N : ℝ) / (N + 1)) ^ m * M) := by gcongr; exact ih u hu
      _ = ((N : ℝ) / (N + 1)) ^ (m + 1) * M := by ring

theorem exists_isSubdivision_diam_lt (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] {N : ℕ} (hK : ∀ s ∈ K.faces, s.card ≤ N + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      (∀ s ∈ K'.faces, s.card ≤ N + 1) ∧
      ∀ s ∈ K'.faces, diam (convexHull ℝ (s : Set E)) < ε := by
  classical
  obtain ⟨M, hM₀, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ K.faces, diam (convexHull ℝ (s : Set E)) ≤ M := by
    obtain ⟨M, hM⟩ := ((Set.toFinite K.faces).image
      fun s : Finset E => diam (convexHull ℝ (s : Set E))).bddAbove
    exact ⟨max M 0, le_max_right _ _,
      fun s hs => (hM (mem_image_of_mem _ hs)).trans (le_max_left _ _)⟩
  have hM₁ : (0 : ℝ) < M + 1 := by linarith
  have hr : (N : ℝ) / (N + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (div_pos hε hM₁) hr
  refine ⟨iteratedBarycentricSubdivision K m, iteratedBarycentricSubdivision_isSubdivision K m,
    Set.toFinite _, card_le_of_mem_iteratedBarycentricSubdivision_faces K hK m, fun s hs => ?_⟩
  have hrm : (0 : ℝ) ≤ ((N : ℝ) / (N + 1)) ^ m := by positivity
  calc diam (convexHull ℝ (s : Set E))
      ≤ ((N : ℝ) / (N + 1)) ^ m * M :=
        diam_le_of_mem_iteratedBarycentricSubdivision_faces K hK hM m s hs
    _ ≤ ((N : ℝ) / (N + 1)) ^ m * (M + 1) := by gcongr; linarith
    _ < ε := (lt_div_iff₀ hM₁).mp hm

theorem exists_isSubdivision_closedStars_subset_cover (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] {ι : Type*} (U : ι → Set E)
    (hU : ∀ i, IsOpen (((↑) : K.space → E) ⁻¹' U i)) (hcover : K.space ⊆ ⋃ i, U i) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      ∀ s ∈ R.faces, ∃ i, (⋃ v ∈ s, closedStar R v) ⊆ U i := by
  classical
  have hcover' : (univ : Set K.space) ⊆ ⋃ i, ((↑) : K.space → E) ⁻¹' U i := by
    intro x _
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover x.property)
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hcover'
  obtain ⟨N, hN⟩ := ((Set.toFinite K.faces).image (fun s : Finset E => s.card)).bddAbove
  have hcard : ∀ s ∈ K.faces, s.card ≤ N + 1 :=
    fun s hs => (hN (mem_image_of_mem _ hs)).trans (Nat.le_succ N)
  obtain ⟨R, hR, hfinite, -, hdiam⟩ := exists_isSubdivision_diam_lt K hcard (half_pos hδ)
  refine ⟨R, hR, hfinite, fun s hs => ?_⟩
  obtain ⟨v₀, hv₀⟩ := R.nonempty_of_mem_faces hs
  have hv₀s : v₀ ∈ convexHull ℝ (s : Set E) := subset_convexHull ℝ _ hv₀
  have hv₀K : v₀ ∈ K.space := hR.space_eq ▸ R.convexHull_subset_space hs hv₀s
  obtain ⟨i, hi⟩ := hleb ⟨v₀, hv₀K⟩ (mem_univ _)
  refine ⟨i, fun y hy => ?_⟩
  obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hy
  obtain ⟨t, ⟨ht, hvt⟩, hyt⟩ := mem_iUnion₂.mp hyv
  have hyK : y ∈ K.space := hR.space_eq ▸ R.convexHull_subset_space ht hyt
  have hys : dist y v < δ / 2 :=
    (dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull ℝ).isBounded hyt hvt).trans_lt
      (hdiam t ht)
  have hvs : dist v v₀ < δ / 2 :=
    (dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded
      (subset_convexHull ℝ _ hv) hv₀s).trans_lt (hdiam s hs)
  have hyball : (⟨y, hyK⟩ : K.space) ∈ ball ⟨v₀, hv₀K⟩ δ := by
    change dist y v₀ < δ
    exact (dist_triangle y v v₀).trans_lt (by linarith)
  exact hi hyball

end DifferentialGeometry.Topology.PiecewiseLinear
