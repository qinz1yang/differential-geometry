/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.FaceLink
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.PiecewiseLinear.RadialProjection
import DifferentialGeometry.Topology.PiecewiseLinear.StarAvoiding

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sum_inv_card_smul_eq_centroid {s : Finset E} (hs : s.Nonempty) :
    ∑ v ∈ s, ((s.card : ℝ))⁻¹ • v = s.centroid ℝ id := by
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _
    (Finset.sum_centroidWeights_eq_one_of_nonempty ℝ _ hs)]
  exact Finset.sum_congr rfl fun v _ => by rw [Finset.centroidWeights_apply]; rfl

theorem card_smul_centroid {s : Finset E} (hs : s.Nonempty) :
    (s.card : ℝ) • s.centroid ℝ id = ∑ v ∈ s, v := by
  have hcard : ((s.card : ℝ)) ≠ 0 := (Nat.cast_pos.mpr (Finset.card_pos.mpr hs)).ne'
  rw [← sum_inv_card_smul_eq_centroid hs, Finset.smul_sum]
  exact Finset.sum_congr rfl fun v _ => by rw [smul_smul, mul_inv_cancel₀ hcard, one_smul]

theorem card_add_card_smul_centroid_union [DecidableEq E] {e t : Finset E} (he : e.Nonempty)
    (ht : t.Nonempty) (hdj : Disjoint e t) :
    ((e.card : ℝ) + (t.card : ℝ)) • (e ∪ t).centroid ℝ id
      = (e.card : ℝ) • e.centroid ℝ id + (t.card : ℝ) • t.centroid ℝ id := by
  have hcard : (((e ∪ t).card : ℝ)) = (e.card : ℝ) + (t.card : ℝ) := by
    rw [Finset.card_union_of_disjoint hdj, Nat.cast_add]
  rw [← hcard, card_smul_centroid (he.mono Finset.subset_union_left), card_smul_centroid he,
    card_smul_centroid ht, Finset.sum_union hdj]

theorem smul_centroid_union [DecidableEq E] {e t : Finset E} (he : e.Nonempty) (ht : t.Nonempty)
    (hdj : Disjoint e t) (k : ℝ) :
    (k * (e.card : ℝ) + k * (t.card : ℝ)) • (e ∪ t).centroid ℝ id
      = (k * (e.card : ℝ)) • e.centroid ℝ id + (k * (t.card : ℝ)) • t.centroid ℝ id := by
  rw [← mul_add, mul_smul, card_add_card_smul_centroid_union he ht hdj, smul_add, smul_smul,
    smul_smul]

theorem centroid_add_smul_sub_centroid [DecidableEq E] {e s : Finset E} (he : e.Nonempty)
    (hes : e ⊂ s) :
    e.centroid ℝ id
        + ((((s \ e).card : ℝ))⁻¹ * (s.card : ℝ)) • (s.centroid ℝ id - e.centroid ℝ id)
      = (s \ e).centroid ℝ id := by
  obtain ⟨v, hvs, hve⟩ := Finset.exists_of_ssubset hes
  have hne : (s \ e).Nonempty := ⟨v, Finset.mem_sdiff.mpr ⟨hvs, hve⟩⟩
  have hb : (((s \ e).card : ℝ)) ≠ 0 := (Nat.cast_pos.mpr (Finset.card_pos.mpr hne)).ne'
  have hdj : Disjoint e (s \ e) := Finset.disjoint_sdiff
  have hunion : e ∪ (s \ e) = s := Finset.union_sdiff_of_subset hes.subset
  have hC := card_add_card_smul_centroid_union he hne hdj
  rw [hunion] at hC
  have hcard : (s.card : ℝ) = (e.card : ℝ) + ((s \ e).card : ℝ) := by
    have hcu : (e ∪ (s \ e)).card = e.card + (s \ e).card := Finset.card_union_of_disjoint hdj
    rw [hunion] at hcu
    exact_mod_cast hcu
  have hstep : ((e.card : ℝ) + ((s \ e).card : ℝ)) • (s.centroid ℝ id - e.centroid ℝ id)
      = ((s \ e).card : ℝ) • ((s \ e).centroid ℝ id - e.centroid ℝ id) := by
    simp only [smul_sub]
    rw [hC, add_smul]
    abel
  rw [hcard, mul_smul, hstep, inv_smul_smul₀ hb]
  abel

def upperLinkFaces [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) (e : Finset E) :
    Set (Finset E) :=
  {u | ∃ d : Finset (Finset E), IsFlag K d ∧ d.Nonempty ∧ (∀ s ∈ d, e ⊂ s) ∧
    u = d.image fun s => s.centroid ℝ id}

theorem upperLinkFaces_subset [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E)
    (e : Finset E) : upperLinkFaces K e ⊆ (barycentricSubdivision K).faces := by
  rintro f ⟨d, hd, hne, -, rfl⟩
  exact ⟨d, hd, hne, rfl⟩

def upperLink [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) (e : Finset E) :
    Geometry.SimplicialComplex ℝ E where
  faces := upperLinkFaces K e
  isRelLowerSet_faces := by
    rintro f ⟨d, hd, hne, hlt, rfl⟩
    refine ⟨hne.image _, fun g hgf hg => ?_⟩
    refine ⟨d.filter fun s => s.centroid ℝ id ∈ g, hd.mono (Finset.filter_subset _ _), ?_, ?_,
      (image_filter_mem_eq hgf).symm⟩
    · obtain ⟨p, hp⟩ := hg
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (hgf hp)
      exact ⟨s, Finset.mem_filter.mpr ⟨hs, hp⟩⟩
    · exact fun s hs => hlt s (Finset.mem_of_mem_filter s hs)
  indep hf := (barycentricSubdivision K).indep (upperLinkFaces_subset K e hf)
  inter_subset_convexHull hf hg := (barycentricSubdivision K).inter_subset_convexHull
    (upperLinkFaces_subset K e hf) (upperLinkFaces_subset K e hg)

theorem mem_upperLink_faces_iff [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E)
    (e : Finset E) {u : Finset E} :
    u ∈ (upperLink K e).faces ↔ ∃ d : Finset (Finset E), IsFlag K d ∧ d.Nonempty ∧
      (∀ s ∈ d, e ⊂ s) ∧ u = d.image fun s => s.centroid ℝ id := Iff.rfl

theorem upperLink_faces_subset [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E)
    (e : Finset E) : (upperLink K e).faces ⊆ (barycentricSubdivision K).faces :=
  upperLinkFaces_subset K e

theorem upperLink_faces_finite [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (e : Finset E) : (upperLink K e).faces.Finite :=
  (Set.toFinite (barycentricSubdivision K).faces).subset (upperLink_faces_subset K e)

theorem upperLink_faces_subset_geometricLink [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) {e : Finset E} (he : e ∈ K.faces) :
    (upperLink K e).faces ⊆
      (SimplicialComplex.geometricLink (barycentricSubdivision K) {e.centroid ℝ id}).faces := by
  rintro f ⟨d, hd, hne, hlt, rfl⟩
  refine (SimplicialComplex.mem_geometricLink_singleton _ _ _).mpr ⟨hne.image _, ?_, ?_⟩
  · intro hmem
    obtain ⟨s, hs, hcs⟩ := Finset.mem_image.mp hmem
    exact absurd (injOn_faces_of_mem_openSimplex K (centroid_mem_openSimplex_of_mem_faces K)
      (hd.mem_faces hs) he hcs).symm (hlt s hs).ne
  · refine ⟨insert e d, ⟨fun s hs => ?_, fun s hs t ht => ?_⟩, Finset.insert_nonempty e d,
      (Finset.image_insert _ _ _).symm⟩
    · rcases Finset.mem_insert.mp hs with rfl | hs'
      · exact he
      · exact hd.mem_faces hs'
    · rcases Finset.mem_insert.mp hs with rfl | hs'
      · rcases Finset.mem_insert.mp ht with rfl | ht'
        · exact Or.inl (Finset.Subset.refl _)
        · exact Or.inl (hlt t ht').subset
      · rcases Finset.mem_insert.mp ht with rfl | ht'
        · exact Or.inr (hlt s hs').subset
        · exact hd.subset_or_subset hs' ht'

theorem exists_isPLHomeomorphOn_upperLink_of_faces_finite [FiniteDimensional ℝ E]
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) {e : Finset E} (he : e ∈ K.faces)
    (hfinite : (upperLink K e).faces.Finite) :
    ∃ f : E → E, IsPLHomeomorphOn f (upperLink K e).space
      (SimplicialComplex.geometricLink K e).space := by
  let _ : Finite (upperLink K e).faces := hfinite.to_subtype
  have hene : e.Nonempty := K.nonempty_of_mem_faces he
  have hapos : (0 : ℝ) < (e.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hene)
  have hlinksub : (SimplicialComplex.geometricLink K e).faces ⊆ (starAvoiding K e).faces := by
    intro r hr
    obtain ⟨hrne, hdisj, hunion⟩ := (mem_geometricLink_faces_iff K).mp hr
    refine ⟨K.down_closed hunion Finset.subset_union_right hrne, ?_, ?_⟩
    · rwa [Finset.union_comm]
    · intro hsub
      obtain ⟨v, hv⟩ := hene
      exact Finset.disjoint_left.mp hdisj hv (hsub hv)
  have hrayL := ((isConeBase_starAvoiding K he
    (centroid_mem_openSimplex hene)).of_faces_subset hlinksub).radial
  have hL' : IsConeBase (e.centroid ℝ id) (upperLink K e) :=
    (isConeBase_geometricLink (barycentricSubdivision K)).of_faces_subset
      (upperLink_faces_subset_geometricLink K he)
  refine exists_isPLHomeomorphOn_of_radial (e.centroid ℝ id) _ _ hrayL hL' ?_ ?_
  · rintro f ⟨d, hd, hne, hlt, rfl⟩
    obtain ⟨utop, hutop, htop⟩ := hd.exists_top hne
    obtain ⟨v0, hv0s, hv0e⟩ := Finset.exists_of_ssubset (hlt utop hutop)
    refine ⟨utop \ e, (mem_geometricLink_faces_iff K).mpr
      ⟨⟨v0, Finset.mem_sdiff.mpr ⟨hv0s, hv0e⟩⟩, Finset.disjoint_sdiff, ?_⟩, ?_⟩
    · rw [Finset.union_sdiff_of_subset (hlt utop hutop).subset]
      exact hd.mem_faces hutop
    · intro w hw
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨v1, hv1s, hv1e⟩ := Finset.exists_of_ssubset (hlt s hs)
      have hsne : (s \ e).Nonempty := ⟨v1, Finset.mem_sdiff.mpr ⟨hv1s, hv1e⟩⟩
      refine ⟨(((s \ e).card : ℝ))⁻¹ * (s.card : ℝ), mul_pos
        (inv_pos.mpr (Nat.cast_pos.mpr (Finset.card_pos.mpr hsne)))
        (Nat.cast_pos.mpr (Finset.card_pos.mpr
          (K.nonempty_of_mem_faces (hd.mem_faces hs)))), ?_⟩
      rw [centroid_add_smul_sub_centroid hene (hlt s hs)]
      refine convexHull_mono (fun q hq => ?_)
        (openSimplex_subset_convexHull _ (centroid_mem_openSimplex hsne))
      simp only [Finset.mem_coe, Finset.mem_sdiff] at hq ⊢
      exact ⟨htop s hs hq.1, hq.2⟩
  · intro x hx
    obtain ⟨r, hr, hxr⟩ := (SimplicialComplex.geometricLink K e).mem_space_iff.mp hx
    obtain ⟨hrne, hdisj, hunion⟩ := (mem_geometricLink_faces_iff K).mp hr
    obtain ⟨r₀, hr₀r, hr₀ne, hxr₀⟩ := exists_openSimplex_of_mem_convexHull hxr
    have hrK : r ∈ K.faces := K.down_closed hunion Finset.subset_union_right hrne
    have hr₀K : r₀ ∈ K.faces := K.down_closed hrK hr₀r hr₀ne
    obtain ⟨d₀, hd₀, hd₀ne, hd₀sub, hxd₀⟩ :=
      exists_flag_of_mem_openSimplex K (centroid_mem_openSimplex_of_mem_faces K) hr₀K hxr₀
    obtain ⟨wt, hw0, hw1, hwx⟩ := mem_convexHull_iff_exists_weights.mp hxd₀
    have hinj : Set.InjOn (fun s : Finset E => s.centroid ℝ id) (d₀ : Set (Finset E)) :=
      IsFlag.injOn K (centroid_mem_openSimplex_of_mem_faces K) hd₀
    rw [Finset.sum_image hinj] at hw1 hwx
    have hcardpos : ∀ t ∈ d₀, (0 : ℝ) < (t.card : ℝ) := fun t ht =>
      Nat.cast_pos.mpr (Finset.card_pos.mpr (K.nonempty_of_mem_faces (hd₀.mem_faces ht)))
    have hlam0 : ∀ t ∈ d₀, 0 ≤ wt (t.centroid ℝ id) := fun t ht =>
      hw0 _ (Finset.mem_image_of_mem _ ht)
    obtain ⟨S, hSdef⟩ : ∃ S : ℝ, ∑ t ∈ d₀, wt (t.centroid ℝ id) / (t.card : ℝ) = S := ⟨_, rfl⟩
    have hSpos : 0 < S := by
      rw [← hSdef]
      have hlt : ∑ _t ∈ d₀, (0 : ℝ) < ∑ t ∈ d₀, wt (t.centroid ℝ id) := by
        rw [Finset.sum_const_zero, hw1]
        exact one_pos
      obtain ⟨t₀, ht₀, ht₀pos⟩ := Finset.exists_lt_of_sum_lt hlt
      exact Finset.sum_pos' (fun t ht => div_nonneg (hlam0 t ht) (hcardpos t ht).le)
        ⟨t₀, ht₀, div_pos ht₀pos (hcardpos t₀ ht₀)⟩
    have hden : (0 : ℝ) < 1 + (e.card : ℝ) * S :=
      add_pos_of_pos_of_nonneg one_pos (mul_nonneg hapos.le hSpos.le)
    obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, (1 + (e.card : ℝ) * S)⁻¹ = σ := ⟨_, rfl⟩
    have hσpos : 0 < σ := by
      rw [← hσdef]
      exact inv_pos.mpr hden
    have hσmul : σ * (1 + (e.card : ℝ) * S) = 1 := by
      rw [← hσdef]
      exact inv_mul_cancel₀ hden.ne'
    have hone : (1 : ℝ) - σ = σ * (e.card : ℝ) * S := by
      have h : σ + σ * (e.card : ℝ) * S = σ * (1 + (e.card : ℝ) * S) := by ring
      rw [hσmul] at h
      linarith
    have hkey : ∀ t ∈ d₀,
        σ * wt (t.centroid ℝ id) / (t.card : ℝ) * (e.card : ℝ)
            = σ * (e.card : ℝ) * (wt (t.centroid ℝ id) / (t.card : ℝ)) ∧
          σ * wt (t.centroid ℝ id) / (t.card : ℝ) * (t.card : ℝ)
            = σ * wt (t.centroid ℝ id) := by
      intro t ht
      have hcne : ((t.card : ℝ)) ≠ 0 := (hcardpos t ht).ne'
      exact ⟨by ring, by field_simp⟩
    have hstep : ∀ t ∈ d₀, (σ * wt (t.centroid ℝ id) / (t.card : ℝ) * (e.card : ℝ)
          + σ * wt (t.centroid ℝ id) / (t.card : ℝ) * (t.card : ℝ)) • (e ∪ t).centroid ℝ id
        = (σ * (e.card : ℝ) * (wt (t.centroid ℝ id) / (t.card : ℝ))) • e.centroid ℝ id
          + (σ * wt (t.centroid ℝ id)) • t.centroid ℝ id := by
      intro t ht
      rw [smul_centroid_union hene (K.nonempty_of_mem_faces (hd₀.mem_faces ht))
        (hdisj.mono_right ((hd₀sub t ht).trans hr₀r)), (hkey t ht).1, (hkey t ht).2]
    have hsumrhs : ∑ t ∈ d₀, ((σ * (e.card : ℝ) * (wt (t.centroid ℝ id) / (t.card : ℝ)))
          • e.centroid ℝ id + (σ * wt (t.centroid ℝ id)) • t.centroid ℝ id)
        = (σ * (e.card : ℝ) * S) • e.centroid ℝ id + σ • x := by
      rw [Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.mul_sum, hSdef, ← hwx,
        Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun t _ =>
        mul_smul σ (wt (t.centroid ℝ id)) (t.centroid ℝ id)
    have hfinal : e.centroid ℝ id + σ • (x - e.centroid ℝ id)
        = ∑ t ∈ d₀, (σ * wt (t.centroid ℝ id) / (t.card : ℝ) * (e.card : ℝ)
            + σ * wt (t.centroid ℝ id) / (t.card : ℝ) * (t.card : ℝ))
              • (e ∪ t).centroid ℝ id := by
      rw [Finset.sum_congr rfl hstep, hsumrhs, add_smul_sub_eq_combo, hone]
    have hdflag : IsFlag K (d₀.image fun t => e ∪ t) := by
      refine ⟨fun s hs => ?_, fun s hs t ht => ?_⟩
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
        exact K.down_closed hunion (Finset.union_subset_union (Finset.Subset.refl e)
          ((hd₀sub t ht).trans hr₀r)) (hene.mono Finset.subset_union_left)
      · obtain ⟨s', hs', rfl⟩ := Finset.mem_image.mp hs
        obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht
        rcases hd₀.subset_or_subset hs' ht' with h | h
        · exact Or.inl (Finset.union_subset_union (Finset.Subset.refl e) h)
        · exact Or.inr (Finset.union_subset_union (Finset.Subset.refl e) h)
    have hdlt : ∀ s ∈ d₀.image fun t => e ∪ t, e ⊂ s := by
      intro s hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, fun heq => ?_⟩
      obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces (hd₀.mem_faces ht)
      have hvu : v ∈ e ∪ t := Finset.mem_union_right _ hv
      rw [← heq] at hvu
      exact Finset.disjoint_left.mp (hdisj.mono_right ((hd₀sub t ht).trans hr₀r)) hvu hv
    refine ⟨σ, hσpos, ?_⟩
    rw [hfinal]
    refine (upperLink K e).convexHull_subset_space
      ⟨d₀.image fun t => e ∪ t, hdflag, hd₀ne.image _, hdlt, rfl⟩
      ((convex_convexHull ℝ _).sum_mem (fun t ht => add_nonneg
        (mul_nonneg (div_nonneg (mul_nonneg hσpos.le (hlam0 t ht)) (hcardpos t ht).le) hapos.le)
        (mul_nonneg (div_nonneg (mul_nonneg hσpos.le (hlam0 t ht)) (hcardpos t ht).le)
          (hcardpos t ht).le)) ?_ (fun t ht => subset_convexHull ℝ _ (Finset.mem_coe.mpr
            (Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ ht)))))
    have hcongr : ∀ t ∈ d₀, σ * wt (t.centroid ℝ id) / (t.card : ℝ) * (e.card : ℝ)
        + σ * wt (t.centroid ℝ id) / (t.card : ℝ) * (t.card : ℝ)
        = σ * (e.card : ℝ) * (wt (t.centroid ℝ id) / (t.card : ℝ))
          + σ * wt (t.centroid ℝ id) := fun t ht => by rw [(hkey t ht).1, (hkey t ht).2]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hSdef, hw1, mul_one]
    linarith

theorem exists_isPLHomeomorphOn_upperLink [FiniteDimensional ℝ E] [DecidableEq E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {e : Finset E} (he : e ∈ K.faces) :
    ∃ f : E → E, IsPLHomeomorphOn f (upperLink K e).space
      (SimplicialComplex.geometricLink K e).space :=
  exists_isPLHomeomorphOn_upperLink_of_faces_finite K he (upperLink_faces_finite K e)

end DifferentialGeometry.Topology.PiecewiseLinear
