/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.IsCombinatorialManifoldOfLocallyFinitePLPieceIn
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerived
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.PiecewiseLinear.LocallyFiniteSplittingDisks
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Depth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def depthKeep (K : Geometry.SimplicialComplex ℝ E) (m : Finset E → ℕ) (k : ℕ) :
    Set (Finset E) :=
  {s | ∀ σ ∈ K.faces, k < m σ →
    Disjoint (convexHull ℝ (s : Set E)) (convexHull ℝ (σ : Set E))}

theorem finite_setOf_faces_inter_nonempty {K : Geometry.SimplicialComplex ℝ E}
    (hK : LocallyFinite fun s : K.faces =>
      (Subtype.val : K.space → E) ⁻¹' convexHull ℝ ((s : Finset E) : Set E))
    {σ : Finset E} (hσ : σ ∈ K.faces) :
    {τ | τ ∈ K.faces ∧
      (convexHull ℝ (τ : Set E) ∩ convexHull ℝ (σ : Set E)).Nonempty}.Finite := by
  have hC : IsCompact ((Subtype.val : K.space → E) ⁻¹' convexHull ℝ (σ : Set E)) := by
    rw [Subtype.isCompact_iff, image_preimage_eq_iff.mpr]
    · exact σ.finite_toSet.isCompact_convexHull ℝ
    · intro x hx
      exact ⟨⟨x, K.convexHull_subset_space hσ hx⟩, rfl⟩
  refine ((hK.finite_nonempty_inter_compact hC).image Subtype.val).subset ?_
  rintro τ ⟨hτ, p, hpτ, hpσ⟩
  exact ⟨⟨τ, hτ⟩, ⟨⟨p, K.convexHull_subset_space hτ hpτ⟩, hpτ, hpσ⟩, rfl⟩

theorem exists_mem_nhds_finite_setOf_faces_inter_nonempty {K : Geometry.SimplicialComplex ℝ E}
    (hK : LocallyFinite fun s : K.faces =>
      (Subtype.val : K.space → E) ⁻¹' convexHull ℝ ((s : Finset E) : Set E))
    {x : E} (hx : x ∈ K.space) :
    ∃ W ∈ 𝓝 x, {τ | τ ∈ K.faces ∧ (convexHull ℝ (τ : Set E) ∩ W).Nonempty}.Finite := by
  obtain ⟨W', hW', hfin⟩ := hK ⟨x, hx⟩
  obtain ⟨W, hW, hWW'⟩ := (mem_nhds_subtype K.space ⟨x, hx⟩ W').mp hW'
  refine ⟨W, hW, (hfin.image Subtype.val).subset ?_⟩
  rintro τ ⟨hτ, p, hpτ, hpW⟩
  exact ⟨⟨τ, hτ⟩, ⟨⟨p, K.convexHull_subset_space hτ hpτ⟩, hpτ, hWW' hpW⟩, rfl⟩

variable [DecidableEq E]

theorem diam_convexHull_image_centroid_le (K : Geometry.SimplicialComplex ℝ E) {N : ℕ}
    (hN : ∀ s ∈ K.faces, s.card ≤ N + 1) {d : Finset (Finset E)} (hd : IsFlag K d)
    (hne : d.Nonempty) {u : Finset E} (hu : u ∈ d) (htop : ∀ s ∈ d, s ⊆ u) :
    Metric.diam (convexHull ℝ ((d.image fun s => s.centroid ℝ id : Finset E) : Set E)) ≤
      ((N : ℝ) / (N + 1)) * Metric.diam (convexHull ℝ (u : Set E)) := by
  have hdu : IsFlag (subcomplexGeneratedBy K {u}) d :=
    ⟨fun s hs => ⟨u, ⟨hd.mem_faces hu, Set.mem_singleton u⟩, htop s hs,
      K.nonempty_of_mem_faces (hd.mem_faces hs)⟩, hd.2⟩
  obtain ⟨u', hu', hle⟩ := exists_diam_le_of_mem_barycentricSubdivision_faces
    (subcomplexGeneratedBy K {u})
    (fun s hs => hN s (subcomplexGeneratedBy_faces_subset K {u} hs)) ⟨d, hdu, hne, rfl⟩
  obtain ⟨t, ⟨-, htu⟩, hu't, -⟩ := hu'
  rw [Set.mem_singleton_iff] at htu
  subst htu
  refine hle.trans (mul_le_mul_of_nonneg_left (Metric.diam_mono
    (convexHull_mono (Finset.coe_subset.mpr hu't))
    (t.finite_toSet.isCompact_convexHull ℝ).isBounded) (by positivity))

noncomputable def depthSubdivision (K : Geometry.SimplicialComplex ℝ E) (m : Finset E → ℕ)
    (k : ℕ) : Geometry.SimplicialComplex ℝ E :=
  Nat.rec (motive := fun _ => Geometry.SimplicialComplex ℝ E) K
    (fun j D => relDerived (subcomplexGeneratedBy_faces_subset D (depthKeep K m j))
      (IsSubdivision.refl _) (centroid_mem_openSimplex_of_mem_faces D)) k

variable (K : Geometry.SimplicialComplex ℝ E) (m : Finset E → ℕ)

theorem depthSubdivision_zero : depthSubdivision K m 0 = K :=
  rfl

theorem mem_depthSubdivision_succ_faces_iff (k : ℕ) {f : Finset E} :
    f ∈ (depthSubdivision K m (k + 1)).faces ↔ ∃ (τ : Finset E) (d : Finset (Finset E)),
      IsRelFace (depthSubdivision K m k)
        (subcomplexGeneratedBy (depthSubdivision K m k) (depthKeep K m k))
        (subcomplexGeneratedBy (depthSubdivision K m k) (depthKeep K m k)) τ d ∧
      f = τ ∪ d.image fun s => s.centroid ℝ id :=
  Iff.rfl

theorem depthSubdivision_succ_isSubdivision (k : ℕ) :
    IsSubdivision (depthSubdivision K m (k + 1)) (depthSubdivision K m k) :=
  relDerived_isSubdivision
    (subcomplexGeneratedBy_faces_subset (depthSubdivision K m k) (depthKeep K m k))
    (IsSubdivision.refl _) (centroid_mem_openSimplex_of_mem_faces (depthSubdivision K m k))

theorem depthSubdivision_isSubdivision (k : ℕ) : IsSubdivision (depthSubdivision K m k) K := by
  induction k with
  | zero => exact IsSubdivision.refl K
  | succ k ih => exact (depthSubdivision_succ_isSubdivision K m k).trans ih

theorem mem_depthSubdivision_succ_of_mem_depthKeep (k : ℕ) {s : Finset E}
    (hs : s ∈ (depthSubdivision K m k).faces) (hkeep : s ∈ depthKeep K m k) :
    s ∈ (depthSubdivision K m (k + 1)).faces :=
  faces_subset_relDerived
    (subcomplexGeneratedBy_faces_subset (depthSubdivision K m k) (depthKeep K m k))
    (IsSubdivision.refl _) (centroid_mem_openSimplex_of_mem_faces (depthSubdivision K m k))
    ⟨s, ⟨hs, hkeep⟩, Finset.Subset.rfl, (depthSubdivision K m k).nonempty_of_mem_faces hs⟩

omit [DecidableEq E] in
theorem mem_depthKeep_of_mem_subcomplexGeneratedBy {D : Geometry.SimplicialComplex ℝ E}
    (k : ℕ) {s : Finset E} (hs : s ∈ (subcomplexGeneratedBy D (depthKeep K m k)).faces) :
    s ∈ depthKeep K m k := by
  obtain ⟨t, ⟨-, ht⟩, hst, -⟩ := hs
  exact fun σ hσ hkσ => (ht σ hσ hkσ).mono_left (convexHull_mono (Finset.coe_subset.mpr hst))

theorem convexHull_subset_of_mem_depthSubdivision_succ_faces (k : ℕ) {σ : Finset E}
    (hσ : σ ∈ K.faces) {τ : Finset E} {d : Finset (Finset E)}
    (hfσ : convexHull ℝ ((τ ∪ d.image fun s => s.centroid ℝ id : Finset E) : Set E) ⊆
      convexHull ℝ (σ : Set E))
    (hd : IsFlag (depthSubdivision K m k) d) {s : Finset E} (hs : s ∈ d) :
    convexHull ℝ (s : Set E) ⊆ convexHull ℝ (σ : Set E) := by
  have hsK := hd.mem_faces hs
  exact (depthSubdivision_isSubdivision K m k).convexHull_subset_of_mem_openSimplex hσ hsK
    (centroid_mem_openSimplex ((depthSubdivision K m k).nonempty_of_mem_faces hsK))
    (hfσ (subset_convexHull ℝ _ (Finset.mem_coe.mpr
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)))))

theorem finite_setOf_depthSubdivision_faces_subset {σ : Finset E} (hσ : σ ∈ K.faces) (k : ℕ) :
    {f | f ∈ (depthSubdivision K m k).faces ∧
      convexHull ℝ (f : Set E) ⊆ convexHull ℝ (σ : Set E)}.Finite := by
  induction k with
  | zero =>
    refine σ.powerset.finite_toSet.subset ?_
    rintro f ⟨hf, hfσ⟩
    rw [Finset.coe_powerset, mem_preimage, mem_powerset_iff, Finset.coe_subset]
    intro v hv
    exact mem_of_mem_convexHull_of_singleton_mem K
      (K.down_closed hf (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)) hσ
      (hfσ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)))
  | succ k ih =>
    refine ((((insert ∅ ih.toFinset) ×ˢ ih.toFinset.powerset :
      Finset (Finset E × Finset (Finset E))).image
        fun p => p.1 ∪ p.2.image fun s => s.centroid ℝ id).finite_toSet).subset ?_
    rintro f ⟨hf, hfσ⟩
    obtain ⟨τ, d, h, rfl⟩ := (mem_depthSubdivision_succ_faces_iff K m k).mp hf
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(τ, d), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩)
    · rcases h.base with h0 | hτ
      · rw [h0]
        exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem (ih.mem_toFinset.mpr ⟨subcomplexGeneratedBy_faces_subset _ _
          hτ, (convexHull_mono (Finset.coe_subset.mpr Finset.subset_union_left)).trans hfσ⟩)
    · refine Finset.mem_powerset.mpr fun s hs => ih.mem_toFinset.mpr ⟨h.flag.mem_faces hs, ?_⟩
      exact convexHull_subset_of_mem_depthSubdivision_succ_faces K m k hσ hfσ h.flag hs

omit [DecidableEq E] in
theorem mem_depthKeep_of_convexHull_subset {σ : Finset E} {k : ℕ}
    (hk : ∀ τ ∈ K.faces, (convexHull ℝ (τ : Set E) ∩ convexHull ℝ (σ : Set E)).Nonempty →
      m τ ≤ k) {f : Finset E} (hfσ : convexHull ℝ (f : Set E) ⊆ convexHull ℝ (σ : Set E)) :
    f ∈ depthKeep K m k :=
  fun τ hτ hkτ => Set.disjoint_left.mpr fun _ hpf hpτ =>
    absurd (hk τ hτ ⟨_, hpτ, hfσ hpf⟩) (not_le.mpr hkτ)

theorem setOf_depthSubdivision_succ_faces_subset_eq {σ : Finset E} {k : ℕ}
    (hk : ∀ τ ∈ K.faces, (convexHull ℝ (τ : Set E) ∩ convexHull ℝ (σ : Set E)).Nonempty →
      m τ ≤ k) (hσ : σ ∈ K.faces) :
    {f | f ∈ (depthSubdivision K m (k + 1)).faces ∧
      convexHull ℝ (f : Set E) ⊆ convexHull ℝ (σ : Set E)} =
    {f | f ∈ (depthSubdivision K m k).faces ∧
      convexHull ℝ (f : Set E) ⊆ convexHull ℝ (σ : Set E)} := by
  ext f
  constructor
  · rintro ⟨hf, hfσ⟩
    obtain ⟨τ, d, h, rfl⟩ := (mem_depthSubdivision_succ_faces_iff K m k).mp hf
    have hd : d = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun s hs => h.notMem s hs ?_
      exact ⟨s, ⟨h.flag.mem_faces hs, mem_depthKeep_of_convexHull_subset K m hk
        (convexHull_subset_of_mem_depthSubdivision_succ_faces K m k hσ hfσ h.flag hs)⟩,
        Finset.Subset.rfl, (depthSubdivision K m k).nonempty_of_mem_faces (h.flag.mem_faces hs)⟩
    subst hd
    have hτne : τ.Nonempty := h.nonempty.resolve_right Finset.not_nonempty_empty
    have hτ := h.base.resolve_left hτne.ne_empty
    rw [Finset.image_empty, Finset.union_empty] at hfσ ⊢
    exact ⟨subcomplexGeneratedBy_faces_subset _ _ hτ, hfσ⟩
  · rintro ⟨hf, hfσ⟩
    exact ⟨mem_depthSubdivision_succ_of_mem_depthKeep K m k hf
      (mem_depthKeep_of_convexHull_subset K m hk hfσ), hfσ⟩

theorem setOf_depthSubdivision_faces_subset_eq {σ : Finset E} {k : ℕ}
    (hk : ∀ τ ∈ K.faces, (convexHull ℝ (τ : Set E) ∩ convexHull ℝ (σ : Set E)).Nonempty →
      m τ ≤ k) (hσ : σ ∈ K.faces) {j : ℕ} (hkj : k ≤ j) :
    {f | f ∈ (depthSubdivision K m j).faces ∧
      convexHull ℝ (f : Set E) ⊆ convexHull ℝ (σ : Set E)} =
    {f | f ∈ (depthSubdivision K m k).faces ∧
      convexHull ℝ (f : Set E) ⊆ convexHull ℝ (σ : Set E)} := by
  induction j, hkj using Nat.le_induction with
  | base => rfl
  | succ j hkj ih =>
    rw [← ih]
    exact setOf_depthSubdivision_succ_faces_subset_eq K m
      (fun τ hτ hne => (hk τ hτ hne).trans hkj) hσ

theorem diam_le_of_mem_depthSubdivision_faces {N : ℕ} (hN : ∀ s ∈ K.faces, s.card ≤ N + 1)
    (k : ℕ) {f : Finset E} (hf : f ∈ (depthSubdivision K m k).faces) {σ : Finset E}
    (hσ : σ ∈ K.faces) (hfσ : convexHull ℝ (f : Set E) ⊆ convexHull ℝ (σ : Set E)) :
    Metric.diam (convexHull ℝ (f : Set E)) ≤
      ((N : ℝ) / (N + 1)) ^ min k (m σ) * Metric.diam (convexHull ℝ (σ : Set E)) := by
  have hbdd : ∀ s : Finset E, Bornology.IsBounded (convexHull ℝ (s : Set E)) :=
    fun s => (s.finite_toSet.isCompact_convexHull ℝ).isBounded
  have hr0 : (0 : ℝ) ≤ (N : ℝ) / (N + 1) := by positivity
  induction k generalizing f with
  | zero =>
    rw [min_eq_left (Nat.zero_le _), pow_zero, one_mul]
    exact Metric.diam_mono hfσ (hbdd σ)
  | succ k ih =>
    have hsub := depthSubdivision_isSubdivision K m k
    by_cases hkm : k < m σ
    · obtain ⟨τ, d, h, rfl⟩ := (mem_depthSubdivision_succ_faces_iff K m k).mp hf
      have hτ : τ = ∅ := by
        by_contra hτne
        obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hτne
        have hkeep := mem_depthKeep_of_mem_subcomplexGeneratedBy K m k
          (h.base.resolve_left hτne)
        exact Set.disjoint_left.mp (hkeep σ hσ hkm) (subset_convexHull ℝ _ (Finset.mem_coe.mpr hp))
          (hfσ (subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_union_left _ hp))))
      subst hτ
      have hdne : d.Nonempty := h.nonempty.resolve_left Finset.not_nonempty_empty
      obtain ⟨u, hu, htop⟩ := h.flag.exists_top hdne
      have huσ := convexHull_subset_of_mem_depthSubdivision_succ_faces K m k hσ hfσ h.flag hu
      have hcardk : ∀ s ∈ (depthSubdivision K m k).faces, s.card ≤ N + 1 :=
        fun s hs => hsub.card_le hN hs
      rw [Finset.empty_union] at hfσ ⊢
      calc Metric.diam (convexHull ℝ ((d.image fun s => s.centroid ℝ id : Finset E) : Set E))
          ≤ ((N : ℝ) / (N + 1)) * Metric.diam (convexHull ℝ (u : Set E)) :=
            diam_convexHull_image_centroid_le _ hcardk h.flag hdne hu htop
        _ ≤ ((N : ℝ) / (N + 1)) * (((N : ℝ) / (N + 1)) ^ min k (m σ) *
              Metric.diam (convexHull ℝ (σ : Set E))) :=
            mul_le_mul_of_nonneg_left (ih (h.flag.mem_faces hu) huσ) hr0
        _ = ((N : ℝ) / (N + 1)) ^ min (k + 1) (m σ) *
              Metric.diam (convexHull ℝ (σ : Set E)) := by
            rw [min_eq_left hkm.le, min_eq_left (Nat.succ_le_of_lt hkm), pow_succ]
            ring
    · have hmin : min (k + 1) (m σ) = min k (m σ) := by omega
      have hfne := (depthSubdivision K m (k + 1)).nonempty_of_mem_faces hf
      have hx := centroid_mem_openSimplex hfne
      have hxσ : f.centroid ℝ id ∈ convexHull ℝ (σ : Set E) :=
        hfσ (openSimplex_subset_convexHull f hx)
      have hxK : f.centroid ℝ id ∈ (depthSubdivision K m k).space := by
        rw [hsub.space_eq]
        exact K.convexHull_subset_space hσ hxσ
      obtain ⟨g, hg, hxg⟩ := exists_face_mem_openSimplex _ hxK
      have hgσ := hsub.convexHull_subset_of_mem_openSimplex hσ hg hxg hxσ
      have hfg := (depthSubdivision_succ_isSubdivision K m k).convexHull_subset_of_mem_openSimplex
        hg hf hx (openSimplex_subset_convexHull g hxg)
      rw [hmin]
      exact (Metric.diam_mono hfg (hbdd g)).trans (ih hg hgσ)

noncomputable def depthLimit : Geometry.SimplicialComplex ℝ E where
  faces := {f | ∃ k₀, ∀ k, k₀ ≤ k → f ∈ (depthSubdivision K m k).faces}
  isRelLowerSet_faces := by
    rintro f ⟨k₀, hf⟩
    exact ⟨(depthSubdivision K m k₀).nonempty_of_mem_faces (hf k₀ le_rfl),
      fun g hgf hg => ⟨k₀, fun k hk => (depthSubdivision K m k).down_closed (hf k hk) hgf hg⟩⟩
  indep := fun ⟨k₀, hf⟩ => (depthSubdivision K m k₀).indep (hf k₀ le_rfl)
  inter_subset_convexHull := fun ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ =>
    (depthSubdivision K m (max k₁ k₂)).inter_subset_convexHull (h₁ _ (le_max_left _ _))
      (h₂ _ (le_max_right _ _))

omit [DecidableEq E] in
theorem exists_depth_bound
    (hK : LocallyFinite fun s : K.faces =>
      (Subtype.val : K.space → E) ⁻¹' convexHull ℝ ((s : Finset E) : Set E))
    {σ : Finset E} (hσ : σ ∈ K.faces) :
    ∃ k₀, ∀ τ ∈ K.faces, (convexHull ℝ (τ : Set E) ∩ convexHull ℝ (σ : Set E)).Nonempty →
      m τ ≤ k₀ := by
  obtain ⟨k₀, hk₀⟩ := ((finite_setOf_faces_inter_nonempty hK hσ).image m).bddAbove
  exact ⟨k₀, fun τ hτ hne => hk₀ (mem_image_of_mem m ⟨hτ, hne⟩)⟩

theorem mem_depthLimit_faces_iff_of_bound {σ : Finset E} (hσ : σ ∈ K.faces) {k₀ : ℕ}
    (hk₀ : ∀ τ ∈ K.faces, (convexHull ℝ (τ : Set E) ∩ convexHull ℝ (σ : Set E)).Nonempty →
      m τ ≤ k₀) {f : Finset E} (hfσ : convexHull ℝ (f : Set E) ⊆ convexHull ℝ (σ : Set E)) :
    f ∈ (depthLimit K m).faces ↔ f ∈ (depthSubdivision K m k₀).faces := by
  constructor
  · rintro ⟨k₁, hf⟩
    have h := setOf_depthSubdivision_faces_subset_eq K m hk₀ hσ (le_max_left k₀ k₁)
    have hmem : f ∈ {f | f ∈ (depthSubdivision K m (max k₀ k₁)).faces ∧
        convexHull ℝ (f : Set E) ⊆ convexHull ℝ (σ : Set E)} :=
      ⟨hf _ (le_max_right k₀ k₁), hfσ⟩
    rw [h] at hmem
    exact hmem.1
  · intro hf
    refine ⟨k₀, fun k hk => ?_⟩
    have hmem : f ∈ {f | f ∈ (depthSubdivision K m k₀).faces ∧
        convexHull ℝ (f : Set E) ⊆ convexHull ℝ (σ : Set E)} := ⟨hf, hfσ⟩
    rw [← setOf_depthSubdivision_faces_subset_eq K m hk₀ hσ hk] at hmem
    exact hmem.1

theorem depthLimit_isSubdivision
    (hK : LocallyFinite fun s : K.faces =>
      (Subtype.val : K.space → E) ⁻¹' convexHull ℝ ((s : Finset E) : Set E)) :
    IsSubdivision (depthLimit K m) K := by
  refine ⟨Subset.antisymm ?_ ?_, fun f ⟨k₀, hf⟩ =>
    (depthSubdivision_isSubdivision K m k₀).exists_face_subset (hf k₀ le_rfl)⟩
  · intro x hx
    obtain ⟨f, ⟨k₀, hf⟩, hxf⟩ := (depthLimit K m).mem_space_iff.mp hx
    rw [← (depthSubdivision_isSubdivision K m k₀).space_eq]
    exact (depthSubdivision K m k₀).convexHull_subset_space (hf k₀ le_rfl) hxf
  · intro x hx
    obtain ⟨σ, hσ, hxσ⟩ := K.mem_space_iff.mp hx
    obtain ⟨k₀, hk₀⟩ := exists_depth_bound K m hK hσ
    have hxk : x ∈ (depthSubdivision K m k₀).space := by
      rw [(depthSubdivision_isSubdivision K m k₀).space_eq]
      exact hx
    obtain ⟨g, hg, hxg⟩ := exists_face_mem_openSimplex _ hxk
    have hgσ := (depthSubdivision_isSubdivision K m k₀).convexHull_subset_of_mem_openSimplex hσ hg
      hxg hxσ
    exact (depthLimit K m).convexHull_subset_space
      ((mem_depthLimit_faces_iff_of_bound K m hσ hk₀ hgσ).mpr hg)
      (openSimplex_subset_convexHull g hxg)

theorem locallyFinite_depthLimit
    (hK : LocallyFinite fun s : K.faces =>
      (Subtype.val : K.space → E) ⁻¹' convexHull ℝ ((s : Finset E) : Set E)) :
    LocallyFinite fun s : (depthLimit K m).faces =>
      (Subtype.val : (depthLimit K m).space → E) ⁻¹' convexHull ℝ ((s : Finset E) : Set E) := by
  have hsub := depthLimit_isSubdivision K m hK
  intro z
  have hzK : (z : E) ∈ K.space := hsub.space_eq ▸ z.2
  obtain ⟨W, hW, hWfin⟩ := exists_mem_nhds_finite_setOf_faces_inter_nonempty hK hzK
  have hfin : {f | f ∈ (depthLimit K m).faces ∧
      (convexHull ℝ (f : Set E) ∩ W).Nonempty}.Finite := by
    refine (hWfin.biUnion (t := fun σ => {f | f ∈ (depthLimit K m).faces ∧
      convexHull ℝ (f : Set E) ⊆ convexHull ℝ (σ : Set E)}) fun σ hσ => ?_).subset ?_
    · obtain ⟨k₀, hk₀⟩ := exists_depth_bound K m hK hσ.1
      refine (finite_setOf_depthSubdivision_faces_subset K m hσ.1 k₀).subset ?_
      rintro f ⟨hf, hfσ⟩
      exact ⟨(mem_depthLimit_faces_iff_of_bound K m hσ.1 hk₀ hfσ).mp hf, hfσ⟩
    · rintro f ⟨hf, p, hpf, hpW⟩
      obtain ⟨σ, hσ, hfσ⟩ := hsub.exists_face_subset hf
      exact mem_iUnion₂.mpr ⟨σ, ⟨hσ, p, hfσ hpf, hpW⟩, hf, hfσ⟩
  refine ⟨Subtype.val ⁻¹' W, continuous_subtype_val.continuousAt.preimage_mem_nhds hW,
    (hfin.preimage Subtype.val_injective.injOn).subset ?_⟩
  rintro ⟨f, hf⟩ ⟨p, hpf, hpW⟩
  exact ⟨hf, p, hpf, hpW⟩

theorem diam_le_of_mem_depthLimit_faces {N : ℕ} (hN : ∀ s ∈ K.faces, s.card ≤ N + 1)
    {f : Finset E} (hf : f ∈ (depthLimit K m).faces) {σ : Finset E} (hσ : σ ∈ K.faces)
    (hfσ : convexHull ℝ (f : Set E) ⊆ convexHull ℝ (σ : Set E)) :
    Metric.diam (convexHull ℝ (f : Set E)) ≤
      ((N : ℝ) / (N + 1)) ^ m σ * Metric.diam (convexHull ℝ (σ : Set E)) := by
  obtain ⟨k₀, hk₀⟩ := hf
  have h := diam_le_of_mem_depthSubdivision_faces K m hN (max k₀ (m σ))
    (hk₀ _ (le_max_left _ _)) hσ hfσ
  rwa [min_eq_right (le_max_right _ _)] at h

end Depth

def LocallyFinitePLPieceIn.subdivide {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    {Y : Set X} (T : LocallyFinitePLPieceIn E n X Y) (K : Geometry.SimplicialComplex ℝ E)
    (hK : IsSubdivision K T.complex)
    (hlf : LocallyFinite fun s : K.faces =>
      (Subtype.val : K.space → E) ⁻¹' convexHull ℝ ((s : Finset E) : Set E)) :
    LocallyFinitePLPieceIn E n X Y where
  complex := K
  locallyFinite := hlf
  map := T.map
  bijOn := by
    rw [hK.space_eq]
    exact T.bijOn
  continuousOn := by
    rw [hK.space_eq]
    exact T.continuousOn
  isEmbedding := by
    rw [hK.space_eq]
    exact T.isEmbedding
  isPiecewiseAffineOn_chart := by
    rw [hK.space_eq]
    exact T.isPiecewiseAffineOn_chart
  isPiecewiseAffineOn_chart_symm := by
    rw [hK.space_eq]
    exact T.isPiecewiseAffineOn_chart_symm

theorem LocallyFinitePLPieceIn.exists_isSubdivision_forall_image_subset {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ} {X : Type*}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {Y : Set X}
    (T : LocallyFinitePLPieceIn E n X Y) {N : ℕ} (hN : ∀ s ∈ T.complex.faces, s.card ≤ N + 1)
    {ι : Type*} (O : ι → Set X) (hO : ∀ i, IsOpen (O i)) (hcover : Y ⊆ ⋃ i, O i) :
    ∃ K : Geometry.SimplicialComplex ℝ E, IsSubdivision K T.complex ∧
      (LocallyFinite fun s : K.faces =>
        (Subtype.val : K.space → E) ⁻¹' convexHull ℝ ((s : Finset E) : Set E)) ∧
      ∀ t ∈ K.faces, ∃ i, ∀ w ∈ t, ∀ s ∈ K.faces, w ∈ s →
        T.map '' convexHull ℝ (s : Set E) ⊆ O i := by
  classical
  have hW : ∀ i, ∃ W : Set E, IsOpen W ∧ T.map ⁻¹' O i ∩ T.complex.space = W ∩ T.complex.space :=
    fun i => continuousOn_iff'.mp T.continuousOn (O i) (hO i)
  choose W hWo hWeq using hW
  have hKW : T.complex.space ⊆ ⋃ i, W i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover (T.bijOn.mapsTo hx))
    have hxi : x ∈ T.map ⁻¹' O i ∩ T.complex.space := ⟨hi, hx⟩
    rw [hWeq i] at hxi
    exact mem_iUnion.mpr ⟨i, hxi.1⟩
  have hleb : ∀ σ : Finset E, ∃ δ : ℝ, 0 < δ ∧ (σ ∈ T.complex.faces →
      ∀ x ∈ convexHull ℝ (σ : Set E), ∃ i, Metric.ball x δ ⊆ W i) := by
    intro σ
    by_cases hσ : σ ∈ T.complex.faces
    · obtain ⟨δ, hδ, h⟩ := lebesgue_number_lemma_of_metric
        (σ.finite_toSet.isCompact_convexHull ℝ) hWo
        ((T.complex.convexHull_subset_space hσ).trans hKW)
      exact ⟨δ, hδ, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hσ⟩
  choose δ hδpos hδ using hleb
  have hself : ∀ τ ∈ T.complex.faces,
      (convexHull ℝ (τ : Set E) ∩ convexHull ℝ (τ : Set E)).Nonempty := by
    intro τ hτ
    obtain ⟨v, hv⟩ := T.complex.nonempty_of_mem_faces hτ
    exact ⟨v, subset_convexHull ℝ _ (Finset.mem_coe.mpr hv),
      subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)⟩
  have hε : ∀ τ : Finset E, ∃ ε : ℝ, 0 < ε ∧ (τ ∈ T.complex.faces → ∀ σ ∈ T.complex.faces,
      (convexHull ℝ (σ : Set E) ∩ convexHull ℝ (τ : Set E)).Nonempty → ε ≤ δ σ) := by
    intro τ
    by_cases hτ : τ ∈ T.complex.faces
    · have hfin := finite_setOf_faces_inter_nonempty T.locallyFinite hτ
      obtain ⟨σ₀, -, hmin⟩ := hfin.toFinset.exists_min_image δ
        ⟨τ, hfin.mem_toFinset.mpr ⟨hτ, hself τ hτ⟩⟩
      exact ⟨δ σ₀, hδpos σ₀, fun _ σ hσ hne => hmin σ (hfin.mem_toFinset.mpr ⟨hσ, hne⟩)⟩
    · exact ⟨1, one_pos, fun h => absurd h hτ⟩
  choose ε hεpos hε using hε
  have hr0 : (0 : ℝ) ≤ (N : ℝ) / (N + 1) := by positivity
  have hr1 : (N : ℝ) / (N + 1) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hdepth : ∀ τ : Finset E, ∃ k : ℕ,
      ((N : ℝ) / (N + 1)) ^ k * Metric.diam (convexHull ℝ (τ : Set E)) < ε τ / 2 := by
    intro τ
    have hD : 0 ≤ Metric.diam (convexHull ℝ (τ : Set E)) := Metric.diam_nonneg
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
      (div_pos (half_pos (hεpos τ)) (by linarith : (0 : ℝ) < Metric.diam
        (convexHull ℝ (τ : Set E)) + 1)) hr1
    refine ⟨k, ?_⟩
    have hk' := (lt_div_iff₀ (by linarith : (0 : ℝ) < Metric.diam
      (convexHull ℝ (τ : Set E)) + 1)).mp hk
    calc ((N : ℝ) / (N + 1)) ^ k * Metric.diam (convexHull ℝ (τ : Set E))
        ≤ ((N : ℝ) / (N + 1)) ^ k * (Metric.diam (convexHull ℝ (τ : Set E)) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hr0 k)
      _ < ε τ / 2 := hk'
  choose m hm using hdepth
  have hsub := depthLimit_isSubdivision T.complex m T.locallyFinite
  have hsmall : ∀ s ∈ (depthLimit T.complex m).faces, ∀ σ ∈ T.complex.faces,
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (σ : Set E) →
        Metric.diam (convexHull ℝ (s : Set E)) < ε σ / 2 :=
    fun s hs σ hσ hsσ =>
      (diam_le_of_mem_depthLimit_faces T.complex m hN hs hσ hsσ).trans_lt (hm σ)
  refine ⟨depthLimit T.complex m, hsub, locallyFinite_depthLimit T.complex m T.locallyFinite,
    fun t ht => ?_⟩
  obtain ⟨w₀, hw₀⟩ := (depthLimit T.complex m).nonempty_of_mem_faces ht
  obtain ⟨σt, hσt, htσ⟩ := hsub.exists_face_subset ht
  have hw₀σ : w₀ ∈ convexHull ℝ (σt : Set E) := htσ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw₀))
  obtain ⟨i, hi⟩ := hδ σt hσt w₀ hw₀σ
  refine ⟨i, fun w hw s hs hws => ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨σs, hσs, hsσ⟩ := hsub.exists_face_subset hs
  have hmeet : (convexHull ℝ (σt : Set E) ∩ convexHull ℝ (σs : Set E)).Nonempty :=
    ⟨w, htσ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw)),
      hsσ (subset_convexHull ℝ _ (Finset.mem_coe.mpr hws))⟩
  have hds := (hsmall s hs σs hσs hsσ).trans_le
    (div_le_div_of_nonneg_right (hε σs hσs σt hσt hmeet) zero_le_two)
  have hdt := (hsmall t ht σt hσt htσ).trans_le
    (div_le_div_of_nonneg_right (hε σt hσt σt hσt (hself σt hσt)) zero_le_two)
  have hy₁ : dist y w ≤ Metric.diam (convexHull ℝ (s : Set E)) :=
    Metric.dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded hy
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr hws))
  have hy₂ : dist w w₀ ≤ Metric.diam (convexHull ℝ (t : Set E)) :=
    Metric.dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull ℝ).isBounded
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw))
      (subset_convexHull ℝ _ (Finset.mem_coe.mpr hw₀))
  have hyW : y ∈ W i := hi (Metric.mem_ball.mpr (by linarith [dist_triangle y w w₀]))
  have hyK : y ∈ T.complex.space := by
    rw [← hsub.space_eq]
    exact (depthLimit T.complex m).convexHull_subset_space hs hy
  have hyO : y ∈ T.map ⁻¹' O i ∩ T.complex.space := by
    rw [hWeq i]
    exact ⟨hyW, hyK⟩
  exact hyO.1

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁] {U : Set M₁}

theorem exists_isSubdivision_section34CarrierSupport_subset [T2Space M₁]
    {ι : Type*} (hU : IsOpen U)
    (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) (h𝒦 : IsCombinatorialManifold 3 𝒦.complex)
    (O : ι → Set M₁) (hO : ∀ i, IsOpen (O i)) (hcover : U ⊆ ⋃ i, O i) :
    ∃ 𝒦₁ : LocallyFinitePLPieceIn Ea 3 M₁ U, IsSubdivision 𝒦₁.complex 𝒦.complex ∧
      𝒦₁.map = 𝒦.map ∧ IsCombinatorialManifold 3 𝒦₁.complex ∧
      ∀ t ∈ 𝒦₁.complex.faces, ∃ i, Section34CarrierSupport 𝒦₁ t ⊆ O i := by
  classical
  have hN : ∀ s ∈ 𝒦.complex.faces, s.card ≤ 3 + 1 := by
    intro s hs
    obtain ⟨v, hv⟩ := 𝒦.complex.nonempty_of_mem_faces hs
    have hv' : ({v} : Finset Ea) ∈ 𝒦.complex.faces :=
      𝒦.complex.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have : Finite (SimplicialComplex.geometricLink 𝒦.complex {v}).faces :=
      (𝒦.geometricLink_faces_finite hv').to_subtype
    have hcard := Finset.card_erase_of_mem hv
    rcases (s.erase v).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.card_empty] at hcard
      omega
    · have hmem : s.erase v ∈ (SimplicialComplex.geometricLink 𝒦.complex {v}).faces :=
        (SimplicialComplex.mem_geometricLink_singleton 𝒦.complex v _).mpr
          ⟨hne, Finset.notMem_erase v s, by rwa [Finset.insert_erase hv]⟩
      have hle : (s.erase v).card ≤ 2 + 1 := card_le_of_isPLBall_or_isPLSphere
        (SimplicialComplex.geometricLink 𝒦.complex {v}) (Or.inr (h𝒦 v hv')) hmem
      omega
  obtain ⟨K, hK, hlf, hstar⟩ := 𝒦.exists_isSubdivision_forall_image_subset hN O hO hcover
  refine ⟨𝒦.subdivide K hK hlf, hK, rfl,
    isCombinatorialManifold_of_locallyFinitePLPieceIn hU _, fun t ht => ?_⟩
  obtain ⟨i, hi⟩ := hstar t ht
  exact ⟨i, iUnion₂_subset fun w hw => iUnion₂_subset fun s hs => hi w hw s hs.1 hs.2⟩

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
