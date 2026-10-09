/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacets
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem source_subset_of_top_simplex {ι : Type*}
    {dim : ι → ℕ} {src : ι → Set E}
    (hball : ∀ i, IsPLBall (dim i) (src i))
    (hinter : ∀ i j, src i ∩ src j =
      ⋃ k ∈ {k | src k ⊆ src i} ∩ {k | src k ⊆ src j}, src k)
    (hstrict : ∀ i j, src j ⊆ src i → j = i ∨ dim j < dim i)
    (T : Geometry.SimplicialComplex ℝ E) [Finite T.faces] {B : Set E}
    (htri : ∀ i, src i ⊆ B → (restrict T (src i)).space = src i)
    {i j : ι} (hiB : src i ⊆ B) {s : Finset E} (hs : s ∈ T.faces)
    (hcard : s.card = dim i + 1) (hsi : convexHull ℝ (s : Set E) ⊆ src i)
    (hsj : convexHull ℝ (s : Set E) ⊆ src j) : src i ⊆ src j := by
  have hx := centroid_mem_openSimplex (T.nonempty_of_mem_faces hs)
  have hxS := openSimplex_subset_convexHull s hx
  have hxij : s.centroid ℝ id ∈ src i ∩ src j := ⟨hsi hxS, hsj hxS⟩
  rw [hinter] at hxij
  obtain ⟨k, ⟨hki, hkj⟩, hxk⟩ := mem_iUnion₂.mp hxij
  have hkB : src k ⊆ B := hki.trans hiB
  obtain ⟨t, ht, hxt⟩ :=
    (restrict T (src k)).mem_space_iff.mp ((htri k hkB).symm ▸ hxk)
  have hsk : s ∈ (restrict T (src k)).faces := (restrict T (src k)).down_closed ht
    (face_subset_of_mem_openSimplex_of_mem_convexHull T hs ht.1 hx hxt)
    (T.nonempty_of_mem_faces hs)
  let _ : Finite (restrict T (src k)).faces := (restrict_faces_finite T (src k)).to_subtype
  have hle := card_le_of_isPLBall (restrict T (src k))
    ((htri k hkB).symm ▸ hball k) hsk
  rcases hstrict i k hki with rfl | hlt
  · exact hkj
  · omega

theorem exists_pair_cofaces_of_finite_cell_decomposition {ι : Type*} [Finite ι]
    {dim : ι → ℕ} {src srcBd : ι → Set E}
    (hparam : ∀ i, ∃ q : (Fin (dim i + 1) → ℝ) → E,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin (dim i + 1))) (src i) ∧
        srcBd i = q '' stdSimplexBoundary (dim i))
    (hboundary : ∀ i, srcBd i = ⋃ j ∈ {j | src j ⊆ src i} \ {i}, src j)
    (hinter : ∀ i j, src i ∩ src j =
      ⋃ k ∈ {k | src k ⊆ src i} ∩ {k | src k ⊆ src j}, src k)
    (hstrict : ∀ i j, src j ⊆ src i → j = i ∨ dim j < dim i)
    {n : ℕ} {B : Set E} (hB : IsPLSphere (n + 1) B)
    (hcover : ∀ x ∈ B, ∃ i, src i ⊆ B ∧ x ∈ src i)
    {r : ι} (hr : dim r = n) (hrB : src r ⊆ B) :
    ∃ a b : ι, a ≠ b ∧ dim a = n + 1 ∧ dim b = n + 1 ∧
      src r ⊆ src a ∧ src a ⊆ B ∧ src r ⊆ src b ∧ src b ⊆ B ∧
      ∀ c : ι, dim c = n + 1 → src r ⊆ src c → src c ⊆ B → c = a ∨ c = b := by
  classical
  let _ : DecidableEq E := Classical.decEq E
  have hball (i : ι) : IsPLBall (dim i) (src i) := by
    obtain ⟨q, hq, -⟩ := hparam i
    exact ⟨q, hq⟩
  obtain ⟨L, hLfin, hLB⟩ := hB.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  obtain ⟨T, hTL, hTfin, htri⟩ := exists_isSubdivision_subcomplexes L
    (fun i : {i : ι // src i ⊆ B} => src i)
    (fun i => (hball i).isPolyhedron) (fun i => hLB.symm ▸ i.2)
  let _ : Finite T.faces := hTfin.to_subtype
  have hTB : T.space = B := hTL.space_eq.trans hLB
  have hTcell (i : ι) (hiB : src i ⊆ B) : (restrict T (src i)).space = src i :=
    restrict_space_of_eq_biUnion T (src i) (htri ⟨i, hiB⟩)
  have hTman : IsCombinatorialManifold (n + 1) T :=
    (hTB.symm ▸ hB).isCombinatorialManifold
  have hdim (i : ι) (hiB : src i ⊆ B) : dim i ≤ n + 1 := by
    let _ : Finite (restrict T (src i)).faces := (restrict_faces_finite T (src i)).to_subtype
    obtain ⟨x, hx⟩ := (hball i).nonempty
    obtain ⟨t, ht, -⟩ := (restrict T (src i)).mem_space_iff.mp ((hTcell i hiB).symm ▸ hx)
    obtain ⟨u, hu, -, huc⟩ := exists_face_superset_card_eq_of_isPLBall
      (restrict T (src i)) ((hTcell i hiB).symm ▸ hball i) ht
    have hbound := card_le_of_isPLSphere T (hTB.symm ▸ hB) hu.1
    omega
  let _ : Finite (restrict T (src r)).faces := (restrict_faces_finite T (src r)).to_subtype
  obtain ⟨x, hx⟩ := (hball r).nonempty
  obtain ⟨t, ht, -⟩ := (restrict T (src r)).mem_space_iff.mp ((hTcell r hrB).symm ▸ hx)
  obtain ⟨s, hsR, -, hsc⟩ := exists_face_superset_card_eq_of_isPLBall
    (restrict T (src r)) ((hTcell r hrB).symm ▸ hball r) ht
  have hs : s ∈ T.faces := hsR.1
  have hscard : s.card = n + 1 := hsc.trans (congrArg (· + 1) hr)
  obtain ⟨v, w, hvw, hpair⟩ := hTman.codimension_one_cofaces T hs hscard
  have hv : v ∉ s ∧ insert v s ∈ T.faces := by
    exact hpair.symm.subset (mem_insert v {w})
  have hw : w ∉ s ∧ insert w s ∈ T.faces := by
    exact hpair.symm.subset (mem_insert_of_mem v (mem_singleton w))
  have howner (u : E) (hu : u ∉ s ∧ insert u s ∈ T.faces) :
      ∃ c : ι, dim c = n + 1 ∧ src r ⊆ src c ∧ src c ⊆ B ∧
        convexHull ℝ (↑(insert u s) : Set E) ⊆ src c := by
    have hxu := centroid_mem_openSimplex (T.nonempty_of_mem_faces hu.2)
    have hxuB : (insert u s).centroid ℝ id ∈ B := hTB ▸
      T.convexHull_subset_space hu.2 (openSimplex_subset_convexHull _ hxu)
    obtain ⟨c, hcB, hxc⟩ := hcover _ hxuB
    obtain ⟨f, hf, hxf⟩ :=
      (restrict T (src c)).mem_space_iff.mp ((hTcell c hcB).symm ▸ hxc)
    have huc : insert u s ∈ (restrict T (src c)).faces :=
      (restrict T (src c)).down_closed hf
        (face_subset_of_mem_openSimplex_of_mem_convexHull T hu.2 hf.1 hxu hxf)
        (T.nonempty_of_mem_faces hu.2)
    let _ : Finite (restrict T (src c)).faces := (restrict_faces_finite T (src c)).to_subtype
    have hle := card_le_of_isPLBall (restrict T (src c))
      ((hTcell c hcB).symm ▸ hball c) huc
    have hicard : (insert u s).card = n + 2 := by
      rw [Finset.card_insert_of_notMem hu.1, hscard]
    have hdc : dim c = n + 1 := by have := hdim c hcB; omega
    refine ⟨c, hdc, ?_, hcB, huc.2⟩
    exact source_subset_of_top_simplex hball hinter hstrict T hTcell hrB hs hsc hsR.2
      ((convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert u s))).trans huc.2)
  have hunique (c : ι) (hdc : dim c = n + 1) (hrc : src r ⊆ src c)
      (hcB : src c ⊆ B) :
      ∃ u, {y | y ∉ s ∧ insert y s ∈ (restrict T (src c)).faces} = {u} := by
    let _ : Finite (restrict T (src c)).faces := (restrict_faces_finite T (src c)).to_subtype
    have hrcne : r ≠ c := by intro heq; subst c; omega
    have hrbd : src r ⊆ srcBd c := by
      rw [hboundary c]
      exact subset_iUnion₂_of_subset r ⟨hrc, hrcne⟩ subset_rfl
    have hparamc : ∃ q : (Fin (n + 2) → ℝ) → E,
        IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2))) (src c) ∧
          srcBd c = q '' stdSimplexBoundary (n + 1) := by
      have hcparam := hparam c
      rw [hdc] at hcparam
      exact hcparam
    obtain ⟨q, hq, hqc⟩ := hparamc
    have hcb : srcBd c = (boundaryComplex (n + 1) (restrict T (src c))).space := by
      have hqR : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin (n + 2)))
          (restrict T (src c)).space := (hTcell c hcB).symm ▸ hq
      rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex _ hqR,
        simplexBoundary_stdVertices_space]
      exact hqc
    have hsC : s ∈ (restrict T (src c)).faces := ⟨hs, hsR.2.trans hrc⟩
    have hxbd : s.centroid ℝ id ∈
        (boundaryComplex (n + 1) (restrict T (src c))).space :=
      hcb ▸ hrbd (hsR.2 (s.centroid_mem_convexHull (T.nonempty_of_mem_faces hs)))
    obtain ⟨f, hf, hxf⟩ :=
      (boundaryComplex (n + 1) (restrict T (src c))).mem_space_iff.mp hxbd
    have hsBd : s ∈ (boundaryComplex (n + 1) (restrict T (src c))).faces :=
      (boundaryComplex (n + 1) (restrict T (src c))).down_closed hf
        (face_subset_of_mem_openSimplex_of_mem_convexHull (restrict T (src c)) hsC
          (boundaryComplex_faces_subset (n + 1) (restrict T (src c)) hf)
          (centroid_mem_openSimplex (T.nonempty_of_mem_faces hs)) hxf)
        (T.nonempty_of_mem_faces hs)
    have hballc : IsPLBall (n + 1) (restrict T (src c)).space :=
      (hTcell c hcB).symm ▸ (hdc ▸ hball c)
    have hman := hballc.isCombinatorialManifoldWithBoundary
    exact (hman.mem_boundaryComplex_iff_unique_coface _ hscard).mp hsBd
  obtain ⟨a, hda, hra, haB, hva⟩ := howner v hv
  obtain ⟨b, hdb, hrb, hbB, hwb⟩ := howner w hw
  have hab : a ≠ b := by
    intro heq
    subst b
    obtain ⟨u, hu⟩ := hunique a hda hra haB
    have hvm : v ∈ {y | y ∉ s ∧ insert y s ∈ (restrict T (src a)).faces} :=
      ⟨hv.1, hv.2, hva⟩
    have hwm : w ∈ {y | y ∉ s ∧ insert y s ∈ (restrict T (src a)).faces} :=
      ⟨hw.1, hw.2, hwb⟩
    rw [hu, mem_singleton_iff] at hvm hwm
    exact hvw (hvm.trans hwm.symm)
  refine ⟨a, b, hab, hda, hdb, hra, haB, hrb, hbB, ?_⟩
  intro c hdc hrc hcB
  obtain ⟨u, hu⟩ := hunique c hdc hrc hcB
  have hum : u ∉ s ∧ insert u s ∈ (restrict T (src c)).faces := by
    change u ∈ {y | y ∉ s ∧ insert y s ∈ (restrict T (src c)).faces}
    rw [hu]
    exact mem_singleton u
  have huvw : u = v ∨ u = w := by
    exact hpair.subset ⟨hum.1, hum.2.1⟩
  have heq (d : ι) (hdd : dim d = n + 1)
      (hud : convexHull ℝ (↑(insert u s) : Set E) ⊆ src d) : c = d := by
    have hcsub : src c ⊆ src d := source_subset_of_top_simplex hball hinter hstrict T hTcell
      hcB hum.2.1 (by rw [Finset.card_insert_of_notMem hum.1, hscard, hdc]) hum.2.2 hud
    rcases hstrict d c hcsub with h | h
    · exact h
    · omega
  rcases huvw with rfl | rfl
  · exact Or.inl (heq a hda hva)
  · exact Or.inr (heq b hdb hwb)

end DifferentialGeometry.Topology.PiecewiseLinear
