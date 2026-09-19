/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderCut
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin

/-! Boundary images of cylindrical diagrams over PL disks. -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace IsCylindricalDiagram

variable {f : E × ℝ → F} {P : Set E} {S : Set F}

theorem image_strip_mem_nhdsWithin [FiniteDimensional ℝ E]
    (hf : IsCylindricalDiagram f P S)
    (hP : IsCompact P) {a b t : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hat : a < t) (htb : t < b) {x : E} (hx : x ∈ P) :
    f '' (P ×ˢ Icc a b) ∈ 𝓝[S] f (x, t) := by
  have ht0 : 0 < t := ha.trans_lt hat
  have ht1 : t < 1 := htb.trans_le hb
  have ha1 : a ≤ 1 := (hat.trans ht1).le
  have hb0 : 0 ≤ b := (ht0.trans htb).le
  have hunique : ∀ z ∈ P ×ˢ Icc (0 : ℝ) 1, f z = f (x, t) → z = (x, t) := by
    intro z hz heq
    rcases hf.eq_or_endpoints z hz (x, t) ⟨hx, ht0.le, ht1.le⟩ heq with
      heq | hends | hends
    · exact heq
    · exact (ht1.ne hends.2).elim
    · exact (ht0.ne' hends.2).elim
  let C := f '' (P ×ˢ Icc (0 : ℝ) a) ∪ f '' (P ×ˢ Icc b 1)
  have hC : IsClosed C := by
    apply IsClosed.union
    · exact ((hP.prod isCompact_Icc).image_of_continuousOn
        (hf.isPiecewiseAffineOn.continuousOn.mono
          (fun _ hz => ⟨hz.1, hz.2.1, hz.2.2.trans ha1⟩))).isClosed
    · exact ((hP.prod isCompact_Icc).image_of_continuousOn
        (hf.isPiecewiseAffineOn.continuousOn.mono
          (fun _ hz => ⟨hz.1, hb0.trans hz.2.1, hz.2.2⟩))).isClosed
  have hnot : f (x, t) ∉ C := by
    rintro (⟨z, hz, heq⟩ | ⟨z, hz, heq⟩)
    · have hzxt := hunique z ⟨hz.1, hz.2.1, hz.2.2.trans ha1⟩ heq
      have hta := hz.2.2
      rw [hzxt] at hta
      exact hat.not_ge hta
    · have hzxt := hunique z ⟨hz.1, hb0.trans hz.2.1, hz.2.2⟩ heq
      have hbt := hz.2.1
      rw [hzxt] at hbt
      exact htb.not_ge hbt
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    ⟨Cᶜ, hC.isOpen_compl.mem_nhds hnot, ?_⟩
  rintro y ⟨hyC, hyS⟩
  obtain ⟨z, hz, rfl⟩ := hf.image_eq.symm ▸ hyS
  have haz : a ≤ z.2 := by
    by_contra hn
    exact hyC (Or.inl ⟨z, ⟨hz.1, hz.2.1, (lt_of_not_ge hn).le⟩, rfl⟩)
  have hzb : z.2 ≤ b := by
    by_contra hn
    exact hyC (Or.inr ⟨z, ⟨hz.1, (lt_of_not_ge hn).le, hz.2.2⟩, rfl⟩)
  exact ⟨z, ⟨hz.1, haz, hzb⟩, rfl⟩

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

open Classical in
private theorem image_side_Ioo_subset_boundaryComplex
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hf : IsCylindricalDiagram f D.space M.space) :
    f '' ((boundaryComplex 2 D).space ×ˢ Ioo (0 : ℝ) 1) ⊆
      (boundaryComplex 3 M).space := by
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  rintro y ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
  have hxD := boundaryComplex_space_subset 2 D hx
  let a := t / 2
  let b := (t + 1) / 2
  have ha : 0 < a := by dsimp [a]; linarith [ht.1]
  have hb : b < 1 := by dsimp [b]; linarith [ht.2]
  have hat : a < t := by dsimp [a]; linarith [ht.1]
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hab : a < b := hat.trans htb
  have hprod := isPLBall_three_prod hD (isPLBall_Icc hab)
  have hstrip := hf.isPLHomeomorphOn_strip hD.isPolyhedron ha.le hb.le (Or.inl ha)
  obtain ⟨Q, hQfin, hQspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite Q.faces := hQfin.to_subtype
  have hQ : IsPLBall 3 Q.space := hQspace.symm ▸ hprod
  have himage := hprod.of_isPLHomeomorphOn hstrip
  obtain ⟨C, hCfin, hCspace⟩ := himage.isPolyhedron.exists_simplicialComplex
  let _ : Finite C.faces := hCfin.to_subtype
  have hC : IsPLBall 3 C.space := hCspace.symm ▸ himage
  have hmap : IsPLHomeomorphOn f Q.space C.space := by
    rw [hQspace, hCspace]
    exact hstrip
  have hxtQ : (x, t) ∈ Q.space := hQspace.symm ▸ ⟨hxD, hat.le, htb.le⟩
  have hxtBdQ : (x, t) ∈ (boundaryComplex 3 Q).space := by
    rw [boundaryComplex_space_prism D hD hab Q hQspace]
    exact Or.inr ⟨hx, hat.le, htb.le⟩
  have hxtBdC := (mem_boundaryComplex_space_iff_of_isPLHomeomorphOn Q C
    hQ.isCombinatorialManifoldWithBoundary hmap hxtQ).mpr hxtBdQ
  have hCM : C.space ⊆ M.space := by
    rw [hCspace, ← hf.image_eq]
    exact image_mono (fun _ hz => ⟨hz.1, ha.le.trans hz.2.1, hz.2.2.trans hb.le⟩)
  have hnhds : C.space ∈ 𝓝[M.space] f (x, t) := by
    rw [hCspace]
    exact hf.image_strip_mem_nhdsWithin hD.isPolyhedron.isCompact ha.le hb.le hat htb hxD
  exact (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin M C hM
    hC.isCombinatorialManifoldWithBoundary hCM (hmap.bijOn.mapsTo hxtQ) hnhds).mp hxtBdC

open Classical in
theorem image_side_subset_boundaryComplex
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hf : IsCylindricalDiagram f D.space M.space) :
    f '' ((boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1) ⊆
      (boundaryComplex 3 M).space := by
  let _ : Finite (boundaryComplex 2 D).faces := (boundaryComplex_faces_finite 2 D).to_subtype
  let _ : Finite (boundaryComplex 3 M).faces := (boundaryComplex_faces_finite 3 M).to_subtype
  have hcl : closure ((boundaryComplex 2 D).space ×ˢ Ioo (0 : ℝ) 1) =
      (boundaryComplex 2 D).space ×ˢ Icc (0 : ℝ) 1 := by
    rw [closure_prod_eq, (isPolyhedron_space (boundaryComplex 2 D)).isClosed.closure_eq,
      closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hcont : ContinuousOn f (closure ((boundaryComplex 2 D).space ×ˢ Ioo (0 : ℝ) 1)) := by
    rw [hcl]
    exact hf.isPiecewiseAffineOn.continuousOn.mono
      (prod_mono (boundaryComplex_space_subset 2 D) Subset.rfl)
  have h := hcont.image_closure.trans
    (closure_minimal (image_side_Ioo_subset_boundaryComplex D M hD hM hf)
      (isPolyhedron_space (boundaryComplex 3 M)).isClosed)
  rwa [hcl] at h

end IsCylindricalDiagram

end DifferentialGeometry.Topology.PiecewiseLinear
