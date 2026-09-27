/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallStarring
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphGluing
import DifferentialGeometry.Topology.PiecewiseLinear.PrismDisk
import DifferentialGeometry.Topology.PiecewiseLinear.PrismBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SphereSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskPair

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem exists_isPLHomeomorphOn_centered_prism_of_boundary_disk_pair
    {P : Set E} (hP : IsPLBall 2 P)
    (K₀ K₁ : Geometry.SimplicialComplex ℝ F) [Finite K₀.faces] [Finite K₁.faces]
    (hK₀ : IsPLBall 3 K₀.space) (hK₁ : IsPLBall 3 K₁.space) {D : Set F}
    (hD₀ : D ⊆ (boundaryComplex 3 K₀).space)
    (hD₁ : D ⊆ (boundaryComplex 3 K₁).space) (hinter : K₀.space ∩ K₁.space = D)
    {g : E → F} (hg : IsPLHomeomorphOn g P D) :
    ∃ ρ : E × ℝ → F,
      IsPLHomeomorphOn ρ (P ×ˢ Icc (-1 : ℝ) 1) (K₀.space ∪ K₁.space) ∧
      (∀ x ∈ P, ρ (x, 0) = g x) ∧
      ρ '' (P ×ˢ Icc (-1 : ℝ) 0) = K₀.space ∧
      ρ '' (P ×ˢ Icc (0 : ℝ) 1) = K₁.space := by
  let _ : DecidableEq F := Classical.decEq _
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  obtain ⟨L, hLfin, hLspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall 2 L.space := hLspace.symm ▸ hP
  have hminus : IsPLBall 3 (P ×ˢ Icc (-1 : ℝ) 0) :=
    isPLBall_three_prod hP (isPLBall_Icc (by norm_num))
  have hplus : IsPLBall 3 (P ×ˢ Icc (0 : ℝ) 1) :=
    isPLBall_three_prod hP (isPLBall_Icc (by norm_num))
  obtain ⟨R₀, hR₀fin, hR₀space⟩ := hminus.isPolyhedron.exists_simplicialComplex
  obtain ⟨R₁, hR₁fin, hR₁space⟩ := hplus.isPolyhedron.exists_simplicialComplex
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  let _ : Finite R₁.faces := hR₁fin.to_subtype
  have hR₀ : IsPLBall 3 R₀.space := hR₀space.symm ▸ hminus
  have hR₁ : IsPLBall 3 R₁.space := hR₁space.symm ▸ hplus
  have hboundary₀ := boundaryComplex_space_prism L hL (by norm_num : (-1 : ℝ) < 0)
    R₀ (hLspace.symm ▸ hR₀space)
  have hboundary₁ := boundaryComplex_space_prism L hL (by norm_num : (0 : ℝ) < 1)
    R₁ (hLspace.symm ▸ hR₁space)
  have hmid₀ : P ×ˢ {(0 : ℝ)} ⊆ (boundaryComplex 3 R₀).space := by
    rw [hboundary₀, hLspace]
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact Or.inl ⟨hx, Or.inr ht⟩
  have hmid₁ : P ×ˢ {(0 : ℝ)} ⊆ (boundaryComplex 3 R₁).space := by
    rw [hboundary₁, hLspace]
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact Or.inl ⟨hx, Or.inl ht⟩
  have hmid : IsPLBall 2 (P ×ˢ {(0 : ℝ)}) :=
    hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const 0)
  have hgmid : IsPLHomeomorphOn (g ∘ Prod.fst) (P ×ˢ {(0 : ℝ)}) D :=
    hP.isPolyhedron.isPLHomeomorphOn_fst_prod_const 0 |>.trans hg
  obtain ⟨f₀, hf₀, hf₀g⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex R₀ K₀ hR₀ hK₀
      hmid hmid₀ hgmid hD₀
  obtain ⟨f₁, hf₁, hf₁g⟩ :=
    exists_isPLHomeomorphOn_eqOn_disk_of_boundaryComplex R₁ K₁ hR₁ hK₁
      hmid hmid₁ hgmid hD₁
  rw [hR₀space] at hf₀
  rw [hR₁space] at hf₁
  have hsource :
      (P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1) = P ×ˢ {(0 : ℝ)} := by
    ext ⟨x, t⟩
    constructor
    · rintro ⟨⟨hx, -, htle⟩, ⟨-, htge, -⟩⟩
      exact ⟨hx, le_antisymm htle htge⟩
    · rintro ⟨hx, ht⟩
      change t = 0 at ht
      subst t
      exact ⟨⟨hx, by norm_num, by norm_num⟩, ⟨hx, by norm_num, by norm_num⟩⟩
  have hagree : EqOn f₀ f₁
      ((P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1)) := by
    intro z hz
    have hzmid : z ∈ P ×ˢ {(0 : ℝ)} := hsource.subset hz
    exact (hf₀g hzmid).trans (hf₁g hzmid).symm
  have hsurj : SurjOn f₀
      ((P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1))
      (K₀.space ∩ K₁.space) := by
    intro y hy
    have hyD : y ∈ D := hinter.subset hy
    obtain ⟨x, hx, hxy⟩ := hg.bijOn.surjOn hyD
    have hxmid : (x, (0 : ℝ)) ∈ P ×ˢ {(0 : ℝ)} := ⟨hx, rfl⟩
    refine ⟨(x, 0), hsource.symm.subset hxmid, ?_⟩
    exact (hf₀g hxmid).trans hxy
  obtain ⟨ρ, hρ, hρminus, hρplus⟩ := exists_isPLHomeomorphOn_union
    hminus.isPolyhedron hplus.isPolyhedron hf₀ hf₁ hagree hsurj
  have hunion :
      (P ×ˢ Icc (-1 : ℝ) 0) ∪ (P ×ˢ Icc (0 : ℝ) 1) =
        P ×ˢ Icc (-1 : ℝ) 1 := by
    ext z
    constructor
    · rintro (⟨hz, hzl, hzr⟩ | ⟨hz, hzl, hzr⟩)
      · exact ⟨hz, hzl, hzr.trans (by norm_num)⟩
      · exact ⟨hz, (by norm_num : (-1 : ℝ) ≤ 0).trans hzl, hzr⟩
    · rintro ⟨hz, hzl, hzr⟩
      by_cases ht : z.2 ≤ 0
      · exact Or.inl ⟨hz, hzl, ht⟩
      · exact Or.inr ⟨hz, (lt_of_not_ge ht).le, hzr⟩
  rw [hunion] at hρ
  refine ⟨ρ, hρ, ?_, ?_, ?_⟩
  · intro x hx
    have hxminus : (x, (0 : ℝ)) ∈ P ×ˢ Icc (-1 : ℝ) 0 := ⟨hx, by norm_num⟩
    have hxmid : (x, (0 : ℝ)) ∈ P ×ˢ {(0 : ℝ)} := ⟨hx, rfl⟩
    exact (hρminus hxminus).trans (hf₀g hxmid)
  · exact hρminus.image_eq.trans hf₀.image_eq
  · exact hρplus.image_eq.trans hf₁.image_eq

private theorem IsPLHomeomorphOn.image_stdSimplexBoundary_of_map_disk
    {S A : Set E} {S' A' : Set F} (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S')
    {q : (Fin 3 → ℝ) → E} (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) A)
    (hAS : A ⊆ S) {q' : (Fin 3 → ℝ) → F}
    (hq' : IsPLHomeomorphOn q' (stdSimplex ℝ (Fin 3)) A') (hA'S' : A' ⊆ S')
    {f : E → F} (hf : IsPLHomeomorphOn f S S') (hfA : f '' A = A') :
    f '' (q '' stdSimplexBoundary 2) = q' '' stdSimplexBoundary 2 := by
  have hcl : closure (S \ A) ⊆ S := closure_minimal sdiff_subset hS.isPolyhedron.isClosed
  rw [← hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hAS,
    hf.bijOn.injOn.image_inter hAS hcl, hfA,
    hf.image_closure hS.isPolyhedron.isCompact sdiff_subset,
    hf.bijOn.injOn.image_sdiff_subset hAS, hf.image_eq, hfA,
    hS'.inter_closure_sdiff_eq_image_stdSimplexBoundary hq' hA'S']

private theorem IsPLHomeomorphOn.image_stdSimplexBoundary_prism_bottom_union_side_of_complex
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsPLBall 2 K.space)
    {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) K.space)
    {a b : ℝ} (hab : a < b) {q : (Fin 3 → ℝ) → E × ℝ}
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3))
      (K.space ×ˢ {a} ∪ (r '' stdSimplexBoundary 2) ×ˢ Icc a b)) :
    q '' stdSimplexBoundary 2 = (r '' stdSimplexBoundary 2) ×ˢ {b} := by
  classical
  let J := r '' stdSimplexBoundary 2
  let S := K.space ×ˢ {a, b} ∪ J ×ˢ Icc a b
  let A := K.space ×ˢ {a} ∪ J ×ˢ Icc a b
  have hprod : IsPLBall 3 (K.space ×ˢ Icc a b) :=
    isPLBall_three_prod hK (isPLBall_Icc hab)
  obtain ⟨T, hTfin, hTspace⟩ := hprod.isPolyhedron.exists_simplicialComplex
  let _ : Finite T.faces := hTfin.to_subtype
  have hT : IsPLBall 3 T.space := hTspace.symm ▸ hprod
  have hboundary := boundaryComplex_space_prism K hK hab T hTspace
  have hJ : J = (boundaryComplex 2 K).space :=
    hr.image_stdSimplexBoundary_eq_boundaryComplex K rfl
  rw [← hJ] at hboundary
  have hS : IsPLSphere 2 S := by
    change IsPLSphere 2 (K.space ×ˢ {a, b} ∪ J ×ˢ Icc a b)
    rw [← hboundary]
    exact isPLSphere_boundaryComplex_space_of_isPLBall T hT
  have hJK : J ⊆ K.space := (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  have hAS : A ⊆ S := union_subset
    (fun _ hx => Or.inl ⟨hx.1, Or.inl hx.2⟩) subset_union_right
  have hdiff : S \ A = (K.space \ J) ×ˢ {b} := by
    ext z
    constructor
    · rintro ⟨⟨hzK, hza | hzb⟩ | hzside, hzA⟩
      · exact (hzA (Or.inl ⟨hzK, hza⟩)).elim
      · refine ⟨⟨hzK, fun hzJ => hzA (Or.inr ⟨hzJ, ?_⟩)⟩, hzb⟩
        rw [show z.2 = b from hzb]
        exact ⟨hab.le, le_rfl⟩
      · exact (hzA (Or.inr hzside)).elim
    · rintro ⟨⟨hzK, hzJ⟩, hzb⟩
      refine ⟨Or.inl ⟨hzK, Or.inr hzb⟩, ?_⟩
      rintro (⟨_, hza⟩ | ⟨hzJ', _⟩)
      · exact hab.ne (hza.symm.trans hzb)
      · exact hzJ hzJ'
  have hcl : closure (S \ A) = K.space ×ˢ {b} := by
    rw [hdiff, closure_prod_eq, hr.closure_sdiff_image_stdSimplexBoundary,
      isClosed_singleton.closure_eq]
  have hmeet : A ∩ (K.space ×ˢ {b}) = J ×ˢ {b} := by
    ext z
    constructor
    · rintro ⟨hzbase | hzside, hz⟩
      · exact (hab.ne (hzbase.2.symm.trans hz.2)).elim
      · exact ⟨hzside.1, hz.2⟩
    · rintro ⟨hzJ, hzb⟩
      refine ⟨Or.inr ⟨hzJ, ?_⟩, hJK hzJ, hzb⟩
      rw [show z.2 = b from hzb]
      exact ⟨hab.le, le_rfl⟩
  have h := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hAS
  rw [hcl, hmeet] at h
  exact h.symm

open Classical in
theorem exists_isPLHomeomorphOn_centered_prism_map_boundary_circles
    {P : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) P)
    (K₀ K₁ : Geometry.SimplicialComplex ℝ F) [Finite K₀.faces] [Finite K₁.faces]
    (hK₀ : IsPLBall 3 K₀.space) (hK₁ : IsPLBall 3 K₁.space) {D Q₀ Q₁ : Set F}
    (hD₀ : D ⊆ (boundaryComplex 3 K₀).space)
    (hD₁ : D ⊆ (boundaryComplex 3 K₁).space) (hinter : K₀.space ∩ K₁.space = D)
    {q₀ q₁ : (Fin 3 → ℝ) → F}
    (hq₀ : IsPLHomeomorphOn q₀ (stdSimplex ℝ (Fin 3)) Q₀)
    (hq₁ : IsPLHomeomorphOn q₁ (stdSimplex ℝ (Fin 3)) Q₁)
    (hQ₀ : Q₀ ⊆ (boundaryComplex 3 K₀).space)
    (hQ₁ : Q₁ ⊆ (boundaryComplex 3 K₁).space)
    (hdis₀ : Disjoint D Q₀) (hdis₁ : Disjoint D Q₁)
    {g : E → F} (hg : IsPLHomeomorphOn g P D) :
    ∃ ρ : E × ℝ → F,
      IsPLHomeomorphOn ρ (P ×ˢ Icc (-1 : ℝ) 1) (K₀.space ∪ K₁.space) ∧
      (∀ x ∈ P, ρ (x, 0) = g x) ∧
      ρ '' (P ×ˢ Icc (-1 : ℝ) 0) = K₀.space ∧
      ρ '' (P ×ˢ Icc (0 : ℝ) 1) = K₁.space ∧
      ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(-1 / 2 : ℝ)}) =
        q₀ '' stdSimplexBoundary 2 ∧
      ρ '' ((r '' stdSimplexBoundary 2) ×ˢ {(1 / 2 : ℝ)}) =
        q₁ '' stdSimplexBoundary 2 := by
  let _ : DecidableEq F := Classical.decEq _
  let _ : DecidableEq (E × ℝ) := Classical.decEq _
  let J := r '' stdSimplexBoundary 2
  have hP : IsPLBall 2 P := ⟨r, hr⟩
  obtain ⟨L, hLfin, hLspace⟩ := hP.isPolyhedron.exists_simplicialComplex
  let _ : Finite L.faces := hLfin.to_subtype
  have hL : IsPLBall 2 L.space := hLspace.symm ▸ hP
  have hJ : J = (boundaryComplex 2 L).space :=
    hr.image_stdSimplexBoundary_eq_boundaryComplex L hLspace
  have hminus : IsPLBall 3 (P ×ˢ Icc (-1 : ℝ) 0) :=
    isPLBall_three_prod hP (isPLBall_Icc (by norm_num))
  have hplus : IsPLBall 3 (P ×ˢ Icc (0 : ℝ) 1) :=
    isPLBall_three_prod hP (isPLBall_Icc (by norm_num))
  obtain ⟨R₀, hR₀fin, hR₀space⟩ := hminus.isPolyhedron.exists_simplicialComplex
  obtain ⟨R₁, hR₁fin, hR₁space⟩ := hplus.isPolyhedron.exists_simplicialComplex
  let _ : Finite R₀.faces := hR₀fin.to_subtype
  let _ : Finite R₁.faces := hR₁fin.to_subtype
  let _ : Finite (boundaryComplex 3 R₀).faces :=
    (boundaryComplex_faces_finite 3 R₀).to_subtype
  let _ : Finite (boundaryComplex 3 R₁).faces :=
    (boundaryComplex_faces_finite 3 R₁).to_subtype
  let _ : Finite (boundaryComplex 3 K₀).faces :=
    (boundaryComplex_faces_finite 3 K₀).to_subtype
  let _ : Finite (boundaryComplex 3 K₁).faces :=
    (boundaryComplex_faces_finite 3 K₁).to_subtype
  have hR₀ : IsPLBall 3 R₀.space := hR₀space.symm ▸ hminus
  have hR₁ : IsPLBall 3 R₁.space := hR₁space.symm ▸ hplus
  have hboundary₀ := boundaryComplex_space_prism L hL (by norm_num : (-1 : ℝ) < 0)
    R₀ (hLspace.symm ▸ hR₀space)
  have hboundary₁ := boundaryComplex_space_prism L hL (by norm_num : (0 : ℝ) < 1)
    R₁ (hLspace.symm ▸ hR₁space)
  rw [hLspace, ← hJ] at hboundary₀ hboundary₁
  let M₀ : Set (E × ℝ) := P ×ˢ {(0 : ℝ)}
  let M₁ : Set (E × ℝ) := P ×ˢ {(0 : ℝ)}
  let A₀ : Set (E × ℝ) :=
    P ×ˢ {(-1 : ℝ)} ∪ J ×ˢ Icc (-1 : ℝ) (-1 / 2 : ℝ)
  let B₁ : Set (E × ℝ) :=
    P ×ˢ {(0 : ℝ)} ∪ J ×ˢ Icc (0 : ℝ) (1 / 2 : ℝ)
  let S₀ : Set (E × ℝ) := (boundaryComplex 3 R₀).space
  let S₁ : Set (E × ℝ) := (boundaryComplex 3 R₁).space
  have hM₀ : IsPLBall 2 M₀ :=
    hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const 0)
  have hM₁ : IsPLBall 2 M₁ :=
    hP.of_isPLHomeomorphOn (hP.isPolyhedron.isPLHomeomorphOn_prod_const 0)
  have hM₀S : M₀ ⊆ S₀ := by
    change M₀ ⊆ (boundaryComplex 3 R₀).space
    rw [hboundary₀]
    rintro z ⟨hz, ht⟩
    exact Or.inl ⟨hz, Or.inr ht⟩
  have hM₁S : M₁ ⊆ S₁ := by
    change M₁ ⊆ (boundaryComplex 3 R₁).space
    rw [hboundary₁]
    rintro z ⟨hz, ht⟩
    exact Or.inl ⟨hz, Or.inl ht⟩
  have hA₀ : IsPLBall 2 A₀ := by
    simpa only [A₀, hLspace, ← hJ] using
      isPLBall_prism_bottom_union_side L hL (by norm_num : (-1 : ℝ) < -1 / 2)
  obtain ⟨p₀, hp₀⟩ := id hA₀
  have hp₀boundary : p₀ '' stdSimplexBoundary 2 = J ×ˢ {(-1 / 2 : ℝ)} := by
    have hp₀' : IsPLHomeomorphOn p₀ (stdSimplex ℝ (Fin 3))
        (L.space ×ˢ {(-1 : ℝ)} ∪ (r '' stdSimplexBoundary 2) ×ˢ
          Icc (-1 : ℝ) (-1 / 2 : ℝ)) := by
      simpa only [A₀, J, hLspace] using hp₀
    simpa only [J] using
      (hLspace.symm ▸ hr).image_stdSimplexBoundary_prism_bottom_union_side_of_complex L hL
        (by norm_num : (-1 : ℝ) < -1 / 2) hp₀'
  have hA₀S : A₀ ⊆ S₀ := by
    change A₀ ⊆ (boundaryComplex 3 R₀).space
    rw [hboundary₀]
    rintro z (hz | hz)
    · exact Or.inl ⟨hz.1, Or.inl hz.2⟩
    · exact Or.inr ⟨hz.1, hz.2.1, hz.2.2.trans (by norm_num)⟩
  have hM₀A₀ : Disjoint M₀ A₀ := by
    apply disjoint_left.mpr
    rintro z hzM (hzA | hzA)
    · have ht0 : z.2 = 0 := hzM.2
      have htm : z.2 = -1 := hzA.2
      linarith
    · have ht0 : z.2 = 0 := hzM.2
      linarith [hzA.2.2]
  have hB₁ : IsPLBall 2 B₁ := by
    simpa only [B₁, hLspace, ← hJ] using
      isPLBall_prism_bottom_union_side L hL (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨b₁, hb₁⟩ := id hB₁
  have hb₁boundary : b₁ '' stdSimplexBoundary 2 = J ×ˢ {(1 / 2 : ℝ)} := by
    have hb₁' : IsPLHomeomorphOn b₁ (stdSimplex ℝ (Fin 3))
        (L.space ×ˢ {(0 : ℝ)} ∪ (r '' stdSimplexBoundary 2) ×ˢ
          Icc (0 : ℝ) (1 / 2 : ℝ)) := by
      simpa only [B₁, J, hLspace] using hb₁
    simpa only [J] using
      (hLspace.symm ▸ hr).image_stdSimplexBoundary_prism_bottom_union_side_of_complex L hL
        (by norm_num : (0 : ℝ) < 1 / 2) hb₁'
  have hB₁S : B₁ ⊆ S₁ := by
    change B₁ ⊆ (boundaryComplex 3 R₁).space
    rw [hboundary₁]
    rintro z (hz | hz)
    · exact Or.inl ⟨hz.1, Or.inl hz.2⟩
    · exact Or.inr ⟨hz.1, hz.2.1, hz.2.2.trans (by norm_num)⟩
  let A₁ : Set (E × ℝ) := closure (S₁ \ B₁)
  have hS₁ : IsPLSphere 2 S₁ := isPLSphere_boundaryComplex_space_of_isPLBall R₁ hR₁
  have hA₁ : IsPLBall 2 A₁ := hS₁.isPLBall_closure_sdiff hB₁ hB₁S
  obtain ⟨p₁, hp₁⟩ := id hA₁
  have hp₁boundary : p₁ '' stdSimplexBoundary 2 = J ×ˢ {(1 / 2 : ℝ)} := by
    calc
      p₁ '' stdSimplexBoundary 2 = A₁ ∩ B₁ :=
        hS₁.image_stdSimplexBoundary_complement hB₁ hB₁S hp₁
      _ = B₁ ∩ A₁ := inter_comm A₁ B₁
      _ = b₁ '' stdSimplexBoundary 2 :=
        hS₁.inter_closure_sdiff_eq_image_stdSimplexBoundary hb₁ hB₁S
      _ = J ×ˢ {(1 / 2 : ℝ)} := hb₁boundary
  have hA₁S : A₁ ⊆ S₁ := closure_minimal sdiff_subset hS₁.isPolyhedron.isClosed
  have hS₁diff : S₁ \ B₁ ⊆ {z : E × ℝ | 1 / 2 ≤ z.2} := by
    rintro z ⟨hzS, hzB⟩
    change z ∈ (boundaryComplex 3 R₁).space at hzS
    rw [hboundary₁] at hzS
    rcases hzS with ⟨hzP, ht | ht⟩ | ⟨hzJ, ht⟩
    · exact (hzB (Or.inl ⟨hzP, ht⟩)).elim
    · change 1 / 2 ≤ z.2
      rw [show z.2 = 1 from ht]
      norm_num
    · exact le_of_not_gt fun hlt => hzB (Or.inr ⟨hzJ, ht.1, hlt.le⟩)
  have hA₁height : A₁ ⊆ {z : E × ℝ | 1 / 2 ≤ z.2} :=
    closure_minimal hS₁diff (isClosed_Ici.preimage continuous_snd)
  have hM₁A₁ : Disjoint M₁ A₁ := by
    apply disjoint_left.mpr
    intro z hzM hzA
    have ht0 : z.2 = 0 := hzM.2
    have hth := hA₁height hzA
    change 1 / 2 ≤ z.2 at hth
    rw [ht0] at hth
    norm_num at hth
  have hgM : IsPLHomeomorphOn (g ∘ Prod.fst) M₀ D :=
    hP.isPolyhedron.isPLHomeomorphOn_fst_prod_const 0 |>.trans hg
  have hQ₀ball : IsPLBall 2 Q₀ := ⟨q₀, hq₀⟩
  have hQ₁ball : IsPLBall 2 Q₁ := ⟨q₁, hq₁⟩
  obtain ⟨f₀, hf₀, hf₀g, hf₀A⟩ :=
    exists_isPLHomeomorphOn_map_disk_pair_of_boundaryComplex R₀ K₀ hR₀ hK₀
      hM₀ hM₀S hA₀ hA₀S hM₀A₀ hQ₀ball hQ₀ hdis₀ hgM hD₀
  obtain ⟨f₁, hf₁, hf₁g, hf₁A⟩ :=
    exists_isPLHomeomorphOn_map_disk_pair_of_boundaryComplex R₁ K₁ hR₁ hK₁
      hM₁ hM₁S hA₁ hA₁S hM₁A₁ hQ₁ball hQ₁ hdis₁ hgM hD₁
  have hf₀S : IsPLHomeomorphOn f₀ S₀ (boundaryComplex 3 K₀).space := by
    have h := hf₀.restrict (isPolyhedron_space (boundaryComplex 3 R₀))
      (boundaryComplex_space_subset 3 R₀)
    rw [← boundaryComplex_space_of_isPLHomeomorphOn R₀ K₀
      hR₀.isCombinatorialManifoldWithBoundary hf₀] at h
    exact h
  have hf₁S : IsPLHomeomorphOn f₁ S₁ (boundaryComplex 3 K₁).space := by
    have h := hf₁.restrict (isPolyhedron_space (boundaryComplex 3 R₁))
      (boundaryComplex_space_subset 3 R₁)
    rw [← boundaryComplex_space_of_isPLHomeomorphOn R₁ K₁
      hR₁.isCombinatorialManifoldWithBoundary hf₁] at h
    exact h
  have hcircle₀ : f₀ '' (J ×ˢ {(-1 / 2 : ℝ)}) = q₀ '' stdSimplexBoundary 2 := by
    rw [← hp₀boundary]
    exact IsPLHomeomorphOn.image_stdSimplexBoundary_of_map_disk
      (isPLSphere_boundaryComplex_space_of_isPLBall R₀ hR₀)
      (isPLSphere_boundaryComplex_space_of_isPLBall K₀ hK₀)
      hp₀ hA₀S hq₀ hQ₀ hf₀S hf₀A
  have hcircle₁ : f₁ '' (J ×ˢ {(1 / 2 : ℝ)}) = q₁ '' stdSimplexBoundary 2 := by
    rw [← hp₁boundary]
    exact IsPLHomeomorphOn.image_stdSimplexBoundary_of_map_disk hS₁
      (isPLSphere_boundaryComplex_space_of_isPLBall K₁ hK₁)
      hp₁ hA₁S hq₁ hQ₁ hf₁S hf₁A
  rw [hR₀space] at hf₀
  rw [hR₁space] at hf₁
  have hsource :
      (P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1) = P ×ˢ {(0 : ℝ)} := by
    ext ⟨x, t⟩
    constructor
    · rintro ⟨⟨hx, -, htle⟩, ⟨-, htge, -⟩⟩
      exact ⟨hx, le_antisymm htle htge⟩
    · rintro ⟨hx, ht⟩
      change t = 0 at ht
      subst t
      exact ⟨⟨hx, by norm_num, by norm_num⟩, ⟨hx, by norm_num, by norm_num⟩⟩
  have hagree : EqOn f₀ f₁
      ((P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1)) := by
    intro z hz
    have hzmid : z ∈ P ×ˢ {(0 : ℝ)} := hsource.subset hz
    exact (hf₀g hzmid).trans (hf₁g hzmid).symm
  have hsurj : SurjOn f₀
      ((P ×ˢ Icc (-1 : ℝ) 0) ∩ (P ×ˢ Icc (0 : ℝ) 1))
      (K₀.space ∩ K₁.space) := by
    intro y hy
    have hyD : y ∈ D := hinter.subset hy
    obtain ⟨x, hx, hxy⟩ := hg.bijOn.surjOn hyD
    have hxmid : (x, (0 : ℝ)) ∈ P ×ˢ {(0 : ℝ)} := ⟨hx, rfl⟩
    refine ⟨(x, 0), hsource.symm.subset hxmid, ?_⟩
    exact (hf₀g hxmid).trans hxy
  obtain ⟨ρ, hρ, hρminus, hρplus⟩ := exists_isPLHomeomorphOn_union
    hminus.isPolyhedron hplus.isPolyhedron hf₀ hf₁ hagree hsurj
  have hunion :
      (P ×ˢ Icc (-1 : ℝ) 0) ∪ (P ×ˢ Icc (0 : ℝ) 1) = P ×ˢ Icc (-1 : ℝ) 1 := by
    ext z
    constructor
    · rintro (⟨hz, hzl, hzr⟩ | ⟨hz, hzl, hzr⟩)
      · exact ⟨hz, hzl, hzr.trans (by norm_num)⟩
      · exact ⟨hz, (by norm_num : (-1 : ℝ) ≤ 0).trans hzl, hzr⟩
    · rintro ⟨hz, hzl, hzr⟩
      by_cases ht : z.2 ≤ 0
      · exact Or.inl ⟨hz, hzl, ht⟩
      · exact Or.inr ⟨hz, (lt_of_not_ge ht).le, hzr⟩
  rw [hunion] at hρ
  refine ⟨ρ, hρ, ?_, hρminus.image_eq.trans hf₀.image_eq,
    hρplus.image_eq.trans hf₁.image_eq, ?_, ?_⟩
  · intro x hx
    have hxmid : (x, (0 : ℝ)) ∈ P ×ˢ {(0 : ℝ)} := ⟨hx, rfl⟩
    exact (hρplus ⟨hx, by norm_num⟩).trans (hf₁g hxmid)
  · have hsub : J ×ˢ {(-1 / 2 : ℝ)} ⊆ P ×ˢ Icc (-1 : ℝ) 0 := by
      rintro z ⟨hzJ, ht⟩
      have hzP : z.1 ∈ P := by
        obtain ⟨x, hx, hxr⟩ := hzJ
        exact hxr ▸ hr.bijOn.mapsTo hx.1
      exact ⟨hzP, ht.symm ▸ by norm_num⟩
    exact ((hρminus.mono hsub).image_eq).trans hcircle₀
  · have hsub : J ×ˢ {(1 / 2 : ℝ)} ⊆ P ×ˢ Icc (0 : ℝ) 1 := by
      rintro z ⟨hzJ, ht⟩
      have hzP : z.1 ∈ P := by
        obtain ⟨x, hx, hxr⟩ := hzJ
        exact hxr ▸ hr.bijOn.mapsTo hx.1
      exact ⟨hzP, ht.symm ▸ by norm_num⟩
    exact ((hρplus.mono hsub).image_eq).trans hcircle₁

end DifferentialGeometry.Topology.PiecewiseLinear
