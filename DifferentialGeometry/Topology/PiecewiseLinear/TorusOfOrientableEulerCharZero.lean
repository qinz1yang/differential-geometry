/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.AnnulusCapping
import DifferentialGeometry.Topology.PiecewiseLinear.BallMarkedExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.CircleParametrization
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePrismComparison
import DifferentialGeometry.Topology.PiecewiseLinear.ConeBaseFlat
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalDiagram
import DifferentialGeometry.Topology.PiecewiseLinear.CylindricalProduct
import DifferentialGeometry.Topology.PiecewiseLinear.DiskPseudoIsotopy
import DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.LinkDimension
import DifferentialGeometry.Topology.PiecewiseLinear.MobiusEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.OneManifoldClassification
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeDerived
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage
import DifferentialGeometry.Topology.PiecewiseLinear.StdSimplexCone
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceAnnulusComplement
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSpanningTrees

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Annulus

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_cone_disk_of_isPLSphere_one {C : Set E} (hC : IsPLSphere 1 C) :
    ∃ (D : Set (E × ℝ)) (r : (Fin 3 → ℝ) → E × ℝ),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D ∧
      r '' stdSimplexBoundary 2 = C ×ˢ {0} ∧
      ∀ y ∈ D, 0 ≤ y.2 ∧ (y.2 = 0 → y ∈ C ×ˢ ({0} : Set ℝ)) := by
  classical
  have hB : IsPolyhedron (C ×ˢ ({0} : Set ℝ)) := isPolyhedron_prod_singleton hC.isPolyhedron 0
  obtain ⟨Lc, hLcfin, hLcspace⟩ := hB.exists_simplicialComplex
  let _ : Finite Lc.faces := hLcfin.to_subtype
  have hLc0 : ∀ q ∈ Lc.space, (q : E × ℝ).2 = 0 := by
    rw [hLcspace]
    rintro q ⟨-, hq⟩
    exact hq
  have hbase := isConeBase_of_snd_eq_zero Lc hLc0 (0 : E)
  have hsph : IsPLSphere 1 Lc.space :=
    hLcspace ▸ hC.of_isPLHomeomorphOn (hC.isPolyhedron.isPLHomeomorphOn_prod_const 0)
  obtain ⟨f, hf⟩ := hsph
  have hf' : IsPLHomeomorphOn f
      (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).space Lc.space := by
    rw [simplexBoundary_stdVertices_space]
    exact hf
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  obtain ⟨g, hg, hgf, -, -⟩ := exists_isPLHomeomorphOn_coneComplex (isConeBase_std 1) hbase hf'
  rw [coneComplex_std_space] at hg
  refine ⟨(coneComplex hbase).space, g, hg, ?_, ?_⟩
  · rw [← simplexBoundary_stdVertices_space, hgf.image_eq, hf'.image_eq, hLcspace]
  · intro y hy
    rcases (mem_coneComplex_space_iff hbase).mp hy with rfl | ⟨z, hz, s, hs, hs1, rfl⟩
    · refine ⟨zero_le_one, fun h => ?_⟩
      norm_num at h
    · have hz0 := hLc0 z hz
      have hy2 : ((((0 : E), (1 : ℝ)) : E × ℝ) + s • (z - ((0 : E), (1 : ℝ)))).2 = 1 - s := by
        simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul, hz0]
        ring
      rw [hy2]
      refine ⟨by linarith, fun h => ?_⟩
      have hs' : s = 1 := by linarith
      rw [hs', one_smul, add_sub_cancel]
      exact hLcspace ▸ hz

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero
    (R : Geometry.SimplicialComplex ℝ E) [Finite R.faces]
    (hR : IsCombinatorialManifoldWithBoundary 2 R) (hRc : IsConnected R.space)
    (hχ : eulerChar R = 0) {C₀ C₁ : Set E} (hC₀ : IsPLSphere 1 C₀) (hC₁ : IsPLSphere 1 C₁)
    (hdis : Disjoint C₀ C₁) (hbd : (boundaryComplex 2 R).space = C₀ ∪ C₁) :
    ∃ h : (Fin 3 → ℝ) × ℝ → E,
      IsPLHomeomorphOn h (stdSimplexBoundary 2 ×ˢ Icc 0 1) R.space ∧
      h '' (stdSimplexBoundary 2 ×ˢ {0}) = C₀ ∧ h '' (stdSimplexBoundary 2 ×ˢ {1}) = C₁ := by
  classical
  have hRpoly := isPolyhedron_space R
  obtain ⟨R', hR'fin, hR'space⟩ :=
    (isPolyhedron_prod_singleton hRpoly (0 : ℝ)).exists_simplicialComplex
  let _ : Finite R'.faces := hR'fin.to_subtype
  have hι : IsPLHomeomorphOn (fun x : E => (x, (0 : ℝ))) R.space R'.space := by
    rw [hR'space]
    exact hRpoly.isPLHomeomorphOn_prod_const 0
  have hR' : IsCombinatorialManifoldWithBoundary 2 R' := hR.of_isPLHomeomorphOn hι
  have hR'c : IsConnected R'.space := by
    rw [hR'space, prod_singleton]
    exact hRc.image _ (continuous_id.prodMk continuous_const).continuousOn
  have hR'χ : eulerChar R' = 0 := (eulerChar_eq_of_isPLHomeomorphOn R R' hι).symm.trans hχ
  have hR'bd : (boundaryComplex 2 R').space = C₀ ×ˢ {0} ∪ C₁ ×ˢ {0} := by
    have h := boundaryComplex_space_of_isPLHomeomorphOn (n := 1) R R' hR hι
    rw [prod_singleton, prod_singleton, ← image_union, ← hbd]
    convert h
  have hCR : C₀ ∪ C₁ ⊆ R.space := hbd ▸ boundaryComplex_space_subset 2 R
  have hR'0 : ∀ y ∈ R'.space, y.2 = 0 := by
    rw [hR'space]
    rintro y ⟨-, hy⟩
    exact hy
  obtain ⟨D₀, r₀, hr₀, hr₀b, hD₀⟩ := exists_cone_disk_of_isPLSphere_one hC₀
  obtain ⟨D₁', r₁', hr₁', hr₁'b, hD₁'⟩ := exists_cone_disk_of_isPLSphere_one hC₁
  let σ : E × ℝ →ᵃ[ℝ] E × ℝ :=
    ((LinearMap.id : E →ₗ[ℝ] E).prodMap (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)).toAffineMap
  have hσ (y : E × ℝ) : σ y = (y.1, -y.2) := rfl
  have hσinj : Function.Injective σ := by
    intro a b hab
    rw [hσ, hσ, Prod.mk.injEq, neg_inj] at hab
    exact Prod.ext hab.1 hab.2
  have hD₁'poly : IsPolyhedron D₁' := IsPLBall.isPolyhedron ⟨r₁', hr₁'⟩
  have hσD : IsPLHomeomorphOn σ D₁' (σ '' D₁') :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hD₁'poly
      ((isPiecewiseAffineOn_of_affine σ isOpen_univ).mono_of_isPolyhedron hD₁'poly
        (subset_univ _)) hσinj.injOn.bijOn_image
  have hr₁ : IsPLHomeomorphOn (σ ∘ r₁') (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (σ '' D₁') := hr₁'.trans hσD
  have hr₁b : (σ ∘ r₁') '' stdSimplexBoundary 2 = C₁ ×ˢ {0} := by
    rw [image_comp, hr₁'b]
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rw [hσ]
      exact ⟨hz.1, by rw [mem_singleton_iff.mp hz.2, neg_zero]; rfl⟩
    · intro y hy
      refine ⟨y, hy, ?_⟩
      rw [hσ]
      exact Prod.ext rfl (by rw [mem_singleton_iff.mp hy.2, neg_zero])
  have hD₁ : ∀ y ∈ σ '' D₁', y.2 ≤ 0 ∧ (y.2 = 0 → y ∈ C₁ ×ˢ ({0} : Set ℝ)) := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨h1, h2⟩ := hD₁' z hz
    rw [hσ]
    refine ⟨neg_nonpos.mpr h1, fun h => ?_⟩
    have hz0 : z.2 = 0 := neg_eq_zero.mp h
    exact ⟨(h2 hz0).1, by rw [hz0, neg_zero]; rfl⟩
  have hdisD : Disjoint D₀ (σ '' D₁') := by
    rw [disjoint_left]
    intro y hy0 hy1
    obtain ⟨a0, b0⟩ := hD₀ y hy0
    obtain ⟨a1, b1⟩ := hD₁ y hy1
    have hy2 : y.2 = 0 := le_antisymm a1 a0
    exact disjoint_left.mp hdis (b0 hy2).1 (b1 hy2).1
  have hmeet₀ : R'.space ∩ D₀ = r₀ '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro y ⟨hyR, hyD⟩
      rw [hr₀b]
      exact (hD₀ y hyD).2 (hR'0 y hyR)
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, hr₀.bijOn.mapsTo hx.1⟩
      have hmem : r₀ x ∈ C₀ ×ˢ ({0} : Set ℝ) := hr₀b ▸ mem_image_of_mem r₀ hx
      rw [hR'space]
      exact ⟨hCR (Or.inl hmem.1), hmem.2⟩
  have hmeet₁ : R'.space ∩ σ '' D₁' = (σ ∘ r₁') '' stdSimplexBoundary 2 := by
    apply Subset.antisymm
    · rintro y ⟨hyR, hyD⟩
      rw [hr₁b]
      exact (hD₁ y hyD).2 (hR'0 y hyR)
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨?_, hr₁.bijOn.mapsTo hx.1⟩
      have hmem : (σ ∘ r₁') x ∈ C₁ ×ˢ ({0} : Set ℝ) := hr₁b ▸ mem_image_of_mem _ hx
      rw [hR'space]
      exact ⟨hCR (Or.inr hmem.1), hmem.2⟩
  have hboundary : (boundaryComplex 2 R').space =
      r₀ '' stdSimplexBoundary 2 ∪ (σ ∘ r₁') '' stdSimplexBoundary 2 := by
    rw [hR'bd, hr₀b, hr₁b]
  obtain ⟨P, hPfin, hP, hPc, hPχ, hPspace⟩ :=
    hR'.exists_closed_of_disk_pair R' hR'c hr₀ hr₁ hdisD hmeet₀ hmeet₁ (by convert hboundary)
  let _ : Finite P.faces := hPfin.to_subtype
  have hPχ' : SimplicialComplex.faceEulerChar P.toPreAbstractSimplicialComplex = 2 := by
    rw [hR'χ] at hPχ
    exact hPχ
  have hPsph : IsPLSphere 2 P.space := hP.isPLSphere_two_of_faceEulerChar_eq_two P hPc hPχ'
  have hR'P : R'.space ⊆ P.space := fun y hy => hPspace ▸ Or.inl (Or.inl hy)
  have hD₀P : D₀ ⊆ P.space := fun y hy => hPspace ▸ Or.inl (Or.inr hy)
  have hD₁P : σ '' D₁' ⊆ P.space := fun y hy => hPspace ▸ Or.inr hy
  have hΔ : IsPLBall 2 (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := isPLBall_stdSimplex 2
  have hΔpoly : IsPolyhedron (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) := hΔ.isPolyhedron
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hJpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPolyhedron_space _
  obtain ⟨Kd, hKdfin, hKdspace⟩ := hΔpoly.exists_simplicialComplex
  let _ : Finite Kd.faces := hKdfin.to_subtype
  have hKd : IsPLBall 2 Kd.space := hKdspace ▸ hΔ
  have hid : IsPLHomeomorphOn id (Convexity.StdSimplex.coordinateSet ℝ (Fin (1 + 2))) Kd.space := by
    rw [hKdspace]
    exact isPLHomeomorphOn_id_of_isHPolytope (isHPolytope_stdSimplex _)
  have hprism := isPLBall_three_prod hΔ (isPLBall_Icc (zero_lt_one' ℝ))
  obtain ⟨A, hAfin, hAspace⟩ := hprism.isPolyhedron.exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  have hA : IsPLBall 3 A.space := hAspace ▸ hprism
  have hAbd : (boundaryComplex 3 A).space = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ {0, 1} ∪
      stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := by
    have h := boundaryComplex_space_prism Kd hKd (zero_lt_one' ℝ) A (by rw [hAspace, hKdspace])
    have h2 := boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex (n := 1) Kd hid
    rw [image_id, simplexBoundary_stdVertices_space] at h2
    rw [← hKdspace, ← h2]
    convert h using 5
  have hS' : IsPLSphere 2 (boundaryComplex 3 A).space := by
    convert isPLSphere_boundaryComplex_space_of_isPLBall A hA
  have hι₀ := hΔpoly.isPLHomeomorphOn_prod_const (0 : ℝ)
  have hι₁ := hΔpoly.isPLHomeomorphOn_prod_const (1 : ℝ)
  have hD₀'S : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ) ⊆ (boundaryComplex 3 A).space := by
    rw [hAbd]
    rintro y ⟨hy1, hy2⟩
    exact Or.inl ⟨hy1, Or.inl hy2⟩
  have hD₁'S : Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ) ⊆ (boundaryComplex 3 A).space := by
    rw [hAbd]
    rintro y ⟨hy1, hy2⟩
    exact Or.inl ⟨hy1, Or.inr hy2⟩
  have hdis' : Disjoint (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ))
      (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ)) := by
    rw [disjoint_left]
    rintro y ⟨-, h0⟩ ⟨-, h1⟩
    rw [mem_singleton_iff] at h0 h1
    rw [h0] at h1
    exact zero_ne_one h1
  have hg := hr₀.symm.trans hι₀
  obtain ⟨G, hG, hGg, hGD₁⟩ := exists_isPLHomeomorphOn_map_disk_pair_eqOn_disk hPsph hS'
    ⟨r₀, hr₀⟩ hD₀P ⟨σ ∘ r₁', hr₁⟩ hD₁P hdisD (hΔ.of_isPLHomeomorphOn hι₁) hD₁'S hdis' hg hD₀'S
  have hGD₀ : G '' D₀ = Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ) := hGg.image_eq.trans hg.image_eq
  have hB₀D : r₀ '' stdSimplexBoundary 2 ⊆ D₀ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hr₀.bijOn.mapsTo hx.1
  have hGB₀ : G '' (r₀ '' stdSimplexBoundary 2) = stdSimplexBoundary 2 ×ˢ ({0} : Set ℝ) := by
    rw [(hGg.mono hB₀D).image_eq, ← image_comp,
      (hr₀.trans hg).image_stdSimplexBoundary_congr hι₀, prod_singleton]
  have hGB₁ : G '' ((σ ∘ r₁') '' stdSimplexBoundary 2) =
      stdSimplexBoundary 2 ×ˢ ({1} : Set ℝ) := by
    have hGr : IsPLHomeomorphOn (G ∘ (σ ∘ r₁')) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ)) := by
      have h := hr₁.trans (hG.restrict (IsPLBall.isPolyhedron ⟨_, hr₁⟩) hD₁P)
      rwa [hGD₁] at h
    rw [← image_comp, hGr.image_stdSimplexBoundary_congr hι₁, prod_singleton]
  have hGinj : InjOn G P.space := hG.bijOn.injOn
  have hlat : G '' R'.space = stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hxP : x ∈ P.space := hR'P hx
      have hyS : G x ∈ (boundaryComplex 3 A).space := hG.bijOn.mapsTo hxP
      rw [hAbd] at hyS
      rcases hyS with ⟨hyΔ, hy01⟩ | hy
      · rcases hy01 with hy0 | hy1
        · obtain ⟨x', hx', hxx'⟩ : G x ∈ G '' D₀ := hGD₀ ▸ ⟨hyΔ, hy0⟩
          have hxx : x' = x := hGinj (hD₀P hx') hxP hxx'
          subst hxx
          have hxB : x' ∈ r₀ '' stdSimplexBoundary 2 := hmeet₀ ▸ ⟨hx, hx'⟩
          have hmem := hGB₀ ▸ mem_image_of_mem G hxB
          refine ⟨hmem.1, ?_⟩
          rw [mem_singleton_iff.mp hmem.2]
          exact ⟨le_rfl, zero_le_one⟩
        · obtain ⟨x', hx', hxx'⟩ : G x ∈ G '' (σ '' D₁') := hGD₁ ▸ ⟨hyΔ, hy1⟩
          have hxx : x' = x := hGinj (hD₁P hx') hxP hxx'
          subst hxx
          have hxB : x' ∈ (σ ∘ r₁') '' stdSimplexBoundary 2 := hmeet₁ ▸ ⟨hx, hx'⟩
          have hmem := hGB₁ ▸ mem_image_of_mem G hxB
          refine ⟨hmem.1, ?_⟩
          rw [mem_singleton_iff.mp hmem.2]
          exact ⟨zero_le_one, le_rfl⟩
      · exact hy
    · intro y hy
      have hyS : y ∈ (boundaryComplex 3 A).space := by
        rw [hAbd]
        exact Or.inr hy
      rw [← hG.image_eq] at hyS
      obtain ⟨x, hxP, rfl⟩ := hyS
      rw [hPspace] at hxP
      rcases hxP with (hxR | hxD₀) | hxD₁
      · exact mem_image_of_mem G hxR
      · have hy0 : G x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({0} : Set ℝ) :=
          hGD₀ ▸ mem_image_of_mem G hxD₀
        have hyB : G x ∈ stdSimplexBoundary 2 ×ˢ ({0} : Set ℝ) := ⟨hy.1, hy0.2⟩
        rw [← hGB₀] at hyB
        obtain ⟨x', hx'B, hx'x⟩ := hyB
        exact ⟨x', (hmeet₀.symm ▸ hx'B : x' ∈ R'.space ∩ D₀).1, hx'x⟩
      · have hy1 : G x ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ ({1} : Set ℝ) :=
          hGD₁ ▸ mem_image_of_mem G hxD₁
        have hyB : G x ∈ stdSimplexBoundary 2 ×ˢ ({1} : Set ℝ) := ⟨hy.1, hy1.2⟩
        rw [← hGB₁] at hyB
        obtain ⟨x', hx'B, hx'x⟩ := hyB
        exact ⟨x', (hmeet₁.symm ▸ hx'B : x' ∈ R'.space ∩ σ '' D₁').1, hx'x⟩
  have hlatpoly : IsPolyhedron (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) :=
    hJpoly.prod isHPolytope_Icc.isPolyhedron
  have hlatS : stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 ⊆ (boundaryComplex 3 A).space := by
    rw [hAbd]
    exact subset_union_right
  have hinvR : Function.invFunOn G P.space '' (stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1) =
      R'.space := by
    rw [← hlat]
    exact hGinj.invFunOn_image hR'P
  have h1 := hG.symm.restrict hlatpoly hlatS
  rw [hinvR] at h1
  have hfst : IsPLHomeomorphOn Prod.fst R'.space R.space := by
    rw [hR'space]
    exact hRpoly.isPLHomeomorphOn_fst_prod_const 0
  refine ⟨Prod.fst ∘ Function.invFunOn G P.space, h1.trans hfst, ?_, ?_⟩
  · rw [image_comp, ← hGB₀, hGinj.invFunOn_image (hB₀D.trans hD₀P), hr₀b,
      fst_image_prod _ (singleton_nonempty 0)]
  · have hB₁D : (σ ∘ r₁') '' stdSimplexBoundary 2 ⊆ σ '' D₁' := by
      rintro _ ⟨x, hx, rfl⟩
      exact hr₁.bijOn.mapsTo hx.1
    rw [image_comp, ← hGB₁, hGinj.invFunOn_image (hB₁D.trans hD₁P), hr₁b,
      fst_image_prod _ (singleton_nonempty 0)]

open Classical in
theorem IsCombinatorialManifold.nonempty_homeomorph_torus_of_isPreconnected_sdiff
    (L : Geometry.SimplicialComplex ℝ E) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hLo : IsOrientable 2 L) (hχ : eulerChar L = 0)
    {J : Set E} (hJ : IsPLSphere 1 J) (hJL : J ⊆ L.space)
    (hnonsep : IsPreconnected (L.space \ J)) :
    Nonempty (L.space ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) := by
  obtain ⟨R, hRfin, hR, -, hRc, hRχ, W, ρ, -, -, -, -, hρ, -, -, -, hRbd, hmeet, hcover,
      hC₀, hC₁, hdisC⟩ :=
    hL.exists_connected_annulus_complement L hLo hJ hJL hnonsep Filter.univ_mem
  let _ : Finite R.faces := hRfin.to_subtype
  have hpair : ρ '' (J ×ˢ {(-1 : ℝ), 1}) =
      ρ '' (J ×ˢ {(-1 : ℝ)}) ∪ ρ '' (J ×ˢ {(1 : ℝ)}) := by
    rw [← image_union, ← prod_union, singleton_union]
  obtain ⟨h, hh, hh0, hh1⟩ := hR.exists_isPLHomeomorphOn_annulus_of_eulerChar_eq_zero R hRc
    (hRχ.trans hχ) hC₀ hC₁ hdisC (hRbd.trans hpair)
  let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
    (simplexBoundary_faces_finite _ _).to_subtype
  have hJm : IsPLSphere 1 (stdSimplexBoundary 2) := by
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPLSphere_simplexBoundary_std 1
  have hJmpoly := hJm.isPolyhedron
  have hJpoly := hJ.isPolyhedron
  have hJ₀ : J ×ˢ {(-1 : ℝ)} ⊆ J ×ˢ Icc (-1 : ℝ) 1 := fun z hz =>
    ⟨hz.1, by rw [mem_singleton_iff.mp hz.2]; norm_num⟩
  have hJ₁ : J ×ˢ {(1 : ℝ)} ⊆ J ×ˢ Icc (-1 : ℝ) 1 := fun z hz =>
    ⟨hz.1, by rw [mem_singleton_iff.mp hz.2]; norm_num⟩
  have hm₀ : stdSimplexBoundary 2 ×ˢ {(0 : ℝ)} ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => ⟨hz.1, by rw [mem_singleton_iff.mp hz.2]; norm_num⟩
  have hm₁ : stdSimplexBoundary 2 ×ˢ {(1 : ℝ)} ⊆ stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => ⟨hz.1, by rw [mem_singleton_iff.mp hz.2]; norm_num⟩
  have hρ₀ := hρ.restrict (isPolyhedron_prod_singleton hJpoly (-1 : ℝ)) hJ₀
  have hρ₁ := hρ.restrict (isPolyhedron_prod_singleton hJpoly (1 : ℝ)) hJ₁
  have hh₀ : IsPLHomeomorphOn h (stdSimplexBoundary 2 ×ˢ {(0 : ℝ)}) (ρ '' (J ×ˢ {(-1 : ℝ)})) := by
    have h' := hh.restrict (isPolyhedron_prod_singleton hJmpoly (0 : ℝ)) hm₀
    rwa [hh0] at h'
  have hh₁ : IsPLHomeomorphOn h (stdSimplexBoundary 2 ×ˢ {(1 : ℝ)}) (ρ '' (J ×ˢ {(1 : ℝ)})) := by
    have h' := hh.restrict (isPolyhedron_prod_singleton hJmpoly (1 : ℝ)) hm₁
    rwa [hh1] at h'
  have hβ := (((hJmpoly.isPLHomeomorphOn_prod_const (0 : ℝ)).trans hh₀).trans hρ₀.symm).trans
    (hJpoly.isPLHomeomorphOn_fst_prod_const (-1 : ℝ))
  set β := Prod.fst ∘ Function.invFunOn ρ (J ×ˢ {(-1 : ℝ)}) ∘ h ∘ fun y => (y, (0 : ℝ))
    with hβdef
  have hβρ : ∀ y ∈ stdSimplexBoundary 2, ρ (β y, -1) = h (y, 0) := by
    intro y hy
    have hz : h (y, 0) ∈ ρ '' (J ×ˢ {(-1 : ℝ)}) := hh₀.bijOn.mapsTo ⟨hy, rfl⟩
    have hw := hρ₀.symm.bijOn.mapsTo hz
    have hρw := hρ₀.bijOn.invOn_invFunOn.2 hz
    have hpt : (β y, (-1 : ℝ)) = Function.invFunOn ρ (J ×ˢ {(-1 : ℝ)}) (h (y, 0)) :=
      Prod.ext rfl (mem_singleton_iff.mp hw.2).symm
    rw [hpt]
    exact hρw
  have hγ := (((hβ.trans (hJpoly.isPLHomeomorphOn_prod_const (1 : ℝ))).trans hρ₁).trans
    hh₁.symm).trans (hJmpoly.isPLHomeomorphOn_fst_prod_const (1 : ℝ))
  set γ := Prod.fst ∘ Function.invFunOn h (stdSimplexBoundary 2 ×ˢ {(1 : ℝ)}) ∘ ρ ∘
    (fun x => (x, (1 : ℝ))) ∘ β with hγdef
  have hγh : ∀ y ∈ stdSimplexBoundary 2, h (γ y, 1) = ρ (β y, 1) := by
    intro y hy
    have hz : ρ (β y, 1) ∈ ρ '' (J ×ˢ {(1 : ℝ)}) := hρ₁.bijOn.mapsTo ⟨hβ.bijOn.mapsTo hy, rfl⟩
    have hw := hh₁.symm.bijOn.mapsTo hz
    have hhw := hh₁.bijOn.invOn_invFunOn.2 hz
    have hpt : (γ y, (1 : ℝ)) =
        Function.invFunOn h (stdSimplexBoundary 2 ×ˢ {(1 : ℝ)}) (ρ (β y, 1)) :=
      Prod.ext rfl (mem_singleton_iff.mp hw.2).symm
    rw [hpt]
    exact hhw
  have hτ₁ : IsPLHomeomorphOn (fun t : ℝ => 4 * t - 1) (Icc 0 (1 / 2)) (Icc (-1) 1) := by
    refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope
        ((4 : ℝ) • AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ 1) isHPolytope_Icc) ⟨?_, ?_, ?_⟩
    · intro t ht
      constructor <;> linarith [ht.1, ht.2]
    · intro s _ t _ hst
      simp only at hst
      linarith
    · intro y hy
      refine ⟨(y + 1) / 4, ⟨by linarith [hy.1], by linarith [hy.2]⟩, ?_⟩
      simp only
      ring
  have hτ₂ : IsPLHomeomorphOn (fun t : ℝ => 2 - 2 * t) (Icc (1 / 2) 1) (Icc 0 1) := by
    refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn isHPolytope_Icc.isPolyhedron
      (isPiecewiseAffineOn_of_affine_of_isHPolytope
        (AffineMap.const ℝ ℝ 2 - (2 : ℝ) • AffineMap.id ℝ ℝ) isHPolytope_Icc) ⟨?_, ?_, ?_⟩
    · intro t ht
      constructor <;> linarith [ht.1, ht.2]
    · intro s _ t _ hst
      simp only at hst
      linarith
    · intro y hy
      refine ⟨(2 - y) / 2, ⟨by linarith [hy.2], by linarith [hy.1]⟩, ?_⟩
      simp only
      ring
  have hf₁ := (hβ.prodMap hτ₁).trans hρ
  have hf₂ := (hγ.prodMap hτ₂).trans hh
  have hf₀ : (ρ ∘ Prod.map β fun t : ℝ => 4 * t - 1) '' (stdSimplexBoundary 2 ×ˢ {0}) =
      ρ '' (J ×ˢ {(-1 : ℝ)}) := by
    rw [image_comp, prodMap_image_prod, hβ.image_eq, image_singleton]
    norm_num
  have hg₁ : (h ∘ Prod.map γ fun t : ℝ => 2 - 2 * t) '' (stdSimplexBoundary 2 ×ˢ {1}) =
      ρ '' (J ×ˢ {(-1 : ℝ)}) := by
    rw [image_comp, prodMap_image_prod, hγ.image_eq, image_singleton, ← hh0]
    norm_num
  have hfm : (ρ ∘ Prod.map β fun t : ℝ => 4 * t - 1) '' (stdSimplexBoundary 2 ×ˢ {1 / 2}) =
      ρ '' (J ×ˢ {(1 : ℝ)}) := by
    rw [image_comp, prodMap_image_prod, hβ.image_eq, image_singleton]
    norm_num
  have hfg : EqOn (ρ ∘ Prod.map β fun t : ℝ => 4 * t - 1)
      (h ∘ Prod.map γ fun t : ℝ => 2 - 2 * t) (stdSimplexBoundary 2 ×ˢ {1 / 2}) := by
    rintro ⟨y, t⟩ ⟨hy, ht⟩
    have ht' : t = 1 / 2 := ht
    subst ht'
    change ρ (β y, 4 * (1 / 2) - 1) = h (γ y, 2 - 2 * (1 / 2))
    rw [show (4 : ℝ) * (1 / 2) - 1 = 1 by norm_num, show (2 : ℝ) - 2 * (1 / 2) = 1 by norm_num,
      hγh y hy]
  have hcyl := isCylindricalDiagram_piecewise hJmpoly hf₁ hf₂ hf₀ hg₁ hfm hfg (hmeet.trans hpair)
  rw [hcover] at hcyl
  obtain ⟨u, hu, hΦu⟩ := hcyl.exists_isPLHomeomorphOn_endMap hJmpoly
  have hv := hu.symm
  have hΦv : ∀ x ∈ stdSimplexBoundary 2,
      ((stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) (1 / 2)).piecewise
        (ρ ∘ Prod.map β fun t : ℝ => 4 * t - 1) (h ∘ Prod.map γ fun t : ℝ => 2 - 2 * t)) (x, 1) =
      ((stdSimplexBoundary 2 ×ˢ Icc (0 : ℝ) (1 / 2)).piecewise
        (ρ ∘ Prod.map β fun t : ℝ => 4 * t - 1) (h ∘ Prod.map γ fun t : ℝ => 2 - 2 * t))
        (Function.invFunOn u (stdSimplexBoundary 2) x, 0) := by
    intro x hx
    have h' := hΦu (Function.invFunOn u (stdSimplexBoundary 2) x) (hv.bijOn.mapsTo hx)
    rw [hu.bijOn.invOn_invFunOn.2 hx] at h'
    exact h'.symm
  have hposv := isPLCirclePositive_of_isOrientable_cylindricalDiagram L
    hL.isCombinatorialManifoldWithBoundary hLo hJm hcyl subset_rfl hv hΦv
  have hposu : IsPLCirclePositive (stdSimplexBoundary 2) u :=
    hposv.of_leftInverse hv.bijOn hu.bijOn.mapsTo fun x hx => hu.bijOn.invOn_invFunOn.2 hx
  have hiso := isPLPseudoIsotopicToId_of_isPLCirclePositive hJm hu hposu
  obtain ⟨Φ', hΦ', hends⟩ :=
    hcyl.exists_endMap_id_of_pseudoIsotopicToId hu hΦu hiso hJmpoly.isPLHomeomorphOn_id
  obtain ⟨e, -⟩ := hΦ'.exists_homeomorph_prod_circle_of_eq_ends hJmpoly.isCompact hends
  obtain ⟨c⟩ := nonempty_homeomorph_loopCircle_of_isPLSphere_one hJm
  let eCirc : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
    (Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
      change z ∈ Metric.sphere (0 : ℂ) 1 ↔
        Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
      rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
        Complex.orthonormalBasisOneI.repr.norm_map]).symm
  let eS : loopCircle ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    (AddCircle.homeomorphCircle one_ne_zero).trans eCirc.symm
  exact ⟨e.trans ((c.symm.trans eS).prodCongr eS)⟩

omit [FiniteDimensional ℝ E] in
open Classical in
theorem isPreconnected_insert_biUnion_convexHull_edgeGraphFace
    (K : Geometry.SimplicialComplex ℝ E) {x y : K.vertices}
    (q : (SimplicialComplex.edgeGraph K).Walk x y) :
    IsPreconnected (insert (x : E)
      (⋃ e ∈ q.edges, convexHull ℝ (edgeGraphFace K e : Set E))) := by
  induction q with
  | nil => simpa using isPreconnected_singleton
  | @cons u v w h q ih =>
    have hu : (u : E) ∈ convexHull ℝ (edgeGraphFace K s(u, v) : Set E) :=
      subset_convexHull ℝ _ (by simp [edgeGraphFace])
    have hv : (v : E) ∈ convexHull ℝ (edgeGraphFace K s(u, v) : Set E) :=
      subset_convexHull ℝ _ (by simp [edgeGraphFace])
    have heq : insert (u : E)
        (⋃ e ∈ (SimpleGraph.Walk.cons h q).edges, convexHull ℝ (edgeGraphFace K e : Set E)) =
        convexHull ℝ (edgeGraphFace K s(u, v) : Set E) ∪
          insert (v : E) (⋃ e ∈ q.edges, convexHull ℝ (edgeGraphFace K e : Set E)) := by
      ext z
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons, mem_insert_iff, mem_union,
        mem_iUnion, exists_prop]
      constructor
      · rintro (rfl | ⟨e, rfl | he, hz⟩)
        · exact Or.inl hu
        · exact Or.inl hz
        · exact Or.inr (Or.inr ⟨e, he, hz⟩)
      · rintro (hz | rfl | ⟨e, he, hz⟩)
        · exact Or.inr ⟨_, Or.inl rfl, hz⟩
        · exact Or.inr ⟨_, Or.inl rfl, hv⟩
        · exact Or.inr ⟨e, Or.inr he, hz⟩
    rw [heq]
    exact (convex_convexHull ℝ _).isPreconnected.union (v : E) hv (mem_insert _ _) ih

open Classical in
theorem IsCombinatorialManifold.exists_isPLSphere_one_isPreconnected_sdiff
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space) (hχ : eulerChar K ≠ 2) :
    ∃ J : Set E, IsPLSphere 1 J ∧ J ⊆ K.space ∧ IsPreconnected (K.space \ J) := by
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  have hFFinite : Set.Finite {s : Finset E | s ∈ K.faces ∧ s.card = 3} :=
    (Set.toFinite K.faces).subset fun _ h => h.1
  let _ : Finite {s : Finset E // s ∈ K.faces ∧ s.card = 3} := hFFinite.to_subtype
  obtain ⟨T, hT, hTree⟩ := exists_edgeGraph_spanningTree K hconn
  have hD := dualCotreeGraph_connected K hK hconn hT hTree
  obtain ⟨Ts, hTs, hTsTree⟩ := hD.exists_isTree_le
  obtain ⟨s, t, hst, hnst⟩ : ∃ s t, (dualCotreeGraph K T).Adj s t ∧ ¬ Ts.Adj s t := by
    by_contra hne
    simp only [not_exists, not_and, not_not] at hne
    have hle : dualCotreeGraph K T ≤ Ts := fun a b h => hne a b h
    have hcard := Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hle)
    have htreeCard : T.edgeSet.ncard + 1 = K.vertices.ncard := by
      simpa using (SimpleGraph.isTree_iff_connected_and_card.mp hTree).2
    have hTsCard : Ts.edgeSet.ncard + 1 =
        Nat.card {s : Finset E // s ∈ K.faces ∧ s.card = 3} := by
      simpa using (SimpleGraph.isTree_iff_connected_and_card.mp hTsTree).2
    have htreeEdgeLe : T.edgeSet.ncard ≤
        (SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2).card := by
      rw [← ncard_edgeSet_edgeGraph_eq_facesOfCard_two K]
      exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hT)
    rw [ncard_edgeSet_dualCotreeGraph K hK hT] at hcard
    rw [natCard_topFaces_eq_facesOfCard_three K] at hTsCard
    rw [ncard_vertices_eq_facesOfCard_one K] at htreeCard
    have hle2 := hK.faceEulerChar_le_two K hconn
    have hEuler := SimplicialComplex.faceEulerChar_eq_of_card_le_three
      K.toPreAbstractSimplicialComplex (fun s hs => by simpa using hK.card_le K hs)
    apply hχ
    change SimplicialComplex.faceEulerChar K.toPreAbstractSimplicialComplex = 2
    rw [hEuler] at hle2 ⊢
    omega
  have hface := dualGraph_sharedFace_mem_facesOfCard_two K hst.1
  rw [SimplicialComplex.mem_facesOfCard] at hface
  obtain ⟨a, b, hab, habeq⟩ := Finset.card_eq_two.mp hface.2
  have haK : ({a} : Finset E) ∈ K.faces :=
    K.down_closed hface.1 (by rw [habeq]; simp) (Finset.singleton_nonempty a)
  have hbK : ({b} : Finset E) ∈ K.faces :=
    K.down_closed hface.1 (by rw [habeq]; simp) (Finset.singleton_nonempty b)
  let u : K.vertices := ⟨a, haK⟩
  let w : K.vertices := ⟨b, hbK⟩
  have hfu : edgeGraphFace K s(u, w) = s.1 ∩ t.1 := by
    rw [habeq]
    simp only [edgeGraphFace, Sym2.map_mk, Sym2.toFinset_mk_eq]
    rfl
  have hadj : (SimplicialComplex.edgeGraph K).Adj u w :=
    ⟨fun h => hab (congrArg Subtype.val h), by
      change ({a, b} : Finset E) ∈ K.faces
      rw [← habeq]
      exact hface.1⟩
  have hnT : ¬ T.Adj u w := by
    intro h
    exact hst.2 (hfu ▸ ⟨s(u, w), T.mem_edgeSet.mpr h, rfl⟩)
  obtain ⟨q⟩ := hTree.connected.preconnected w u
  let c := SimpleGraph.Walk.cons hadj (q.bypass.mapLe hT)
  have hc : c.IsCycle := by
    refine (SimpleGraph.Walk.cons_isCycle_iff _ hadj).mpr ⟨q.bypass_isPath.mapLe hT, ?_⟩
    intro hmem
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hmem
    exact hnT (T.mem_edgeSet.mp (q.bypass.edges_subset_edgeSet hmem))
  have hcedges : ∀ e ∈ c.edges, e = s(u, w) ∨ e ∈ T.edgeSet := by
    intro e he
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons, SimpleGraph.Walk.edges_mapLe_eq_edges] at he
    exact he.imp_right fun he => q.bypass.edges_subset_edgeSet he
  let A : Set (Finset E) := {f | ∃ e ∈ c.edges, f = edgeGraphFace K e}
  let G := subcomplexGeneratedBy K A
  let _ : Finite G.faces := (subcomplexGeneratedBy_faces_finite K A).to_subtype
  have hAK : ∀ e ∈ c.edges, edgeGraphFace K e ∈ K.faces := fun e he =>
    ((SimplicialComplex.mem_facesOfCard _).mp
      (edgeGraphFace_mem_facesOfCard_two K (c.edges_subset_edgeSet he))).1
  have hA2 : ∀ f ∈ K.faces ∩ A, f.card = 2 := by
    rintro f ⟨-, e, he, rfl⟩
    exact ((SimplicialComplex.mem_facesOfCard _).mp
      (edgeGraphFace_mem_facesOfCard_two K (c.edges_subset_edgeSet he))).2
  have hGfaces : G.faces ⊆ K.faces := subcomplexGeneratedBy_faces_subset K A
  have hGcard : ∀ f ∈ G.faces, f.card ≤ 2 := by
    intro f hf
    obtain ⟨g, -, hfg, hg⟩ := exists_face_superset_card_eq_subcomplexGeneratedBy K A hA2 hf
    exact hg ▸ Finset.card_le_card hfg
  have hG2 {f : Finset E} (hf : f.card = 2) : f ∈ G.faces ↔ f ∈ K.faces ∩ A :=
    mem_subcomplexGeneratedBy_faces_of_card K A hA2 hf
  have hGedge : ∀ f ∈ G.faces, f.card = 2 → f = s.1 ∩ t.1 ∨ f ∈ spanningTreeFaces K T := by
    intro f hf hfc
    obtain ⟨-, e, he, rfl⟩ := (hG2 hfc).mp hf
    rcases hcedges e he with rfl | heT
    · exact Or.inl hfu
    · exact Or.inr ⟨e, heT, rfl⟩
  have hpair_mem {p₁ p₂ q₁ q₂ : E} (hp : p₁ ≠ p₂) (heq : ({p₁, p₂} : Finset E) = {q₁, q₂}) :
      (p₁ = q₁ ∧ p₂ = q₂) ∨ (p₁ = q₂ ∧ p₂ = q₁) := by
    have h1 : p₁ ∈ ({q₁, q₂} : Finset E) := heq ▸ by simp
    have h2 : p₂ ∈ ({q₁, q₂} : Finset E) := heq ▸ by simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with rfl | rfl
    · exact Or.inl ⟨rfl, h2.resolve_left hp.symm⟩
    · exact Or.inr ⟨rfl, h2.resolve_right hp.symm⟩
  have hG1 : IsCombinatorialManifold 1 G := by
    refine (isCombinatorialManifold_one_iff G).mpr ⟨hGcard, fun v hv => ?_⟩
    obtain ⟨f, ⟨-, e, he, rfl⟩, hvf, -⟩ := hv
    have hvmem : v ∈ edgeGraphFace K e := hvf (Finset.mem_singleton_self v)
    obtain ⟨v', hv'e, rfl⟩ : ∃ v' : K.vertices, v' ∈ e ∧ (v' : E) = v := by
      induction e using Sym2.ind with
      | _ y z =>
        simp only [edgeGraphFace, Sym2.map_mk, Sym2.toFinset_mk_eq, Finset.mem_insert,
          Finset.mem_singleton] at hvmem
        rcases hvmem with rfl | rfl
        · exact ⟨y, Sym2.mem_mk_left y z, rfl⟩
        · exact ⟨z, Sym2.mem_mk_right y z, rfl⟩
    have hv'supp : v' ∈ c.support := by
      induction e using Sym2.ind with
      | _ y z =>
        rcases Sym2.mem_iff.mp hv'e with rfl | rfl
        · exact c.fst_mem_support_of_mem_edges he
        · exact c.snd_mem_support_of_mem_edges he
    have hN : {x : E | x ≠ (v' : E) ∧ {(v' : E), x} ∈ G.faces} =
        Subtype.val '' (c.toSubgraph.neighborSet v') := by
      ext x
      constructor
      · rintro ⟨hxv, hx⟩
        have hxc : ({(v' : E), x} : Finset E).card = 2 := Finset.card_pair hxv.symm
        obtain ⟨-, e', he', hxe'⟩ := (hG2 hxc).mp hx
        induction e' using Sym2.ind with
        | _ y z =>
          simp only [edgeGraphFace, Sym2.map_mk, Sym2.toFinset_mk_eq] at hxe'
          rcases hpair_mem hxv.symm hxe' with ⟨hy, hz⟩ | ⟨hz, hy⟩
          · have hyv : y = v' := Subtype.ext hy.symm
            subst hyv
            exact ⟨z, SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr he', hz.symm⟩
          · have hzv : z = v' := Subtype.ext hz.symm
            subst hzv
            have hadj' : c.toSubgraph.Adj z y :=
              SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mpr (by rwa [Sym2.eq_swap])
            exact ⟨y, hadj', hy.symm⟩
      · rintro ⟨z, hz, rfl⟩
        have hzadj : c.toSubgraph.Adj v' z := hz
        have hKadj := hzadj.adj_sub
        refine ⟨fun h => hKadj.1 (Subtype.ext h).symm, ?_⟩
        rw [hG2 (Finset.card_pair fun h => hKadj.1 (Subtype.ext h))]
        refine ⟨hKadj.2, s(v', z), SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges.mp hzadj, ?_⟩
        simp only [edgeGraphFace, Sym2.map_mk, Sym2.toFinset_mk_eq]
    have hNcard : (Subtype.val '' (c.toSubgraph.neighborSet v')).ncard = 2 := by
      rw [Set.ncard_image_of_injective _ Subtype.val_injective]
      exact hc.ncard_neighborSet_toSubgraph_eq_two hv'supp
    rw [hN]
    exact Set.ncard_eq_two.mp hNcard
  have hGspace : G.space =
      insert (u : E) (⋃ e ∈ c.edges, convexHull ℝ (edgeGraphFace K e : Set E)) := by
    rw [subcomplexGeneratedBy_space]
    ext z
    simp only [mem_iUnion, mem_insert_iff, exists_prop, mem_inter_iff]
    constructor
    · rintro ⟨f, ⟨-, e, he, rfl⟩, hz⟩
      exact Or.inr ⟨e, he, hz⟩
    · rintro (hz | ⟨e, he, hz⟩)
      · have hfirst : s(u, w) ∈ c.edges := by simp [c]
        refine ⟨_, ⟨hAK _ hfirst, s(u, w), hfirst, rfl⟩, subset_convexHull ℝ _ ?_⟩
        simp only [edgeGraphFace, Sym2.map_mk, Sym2.toFinset_mk_eq, Finset.coe_insert,
          Finset.coe_singleton, mem_insert_iff, mem_singleton_iff]
        exact Or.inl hz
      · exact ⟨_, ⟨hAK e he, e, he, rfl⟩, hz⟩
  have hGconn : IsConnected G.space := by
    rw [hGspace]
    exact ⟨insert_nonempty _ _, isPreconnected_insert_biUnion_convexHull_edgeGraphFace K c⟩
  have hGsph : IsPLSphere 1 G.space :=
    isPLSphere_one_of_edgeGraph_connected G hG1 (edgeGraph_connected_of_isConnected_space G hGconn)
  refine ⟨G.space, hGsph, space_mono_of_faces_subset hGfaces, ?_⟩
  set F := K.space \ G.space with hFdef
  have hopenF : ∀ σ ∈ K.faces, σ ∉ G.faces → openSimplex σ ⊆ F := fun σ hσ hσG x hx =>
    ⟨K.convexHull_subset_space hσ (openSimplex_subset_convexHull σ hx),
      notMem_space_of_notMem_faces hGfaces hσ hσG hx⟩
  have htriG : ∀ r : {s : Finset E // s ∈ K.faces ∧ s.card = 3}, r.1 ∉ G.faces := by
    intro r hr
    have := hGcard _ hr
    have := r.2.2
    omega
  have hclosure {σ τ : Finset E} (hτ : τ.Nonempty) (hστ : σ ⊆ τ) {x : E}
      (hx : x ∈ openSimplex σ) : x ∈ closure (openSimplex τ) :=
    convexHull_subset_closure_openSimplex hτ
      (convexHull_mono (Finset.coe_subset.mpr hστ) (openSimplex_subset_convexHull σ hx))
  have hjoin {τ : Finset E} (x : E) (hx : x ∈ closure (openSimplex τ)) :
      IsPreconnected (openSimplex τ ∪ {x}) :=
    (convex_openSimplex τ).isPreconnected.subset_closure subset_union_left
      (union_subset subset_closure (singleton_subset_iff.mpr hx))
  obtain ⟨x₁, hx₁⟩ := hconn.nonempty
  obtain ⟨σ₁, hσ₁, -⟩ := exists_face_mem_openSimplex K hx₁
  obtain ⟨τ₁, hτ₁, -, hτ₁card⟩ :=
    hK.isCombinatorialManifoldWithBoundary.exists_face_superset_card_eq hσ₁
  obtain ⟨r₀, -⟩ : ∃ r₀ : {s : Finset E // s ∈ K.faces ∧ s.card = 3}, r₀.1 = τ₁ :=
    ⟨⟨τ₁, hτ₁, hτ₁card⟩, rfl⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ ∈ openSimplex r₀.1 :=
    ⟨_, centroid_mem_openSimplex (K.nonempty_of_mem_faces r₀.2.1)⟩
  have htri : ∀ r : {s : Finset E // s ∈ K.faces ∧ s.card = 3},
      openSimplex r.1 ⊆ connectedComponentIn F x₀ := by
    intro r
    obtain ⟨p⟩ := hTsTree.connected.preconnected r r₀
    induction p with
    | @nil v =>
      exact (convex_openSimplex _).isPreconnected.subset_connectedComponentIn hx₀
        (hopenF _ v.2.1 (htriG v))
    | @cons r r' _ hrr' p ih =>
      obtain ⟨hdual, hnotT⟩ := hTs hrr'
      have hf := dualGraph_sharedFace_mem_facesOfCard_two K hdual
      rw [SimplicialComplex.mem_facesOfCard] at hf
      have hfG : r.1 ∩ r'.1 ∉ G.faces := by
        intro hfG
        rcases hGedge _ hfG hf.2 with hfe | hfT
        · apply hnst
          have hshared : dualGraphSharedFace K s(r, r') = dualGraphSharedFace K s(s, t) := by
            simpa [dualGraphSharedFace] using hfe
          have heq := dualGraphSharedFace_injOn_edgeSet K hK
            ((dualGraph 2 K).mem_edgeSet.mpr hdual) ((dualGraph 2 K).mem_edgeSet.mpr hst.1)
            hshared
          rw [← Ts.mem_edgeSet, ← heq, Ts.mem_edgeSet]
          exact hrr'
        · exact hnotT hfT
      have hfne : (r.1 ∩ r'.1).Nonempty := K.nonempty_of_mem_faces hf.1
      set z := (r.1 ∩ r'.1).centroid ℝ id
      have hz : z ∈ openSimplex (r.1 ∩ r'.1) := centroid_mem_openSimplex hfne
      have hzF : z ∈ F := hopenF _ hf.1 hfG hz
      have hS₁ := hjoin z (hclosure (K.nonempty_of_mem_faces r.2.1) Finset.inter_subset_left hz)
      have hS₂ := hjoin z (hclosure (K.nonempty_of_mem_faces r'.2.1) Finset.inter_subset_right hz)
      have hS := hS₁.union z (Or.inr rfl) (Or.inr rfl) hS₂
      have hSF : (openSimplex r.1 ∪ {z}) ∪ (openSimplex r'.1 ∪ {z}) ⊆ F :=
        union_subset (union_subset (hopenF _ r.2.1 (htriG r)) (singleton_subset_iff.mpr hzF))
          (union_subset (hopenF _ r'.2.1 (htriG r')) (singleton_subset_iff.mpr hzF))
      have hy' := centroid_mem_openSimplex (K.nonempty_of_mem_faces r'.2.1)
      have hsub := hS.subset_connectedComponentIn (Or.inr (Or.inl hy')) hSF
      rw [← connectedComponentIn_eq (ih hx₀ hy')] at hsub
      exact fun x hx => hsub (Or.inl (Or.inl hx))
  have hall : F ⊆ connectedComponentIn F x₀ := by
    intro y hy
    obtain ⟨σ, hσ, hyσ⟩ := exists_face_mem_openSimplex K hy.1
    have hσG : σ ∉ G.faces := fun h =>
      hy.2 (G.convexHull_subset_space h (openSimplex_subset_convexHull σ hyσ))
    obtain ⟨τ, hτ, hστ, hτcard⟩ :=
      hK.isCombinatorialManifoldWithBoundary.exists_face_superset_card_eq hσ
    let r : {s : Finset E // s ∈ K.faces ∧ s.card = 3} := ⟨τ, hτ, hτcard⟩
    have hS := hjoin y (hclosure (K.nonempty_of_mem_faces hτ) hστ hyσ)
    have hSF : openSimplex τ ∪ {y} ⊆ F :=
      union_subset (hopenF τ hτ (htriG r)) (singleton_subset_iff.mpr hy)
    have hy' := centroid_mem_openSimplex (K.nonempty_of_mem_faces hτ)
    have hsub := hS.subset_connectedComponentIn (Or.inl hy') hSF
    rw [← connectedComponentIn_eq (htri r hy')] at hsub
    exact hsub (Or.inr rfl)
  rw [← Subset.antisymm (connectedComponentIn_subset F x₀) hall]
  exact isPreconnected_connectedComponentIn

end Annulus

theorem IsCombinatorialManifold.nonempty_homeomorph_torus_of_isOrientable_of_eulerChar_eq_zero
    (L : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))) [Finite L.faces]
    (hL : IsCombinatorialManifold 2 L) (hLc : IsConnected L.space)
    (hLo : IsOrientable 2 L) (hχ : eulerChar L = 0) :
    Nonempty (L.space ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) := by
  obtain ⟨J, hJ, hJL, hnonsep⟩ :=
    hL.exists_isPLSphere_one_isPreconnected_sdiff L hLc (by rw [hχ]; norm_num)
  exact hL.nonempty_homeomorph_torus_of_isPreconnected_sdiff L hLo hχ hJ hJL hnonsep

end DifferentialGeometry.Topology.PiecewiseLinear
