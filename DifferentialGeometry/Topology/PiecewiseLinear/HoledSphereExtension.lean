/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.HoledDiskBoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.BallFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.BallReplacement

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

section Positivity

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem IsPLCirclePositive.of_eqOn {S : Set E} {u v : E → E}
    (hu : IsPLCirclePositive S u) (hvu : EqOn v u S) : IsPLCirclePositive S v := by
  obtain ⟨c, hc, hcb, hcu⟩ := hu
  refine ⟨c, hc, hcb, hcu.congr fun t => ?_⟩
  change Function.invFunOn c univ (v (c t)) = Function.invFunOn c univ (u (c t))
  rw [hvu (hcb.mapsTo (mem_univ t))]

theorem IsPLCirclePositive.conj {S : Set E} {S' : Set F} {u : E → E} {h : E → F}
    (hu : IsPLCirclePositive S u) (hmu : MapsTo u S S) (hh : ContinuousOn h S)
    (hbij : BijOn h S S') :
    IsPLCirclePositive S' (h ∘ u ∘ Function.invFunOn h S) := by
  obtain ⟨g, hgc, hgb, hlift⟩ := hu
  have hg' : BijOn (h ∘ g) univ S' := hbij.comp hgb
  have hmap : MapsTo (h ∘ u ∘ Function.invFunOn h S) S' S' := fun y hy =>
    hbij.mapsTo (hmu (hbij.surjOn.mapsTo_invFunOn hy))
  refine ⟨h ∘ g, hh.comp_continuous hgc fun θ => hgb.mapsTo (mem_univ θ), hg', ?_⟩
  refine hlift.congr fun θ => ?_
  apply hg'.injOn (mem_univ _) (mem_univ _)
  rw [circleConj_spec hg' hmap θ]
  change h (u (Function.invFunOn h S (h (g θ)))) = h (g (circleConj g u θ))
  rw [circleConj_spec hgb hmu θ, hbij.invOn_invFunOn.1 (hgb.mapsTo (mem_univ θ))]

end Positivity

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem IsPLSphere.exists_holed_chart {ι : Type*} {S : Set E} (hS : IsPLSphere 2 S)
    {D : ι → Set E} {q : ι → (Fin 3 → ℝ) → E}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i)) (hDS : ∀ i, D i ⊆ S)
    (hdis : Pairwise fun i j => Disjoint (D i) (D j)) (i₀ : ι) :
    ∃ (χ : E → Plane) (Δ : Set Plane), IsPLBall 2 Δ ∧
      IsPLHomeomorphOn χ (S \ (D i₀ \ q i₀ '' stdSimplexBoundary 2)) Δ ∧
      χ '' (q i₀ '' stdSimplexBoundary 2) = frontier Δ ∧
      ∀ i, i ≠ i₀ → D i ⊆ S \ (D i₀ \ q i₀ '' stdSimplexBoundary 2) ∧
        χ '' D i ⊆ interior Δ ∧ IsPLHomeomorphOn χ (D i) (χ '' D i) ∧
        χ '' (q i '' stdSimplexBoundary 2) = frontier (χ '' D i) := by
  classical
  have hD₀ : IsPLBall 2 (D i₀) := ⟨q i₀, hq i₀⟩
  have hcl := hS.closure_sdiff_eq_sdiff_image_stdSimplexBoundary (hq i₀) (hDS i₀)
  obtain ⟨u, hu⟩ := hS.isPLBall_closure_sdiff hD₀ (hDS i₀)
  have hJ := hS.image_stdSimplexBoundary_complement hD₀ (hDS i₀) hu
  have hJ₀ := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary (hq i₀) (hDS i₀)
  have hubd : u '' stdSimplexBoundary 2 = q i₀ '' stdSimplexBoundary 2 := by
    rw [hJ, inter_comm, hJ₀]
  rw [hcl] at hu
  obtain ⟨T, hT, hcard, -, -, -⟩ := exists_affineIndependent_openSimplex_subset
    (by simp : Module.finrank ℝ Plane = 1 + 1) (0 : Plane)
    (Filter.univ_mem : univ ∈ nhds (0 : Plane))
  obtain ⟨v, hv⟩ : IsPLBall 2 (convexHull ℝ (T : Set Plane)) :=
    isPLBall_convexHull_of_affineIndependent T hT hcard
  set C := S \ (D i₀ \ q i₀ '' stdSimplexBoundary 2) with hCdef
  set Δ := convexHull ℝ (T : Set Plane) with hΔdef
  have hχ : IsPLHomeomorphOn (v ∘ Function.invFunOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))) C Δ :=
    hu.symm.trans hv
  have hbd : stdSimplexBoundary 2 ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := fun x hx => hx.1
  have hfront : (v ∘ Function.invFunOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))) ''
      (q i₀ '' stdSimplexBoundary 2) = frontier Δ := by
    rw [← hubd, image_comp, hu.bijOn.injOn.invFunOn_image hbd]
    exact hv.image_stdSimplexBoundary_eq_frontier (n := 1)
  have hc₀C : q i₀ '' stdSimplexBoundary 2 ⊆ C := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨hDS i₀ ((hq i₀).bijOn.mapsTo hy.1), fun h => h.2 ⟨y, hy, rfl⟩⟩
  refine ⟨v ∘ Function.invFunOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)), Δ, ⟨v, hv⟩, hχ, hfront, ?_⟩
  intro i hi
  have hDiC : D i ⊆ C := fun x hx =>
    ⟨hDS i hx, fun h => disjoint_left.mp (hdis hi) hx h.1⟩
  have hχi := hχ.restrict (IsPLBall.isPolyhedron ⟨q i, hq i⟩) hDiC
  refine ⟨hDiC, ?_, hχi, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hmem : (v ∘ Function.invFunOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))) x ∈ Δ :=
      hχ.bijOn.mapsTo (hDiC hx)
    by_contra hint
    have hfr : (v ∘ Function.invFunOn u (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))) x ∈ frontier Δ :=
      ⟨subset_closure hmem, hint⟩
    rw [← hfront] at hfr
    obtain ⟨y, hy, hyx⟩ := hfr
    have hyx' := hχ.bijOn.injOn (hc₀C hy) (hDiC hx) hyx
    obtain ⟨z, hz, rfl⟩ := hy
    exact disjoint_left.mp (hdis hi) hx (hyx' ▸ (hq i₀).bijOn.mapsTo hz.1)
  · have h := ((hq i).trans hχi).image_stdSimplexBoundary_eq_frontier (n := 1)
    rwa [image_comp] at h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
theorem image_sdiff_iUnion_sdiff_eq {ι : Type*} {S C : Set E} {Δ : Set Plane} {χ : E → Plane}
    {D c : ι → Set E} (i₀ : ι) (hχ : BijOn χ C Δ) (hC : C = S \ (D i₀ \ c i₀))
    (hDC : ∀ i, i ≠ i₀ → D i ⊆ C) (hcD : ∀ i, c i ⊆ D i)
    (hint : ∀ i, i ≠ i₀ → interior (χ '' D i) = χ '' D i \ χ '' c i) :
    χ '' (S \ ⋃ i, (D i \ c i)) = Δ \ ⋃ k : {i // i ≠ i₀}, interior (χ '' D k) ∧
      S \ ⋃ i, (D i \ c i) ⊆ C := by
  have hsub : S \ ⋃ i, (D i \ c i) ⊆ C := by
    rintro x ⟨hxS, hx⟩
    rw [hC]
    exact ⟨hxS, fun h => hx (mem_iUnion.mpr ⟨i₀, h⟩)⟩
  refine ⟨Subset.antisymm ?_ ?_, hsub⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨hχ.mapsTo (hsub hx), ?_⟩
    simp only [mem_iUnion, not_exists]
    intro k hk
    rw [hint k.1 k.2] at hk
    obtain ⟨⟨y, hy, hyx⟩, hnc⟩ := hk
    have hxy : y = x := hχ.injOn (hDC k.1 k.2 hy) (hsub hx) hyx
    subst hxy
    exact hx.2 (mem_iUnion.mpr ⟨k.1, hy, fun hyc => hnc ⟨y, hyc, rfl⟩⟩)
  · rintro z ⟨hzΔ, hz⟩
    obtain ⟨x, hxC, rfl⟩ := hχ.surjOn hzΔ
    have hxC' : x ∈ S \ (D i₀ \ c i₀) := hC ▸ hxC
    refine ⟨x, ⟨hxC'.1, ?_⟩, rfl⟩
    simp only [mem_iUnion, not_exists]
    intro i hi
    by_cases hii : i = i₀
    · subst hii
      exact hxC'.2 hi
    · refine hz (mem_iUnion.mpr ⟨⟨i, hii⟩, ?_⟩)
      rw [hint i hii]
      refine ⟨⟨x, hi.1, rfl⟩, fun ⟨y, hy, hyx⟩ => hi.2 ?_⟩
      have hyx' := hχ.injOn (hDC i hii (hcD i hy)) hxC hyx
      exact hyx' ▸ hy

theorem IsPLSphere.exists_isPLHomeomorphOn_holed {ι : Type*} [Finite ι]
    {S : Set E} {S' : Set F} (hS : IsPLSphere 2 S) (hS' : IsPLSphere 2 S')
    {D : ι → Set E} {D' : ι → Set F} {q : ι → (Fin 3 → ℝ) → E} {q' : ι → (Fin 3 → ℝ) → F}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hq' : ∀ i, IsPLHomeomorphOn (q' i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D' i))
    (hDS : ∀ i, D i ⊆ S) (hD'S' : ∀ i, D' i ⊆ S')
    (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    (hdis' : Pairwise fun i j => Disjoint (D' i) (D' j)) (i₀ : ι) {φ : E → F}
    (hφ : IsPLHomeomorphOn φ (q i₀ '' stdSimplexBoundary 2) (q' i₀ '' stdSimplexBoundary 2)) :
    ∃ G₀ : E → F,
      IsPLHomeomorphOn G₀ (S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2))
        (S' \ ⋃ i, (D' i \ q' i '' stdSimplexBoundary 2)) ∧
      EqOn G₀ φ (q i₀ '' stdSimplexBoundary 2) ∧
      (∀ i, G₀ '' (q i '' stdSimplexBoundary 2) = q' i '' stdSimplexBoundary 2) ∧
      ∀ ψ : ι → E → F,
        (∀ i, i ≠ i₀ → IsPLHomeomorphOn (ψ i) (q i '' stdSimplexBoundary 2)
          (q' i '' stdSimplexBoundary 2)) →
        (∀ i, i ≠ i₀ → IsPLCirclePositive (q' i '' stdSimplexBoundary 2)
          (ψ i ∘ Function.invFunOn G₀ (q i '' stdSimplexBoundary 2))) →
        ∃ G : E → F,
          IsPLHomeomorphOn G (S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2))
            (S' \ ⋃ i, (D' i \ q' i '' stdSimplexBoundary 2)) ∧
          EqOn G φ (q i₀ '' stdSimplexBoundary 2) ∧
          ∀ i, i ≠ i₀ → EqOn G (ψ i) (q i '' stdSimplexBoundary 2) := by
  classical
  obtain ⟨χ, Δ, hΔ, hχ, hχ0, hχi⟩ := hS.exists_holed_chart hq hDS hdis i₀
  obtain ⟨χ', Δ', hΔ', hχ', hχ'0, hχ'i⟩ := hS'.exists_holed_chart hq' hD'S' hdis' i₀
  have hcD : ∀ i, q i '' stdSimplexBoundary 2 ⊆ D i := fun i => by
    rintro _ ⟨y, hy, rfl⟩
    exact (hq i).bijOn.mapsTo hy.1
  have hc'D' : ∀ i, q' i '' stdSimplexBoundary 2 ⊆ D' i := fun i => by
    rintro _ ⟨y, hy, rfl⟩
    exact (hq' i).bijOn.mapsTo hy.1
  have hcS : ∀ i, q i '' stdSimplexBoundary 2 ⊆ S \ (D i₀ \ q i₀ '' stdSimplexBoundary 2) := by
    intro i x hx
    by_cases hi : i = i₀
    · subst hi
      exact ⟨hDS i (hcD i hx), fun h => h.2 hx⟩
    · exact (hχi i hi).1 (hcD i hx)
  have hc'S' : ∀ i, q' i '' stdSimplexBoundary 2 ⊆
      S' \ (D' i₀ \ q' i₀ '' stdSimplexBoundary 2) := by
    intro i x hx
    by_cases hi : i = i₀
    · subst hi
      exact ⟨hD'S' i (hc'D' i hx), fun h => h.2 hx⟩
    · exact (hχ'i i hi).1 (hc'D' i hx)
  have hcpoly : ∀ i, IsPolyhedron (q i '' stdSimplexBoundary 2) := fun i =>
    ((hq i).isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron
  have hc'poly : ∀ i, IsPolyhedron (q' i '' stdSimplexBoundary 2) := fun i =>
    ((hq' i).isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron
  have hintA : ∀ i, i ≠ i₀ → interior (χ '' D i) =
      χ '' D i \ χ '' (q i '' stdSimplexBoundary 2) := by
    intro i hi
    have hcl : IsClosed (χ '' D i) :=
      (IsPLBall.of_isPLHomeomorphOn ⟨q i, hq i⟩ (hχi i hi).2.2.1).isPolyhedron.isClosed
    rw [(hχi i hi).2.2.2, hcl.frontier_eq, sdiff_sdiff_right_self,
      inter_eq_right.mpr interior_subset]
  have hintB : ∀ i, i ≠ i₀ → interior (χ' '' D' i) =
      χ' '' D' i \ χ' '' (q' i '' stdSimplexBoundary 2) := by
    intro i hi
    have hcl : IsClosed (χ' '' D' i) :=
      (IsPLBall.of_isPLHomeomorphOn ⟨q' i, hq' i⟩ (hχ'i i hi).2.2.1).isPolyhedron.isClosed
    rw [(hχ'i i hi).2.2.2, hcl.frontier_eq, sdiff_sdiff_right_self,
      inter_eq_right.mpr interior_subset]
  obtain ⟨hPeq, hPC⟩ := image_sdiff_iUnion_sdiff_eq (S := S) i₀ hχ.bijOn rfl
    (fun i hi => (hχi i hi).1) hcD hintA
  obtain ⟨hP'eq, hP'C'⟩ := image_sdiff_iUnion_sdiff_eq (S := S') i₀ hχ'.bijOn rfl
    (fun i hi => (hχ'i i hi).1) hc'D' hintB
  let A : {i // i ≠ i₀} → Set Plane := fun k => χ '' D k.1
  let B : {i // i ≠ i₀} → Set Plane := fun k => χ' '' D' k.1
  have hA : ∀ k, IsPLBall 2 (A k) := fun k =>
    IsPLBall.of_isPLHomeomorphOn ⟨q k.1, hq k.1⟩ (hχi k.1 k.2).2.2.1
  have hB : ∀ k, IsPLBall 2 (B k) := fun k =>
    IsPLBall.of_isPLHomeomorphOn ⟨q' k.1, hq' k.1⟩ (hχ'i k.1 k.2).2.2.1
  have hAdis : Pairwise fun k l => Disjoint (A k) (A l) := by
    intro k l hkl
    exact (hdis fun h => hkl (Subtype.ext h)).image hχ.bijOn.injOn (hχi k.1 k.2).1
      (hχi l.1 l.2).1
  have hBdis : Pairwise fun k l => Disjoint (B k) (B l) := by
    intro k l hkl
    exact (hdis' fun h => hkl (Subtype.ext h)).image hχ'.bijOn.injOn (hχ'i k.1 k.2).1
      (hχ'i l.1 l.2).1
  have hPc : IsPolyhedron (Δ \ ⋃ k, interior (A k)) :=
    hΔ.isPolyhedron.sdiff_iUnion_interior_of_isPLBall (n := 1) hA
  have hPc' : IsPolyhedron (Δ' \ ⋃ k, interior (B k)) :=
    hΔ'.isPolyhedron.sdiff_iUnion_interior_of_isPLBall (n := 1) hB
  have hχP : IsPLHomeomorphOn χ (S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2))
      (Δ \ ⋃ k, interior (A k)) := by
    have hinv := hχ.symm.restrict hPc sdiff_subset
    have hPpoly : IsPolyhedron (S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2)) := by
      have h := hPc.image_of_isPiecewiseAffineOn hinv.isPiecewiseAffineOn hinv.bijOn.injOn
      rwa [← hPeq, hχ.bijOn.injOn.invFunOn_image hPC] at h
    have h := hχ.restrict hPpoly hPC
    rwa [hPeq] at h
  have hχ'inv : IsPLHomeomorphOn (Function.invFunOn χ' (S' \ (D' i₀ \ q' i₀ ''
      stdSimplexBoundary 2))) (Δ' \ ⋃ k, interior (B k))
      (S' \ ⋃ i, (D' i \ q' i '' stdSimplexBoundary 2)) := by
    have hinv := hχ'.symm.restrict hPc' sdiff_subset
    have himg : Function.invFunOn χ' (S' \ (D' i₀ \ q' i₀ '' stdSimplexBoundary 2)) ''
        (Δ' \ ⋃ k, interior (B k)) = S' \ ⋃ i, (D' i \ q' i '' stdSimplexBoundary 2) := by
      rw [← hP'eq, hχ'.bijOn.injOn.invFunOn_image hP'C']
    rwa [himg] at hinv
  have hχc : ∀ i, IsPLHomeomorphOn χ (q i '' stdSimplexBoundary 2)
      (χ '' (q i '' stdSimplexBoundary 2)) := fun i => hχ.restrict (hcpoly i) (hcS i)
  have hχ'c : ∀ i, IsPLHomeomorphOn χ' (q' i '' stdSimplexBoundary 2)
      (χ' '' (q' i '' stdSimplexBoundary 2)) := fun i => hχ'.restrict (hc'poly i) (hc'S' i)
  have hφpl : IsPLHomeomorphOn
      (χ' ∘ (φ ∘ Function.invFunOn χ (q i₀ '' stdSimplexBoundary 2)))
      (frontier Δ) (frontier Δ') := by
    have h1 := hχc i₀
    have h2 := hχ'c i₀
    rw [hχ0] at h1
    rw [hχ'0] at h2
    exact (h1.symm.trans hφ).trans h2
  obtain ⟨f, hf, hfhol, hfφ, hfA⟩ := exists_isPLHomeomorphOn_holed_disk_eqOn_outer_boundary
    hΔ hΔ' hA hB (fun k => (hχi k.1 k.2).2.1) (fun k => (hχ'i k.1 k.2).2.1) hAdis hBdis hφpl
  have hback : ∀ i, ∀ y ∈ q' i '' stdSimplexBoundary 2,
      Function.invFunOn χ' (S' \ (D' i₀ \ q' i₀ '' stdSimplexBoundary 2)) (χ' y) = y :=
    fun i y hy => hχ'.bijOn.invOn_invFunOn.1 (hc'S' i hy)
  have hG₀φ : EqOn (Function.invFunOn χ' (S' \ (D' i₀ \ q' i₀ '' stdSimplexBoundary 2)) ∘
      f ∘ χ) φ (q i₀ '' stdSimplexBoundary 2) := by
    intro y hy
    have hχy : χ y ∈ frontier Δ := hχ0 ▸ mem_image_of_mem χ hy
    change Function.invFunOn χ' _ (f (χ y)) = φ y
    rw [hfφ hχy]
    change Function.invFunOn χ' _ (χ' (φ (Function.invFunOn χ _ (χ y)))) = φ y
    rw [(hχc i₀).bijOn.invOn_invFunOn.1 hy]
    exact hback i₀ (φ y) (hφ.bijOn.mapsTo hy)
  have hG₀c : ∀ i, i ≠ i₀ →
      (Function.invFunOn χ' (S' \ (D' i₀ \ q' i₀ '' stdSimplexBoundary 2)) ∘ f ∘ χ) ''
        (q i '' stdSimplexBoundary 2) = q' i '' stdSimplexBoundary 2 := by
    intro i hi
    rw [image_comp, image_comp, (hχi i hi).2.2.2]
    have hfr := (hfA ⟨i, hi⟩).2
    change f '' frontier (χ '' D i) = frontier (χ' '' D' i) at hfr
    rw [hfr, ← (hχ'i i hi).2.2.2, hχ'.bijOn.injOn.invFunOn_image (hc'S' i)]
  refine ⟨Function.invFunOn χ' (S' \ (D' i₀ \ q' i₀ '' stdSimplexBoundary 2)) ∘ f ∘ χ,
    (hχP.trans hfhol).trans hχ'inv, hG₀φ, ?_, ?_⟩
  · intro i
    by_cases hi : i = i₀
    · subst hi
      rw [image_congr hG₀φ, hφ.image_eq]
    · exact hG₀c i hi
  · intro ψ hψ hpos
    set G₀ := Function.invFunOn χ' (S' \ (D' i₀ \ q' i₀ '' stdSimplexBoundary 2)) ∘ f ∘ χ
      with hG₀def
    have hG₀inj : InjOn G₀ (S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2)) :=
      ((hχP.trans hfhol).trans hχ'inv).bijOn.injOn
    have hcP : ∀ i, q i '' stdSimplexBoundary 2 ⊆
        S \ ⋃ i, (D i \ q i '' stdSimplexBoundary 2) := by
      intro i x hx
      refine ⟨hDS i (hcD i hx), ?_⟩
      simp only [mem_iUnion, not_exists]
      intro j hj
      by_cases hij : j = i
      · subst hij
        exact hj.2 hx
      · exact disjoint_left.mp (hdis hij) hj.1 (hcD i hx)
    have hψpl : ∀ k : {i // i ≠ i₀}, IsPLHomeomorphOn
        (χ' ∘ (ψ k.1 ∘ Function.invFunOn χ (q k.1 '' stdSimplexBoundary 2)))
        (frontier (A k)) (frontier (B k)) := by
      intro k
      have h1 := hχc k.1
      have h2 := hχ'c k.1
      rw [(hχi k.1 k.2).2.2.2] at h1
      rw [(hχ'i k.1 k.2).2.2.2] at h2
      exact (h1.symm.trans (hψ k.1 k.2)).trans h2
    have hcorr : ∀ k : {i // i ≠ i₀}, IsPLCirclePositive (frontier (B k))
        ((χ' ∘ (ψ k.1 ∘ Function.invFunOn χ (q k.1 '' stdSimplexBoundary 2))) ∘
          Function.invFunOn f Δ) := by
      intro k
      have hmaps : MapsTo (ψ k.1 ∘ Function.invFunOn G₀ (q k.1 '' stdSimplexBoundary 2))
          (q' k.1 '' stdSimplexBoundary 2) (q' k.1 '' stdSimplexBoundary 2) := by
        intro z hz
        have hsurj : SurjOn G₀ (q k.1 '' stdSimplexBoundary 2)
            (q' k.1 '' stdSimplexBoundary 2) := hG₀c k.1 k.2 ▸ surjOn_image G₀ _
        exact (hψ k.1 k.2).bijOn.mapsTo (hsurj.mapsTo_invFunOn hz)
      have h1 := (hpos k.1 k.2).conj hmaps
        (hχ'.isPiecewiseAffineOn.continuousOn.mono (hc'S' k.1)) (hχ'c k.1).bijOn
      rw [(hχ'i k.1 k.2).2.2.2] at h1
      refine h1.of_eqOn fun z hz => ?_
      have hz' : z ∈ f '' frontier (A k) := (hfA k).2.symm ▸ hz
      obtain ⟨w, hw, rfl⟩ := hz'
      have hwΔ : w ∈ Δ :=
        interior_subset ((hχi k.1 k.2).2.1 ((hA k).isPolyhedron.isClosed.frontier_subset hw))
      rw [show frontier (A k) = χ '' (q k.1 '' stdSimplexBoundary 2) from
        ((hχi k.1 k.2).2.2.2).symm] at hw
      obtain ⟨y, hy, rfl⟩ := hw
      have hfinv : Function.invFunOn f Δ (f (χ y)) = χ y :=
        hf.bijOn.invOn_invFunOn.1 hwΔ
      have hfχy : f (χ y) ∈ χ' '' (q' k.1 '' stdSimplexBoundary 2) := by
        rw [(hχ'i k.1 k.2).2.2.2]
        exact hz
      have hy'c : Function.invFunOn χ' (q' k.1 '' stdSimplexBoundary 2) (f (χ y)) ∈
          q' k.1 '' stdSimplexBoundary 2 := (hχ'c k.1).bijOn.surjOn.mapsTo_invFunOn hfχy
      have hχ'y' : χ' (Function.invFunOn χ' (q' k.1 '' stdSimplexBoundary 2) (f (χ y))) =
          f (χ y) := (hχ'c k.1).bijOn.surjOn.rightInvOn_invFunOn hfχy
      have hG₀y : G₀ y = Function.invFunOn χ' (q' k.1 '' stdSimplexBoundary 2) (f (χ y)) := by
        change Function.invFunOn χ' _ (f (χ y)) = _
        conv_lhs => rw [← hχ'y']
        exact hback k.1 _ hy'c
      have hGinv : Function.invFunOn G₀ (q k.1 '' stdSimplexBoundary 2)
          (Function.invFunOn χ' (q' k.1 '' stdSimplexBoundary 2) (f (χ y))) = y := by
        rw [← hG₀y]
        exact (hG₀inj.mono (hcP k.1)).leftInvOn_invFunOn hy
      change χ' (ψ k.1 (Function.invFunOn χ _ (Function.invFunOn f Δ (f (χ y))))) =
        χ' (ψ k.1 (Function.invFunOn G₀ _
          (Function.invFunOn χ' (q' k.1 '' stdSimplexBoundary 2) (f (χ y)))))
      rw [hfinv, (hχc k.1).bijOn.invOn_invFunOn.1 hy, hGinv]
    obtain ⟨g, hg, hgf, hgψ⟩ := hf.exists_holed_disk_extension_of_positive_boundary_corrections
      hΔ hΔ' hA hB (fun k => (hχi k.1 k.2).2.1.trans interior_subset)
      (fun k => (hχ'i k.1 k.2).2.1) hBdis (fun k => (hfA k).1) hψpl hcorr
    refine ⟨Function.invFunOn χ' (S' \ (D' i₀ \ q' i₀ '' stdSimplexBoundary 2)) ∘ g ∘ χ,
      (hχP.trans hg).trans hχ'inv, ?_, ?_⟩
    · intro y hy
      have hχy : χ y ∈ frontier Δ := hχ0 ▸ mem_image_of_mem χ hy
      change Function.invFunOn χ' _ (g (χ y)) = φ y
      rw [hgf hχy]
      exact hG₀φ hy
    · intro i hi y hy
      have hχy : χ y ∈ frontier (A ⟨i, hi⟩) :=
        (hχi i hi).2.2.2 ▸ mem_image_of_mem χ hy
      change Function.invFunOn χ' _ (g (χ y)) = ψ i y
      rw [hgψ ⟨i, hi⟩ hχy]
      change Function.invFunOn χ' _ (χ' (ψ i (Function.invFunOn χ _ (χ y)))) = ψ i y
      rw [(hχc i).bijOn.invOn_invFunOn.1 hy]
      exact hback i (ψ i y) ((hψ i hi).bijOn.mapsTo hy)

end DifferentialGeometry.Topology.PiecewiseLinear
