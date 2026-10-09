/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedSphereBoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.CirclePositiveConjugation
import DifferentialGeometry.Topology.PiecewiseLinear.PositiveBoundaryExtension
import DifferentialGeometry.Topology.PiecewiseLinear.SphereHoledBoundaryExtension

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private theorem isPLHomeomorphOn_conjugate_subset
    {C S : Set E3} {D : Set Plane} {χ : E3 → Plane} {δ : E3 → E3}
    (hχ : IsPLHomeomorphOn χ C D) (hS : IsPolyhedron S) (hSC : S ⊆ C)
    (hδ : IsPLHomeomorphOn δ S S) :
    IsPLHomeomorphOn (χ ∘ δ ∘ Function.invFunOn χ C) (χ '' S) (χ '' S) := by
  have hχS := hχ.restrict hS hSC
  have himpoly : IsPolyhedron (χ '' S) :=
    hS.image_of_isPiecewiseAffineOn hχS.isPiecewiseAffineOn hχS.bijOn.injOn
  have himD : χ '' S ⊆ D := image_subset_iff.mpr (hχ.bijOn.mapsTo.mono_left hSC)
  have hi := hχ.symm.restrict himpoly himD
  rw [hχ.bijOn.injOn.invFunOn_image hSC] at hi
  exact (hi.trans hδ).trans hχS

theorem IsPLSphere.exists_extension_of_positive_disk_family
    {ι : Type*} [Finite ι] {S : Set E3} (hS : IsPLSphere 2 S)
    {D : ι → Set E3} {q : ι → (Fin 3 → ℝ) → E3}
    (hq : ∀ i, IsPLHomeomorphOn (q i) (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D i))
    (hDS : ∀ i, D i ⊆ S) (hdis : Pairwise fun i j => Disjoint (D i) (D j))
    {δ : ι → E3 → E3} (hδ : ∀ i, IsPLHomeomorphOn (δ i) (D i) (D i))
    (hpos : ∀ i, IsPLCirclePositive (q i '' stdSimplexBoundary 2) (δ i)) :
    ∃ F : E3 → E3, IsPLHomeomorphOn F S S ∧ ∀ i, EqOn F (δ i) (D i) := by
  classical
  by_cases hι : Nonempty ι
  swap
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    exact ⟨id, hS.isPolyhedron.isPLHomeomorphOn_id, fun i => isEmptyElim i⟩
  let i₀ := Classical.choice hι
  let J := fun i => q i '' stdSimplexBoundary 2
  have hJD (i : ι) : J i ⊆ D i :=
    image_subset_iff.mpr fun _ hx => (hq i).bijOn.mapsTo hx.1
  have hJpoly (i : ι) : IsPolyhedron (J i) :=
    ((hq i).isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron
  have hδJ (i : ι) : δ i '' J i = J i := by
    simpa only [J, image_comp] using ((hq i).trans (hδ i)).image_stdSimplexBoundary_congr (hq i)
  have hδrim (i : ι) : IsPLHomeomorphOn (δ i) (J i) (J i) := by
    have ht := (hδ i).restrict (hJpoly i) (hJD i)
    rwa [hδJ i] at ht
  obtain ⟨χ, Δ, hΔ, hχ, hχ₀, hχi⟩ := hS.exists_holed_chart hq hDS hdis i₀
  let C := S \ (D i₀ \ J i₀)
  let I := {i : ι // i ≠ i₀}
  let A := fun i : I => χ '' D i.1
  have hJ₀C : J i₀ ⊆ C := fun _ hx => ⟨hDS i₀ (hJD i₀ hx), fun h => h.2 hx⟩
  have hJiC (i : I) : J i.1 ⊆ C := (hJD i.1).trans (hχi i.1 i.2).1
  have hA (i : I) : IsPLBall 2 (A i) :=
    (show IsPLBall 2 (D i.1) from ⟨q i.1, hq i.1⟩).of_isPLHomeomorphOn (hχi i.1 i.2).2.2.1
  have hAint (i : I) : A i ⊆ interior Δ := (hχi i.1 i.2).2.1
  have hAfr (i : I) : χ '' J i.1 = frontier (A i) := (hχi i.1 i.2).2.2.2
  have hAdis : Pairwise fun i j : I => Disjoint (A i) (A j) := by
    intro i j hij
    refine disjoint_left.mpr ?_
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have hxy : y = x := hχ.bijOn.injOn ((hχi j.1 j.2).1 hy) ((hχi i.1 i.2).1 hx) hyx
    exact disjoint_left.mp (hdis (fun he => hij (Subtype.ext he))) hx (hxy ▸ hy)
  let d₀ := χ ∘ δ i₀ ∘ Function.invFunOn χ C
  have hd₀ : IsPLHomeomorphOn d₀ (frontier Δ) (frontier Δ) := by
    rw [← hχ₀]
    exact isPLHomeomorphOn_conjugate_subset hχ (hJpoly i₀) hJ₀C (hδrim i₀)
  have hd₀pos : IsPLCirclePositive (frontier Δ) d₀ := by
    rw [← hχ₀]
    exact (hχ.isPLCirclePositive_conj_iff hJ₀C (hδrim i₀).bijOn.mapsTo).mpr (hpos i₀)
  have hcompact : IsCompact (⋃ i : I, A i) :=
    isCompact_iUnion fun i => (hA i).isPolyhedron.isCompact
  have hinside : (⋃ i : I, A i) ⊆ interior Δ := iUnion_subset hAint
  obtain ⟨H, hH, hHouter, hHfix⟩ :=
    exists_positive_boundary_extension_fixing_compact hΔ hcompact hinside hd₀ hd₀pos
  have hmatch (i : I) : H '' A i = A i :=
    ((hHfix.mono (subset_iUnion A i)).image_eq).trans (image_id _)
  have hHinv (i : I) {x : Plane} (hx : x ∈ A i) : Function.invFunOn H Δ x = x := by
    have he := hH.bijOn.invOn_invFunOn.1 (interior_subset (hAint i hx))
    have hfix : H x = x := hHfix (mem_iUnion.mpr ⟨i, hx⟩)
    rwa [hfix] at he
  have hback₀ : Function.invFunOn χ C '' frontier Δ = J i₀ := by
    rw [← hχ₀]
    exact hχ.bijOn.injOn.invFunOn_image hJ₀C
  have hback (i : I) : Function.invFunOn χ C '' frontier (A i) = J i.1 := by
    rw [← hAfr i]
    exact hχ.bijOn.injOn.invFunOn_image (hJiC i)
  have hφC : MapsTo (δ i₀) (Function.invFunOn χ C '' frontier Δ) C := by
    rw [hback₀]
    exact fun _ hx => hJ₀C ((hδrim i₀).bijOn.mapsTo hx)
  have hψC (i : I) : MapsTo (δ i.1) (Function.invFunOn χ C '' frontier (A i)) C := by
    rw [hback i]
    exact fun _ hx => hJiC i ((hδrim i.1).bijOn.mapsTo hx)
  have hψ (i : I) : IsPLHomeomorphOn (χ ∘ δ i.1 ∘ Function.invFunOn χ C)
      (frontier (A i)) (frontier (A i)) := by
    rw [← hAfr i]
    exact isPLHomeomorphOn_conjugate_subset hχ (hJpoly i.1) (hJiC i) (hδrim i.1)
  have hψpos (i : I) : IsPLCirclePositive (frontier (A i))
      ((χ ∘ δ i.1 ∘ Function.invFunOn χ C) ∘ Function.invFunOn H Δ) := by
    have hp : IsPLCirclePositive (frontier (A i)) (χ ∘ δ i.1 ∘ Function.invFunOn χ C) := by
      rw [← hAfr i]
      exact (hχ.isPLCirclePositive_conj_iff (hJiC i) (hδrim i.1).bijOn.mapsTo).mpr (hpos i.1)
    apply hp.of_eqOn
    intro x hx
    change χ (δ i.1 (Function.invFunOn χ C (Function.invFunOn H Δ x))) =
      χ (δ i.1 (Function.invFunOn χ C x))
    rw [hHinv i ((hA i).isPolyhedron.isClosed.frontier_subset hx)]
  obtain ⟨G, hG, hG₀, hGi⟩ :=
    IsPLHomeomorphOn.exists_holed_surface_extension_of_prescribed_boundary_maps
      hχ hχ hH hΔ hΔ hA hA (fun i => (hAint i).trans interior_subset)
      hAint hAdis hmatch hφC hHouter hψC hψ hψpos
  have hint (i : ι) (hi : i ≠ i₀) :
      interior (χ '' D i) = χ '' D i \ χ '' J i := by
    rw [(hχi i hi).2.2.2, self_sdiff_frontier]
  obtain ⟨hPeq, hPC⟩ := image_sdiff_iUnion_sdiff_eq (S := S) i₀ hχ.bijOn rfl
    (fun i hi => (hχi i hi).1) hJD hint
  have hRimage : Function.invFunOn χ C '' (Δ \ ⋃ i : I, interior (A i)) =
      S \ ⋃ i, (D i \ J i) := by
    rw [← hPeq, hχ.bijOn.injOn.invFunOn_image hPC]
  rw [hRimage] at hG
  rw [hback₀] at hG₀
  have hagree (i : ι) : EqOn G (δ i) (J i) := by
    by_cases hi : i = i₀
    · subst i
      exact hG₀
    · have ht := hGi ⟨i, hi⟩
      rw [hback ⟨i, hi⟩] at ht
      exact ht
  obtain ⟨F, hF, -, hFD⟩ := hS.exists_isPLHomeomorphOn_glue_holed_disks
    hS hq hq hDS hDS hdis hdis hG hδ hagree
  exact ⟨F, hF, hFD⟩

end DifferentialGeometry.Topology.PiecewiseLinear
