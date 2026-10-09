/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ComplementComponents
import DifferentialGeometry.Topology.PiecewiseLinear.JordanDiskPasting
import DifferentialGeometry.Topology.PiecewiseLinear.NestedJordanCurves
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralDiskRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralTubeOuterTrace
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellSubdisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isTopologicalCellWithInterior_closure_inside {Γ : Set Schoenflies.Plane}
    (hΓ : Schoenflies.IsJordanCurve Γ) :
    IsTopologicalCellWithInterior 2 (closure (Schoenflies.inside Γ)) (Schoenflies.inside Γ) := by
  obtain ⟨e, -, hecl, hein⟩ := exists_homeomorph_image_closure_inside_eq_closedBall hΓ
  have hball : IsTopologicalCellWithInterior 2 (Metric.closedBall (0 : Schoenflies.Plane) 1)
      (Metric.ball 0 1) := by
    refine ⟨Homeomorph.refl _, ?_⟩
    ext z
    constructor
    · intro hz
      exact ⟨⟨z, Metric.ball_subset_closedBall hz⟩,
        ⟨⟨z, Metric.ball_subset_closedBall hz⟩, mem_ball_zero_iff.mp hz, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      exact mem_ball_zero_iff.mpr hq
  have h := hball.image_of_injOn e.symm.continuous.continuousOn e.symm.injective.injOn
  rw [← hecl, ← hein] at h
  simpa only [image_image, Homeomorph.symm_apply_apply, image_id'] using h

theorem exists_isPLHomeomorphOn_chart_closure_inside {M : Set E3} (hM : IsLocallyPolyhedral M)
    {χ : E3 → Schoenflies.Plane} {ξ : Schoenflies.Plane → E3} (hχ : ContinuousOn χ M)
    (hξ : ContinuousOn ξ (χ '' M)) (hξχ : ∀ x ∈ M, ξ (χ x) = x) {J : Set E3}
    (hJ : IsPLSphere 1 J) (hJM : J ⊆ M)
    (hcl : closure (Schoenflies.inside (χ '' J)) ⊆ χ '' M) :
    ∃ r : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (ξ '' closure (Schoenflies.inside (χ '' J))) ∧
      r '' stdSimplexBoundary 2 = J ∧ ξ '' closure (Schoenflies.inside (χ '' J)) ⊆ M ∧
      ∀ x ∈ M, (x ∈ ξ '' closure (Schoenflies.inside (χ '' J)) ↔
        χ x ∈ closure (Schoenflies.inside (χ '' J))) := by
  have hχi : InjOn χ M := fun x hx y hy hxy => by rw [← hξχ x hx, ← hξχ y hy, hxy]
  have hχξ : ∀ p ∈ χ '' M, χ (ξ p) = p := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hξχ x hx]
  have hΓ : Schoenflies.IsJordanCurve (χ '' J) :=
    isJordanCurve_image_of_isPLSphere_one hJ hJM hχ hχi
  have hsep := Schoenflies.jordan_curve_theorem hΓ
  have hΓcl : closure (Schoenflies.inside (χ '' J)) = Schoenflies.inside (χ '' J) ∪ χ '' J :=
    closure_inside_eq_union hΓ
  have hinsub : Schoenflies.inside (χ '' J) ⊆ χ '' M := subset_closure.trans hcl
  have hξcl : ContinuousOn ξ (closure (Schoenflies.inside (χ '' J))) := hξ.mono hcl
  have hξinj : InjOn ξ (χ '' M) := fun p hp q hq hpq => by rw [← hχξ p hp, ← hχξ q hq, hpq]
  have hmem : ∀ x ∈ M, (x ∈ ξ '' closure (Schoenflies.inside (χ '' J)) ↔
      χ x ∈ closure (Schoenflies.inside (χ '' J))) := by
    intro x hx
    constructor
    · rintro ⟨p, hp, rfl⟩
      rwa [hχξ p (hcl hp)]
    · intro h
      exact ⟨χ x, h, hξχ x hx⟩
  have hDM : ξ '' closure (Schoenflies.inside (χ '' J)) ⊆ M := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hcl hp
    rw [hξχ x hx]
    exact hx
  have hccpt : IsCompact (closure (Schoenflies.inside (χ '' J))) :=
    hsep.isBounded_inside.isCompact_closure
  have hDc : IsCompact (ξ '' closure (Schoenflies.inside (χ '' J))) :=
    hccpt.image_of_continuousOn hξcl
  have hJeq : ξ '' (χ '' J) = J := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [hξχ x (hJM hx)]
      exact hx
    · intro hy
      exact ⟨χ y, ⟨y, hy, rfl⟩, hξχ y (hJM hy)⟩
  have hsd : closure (Schoenflies.inside (χ '' J)) \ Schoenflies.inside (χ '' J) = χ '' J := by
    rw [hΓcl, union_sdiff_left, sdiff_eq_left.mpr
      (Set.disjoint_left.mpr fun p hp hpi => Schoenflies.inside_subset_compl hpi hp)]
  have hDsd :
      ξ '' closure (Schoenflies.inside (χ '' J)) \ ξ '' Schoenflies.inside (χ '' J) = J := by
    rw [← (hξinj.mono hcl).image_sdiff_subset subset_closure, hsd, hJeq]
  have hcell : IsTopologicalCellWithInterior 2 (ξ '' closure (Schoenflies.inside (χ '' J)))
      (ξ '' Schoenflies.inside (χ '' J)) :=
    (isTopologicalCellWithInterior_closure_inside hΓ).image_of_injOn hξcl (hξinj.mono hcl)
  obtain ⟨Q, hQ, hDQ, hQM, -⟩ := hM.exists_isPolyhedron_neighborhood_of_isCompact hDc hDM
  obtain ⟨p₀, hp₀⟩ := hsep.isConnected_inside.nonempty
  have hx₀ : ξ p₀ ∈ ξ '' Schoenflies.inside (χ '' J) := ⟨p₀, hp₀, rfl⟩
  obtain ⟨U₁, hU₁, hU₁eq⟩ := _root_.continuousOn_iff'.mp hχ _ hsep.isOpen_inside
  have hDintU : ∀ y ∈ M, (y ∈ ξ '' Schoenflies.inside (χ '' J) ↔ y ∈ U₁) := by
    intro y hy
    have hiff : y ∈ χ ⁻¹' Schoenflies.inside (χ '' J) ∩ M ↔ y ∈ U₁ ∩ M := by rw [hU₁eq]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact (hiff.mp ⟨by rw [mem_preimage, hχξ p (hinsub hp)]; exact hp, hy⟩).1
    · intro hyU
      exact ⟨χ y, (hiff.mpr ⟨hyU, hy⟩).1, hξχ y hy⟩
  have hDintQ : ξ '' Schoenflies.inside (χ '' J) ⊆ Q \ J := by
    intro y hy
    refine ⟨hDQ (image_mono subset_closure hy), fun hyJ => ?_⟩
    rw [← hDsd] at hyJ
    exact hyJ.2 hy
  have hcomp : connectedComponentIn (Q \ J) (ξ p₀) = ξ '' Schoenflies.inside (χ '' J) := by
    apply Subset.antisymm
    · have hsub := connectedComponentIn_subset (Q \ J) (ξ p₀)
      rcases (isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn) U₁
          (ξ '' closure (Schoenflies.inside (χ '' J)))ᶜ hU₁ hDc.isClosed.isOpen_compl
          (fun y hy => by
            by_cases hyD : y ∈ ξ '' closure (Schoenflies.inside (χ '' J))
            · refine Or.inl ((hDintU y (hQM (hsub hy).1)).mp ?_)
              by_contra hn
              exact (hsub hy).2 (hDsd ▸ ⟨hyD, hn⟩)
            · exact Or.inr hyD)
          (by
            ext y
            simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
            intro hy hyU hyD
            exact hyD (image_mono subset_closure
              ((hDintU y (hQM (hsub hy).1)).mpr hyU))) with h | h
      · intro y hy
        exact (hDintU y (hQM (hsub hy).1)).mpr (h hy)
      · exact absurd (image_mono subset_closure hx₀) (h (mem_connectedComponentIn (hDintQ hx₀)))
    · exact (hsep.isConnected_inside.isPreconnected.image ξ
        (hξ.mono hinsub)).subset_connectedComponentIn hx₀ hDintQ
  have hclD : closure (ξ '' Schoenflies.inside (χ '' J)) =
      ξ '' closure (Schoenflies.inside (χ '' J)) :=
    Subset.antisymm (closure_minimal (image_mono subset_closure) hDc.isClosed)
      hcell.subset_closure
  obtain ⟨TQ, hTQfin, hTQ⟩ := hQ.exists_simplicialComplex
  obtain ⟨TL, hTLfin, hTL⟩ := hJ.isPolyhedron.exists_simplicialComplex
  have : Finite TQ.faces := hTQfin.to_subtype
  have : Finite TL.faces := hTLfin.to_subtype
  have hLQ : TL.space ⊆ TQ.space := by
    rw [hTQ, hTL, ← hDsd]
    exact sdiff_subset.trans hDQ
  have hpoly := isPolyhedron_closure_connectedComponentIn_sdiff_of_subset TQ TL hLQ (ξ p₀)
  rw [hTQ, hTL, hcomp, hclD] at hpoly
  obtain ⟨r, hr, hrb⟩ := hcell.exists_isPLHomeomorphOn_of_isPolyhedron hpoly (hDsd.symm ▸ hJ)
  exact ⟨r, hr, hrb.trans hDsd, hDM, hmem⟩

section PseudoCells

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd Ec Eint Ebd : Finset E3 → Set E3} {h : E3 → E3} {Cpp : E3 → Set E3}
  {XK : Geometry.SimplicialComplex ℝ E3}

theorem IsHandleDecompositionOfTube.subset_pseudoCell_of_isPreconnected
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp) {S : Set E3}
    (hS : IsPreconnected S)
    (hSA : S ⊆ ⋃ e ∈ {e : Finset E3 | e ∈ K.faces ∧ e.card = 2}, Ec e) {e : Finset E3}
    (he : e ∈ K.faces) (hcard : e.card = 2) (hSe : (S ∩ Ec e).Nonempty) : S ⊆ Ec e := by
  have hfin : {f : Finset E3 | f ∈ K.faces ∧ f.card = 2}.Finite :=
    hd.tube.facesFinite.subset fun f hf => hf.1
  set Oth := ⋃ e' ∈ {e' : Finset E3 | e' ∈ K.faces ∧ e'.card = 2 ∧ e' ≠ e}, Ec e' with hOthdef
  have hOthc : IsClosed Oth := (hfin.subset fun e' he' => ⟨he'.1, he'.2.1⟩).isClosed_biUnion
    fun e' he' => (hd.pseudoCell e' he'.1 he'.2.1).isClosed
  have hcov : S ⊆ Ec e ∪ Oth := by
    intro y hy
    obtain ⟨e', ⟨he', hcard'⟩, hye'⟩ := mem_iUnion₂.mp (hSA hy)
    by_cases hee : e' = e
    · exact Or.inl (hee ▸ hye')
    · exact Or.inr (mem_iUnion₂.mpr ⟨e', ⟨he', hcard', hee⟩, hye'⟩)
  have hdis : Disjoint (Ec e) Oth := by
    refine Set.disjoint_left.mpr fun y hye hyO => ?_
    obtain ⟨e', ⟨he', hcard', hne⟩, hye'⟩ := mem_iUnion₂.mp hyO
    exact Set.disjoint_left.mp (hd.pseudoCellDisjoint e he hcard e' he' hcard' hne.symm) hye hye'
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hS) (Ec e) Oth
      (hd.pseudoCell e he hcard).isClosed hOthc hcov
      (by rw [hdis.inter_eq, inter_empty]) with h1 | h1
  · exact h1
  · obtain ⟨y, hyS, hye⟩ := hSe
    exact absurd (h1 hyS) (Set.disjoint_left.mp hdis hye)

theorem IsPolyhedralTubeNeighborhood.center_mem_inside_trace
    (hd : IsHandleDecompositionOfTube K N C D Dbd h N' Ec Eint Ebd Cpp)
    (h2 : IsPolyhedralTubeNeighborhood K h N' Ec Eint Ebd XK)
    (h34 : HasSinglePolygonTraces K h Ec XK.space) {e : Finset E3} (he : e ∈ K.faces)
    (hcard : e.card = 2) {Ψ : E3 → Schoenflies.Plane} {Φ : Schoenflies.Plane → E3}
    (hΨc : ContinuousOn Ψ (Eint e)) (hΦc : ContinuousOn Φ (Metric.ball 0 1))
    (hΨb : MapsTo Ψ (Eint e) (Metric.ball 0 1)) (hΦb : MapsTo Φ (Metric.ball 0 1) (Eint e))
    (hΦΨ : ∀ x ∈ Eint e, Φ (Ψ x) = x)
    (hΨΦ : ∀ p ∈ Metric.ball (0 : Schoenflies.Plane) 1, Ψ (Φ p) = p) :
    Ψ (h (e.centroid ℝ id)) ∈ Schoenflies.inside (Ψ '' (Ec e ∩ frontier XK.space)) := by
  have hpc := hd.pseudoCell e he hcard
  obtain ⟨hJ, DJint, hcell, hsd, hP⟩ := h34 e he hcard
  have hT := h2.trace_subset hd he hcard
  obtain ⟨-, himg⟩ := hpc.subset_and_image_eq_inside hΨc hΦc hΨb hΦb hΦΨ hΨΦ hcell
    inter_subset_left (hsd.symm ▸ hJ) (hsd.symm ▸ hT.trans sdiff_subset) hP hpc.centerMem
  rw [hsd] at himg
  exact himg ▸ mem_image_of_mem Ψ hP

end PseudoCells

end DifferentialGeometry.Topology.PiecewiseLinear
