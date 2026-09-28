/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CollaredSurfaceCapPartition
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCappingInvariants

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_orientable_surface_pair_of_circle_cap [d : DecidableEq E3]
    (X₀ X₁ : Geometry.SimplicialComplex ℝ E3) [Finite X₀.faces] [Finite X₁.faces]
    (hX₀ : IsCombinatorialManifoldWithBoundary 2 X₀) (hX₀o : IsOrientable 2 X₀)
    (hX₁ : IsCombinatorialManifoldWithBoundary 2 X₁) (hX₁o : IsOrientable 2 X₁)
    {Δ L' T O : Set E3} {r : (Fin 3 → ℝ) → E3} {f : E3 → E3}
    (htrace₀ : HasFiniteCollaredTrace X₀.space T) (hdis : Disjoint X₀.space X₁.space)
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hG₀ : r '' stdSimplexBoundary 2 ∈ traceCircles X₀.space T)
    (hmeet : (X₀.space ∪ X₁.space) ∩ Δ = r '' stdSimplexBoundary 2) (hΔO : Δ ⊆ O)
    (hf : IsPLHomeomorphOn f ((X₀.space ∪ X₁.space) ∪ Δ) L')
    (hout : L' \ O = (X₀.space ∪ X₁.space) \ O)
    (hfix : EqOn f id (((X₀.space ∪ X₁.space) \ O) ∪
      (((X₀.space ∪ X₁.space) ∩ T) \ r '' stdSimplexBoundary 2)))
    (hnew : HasFiniteCollaredTrace L' T)
    (htrace : L' ∩ T = ((X₀.space ∪ X₁.space) ∩ T) \ r '' stdSimplexBoundary 2)
    (hboundary₀ : (boundaryComplex 2 X₀).space ∩ O ⊆ T)
    (hboundary₁ : (boundaryComplex 2 X₁).space ∩ O ⊆ T) :
    ∃ (Q₀ Q₁ : Geometry.SimplicialComplex ℝ E3)
      (hQ₀fin : Q₀.faces.Finite) (hQ₁fin : Q₁.faces.Finite),
      letI := hQ₀fin.to_subtype
      letI := hQ₁fin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 Q₀ ∧ IsOrientable 2 Q₀ ∧
      IsCombinatorialManifoldWithBoundary 2 Q₁ ∧ IsOrientable 2 Q₁ ∧
      HasFiniteCollaredTrace Q₀.space T ∧ HasFiniteCollaredTrace Q₁.space T ∧
      IsPLHomeomorphOn f (X₀.space ∪ Δ) Q₀.space ∧ IsPLHomeomorphOn f X₁.space Q₁.space ∧
      Disjoint Q₀.space Q₁.space ∧ L' = Q₀.space ∪ Q₁.space ∧
      Q₀.space \ O = X₀.space \ O ∧ Q₁.space \ O = X₁.space \ O ∧
      Q₀.space ∩ T = (X₀.space ∩ T) \ r '' stdSimplexBoundary 2 ∧
      Q₁.space ∩ T = X₁.space ∩ T ∧
      (boundaryComplex 2 Q₀).space = (boundaryComplex 2 X₀).space \ r '' stdSimplexBoundary 2 ∧
      (boundaryComplex 2 Q₁).space = (boundaryComplex 2 X₁).space ∧
      eulerChar Q₀ = eulerChar X₀ + 1 ∧ eulerChar Q₁ = eulerChar X₁ := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  have hΔ : IsPLBall 2 Δ := ⟨r, hr⟩
  have hGsub : r '' stdSimplexBoundary 2 ⊆ X₀.space :=
    (traceCircles_subset hG₀).trans inter_subset_left
  have hmeet₀ : X₀.space ∩ Δ = r '' stdSimplexBoundary 2 := Subset.antisymm
    (fun x hx => hmeet.subset ⟨Or.inl hx.1, hx.2⟩)
    (fun x hx => ⟨hGsub hx, (hmeet.symm.subset hx).2⟩)
  obtain ⟨P₀, P₁, hf₀, hf₁, hstate₀, hstate₁, hPdis, hcover, hout₀, hout₁, hmeet₀T, hmeet₁T⟩ :=
    exists_collared_partition_of_circle_cap (isPolyhedron_space X₀) (isPolyhedron_space X₁)
      hΔ.isPolyhedron hdis hGsub hmeet hΔO hf hout hfix hnew htrace
  obtain ⟨Q₀, hQ₀fin, hQ₀, hQ₀o, hQ₀space, hQ₀b, hQ₀χ⟩ :=
    hX₀.exists_surface_of_isPLHomeomorphOn_union_disk X₀ hX₀o hr hmeet₀
      (htrace₀.circleCollar _ hG₀) hf₀
  obtain ⟨Q₁, hQ₁fin, hQ₁space⟩ := hstate₁.isPolyhedron.exists_simplicialComplex
  let _ : Finite Q₀.faces := hQ₀fin.to_subtype
  let _ : Finite Q₁.faces := hQ₁fin.to_subtype
  have hfQ₀ : IsPLHomeomorphOn f (X₀.space ∪ Δ) Q₀.space := by rw [hQ₀space]; exact hf₀
  have hfQ₁ : IsPLHomeomorphOn f X₁.space Q₁.space := by rw [hQ₁space]; exact hf₁
  have hQ₁ := hX₁.of_isPLHomeomorphOn hfQ₁
  have hQ₁o := (isOrientable_iff_of_isPLHomeomorphOn hX₁ hfQ₁).mp hX₁o
  have hfix₀ : EqOn f id ((boundaryComplex 2 X₀).space \ r '' stdSimplexBoundary 2) := by
    apply hfix.mono
    intro x hx
    have hxX := boundaryComplex_space_subset 2 X₀ hx.1
    by_cases hxO : x ∈ O
    · exact Or.inr ⟨⟨Or.inl hxX, hboundary₀ ⟨hx.1, hxO⟩⟩, hx.2⟩
    · exact Or.inl ⟨Or.inl hxX, hxO⟩
  have hfix₁ : EqOn f id (boundaryComplex 2 X₁).space := by
    apply hfix.mono
    intro x hx
    have hxX := boundaryComplex_space_subset 2 X₁ hx
    have hxG : x ∉ r '' stdSimplexBoundary 2 := fun hxG =>
      disjoint_left.mp hdis (hGsub hxG) hxX
    by_cases hxO : x ∈ O
    · exact Or.inr ⟨⟨Or.inr hxX, hboundary₁ ⟨hx, hxO⟩⟩, hxG⟩
    · exact Or.inl ⟨Or.inr hxX, hxO⟩
  have hQ₀b' : (boundaryComplex 2 Q₀).space =
      (boundaryComplex 2 X₀).space \ r '' stdSimplexBoundary 2 := by
    rw [hQ₀b]
    simpa only [image_id] using hfix₀.image_eq
  have hQ₁b : (boundaryComplex 2 Q₁).space = (boundaryComplex 2 X₁).space := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn X₁ Q₁ hX₁ hfQ₁]
    simpa only [image_id] using hfix₁.image_eq
  refine ⟨Q₀, Q₁, hQ₀fin, hQ₁fin, hQ₀, hQ₀o, hQ₁, hQ₁o,
    hQ₀space.symm ▸ hstate₀, hQ₁space.symm ▸ hstate₁, hfQ₀, hfQ₁,
    ?_, ?_, ?_, ?_, ?_, ?_, hQ₀b', hQ₁b, hQ₀χ,
    (eulerChar_eq_of_isPLHomeomorphOn X₁ Q₁ hfQ₁).symm⟩
  · rwa [hQ₀space, hQ₁space]
  · rwa [hQ₀space, hQ₁space]
  · rwa [hQ₀space]
  · rwa [hQ₁space]
  · rwa [hQ₀space]
  · rwa [hQ₁space]

theorem exists_orientable_surface_pair_of_trace_cap [d : DecidableEq E3]
    (X₀ X₁ : Geometry.SimplicialComplex ℝ E3) [Finite X₀.faces] [Finite X₁.faces]
    (hX₀ : IsCombinatorialManifoldWithBoundary 2 X₀) (hX₀o : IsOrientable 2 X₀)
    (hX₁ : IsCombinatorialManifoldWithBoundary 2 X₁) (hX₁o : IsOrientable 2 X₁)
    {Δ L' T O : Set E3} {r : (Fin 3 → ℝ) → E3} {f : E3 → E3}
    (htrace₀ : HasFiniteCollaredTrace X₀.space T)
    (htrace₁ : HasFiniteCollaredTrace X₁.space T) (hdis : Disjoint X₀.space X₁.space)
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hG : r '' stdSimplexBoundary 2 ∈ traceCircles (X₀.space ∪ X₁.space) T)
    (hmeet : (X₀.space ∪ X₁.space) ∩ Δ = r '' stdSimplexBoundary 2) (hΔO : Δ ⊆ O)
    (hf : IsPLHomeomorphOn f ((X₀.space ∪ X₁.space) ∪ Δ) L')
    (hout : L' \ O = (X₀.space ∪ X₁.space) \ O)
    (hfix : EqOn f id (((X₀.space ∪ X₁.space) \ O) ∪
      (((X₀.space ∪ X₁.space) ∩ T) \ r '' stdSimplexBoundary 2)))
    (hnew : HasFiniteCollaredTrace L' T)
    (htrace : L' ∩ T = ((X₀.space ∪ X₁.space) ∩ T) \ r '' stdSimplexBoundary 2)
    (hboundary₀ : (boundaryComplex 2 X₀).space ∩ O ⊆ T)
    (hboundary₁ : (boundaryComplex 2 X₁).space ∩ O ⊆ T) :
    ∃ (Q₀ Q₁ : Geometry.SimplicialComplex ℝ E3)
      (hQ₀fin : Q₀.faces.Finite) (hQ₁fin : Q₁.faces.Finite),
      letI := hQ₀fin.to_subtype
      letI := hQ₁fin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 Q₀ ∧ IsOrientable 2 Q₀ ∧
      IsCombinatorialManifoldWithBoundary 2 Q₁ ∧ IsOrientable 2 Q₁ ∧
      HasFiniteCollaredTrace Q₀.space T ∧ HasFiniteCollaredTrace Q₁.space T ∧
      Disjoint Q₀.space Q₁.space ∧ L' = Q₀.space ∪ Q₁.space ∧
      Q₀.space \ O = X₀.space \ O ∧ Q₁.space \ O = X₁.space \ O ∧
      Q₀.space ∩ T = (X₀.space ∩ T) \ r '' stdSimplexBoundary 2 ∧
      Q₁.space ∩ T = (X₁.space ∩ T) \ r '' stdSimplexBoundary 2 ∧
      (boundaryComplex 2 Q₀).space = (boundaryComplex 2 X₀).space \ r '' stdSimplexBoundary 2 ∧
      (boundaryComplex 2 Q₁).space = (boundaryComplex 2 X₁).space \ r '' stdSimplexBoundary 2 ∧
      ((r '' stdSimplexBoundary 2 ∈ traceCircles X₀.space T ∧
        IsPLHomeomorphOn f (X₀.space ∪ Δ) Q₀.space ∧
        IsPLHomeomorphOn f X₁.space Q₁.space ∧
        eulerChar Q₀ = eulerChar X₀ + 1 ∧ eulerChar Q₁ = eulerChar X₁) ∨
        (r '' stdSimplexBoundary 2 ∈ traceCircles X₁.space T ∧
          IsPLHomeomorphOn f X₀.space Q₀.space ∧
          IsPLHomeomorphOn f (X₁.space ∪ Δ) Q₁.space ∧
          eulerChar Q₀ = eulerChar X₀ ∧ eulerChar Q₁ = eulerChar X₁ + 1)) := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  have hseams := traceCircles_eq_union_of_disjoint htrace₀.finiteTrace htrace₁.finiteTrace
    htrace₀.traceCover htrace₁.traceCover hdis
  rcases hseams.subset hG with hG₀ | hG₁
  · obtain ⟨Q₀, Q₁, hQ₀fin, hQ₁fin, hQ₀, hQ₀o, hQ₁, hQ₁o, hstate₀, hstate₁,
        hf₀, hf₁, hQdis, hcover, hout₀, hout₁, hmeet₀, hmeet₁, hQ₀b, hQ₁b, hχ₀, hχ₁⟩ :=
      exists_orientable_surface_pair_of_circle_cap X₀ X₁ hX₀ hX₀o hX₁ hX₁o htrace₀ hdis
        hr hG₀ hmeet hΔO hf hout hfix hnew htrace hboundary₀ hboundary₁
    let _ : Finite Q₀.faces := hQ₀fin.to_subtype
    let _ : Finite Q₁.faces := hQ₁fin.to_subtype
    have hdiff (V : Set E3) (hV : V ⊆ X₁.space) : V \ r '' stdSimplexBoundary 2 = V :=
      Subset.antisymm sdiff_subset fun x hx => ⟨hx, fun hxG =>
        disjoint_left.mp hdis (traceCircles_subset hG₀ hxG).1 (hV hx)⟩
    exact ⟨Q₀, Q₁, hQ₀fin, hQ₁fin, hQ₀, hQ₀o, hQ₁, hQ₁o, hstate₀, hstate₁,
      hQdis, hcover, hout₀, hout₁, hmeet₀, hmeet₁.trans (hdiff _ inter_subset_left).symm,
      hQ₀b, hQ₁b.trans (hdiff _ (boundaryComplex_space_subset 2 X₁)).symm,
      Or.inl ⟨hG₀, hf₀, hf₁, hχ₀, hχ₁⟩⟩
  · obtain ⟨Q₁, Q₀, hQ₁fin, hQ₀fin, hQ₁, hQ₁o, hQ₀, hQ₀o, hstate₁, hstate₀,
        hf₁, hf₀, hQdis, hcover, hout₁, hout₀, hmeet₁, hmeet₀, hQ₁b, hQ₀b, hχ₁, hχ₀⟩ :=
      exists_orientable_surface_pair_of_circle_cap X₁ X₀ hX₁ hX₁o hX₀ hX₀o htrace₁ hdis.symm
        hr hG₁ (by rwa [union_comm X₁.space X₀.space]) hΔO
        (by rwa [union_comm X₁.space X₀.space])
        (by rwa [union_comm X₁.space X₀.space])
        (by rwa [union_comm X₁.space X₀.space]) hnew
        (by rwa [union_comm X₁.space X₀.space]) hboundary₁ hboundary₀
    let _ : Finite Q₀.faces := hQ₀fin.to_subtype
    let _ : Finite Q₁.faces := hQ₁fin.to_subtype
    have hdiff (V : Set E3) (hV : V ⊆ X₀.space) : V \ r '' stdSimplexBoundary 2 = V :=
      Subset.antisymm sdiff_subset fun x hx => ⟨hx, fun hxG =>
        disjoint_left.mp hdis.symm (traceCircles_subset hG₁ hxG).1 (hV hx)⟩
    exact ⟨Q₀, Q₁, hQ₀fin, hQ₁fin, hQ₀, hQ₀o, hQ₁, hQ₁o, hstate₀, hstate₁,
      hQdis.symm, hcover.trans (union_comm _ _), hout₀, hout₁,
      hmeet₀.trans (hdiff _ inter_subset_left).symm, hmeet₁,
      hQ₀b.trans (hdiff _ (boundaryComplex_space_subset 2 X₀)).symm, hQ₁b,
      Or.inr ⟨hG₁, hf₀, hf₁, hχ₀, hχ₁⟩⟩
end DifferentialGeometry.Topology.PiecewiseLinear
