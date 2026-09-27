/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceSplit
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCappingInvariants

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsCombinatorialManifoldWithBoundary.exists_separating_split_reducing_nullTraceCount
    [d : DecidableEq E3] (X : Geometry.SimplicialComplex ℝ E3) [Finite X.faces]
    (hX : IsCombinatorialManifoldWithBoundary 2 X) (hXo : IsOrientable 2 X)
    {I H K R T O F : Set E3} (htrace : HasFiniteCollaredTrace X.space T)
    (hT : IsPLTorus T) (h303 : Moise303) (hI : IsOpen I) (hIc : IsConnected I)
    (hHI : H ⊆ I) (hKI : K ⊆ I) (hHK : Disjoint H K)
    (hH : IsClosed (((↑) : I → E3) ⁻¹' H)) (hK : IsClosed (((↑) : I → E3) ⁻¹' K))
    (hCI : R ∪ (T ∪ X.space) ⊆ I) (hC : IsSeparatorIn I (R ∪ (T ∪ X.space)) H K)
    (hO : IsOpen O) (hTO : T ⊆ O) (hOI : O ⊆ I) (hOHK : Disjoint O (H ∪ K))
    (hRO : Disjoint R O) (hFO : Disjoint F O)
    (hboundary : (boundaryComplex 2 X).space ∩ O ⊆ T)
    (hnull : ∃ G ∈ traceCircles X.space T, boundsDiskIn G T) :
    ∃ (Q : Geometry.SimplicialComplex ℝ E3) (hQfin : Q.faces.Finite),
      letI := hQfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 Q ∧ IsOrientable 2 Q ∧
      HasFiniteCollaredTrace Q.space T ∧ IsSeparatorIn I (R ∪ (T ∪ Q.space)) H K ∧
      R ∪ (T ∪ Q.space) ⊆ I ∧
      IsProtectedReplacement (R ∪ (T ∪ X.space)) (R ∪ (T ∪ Q.space)) F O ∧
      Q.space \ O = X.space \ O ∧ traceCircles Q.space T ⊆ traceCircles X.space T ∧
      nullTraceCount Q.space T < nullTraceCount X.space T ∧
      (boundaryComplex 2 Q).space ∩ O ⊆ T ∧
      (boundaryComplex 2 Q).space ⊆ (boundaryComplex 2 X).space ∧
      eulerChar Q = eulerChar X + 1 ∧
      ∃ G ∈ traceCircles X.space T,
        (boundaryComplex 2 Q).space = (boundaryComplex 2 X).space \ G := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨L', hstate, hsep, hsubI, hprot, hout, hseams, hcount,
      Δ, r, f, hr, -, hmeet, hG, hf, hfix, -⟩ :=
    htrace.exists_split_reducing_nullTraceCount_with_cap hT h303 hI hIc hHI hKI hHK hH hK
      hCI hC hO hTO hOI hOHK hRO hFO hnull
  obtain ⟨Q, hQfin, hQ, hQo, hQspace, hQb, hQχ⟩ :=
    hX.exists_surface_of_isPLHomeomorphOn_union_disk X hXo hr hmeet
      (htrace.circleCollar _ hG) hf
  let _ : Finite Q.faces := hQfin.to_subtype
  have hfixBoundary : EqOn f id ((boundaryComplex 2 X).space \ r '' stdSimplexBoundary 2) := by
    apply hfix.mono
    intro x hx
    have hxX := boundaryComplex_space_subset 2 X hx.1
    by_cases hxO : x ∈ O
    · exact Or.inr ⟨⟨hxX, hboundary ⟨hx.1, hxO⟩⟩, hx.2⟩
    · exact Or.inl ⟨hxX, hxO⟩
  have hQb' : (boundaryComplex 2 Q).space =
      (boundaryComplex 2 X).space \ r '' stdSimplexBoundary 2 := by
    rw [hQb]
    simpa only [image_id] using hfixBoundary.image_eq
  refine ⟨Q, hQfin, hQ, hQo, hQspace.symm ▸ hstate, hQspace.symm ▸ hsep,
    hQspace.symm ▸ hsubI, hQspace.symm ▸ hprot, hQspace.symm ▸ hout,
    hQspace.symm ▸ hseams, hQspace.symm ▸ hcount, ?_,
    hQb'.subset.trans sdiff_subset, hQχ, r '' stdSimplexBoundary 2, hG, hQb'⟩
  exact fun x hx => hboundary ⟨(hQb'.subset hx.1).1, hx.2⟩

end DifferentialGeometry.Topology.PiecewiseLinear
