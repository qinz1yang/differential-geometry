/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceSplit
import DifferentialGeometry.Topology.PiecewiseLinear.SurfacePairCapping
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceTraceMonotonicity

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_separating_surface_pair_split [d : DecidableEq E3]
    (X₀ X₁ : Geometry.SimplicialComplex ℝ E3) [Finite X₀.faces] [Finite X₁.faces]
    (hX₀ : IsCombinatorialManifoldWithBoundary 2 X₀) (hX₀o : IsOrientable 2 X₀)
    (hX₁ : IsCombinatorialManifoldWithBoundary 2 X₁) (hX₁o : IsOrientable 2 X₁)
    {I H K R T O F : Set E3} (htrace₀ : HasFiniteCollaredTrace X₀.space T)
    (htrace₁ : HasFiniteCollaredTrace X₁.space T) (hdis : Disjoint X₀.space X₁.space)
    (hT : IsPLTorus T) (h303 : Moise303) (hI : IsOpen I) (hIc : IsConnected I)
    (hHI : H ⊆ I) (hKI : K ⊆ I) (hHK : Disjoint H K)
    (hH : IsClosed (((↑) : I → E3) ⁻¹' H)) (hK : IsClosed (((↑) : I → E3) ⁻¹' K))
    (hCI : R ∪ (T ∪ (X₀.space ∪ X₁.space)) ⊆ I)
    (hC : IsSeparatorIn I (R ∪ (T ∪ (X₀.space ∪ X₁.space))) H K)
    (hO : IsOpen O) (hTO : T ⊆ O) (hOI : O ⊆ I) (hOHK : Disjoint O (H ∪ K))
    (hRO : Disjoint R O) (hFO : Disjoint F O)
    (hboundary₀ : (boundaryComplex 2 X₀).space ∩ O ⊆ T)
    (hboundary₁ : (boundaryComplex 2 X₁).space ∩ O ⊆ T)
    (hnull : ∃ G ∈ traceCircles (X₀.space ∪ X₁.space) T, boundsDiskIn G T) :
    ∃ (Q₀ Q₁ : Geometry.SimplicialComplex ℝ E3)
      (hQ₀fin : Q₀.faces.Finite) (hQ₁fin : Q₁.faces.Finite) (G : Set E3),
      letI := hQ₀fin.to_subtype
      letI := hQ₁fin.to_subtype
      G ∈ traceCircles (X₀.space ∪ X₁.space) T ∧
      IsCombinatorialManifoldWithBoundary 2 Q₀ ∧ IsOrientable 2 Q₀ ∧
      IsCombinatorialManifoldWithBoundary 2 Q₁ ∧ IsOrientable 2 Q₁ ∧
      HasFiniteCollaredTrace Q₀.space T ∧ HasFiniteCollaredTrace Q₁.space T ∧
      Disjoint Q₀.space Q₁.space ∧ IsSeparatorIn I (R ∪ (T ∪ (Q₀.space ∪ Q₁.space))) H K ∧
      R ∪ (T ∪ (Q₀.space ∪ Q₁.space)) ⊆ I ∧
      IsProtectedReplacement (R ∪ (T ∪ (X₀.space ∪ X₁.space)))
        (R ∪ (T ∪ (Q₀.space ∪ Q₁.space))) F O ∧
      Q₀.space \ O = X₀.space \ O ∧ Q₁.space \ O = X₁.space \ O ∧
      traceCircles Q₀.space T ⊆ traceCircles X₀.space T ∧
      traceCircles Q₁.space T ⊆ traceCircles X₁.space T ∧
      Q₀.space ∩ T = (X₀.space ∩ T) \ G ∧ Q₁.space ∩ T = (X₁.space ∩ T) \ G ∧
      (boundaryComplex 2 Q₀).space = (boundaryComplex 2 X₀).space \ G ∧
      (boundaryComplex 2 Q₁).space = (boundaryComplex 2 X₁).space \ G ∧
      nullTraceCount (Q₀.space ∪ Q₁.space) T < nullTraceCount (X₀.space ∪ X₁.space) T ∧
      eulerChar Q₀ + eulerChar Q₁ = eulerChar X₀ + eulerChar X₁ + 1 ∧
      ∃ (Δ : Set E3) (r : (Fin 3 → ℝ) → E3) (f : E3 → E3),
        IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧ r '' stdSimplexBoundary 2 = G ∧ Δ ⊆ T ∧
        (X₀.space ∪ X₁.space) ∩ Δ = G ∧
        EqOn f id ((boundaryComplex 2 X₀).space \ G) ∧
        EqOn f id ((boundaryComplex 2 X₁).space \ G) ∧
        ((G ∈ traceCircles X₀.space T ∧ IsPLHomeomorphOn f (X₀.space ∪ Δ) Q₀.space ∧
          IsPLHomeomorphOn f X₁.space Q₁.space ∧
          eulerChar Q₀ = eulerChar X₀ + 1 ∧ eulerChar Q₁ = eulerChar X₁) ∨
          (G ∈ traceCircles X₁.space T ∧ IsPLHomeomorphOn f X₀.space Q₀.space ∧
            IsPLHomeomorphOn f (X₁.space ∪ Δ) Q₁.space ∧
            eulerChar Q₀ = eulerChar X₀ ∧ eulerChar Q₁ = eulerChar X₁ + 1)) := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  have hwhole := htrace₀.union_of_disjoint htrace₁ hdis
  obtain ⟨L', hstate, hsep, hsubI, hprot, hout, -, hcount,
      Δ, r, f, hr, hΔT, hmeet, hG, hf, hfix, hnewTrace⟩ :=
    hwhole.exists_split_reducing_nullTraceCount_with_cap hT h303 hI hIc hHI hKI hHK hH hK
      hCI hC hO hTO hOI hOHK hRO hFO hnull
  obtain ⟨Q₀, Q₁, hQ₀fin, hQ₁fin, hQ₀, hQ₀o, hQ₁, hQ₁o, hstate₀, hstate₁,
      hQdis, hcover, hout₀, hout₁, hmeet₀, hmeet₁, hQ₀b, hQ₁b, hcaps⟩ :=
    exists_orientable_surface_pair_of_trace_cap X₀ X₁ hX₀ hX₀o hX₁ hX₁o htrace₀ htrace₁ hdis
      hr hG hmeet (hΔT.trans hTO) hf hout hfix hstate hnewTrace hboundary₀ hboundary₁
  let _ : Finite Q₀.faces := hQ₀fin.to_subtype
  let _ : Finite Q₁.faces := hQ₁fin.to_subtype
  have hfixed (V : Set E3) (hVL : V ⊆ X₀.space ∪ X₁.space) (hVT : V ∩ O ⊆ T) :
      EqOn f id (V \ r '' stdSimplexBoundary 2) := by
    apply hfix.mono
    intro x hx
    by_cases hxO : x ∈ O
    · exact Or.inr ⟨⟨hVL hx.1, hVT ⟨hx.1, hxO⟩⟩, hx.2⟩
    · exact Or.inl ⟨hVL hx.1, hxO⟩
  have hχ : eulerChar Q₀ + eulerChar Q₁ = eulerChar X₀ + eulerChar X₁ + 1 := by
    rcases hcaps with ⟨-, -, -, hχ₀, hχ₁⟩ | ⟨-, -, -, hχ₀, hχ₁⟩ <;> omega
  exact ⟨Q₀, Q₁, hQ₀fin, hQ₁fin, r '' stdSimplexBoundary 2, hG,
    hQ₀, hQ₀o, hQ₁, hQ₁o, hstate₀, hstate₁, hQdis, hcover ▸ hsep, hcover ▸ hsubI,
    hcover ▸ hprot, hout₀, hout₁,
    traceCircles_subset_of_inter_subset htrace₀.traceCover (hmeet₀.subset.trans sdiff_subset),
    traceCircles_subset_of_inter_subset htrace₁.traceCover (hmeet₁.subset.trans sdiff_subset),
    hmeet₀, hmeet₁, hQ₀b, hQ₁b, hcover ▸ hcount, hχ, Δ, r, f, hr, rfl, hΔT, hmeet,
    hfixed _ ((boundaryComplex_space_subset 2 X₀).trans subset_union_left) hboundary₀,
    hfixed _ ((boundaryComplex_space_subset 2 X₁).trans subset_union_right) hboundary₁, hcaps⟩

end DifferentialGeometry.Topology.PiecewiseLinear
