/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceSeamDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCapReplacement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_polyhedral_disk_split_reducing_seams (h303 : Moise303)
    (I H K R T L Δ D₁ D₂ Ω F : Set E3) (r r₁ r₂ : (Fin 3 → ℝ) → E3)
    (hI : IsOpen I) (hIc : IsConnected I) (hHI : H ⊆ I) (hKI : K ⊆ I)
    (hHK : Disjoint H K) (hH : IsClosed (((↑) : I → E3) ⁻¹' H))
    (hK : IsClosed (((↑) : I → E3) ⁻¹' K)) (hCI : (R ∪ (T ∪ L)) ⊆ I)
    (hC : IsSeparatorIn I ((R ∪ (T ∪ L))) H K)
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ) (hΔT : Δ ⊆ T)
    (hr₁ : IsPLHomeomorphOn r₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁)
    (hr₂ : IsPLHomeomorphOn r₂ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₂)
    (hpair : D₁ ∩ D₂ = Δ) (hD₁T : D₁ ∩ T = Δ)
    (hsub : D₁ ∪ D₂ ⊆ (R ∪ (T ∪ L))) (hnear : D₁ ∪ D₂ ∈ 𝓝ˢ[(R ∪ (T ∪ L))] Δ)
    (hΔ₁ : Δ ⊆ D₁ \ r₁ '' stdSimplexBoundary 2)
    (hΔ₂ : Δ ⊆ D₂ \ r₂ '' stdSimplexBoundary 2)
    (hΩ : IsOpen Ω) (hΔΩ : Δ ⊆ Ω) (hΩI : Ω ⊆ I) (hΩHK : Disjoint Ω (H ∪ K))
    (hR : Disjoint R Ω) (hF : Disjoint F Ω) (hfin : (traceCircles L T).Finite)
    (hcover : L ∩ T = ⋃ G ∈ traceCircles L T, G)
    (hG : r '' stdSimplexBoundary 2 ∈ traceCircles L T)
    (hL : IsPolyhedron L) (hD₂T : D₂ ⊆ T)
    (htrace : Ω ∩ L ∩ T ⊆ r '' stdSimplexBoundary 2) :
    ∃ C' L' : Set E3, IsSeparatorIn I C' H K ∧
      IsProtectedReplacement (R ∪ (T ∪ L)) C' F Ω ∧ C' = R ∪ (T ∪ L') ∧ T ⊆ C' ∧
      traceCircles L' T = traceCircles L T \ {r '' stdSimplexBoundary 2} ∧
      nullTraceCount L' T < nullTraceCount L T ∧ L' \ Ω = L \ Ω ∧ IsPolyhedron L' := by
  obtain ⟨C', L', hsep, hprot, heq, hT, hseams, hcount, hout,
      A, B, J, hAnn, hA, hAΔ, hB, hBΩ, hBC, hL'eq, htrace', -⟩ :=
    exists_disk_split_reducing_seams_with_annulus h303 I H K R T L Δ D₁ D₂ Ω F r r₁ r₂
      hI hIc hHI hKI hHK hH hK hCI hC hr hΔT hr₁ hr₂ hpair hD₁T hsub hnear hΔ₁ hΔ₂
      hΩ hΔΩ hΩI hΩHK hR hF hfin hcover hG
  have hL' := isPolyhedron_cap_replacement hL hB.isPolyhedron hr rfl hAnn hA hAΔ
    ⟨r₁, hr₁⟩ (hΔ₁.trans sdiff_subset) hΔT hD₂T hnear hΩ hΔΩ hΩI hR hCI
    ((traceCircles_subset hG).trans inter_subset_left) htrace hBΩ hBC hsep.1 heq hL'eq htrace'
  exact ⟨C', L', hsep, hprot, heq, hT, hseams, hcount, hout, hL'⟩

end DifferentialGeometry.Topology.PiecewiseLinear
