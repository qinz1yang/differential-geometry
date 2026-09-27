/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Covering.SheetTrace
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BranchCollarSides

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}
  {E : Type*} [TopologicalSpace E] [T2Space E]

theorem source_quarter_cap_eq_of_common_source_point
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {ι : M → E} (hιc : Continuous ι) (hι : Function.Injective ι)
    {J Q C : Set (EuclideanSpace ℝ (Fin 2))}
    {ρ : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 2)}
    (hρ : hD.IsTwoSidedBranchCollar c J Q C ρ)
    {A B : Bool → Set (EuclideanSpace ℝ (Fin 2))} {K : Set E}
    (hAc : ∀ b, IsCompact (A b)) (hBc : ∀ b, IsCompact (B b))
    (hAD : ∀ b, A b ⊆ D.domain) (hBD : ∀ b, B b ⊆ D.domain)
    (hAi : ∀ b, InjOn D (A b)) (hBi : ∀ b, InjOn D (B b))
    (hAA : Disjoint (A false) (A true)) (hBB : Disjoint (B false) (B true))
    (hpreA : ∀ x ∈ D.domain, ι (D x) ∈ K → x ∈ A false ∪ A true)
    (hpreB : ∀ x ∈ D.domain, ι (D x) ∈ K → x ∈ B false ∪ B true)
    (b d positive : Bool)
    (hconnA : IsPreconnected (K ∩ (ι ∘ D) '' (A b ∩ collarHalf J ρ positive)))
    (hconnB : IsPreconnected (K ∩ (ι ∘ D) '' (B d ∩ collarHalf J ρ positive)))
    {a : EuclideanSpace ℝ (Fin 2)} (ha : a ∈ J) (haA : a ∈ A b) (haB : a ∈ B d)
    (hfa : ι (D a) ∈ K) :
    K ∩ (ι ∘ D) '' (A b ∩ collarHalf J ρ positive) =
      K ∩ (ι ∘ D) '' (B d ∩ collarHalf J ρ positive) := by
  have hAB : Disjoint (A b) (A (!b)) := by
    cases b
    · exact hAA
    · exact hAA.symm
  have hBD' : Disjoint (B d) (B (!d)) := by
    cases d
    · exact hBB
    · exact hBB.symm
  have hcoverA : ∀ x ∈ A b, (ι ∘ D) x ∈ K → x ∈ B d ∪ B (!d) := by
    intro x hx hfx
    have h := hpreB x (hAD b hx) hfx
    cases d
    · exact h
    · exact h.symm
  have hcoverB : ∀ x ∈ B d, (ι ∘ D) x ∈ K → x ∈ A b ∪ A (!b) := by
    intro x hx hfx
    have h := hpreA x (hBD d hx) hfx
    cases b
    · exact h
    · exact h.symm
  exact Covering.inter_image_source_side_eq_of_preconnected (hAc b) (hBc d)
    (hιc.comp_continuousOn (D.continuousOn.mono (hAD b)))
    (hιc.comp_continuousOn (D.continuousOn.mono (hBD d)))
    (fun x hx y hy hxy => hAi b hx hy (hι hxy))
    (fun x hx y hy hxy => hBi d hx hy (hι hxy))
    (hAc b).isClosed (hAc (!b)).isClosed (hBc d).isClosed (hBc (!d)).isClosed
    hAB hBD' hcoverA hcoverB hconnA hconnB haA haB (hD.subset_collarHalf hρ positive ha) hfa

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSingularCellData
