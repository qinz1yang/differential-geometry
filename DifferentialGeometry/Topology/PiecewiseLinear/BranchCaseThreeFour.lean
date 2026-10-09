/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BranchComplexityDrop
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryWordFourArcs

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

open Classical in
theorem exists_four_arc_word_and_simplicialComplexity_lt_of_boundaryBranch
    (hD : NormalSingularCellData D BdM B)
    {cb : hD.singularSet.Branch} (hc : hD.singularSet.IsBoundaryBranch cb)
    {W : Set M} {P Pc Q : Set (EuclideanSpace ℝ (Fin 2))} {d R a b c : ℝ}
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hE : E ∈ (plGroupoid 3).maximalAtlas M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hesrc : e.source ⊆ E.target)
    (hd : 0 ≤ d) (hcR : c + 2 * d ≤ R) (hbd : b < d)
    (hsupp : slideSupportLong R ⊆ e.target)
    (hAt : slideBandA c ⊆ e.target) (hBt : slideBandQ a b ⊆ e.target)
    (hSK : hD.singularSet.branchCarrier cb ⊆ E.symm '' (e.symm '' slideSupportLong R))
    (hW : W ∈ 𝓝ˢ (E.symm '' (e.symm '' slideSupportLong R)))
    (hA : D '' P ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆
      E.symm '' (e.symm '' slideBandA c))
    (hB : D '' Q ∩ E.symm '' (e.symm '' slideSupportLong R) ⊆
      E.symm '' (e.symm '' slideBandQ a b))
    (hAB : D '' P ∩ D '' Q ⊆ E.symm '' (e.symm '' slideSupportLong R))
    (hdom : P ∪ Pc = D.domain) (hPpoly : IsPolyhedron P) (hPcpoly : IsPolyhedron Pc)
    (hinjP : InjOn D P) (hinjQ : InjOn D (Q ∩ D ⁻¹' W)) (hPcQ : Pc ∩ D ⁻¹' W ⊆ Q)
    (hseam : ∀ x ∈ P ∩ Pc, D x ∉ W)
    (hclean : doublePointSet D D.domain ∩ W ⊆ hD.singularSet.branchCarrier cb) :
    ∃ (U : Set M) (h : M → M)
        (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 2)))
        (hKfinite : K.faces.Finite),
      let _ : Finite K.faces := hKfinite.to_subtype
      (∃ (Ab Cb A₁ A₂ A₃ A₄ : Set (EuclideanSpace ℝ (Fin 2)))
          (p q u v : EuclideanSpace ℝ (Fin 2)) (p' q' u' v' : frontier D.domain)
          (σ : Path p' q') (τ : Path q' u') (υ : Path u' v') (φ : Path v' p')
          (ev : loopCircle ≃ₜ frontier D.domain),
        IsPLBall 1 Ab ∧ IsPLBall 1 Cb ∧ Disjoint Ab Cb ∧
        hD.branchPreimage cb = Ab ∪ Cb ∧
        Schoenflies.IsArcBetween Ab p q ∧ Schoenflies.IsArcBetween Cb u v ∧
        (p' : EuclideanSpace ℝ (Fin 2)) = p ∧ (q' : EuclideanSpace ℝ (Fin 2)) = q ∧
        (u' : EuclideanSpace ℝ (Fin 2)) = u ∧ (v' : EuclideanSpace ℝ (Fin 2)) = v ∧
        Set.range (fun t => ((σ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₁ ∧
        Set.range (fun t => ((τ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₂ ∧
        Set.range (fun t => ((υ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₃ ∧
        Set.range (fun t => ((φ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₄ ∧
        frontier D.domain = A₁ ∪ (A₂ ∪ (A₃ ∪ A₄)) ∧
        (∀ θ, ev θ = pathToCircle (σ.trans (τ.trans (υ.trans φ))) θ) ∧
        ((D u = D p ∧ D v = D q) ∨ (D u = D q ∧ D v = D p))) ∧
      IsOpen U ∧ hD.singularSet.branchCarrier cb ⊆ U ∧
      closure U ⊆ W ∧ IsPL 3 3 h ∧ Function.Injective h ∧ EqOn h id Uᶜ ∧ MapsTo h U U ∧
      (∀ (N : Set M) (N₁ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ x ∈ E.source, x ∈ N ↔ E x ∈ N₁) →
        (∀ y ∈ e.source, y ∈ N₁ ↔ 0 ≤ (e y).1) → MapsTo h N N) ∧
      (∀ (N Bd : Set M) (N₁ Bd₁ : Set (EuclideanSpace ℝ (Fin 3))),
        (∀ x ∈ E.source, x ∈ N ↔ E x ∈ N₁) →
        (∀ y ∈ e.source, y ∈ N₁ ↔ 0 ≤ (e y).1) →
        (∀ x ∈ E.source, x ∈ Bd ↔ E x ∈ Bd₁) →
        (∀ y ∈ e.source, y ∈ Bd₁ ↔ (e y).1 = 0) →
        ∀ x ∈ N, h x ∈ Bd → x ∈ Bd) ∧
      Disjoint (h '' (D '' P)) (D '' Q) ∧
      IsPLOn 2 3 (P.piecewise (h ∘ D) D) D.domain ∧
      IsLocallyInjective (D.domain.domRestrict (P.piecewise (h ∘ D) D)) ∧
      (∀ y, (D.domain ∩ P.piecewise (h ∘ D) D ⁻¹' {y}).encard ≤ 2) ∧
      (∀ y ∉ U, P.piecewise (h ∘ D) D ⁻¹' {y} = D ⁻¹' {y}) ∧
      doublePointSet (P.piecewise (h ∘ D) D) D.domain =
        doublePointSet D D.domain \ hD.singularSet.branchCarrier cb ∧
      K.space = D.domain ∧
      simplicialComplexity K (P.piecewise (h ∘ D) D) < simplicialComplexity K D := by
  obtain ⟨U, h, K, hKfinite, hUopen, hSU, hUW, hhpl, hhinj, hhfix, hhmap, hhN, hhrefl, hdisj,
    hgpl, hgloc, hgcard, hgfib, hgdouble, hKspace, hlt⟩ :=
    hD.exists_separated_cell_simplicialComplexity_lt_along_boundary_branch cb E hE e he hei
      hesrc hd hcR hbd hsupp hAt hBt hSK hW hA hB hAB hdom hPpoly hPcpoly hinjP hinjQ hPcQ
      hseam hclean
  exact ⟨U, h, K, hKfinite, hD.exists_boundary_four_arc_word_of_boundaryBranch hc,
    hUopen, hSU, hUW, hhpl, hhinj, hhfix, hhmap, hhN, hhrefl, hdisj, hgpl, hgloc, hgcard,
    hgfib, hgdouble, hKspace, hlt⟩

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
