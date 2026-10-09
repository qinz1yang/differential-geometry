/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundarySurgeryCellPredicate
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryWordWitnessOfCell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

namespace BoundaryWordWitness

section Reverse

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {X : Type v} [TopologicalSpace X] {G : SingularTwoCell M} {ρ : X → M}

def ofReversedWord {w : freeLoop X} (W : BoundaryWordWitness G ρ w) :
    BoundaryWordWitness G ρ (w.comp ⟨fun θ => -θ, continuous_neg⟩) where
  param := (Homeomorph.neg loopCircle).trans W.param
  loop := W.loop.comp ⟨fun θ => -θ, continuous_neg⟩
  realizes := fun θ => W.realizes (-θ)
  homotopic := W.homotopic.comp (ContinuousMap.Homotopic.refl _)

theorem comp_neg_comp_neg (w : freeLoop X) :
    (w.comp ⟨fun θ => -θ, continuous_neg⟩).comp
        (⟨fun θ => -θ, continuous_neg⟩ : C(loopCircle, loopCircle)) = w :=
  ContinuousMap.ext fun θ => by
    change w (- -θ) = w θ
    rw [neg_neg]

theorem exists_of_twoArcMatch_of_endpoints [T2Space M] (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {a b : X} {P : Path a b} {Q : Path b a}
    (hP : Function.Injective ⇑P) (hQ : Function.Injective ⇑Q) {x y : M}
    {α : Path x y} {ω : Path y x}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : Set.range ⇑α = ρ '' Set.range ⇑P) (hω : Set.range ⇑ω = ρ '' Set.range ⇑Q)
    (hend : (x = ρ a ∧ y = ρ b) ∨ (x = ρ b ∧ y = ρ a)) :
    Nonempty (BoundaryWordWitness G ρ (pathToCircle (P.trans Q))) := by
  rcases hend with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · subst hx
    subst hy
    exact exists_of_twoArcMatch hρ e hP hQ hparam hα hω
  · subst hx
    subst hy
    have hPsymm : Function.Injective ⇑P.symm := by
      intro s t hst
      have h : P (unitInterval.symm s) = P (unitInterval.symm t) := hst
      exact unitInterval.symm_bijective.injective (hP h)
    have hQsymm : Function.Injective ⇑Q.symm := by
      intro s t hst
      have h : Q (unitInterval.symm s) = Q (unitInterval.symm t) := hst
      exact unitInterval.symm_bijective.injective (hQ h)
    obtain ⟨W⟩ := exists_of_twoArcMatch hρ e hPsymm hQsymm hparam
      (by rwa [Path.symm_range]) (by rwa [Path.symm_range])
    have hword : pathToCircle (P.symm.trans Q.symm) =
        (pathToCircle (Q.trans P)).comp ⟨fun θ => -θ, continuous_neg⟩ := by
      rw [← Path.trans_symm Q P, pathToCircle_symm]
    rw [hword] at W
    have hback := W.ofReversedWord
    rw [comp_neg_comp_neg] at hback
    exact ⟨hback.ofHomotopicWord (pathToCircle_trans_homotopic_comm Q P)⟩

theorem exists_of_twoArcMatch_reversing_of_endpoints [T2Space M] (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {a b : X} {σ υ : Path a b}
    (hσ : Function.Injective ⇑σ) (hυ : Function.Injective ⇑υ) {x y : M}
    {α : Path x y} {ω : Path y x}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : Set.range ⇑α = ρ '' Set.range ⇑σ) (hω : Set.range ⇑ω = ρ '' Set.range ⇑υ)
    (hend : (x = ρ a ∧ y = ρ b) ∨ (x = ρ b ∧ y = ρ a)) :
    Nonempty (BoundaryWordWitness G ρ (pathToCircle (σ.trans υ.symm))) := by
  refine exists_of_twoArcMatch_of_endpoints hρ e hσ ?_ hparam hα ?_ hend
  · intro s t hst
    have h : υ (unitInterval.symm s) = υ (unitInterval.symm t) := hst
    exact unitInterval.symm_bijective.injective (hυ h)
  · rwa [Path.symm_range]

end Reverse

end BoundaryWordWitness

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_boundaryCandidates_of_cut [T2Space M] (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {A C : Set (EuclideanSpace ℝ (Fin 2))}
    {p q r s : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {D₁ D₂ D₃ : SingularTwoCell M}
    (hcut : hD.IsBoundaryBranchCut c A C p q r s g D₁ D₂ D₃) :
    ∃ (A₂ A₄ : Set (EuclideanSpace ℝ (Fin 2))) (u v : EuclideanSpace ℝ (Fin 2))
        (p' q' u' v' : frontier D.domain) (σ₀ : Path p' q') (τ₀ : Path q' u')
        (υ₀ : Path u' v') (φ₀ : Path v' p') (ev : loopCircle ≃ₜ frontier D.domain)
        (Gd G : SingularTwoCell M) (xd yd : M) (αd : Path xd yd) (ωd : Path yd xd)
        (ed : loopCircle ≃ₜ frontier Gd.domain) (xc yc : M) (αc : Path xc yc)
        (ωc : Path yc xc) (ec : loopCircle ≃ₜ frontier G.domain),
      hD.IsBoundarySurgeryCell c Gd ∧ hD.IsCrossRegluedCell c G ∧
      (p' : EuclideanSpace ℝ (Fin 2)) = p ∧ (q' : EuclideanSpace ℝ (Fin 2)) = q ∧
      (u' : EuclideanSpace ℝ (Fin 2)) = u ∧ (v' : EuclideanSpace ℝ (Fin 2)) = v ∧
      Set.range (fun t => ((σ₀ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) =
        D₁.domain ∩ frontier D.domain ∧
      Set.range (fun t => ((τ₀ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₂ ∧
      Set.range (fun t => ((υ₀ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) =
        D₃.domain ∩ frontier D.domain ∧
      Set.range (fun t => ((φ₀ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) = A₄ ∧
      frontier D.domain = (D₁.domain ∩ frontier D.domain) ∪
        (A₂ ∪ ((D₃.domain ∩ frontier D.domain) ∪ A₄)) ∧
      (∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ) ∧
      Function.Injective ⇑σ₀ ∧ Function.Injective ⇑τ₀ ∧
      Function.Injective ⇑υ₀ ∧ Function.Injective ⇑φ₀ ∧
      ((D u = D p ∧ D v = D q) ∨ (D u = D q ∧ D v = D p)) ∧
      Set.range ⇑αd = ⇑D '' (D₁.domain ∩ frontier D.domain) ∧
      Set.range ⇑ωd = ⇑D '' (D₃.domain ∩ frontier D.domain) ∧
      (∀ θ, Gd (ed θ) = pathToCircle (αd.trans ωd) θ) ∧
      ((xd = D p ∧ yd = D q) ∨ (xd = D q ∧ yd = D p)) ∧
      Set.range ⇑αc = ⇑D '' (A₂ ∪ ((D₁.domain ∩ frontier D.domain) ∪ A₄)) ∧
      Set.range ⇑ωc = ⇑D '' (D₃.domain ∩ frontier D.domain) ∧
      (∀ θ, G (ec θ) = pathToCircle (αc.trans ωc) θ) ∧
      ((xc = D p ∧ yc = D q) ∨ (xc = D q ∧ yc = D p)) := by
  obtain ⟨A₂, A₄, u, v, p', q', u', v', σ₀, τ₀, υ₀, φ₀, ev,
    ⟨-, -, -, -, -, -, hp', hq', hu', hv', hr₁, hr₂, hr₃, hr₄, hJ, hev, hpair⟩,
    hσinj, hτinj, hυinj, hφinj, -, -, -, -, hkey⟩ :=
    hD.exists_boundary_four_arc_word_of_cut hcut
  obtain ⟨Gd, pullback, ⟨hA, hC, hAC, hcover, hU, hV, hUV, hg, hpA, hqA, hrC, hsC,
    hcompat, horientation, hmaps, hinj, hfactor, hmissC, hGdimage, hrange,
    himageBoundary, hrangeB, hinterB, hlocal, hfiber, hdouble, hremove,
    htriangulated, hnormal, xd', yd', αd', ωd', ed', hαd', hωd', hparamd',
    R₀, T₀, a₀, b₀, ρ₀, κ₀, hfrontGd, hGdR, hGdT, hρ₀inj, hκ₀inj, hρ₀range, hκ₀range,
    he₀, hclosed₁, hclosed₂, hclosed₃, hdomains, hinter₁₂, hinter₂₃, hkept, hband⟩,
    xd, yd, αd, ωd, ed, hαd, hωd, hparamd, hendd⟩ :=
    hD.exists_boundary_surgery_cell_of_cut hcut
  obtain ⟨P, Q, P', Q', A', R, T, a, b, f₁, f₂, h, f₃, H, G, hcbody,
    xc, yc, αc, ωc, ec, hαc, hωc, hparamc, hendc⟩ :=
    hD.exists_cross_reglued_cell_of_cut hcut
  refine ⟨A₂, A₄, u, v, p', q', u', v', σ₀, τ₀, υ₀, φ₀, ev, Gd, G,
    xd, yd, αd, ωd, ed, xc, yc, αc, ωc, ec, ?_, ?_, hp', hq', hu', hv',
    hr₁, hr₂, hr₃, hr₄, hJ, hev, hσinj, hτinj, hυinj, hφinj, hpair,
    hαd, hωd, hparamd, hendd, ?_, hωc, hparamc, hendc⟩
  · exact ⟨A, C, D₁.domain ∩ frontier D.domain, D₃.domain ∩ frontier D.domain,
      p, q, r, s, g, pullback, hA, hC, hAC, hcover, hU, hV, hUV, hg, hpA, hqA, hrC, hsC,
      hcompat, horientation, hmaps, hinj, hfactor, hmissC, hGdimage, hrange,
      himageBoundary, hrangeB, hinterB, hlocal, hfiber, hdouble, hremove,
      htriangulated, hnormal, xd', yd', αd', ωd', ed', hαd', hωd', hparamd',
      R₀, T₀, a₀, b₀, ρ₀, κ₀, hfrontGd, hGdR, hGdT, hρ₀inj, hκ₀inj, hρ₀range, hκ₀range,
      he₀, D₁.domain, D₂.domain, D₃.domain, hclosed₁, hclosed₂, hclosed₃, hdomains,
      hinter₁₂, hinter₂₃, hkept, hband⟩
  · exact ⟨A, C, D₁.domain, D₂.domain, D₃.domain, P, Q, P', Q', A', R, T,
      p, q, r, s, a, b, g, f₁, f₂, h, f₃, H, hcbody⟩
  · rw [hαc, hkey]

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
