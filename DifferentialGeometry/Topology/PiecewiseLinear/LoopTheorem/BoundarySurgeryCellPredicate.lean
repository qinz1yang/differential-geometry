/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedCellPredicate

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

def IsBoundarySurgeryCell (hD : NormalSingularCellData D BdM B) (c : hD.singularSet.Branch)
    (Gd : SingularTwoCell M) : Prop :=
  ∃ A C U V : Set (EuclideanSpace ℝ (Fin 2)),
  ∃ p q r s : EuclideanSpace ℝ (Fin 2),
  ∃ g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
  ∃ pullback : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
    IsPLBall 1 A ∧ IsPLBall 1 C ∧ Disjoint A C ∧
    hD.branchPreimage c = A ∪ C ∧
    IsPLBall 1 U ∧ IsPLBall 1 V ∧ Disjoint U V ∧
    IsPLHomeomorphOn g A C ∧
    p ∈ A ∧ q ∈ A ∧ r ∈ C ∧ s ∈ C ∧
    EqOn D (D ∘ g) A ∧
    ((g p = r ∧ g q = s) ∨ (g p = s ∧ g q = r)) ∧
    MapsTo pullback Gd.domain D.domain ∧
    InjOn pullback Gd.domain ∧
    EqOn (D ∘ pullback) Gd Gd.domain ∧
    Disjoint (pullback '' Gd.domain) C ∧
    Gd '' Gd.domain ⊆ D '' D.domain ∧
    Set.range Gd.boundary = D '' (U ∪ V) ∧
    Gd '' Gd.domain ∩ BdM = Set.range Gd.boundary ∧
    Set.range Gd.boundary ⊆ B ∧ Gd '' Gd.domain ∩ BdM ⊆ B ∧
    (∀ x ∈ Gd.domain, ∃ W ∈ 𝓝[Gd.domain] x, Set.InjOn Gd W) ∧
    (∀ y, (Gd.domain ∩ Gd ⁻¹' {y}).encard ≤ 2) ∧
    doublePointSet Gd Gd.domain ⊆ doublePointSet D D.domain ∧
    Disjoint (doublePointSet Gd Gd.domain) (hD.singularSet.branchCarrier c) ∧
    Nonempty (NormalSingularSetTriangulation Gd BdM) ∧
    Nonempty (NormalSingularCellData Gd BdM B) ∧
    ∃ (x y : M) (σ : Path x y) (ω : Path y x)
        (e : loopCircle ≃ₜ frontier Gd.domain),
      Set.range σ = D '' U ∧ Set.range ω = D '' V ∧
        (∀ θ, Gd (e θ) = pathToCircle (σ.trans ω) θ) ∧
        ∃ R T : Set (EuclideanSpace ℝ (Fin 2)),
        ∃ (a' b' : frontier Gd.domain) (ρ : Path a' b') (κ : Path b' a'),
          frontier Gd.domain = R ∪ T ∧
          Gd '' R = D '' U ∧ Gd '' T = D '' V ∧
          Function.Injective ρ ∧ Function.Injective κ ∧
          Set.range (fun t => ((ρ t : frontier Gd.domain) :
            EuclideanSpace ℝ (Fin 2))) = R ∧
          Set.range (fun t => ((κ t : frontier Gd.domain) :
            EuclideanSpace ℝ (Fin 2))) = T ∧
          (∀ θ, e θ = pathToCircle (ρ.trans κ) θ) ∧
          ∃ U₁ U₂ U₃ : Set (EuclideanSpace ℝ (Fin 2)),
            IsClosed U₁ ∧ IsClosed U₂ ∧ IsClosed U₃ ∧
            U₁ ∪ U₂ ∪ U₃ = D.domain ∧ U₁ ∩ U₂ = A ∧ U₂ ∩ U₃ = C ∧
            D.domain \ U₂ ⊆ pullback '' Gd.domain ∧
            Disjoint (pullback '' Gd.domain) (U₂ \ A)

theorem exists_isBoundarySurgeryCell_of_boundaryBranch [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    (hc : hD.singularSet.IsBoundaryBranch c) :
    ∃ Gd : SingularTwoCell M, hD.IsBoundarySurgeryCell c Gd := by
  obtain ⟨A, C, U, V, p, q, r, s, g, Gd, pullback, hrest⟩ :=
    hD.exists_boundary_surgery_cell_of_boundaryBranch hc
  exact ⟨Gd, A, C, U, V, p, q, r, s, g, pullback, hrest⟩

theorem nonempty_normalSingularCellData_of_isBoundarySurgeryCell
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd) :
    Nonempty (NormalSingularCellData Gd BdM B) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hN, -⟩ := hGd
  exact hN

theorem image_subset_of_isBoundarySurgeryCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {Gd : SingularTwoCell M}
    (hGd : hD.IsBoundarySurgeryCell c Gd) : ⇑Gd '' Gd.domain ⊆ ⇑D '' D.domain := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, him, -⟩ := hGd
  exact him

theorem doublePointSet_subset_of_isBoundarySurgeryCell (hD : NormalSingularCellData D BdM B)
    {c : hD.singularSet.Branch} {Gd : SingularTwoCell M}
    (hGd : hD.IsBoundarySurgeryCell c Gd) :
    doublePointSet Gd Gd.domain ⊆ doublePointSet D D.domain := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hsub, -⟩ := hGd
  exact hsub

theorem disjoint_doublePointSet_branchCarrier_of_isBoundarySurgeryCell
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd) :
    Disjoint (doublePointSet Gd Gd.domain) (hD.singularSet.branchCarrier c) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, hmissc, -⟩ := hGd
  exact hmissc

theorem not_isBoundarySurgeryCell_self (hD : NormalSingularCellData D BdM B)
    (c : hD.singularSet.Branch) : ¬ hD.IsBoundarySurgeryCell c D := by
  intro hGd
  obtain ⟨z, hz⟩ := (hD.singularSet.branchCarrier_isConnected c).nonempty
  exact Set.disjoint_right.mp
    (hD.disjoint_doublePointSet_branchCarrier_of_isBoundarySurgeryCell hGd) hz
    (hD.singularSet.branchCarrier_subset_doublePointSet c hz)

theorem exists_injective_boundaryArcs_of_isBoundarySurgeryCell
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd) :
    ∃ R T : Set (EuclideanSpace ℝ (Fin 2)),
    ∃ (x y : M) (σ : Path x y) (ω : Path y x) (e : loopCircle ≃ₜ frontier Gd.domain),
    ∃ (a' b' : frontier Gd.domain) (ρ : Path a' b') (κ : Path b' a'),
      frontier Gd.domain = R ∪ T ∧
      Set.range σ = ⇑Gd '' R ∧ Set.range ω = ⇑Gd '' T ∧
      (∀ θ, Gd (e θ) = pathToCircle (σ.trans ω) θ) ∧
      Function.Injective ρ ∧ Function.Injective κ ∧
      Set.range (fun t => ((ρ t : frontier Gd.domain) :
        EuclideanSpace ℝ (Fin 2))) = R ∧
      Set.range (fun t => ((κ t : frontier Gd.domain) :
        EuclideanSpace ℝ (Fin 2))) = T ∧
      (∀ θ, e θ = pathToCircle (ρ.trans κ) θ) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -,
    x, y, σ, ω, e, hσ, hω, hparam, R, T, a', b', ρ, κ,
    hfront, hRim, hTim, hρinj, hκinj, hρrange, hκrange, heparam, -⟩ := hGd
  exact ⟨R, T, x, y, σ, ω, e, a', b', ρ, κ, hfront, hσ.trans hRim.symm, hω.trans hTim.symm,
    hparam, hρinj, hκinj, hρrange, hκrange, heparam⟩

theorem exists_branchOrigin_of_isBoundarySurgeryCell [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd)
    (hG : NormalSingularCellData Gd BdM B) :
    ∃ origin : hG.singularSet.Branch → hD.singularSet.Branch,
      Function.Injective origin ∧ ∀ b, origin b ≠ c := by
  obtain ⟨_, _, _, _, _, _, _, _, _, pb,
    -, -, -, hpre, -, -, -, -, -, -,
    -, -, -, -, hmaps, hinjp, heqp, -, -, -,
    -, -, -, -, -, hsub, hmissc, -, -,
    _, _, _, _, _, -, -, -, _, _, _, _, _, _,
    -, -, -, -, -, -, -, -,
    U₁, U₂, U₃, h₁, h₂, h₃, hunion, h₁₂, h₂₃, hout, hin⟩ := hGd
  have hPD : pb '' Gd.domain ⊆ D.domain := by
    rintro _ ⟨x, hx, rfl⟩
    exact hmaps hx
  have hdps : doublePointSet Gd Gd.domain = doublePointSet D (pb '' Gd.domain) :=
    doublePointSet_eq_image_of_pullback hinjp heqp
  have hwhole : ∀ a : hD.singularSet.Branch,
      hD.singularSet.branchCarrier a ⊆ doublePointSet Gd Gd.domain ∨
        Disjoint (hD.singularSet.branchCarrier a) (doublePointSet Gd Gd.domain) := by
    intro a
    by_cases hac : a = c
    · refine Or.inr ?_
      rw [hac]
      exact hmissc.symm
    · rw [hdps]
      exact hD.branchCarrier_subset_or_disjoint_doublePointSet h₁ h₂ h₃ hpre hunion h₁₂ h₂₃
        hPD hout hin hac
  exact ⟨hD.singularSet.branchOrigin hG.singularSet hsub,
    hD.singularSet.injective_branchOrigin_of_subset_or_disjoint hG.singularSet hsub hwhole,
    hD.singularSet.branchOrigin_ne hG.singularSet hsub hmissc⟩

theorem exists_descendingSurgery_of_crossSeamTube_reversing_of_isBoundarySurgeryCell
    [T2Space M] {U : Set M} {hD : NormalSingularCellData D BdM B}
    {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) {G cell : SingularTwoCell M}
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hdomain : cell.domain = G.domain)
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hreglued : EqOn G (T.chart ∘ crossSeamInclude ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hG : hD.IsCrossRegluedCell c G)
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder),
      x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM)
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ υ : Path a b} {τ φ : Path b a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (hρ : IsEmbedding ρ) (hrange : B ⊆ Set.range ρ)
    (Wdirect : BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ.symm)))
    (Wraw : BoundaryWordWitness G ρ (pathToCircle (σ.trans (φ.trans (υ.trans τ)))))
    {Ω₁ Ω₂ : Set loopCircle} (hΩ₁ : IsClosed Ω₁) (hΩ₂ : IsClosed Ω₂)
    (hcover : Ω₁ ∪ Ω₂ = univ)
    (hcocont : ContinuousOn (fun θ => coord ↑(Wraw.param θ)) Ω₁)
    (hΩ₁tube : ∀ θ ∈ Ω₁, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder)
    (hΩ₁max : ∀ θ, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder → θ ∈ Ω₁)
    (hlateral : ∀ θ ∈ Ω₁ ∩ Ω₂, (coord ↑(Wraw.param θ)).2.1 ∈ spliceSquareBoundary) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  obtain ⟨hnormal⟩ := hD.nonempty_normalSingularCellData_of_isBoundarySurgeryCell hGd
  obtain ⟨origin, hinj, hmiss⟩ := hD.exists_branchOrigin_of_isBoundarySurgeryCell hGd hnormal
  exact exists_descendingSurgery_of_crossSeamTube_reversing_of_isCrossRegluedCell T hdomain
    hcoord hreglued hresolved hcompl hG hendDisks hends htubeBdM hBdM hnormal origin hinj
    hmiss σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN hρ hrange Wdirect Wraw hΩ₁ hΩ₂ hcover
    hcocont hΩ₁tube hΩ₁max hlateral

theorem exists_descendingSurgery_of_crossSeamTube_preserving_of_isBoundarySurgeryCell
    [T2Space M] {U : Set M} {hD : NormalSingularCellData D BdM B}
    {c : hD.singularSet.Branch}
    (T : CrossSeamTubeData hD c U) {G cell : SingularTwoCell M}
    {coord : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)}
    (hdomain : cell.domain = G.domain)
    (hcoord : BijOn coord (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)) bentSource)
    (hreglued : EqOn G (T.chart ∘ crossSeamInclude ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hresolved : EqOn cell (T.chart ∘ crossSeamResolve ∘ coord)
      (G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hcompl : EqOn cell G (G.domain \ ⇑G ⁻¹' (T.chart '' spliceCylinder)))
    (hG : hD.IsCrossRegluedCell c G)
    (hendDisks : T.chart '' spliceEndDisks ⊆ B)
    (hends : ∀ x ∈ G.domain ∩ ⇑G ⁻¹' (T.chart '' spliceCylinder),
      x ∈ frontier G.domain ↔ (coord x).2.2 = 0 ∨ (coord x).2.2 = 1)
    (htubeBdM : T.chart '' spliceCylinder ∩ BdM ⊆ T.chart '' spliceEndDisks)
    (hBdM : B ⊆ BdM)
    {Gd : SingularTwoCell M} (hGd : hD.IsBoundarySurgeryCell c Gd)
    {Q : Type w} [TopologicalSpace Q] {p' q' u' v' : Q}
    (σ₀ : Path p' q') (τ₀ : Path q' u') (υ₀ : Path u' v') (φ₀ : Path v' p')
    (ev : loopCircle → Q)
    (hev : ∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ)
    {X : Type v} [TopologicalSpace X] [PathConnectedSpace X] {f : Q → X} {x a b : X}
    {σ : Path a b} {τ : Path b b} {υ : Path b a} {φ : Path a a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hφ : ∀ t, φ t = f (φ₀ t)) (γ : freeLoop X) (hγ : ∀ θ, γ θ = f (ev θ))
    {N : Subgroup (FundamentalGroup X x)} [N.Normal] (hγN : ¬loopClassMeets γ x N)
    {ρ : X → M} (hρ : IsEmbedding ρ) (hrange : B ⊆ Set.range ρ)
    (Wdirect : BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ)))
    (Wraw : BoundaryWordWitness G ρ
      (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm)))))
    {Ω₁ Ω₂ : Set loopCircle} (hΩ₁ : IsClosed Ω₁) (hΩ₂ : IsClosed Ω₂)
    (hcover : Ω₁ ∪ Ω₂ = univ)
    (hcocont : ContinuousOn (fun θ => coord ↑(Wraw.param θ)) Ω₁)
    (hΩ₁tube : ∀ θ ∈ Ω₁, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder)
    (hΩ₁max : ∀ θ, ⇑G ↑(Wraw.param θ) ∈ T.chart '' spliceCylinder → θ ∈ Ω₁)
    (hlateral : ∀ θ ∈ Ω₁ ∩ Ω₂, (coord ↑(Wraw.param θ)).2.1 ∈ spliceSquareBoundary) :
    ∃ (S : hD.DescendingSurgery) (e : loopCircle ≃ₜ frontier S.cell.domain) (δ : freeLoop X),
      (∀ θ, ρ (δ θ) = S.cell (e θ)) ∧ ¬loopClassMeets δ x N := by
  obtain ⟨hnormal⟩ := hD.nonempty_normalSingularCellData_of_isBoundarySurgeryCell hGd
  obtain ⟨origin, hinj, hmiss⟩ := hD.exists_branchOrigin_of_isBoundarySurgeryCell hGd hnormal
  exact exists_descendingSurgery_of_crossSeamTube_preserving_of_isCrossRegluedCell T hdomain
    hcoord hreglued hresolved hcompl hG hendDisks hends htubeBdM hBdM hnormal origin hinj
    hmiss σ₀ τ₀ υ₀ φ₀ ev hev hσ hτ hυ hφ γ hγ hγN hρ hrange Wdirect Wraw hΩ₁ hΩ₂ hcover
    hcocont hΩ₁tube hΩ₁max hlateral

end NormalSingularCellData

end DifferentialGeometry.Topology.PiecewiseLinear
