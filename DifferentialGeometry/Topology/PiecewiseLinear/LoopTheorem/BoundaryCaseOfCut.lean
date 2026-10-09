/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryCandidatesOfCut
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryCaseFromSource
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossSeamResolvedCell
import Mathlib.Topology.Subpath

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v

namespace BoundaryWordWitness

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {X : Type v} [TopologicalSpace X] {G : SingularTwoCell M} {ρ : X → M}

theorem exists_param_of_twoArcMatch [T2Space M] (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {a b : X} {P : Path a b} {Q : Path b a}
    (hP : Function.Injective ⇑P) (hQ : Function.Injective ⇑Q)
    {α : Path (ρ a) (ρ b)} {ω : Path (ρ b) (ρ a)}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : Set.range ⇑α = ρ '' Set.range ⇑P)
    (hω : Set.range ⇑ω = ρ '' Set.range ⇑Q) :
    ∃ W : BoundaryWordWitness G ρ (pathToCircle (P.trans Q)), W.param = e := by
  have : T2Space X := hρ.t2Space
  have hαmem : ∀ t, α t ∈ Set.range ρ := by
    intro t
    have ht : α t ∈ Set.range ⇑α := Set.mem_range_self t
    rw [hα] at ht
    obtain ⟨y, -, hy⟩ := ht
    exact ⟨y, hy⟩
  have hωmem : ∀ t, ω t ∈ Set.range ρ := by
    intro t
    have ht : ω t ∈ Set.range ⇑ω := Set.mem_range_self t
    rw [hω] at ht
    obtain ⟨y, -, hy⟩ := ht
    exact ⟨y, hy⟩
  have hPhom : (liftPath hρ α hαmem).Homotopic P :=
    Path.Homotopic.of_injective_of_range_eq hP (range_liftPath hρ α hαmem hα)
  have hQhom : (liftPath hρ ω hωmem).Homotopic Q :=
    Path.Homotopic.of_injective_of_range_eq hQ (range_liftPath hρ ω hωmem hω)
  refine ⟨{ param := e
            loop := pathToCircle ((liftPath hρ α hαmem).trans (liftPath hρ ω hωmem))
            realizes := fun θ => ?_
            homotopic := pathToCircle_homotopic (hPhom.hcomp hQhom) }, rfl⟩
  rw [hparam θ]
  exact (pathToCircle_eq_of_forall ((liftPath hρ α hαmem).trans (liftPath hρ ω hωmem))
    (α.trans ω) (trans_apply_eq_map (fun t => (liftPath_apply hρ α hαmem t).symm)
      (fun t => (liftPath_apply hρ ω hωmem t).symm)) θ).symm

theorem exists_param_of_twoArcMatch_of_endpoints [T2Space M] (hρ : IsEmbedding ρ)
    (e : loopCircle ≃ₜ frontier G.domain) {a b : X} {P : Path a b} {Q : Path b a}
    (hP : Function.Injective ⇑P) (hQ : Function.Injective ⇑Q) {x y : M}
    {α : Path x y} {ω : Path y x}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : Set.range ⇑α = ρ '' Set.range ⇑P)
    (hω : Set.range ⇑ω = ρ '' Set.range ⇑Q)
    (hend : (x = ρ a ∧ y = ρ b) ∨ (x = ρ b ∧ y = ρ a)) :
    ∃ W : BoundaryWordWitness G ρ (pathToCircle (P.trans Q)),
      W.param = e ∨ W.param = (Homeomorph.neg loopCircle).trans e := by
  rcases hend with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · subst hx
    subst hy
    obtain ⟨W, hW⟩ := exists_param_of_twoArcMatch hρ e hP hQ hparam hα hω
    exact ⟨W, Or.inl hW⟩
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
    obtain ⟨W, hW⟩ := exists_param_of_twoArcMatch hρ e hPsymm hQsymm hparam
      (by rwa [Path.symm_range]) (by rwa [Path.symm_range])
    have hword : pathToCircle (P.symm.trans Q.symm) =
        (pathToCircle (Q.trans P)).comp ⟨fun θ => -θ, continuous_neg⟩ := by
      rw [← Path.trans_symm Q P, pathToCircle_symm]
    have hfirst : (pathToCircle (P.symm.trans Q.symm)).Homotopic
        ((pathToCircle (Q.trans P)).comp ⟨fun θ => -θ, continuous_neg⟩) :=
      hword ▸ ContinuousMap.Homotopic.refl _
    have hsecond : (((pathToCircle (Q.trans P)).comp
        (⟨fun θ => -θ, continuous_neg⟩ : C(loopCircle, loopCircle))).comp
        (⟨fun θ => -θ, continuous_neg⟩ : C(loopCircle, loopCircle))).Homotopic
        (pathToCircle (P.trans Q)) := by
      rw [comp_neg_comp_neg]
      exact pathToCircle_trans_homotopic_comm Q P
    refine ⟨((W.ofHomotopicWord hfirst).ofReversedWord).ofHomotopicWord hsecond, Or.inr ?_⟩
    exact congrArg (fun p : loopCircle ≃ₜ frontier G.domain =>
      (Homeomorph.neg loopCircle).trans p) hW

end BoundaryWordWitness

section Cover

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem boundaryCover_of_neg {G : SingularTwoCell M} {K : Set M}
    {co : EuclideanSpace ℝ (Fin 2) → Bool × ((ℝ × ℝ) × ℝ)} {S : Set (ℝ × ℝ)}
    {e e' : loopCircle ≃ₜ frontier G.domain} (he : ∀ θ, e' θ = e (-θ))
    {Ω₁ Ω₂ : Set loopCircle} (hΩ₁ : IsClosed Ω₁) (hΩ₂ : IsClosed Ω₂)
    (hcover : Ω₁ ∪ Ω₂ = univ)
    (hcocont : ContinuousOn (fun θ => co ↑(e θ)) Ω₁)
    (hΩ₁tube : ∀ θ ∈ Ω₁, ⇑G ↑(e θ) ∈ K)
    (hΩ₁max : ∀ θ, ⇑G ↑(e θ) ∈ K → θ ∈ Ω₁)
    (hlateral : ∀ θ ∈ Ω₁ ∩ Ω₂, (co ↑(e θ)).2.1 ∈ S) :
    IsClosed ((fun t : loopCircle => -t) ⁻¹' Ω₁) ∧
      IsClosed ((fun t : loopCircle => -t) ⁻¹' Ω₂) ∧
      (fun t : loopCircle => -t) ⁻¹' Ω₁ ∪ (fun t : loopCircle => -t) ⁻¹' Ω₂ = univ ∧
      ContinuousOn (fun θ => co ↑(e' θ)) ((fun t : loopCircle => -t) ⁻¹' Ω₁) ∧
      (∀ θ ∈ (fun t : loopCircle => -t) ⁻¹' Ω₁, ⇑G ↑(e' θ) ∈ K) ∧
      (∀ θ, ⇑G ↑(e' θ) ∈ K → θ ∈ (fun t : loopCircle => -t) ⁻¹' Ω₁) ∧
      (∀ θ ∈ (fun t : loopCircle => -t) ⁻¹' Ω₁ ∩ (fun t : loopCircle => -t) ⁻¹' Ω₂,
        (co ↑(e' θ)).2.1 ∈ S) := by
  refine ⟨hΩ₁.preimage continuous_neg, hΩ₂.preimage continuous_neg, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Set.preimage_union, hcover, Set.preimage_univ]
  · have hfun : (fun θ => co ↑(e' θ)) =
        (fun θ => co ↑(e θ)) ∘ (fun t : loopCircle => -t) :=
      funext fun θ => congrArg (fun z : frontier G.domain => co ↑z) (he θ)
    rw [hfun]
    exact hcocont.comp continuous_neg.continuousOn (Set.mapsTo_preimage _ _)
  · intro θ hθ
    rw [he θ]
    exact hΩ₁tube (-θ) hθ
  · intro θ hθ
    rw [he θ] at hθ
    exact hΩ₁max (-θ) hθ
  · intro θ hθ
    rw [he θ]
    exact hlateral (-θ) ⟨hθ.1, hθ.2⟩

end Cover

private theorem connected_image_in_left {Y : Type*} [TopologicalSpace Y]
    {S U V : Set Y} (hS : IsPreconnected S) (hU : IsClosed U) (hV : IsClosed V)
    (hcover : S ⊆ U ∪ V) (hd : Disjoint U V) (hSU : (S ∩ U).Nonempty) : S ⊆ U := by
  intro y hy
  by_contra hyU
  have hyV : y ∈ V := (hcover hy).resolve_left hyU
  obtain ⟨z, hzS, hzU, hzV⟩ := isPreconnected_closed_iff.mp hS U V hU hV hcover
    hSU ⟨y, hy, hyV⟩
  exact Set.disjoint_left.mp hd hzU hzV

private theorem homotopic_three_subpaths {Y : Type*} [TopologicalSpace Y]
    {a b c d : Y} (γ : Path a b) (t₁ t₂ : unitInterval)
    (hc : γ t₁ = c) (hd : γ t₂ = d) :
    γ.Homotopic (((γ.subpath 0 t₁).cast γ.source.symm hc.symm).trans
      (((γ.subpath t₁ t₂).cast hc.symm hd.symm).trans
        ((γ.subpath t₂ 1).cast hd.symm γ.target.symm))) := by
  have h₂ : ((γ.subpath t₁ t₂).trans (γ.subpath t₂ 1)).Homotopic
      (γ.subpath t₁ 1) := ⟨Path.Homotopy.subpathTransSubpath γ t₁ t₂ 1⟩
  have h₁ : ((γ.subpath 0 t₁).trans (γ.subpath t₁ 1)).Homotopic
      (γ.subpath 0 1) := ⟨Path.Homotopy.subpathTransSubpath γ 0 t₁ 1⟩
  have h := ((Path.Homotopic.refl (γ.subpath 0 t₁)).hcomp h₂).trans h₁
  have h' := h.pathCast γ.source.symm γ.target.symm
  rw [Path.subpath_zero_one] at h'
  exact h'.symm

namespace NormalSingularCellData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {BdM B : Set M}

theorem exists_boundary_case_data_of_cut [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {A C : Set (EuclideanSpace ℝ (Fin 2))} {p q r s : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {D₁ D₂ D₃ : SingularTwoCell M}
    (hcut : hD.IsBoundaryBranchCut c A C p q r s g D₁ D₂ D₃) :
    (∃ (A₂ A₄ : Set (EuclideanSpace ℝ (Fin 2)))
        (u v : EuclideanSpace ℝ (Fin 2))
        (p' q' u' v' : frontier D.domain)
        (σ₀ : Path p' q') (τ₀ : Path q' u')
        (υ₀ : Path u' v') (φ₀ : Path v' p')
        (ev : loopCircle ≃ₜ frontier D.domain),
      Function.Injective σ₀ ∧ Function.Injective τ₀ ∧
      Function.Injective υ₀ ∧ Function.Injective φ₀ ∧
      Set.range (fun t => ((σ₀ t : frontier D.domain) :
        EuclideanSpace ℝ (Fin 2))) = D₁.domain ∩ frontier D.domain ∧
      Set.range (fun t => ((τ₀ t : frontier D.domain) :
        EuclideanSpace ℝ (Fin 2))) = A₂ ∧
      Set.range (fun t => ((υ₀ t : frontier D.domain) :
        EuclideanSpace ℝ (Fin 2))) = D₃.domain ∩ frontier D.domain ∧
      Set.range (fun t => ((φ₀ t : frontier D.domain) :
        EuclideanSpace ℝ (Fin 2))) = A₄ ∧
      (∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ) ∧
      ((u = r ∧ v = s) ∨ (u = s ∧ v = r))) ∧
    (∃ (A₂ A₄ : Set (EuclideanSpace ℝ (Fin 2)))
        (H G : SingularTwoCell M)
        (P Q P' Q' R T : Set (EuclideanSpace ℝ (Fin 2)))
        (f₁ f₂ h f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
        (a b : EuclideanSpace ℝ (Fin 2))
        (ρ : ℝ → EuclideanSpace ℝ (Fin 2)) (t₁ t₂ : ℝ)
        (x y : M) (σ : Path x y) (ω : Path y x)
        (e : loopCircle ≃ₜ frontier G.domain)
        (a' b' : frontier G.domain) (ρG : Path a' b') (κG : Path b' a'),
      IsPLBall 2 P ∧ IsPLBall 2 Q ∧ H.domain = P ∪ Q ∧
      IsPLHomeomorphOn f₁ P D₁.domain ∧ IsPLHomeomorphOn f₂ Q D₂.domain ∧
      IsPLBall 2 P' ∧ IsPLBall 2 Q' ∧ G.domain = P' ∪ Q' ∧
      IsPLHomeomorphOn h P' H.domain ∧ IsPLHomeomorphOn f₃ Q' D₃.domain ∧
      EqOn G (H.toFun ∘ h) P' ∧ EqOn G (D.toFun ∘ f₃) Q' ∧
      Schoenflies.IsCutPair (frontier P') a b (P' ∩ Q') R ∧
      Schoenflies.IsCutPair (frontier Q') a b (P' ∩ Q') T ∧
      IsPLBall 1 R ∧ IsPLBall 1 T ∧ frontier G.domain = R ∪ T ∧
      ContinuousOn ρ (Set.Icc 0 1) ∧ Set.InjOn ρ (Set.Icc 0 1) ∧
      ρ '' Set.Icc 0 1 = R ∧
      ((ρ 0 = a ∧ ρ 1 = b) ∨ (ρ 0 = b ∧ ρ 1 = a)) ∧
      t₁ ∈ Set.Icc 0 1 ∧ t₂ ∈ Set.Icc 0 1 ∧ t₁ < t₂ ∧
      (∀ t ∈ Set.Icc 0 t₁, G (ρ t) = D (f₂ (h (ρ t)))) ∧
      (∀ t ∈ Set.Icc t₁ t₂, G (ρ t) = D (f₁ (h (ρ t)))) ∧
      (∀ t ∈ Set.Icc t₂ 1, G (ρ t) = D (f₂ (h (ρ t)))) ∧
      (∀ z ∈ T, G z = D (f₃ z)) ∧
      (∀ t ∈ Set.Icc 0 t₁,
        f₂ (h (ρ t)) ∈ D₂.domain ∩ frontier D.domain) ∧
      (∀ t ∈ Set.Icc t₁ t₂,
        f₁ (h (ρ t)) ∈ D₁.domain ∩ frontier D.domain) ∧
      (∀ t ∈ Set.Icc t₂ 1,
        f₂ (h (ρ t)) ∈ D₂.domain ∩ frontier D.domain) ∧
      (∀ t ∈ Set.Icc 0 t₁,
        f₂ (h (ρ t)) ∈ A₂ ∪ A₄) ∧
      (∀ t ∈ Set.Icc t₂ 1,
        f₂ (h (ρ t)) ∈ A₂ ∪ A₄) ∧
      f₂ (h (ρ t₁)) = g (f₁ (h (ρ t₁))) ∧
      f₂ (h (ρ t₂)) = g (f₁ (h (ρ t₂))) ∧
      Set.range σ = G '' R ∧ Set.range ω = G '' T ∧
      (∀ θ, G (e θ) = pathToCircle (σ.trans ω) θ) ∧
      Function.Injective ρG ∧ Function.Injective κG ∧
      Set.range (fun t => ((ρG t : frontier G.domain) :
        EuclideanSpace ℝ (Fin 2))) = R ∧
      Set.range (fun t => ((κG t : frontier G.domain) :
        EuclideanSpace ℝ (Fin 2))) = T ∧
      (∀ θ, e θ = pathToCircle (ρG.trans κG) θ)) ∧
    (∃ (Gd : SingularTwoCell M) (xd yd : M)
        (αd : Path xd yd) (ωd : Path yd xd)
        (ed : loopCircle ≃ₜ frontier Gd.domain),
      Set.range αd = D '' (D₁.domain ∩ frontier D.domain) ∧
      Set.range ωd = D '' (D₃.domain ∩ frontier D.domain) ∧
      (∀ θ, Gd (ed θ) = pathToCircle (αd.trans ωd) θ) ∧
      ((xd = D p ∧ yd = D q) ∨ (xd = D q ∧ yd = D p))) := by
  have hcutCopy := hcut
  obtain ⟨-, -, -, -, -, -, -, -, hdomainsCut, hinter₁₂Cut, -, -, -, -, -, -, -, -, -, -, -,
    hcut₁Cut, -⟩ := hcut
  obtain ⟨A₂, A₄, u, v, p', q', u', v', σ₀, τ₀, υ₀, φ₀, ev,
    ⟨-, -, -, -, -, -, hp', hq', hu', hv', hrσ, hrτ, hrυ, hrφ, -, hev, -⟩,
    hσinj, hτinj, hυinj, hφinj, hueq, -, -, -, hkey⟩ :=
    hD.exists_boundary_four_arc_word_of_cut hcutCopy
  obtain ⟨H, G, P, Q, P', Q', R, T, f₁, f₂, h, f₃, a, b, ρ, t₁, t₂,
    hP, hQ, hHdomain, hf₁, hf₂, hH₁, hH₂, hP', hQ', hGdomain, hh, hf₃,
    hGH, hG₃, hcutP', hcutQ', hR', hT', hfrontG, hha, hhb, hf₃a, hf₃b,
    hρc, hρi, hρimage, hρends, ht₁, ht₂, htlt, hρleft, hρmid, hρright, hT,
    hsourceLeft, hsourceMid, hsourceRight, hseam₁, hseam₂,
    x, y, σ, ω, e, hσrange, hωrange, hboundaryParam,
    a', b', ρG, κG, hρGinj, hκGinj, hρGrange, hκGrange, heparam⟩ :=
    exists_cross_reglued_source_segments_of_cut_with_source_data hD hcutCopy
  obtain ⟨Gd, pullback, ⟨hA, hC, hAC, hcover, hU, hV, hUV, hg, hpA, hqA, hrC, hsC,
    hcompat, horientation, hmaps, hinj, hfactor, hmissC, hGdimage, hrange,
    himageBoundary, hrangeB, hinterB, hlocal, hfiber, hdouble, hremove,
    htriangulated, hnormal, xd', yd', αd', ωd', ed', hαd', hωd', hparamd',
    R₀, T₀, a₀, b₀, ρ₀, κ₀, hfrontGd, hGdR, hGdT, hρ₀inj, hκ₀inj, hρ₀range, hκ₀range,
    he₀, hclosed₁, hclosed₂, hclosed₃, hdomains, hinter₁₂, hinter₂₃, hkept, hband⟩,
    xd, yd, αd, ωd, ed, hαd, hωd, hparamd, hendd⟩ :=
    hD.exists_boundary_surgery_cell_of_cut hcutCopy
  have houter : ∀ z ∈ D₂.domain ∩ frontier D.domain, z ∈ A₂ ∪ A₄ := by
    intro z hz
    have hz' : z ∈ A₂ ∪ ((D₁.domain ∩ frontier D.domain) ∪ A₄) := by
      rw [← hkey]
      exact ⟨Or.inr hz.1, hz.2⟩
    rcases hz' with hzA₂ | hzD₁ | hzA₄
    · exact Or.inl hzA₂
    · have hzA : z ∈ A := by
        rw [← hinter₁₂Cut]
        exact ⟨hzD₁.1, hz.1⟩
      have hzpq := hcut₁Cut.inter_eq.subset ⟨hzA, hzD₁⟩
      rcases hzpq with rfl | rfl
      · exact Or.inr (by
          rw [← hrφ]
          refine ⟨1, ?_⟩
          simp [hp', φ₀.target])
      · exact Or.inl (by
          rw [← hrτ]
          refine ⟨0, ?_⟩
          simp [hq', τ₀.source])
    · exact Or.inr hzA₄
  exact ⟨
    ⟨A₂, A₄, u, v, p', q', u', v', σ₀, τ₀, υ₀, φ₀, ev,
      hσinj, hτinj, hυinj, hφinj, hrσ, hrτ, hrυ, hrφ, hev, hueq⟩,
    ⟨A₂, A₄, H, G, P, Q, P', Q', R, T, f₁, f₂, h, f₃, a, b, ρ, t₁, t₂,
      x, y, σ, ω, e, a', b', ρG, κG,
      hP, hQ, hHdomain, hf₁, hf₂, hP', hQ', hGdomain, hh, hf₃,
      hGH, hG₃, hcutP', hcutQ', hR', hT', hfrontG,
      hρc, hρi, hρimage, hρends, ht₁, ht₂, htlt, hρleft, hρmid, hρright, hT,
      hsourceLeft, hsourceMid, hsourceRight,
      (fun t ht => houter _ (hsourceLeft t ht)),
      (fun t ht => houter _ (hsourceRight t ht)),
      hseam₁, hseam₂,
      hσrange, hωrange, hboundaryParam,
      hρGinj, hκGinj, hρGrange, hκGrange, heparam⟩,
    ⟨Gd, xd, yd, αd, ωd, ed, hαd, hωd, hparamd, hendd⟩⟩

theorem exists_boundaryWordWitness_direct_of_cut [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {A C : Set (EuclideanSpace ℝ (Fin 2))} {p q r s : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {D₁ D₂ D₃ : SingularTwoCell M}
    (hcut : hD.IsBoundaryBranchCut c A C p q r s g D₁ D₂ D₃)
    {X : Type v} [TopologicalSpace X] {ρ : X → M}
    (f : frontier D.domain → X) (hf : Continuous f)
    (hfρ : ∀ z : frontier D.domain, ρ (f z) = D z)
    {p' q' u' v' : frontier D.domain}
    (σ₀ : Path p' q') (υ₀ : Path u' v')
    (hp' : (p' : EuclideanSpace ℝ (Fin 2)) = p)
    (hq' : (q' : EuclideanSpace ℝ (Fin 2)) = q)
    (hu' : (u' : EuclideanSpace ℝ (Fin 2)) = g q)
    (hv' : (v' : EuclideanSpace ℝ (Fin 2)) = g p)
    (hσ₀ : Function.Injective σ₀) (hυ₀ : Function.Injective υ₀)
    (hrσ : Set.range (fun t => ((σ₀ t : frontier D.domain) :
      EuclideanSpace ℝ (Fin 2))) = D₁.domain ∩ frontier D.domain)
    (hrυ : Set.range (fun t => ((υ₀ t : frontier D.domain) :
      EuclideanSpace ℝ (Fin 2))) = D₃.domain ∩ frontier D.domain)
    {a b : X} {σ : Path a b} {υ : Path b a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t)) :
    ∃ Gd : SingularTwoCell M, hD.IsBoundarySurgeryCell c Gd ∧
      Nonempty (BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ))) := by
  obtain ⟨Gd, pullback, hbody, x, y, α, ω, e, -, -, hparam, -,
    a₁, b₁, ρ₁, κ₁, p₁, q₁, u₁, v₁, σ₁, υ₁,
    hp₁, hq₁, hu₁, hv₁, hrσ₁, hrυ₁, -, -, hα, hω, -, -, -⟩ :=
    hD.exists_boundary_surgery_cell_of_cut_with_source_paths hcut
  have hGd : hD.IsBoundarySurgeryCell c Gd := by
    obtain ⟨hA, hC, hAC, hcover, hU, hV, hUV, hg, hpA, hqA, hrC, hsC,
      hcompat, horientation, hmaps, hinj, hfactor, hmissC, hGdimage, hrange,
      himageBoundary, hrangeB, hinterB, hlocal, hfiber, hdouble, hremove,
      htriangulated, hnormal, xd', yd', αd', ωd', ed', hαd', hωd', hparamd',
      R₀, T₀, a₀, b₀, ρ₀, κ₀, hfrontGd, hGdR, hGdT, hρ₀inj, hκ₀inj,
      hρ₀range, hκ₀range, he₀, hclosed₁, hclosed₂, hclosed₃,
      hdomains, hinter₁₂, hinter₂₃, hkept, hband⟩ := hbody
    exact ⟨A, C, D₁.domain ∩ frontier D.domain, D₃.domain ∩ frontier D.domain,
      p, q, r, s, g, pullback, hA, hC, hAC, hcover, hU, hV, hUV, hg,
      hpA, hqA, hrC, hsC, hcompat, horientation, hmaps, hinj, hfactor, hmissC,
      hGdimage, hrange, himageBoundary, hrangeB, hinterB, hlocal, hfiber,
      hdouble, hremove, htriangulated, hnormal, xd', yd', αd', ωd', ed',
      hαd', hωd', hparamd', R₀, T₀, a₀, b₀, ρ₀, κ₀, hfrontGd, hGdR, hGdT,
      hρ₀inj, hκ₀inj, hρ₀range, hκ₀range, he₀, D₁.domain, D₂.domain, D₃.domain,
      hclosed₁, hclosed₂, hclosed₃, hdomains, hinter₁₂, hinter₂₃, hkept, hband⟩
  have hpp : p₁ = p' := Subtype.ext (hp₁.trans hp'.symm)
  have hqq : q₁ = q' := Subtype.ext (hq₁.trans hq'.symm)
  have huu : u₁ = u' := Subtype.ext (hu₁.trans hu'.symm)
  have hvv : v₁ = v' := Subtype.ext (hv₁.trans hv'.symm)
  subst p₁ q₁ u₁ v₁
  have ha : a = f p' := by simpa using hσ 0
  have hb : b = f q' := by simpa using hσ 1
  have hu : b = f u' := by simpa using hυ 0
  have hv : a = f v' := by simpa using hυ 1
  have hx : x = ρ a := by
    have hx' : x = D p' := by simpa using hα 0
    exact hx'.trans ((hfρ p').symm.trans (congrArg ρ ha.symm))
  have hy : y = ρ b := by
    have hy' : y = D q' := by simpa using hα 1
    exact hy'.trans ((hfρ q').symm.trans (congrArg ρ hb.symm))
  subst x y
  have hσ₁ : Set.range σ₁ ⊆ Set.range σ₀ := by
    rintro z ⟨t, rfl⟩
    have hz : (σ₁ t : EuclideanSpace ℝ (Fin 2)) ∈
        Set.range (fun t => ((σ₀ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) := by
      rw [hrσ, ← hrσ₁]
      exact ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := hz
    exact ⟨s, Subtype.ext hs⟩
  have hυ₁ : Set.range υ₁ ⊆ Set.range υ₀ := by
    rintro z ⟨t, rfl⟩
    have hz : (υ₁ t : EuclideanSpace ℝ (Fin 2)) ∈
        Set.range (fun t => ((υ₀ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) := by
      rw [hrυ, ← hrυ₁]
      exact ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := hz
    exact ⟨s, Subtype.ext hs⟩
  obtain ⟨W, -⟩ := BoundaryWordWitness.exists_of_sourceDirectMatch_preserving f hf σ₀ υ₀
    hσ₀ hυ₀ hσ₁ hυ₁ hσ hυ
    (σX := (σ₁.map hf).cast ha hb) (υX := (υ₁.map hf).cast hu hv)
    (fun _ => rfl) (fun _ => rfl) e hparam
    (fun t => (hα t).trans (hfρ (σ₁ t)).symm)
    (fun t => (hω t).trans (hfρ (υ₁ t)).symm)
  exact ⟨Gd, hGd, ⟨W⟩⟩

private theorem push_ambient_source_path
    {X : Type v} [TopologicalSpace X] {ρ : X → M} (hρ : Function.Injective ρ)
    (f : frontier D.domain → X) (hf : Continuous f)
    (hfρ : ∀ z : frontier D.domain, ρ (f z) = D z)
    {p q : frontier D.domain} (P : Path p q) (hP : Function.Injective P)
    (ξ : unitInterval → EuclideanSpace ℝ (Fin 2)) (hξ : Continuous ξ)
    (hξ0 : ξ 0 = p) (hξ1 : ξ 1 = q)
    (hr : Set.range ξ ⊆ Set.range (fun t => (P t : EuclideanSpace ℝ (Fin 2))))
    {a b : X} {P' Q : Path a b} (hP' : ∀ t, P' t = f (P t))
    (hQ : ∀ t, ρ (Q t) = D (ξ t)) : Q.Homotopic P' := by
  have hmem (t : unitInterval) : ξ t ∈ frontier D.domain := by
    obtain ⟨s, hs⟩ := hr ⟨t, rfl⟩
    exact hs ▸ (P s).property
  let ξ₀ : Path p q := {
    toFun := fun t => ⟨ξ t, hmem t⟩
    continuous_toFun := hξ.subtype_mk hmem
    source' := Subtype.ext hξ0
    target' := Subtype.ext hξ1 }
  apply BoundaryWordWitness.push_source_homotopy f hf hP (P₁ := ξ₀) _ hP'
  · intro t
    exact hρ ((hQ t).trans (hfρ (ξ₀ t)).symm)
  · rintro z ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := hr ⟨t, rfl⟩
    exact ⟨s, Subtype.ext hs⟩

private theorem push_ambient_source_subpath
    {X : Type v} [TopologicalSpace X] {ρ : X → M} (hρ : Function.Injective ρ)
    (f : frontier D.domain → X) (hf : Continuous f)
    (hfρ : ∀ z : frontier D.domain, ρ (f z) = D z)
    {p q : frontier D.domain} (P : Path p q) (hP : Function.Injective P)
    (ξ : ℝ → EuclideanSpace ℝ (Fin 2)) (l r : unitInterval) (hlr : l ≤ r)
    (hξ : ContinuousOn ξ (Set.Icc (l : ℝ) (r : ℝ)))
    (hξ0 : ξ l = p) (hξ1 : ξ r = q)
    (hr : ∀ t ∈ Set.Icc (l : ℝ) (r : ℝ), ξ t ∈
      Set.range (fun t => (P t : EuclideanSpace ℝ (Fin 2))))
    {a b c d : X} (β : Path a b) (P' : Path c d)
    (hc : c = β l) (hd : d = β r) (hP' : ∀ t, P' t = f (P t))
    (hβ : ∀ t : unitInterval, (t : ℝ) ∈ Set.Icc (l : ℝ) (r : ℝ) →
      ρ (β t) = D (ξ t)) : ((β.subpath l r).cast hc hd).Homotopic P' := by
  have hmem (t : unitInterval) : (Set.Icc.convexComb l r t : ℝ) ∈
      Set.Icc (l : ℝ) (r : ℝ) :=
    ⟨Set.Icc.le_convexComb hlr t, Set.Icc.convexComb_le hlr t⟩
  exact push_ambient_source_path hρ f hf hfρ P hP
    (fun t => ξ (Set.Icc.convexComb l r t))
    (hξ.comp_continuous
      (continuous_subtype_val.comp (Set.Icc.continuous_convexComb l r)) hmem)
    (by simpa only [Set.Icc.convexComb_zero] using hξ0)
    (by simpa only [Set.Icc.convexComb_one] using hξ1)
    (by rintro z ⟨t, rfl⟩; exact hr _ (hmem t)) hP'
    (fun t => hβ _ (hmem t))

private theorem range_ambient_symm {S : Set (EuclideanSpace ℝ (Fin 2))}
    {p q : S} (P : Path p q) :
    Set.range (fun t => (P.symm t : EuclideanSpace ℝ (Fin 2))) =
      Set.range (fun t => (P t : EuclideanSpace ℝ (Fin 2))) := by
  change Set.range (Subtype.val ∘ ⇑P.symm) = Set.range (Subtype.val ∘ ⇑P)
  rw [Set.range_comp, Path.symm_range, Set.range_comp]

theorem exists_boundaryWordWitnesses_of_cut [T2Space M]
    (hD : NormalSingularCellData D BdM B) {c : hD.singularSet.Branch}
    {A Cc : Set (EuclideanSpace ℝ (Fin 2))} {p q r s : EuclideanSpace ℝ (Fin 2)}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {D₁ D₂ D₃ : SingularTwoCell M}
    (hcut : hD.IsBoundaryBranchCut c A Cc p q r s g D₁ D₂ D₃)
    {X : Type v} [TopologicalSpace X]
    {ρ : X → M} (hρ : IsEmbedding ρ) (hrange : B ⊆ Set.range ρ)
    (f : frontier D.domain → X) (hf : Continuous f)
    (hfρ : ∀ z : frontier D.domain, ρ (f z) = ⇑D z) :
    ∃ (p' q' u' v' : frontier D.domain) (σ₀ : Path p' q') (τ₀ : Path q' u')
        (υ₀ : Path u' v') (φ₀ : Path v' p') (ev : loopCircle ≃ₜ frontier D.domain)
        (Gd G : SingularTwoCell M),
      hD.IsBoundarySurgeryCell c Gd ∧ hD.IsCrossRegluedCell c G ∧
      (∀ θ, ev θ = pathToCircle (σ₀.trans (τ₀.trans (υ₀.trans φ₀))) θ) ∧
      ((∃ (a b : X) (σ υ : Path a b) (τ φ : Path b a),
          (∀ t, σ t = f (σ₀ t)) ∧ (∀ t, τ t = f (τ₀ t)) ∧
          (∀ t, υ t = f (υ₀ t)) ∧ (∀ t, φ t = f (φ₀ t)) ∧
          Nonempty (BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ.symm))) ∧
          Nonempty (BoundaryWordWitness G ρ
            (pathToCircle (σ.trans (φ.trans (υ.trans τ)))))) ∨
        (∃ (a b : X) (σ : Path a b) (τ : Path b b) (υ : Path b a) (φ : Path a a),
          (∀ t, σ t = f (σ₀ t)) ∧ (∀ t, τ t = f (τ₀ t)) ∧
          (∀ t, υ t = f (υ₀ t)) ∧ (∀ t, φ t = f (φ₀ t)) ∧
          Nonempty (BoundaryWordWitness Gd ρ (pathToCircle (σ.trans υ))) ∧
          Nonempty (BoundaryWordWitness G ρ
            (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm))))))) := by
  classical
  have hcutCopy := hcut
  obtain ⟨A₂, A₄, u, v, p', q', u', v', σ₀, τ₀, υ₀, φ₀, ev,
    ⟨hA₀, hC₀, hAC₀, hcover₀, hArcA, hArcC, hp', hq', hu', hv',
      hrσ, hrτ, hrυ, hrφ, hfrontD, hev, hpairD⟩,
    hσinj, hτinj, hυinj, hφinj, huvrs, hm₃₄, hm₂, hm₁, hkey⟩ :=
    hD.exists_boundary_four_arc_word_of_cut hcut
  obtain ⟨P, Q, P', Q', A', R, T, a, b, f₁, f₂, h, f₃, H, G, hbody,
    x, y, α, ω, e, hαrange, hωrange, hparam, hxy,
    R₀, T₀, SH, pH, qH, hcutP, hcutQ, hcutH, hR₀SH, hSHsplit,
    hRimage, hR₀image, hSHT₀image, hTimage, hf₁pH, hf₁qH, hf₂pH, hf₂qH,
    hseam, aG, bG, πG, κG, haG, hbG, hπinj, hκinj, hπrange, hκrange, he⟩ :=
    hD.exists_cross_reglued_cell_of_cut_with_source_arcs hcut
  have hG : hD.IsCrossRegluedCell c G :=
    ⟨A, Cc, D₁.domain, D₂.domain, D₃.domain, P, Q, P', Q', A', R, T,
      p, q, r, s, a, b, g, f₁, f₂, h, f₃, H, hbody⟩
  obtain ⟨hA, hC, hAC, hcover, hg, hcompat, hpA, hqA, hrC, hsC, horientation,
    hdomains, hinter₁₂, hinter₂₃, hdisjoint₁₃, hP, hQ, hHdomain, hf₁, hf₂,
    hf₁seam, hf₂seam, hH₁, hH₂, hA'def, hA', hA'seam, hA'front, hk,
    hP', hQ', hGdomain, hh, hf₃, hhseam, hf₃seam, hGH, hG₃,
    hcutP', hcutQ', hR, hT, hfrontG, hha, hhb, hf₃a, hf₃b, hGimage,
    hbranchPersists, -⟩ := hbody
  have hRsub : R ⊆ P' := hcutP'.snd_subset.trans hP'.isPolyhedron.isClosed.frontier_subset
  have hTsub : T ⊆ Q' := hcutQ'.snd_subset.trans hQ'.isPolyhedron.isClosed.frontier_subset
  have hR₀P : R₀ ⊆ P := hcutP.snd_subset.trans hP.isPolyhedron.isClosed.frontier_subset
  have hT₀Q : T₀ ⊆ Q := hcutQ.snd_subset.trans hQ.isPolyhedron.isClosed.frontier_subset
  have hπmem (t : unitInterval) : (πG t : EuclideanSpace ℝ (Fin 2)) ∈ R := by
    rw [← hπrange]
    exact ⟨t, rfl⟩
  have hκmem (t : unitInterval) : (κG t : EuclideanSpace ℝ (Fin 2)) ∈ T := by
    rw [← hκrange]
    exact ⟨t, rfl⟩
  have hπext (t : ℝ) : (πG.extend t : EuclideanSpace ℝ (Fin 2)) ∈ R := by
    have ht : πG.extend t ∈ Set.range πG := by
      rw [← Path.extend_range]
      exact ⟨t, rfl⟩
    obtain ⟨u, hu⟩ := ht
    rw [← hu]
    exact hπmem u
  let η : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => h (πG.extend t)
  have hηc : Continuous η :=
    hh.isPiecewiseAffineOn.continuousOn.comp_continuous
      (continuous_subtype_val.comp πG.continuous_extend) (fun t => hRsub (hπext t))
  have hηi : Set.InjOn η (Set.Icc 0 1) := by
    intro t ht u hu htu
    have hπeq := hh.bijOn.injOn (hRsub (hπext t)) (hRsub (hπext u)) htu
    have hπeq' : πG ⟨t, ht⟩ = πG ⟨u, hu⟩ := by
      apply Subtype.ext
      simpa only [Path.extend_apply πG ht, Path.extend_apply πG hu] using hπeq
    exact congrArg Subtype.val (hπinj hπeq')
  have hηimage : η '' Set.Icc 0 1 = SH := by
    have hπimage : (fun t : ℝ => (πG.extend t : EuclideanSpace ℝ (Fin 2))) ''
        Set.Icc 0 1 = R := by
      apply Subset.antisymm
      · rintro z ⟨t, -, rfl⟩
        exact hπext t
      · intro z hz
        obtain ⟨t, ht⟩ := hπrange.symm.subset hz
        exact ⟨t, t.property, by simpa only [Path.extend_extends'] using ht⟩
    change (h ∘ fun t => (πG.extend t : EuclideanSpace ℝ (Fin 2))) '' _ = _
    rw [Set.image_comp, hπimage, hRimage]
  have hηSH {t : ℝ} (ht : t ∈ Set.Icc 0 1) : η t ∈ SH := by
    rw [← hηimage]
    exact ⟨t, ht, rfl⟩
  have hη0 : η 0 = Function.invFunOn f₂ Q p := by
    simpa [η, haG] using hha
  have hη1 : η 1 = Function.invFunOn f₂ Q q := by
    simpa [η, hbG] using hhb
  obtain ⟨t₁, t₂, hηt₁, hηt₂, ht₁, ht₂, hne, hparts⟩ :=
    exists_three_segment_parameters_of_injective_param η hηc.continuousOn hηi hηimage
      hcutP.snd hR₀SH hSHsplit hcutQ.snd.left_mem hcutQ.snd.right_mem
  have hclosed₂ : IsClosed A₂ := by
    rw [← hrτ]
    exact (isCompact_range (continuous_subtype_val.comp τ₀.continuous)).isClosed
  have hclosed₄ : IsClosed A₄ := by
    rw [← hrφ]
    exact (isCompact_range (continuous_subtype_val.comp φ₀.continuous)).isClosed
  have huv : u ≠ v := by
    intro huv
    have huv' : u' = v' := Subtype.ext (hu'.trans (huv.trans hv'.symm))
    exact zero_ne_one (hυinj (υ₀.source.trans (huv'.trans υ₀.target.symm)))
  have hdisjoint₂₄ : Disjoint A₂ A₄ := by
    apply Set.disjoint_left.mpr
    intro z hz₂ hz₄
    have hzu : z = u := hm₂ z hz₂ (Or.inr hz₄)
    have huD : u ∈ D₃.domain ∩ frontier D.domain := by
      rw [← hrυ]
      exact ⟨0, by simpa only [Path.source] using hu'⟩
    have huv' : u = v := hm₃₄ u huD (hzu ▸ hz₄)
    exact huv huv'
  have hp₄ : p ∈ A₄ := by
    rw [← hrφ]
    exact ⟨1, by simpa only [Path.target] using hp'⟩
  have hq₂ : q ∈ A₂ := by
    rw [← hrτ]
    exact ⟨0, by simpa only [Path.source] using hq'⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hcut₁, -⟩ := hcutCopy
  have hmiddle : D₂.domain ∩ frontier D.domain ⊆ A₂ ∪ A₄ := by
    intro z hz
    have hz' : z ∈ A₂ ∪ ((D₁.domain ∩ frontier D.domain) ∪ A₄) := by
      rw [← hkey]
      exact ⟨Or.inr hz.1, hz.2⟩
    rcases hz' with hz₂ | hz₁ | hz₄
    · exact Or.inl hz₂
    · have hzA : z ∈ A := hinter₁₂ ▸ ⟨hz₁.1, hz.1⟩
      rcases hcut₁.inter_eq.subset ⟨hzA, hz₁⟩ with rfl | rfl
      · exact Or.inr hp₄
      · exact Or.inl hq₂
    · exact Or.inr hz₄
  have hpD₂ : p ∈ D₂.domain := (hinter₁₂.symm ▸ hpA).2
  have hqD₂ : q ∈ D₂.domain := (hinter₁₂.symm ▸ hqA).2
  have hf₂η0 : f₂ (η 0) = p := by
    rw [hη0]
    exact hf₂.bijOn.invOn_invFunOn.2 hpD₂
  have hf₂η1 : f₂ (η 1) = q := by
    rw [hη1]
    exact hf₂.bijOn.invOn_invFunOn.2 hqD₂
  have hgp : g p ∈ D₃.domain ∩ frontier D.domain := by
    rw [← hTimage, ← hf₃a]
    exact ⟨a, hcutQ'.snd.left_mem, rfl⟩
  have hgq : g q ∈ D₃.domain ∩ frontier D.domain := by
    rw [← hTimage, ← hf₃b]
    exact ⟨b, hcutQ'.snd.right_mem, rfl⟩
  have houter (l r : unitInterval)
      (hleft : ∀ t ∈ Set.Icc 0 (l : ℝ), η t ∈ T₀)
      (hright : ∀ t ∈ Set.Icc (r : ℝ) 1, η t ∈ T₀) :
      (∀ t ∈ Set.Icc 0 (l : ℝ), f₂ (η t) ∈ A₄) ∧
        (∀ t ∈ Set.Icc (r : ℝ) 1, f₂ (η t) ∈ A₂) := by
    have hleft01 : Set.Icc 0 (l : ℝ) ⊆ Set.Icc 0 1 :=
      Set.Icc_subset_Icc le_rfl l.property.2
    have hright01 : Set.Icc (r : ℝ) 1 ⊆ Set.Icc 0 1 :=
      Set.Icc_subset_Icc r.property.1 le_rfl
    have hcontL : ContinuousOn (f₂ ∘ η) (Set.Icc 0 (l : ℝ)) :=
      hf₂.isPiecewiseAffineOn.continuousOn.comp hηc.continuousOn
        (fun t ht => hT₀Q (hleft t ht))
    have hcontR : ContinuousOn (f₂ ∘ η) (Set.Icc (r : ℝ) 1) :=
      hf₂.isPiecewiseAffineOn.continuousOn.comp hηc.continuousOn
        (fun t ht => hT₀Q (hright t ht))
    have hcovL : (f₂ ∘ η) '' Set.Icc 0 (l : ℝ) ⊆ A₄ ∪ A₂ := by
      rintro z ⟨t, ht, rfl⟩
      rw [Set.union_comm]
      apply hmiddle
      rw [← hSHT₀image]
      exact ⟨η t, ⟨hηSH (hleft01 ht), hleft t ht⟩, rfl⟩
    have hcovR : (f₂ ∘ η) '' Set.Icc (r : ℝ) 1 ⊆ A₂ ∪ A₄ := by
      rintro z ⟨t, ht, rfl⟩
      apply hmiddle
      rw [← hSHT₀image]
      exact ⟨η t, ⟨hηSH (hright01 ht), hright t ht⟩, rfl⟩
    have hL := connected_image_in_left (isPreconnected_Icc.image _ hcontL)
      hclosed₄ hclosed₂ hcovL hdisjoint₂₄.symm
      ⟨p, ⟨0, ⟨le_rfl, l.property.1⟩, hf₂η0⟩, hp₄⟩
    have hR' := connected_image_in_left (isPreconnected_Icc.image _ hcontR)
      hclosed₂ hclosed₄ hcovR hdisjoint₂₄
      ⟨q, ⟨1, ⟨r.property.2, le_rfl⟩, hf₂η1⟩, hq₂⟩
    exact ⟨fun t ht => hL ⟨t, ht, rfl⟩, fun t ht => hR' ⟨t, ht, rfl⟩⟩
  have hGb : ∀ z : frontier G.domain, G z ∈ Set.range ρ := by
    intro z
    exact hrange (hD.range_boundary_subset_of_isCrossRegluedCell hG ⟨z, rfl⟩)
  choose F hFρ using hGb
  have hFc : Continuous F := hρ.isInducing.continuous_iff.mpr (by
    have heq : ρ ∘ F = G.boundary := funext hFρ
    rw [heq]
    exact G.boundary.continuous)
  have hηext (t : unitInterval) : η t = h (πG t) := by
    simp only [η, Path.extend_extends']
  have hFa : F aG = f p' := by
    apply hρ.injective
    rw [hFρ, hfρ, hp']
    rw [hGH (hRsub (haG ▸ hcutP'.snd.left_mem))]
    change H (h aG) = D p
    rw [haG, hha, hH₂ (hf₂.bijOn.surjOn.mapsTo_invFunOn hpD₂)]
    exact congrArg D (hf₂.bijOn.invOn_invFunOn.2 hpD₂)
  have hFb : F bG = f q' := by
    apply hρ.injective
    rw [hFρ, hfρ, hq']
    rw [hGH (hRsub (hbG ▸ hcutP'.snd.right_mem))]
    change H (h bG) = D q
    rw [hbG, hhb, hH₂ (hf₂.bijOn.surjOn.mapsTo_invFunOn hqD₂)]
    exact congrArg D (hf₂.bijOn.invOn_invFunOn.2 hqD₂)
  let β : Path (f p') (f q') := (πG.map hFc).cast hFa.symm hFb.symm
  let κ : Path (f q') (f p') := (κG.map hFc).cast hFb.symm hFa.symm
  have hβ₁ (t : unitInterval) (ht : η t ∈ R₀) :
      ρ (β t) = D (f₁ (η t)) := by
    change ρ (F (πG t)) = _
    rw [hFρ, hGH (hRsub (hπmem t))]
    change H (h (πG t)) = _
    rw [← hηext t]
    exact hH₁ (hR₀P ht)
  have hβ₂ (t : unitInterval) (ht : η t ∈ T₀) :
      ρ (β t) = D (f₂ (η t)) := by
    change ρ (F (πG t)) = _
    rw [hFρ, hGH (hRsub (hπmem t))]
    change H (h (πG t)) = _
    rw [← hηext t]
    exact hH₂ (hT₀Q ht)
  have hκ (t : unitInterval) : ρ (κ t) = D (f₃ (κG t)) :=
    (hFρ _).trans (hG₃ (hTsub (hκmem t)))
  have hβt₁ : β ⟨t₁, ht₁⟩ = f p' := by
    apply hρ.injective
    rw [hβ₁ _ (hηt₁.symm ▸ hcutP.snd.left_mem), hηt₁, hf₁pH, hfρ, hp']
  have hβt₂ : β ⟨t₂, ht₂⟩ = f q' := by
    apply hρ.injective
    rw [hβ₁ _ (hηt₂.symm ▸ hcutP.snd.right_mem), hηt₂, hf₁qH, hfρ, hq']
  have hreal : ∀ θ, ρ (pathToCircle (β.trans κ) θ) = G (e θ) := by
    intro θ
    rw [he θ]
    rw [pathToCircle_eq_of_forall (πG.trans κG) (β.trans κ)
      (trans_apply_eq_map (f := F) (fun _ => rfl) (fun _ => rfl)) θ, hFρ]
  let Wback : BoundaryWordWitness G ρ (pathToCircle (β.trans κ).symm) := {
    param := (Homeomorph.neg loopCircle).trans e
    loop := pathToCircle (β.trans κ).symm
    realizes := fun θ => by
      rw [pathToCircle_symm]
      exact hreal (-θ)
    homotopic := ContinuousMap.Homotopic.refl _ }
  have hcont₁ (l r : unitInterval)
      (hseg : ∀ t ∈ Set.Icc (l : ℝ) (r : ℝ), η t ∈ R₀) :
      ContinuousOn (f₁ ∘ η) (Set.Icc (l : ℝ) (r : ℝ)) :=
    hf₁.isPiecewiseAffineOn.continuousOn.comp hηc.continuousOn
      (fun t ht => hR₀P (hseg t ht))
  have hcont₂ (l r : unitInterval)
      (hseg : ∀ t ∈ Set.Icc (l : ℝ) (r : ℝ), η t ∈ T₀) :
      ContinuousOn (f₂ ∘ η) (Set.Icc (l : ℝ) (r : ℝ)) :=
    hf₂.isPiecewiseAffineOn.continuousOn.comp hηc.continuousOn
      (fun t ht => hT₀Q (hseg t ht))
  have hcont₃ : Continuous (fun t => f₃ (κG t)) :=
    hf₃.isPiecewiseAffineOn.continuousOn.comp_continuous
      (continuous_subtype_val.comp κG.continuous) (fun t => hTsub (hκmem t))
  have hκrange' : Set.range (fun t => f₃ (κG t)) ⊆ D₃.domain ∩ frontier D.domain := by
    rintro z ⟨t, rfl⟩
    rw [← hTimage]
    exact ⟨κG t, hκmem t, rfl⟩
  rcases hparts with ⟨hlt, hleft, hmid, hright⟩ | ⟨hlt, hleft, hmid, hright⟩
  · obtain ⟨hleft₄, hright₂⟩ := houter ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ hleft hright
    have hgpv : g p = v := hm₃₄ _ hgp (by
      simpa only [hηt₁, hf₂pH] using hleft₄ t₁ ⟨ht₁.1, le_rfl⟩)
    have hgqu : g q = u := hm₂ _ (by
      simpa only [hηt₂, hf₂qH] using hright₂ t₂ ⟨le_rfl, ht₂.2⟩) (Or.inl hgq)
    have huX : f u' = f q' := by
      apply hρ.injective
      rw [hfρ, hfρ, hu', hq', ← hgqu]
      exact (hcompat hqA).symm
    have hvX : f v' = f p' := by
      apply hρ.injective
      rw [hfρ, hfρ, hv', hp', ← hgpv]
      exact (hcompat hpA).symm
    let σ := σ₀.map hf
    let τ : Path (f q') (f q') := (τ₀.map hf).cast rfl huX.symm
    let υ : Path (f q') (f p') := (υ₀.map hf).cast huX.symm hvX.symm
    let φ : Path (f p') (f p') := (φ₀.map hf).cast hvX.symm rfl
    have hL := push_ambient_source_subpath hρ.injective f hf hfρ φ₀.symm
      (hφinj.comp unitInterval.symm_bijective.injective) (f₂ ∘ η) 0 ⟨t₁, ht₁⟩
      ht₁.1 (hcont₂ _ _ hleft)
      (hf₂η0.trans hp'.symm)
      ((congrArg f₂ hηt₁).trans (hf₂pH.trans (hgpv.trans hv'.symm)))
      (fun t ht => by rw [range_ambient_symm, hrφ]; exact hleft₄ t ht)
      β φ.symm β.source.symm hβt₁.symm (fun _ => rfl)
      (fun t ht => hβ₂ t (hleft t ht))
    have hM := push_ambient_source_subpath hρ.injective f hf hfρ σ₀ hσinj
      (f₁ ∘ η) ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ hlt.le (hcont₁ _ _ hmid)
      ((congrArg f₁ hηt₁).trans (hf₁pH.trans hp'.symm))
      ((congrArg f₁ hηt₂).trans (hf₁qH.trans hq'.symm))
      (fun t ht => by rw [hrσ, ← hR₀image]; exact ⟨η t, hmid t ht, rfl⟩)
      β σ hβt₁.symm hβt₂.symm (fun _ => rfl)
      (fun t ht => hβ₁ t (hmid t ht))
    have hR' := push_ambient_source_subpath hρ.injective f hf hfρ τ₀.symm
      (hτinj.comp unitInterval.symm_bijective.injective) (f₂ ∘ η) ⟨t₂, ht₂⟩ 1
      ht₂.2 (hcont₂ _ _ hright)
      ((congrArg f₂ hηt₂).trans (hf₂qH.trans (hgqu.trans hu'.symm)))
      (hf₂η1.trans hq'.symm)
      (fun t ht => by rw [range_ambient_symm, hrτ]; exact hright₂ t ht)
      β τ.symm hβt₂.symm β.target.symm (fun _ => rfl)
      (fun t ht => hβ₂ t (hright t ht))
    have hK := push_ambient_source_path hρ.injective f hf hfρ υ₀ hυinj
      (fun t => f₃ (κG t)) hcont₃
      (by simpa only [Path.source, hbG] using hf₃b.trans (hgqu.trans hu'.symm))
      (by simpa only [Path.target, haG] using hf₃a.trans (hgpv.trans hv'.symm))
      (by rw [hrυ]; exact hκrange') (P' := υ) (Q := κ) (fun _ => rfl) hκ
    have hlong := (homotopic_three_subpaths β ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ hβt₁ hβt₂).trans
      (hL.hcomp (hM.hcomp hR'))
    have Wwalk := Wback.ofHomotopicWord (pathToCircle_homotopic (hlong.hcomp hK).symm₂)
    have Wfront := Wwalk.ofReversedWord
    rw [pathToCircle_symm, BoundaryWordWitness.comp_neg_comp_neg] at Wfront
    have hrot₂ := pathToCircle_homotopic
      (Path.Homotopic.trans_assoc φ.symm (σ.trans τ.symm) υ)
    have hrot₃ := pathToCircle_trans_homotopic_comm φ.symm ((σ.trans τ.symm).trans υ)
    have hrot₄ := pathToCircle_homotopic
      (Path.Homotopic.trans_assoc (σ.trans τ.symm) υ φ.symm)
    have hrot₅ := pathToCircle_homotopic
      (Path.Homotopic.trans_assoc σ τ.symm (υ.trans φ.symm))
    have Wcross := Wfront.ofHomotopicWord (((hrot₂.trans hrot₃).trans hrot₄).trans hrot₅)
    obtain ⟨Gd, hGd, Wdirect⟩ := hD.exists_boundaryWordWitness_direct_of_cut hcut f hf hfρ
      σ₀ υ₀ hp' hq' (hu'.trans hgqu.symm) (hv'.trans hgpv.symm)
      hσinj hυinj hrσ hrυ (σ := σ) (υ := υ) (fun _ => rfl) (fun _ => rfl)
    exact ⟨p', q', u', v', σ₀, τ₀, υ₀, φ₀, ev, Gd, G, hGd, hG, hev,
      Or.inr ⟨f p', f q', σ, τ, υ, φ, (fun _ => rfl), (fun _ => rfl),
        (fun _ => rfl), (fun _ => rfl), Wdirect, ⟨Wcross⟩⟩⟩
  · obtain ⟨hleft₄, hright₂⟩ := houter ⟨t₂, ht₂⟩ ⟨t₁, ht₁⟩ hleft hright
    have hgqv : g q = v := hm₃₄ _ hgq (by
      simpa only [hηt₂, hf₂qH] using hleft₄ t₂ ⟨ht₂.1, le_rfl⟩)
    have hgpu : g p = u := hm₂ _ (by
      simpa only [hηt₁, hf₂pH] using hright₂ t₁ ⟨le_rfl, ht₁.2⟩) (Or.inl hgp)
    have huX : f u' = f p' := by
      apply hρ.injective
      rw [hfρ, hfρ, hu', hp', ← hgpu]
      exact (hcompat hpA).symm
    have hvX : f v' = f q' := by
      apply hρ.injective
      rw [hfρ, hfρ, hv', hq', ← hgqv]
      exact (hcompat hqA).symm
    let σ := σ₀.map hf
    let τ : Path (f q') (f p') := (τ₀.map hf).cast rfl huX.symm
    let υ : Path (f p') (f q') := (υ₀.map hf).cast huX.symm hvX.symm
    let φ : Path (f q') (f p') := (φ₀.map hf).cast hvX.symm rfl
    have hL := push_ambient_source_subpath hρ.injective f hf hfρ φ₀.symm
      (hφinj.comp unitInterval.symm_bijective.injective) (f₂ ∘ η) 0 ⟨t₂, ht₂⟩
      ht₂.1 (hcont₂ _ _ hleft)
      (hf₂η0.trans hp'.symm)
      ((congrArg f₂ hηt₂).trans (hf₂qH.trans (hgqv.trans hv'.symm)))
      (fun t ht => by rw [range_ambient_symm, hrφ]; exact hleft₄ t ht)
      β φ.symm β.source.symm hβt₂.symm (fun _ => rfl)
      (fun t ht => hβ₂ t (hleft t ht))
    have hM := push_ambient_source_subpath hρ.injective f hf hfρ σ₀.symm
      (hσinj.comp unitInterval.symm_bijective.injective)
      (f₁ ∘ η) ⟨t₂, ht₂⟩ ⟨t₁, ht₁⟩ hlt.le (hcont₁ _ _ hmid)
      ((congrArg f₁ hηt₂).trans (hf₁qH.trans hq'.symm))
      ((congrArg f₁ hηt₁).trans (hf₁pH.trans hp'.symm))
      (fun t ht => by
        rw [range_ambient_symm, hrσ, ← hR₀image]
        exact ⟨η t, hmid t ht, rfl⟩)
      β σ.symm hβt₂.symm hβt₁.symm (fun _ => rfl)
      (fun t ht => hβ₁ t (hmid t ht))
    have hR' := push_ambient_source_subpath hρ.injective f hf hfρ τ₀.symm
      (hτinj.comp unitInterval.symm_bijective.injective) (f₂ ∘ η) ⟨t₁, ht₁⟩ 1
      ht₁.2 (hcont₂ _ _ hright)
      ((congrArg f₂ hηt₁).trans (hf₂pH.trans (hgpu.trans hu'.symm)))
      (hf₂η1.trans hq'.symm)
      (fun t ht => by rw [range_ambient_symm, hrτ]; exact hright₂ t ht)
      β τ.symm hβt₁.symm β.target.symm (fun _ => rfl)
      (fun t ht => hβ₂ t (hright t ht))
    have hK := push_ambient_source_path hρ.injective f hf hfρ υ₀.symm
      (hυinj.comp unitInterval.symm_bijective.injective)
      (fun t => f₃ (κG t)) hcont₃
      (by simpa only [Path.source, hbG] using hf₃b.trans (hgqv.trans hv'.symm))
      (by simpa only [Path.target, haG] using hf₃a.trans (hgpu.trans hu'.symm))
      (by rw [range_ambient_symm, hrυ]; exact hκrange')
      (P' := υ.symm) (Q := κ) (fun _ => rfl) hκ
    have hlong := (homotopic_three_subpaths β ⟨t₂, ht₂⟩ ⟨t₁, ht₁⟩ hβt₂ hβt₁).trans
      (hL.hcomp (hM.hcomp hR'))
    have Wwalk := Wback.ofHomotopicWord (pathToCircle_homotopic (hlong.hcomp hK).symm₂)
    simp only [Path.trans_symm, Path.symm_symm] at Wwalk
    have hrot₁ := pathToCircle_trans_homotopic_comm υ ((τ.trans σ).trans φ)
    have hrot₂ := pathToCircle_homotopic (Path.Homotopic.trans_assoc (τ.trans σ) φ υ)
    have hrot₃ := pathToCircle_homotopic (Path.Homotopic.trans_assoc τ σ (φ.trans υ))
    have hrot₄ := pathToCircle_trans_homotopic_comm τ (σ.trans (φ.trans υ))
    have hrot₅ := pathToCircle_homotopic (Path.Homotopic.trans_assoc σ (φ.trans υ) τ)
    have hrot₆ := pathToCircle_homotopic
      ((Path.Homotopic.refl σ).hcomp (Path.Homotopic.trans_assoc φ υ τ))
    have Wcross := Wwalk.ofHomotopicWord
      (((((hrot₁.trans hrot₂).trans hrot₃).trans hrot₄).trans hrot₅).trans hrot₆)
    obtain ⟨Gd, hGd, Wdirect⟩ := hD.exists_boundaryWordWitness_direct_of_cut hcut f hf hfρ
      σ₀ υ₀.symm hp' hq' (hv'.trans hgqv.symm) (hu'.trans hgpu.symm)
      hσinj (hυinj.comp unitInterval.symm_bijective.injective) hrσ
      (by rw [range_ambient_symm, hrυ]) (σ := σ) (υ := υ.symm)
      (fun _ => rfl) (fun _ => rfl)
    exact ⟨p', q', u', v', σ₀, τ₀, υ₀, φ₀, ev, Gd, G, hGd, hG, hev,
      Or.inl ⟨f p', f q', σ, υ, τ, φ, (fun _ => rfl), (fun _ => rfl),
        (fun _ => rfl), (fun _ => rfl), Wdirect, ⟨Wcross⟩⟩⟩

end NormalSingularCellData

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem image_range_of_frontierRealization {D : SingularTwoCell M} {X : Type v}
    [TopologicalSpace X] {ρ : X → M} {f : frontier D.domain → X}
    (hf : ∀ z : frontier D.domain, ρ (f z) = D ↑z) {a b : frontier D.domain} {y z : X}
    {p₀ : Path a b} {p : Path y z} (hp : ∀ t, p t = f (p₀ t)) :
    ρ '' Set.range ⇑p =
      ⇑D '' Set.range (fun t => ((p₀ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2))) := by
  have h₁ : Set.range ⇑p = Set.range fun t => f (p₀ t) := congrArg Set.range (funext hp)
  have h₂ : (ρ ∘ fun t => f (p₀ t)) =
      ⇑D ∘ fun t => ((p₀ t : frontier D.domain) : EuclideanSpace ℝ (Fin 2)) :=
    funext fun t => hf (p₀ t)
  rw [h₁, ← Set.range_comp, h₂, Set.range_comp]

end DifferentialGeometry.Topology.PiecewiseLinear
