/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CellGluing
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.CrossRegluedCellFields

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

def crossRegluedSourceVLeft (P' P : Set (EuclideanSpace ℝ (Fin 2)))
    (h : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  P' ∩ h ⁻¹' P

def crossRegluedSourceVMiddle (P' Q : Set (EuclideanSpace ℝ (Fin 2)))
    (h : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  P' ∩ h ⁻¹' Q

def crossRegluedSourceVRight (Q' : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 2)) := Q'

def crossRegluedSourceJFirst (P' P Q : Set (EuclideanSpace ℝ (Fin 2)))
    (h : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  P' ∩ h ⁻¹' (P ∩ Q)

def crossRegluedSourceJSecond (P' Q' : Set (EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  P' ∩ Q'

def crossRegluedSourceFLeft (f₁ h : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := f₁ ∘ h

def crossRegluedSourceFMiddle (f₂ h : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := f₂ ∘ h

def crossRegluedSourceFRight (f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) := f₃

section Reading

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D H G : SingularTwoCell M}
  {P Q P' Q' A' : Set (EuclideanSpace ℝ (Fin 2))}
  {g f₁ f₂ h f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}

theorem crossRegluedSource_reading
    (hH₁ : EqOn H (D ∘ f₁) P) (hH₂ : EqOn H (D ∘ f₂) Q)
    (hGH : EqOn G (H ∘ h) P') (hG₃ : EqOn G (D ∘ f₃) Q')
    (hf₂f₁ : EqOn f₂ (g ∘ f₁) (P ∩ Q))
    (hsource : EqOn f₃ ((g ∘ f₂) ∘ h) (P' ∩ Q'))
    (hhseam : h '' (P' ∩ Q') = A') (hA'Q : A' ⊆ Q)
    (hA'notP : Disjoint A' P) :
    EqOn G (D ∘ crossRegluedSourceFLeft f₁ h)
        (crossRegluedSourceVLeft P' P h) ∧
      EqOn G (D ∘ crossRegluedSourceFMiddle f₂ h)
        (crossRegluedSourceVMiddle P' Q h) ∧
      EqOn G (D ∘ crossRegluedSourceFRight f₃)
        (crossRegluedSourceVRight Q') ∧
      crossRegluedSourceVLeft P' P h ∩ crossRegluedSourceVMiddle P' Q h =
        crossRegluedSourceJFirst P' P Q h ∧
      crossRegluedSourceVMiddle P' Q h ∩ crossRegluedSourceVRight Q' =
        crossRegluedSourceJSecond P' Q' ∧
      Disjoint (crossRegluedSourceVLeft P' P h) (crossRegluedSourceVRight Q') ∧
      Disjoint (crossRegluedSourceJFirst P' P Q h)
        (crossRegluedSourceJSecond P' Q') ∧
      EqOn (crossRegluedSourceFMiddle f₂ h)
        (g ∘ crossRegluedSourceFLeft f₁ h)
        (crossRegluedSourceJFirst P' P Q h) ∧
      EqOn (crossRegluedSourceFRight f₃)
        (g ∘ crossRegluedSourceFMiddle f₂ h)
        (crossRegluedSourceJSecond P' Q') := by
  have hseamQ : P' ∩ Q' ⊆ h ⁻¹' Q := by
    intro x hx
    have hxA' : h x ∈ A' := by
      rw [← hhseam]
      exact ⟨x, hx, rfl⟩
    exact hA'Q hxA'
  have hseamNotP : ∀ x ∈ P' ∩ Q', h x ∉ P := by
    intro x hx hxP
    have hxA' : h x ∈ A' := by
      rw [← hhseam]
      exact ⟨x, hx, rfl⟩
    exact Set.disjoint_left.mp hA'notP hxA' hxP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change G x = D (f₁ (h x))
    exact apply_crossReglued_left hH₁ hGH hx.1 hx.2
  · intro x hx
    change G x = D (f₂ (h x))
    exact apply_crossReglued_middle hH₂ hGH hx.1 hx.2
  · intro x hx
    change G x = D (f₃ x)
    exact apply_crossReglued_right hG₃ hx
  · ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, ⟨hx.1.2, hx.2.2⟩⟩
    · intro hx
      exact ⟨⟨hx.1, hx.2.1⟩, ⟨hx.1, hx.2.2⟩⟩
  · apply Set.Subset.antisymm
    · intro x hx
      exact ⟨hx.1.1, hx.2⟩
    · intro x hx
      exact ⟨⟨hx.1, hseamQ hx⟩, hx.2⟩
  · apply Set.disjoint_left.mpr
    intro x hxV₁ hxV₃
    exact hseamNotP x ⟨hxV₁.1, hxV₃⟩ hxV₁.2
  · apply Set.disjoint_left.mpr
    intro x hxJ₁₂ hxJ₂₃
    exact hseamNotP x ⟨hxJ₂₃.1, hxJ₂₃.2⟩ hxJ₁₂.2.1
  · intro x hx
    change f₂ (h x) = g (f₁ (h x))
    simpa only [Function.comp_apply] using hf₂f₁ hx.2
  · intro x hx
    change f₃ x = g (f₂ (h x))
    simpa only [Function.comp_apply] using hsource hx

end Reading

section Producer

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {D : SingularTwoCell M} {A C U₁ U₂ U₃ : Set (EuclideanSpace ℝ (Fin 2))}
  {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}

theorem exists_crossRegluedSource_of_isPLHomeomorphOn_disjoint_boundary_arcs
    (D₁ D₂ D₃ : SingularTwoCell M) (hA : IsPLBall 1 A) (hAC : Disjoint A C)
    {a₀ a₁ : EuclideanSpace ℝ (Fin 2)}
    (hAfront₂ : A ⊆ frontier D₂.domain) (hCfront₂ : C ⊆ frontier D₂.domain)
    (hcut₁ : Schoenflies.IsCutPair (frontier D₁.domain) a₀ a₁ A
      (D₁.domain ∩ frontier D.domain))
    (hcut₃ : Schoenflies.IsCutPair (frontier D₃.domain) (g a₀) (g a₁) C
      (D₃.domain ∩ frontier D.domain))
    (hg : IsPLHomeomorphOn g A C)
    (hcompat₁₂ : EqOn D₁ (D₂ ∘ g) A) (hcompat₂₃ : EqOn D₂ (D₃ ∘ g) A)
    (hfun₁ : D₁.toFun = D.toFun) (hfun₂ : D₂.toFun = D.toFun)
    (hfun₃ : D₃.toFun = D.toFun) :
    ∃ (H G : SingularTwoCell M) (P Q P' Q' A' : Set (EuclideanSpace ℝ (Fin 2)))
      (f₁ f₂ h f₃ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)),
      IsPLBall 2 P ∧ IsPLBall 2 Q ∧ H.domain = P ∪ Q ∧
      IsPLHomeomorphOn f₁ P D₁.domain ∧ IsPLHomeomorphOn f₂ Q D₂.domain ∧
      EqOn f₂ (g ∘ f₁) (P ∩ Q) ∧ f₁ '' (P ∩ Q) = A ∧ f₂ '' (P ∩ Q) = C ∧
      EqOn H (D ∘ f₁) P ∧ EqOn H (D ∘ f₂) Q ∧
      A' = Function.invFunOn f₂ Q '' A ∧ IsPLBall 1 A' ∧
      Disjoint A' (P ∩ Q) ∧ A' ⊆ Q ∧ Disjoint A' P ∧
      IsPLHomeomorphOn (g ∘ f₂) A' C ∧ IsPLBall 2 P' ∧ IsPLBall 2 Q' ∧
      G.domain = P' ∪ Q' ∧ IsPLHomeomorphOn h P' H.domain ∧
      IsPLHomeomorphOn f₃ Q' D₃.domain ∧ h '' (P' ∩ Q') = A' ∧
      f₃ '' (P' ∩ Q') = C ∧ EqOn G (H ∘ h) P' ∧
      EqOn G (D ∘ f₃) Q' ∧ EqOn f₃ ((g ∘ f₂) ∘ h) (P' ∩ Q') := by
  obtain ⟨H, P, Q, f₁, f₂, hP, hQ, -, hHdomain, -, -, -, hf₁, hf₂, hf₂f₁,
    hf₁seam, hf₂seam, hH₁, hH₂, pH, qH, R₀, T₀, hcutP, hcutQ, hR₀, -, hfrontH,
    hf₁pH, hf₁qH, hf₂pH, hf₂qH⟩ :=
    D₁.exists_glue_of_isPLHomeomorphOn_boundary_arc D₂ hA hcut₁.fst hcut₁.fst_subset hg
      hCfront₂ hcompat₁₂
  let j := Function.invFunOn f₂ Q
  let A' := j '' A
  have hAD₂ : A ⊆ D₂.domain :=
    hAfront₂.trans D₂.isPLBall_domain.isPolyhedron.isClosed.frontier_subset
  have hjA : IsPLHomeomorphOn j A A' := by
    simpa only [j, A'] using hf₂.symm.restrict hA.isPolyhedron hAD₂
  have hA' : IsPLBall 1 A' := hA.of_isPLHomeomorphOn hjA
  have hA'arc : Schoenflies.IsArcBetween A' (j a₀) (j a₁) := by
    obtain ⟨α, hαc, hαi, hαimage, hα0, hα1⟩ := hcut₁.fst
    have hαA : ∀ t ∈ unitInterval, α t ∈ A := by
      intro t ht
      rw [← hαimage]
      exact ⟨t, ht, rfl⟩
    refine ⟨j ∘ α, hjA.isPiecewiseAffineOn.continuousOn.comp hαc hαA, ?_, ?_, ?_, ?_⟩
    · intro s hs t ht hst
      exact hαi hs ht (hjA.bijOn.injOn (hαA s hs) (hαA t ht) hst)
    · calc
        (j ∘ α) '' unitInterval = j '' (α '' unitInterval) := image_comp j α unitInterval
        _ = j '' A := congrArg (j '' ·) hαimage
        _ = A' := rfl
    · simp only [Function.comp_apply, hα0]
    · simp only [Function.comp_apply, hα1]
  have hjfront : j '' frontier D₂.domain = frontier Q := by
    simpa only [j] using hf₂.symm.image_frontier (by simp)
      D₂.isPLBall_domain.isPolyhedron.isClosed hQ.isPolyhedron.isClosed
  have hA'frontQ : A' ⊆ frontier Q := by
    rw [← hjfront]
    exact image_mono hAfront₂
  have hA'seam : Disjoint A' (P ∩ Q) := by
    rw [Set.disjoint_left]
    rintro x ⟨y, hyA, rfl⟩ hxseam
    have hyD₂ : y ∈ D₂.domain := hAD₂ hyA
    have hf₂j : f₂ (j y) = y := hf₂.bijOn.invOn_invFunOn.2 hyD₂
    have hCmem : f₂ (j y) ∈ C := by
      rw [← hf₂seam]
      exact ⟨j y, hxseam, rfl⟩
    exact Set.disjoint_left.mp hAC hyA (hf₂j ▸ hCmem)
  have hA'T : A' ⊆ T₀ := by
    intro x hxA'
    have hxfront := hA'frontQ hxA'
    rw [← hcutQ.union_eq] at hxfront
    exact hxfront.resolve_left (Set.disjoint_left.mp hA'seam hxA')
  have hA'frontH : A' ⊆ frontier H.domain := by
    rw [hfrontH]
    exact hA'T.trans subset_union_right
  have hA'Q : A' ⊆ Q := by
    rintro x ⟨y, hyA, rfl⟩
    exact hf₂.bijOn.surjOn.mapsTo_invFunOn (hAD₂ hyA)
  have hA'notP : Disjoint A' P := by
    rw [Set.disjoint_left]
    intro x hxA' hxP
    exact Set.disjoint_left.mp hA'seam hxA' ⟨hxP, hA'Q hxA'⟩
  have hf₂A'image : f₂ '' A' = A := by
    calc
      f₂ '' A' = f₂ '' (j '' A) := rfl
      _ = (f₂ ∘ j) '' A := (image_comp f₂ j A).symm
      _ = id '' A := Set.image_congr fun y hy => hf₂.bijOn.invOn_invFunOn.2 (hAD₂ hy)
      _ = A := image_id A
  have hf₂A' : IsPLHomeomorphOn f₂ A' A := by
    have h := hf₂.restrict hA'.isPolyhedron hA'Q
    rwa [hf₂A'image] at h
  have hk : IsPLHomeomorphOn (g ∘ f₂) A' C := hf₂A'.trans hg
  have hcompatH₃ : EqOn H (D₃ ∘ (g ∘ f₂)) A' := by
    intro x hx
    calc
      H x = D₂ (f₂ x) := hH₂ (hA'Q hx)
      _ = D₃ (g (f₂ x)) := hcompat₂₃ (hf₂A'.bijOn.mapsTo hx)
      _ = (D₃ ∘ (g ∘ f₂)) x := rfl
  obtain ⟨G, P', Q', h, f₃, hP', hQ', -, hGdomain, -, -, -, hh, hf₃, hsource,
    hhseam, hf₃seam, hGH, hG₃, a, b, R', T', hcutP', hcutQ', hR', hT', hfrontG,
    hha, hhb, hf₃a, hf₃b⟩ :=
    H.exists_glue_of_isPLHomeomorphOn_boundary_arc D₃ hA' hA'arc hA'frontH hk
      hcut₃.fst_subset hcompatH₃
  have hH₁' : EqOn H (D ∘ f₁) P := by
    intro x hx
    simpa only [Function.comp_apply, hfun₁] using hH₁ hx
  have hH₂' : EqOn H (D ∘ f₂) Q := by
    intro x hx
    simpa only [Function.comp_apply, hfun₂] using hH₂ hx
  have hG₃' : EqOn G (D ∘ f₃) Q' := by
    intro x hx
    simpa only [Function.comp_apply, hfun₃] using hG₃ hx
  exact ⟨H, G, P, Q, P', Q', A', f₁, f₂, h, f₃, hP, hQ, hHdomain, hf₁, hf₂,
    hf₂f₁, hf₁seam, hf₂seam, hH₁', hH₂', rfl, hA', hA'seam, hA'Q, hA'notP, hk,
    hP', hQ', hGdomain, hh, hf₃, hhseam, hf₃seam, hGH, hG₃', hsource⟩

end Producer

end DifferentialGeometry.Topology.PiecewiseLinear
