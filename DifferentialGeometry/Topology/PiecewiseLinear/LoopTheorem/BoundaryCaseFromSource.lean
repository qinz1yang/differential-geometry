/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.BoundaryWordWitnessOfCell

open Set Topology
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u v w

namespace BoundaryWordWitness

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  {X : Type v} [TopologicalSpace X] {G : SingularTwoCell M} {ρ : X → M}

private theorem map_source_homotopy {Q : Type w} [TopologicalSpace Q]
    (f : Q → X) (hf : Continuous f) {p q : Q} {a b : X}
    {P₀ P₁ : Path p q} {P₁X P : Path a b}
    (hP : ∀ t, P t = f (P₀ t)) (hP₁X : ∀ t, P₁X t = f (P₁ t))
    (hsource : P₁.Homotopic P₀) : P₁X.Homotopic P := by
  have ha : a = f p := by simpa using hP 0
  have hb : b = f q := by simpa using hP 1
  subst a
  subst b
  have hPeq : P = P₀.map hf := by
    apply Path.ext
    exact funext hP
  have hP₁Xeq : P₁X = P₁.map hf := by
    apply Path.ext
    exact funext hP₁X
  rw [hPeq, hP₁Xeq]
  exact hsource.map ⟨f, hf⟩

private theorem source_homotopic_of_injective_of_range_subset
    {Q : Type w} [TopologicalSpace Q] [T2Space Q] {p q : Q}
    {P₀ P₁ : Path p q} (hP₀ : Function.Injective ⇑P₀)
    (hP₁ : Set.range ⇑P₁ ⊆ Set.range ⇑P₀) : P₁.Homotopic P₀ := by
  have hemb : Topology.IsEmbedding ⇑P₀ :=
    (P₀.continuous.isClosedEmbedding hP₀).toIsEmbedding
  have hmem : ∀ t : unitInterval, P₁ t ∈ Set.range ⇑P₀ := by
    intro t
    exact hP₁ (Set.mem_range_self t)
  obtain ⟨φ, hcont, hzero, hone, happ⟩ :
      ∃ φ : unitInterval → unitInterval, Continuous φ ∧ φ 0 = 0 ∧ φ 1 = 1 ∧
        ∀ t, P₀ (φ t) = P₁ t := by
    refine ⟨fun t => hemb.toHomeomorph.symm ⟨P₁ t, hmem t⟩,
      hemb.toHomeomorph.symm.continuous.comp (P₁.continuous.subtype_mk hmem), ?_, ?_, ?_⟩
    · change hemb.toHomeomorph.symm ⟨P₁ 0, hmem 0⟩ = 0
      have hval : (⟨P₁ 0, hmem 0⟩ : Set.range ⇑P₀) = ⟨P₀ 0, Set.mem_range_self 0⟩ :=
        Subtype.ext (P₁.source.trans P₀.source.symm)
      rw [hval]
      exact hemb.toHomeomorph_symm_apply 0
    · change hemb.toHomeomorph.symm ⟨P₁ 1, hmem 1⟩ = 1
      have hval : (⟨P₁ 1, hmem 1⟩ : Set.range ⇑P₀) = ⟨P₀ 1, Set.mem_range_self 1⟩ :=
        Subtype.ext (P₁.target.trans P₀.target.symm)
      rw [hval]
      exact hemb.toHomeomorph_symm_apply 1
    · intro t
      change P₀ (hemb.toHomeomorph.symm ⟨P₁ t, hmem t⟩) = P₁ t
      obtain ⟨s, hs⟩ := hmem t
      have hval : (⟨P₁ t, hmem t⟩ : Set.range ⇑P₀) = ⟨P₀ s, Set.mem_range_self s⟩ :=
        Subtype.ext hs.symm
      rw [hval, hemb.toHomeomorph_symm_apply s]
      exact hs
  have hre : P₀.reparam φ hcont hzero hone = P₁ := by
    ext t
    exact happ t
  have hhom : P₀.Homotopic (P₀.reparam φ hcont hzero hone) :=
    ⟨Path.Homotopy.reparam P₀ φ hcont hzero hone⟩
  rw [hre] at hhom
  exact hhom.symm

theorem push_source_homotopy {Q : Type w} [TopologicalSpace Q] [T2Space Q]
    (f : Q → X) (hf : Continuous f) {p q : Q} {P₀ P₁ : Path p q}
    (hP₀ : Function.Injective ⇑P₀) (hP₁ : Set.range ⇑P₁ ⊆ Set.range ⇑P₀)
    {a b : X} {P₁X P : Path a b}
    (hP : ∀ t, P t = f (P₀ t)) (hP₁X : ∀ t, P₁X t = f (P₁ t)) :
    P₁X.Homotopic P := by
  exact map_source_homotopy f hf hP hP₁X
    (source_homotopic_of_injective_of_range_subset hP₀ hP₁)

theorem push_source_homotopy_reverse {Q : Type w} [TopologicalSpace Q] [T2Space Q]
    (f : Q → X) (hf : Continuous f) {p q : Q} {P₀ : Path p q} {P₁ : Path q p}
    (hP₀ : Function.Injective ⇑P₀) (hP₁ : Set.range ⇑P₁ ⊆ Set.range ⇑P₀)
    {a b : X} {P₁X : Path b a} {P : Path a b}
    (hP : ∀ t, P t = f (P₀ t)) (hP₁X : ∀ t, P₁X t = f (P₁ t)) :
    P₁X.Homotopic P.symm := by
  have hPrev : ∀ t, P.symm t = f (P₀.symm t) := by
    intro t
    change P (unitInterval.symm t) = f (P₀ (unitInterval.symm t))
    exact hP _
  have hP₁symm : Set.range ⇑P₁ ⊆ Set.range ⇑P₀.symm := by
    rw [P₀.symm_range]
    exact hP₁
  have hP₀symm : Function.Injective ⇑P₀.symm := by
    intro s t hst
    exact unitInterval.symm_bijective.injective (hP₀ hst)
  exact map_source_homotopy f hf hPrev hP₁X
    (source_homotopic_of_injective_of_range_subset hP₀symm hP₁symm)

private theorem witness_of_pushed_two_arcs
    {a b : X} {P : Path a b} {Q : Path b a} {P' : Path a b} {Q' : Path b a}
    (hP : P'.Homotopic P) (hQ : Q'.Homotopic Q)
    (e : loopCircle ≃ₜ frontier G.domain)
    {α : Path (ρ a) (ρ b)} {ω : Path (ρ b) (ρ a)}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : ∀ t, α t = ρ (P' t)) (hω : ∀ t, ω t = ρ (Q' t)) :
    ∃ W : BoundaryWordWitness G ρ (pathToCircle (P.trans Q)), W.param = e := by
  let loop₁ := pathToCircle (P'.trans Q')
  have hreal : ∀ θ, ρ (loop₁ θ) = G (e θ) := by
    intro θ
    rw [hparam θ]
    exact (pathToCircle_eq_of_forall (P'.trans Q') (α.trans ω)
      (trans_apply_eq_map (f := ρ) (fun t => by rw [hα t])
        (fun t => by rw [hω t])) θ).symm
  exact ⟨{
    param := e
    loop := loop₁
    realizes := hreal
    homotopic := pathToCircle_homotopic (hP.hcomp hQ) }, rfl⟩

theorem exists_of_sourceDirectMatch_reversing
    {Q : Type w} [TopologicalSpace Q] [T2Space Q]
    (f : Q → X) (hf : Continuous f)
    {p q p' q' : Q} (σ₀ : Path p q) (υ₀ : Path p' q')
    (hσ₀ : Function.Injective ⇑σ₀) (hυ₀ : Function.Injective ⇑υ₀)
    {σ₁ : Path p q} {υ₁ : Path p' q'}
    (hσ₁ : Set.range ⇑σ₁ ⊆ Set.range ⇑σ₀)
    (hυ₁ : Set.range ⇑υ₁ ⊆ Set.range ⇑υ₀)
    {a b : X} {σ υ : Path a b} {σX υX : Path a b}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hσX : ∀ t, σX t = f (σ₁ t)) (hυX : ∀ t, υX t = f (υ₁ t))
    (e : loopCircle ≃ₜ frontier G.domain)
    {α : Path (ρ a) (ρ b)} {ω : Path (ρ b) (ρ a)}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : ∀ t, α t = ρ (σX t)) (hω : ∀ t, ω t = ρ (υX.symm t)) :
    ∃ W : BoundaryWordWitness G ρ (pathToCircle (σ.trans υ.symm)), W.param = e := by
  have hσhom := push_source_homotopy f hf hσ₀ hσ₁ hσ hσX
  have hυrange : Set.range ⇑υ₁.symm ⊆ Set.range ⇑υ₀ := by
    rw [Path.symm_range]
    exact hυ₁
  have hυXrev : ∀ t, υX.symm t = f (υ₁.symm t) := by
    intro t
    change υX (unitInterval.symm t) = f (υ₁ (unitInterval.symm t))
    exact hυX _
  have hυhom := push_source_homotopy_reverse f hf hυ₀ hυrange hυ hυXrev
  exact witness_of_pushed_two_arcs (P := σ) (Q := υ.symm) (P' := σX)
    (Q' := υX.symm) hσhom hυhom e hparam hα hω

theorem exists_of_sourceDirectMatch_preserving
    {Q : Type w} [TopologicalSpace Q] [T2Space Q]
    (f : Q → X) (hf : Continuous f)
    {p q p' q' : Q} (σ₀ : Path p q) (υ₀ : Path p' q')
    (hσ₀ : Function.Injective ⇑σ₀) (hυ₀ : Function.Injective ⇑υ₀)
    {σ₁ : Path p q} {υ₁ : Path p' q'}
    (hσ₁ : Set.range ⇑σ₁ ⊆ Set.range ⇑σ₀)
    (hυ₁ : Set.range ⇑υ₁ ⊆ Set.range ⇑υ₀)
    {a b : X} {σ : Path a b} {υ : Path b a} {σX : Path a b} {υX : Path b a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hυ : ∀ t, υ t = f (υ₀ t))
    (hσX : ∀ t, σX t = f (σ₁ t)) (hυX : ∀ t, υX t = f (υ₁ t))
    (e : loopCircle ≃ₜ frontier G.domain)
    {α : Path (ρ a) (ρ b)} {ω : Path (ρ b) (ρ a)}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : ∀ t, α t = ρ (σX t)) (hω : ∀ t, ω t = ρ (υX t)) :
    ∃ W : BoundaryWordWitness G ρ (pathToCircle (σ.trans υ)), W.param = e := by
  have hσhom := push_source_homotopy f hf hσ₀ hσ₁ hσ hσX
  have hυhom := push_source_homotopy f hf hυ₀ hυ₁ hυ hυX
  exact witness_of_pushed_two_arcs (P := σ) (Q := υ) (P' := σX) (Q' := υX)
    hσhom hυhom e hparam hα hω

theorem exists_of_sourceCrossMatch_reversing
    {Q : Type w} [TopologicalSpace Q] [T2Space Q]
    (f : Q → X) (hf : Continuous f)
    {p q u v : Q} (σ₀ : Path p q) (τ₀ : Path q u)
    (υ₀ : Path u v) (φ₀ : Path v p)
    (hσ₀ : Function.Injective ⇑σ₀) (hτ₀ : Function.Injective ⇑τ₀)
    (hυ₀ : Function.Injective ⇑υ₀) (hφ₀ : Function.Injective ⇑φ₀)
    {σ₁ : Path p q} {τ₁ : Path q u} {υ₁ : Path u v} {φ₁ : Path v p}
    (hσ₁ : Set.range ⇑σ₁ ⊆ Set.range ⇑σ₀)
    (hτ₁ : Set.range ⇑τ₁ ⊆ Set.range ⇑τ₀)
    (hυ₁ : Set.range ⇑υ₁ ⊆ Set.range ⇑υ₀)
    (hφ₁ : Set.range ⇑φ₁ ⊆ Set.range ⇑φ₀)
    {a b : X} {σ υ : Path a b} {τ φ : Path b a}
    {τX φX : Path b a} {σX υX : Path a b}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t))
    (hυ : ∀ t, υ t = f (υ₀ t)) (hφ : ∀ t, φ t = f (φ₀ t))
    (hτX : ∀ t, τX t = f (τ₁ t)) (hσX : ∀ t, σX t = f (σ₁ t))
    (hφX : ∀ t, φX t = f (φ₁ t)) (hυX : ∀ t, υX t = f (υ₁ t))
    (e : loopCircle ≃ₜ frontier G.domain)
    {α : Path (ρ b) (ρ a)} {ω : Path (ρ a) (ρ b)}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : ∀ t, α t = ρ ((τX.trans (σX.trans φX)) t))
    (hω : ∀ t, ω t = ρ (υX t)) :
    ∃ W : BoundaryWordWitness G ρ
      (pathToCircle (σ.trans (φ.trans (υ.trans τ)))), W.param = e := by
  have hσhom := push_source_homotopy f hf hσ₀ hσ₁ hσ hσX
  have hτhom := push_source_homotopy f hf hτ₀ hτ₁ hτ hτX
  have hυhom := push_source_homotopy f hf hυ₀ hυ₁ hυ hυX
  have hφhom := push_source_homotopy f hf hφ₀ hφ₁ hφ hφX
  have hlong := hτhom.hcomp (hσhom.hcomp hφhom)
  obtain ⟨W, hW⟩ := witness_of_pushed_two_arcs (P := τ.trans (σ.trans φ)) (Q := υ)
    (P' := τX.trans (σX.trans φX)) (Q' := υX) hlong hυhom e hparam hα hω
  have hrot₂ := pathToCircle_homotopic
    (Path.Homotopic.trans_assoc τ (σ.trans φ) υ)
  have hrot₃ := pathToCircle_trans_homotopic_comm τ ((σ.trans φ).trans υ)
  have hrot₄ := pathToCircle_homotopic
    (Path.Homotopic.trans_assoc (σ.trans φ) υ τ)
  have hrot₅ := pathToCircle_homotopic
    (Path.Homotopic.trans_assoc σ φ (υ.trans τ))
  exact ⟨W.ofHomotopicWord (((hrot₂.trans hrot₃).trans hrot₄).trans hrot₅), hW⟩

theorem exists_of_sourceCrossMatch_preserving
    {Q : Type w} [TopologicalSpace Q] [T2Space Q]
    (f : Q → X) (hf : Continuous f)
    {p q u v : Q} (σ₀ : Path p q) (τ₀ : Path q u)
    (υ₀ : Path u v) (φ₀ : Path v p)
    (hσ₀ : Function.Injective ⇑σ₀) (hτ₀ : Function.Injective ⇑τ₀)
    (hυ₀ : Function.Injective ⇑υ₀) (hφ₀ : Function.Injective ⇑φ₀)
    {σ₁ : Path p q} {τ₁ : Path q u} {υ₁ : Path u v} {φ₁ : Path v p}
    (hσ₁ : Set.range ⇑σ₁ ⊆ Set.range ⇑σ₀)
    (hτ₁ : Set.range ⇑τ₁ ⊆ Set.range ⇑τ₀)
    (hυ₁ : Set.range ⇑υ₁ ⊆ Set.range ⇑υ₀)
    (hφ₁ : Set.range ⇑φ₁ ⊆ Set.range ⇑φ₀)
    {a b : X} {σ : Path a b} {τ : Path b b} {υ : Path b a} {φ : Path a a}
    {σX : Path a b} {τX : Path b b} {υX : Path b a} {φX : Path a a}
    (hσ : ∀ t, σ t = f (σ₀ t)) (hτ : ∀ t, τ t = f (τ₀ t))
    (hυ : ∀ t, υ t = f (υ₀ t)) (hφ : ∀ t, φ t = f (φ₀ t))
    (hτX : ∀ t, τX t = f (τ₁ t)) (hσX : ∀ t, σX t = f (σ₁ t))
    (hφX : ∀ t, φX t = f (φ₁ t)) (hυX : ∀ t, υX t = f (υ₁ t))
    (e : loopCircle ≃ₜ frontier G.domain)
    {α : Path (ρ a) (ρ b)} {ω : Path (ρ b) (ρ a)}
    (hparam : ∀ θ, G (e θ) = pathToCircle (α.trans ω) θ)
    (hα : ∀ t, α t = ρ ((φX.symm.trans (σX.trans τX.symm)) t))
    (hω : ∀ t, ω t = ρ (υX t)) :
    ∃ W : BoundaryWordWitness G ρ
      (pathToCircle (σ.trans (τ.symm.trans (υ.trans φ.symm)))), W.param = e := by
  have hσhom := push_source_homotopy f hf hσ₀ hσ₁ hσ hσX
  have hτrange : Set.range ⇑τ₁.symm ⊆ Set.range ⇑τ₀ := by
    rw [Path.symm_range]
    exact hτ₁
  have hτXrev : ∀ t, τX.symm t = f (τ₁.symm t) := by
    intro t
    change τX (unitInterval.symm t) = f (τ₁ (unitInterval.symm t))
    exact hτX _
  have hτhom := push_source_homotopy_reverse f hf hτ₀ hτrange hτ hτXrev
  have hυhom := push_source_homotopy f hf hυ₀ hυ₁ hυ hυX
  have hφrange : Set.range ⇑φ₁.symm ⊆ Set.range ⇑φ₀ := by
    rw [Path.symm_range]
    exact hφ₁
  have hφXrev : ∀ t, φX.symm t = f (φ₁.symm t) := by
    intro t
    change φX (unitInterval.symm t) = f (φ₁ (unitInterval.symm t))
    exact hφX _
  have hφhom := push_source_homotopy_reverse f hf hφ₀ hφrange hφ hφXrev
  have hlong := hφhom.hcomp (hσhom.hcomp hτhom)
  obtain ⟨W, hW⟩ := witness_of_pushed_two_arcs
    (P := φ.symm.trans (σ.trans τ.symm)) (Q := υ)
    (P' := φX.symm.trans (σX.trans τX.symm)) (Q' := υX)
    hlong hυhom e hparam hα hω
  have hrot₂ := pathToCircle_homotopic
    (Path.Homotopic.trans_assoc φ.symm (σ.trans τ.symm) υ)
  have hrot₃ := pathToCircle_trans_homotopic_comm φ.symm ((σ.trans τ.symm).trans υ)
  have hrot₄ := pathToCircle_homotopic
    (Path.Homotopic.trans_assoc (σ.trans τ.symm) υ φ.symm)
  have hrot₅ := pathToCircle_homotopic
    (Path.Homotopic.trans_assoc σ τ.symm (υ.trans φ.symm))
  exact ⟨W.ofHomotopicWord (((hrot₂.trans hrot₃).trans hrot₄).trans hrot₅), hW⟩

end BoundaryWordWitness

end DifferentialGeometry.Topology.PiecewiseLinear
