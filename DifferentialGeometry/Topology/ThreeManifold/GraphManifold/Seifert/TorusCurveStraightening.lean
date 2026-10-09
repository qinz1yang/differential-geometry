import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusCurveAnnulus
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusBigonHeight
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TorusAxesChart

/-!
# Torus curves: straightening the first circle

Chapter 6, packet K08, lane MC4 of the `TorusMappingClassLinear` programme, stage (i) and the
assembly of stages (i)–(iii) (review 12, §4.1, §4.2, §4.6).

Stage (i) (`exists_isotopic_height_one_of_push`): for `φ` with matrix `1`, choose a regular
height `s` (MC2, `exists_isRegularHeight`); its level set is finite (`IsRegularHeight.finite`).
By strong induction on the crossing count, while `φ (α)` meets `α_s` the push of MC2
(`exists_isotopic_ncard_lt`) gives an isotopic map, still with matrix `1` by isotopy invariance
of the matrix and regular at `s`, with strictly fewer crossings; once the level set is empty,
stage (ii) applies (`exists_isotopic_height_one_of_forall_ne_of_push`). The hypothesis `hann` is
the annulus vertical-cut push of MC2 (one empty bigon of `φ (α)` against a vertical circle,
removed by a push supported in the cut annulus), still to be delivered by that lane.

Assembly (`isotopic_refl_of_torusMatrix_eq_one_of_push`): stage (i) gives `φ (α) ⊆ α`, the
normal form of MC1 the identity near `α`, stage (iii) (`exists_isotopic_eqOn_nhds_axes_of_push`,
hypothesis `hrel`: the relative push of `φ (β)` against a vertical circle, supported away from
`α`) the identity near `α ∪ β`, and the disc chart of MC3 the isotopy to the identity.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

namespace GC.Seifert

open AnnulusStraightening

theorem exists_isotopic_height_one_of_push
    (hann : ∀ φ : TDiff, torusMatrix φ = 1 → ∀ s : Circle, (∀ z, heightOnCircle φ z ≠ s) →
      ∀ θ : Circle, (∀ z, (φ (alphaCircle z)).1 = θ →
        mfderiv (𝓡 1) (𝓡 1) (fun z => (φ (alphaCircle z)).1) z ≠ 0) →
      HasSameSideArcIn (fun z => (φ (alphaCircle z)).1) θ univ →
      ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ (∀ z, heightOnCircle ψ z ≠ s) ∧
        (∀ z, (ψ (alphaCircle z)).1 = θ →
          mfderiv (𝓡 1) (𝓡 1) (fun z => (ψ (alphaCircle z)).1) z ≠ 0) ∧
        {z | (ψ (alphaCircle z)).1 = θ}.ncard < {z | (φ (alphaCircle z)).1 = θ}.ncard)
    (φ : TDiff) (h : torusMatrix φ = 1) :
    ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ ∀ z, heightOnCircle ψ z = 1 := by
  obtain ⟨s, hs⟩ := exists_isRegularHeight φ
  have key : ∀ n : ℕ, ∀ φ : TDiff, torusMatrix φ = 1 → IsRegularHeight φ s →
      {z | heightOnCircle φ z = s}.ncard = n →
      ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ ∀ z, heightOnCircle ψ z = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro φ h hs hn
      by_cases hne : ∃ z, heightOnCircle φ z = s
      · obtain ⟨ψ, hφψ, hs', hlt⟩ := exists_isotopic_ncard_lt φ h hs hne
        obtain ⟨χ, hψχ, hχ⟩ := ih _ (hn ▸ hlt) ψ
          (by rw [← torusMatrix_eq_of_isotopic hφψ, h]) hs' rfl
        exact ⟨χ, hφψ.trans hψχ, hχ⟩
      · exact exists_isotopic_height_one_of_forall_ne_of_push hann φ h
          (fun z hz => hne ⟨z, hz⟩)
  exact key _ φ h hs rfl

theorem isotopic_refl_of_torusMatrix_eq_one_of_push
    (hann : ∀ φ : TDiff, torusMatrix φ = 1 → ∀ s : Circle, (∀ z, heightOnCircle φ z ≠ s) →
      ∀ θ : Circle, (∀ z, (φ (alphaCircle z)).1 = θ →
        mfderiv (𝓡 1) (𝓡 1) (fun z => (φ (alphaCircle z)).1) z ≠ 0) →
      HasSameSideArcIn (fun z => (φ (alphaCircle z)).1) θ univ →
      ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧ (∀ z, heightOnCircle ψ z ≠ s) ∧
        (∀ z, (ψ (alphaCircle z)).1 = θ →
          mfderiv (𝓡 1) (𝓡 1) (fun z => (ψ (alphaCircle z)).1) z ≠ 0) ∧
        {z | (ψ (alphaCircle z)).1 = θ}.ncard < {z | (φ (alphaCircle z)).1 = θ}.ncard)
    (hrel : ∀ φ : TDiff, torusMatrix φ = 1 → ∀ U : Set Torus, IsOpen U →
      range alphaCircle ⊆ U → (∀ p ∈ U, φ p = p) → ∀ s : Circle,
      (∀ w, (φ (betaCircle w)).1 = s →
        mfderiv (𝓡 1) (𝓡 1) (fun w => (φ (betaCircle w)).1) w ≠ 0) →
      HasSameSideArcIn (fun w => (φ (betaCircle w)).1) s (Icc 0 1) →
      ∃ ψ : TDiff, IsotopicDiffeomorph φ ψ ∧
        (∃ U' : Set Torus, IsOpen U' ∧ range alphaCircle ⊆ U' ∧ ∀ p ∈ U', ψ p = p) ∧
        (∀ w, (ψ (betaCircle w)).1 = s →
          mfderiv (𝓡 1) (𝓡 1) (fun w => (ψ (betaCircle w)).1) w ≠ 0) ∧
        {w | (ψ (betaCircle w)).1 = s}.ncard < {w | (φ (betaCircle w)).1 = s}.ncard)
    (φ : TDiff) (h : torusMatrix φ = 1) : IsotopicDiffeomorph φ torusRefl := by
  obtain ⟨ψ₁, h₁, hα₁⟩ := exists_isotopic_height_one_of_push hann φ h
  have hm₁ : torusMatrix ψ₁ = 1 := by rw [← torusMatrix_eq_of_isotopic h₁, h]
  obtain ⟨ψ₂, h₂, U, hU, hαU, hψ₂U⟩ := exists_isotopic_eqOn_nhds_alpha ψ₁ hm₁ hα₁
  have hm₂ : torusMatrix ψ₂ = 1 := by rw [← torusMatrix_eq_of_isotopic h₂, hm₁]
  obtain ⟨ψ₃, h₃, V, hV, hαβV, hψ₃V⟩ :=
    exists_isotopic_eqOn_nhds_axes_of_push hrel ψ₂ hm₂ hU hαU hψ₂U
  exact h₁.trans (h₂.trans (h₃.trans (isotopic_refl_of_eqOn_nhds_axes ψ₃ hV hαβV hψ₃V)))

end GC.Seifert
