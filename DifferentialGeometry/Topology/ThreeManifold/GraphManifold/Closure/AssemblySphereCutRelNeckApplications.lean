import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelNeck
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeams

/-!
# Consumer of the neck profile: the reparametrised seam collar

`SphereSeam.neckCollar S h`: the signed collar of a sphere seam with its normal coordinate
reparametrised by a diffeomorphism `h` of the line, `(z, s) ↦ S.collar (z, h s)`, as a partial
diffeomorphism with source `h⁻¹ (-1, 1)` and the same target. The placed fibre plug is mapped onto
the neck of `W` through it, with `h` the neck profile of `exists_neckProfile`
(`exists_neckCollar`: both shell germs are realised by one partial diffeomorphism).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- The seam collar with its normal coordinate reparametrised by `h`. -/
def SphereSeam.neckCollar {W : CompactCarrier.{u}} (S : SphereSeam W)
    (h : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ) :
    PartialDiffeomorph sphereSignedCollarModel W.model (ClosureSphere.{u} × ℝ) W.Carrier ∞ :=
  ((Diffeomorph.refl (𝓡 2) ClosureSphere.{u} ∞).prodCongr h).toPartialDiffeomorph.trans S.collar

namespace SphereSeam

variable {W : CompactCarrier.{u}} (S : SphereSeam W) (h : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ)

theorem neckCollar_apply (p : ClosureSphere.{u} × ℝ) :
    S.neckCollar h p = S.collar (p.1, h p.2) := rfl

theorem neckCollar_source : (S.neckCollar h).source = univ ×ˢ (h ⁻¹' Ioo (-1) 1) := by
  ext p
  change (p ∈ univ ∧ (p.1, h p.2) ∈ S.collar.source) ↔ _
  rw [S.source_eq]
  simp [sphereSignedCollarSource]

theorem neckCollar_target : (S.neckCollar h).target = S.collar.target := by
  ext w
  change (w ∈ S.collar.target ∧ _ ∈ univ) ↔ _
  simp

end SphereSeam

/-- **Neck collar with two shell germs.** For positive slopes, a gap condition and offsets of
opposite signs, there is one partial diffeomorphism onto the seam collar which is
`(z, s) ↦ S.collar (z, c₀ + m₀ s)` for `s ≥ a` and `(z, s) ↦ S.collar (z, c₁ + m₁ s)` for `s ≤ -a`,
wherever these heights are in `(-1, 1)`. -/
theorem exists_neckCollar {W : CompactCarrier.{u}} (S : SphereSeam W) {a m₀ m₁ c₀ c₁ : ℝ}
    (ha : 0 < a) (hm₀ : 0 < m₀) (hm₁ : 0 < m₁) (hc₀ : 0 ≤ c₀) (hc₁ : c₁ ≤ 0)
    (hgap : |m₀ - m₁| * a ≤ c₀ - c₁) :
    ∃ N : PartialDiffeomorph sphereSignedCollarModel W.model (ClosureSphere.{u} × ℝ) W.Carrier ∞,
      N.target = S.collar.target ∧
      (∀ z s, a ≤ s → c₀ + m₀ * s < 1 →
        (z, s) ∈ N.source ∧ N (z, s) = S.collar (z, c₀ + m₀ * s)) ∧
      ∀ z s, s ≤ -a → -1 < c₁ + m₁ * s →
        (z, s) ∈ N.source ∧ N (z, s) = S.collar (z, c₁ + m₁ * s) := by
  obtain ⟨h, -, h₀, h₁⟩ := exists_neckProfile ha hm₀ hm₁ hgap
  refine ⟨S.neckCollar h, S.neckCollar_target h, fun z s hs hs1 => ?_, fun z s hs hs1 => ?_⟩
  · have he := h₀ s hs
    refine ⟨?_, by rw [S.neckCollar_apply, he]⟩
    rw [S.neckCollar_source]
    refine ⟨mem_univ _, ?_, ?_⟩
    · change -1 < h s
      rw [he]
      nlinarith
    · change h s < 1
      rw [he]
      exact hs1
  · have he := h₁ s hs
    refine ⟨?_, by rw [S.neckCollar_apply, he]⟩
    rw [S.neckCollar_source]
    refine ⟨mem_univ _, ?_, ?_⟩
    · change -1 < h s
      rw [he]
      exact hs1
    · change h s < 1
      rw [he]
      nlinarith

end GC.GraphManifold.Assembly
