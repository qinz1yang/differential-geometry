import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCircleIsotopy

/-!
# Consumer of D2S1 input (b1): the isotopy from the identity

Time-reversed form of `exists_circleIsotopy_of_preservesOrientation`: an orientation-preserving
diffeomorphism of the circle is reached from the identity by a jointly smooth isotopy (inverses
jointly smooth), the identity for `t < ε` and `f` for `t > 1 − ε` — the endpoint convention of the
disk input (b).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

/-- `Diff⁺(S¹)` is connected, isotopy from the identity to `f`. -/
theorem exists_circleIsotopy_from_refl_of_preservesOrientation
    (o : ManifoldOrientation (𝓡 1) Circle 1)
    (f : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) (hf : f.preservesOrientation o o) :
    ∃ K : ℝ → (Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle),
      ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 1) ∞ (fun x : Circle × ℝ => K x.2 x.1) ∧
      ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 1) ∞ (fun x : Circle × ℝ => (K x.2).symm x.1) ∧
      ∃ ε : ℝ, 0 < ε ∧ (∀ t x, t < ε → K t x = x) ∧ (∀ t x, 1 - ε < t → K t x = f x) := by
  obtain ⟨L, hL, hLi, ε, hε, hlo, hhi⟩ := exists_circleIsotopy_of_preservesOrientation o f hf
  have hrev : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
      (fun x : Circle × ℝ => (x.1, 1 - x.2)) :=
    contMDiff_fst.prodMk (contMDiff_const.sub contMDiff_snd)
  refine ⟨fun t => L (1 - t), hL.comp hrev, hLi.comp hrev, ε, hε, fun t x ht => ?_,
    fun t x ht => ?_⟩
  · exact hhi (1 - t) x (by linarith)
  · exact hlo (1 - t) x (by linarith)

end GC.GraphManifold.Assembly
