import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.BoundaryFaithfulness
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace DifferentialGeometry.Hyperboloid

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem eq_of_boundaryHomeomorph_eq (hdim : 2 ≤ Module.rank ℝ E)
    {f g : Hyperboloid E ≃ᵢ Hyperboloid F}
    (hfg : boundaryHomeomorph f = boundaryHomeomorph g) : f = g := by
  have hb : boundaryHomeomorph (f.trans g.symm) =
      boundaryHomeomorph (IsometryEquiv.refl (Hyperboloid E)) := by
    rw [boundaryHomeomorph_trans, ← boundaryHomeomorph_symm, hfg, boundaryHomeomorph_refl]
    exact Homeomorph.self_trans_symm (boundaryHomeomorph g)
  have he := boundaryHomeomorph_injective hdim hb
  apply IsometryEquiv.ext
  intro x
  have hx := congrArg (fun k : Hyperboloid E ≃ᵢ Hyperboloid E => g (k x)) he
  change g (g.symm (f x)) = g x at hx
  simpa only [g.apply_symm_apply] using hx

variable {G K : Type*} [Group G] [Group K]
  [MulAction G (Hyperboloid E)] [IsIsometricSMul G (Hyperboloid E)]
  [MulAction K (Hyperboloid F)] [IsIsometricSMul K (Hyperboloid F)]

theorem isometryEquiv_smul_of_boundary_equivariant
    (hdim : 2 ≤ Module.rank ℝ E) (e : Hyperboloid E ≃ᵢ Hyperboloid F) (φ : G → K)
    (he : ∀ γ ξ, boundaryHomeomorph e
      (boundaryHomeomorph (IsometryEquiv.constSMul γ) ξ) =
        boundaryHomeomorph (IsometryEquiv.constSMul (φ γ)) (boundaryHomeomorph e ξ))
    (γ : G) (x : Hyperboloid E) : e (γ • x) = φ γ • e x := by
  let a : Hyperboloid E ≃ᵢ Hyperboloid E := IsometryEquiv.constSMul γ
  let b : Hyperboloid F ≃ᵢ Hyperboloid F := IsometryEquiv.constSMul (φ γ)
  have hab : a.trans e = e.trans b := by
    apply eq_of_boundaryHomeomorph_eq hdim
    rw [boundaryHomeomorph_trans, boundaryHomeomorph_trans]
    apply Homeomorph.ext
    intro ξ
    exact he γ ξ
  exact congrArg (fun f : Hyperboloid E ≃ᵢ Hyperboloid F => f x) hab

end DifferentialGeometry.Hyperboloid
