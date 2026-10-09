import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Orientation

set_option autoImplicit false
noncomputable section
open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {n : ℕ} {A B C : Type*}
  [TopologicalSpace A] [ChartedSpace (EuclideanSpace ℝ (Fin n)) A]
  [TopologicalSpace B] [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [TopologicalSpace C] [ChartedSpace (EuclideanSpace ℝ (Fin n)) C]
  [IsManifold (𝓡 n) ∞ A] [IsManifold (𝓡 n) ∞ B] [IsManifold (𝓡 n) ∞ C]

theorem local_orientation_of_comp_eq_at
    (f : A → B) (g : B → C) (h : A → C)
    (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f)
    (hg : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ g)
    (hh : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ h)
    (heq : g ∘ f = h)
    (oA : ManifoldOrientation (𝓡 n) A n) (oB : ManifoldOrientation (𝓡 n) B n)
    (oC : ManifoldOrientation (𝓡 n) C n) (x : A)
    (hfo : Orientation.map (Fin n) (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (oA.orientation x) = oB.orientation (f x))
    (hho : Orientation.map (Fin n) (hh.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (oA.orientation x) = oC.orientation (h x)) :
    Orientation.map (Fin n) (hg.mfderivToContinuousLinearEquiv (by simp) (f x)).toLinearEquiv
      (oB.orientation (f x)) = oC.orientation (g (f x)) := by
  have hlin : (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.trans
      (hg.mfderivToContinuousLinearEquiv (by simp) (f x)).toLinearEquiv =
      (hh.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 n) (𝓡 n) g (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) = mfderiv (𝓡 n) (𝓡 n) h x v
    rw [← mfderiv_comp_apply x (hg.mdifferentiable (by simp) _) (hf.mdifferentiable (by simp) _) v]
    exact congrArg (fun k : A → C => mfderiv (𝓡 n) (𝓡 n) k x v) heq
  rw [← hfo]
  erw [DifferentialGeometry.VectorBundle.map_orientation_trans_between, hlin]
  have hp : g (f x) = h x := congrFun heq x
  rw [hp]
  exact hho

theorem local_orientation_of_comp
    (f : A → B) (g : B → C) (h : A → C)
    (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f)
    (hg : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ g)
    (hh : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ h)
    (heq : g ∘ f = h)
    (oA : ManifoldOrientation (𝓡 n) A n) (oB : ManifoldOrientation (𝓡 n) B n)
    (oC : ManifoldOrientation (𝓡 n) C n)
    (hgo : ∀ y, Orientation.map (Fin n) (hg.mfderivToContinuousLinearEquiv (by simp) y).toLinearEquiv
      (oB.orientation y) = oC.orientation (g y))
    (hho : ∀ x, Orientation.map (Fin n) (hh.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (oA.orientation x) = oC.orientation (h x)) :
    ∀ x, Orientation.map (Fin n) (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (oA.orientation x) = oB.orientation (f x) := by
  intro x
  let L := (hg.mfderivToContinuousLinearEquiv (by simp) (f x)).toLinearEquiv
  apply (Orientation.map (Fin n) L).injective
  have hlin : (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.trans L =
      (hh.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    change mfderiv (𝓡 n) (𝓡 n) g (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) = mfderiv (𝓡 n) (𝓡 n) h x v
    rw [← mfderiv_comp_apply x (hg.mdifferentiable (by simp) _) (hf.mdifferentiable (by simp) _) v]
    exact congrArg (fun k : A → C => mfderiv (𝓡 n) (𝓡 n) k x v) heq
  erw [DifferentialGeometry.VectorBundle.map_orientation_trans_between, hlin, hho, hgo]
  congr 1
  exact (congrFun heq x).symm

variable [ConnectedSpace A]

theorem localDiffeomorph_orientation_of_eq_at
    (f : A → B) (hf : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ f) (hi : Injective f)
    (oA : ManifoldOrientation (𝓡 n) A n) (oB : ManifoldOrientation (𝓡 n) B n) (x₀ : A)
    (h0 : Orientation.map (Fin n) (hf.mfderivToContinuousLinearEquiv (by simp) x₀).toLinearEquiv
      (oA.orientation x₀) = oB.orientation (f x₀)) :
    ∀ x, Orientation.map (Fin n) (hf.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
      (oA.orientation x) = oB.orientation (f x) := by
  rcases localDiffeomorph_orientation_dichotomy f hf hi oA oB with hp | hn
  · exact hp
  · have heq := h0.symm.trans (hn x₀)
    exact False.elim (Module.Ray.ne_neg_self _ heq)

end DifferentialGeometry.Topology.Manifold
