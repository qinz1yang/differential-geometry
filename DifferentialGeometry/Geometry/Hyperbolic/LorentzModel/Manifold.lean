import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.UpperSheet
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.IsometrySmooth
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.ProjectiveOrthogonalGroup
import Mathlib.Geometry.Manifold.Algebra.SMul

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Hyperbolic.HUpper

instance (n : ℕ) : ChartedSpace (EuclideanSpace ℝ (Fin n)) (HUpper n) :=
  Manifold.Homeomorph.pullbackChartedSpace (Hyperboloid.hUpperIsometryEquiv n).toHomeomorph

instance (n : ℕ) : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ω (HUpper n) :=
  Manifold.Homeomorph.instIsManifoldPullback (Hyperboloid.hUpperIsometryEquiv n).toHomeomorph

end DifferentialGeometry.Hyperbolic.HUpper

namespace DifferentialGeometry.Hyperboloid

def hUpperDiffeomorph (n : ℕ) (r : ℕ∞ω := ∞) :
    Hyperbolic.HUpper n ≃ₘ^r⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ Hyperboloid (EuclideanSpace ℝ (Fin n)) :=
  Manifold.Homeomorph.pullbackDiffeomorph (hUpperIsometryEquiv n).toHomeomorph

@[simp] theorem hUpperDiffeomorph_apply (n : ℕ) (r : ℕ∞ω) (x : Hyperbolic.HUpper n) :
    hUpperDiffeomorph n r x = hUpperIsometryEquiv n x := rfl

@[simp] theorem hUpperDiffeomorph_symm_apply (n : ℕ) (r : ℕ∞ω)
    (x : Hyperboloid (EuclideanSpace ℝ (Fin n))) :
    (hUpperDiffeomorph n r).symm x = (hUpperIsometryEquiv n).symm x := rfl

@[simp] theorem hUpperDiffeomorph_toHomeomorph (n : ℕ) (r : ℕ∞ω) :
    (hUpperDiffeomorph n r).toHomeomorph = (hUpperIsometryEquiv n).toHomeomorph := rfl

end DifferentialGeometry.Hyperboloid

namespace DifferentialGeometry.HyperbolicAction

open ProjectiveOrthogonalGroup (PO)

theorem contMDiff_po_smul (n : ℕ) (r : ℕ∞ω) (q : PO (n + 1) 1) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) r
      ((poMulAction (by omega : 1 ≤ n + 1)).smul q) := by
  let J := Hyperboloid.hUpperDiffeomorph (n + 1) r
  let A := (Hyperboloid.projectiveOrthogonalGroupEquiv n).symm q
  have hs := J.symm.contMDiff.comp ((Hyperboloid.contMDiff_isometryEquiv (n := r) A).comp J.contMDiff)
  apply hs.congr
  intro x
  symm
  change (Hyperboloid.hUpperIsometryEquiv (n + 1)).symm
    (A (Hyperboloid.hUpperIsometryEquiv (n + 1) x)) = _
  rw [Hyperboloid.projectiveOrthogonalGroupEquiv_symm_apply,
    (Hyperboloid.hUpperIsometryEquiv (n + 1)).symm_apply_apply]

theorem contMDiffConstSMul_poMulAction (n : ℕ) (r : ℕ∞ω) :
    letI : MulAction (PO (n + 1) 1) (Hyperbolic.HUpper (n + 1)) := poMulAction (by omega)
    ContMDiffConstSMul 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))) r
      (PO (n + 1) 1) (Hyperbolic.HUpper (n + 1)) := by
  let : MulAction (PO (n + 1) 1) (Hyperbolic.HUpper (n + 1)) := poMulAction (by omega)
  exact ⟨contMDiff_po_smul n r⟩

end DifferentialGeometry.HyperbolicAction
