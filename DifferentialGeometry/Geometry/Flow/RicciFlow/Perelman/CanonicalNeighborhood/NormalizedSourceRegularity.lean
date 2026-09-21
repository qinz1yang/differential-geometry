import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem NormalizedSequence.regular_window_of_higher_good
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (i : ℕ)
    {s : ℝ} (hs : s ∈ Icc (-X.depth i) 0) {y : (X.term i).M}
    (hq : 2 ≤ (X.term i).S.scalar s y)
    (W : WindowedModelWitness eps kappa (X.term i).S y s) :
    Ioo (s - (eps * (X.term i).S.scalar s y)⁻¹) s ⊆ (X.interval i).regular := by
  rw [X.regular_eq i]
  intro t ht
  have hinv : ((X.term i).S.scalar s y)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hdepth : (eps * (X.term i).S.scalar s y)⁻¹ ≤ X.depth i := by
    rw [mul_inv]
    calc
      eps⁻¹ * ((X.term i).S.scalar s y)⁻¹ ≤ eps⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hinv (inv_nonneg.mpr W.eps_pos.le)
      _ = modelDepth eps := by rw [mul_one]; rfl
      _ ≤ X.depth i := X.depth_buffer i
  exact ⟨by linarith [hs.1, ht.1], ht.2.trans_le hs.2⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
