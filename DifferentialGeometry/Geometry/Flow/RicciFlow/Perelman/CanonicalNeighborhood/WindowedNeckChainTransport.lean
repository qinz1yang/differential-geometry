import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedStrongNeckTransport
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem OrderedNeckChain.exists_windowed_transport_tolerance
    {P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval}
    [PreconnectedSpace P.M] {alpha : ℝ} {V : Set P.M}
    (chain : OrderedNeckChain P.S (neckModelTolerance alpha) 0 V)
    (ha : 0 < alpha) (hsmall : alpha < 1 / 32) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D)
        (delta kappa : ℝ) (x : M) (t : ℝ)
        (W : WindowedModelWitness delta kappa S x t), delta ≤ delta₀ →
        IsSolutionOn S → Ioo (t - (delta * S.scalar t x)⁻¹) t ⊆ D.regular →
        ∀ hmodel : W.model = P,
          ∃ necks : ∀ i, StrongNeck S (2 * alpha)
              (W.embedding (hmodel.symm ▸ chain.centers i)) t,
            ∀ i, (necks i).map = (hmodel.symm ▸ (chain.necks i).map).trans W.embedding := by
  classical
  choose d hdpos hd using fun i => (chain.necks i).exists_windowed_transport_tolerance ha hsmall
  have hn : (Finset.univ : Finset (Fin chain.count)).Nonempty :=
    ⟨⟨0, chain.count_pos⟩, Finset.mem_univ _⟩
  let delta₀ := Finset.univ.inf' hn d
  have hpos : 0 < delta₀ := (Finset.lt_inf'_iff _).mpr fun i _ => hdpos i
  refine ⟨delta₀, hpos, ?_⟩
  intro M _ _ _ _ _ D S delta kappa x t W hdelta hS hreg hmodel
  have hdi (i : Fin chain.count) : delta ≤ d i :=
    hdelta.trans (Finset.inf'_le _ (Finset.mem_univ i))
  choose necks hmap using fun i => hd i M D S delta kappa x t W (hdi i) hS hreg hmodel
  exact ⟨necks, hmap⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
