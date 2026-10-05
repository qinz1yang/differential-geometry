import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Distance.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds

noncomputable section

open Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData (I := I) ancientTimeInterval)

local instance movingDistanceTopology : TopologicalSpace F.M := F.topology
local instance movingDistanceCharted : ChartedSpace H F.M := F.charted
local instance movingDistanceSmooth : IsManifold I ∞ F.M := F.smooth
local instance movingDistanceT2 : T2Space F.M := F.t2
local instance movingDistanceSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem IsAncientKappaSolution.absolutelyContinuousOnInterval_moving_distance
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (x y : ℝ → F.M)
    (hx : ContMDiffOn 𝓘(ℝ, ℝ) I 1 x (Icc a b))
    (hy : ContMDiffOn 𝓘(ℝ, ℝ) I 1 y (Icc a b)) :
    AbsolutelyContinuousOnInterval
      (fun t => (riemannianEDistOf (F.S.base.metric (-t)) (x t) (y t)).toReal) a b := by
  let _ : ConnectedSpace F.M := hF.connected
  obtain ⟨K, hK⟩ := ancientKappa_rmNormSqBounded_finrank F hF
  have hreg : Icc ((0 : ℝ) - b) (0 - a) ⊆ ancientTimeInterval.regular := by
    intro t ht
    simpa only [ancientTimeInterval_regular, mem_Iio] using ht.2.trans_lt (by linarith : 0 - a < 0)
  have hRm (t : ℝ) (ht : t ∈ Icc ((0 : ℝ) - b) (0 - a)) (z : F.M) :
      Tensor0SBundle.normSq0S (F.S.base.metric t) z 4 (F.S.base.rm04 t z) ≤ K :=
    hK t (ancientTimeInterval.regular_subset (hreg ht)) z
  simpa only [zero_sub] using
    absolutelyContinuousOnInterval_riemannianEDistOf_toReal_of_normSq0S_rm04_le
      F.S F.isSolution hab hreg hRm x y hx hy

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
