import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.KLimCurvatureBounds


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

local instance terminalFlatTopology : TopologicalSpace F.M := F.topology
local instance terminalFlatCharted : ChartedSpace H F.M := F.charted
local instance terminalFlatSmooth : IsManifold I ∞ F.M := F.smooth
local instance terminalFlatT2 : T2Space F.M := F.t2


theorem KLim.not_terminal_flat {kappa : ℝ} (hK : KLim (I := I) kappa F)
    (hdim : Module.finrank ℝ E = 3) :
    ¬ ∀ x : F.M, F.rmNormSq (I := I) 0 x = 0 := by
  intro hflat
  obtain ⟨t, ht, x, hx⟩ := hK.notFlat
  have ht0 : t ≤ 0 := by simpa only [hK.carrier_eq, Set.mem_Iic] using ht
  have hscalar := scalar_abs_le_rm (F.S.base.metric 0) x
  change |F.S.scalar 0 x| ≤ (Module.finrank ℝ E : ℝ) ^ 2 *
    Real.sqrt (F.rmNormSq (I := I) 0 x) at hscalar
  rw [hflat x, Real.sqrt_zero, mul_zero] at hscalar
  have hzero : F.S.scalar 0 x = 0 := abs_eq_zero.mp (le_antisymm hscalar (abs_nonneg _))
  refine hx (le_antisymm ?_ (pointedFlow_rmNormSq_nonneg F t x))
  simpa using hK.rmNormSq_le_of_terminal_scalar_le F hdim ht0 x hzero.le

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
