import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FamilyContinuity
import DifferentialGeometry.Topology.Manifold.CurveEndpointPerturbation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Approximation
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter Set
open DifferentialGeometry.Geometry.Curvature
open scoped ContDiff Manifold _root_.Topology Interval

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [PreconnectedSpace M] {D : RealTimeInterval}

theorem upperSemicontinuous_lCost_of_scalar_nonneg
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {T tau : ℝ} (htau : 0 < tau) (x : M)
    {K : Set ℝ} (hK : IsOpen K) (hslab : [[0, Real.sqrt tau]] ⊆ K)
    (hcarrier : ∀ s ∈ K, T - s ^ 2 ∈ D.carrier)
    (hscalar : ∀ s ∈ Icc 0 tau, ∀ z : M, 0 ≤ S.scalar (T - s) z) :
    UpperSemicontinuous (fun y => lCost S T x y tau) := by
  intro y A hA
  obtain ⟨gamma, hgamma, hstart, hend, hact⟩ :=
    exists_lRegularizedAction_lt_of_lCost_lt_of_preconnected S T x y tau htau A hA
  obtain ⟨V, hV, hqV, alpha, halpha, hslices, hstartAlpha, hendAlpha, hcenter⟩ :=
    DifferentialGeometry.Geometry.exists_contMDiff_endpoint_perturbation gamma hgamma
      (Real.sqrt_pos.mpr htau : 0 < Real.sqrt tau)
  let p := gamma (Real.sqrt tau)
  let q : E := extChartAt I p p
  have hq : q ∈ V := hqV
  have hfamily : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ, ℝ)) I 1 alpha (V ×ˢ K) :=
    halpha.mono (prod_mono subset_rfl (subset_univ K))
  have hcont := continuousOn_lRegularizedAction_family_of_contMDiffOn_one
    S hS T 0 (Real.sqrt tau) hV hK hfamily hcarrier hslab
  have hactcenter : lRegularizedAction S T (fun s => alpha (q, s)) 0 (Real.sqrt tau) < A := by
    have hcurve : (fun s => alpha (q, s)) = gamma := funext hcenter
    rwa [hcurve]
  have hcoord : ContinuousAt (fun z : M => extChartAt I p z) y := by
    have hp : p = y := hend
    rw [← hp]
    exact continuousAt_extChartAt (I := I) p
  have hqy : extChartAt I p y = q := by
    dsimp only [q]
    rw [show p = y from hend]
  have hparams : ∀ᶠ B in 𝓝 q,
      lRegularizedAction S T (fun s => alpha (B, s)) 0 (Real.sqrt tau) < A :=
    ((hcont q hq).continuousAt (hV.mem_nhds hq)).eventually (Iio_mem_nhds hactcenter)
  have hparamsY : ∀ᶠ z in 𝓝 y,
      lRegularizedAction S T (fun s => alpha (extChartAt I p z, s)) 0 (Real.sqrt tau) < A := by
    exact (hqy ▸ hcoord.tendsto).eventually hparams
  have hVY : ∀ᶠ z in 𝓝 y, extChartAt I p z ∈ V :=
    (hqy ▸ hcoord.tendsto).eventually (hV.mem_nhds hq)
  have hySource : y ∈ (extChartAt I p).source := by
    rw [show p = y from hend]
    exact mem_extChartAt_source y
  filter_upwards [hparamsY, hVY,
    (isOpen_extChartAt_source (I := I) p).mem_nhds hySource] with z hactz hzV hzSource
  have hcost := lCost_le_lRegularizedAction_of_scalar_nonneg S htau.le hscalar
    (fun s => alpha (extChartAt I p z, s)) (hslices _ hzV)
  have hzero : alpha (extChartAt I p z, 0) = x := (hstartAlpha _ hzV).trans hstart
  have hterminal : alpha (extChartAt I p z, Real.sqrt tau) = z :=
    (hendAlpha _ hzV).trans ((extChartAt I p).left_inv hzSource)
  rw [hzero, hterminal] at hcost
  exact hcost.trans_lt hactz

end DifferentialGeometry.PDE.RicciFlow.Perelman
