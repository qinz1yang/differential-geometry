import DifferentialGeometry.Bundle.SmoothScalarGerm
import DifferentialGeometry.Geometry.Comparison.Variation.FixedChartIdentities
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisBracket
import DifferentialGeometry.Geometry.Connection.ParallelTransport.CovariantDerivativeAlong

noncomputable section

set_option autoImplicit false

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CovariantDerivativeAlong

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem contMDiff_sum_along
    {ι : Type*} (s : Finset ι) (gamma : Real -> M)
    (V : ι -> forall t, TangentSpace I (gamma t))
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hV : forall i, i ∈ s -> ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun t : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma t) (V i t) : TangentBundle I M))) :
    ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun t : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma t) (∑ i ∈ s, V i t) : TangentBundle I M)) := by
  intro t0
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨hgamma t0, ?_⟩
  have hsum : ContMDiffAt 𝓘(Real, Real) 𝓘(Real, E) ∞
      (fun t : Real =>
        ∑ i ∈ s,
          ((trivializationAt E (TangentSpace I) (gamma t0))
            (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
              (gamma t) (V i t))).2) t0 := by
    apply ContMDiffAt.sum
    intro i hi
    exact ((Bundle.contMDiffAt_totalSpace (f := fun t : Real =>
      (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
        (gamma t) (V i t) : TangentBundle I M))).1 (hV i hi t0)).2
  refine hsum.congr_of_eventuallyEq ?_
  have hbase :
      ∀ᶠ t in 𝓝 t0,
        gamma t ∈
          (trivializationAt E (TangentSpace I) (gamma t0)).baseSet := by
    have hmem :
        gamma t0 ∈
          (trivializationAt E (TangentSpace I) (gamma t0)).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt' (gamma t0)
    exact (hgamma t0).continuousAt.preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) (gamma t0)).open_baseSet.mem_nhds
        hmem)
  filter_upwards [hbase] with t ht
  simp only [TotalSpace.mk']
  rw [(trivializationAt E (TangentSpace I) (gamma t0)).apply_eq_prod_continuousLinearEquivAt
    Real (gamma t) ht]
  simp_rw [(trivializationAt E (TangentSpace I) (gamma t0)).apply_eq_prod_continuousLinearEquivAt
    Real (gamma t) ht]
  rw [map_sum]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem exists_frame_exp
    (gamma : Real -> M) (V : forall s, TangentSpace I (gamma s)) (t : Real)
    (hgamma : ContMDiff 𝓘(Real, Real) I ∞ gamma)
    (hV : ContMDiff 𝓘(Real, Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (gamma s) (V s) : TangentBundle I M)))
    (B : Fin (Module.finrank Real E) -> forall x : M, TangentSpace I x)
    (hBnear : ∀ᶠ x in 𝓝 (gamma t), forall i,
      B i x = chartBasisVecFiber (I := I) (gamma t) i x) :
    exists c : Fin (Module.finrank Real E) -> Real -> Real,
      (forall i, ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ (c i)) /\
      (forall i, c i t =
        chartSectionCoord (E := E) (chartRepAt (I := I) gamma V t) i t) /\
      V =ᶠ[𝓝 t] fun s => ∑ i, c i s • B i (gamma s) := by
  classical
  let e := trivializationAt E (TangentSpace I) (gamma t)
  let S : Real -> TangentBundle I M := fun s =>
    TotalSpace.mk' E (E := (TangentSpace I : M -> Type _)) (gamma s) (V s)
  let U : Set Real := gamma ⁻¹' e.baseSet
  let cLoc : Fin (Module.finrank Real E) -> Real -> Real :=
    fun i => chartSectionCoord (E := E) (chartRepAt (I := I) gamma V t) i
  have hUopen : IsOpen U :=
    hgamma.continuous.isOpen_preimage _ e.open_baseSet
  have htU : t ∈ U :=
    mem_baseSet_trivializationAt E (TangentSpace I) (gamma t)
  have hSMaps : MapsTo S U e.source := by
    intro s hs
    exact e.mem_source.mpr hs
  have hcoord :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) ∞
        (fun s => (e (S s)).2) U :=
    (e.contMDiffOn_iff hSMaps).mp hV.contMDiffOn |>.2
  have hcLocOn : forall i,
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, Real) ∞ (cLoc i) U := by
    intro i
    refine ((chartCoordCLM (E := E) i).contMDiff.comp_contMDiffOn hcoord).congr ?_
    intro s hs
    change chartCoordCLM (E := E) i
          (e.continuousLinearMapAt Real (gamma s) (V s)) =
        chartCoordCLM (E := E) i ((e (S s)).2)
    congr 1
    rw [e.continuousLinearMapAt_apply (R := Real)]
    rw [e.coe_linearMapAt_of_mem hs]
  have hc : forall i, exists f : Real -> Real,
      ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ∞ f /\
        f =ᶠ[𝓝 t] cLoc i :=
    fun i => exists_smooth_germ (I := 𝓘(Real, Real))
      hUopen htU (hcLocOn i)
  choose c hcsm hceq using hc
  have hgammaCont : ContinuousAt gamma t := hgamma.continuous.continuousAt
  have hBcurve :
      ∀ᶠ s in 𝓝 t, forall i, B i (gamma s) =
        chartBasisVecFiber (I := I) (gamma t) i (gamma s) :=
    hgammaCont hBnear
  have hbase :
      ∀ᶠ s in 𝓝 t,
        gamma s ∈ (trivializationAt E (TangentSpace I) (gamma t)).baseSet := by
    exact hgammaCont
      ((trivializationAt E (TangentSpace I) (gamma t)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I) (gamma t)))
  refine ⟨c, hcsm, fun i => (hceq i).self_of_nhds, ?_⟩
  filter_upwards [hBcurve, hbase, Filter.eventually_all.mpr hceq] with
    s hBs hs hcs
  have hcancel :
      (trivializationAt E (TangentSpace I) (gamma t)).symmL Real (gamma s)
          ((trivializationAt E (TangentSpace I) (gamma t)).continuousLinearMapAt
            Real (gamma s) (V s)) =
        V s :=
    (trivializationAt E (TangentSpace I) (gamma t)).symmL_continuousLinearMapAt
      (R := Real) hs (V s)
  rw [← hcancel, symmL_eq_sum_chartBasisVecFiber (I := I)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hcs i, hBs i]
  rfl

end CovariantDerivativeAlong
end Riemannian
end Geometry
end DifferentialGeometry
