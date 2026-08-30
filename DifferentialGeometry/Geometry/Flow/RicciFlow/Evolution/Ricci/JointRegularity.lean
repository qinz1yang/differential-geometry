import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.CovariantDerivativeCoordinates
import DifferentialGeometry.Geometry.Metric.Family.DifferentialOperatorRegularity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem chartRicci_joint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (α : M)
    (i j : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E =>
        let x := (extChartAt I α).symm p.2
        S.ricciAt p.1 x
          (vec2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x)))
      (D.regular ×ˢ interior (extChartAt I α).target) := by
  intro p hp
  let U := D.regular ×ˢ interior (extChartAt I α).target
  have hUopen : IsOpen U := D.regular_isOpen.prod isOpen_interior
  have hmetric : ContDiffAt Real ∞
      (fun q : Real × E =>
        chartGramOnE (I := I) (S.family.metric q.1) α i j q.2) p :=
    (MetricFamilySmoothOn.chartGramOnE_contDiffOn
      (I := I) (g_fam := S.family.metric) hS.smoothMetric
      (J := D.regular) (fun _ h => h) α i j).contDiffAt
        (hUopen.mem_nhds hp)
  have hmetricM : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, E)) 𝓘(Real, Real) ∞
      (fun q : Real × E =>
        chartGramOnE (I := I) (S.family.metric q.1) α i j q.2) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod] at hmetric
    exact hmetric
  have hderivM := DifferentialGeometry.timeDeriv_smoothAt
    (m := ∞) (n := ∞) hmetricM
    (by simp)
  have hderiv : ContDiffAt Real ∞
      (fun q : Real × E =>
        deriv (fun t : Real =>
          chartGramOnE (I := I) (S.family.metric t) α i j q.2) q.1) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hderivM
  have hsmooth : ContDiffAt Real ∞
      (fun q : Real × E => (-1 / 2 : Real) *
        deriv (fun t : Real =>
          chartGramOnE (I := I) (S.family.metric t) α i j q.2) q.1) p :=
    contDiffAt_const.mul hderiv
  refine (hsmooth.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hUopen.mem_nhds hp] with q hq
  let x := (extChartAt I α).symm q.2
  let X := DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α i x
  let Y := DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α j x
  have heq := (metricDerivAt (I := I) S hS
    (⟨q.1, hq.1⟩ : D.RegularTime) x X Y).deriv
  change S.ricciAt q.1 x (vec2 X Y) =
    (-1 / 2 : Real) * deriv (fun t : Real =>
      chartGramOnE (I := I) (S.family.metric t) α i j q.2) q.1
  have hgram : deriv (fun t : Real =>
      chartGramOnE (I := I) (S.family.metric t) α i j q.2) q.1 =
      (-2 : Real) * S.ricciAt q.1 x (vec2 X Y) := by
    simpa only [chartGramOnE_def, DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply, x, X, Y] using heq
  rw [hgram]
  ring

omit [SigmaCompactSpace M] in
theorem chartNablaRicci [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (alpha : M)
    (d i j : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E =>
        let x := (extChartAt I alpha).symm p.2
        totalNabla0SFun (𝕜 := Real) (I := I) 2
          (S.family.connection p.1) (S.ricci p.1) x
          (vec3 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) alpha d x)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) alpha i x)
            (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) alpha j x)))
      (D.regular ×ˢ interior (extChartAt I alpha).target) := by
  classical
  let U := D.regular ×ˢ interior (extChartAt I alpha).target
  have hRicChart (a b : Fin (Module.finrank Real E)) : ContDiffOn Real ∞
      (fun p : Real × E => chartRicciTensor (I := I)
        (S.family.metric p.1) alpha a b p.2) U := by
    refine (chartRicci_joint (I := I) S hS alpha a b).congr ?_
    intro p hp
    let x := (extChartAt I alpha).symm p.2
    have hxsrc : x ∈ (extChartAt I alpha).source :=
      (extChartAt I alpha).map_target (interior_subset hp.2)
    have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) alpha :=
      (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source
        (I := I) alpha x).2 hxsrc
    have hright : extChartAt I alpha x = p.2 :=
      (extChartAt I alpha).right_inv (interior_subset hp.2)
    symm
    rw [SolutionOn.ricciAt_eq]
    change metricRicciAt (I := I) (S.family.metric p.1) x
      (vec2 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) alpha a x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) alpha b x)) = _
    rw [metricRicciAt_apply_eq_ricciTensor,
      ricciTensor_chartBasisVec_alpha_eq (I := I)
        (S.family.metric p.1) alpha a b hxgood, hright]
  have hfd := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    (G := fun t y => chartRicciTensor (I := I)
      (S.family.metric t) alpha i j y)
    D.regular_isOpen.uniqueDiffOn isOpen_interior (hRicChart i j)
  have hpart : ContDiffOn Real ∞
      (fun p : Real × E => partialDeriv (E := E) d
        (chartRicciTensor (I := I) (S.family.metric p.1) alpha i j) p.2) U := by
    change ContDiffOn Real ∞
      (fun p : Real × E =>
        (Function.uncurry (fun t y => fderiv Real
          (fun z => chartRicciTensor (I := I) (S.family.metric t) alpha i j z) y) p)
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E d)) U
    exact hfd.clm_apply (contDiffOn_const (c := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E d))
  have hGamma (a b c : Fin (Module.finrank Real E)) : ContDiffOn Real ∞
      (fun p : Real × E => chartChristoffel (I := I)
        (S.family.metric p.1) alpha a b c p.2) U :=
    MetricFamilySmoothOn.chartChristoffelOnE_contDiffOn
      (I := I) (g_fam := S.family.metric) hS.smoothMetric
      (J := D.regular) (fun _ ht => ht) D.regular_isOpen.uniqueDiffOn alpha a b c
  have hformula : ContDiffOn Real ∞
      (fun p : Real × E =>
        partialDeriv (E := E) d
            (chartRicciTensor (I := I) (S.family.metric p.1) alpha i j) p.2 -
          ∑ m, chartChristoffel (I := I) (S.family.metric p.1)
              alpha d i m p.2 *
            chartRicciTensor (I := I) (S.family.metric p.1) alpha m j p.2 -
          ∑ m, chartChristoffel (I := I) (S.family.metric p.1)
              alpha d j m p.2 *
            chartRicciTensor (I := I) (S.family.metric p.1) alpha i m p.2) U := by
    exact (hpart.sub (ContDiffOn.sum fun m _ =>
      (hGamma d i m).mul (hRicChart m j))).sub
        (ContDiffOn.sum fun m _ => (hGamma d j m).mul (hRicChart i m))
  refine hformula.congr ?_
  intro p hp
  let x := (extChartAt I alpha).symm p.2
  let K : Fin 3 → Fin (Module.finrank Real E) :=
    Fin.cons d (Fin.cons i (fun _ => j))
  have hxsrc : x ∈ (extChartAt I alpha).source :=
    (extChartAt I alpha).map_target (interior_subset hp.2)
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) alpha :=
    (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source
      (I := I) alpha x).2 hxsrc
  have hright : extChartAt I alpha x = p.2 :=
    (extChartAt I alpha).right_inv (interior_subset hp.2)
  have hraw := nablaRicChartComp (I := I) (S.family.metric p.1)
    (S.ricci p.1) (fun y => by
      simp only [SolutionOn.ricci_eq, SolutionFamily.ricci_apply]
      rfl) alpha K hxgood
  have hK0 : K (0 : Fin 3) = d := by rfl
  have hK1 : K (1 : Fin 3) = i := by rfl
  have hK2 : K (2 : Fin 3) = j := by rfl
  have hslots :
      (fun a : Fin 3 => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) alpha (K a) x) =
        vec3 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) alpha d x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) alpha i x)
          (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) alpha j x) := by
    funext q
    fin_cases q <;> rfl
  rw [hslots, hK0, hK1, hK2, hright] at hraw
  change metricNabla0S (I := I) (S.family.metric p.1) (S.ricci p.1) x
      (vec3 (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) alpha d x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) alpha i x)
        (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) alpha j x)) = _
  exact hraw

omit [SigmaCompactSpace M] in
theorem nablaRicci_cont [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 3 D.regular
      (fun t x => totalNabla0SFun (𝕜 := Real) (I := I) 2
        (S.family.connection t) (S.ricci t) x) := by
  classical
  let A : (t : Real) → (x : M) → Tensor0SSpace 3 I x :=
    fun t x => totalNabla0SFun (𝕜 := Real) (I := I) 2
      (S.family.connection t) (S.ricci t) x
  change tensor0SFamilyContinuousOnSet (I := I) (M := M) 3 D.regular A
  apply tensor0SFamilyContinuousOnSet_of_chartBasisComp (A := A)
    (N := fun alpha => chartLeviCivitaGoodSet (I := I) alpha)
    (hN := fun alpha => (chartLeviCivitaGoodSet_isOpen (I := I) alpha).mem_nhds
      (self_mem_chartLeviCivitaGoodSet (I := I) (α := alpha)))
  intro alpha idx
  have hincl : ContinuousOn
      (fun q : {t : Real // t ∈ D.regular} × M =>
        ((q.1 : Real), extChartAt I alpha q.2))
      {q : {t : Real // t ∈ D.regular} × M |
        q.2 ∈ chartLeviCivitaGoodSet (I := I) alpha} :=
    (continuous_subtype_val.comp continuous_fst).continuousOn.prodMk
      ((continuousOn_extChartAt (I := I) alpha).comp
        continuous_snd.continuousOn (fun q hq =>
          chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq))
  have hraw :=
    (chartNablaRicci (I := I) S hS alpha (idx 0) (idx 1) (idx 2)).continuousOn
  refine (hraw.comp hincl (fun q hq =>
    ⟨q.1.2, chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hq⟩)).congr ?_
  intro q hq
  have hleft : (extChartAt I alpha).symm (extChartAt I alpha q.2) = q.2 :=
    (extChartAt I alpha).left_inv
      (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq)
  simp only [Function.comp_apply, A]
  rw [hleft]
  congr 1
  funext k
  fin_cases k <;> rfl

end DifferentialGeometry.PDE.RicciFlow
