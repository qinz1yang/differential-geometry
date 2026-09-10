import DifferentialGeometry.Bundle.PartialMfderiv.Basic
import DifferentialGeometry.Geometry.Metric.Family.Continuity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Connection.CovariantDerivativeCoordinates
import DifferentialGeometry.Geometry.Connection.Coordinates.CovariantDerivativeRealization
import DifferentialGeometry.Geometry.Metric.Family.Regularity.DifferentialOperator

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
open DifferentialGeometry.Tensor.Coordinates

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
      (fun p : Real × E => DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
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
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) d
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

omit [SigmaCompactSpace M] in
private theorem totalNabla0S_apply_localFrameAt
    {q : Nat}
    (cov : CovariantDerivative I E (TangentSpace I : M -> Type _))
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    (nablaA : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) (q + 1))
    (hreal : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) q cov A nablaA)
    {u : Set M}
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (1 : WithTop ℕ∞) frame u)
    (hu : IsOpen u) (x : M) (hx : x ∈ u)
    (d : CoordinateIdx (𝕜 := Real) E)
    (slots : Fin q -> CoordinateIdx (𝕜 := Real) E) :
    nablaA x (Fin.cons (frame d x) (fun r => frame (slots r) x)) =
      mvfderiv (I := I)
          (fun y : M => A y (fun r => frame (slots r) y))
          x (frame d x) -
        ∑ r : Fin q, ∑ p : CoordinateIdx (𝕜 := Real) E,
          christoffelSymbolInFrame cov frame hframe x d (slots r) p *
            A x (fun s => frame (Function.update slots r p s) x) := by
  classical
  have h := covDerivStepComp_frameComp_eq
    (I := I) cov A nablaA hreal frame hframe
    hu hx (Fin.cons d slots)
  rw [frameTuple_eq_cons] at h
  simp only [Fin.cons_zero, Fin.tail_cons] at h
  have htail : frameTuple (I := I) frame x slots =
      (fun r => frame (slots r) x) := rfl
  rw [htail] at h
  rw [← h]
  simp only [covDerivStepComp, frameComp0S,
    Fin.tail_cons, Fin.cons_zero]
  rfl

omit [SigmaCompactSpace M] [T2Space M] in
private theorem tensor0SField_localFrame_mdiffAt
    {q : Nat}
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) q)
    {u : Set M}
    (frame : CoordinateIdx (𝕜 := Real) E → (x : M) → TangentSpace I x)
    (hframe : IsLocalFrameOn I E (∞ : WithTop ℕ∞) frame u)
    (hu : IsOpen u) (x : M) (hx : x ∈ u)
    (slots : Fin q -> CoordinateIdx (𝕜 := Real) E) :
    MDifferentiableAt I (modelWithCornersSelf Real Real)
      (fun y : M => A y
        (fun r => frame (slots r) y)) x := by
  apply tensor0SField_eval_C1_slots_mdiffAt
  intro r
  exact (hframe.contMDiffAt hu hx (slots r)).of_le (by simp)

omit [SigmaCompactSpace M] [T2Space M] in
private theorem local_frame_eq_chart_for_nabla2Ricci
    (alpha : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) alpha).baseSet)
    (i : Fin (Module.finrank Real E)) :
    (trivializationAt E (TangentSpace I) alpha).localFrame
        (chartModelBasis E) i x =
      chartBasisVecFiber (I := I) alpha i x := by
  rw [(trivializationAt E (TangentSpace I) alpha).localFrame_apply_of_mem_baseSet
    (chartModelBasis E) hx]
  rw [Bundle.Trivialization.basisAt, Module.Basis.map_apply]
  change ((trivializationAt E (TangentSpace I) alpha).linearEquivAt Real x hx).symm
      (chartModelBasis E i) =
    (trivializationAt E (TangentSpace I) alpha).symmL Real x (chartModelBasis E i)
  rw [(trivializationAt E (TangentSpace I) alpha).symmL_apply hx]
  rfl

omit [SigmaCompactSpace M] in
private theorem local_chr_eq_chart_for_nabla2Ricci [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (alpha : M)
    {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) alpha)
    (i j k : Fin (Module.finrank Real E)) :
    let e := trivializationAt E (TangentSpace I) alpha
    let frame := e.localFrame (chartModelBasis E)
    let hframe := e.isLocalFrameOn_localFrame_baseSet I (1 : WithTop ℕ∞)
      (chartModelBasis E)
    christoffelSymbolInFrame (metricCov (I := I) g) frame hframe x i j k =
      chartChristoffel (I := I) g alpha i j k (extChartAt I alpha x) := by
  dsimp
  let e := trivializationAt E (TangentSpace I) alpha
  let frame := e.localFrame (chartModelBasis E)
  let hframe := e.isLocalFrameOn_localFrame_baseSet I (1 : WithTop ℕ∞)
    (chartModelBasis E)
  have hxbase : x ∈ e.baseSet := by
    simpa only [e] using chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hcov :
      (metricCov (I := I) g) (frame j) x (frame i x) =
        ∑ l : Fin (Module.finrank Real E),
          chartChristoffel (I := I) g alpha i j l (extChartAt I alpha x) •
            frame l x := by
    have hframe_diff :=
      (hframe.contMDiffAt e.open_baseSet hxbase j).mdifferentiableAt (by simp)
    have hchart_diff :=
      chartBasisVec_alpha_mdifferentiableAt (I := I) alpha j hx
    have hev :
        (fun y : M => frame j y) =ᶠ[𝓝 x]
          (fun y : M => chartBasisVecFiber (I := I) alpha j y) := by
      filter_upwards [e.open_baseSet.mem_nhds hxbase] with y hy
      exact local_frame_eq_chart_for_nabla2Ricci (I := I) alpha hy j
    have hcov_congr :
        (metricCov (I := I) g).toFun (frame j) x =
          (LeviCivita (I := I) g).toFun
            (fun y : M => chartBasisVecFiber (I := I) alpha j y) x := by
      change
        (LeviCivita (I := I) g).toFun (frame j) x =
          (LeviCivita (I := I) g).toFun
            (fun y : M => chartBasisVecFiber (I := I) alpha j y) x
      exact
        (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.congr_of_eventuallyEq
          hframe_diff hchart_diff univ_mem hev
    calc
      (metricCov (I := I) g) (frame j) x (frame i x) =
          (LeviCivita (I := I) g).toFun
            (fun y : M => chartBasisVecFiber (I := I) alpha j y) x
            (frame i x) :=
        congrArg (fun L => L (frame i x)) hcov_congr
      _ = (LeviCivita (I := I) g).toFun
            (fun y : M => chartBasisVecFiber (I := I) alpha j y) x
            (chartBasisVecFiber (I := I) alpha i x) := by
        have hi : frame i x = chartBasisVecFiber (I := I) alpha i x := by
          simpa only [frame, e] using
            local_frame_eq_chart_for_nabla2Ricci (I := I) alpha hxbase i
        rw [hi]
      _ = ∑ l : Fin (Module.finrank Real E),
            chartChristoffel (I := I) g alpha i j l (extChartAt I alpha x) •
              chartBasisVecFiber (I := I) alpha l x :=
        LeviCivita_chartBasisVec_alpha_basis_apply (I := I) g alpha i j hx
      _ = ∑ l : Fin (Module.finrank Real E),
            chartChristoffel (I := I) g alpha i j l (extChartAt I alpha x) •
              frame l x := by
        refine Finset.sum_congr rfl fun l _ => ?_
        have hl : frame l x = chartBasisVecFiber (I := I) alpha l x := by
          simpa only [frame, e] using
            local_frame_eq_chart_for_nabla2Ricci (I := I) alpha hxbase l
        rw [hl]
  have hcoeff (l : Fin (Module.finrank Real E)) :
      hframe.coeff k x (frame l x) = if l = k then 1 else 0 := by
    rw [hframe.coeff_apply_of_mem hxbase]
    change
      ((hframe.toBasisAt hxbase).repr
        (e.localFrame (chartModelBasis E) l x)) k =
          if l = k then 1 else 0
    rw [← hframe.toBasisAt_coe hxbase l]
    rw [(hframe.toBasisAt hxbase).repr_self]
    simp [Finsupp.single_apply]
  change christoffelSymbolInFrame (metricCov (I := I) g) frame hframe x i j k =
    chartChristoffel (I := I) g alpha i j k (extChartAt I alpha x)
  rw [christoffelSymbolInFrame_eval, hcov, map_sum]
  simp only [map_smul, hcoeff]
  simp

omit [SigmaCompactSpace M] in
theorem chartNabla2Ricci [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (alpha : M)
    (d a i j : Fin (Module.finrank Real E)) :
    ContDiffOn Real ∞
      (fun p : Real × E =>
        let x := (extChartAt I alpha).symm p.2
        metricNabla2Ric (I := I) (M := M) (S.family.metric p.1) x
          (vec4 (chartBasisVecFiber (I := I) alpha d x)
            (chartBasisVecFiber (I := I) alpha a x)
            (chartBasisVecFiber (I := I) alpha i x)
            (chartBasisVecFiber (I := I) alpha j x)))
      (D.regular ×ˢ interior (extChartAt I alpha).target) := by
  classical
  let U := D.regular ×ˢ interior (extChartAt I alpha).target
  let F : Real → E → Real := fun t y =>
    let x := (extChartAt I alpha).symm y
    totalNabla0SFun (𝕜 := Real) (I := I) 2
      (S.family.connection t) (S.ricci t) x
      (vec3 (chartBasisVecFiber (I := I) alpha a x)
        (chartBasisVecFiber (I := I) alpha i x)
        (chartBasisVecFiber (I := I) alpha j x))
  have hF : ContDiffOn Real ∞ (fun p : Real × E => F p.1 p.2) U := by
    simpa only [F] using chartNablaRicci (I := I) S hS alpha a i j
  have hfd := DifferentialGeometry.Analysis.spatialFDeriv_contDiffOn
    (G := F) D.regular_isOpen.uniqueDiffOn isOpen_interior hF
  have hpart : ContDiffOn Real ∞
      (fun p : Real × E => partialDeriv (E := E) d (F p.1) p.2) U := by
    change ContDiffOn Real ∞
      (fun p : Real × E =>
        (Function.uncurry (fun t y => fderiv Real (F t) y) p)
          (chartModelBasis E d)) U
    exact hfd.clm_apply (contDiffOn_const (c := chartModelBasis E d))
  have hGamma (b c e : Fin (Module.finrank Real E)) : ContDiffOn Real ∞
      (fun p : Real × E => chartChristoffel (I := I)
        (S.family.metric p.1) alpha b c e p.2) U :=
    MetricFamilySmoothOn.chartChristoffelOnE_contDiffOn
      (I := I) (g_fam := S.family.metric) hS.smoothMetric
      (J := D.regular) (fun _ ht => ht) D.regular_isOpen.uniqueDiffOn alpha b c e
  have hAcomp (b c e : Fin (Module.finrank Real E)) : ContDiffOn Real ∞
      (fun p : Real × E =>
        let x := (extChartAt I alpha).symm p.2
        totalNabla0SFun (𝕜 := Real) (I := I) 2
          (S.family.connection p.1) (S.ricci p.1) x
          (vec3 (chartBasisVecFiber (I := I) alpha b x)
            (chartBasisVecFiber (I := I) alpha c x)
            (chartBasisVecFiber (I := I) alpha e x))) U :=
    chartNablaRicci (I := I) S hS alpha b c e
  have hformula : ContDiffOn Real ∞
      (fun p : Real × E =>
        partialDeriv (E := E) d (F p.1) p.2 -
          ∑ m, chartChristoffel (I := I) (S.family.metric p.1)
              alpha d a m p.2 *
            (let x := (extChartAt I alpha).symm p.2
             totalNabla0SFun (𝕜 := Real) (I := I) 2
               (S.family.connection p.1) (S.ricci p.1) x
               (vec3 (chartBasisVecFiber (I := I) alpha m x)
                 (chartBasisVecFiber (I := I) alpha i x)
                 (chartBasisVecFiber (I := I) alpha j x))) -
          ∑ m, chartChristoffel (I := I) (S.family.metric p.1)
              alpha d i m p.2 *
            (let x := (extChartAt I alpha).symm p.2
             totalNabla0SFun (𝕜 := Real) (I := I) 2
               (S.family.connection p.1) (S.ricci p.1) x
               (vec3 (chartBasisVecFiber (I := I) alpha a x)
                 (chartBasisVecFiber (I := I) alpha m x)
                 (chartBasisVecFiber (I := I) alpha j x))) -
          ∑ m, chartChristoffel (I := I) (S.family.metric p.1)
              alpha d j m p.2 *
            (let x := (extChartAt I alpha).symm p.2
             totalNabla0SFun (𝕜 := Real) (I := I) 2
               (S.family.connection p.1) (S.ricci p.1) x
               (vec3 (chartBasisVecFiber (I := I) alpha a x)
                 (chartBasisVecFiber (I := I) alpha i x)
                 (chartBasisVecFiber (I := I) alpha m x)))) U := by
    exact ((hpart.sub (ContDiffOn.sum fun m _ =>
      (hGamma d a m).mul (hAcomp m i j))).sub
        (ContDiffOn.sum fun m _ => (hGamma d i m).mul (hAcomp a m j))).sub
          (ContDiffOn.sum fun m _ => (hGamma d j m).mul (hAcomp a i m))
  refine hformula.congr ?_
  intro p hp
  let x := (extChartAt I alpha).symm p.2
  let cov := metricCov (I := I) (M := M) (S.family.metric p.1)
  let Ric := S.ricci p.1
  let nablaRic := metricNablaRic (I := I) (M := M) (S.family.metric p.1)
  let nabla2Ric := metricNabla2Ric (I := I) (M := M) (S.family.metric p.1)
  let e := trivializationAt E (TangentSpace I) alpha
  let frame := e.localFrame (chartModelBasis E)
  let hframe := e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞)
    (chartModelBasis E)
  let hframeOne := e.isLocalFrameOn_localFrame_baseSet I (1 : WithTop ℕ∞)
    (chartModelBasis E)
  let slots : Fin 3 → CoordinateIdx (𝕜 := Real) E :=
    fun r => if r = 0 then a else if r = 1 then i else j
  have hxsrc : x ∈ (extChartAt I alpha).source :=
    (extChartAt I alpha).map_target (interior_subset hp.2)
  have hxgood : x ∈ chartLeviCivitaGoodSet (I := I) alpha :=
    (mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source
      (I := I) alpha x).2 hxsrc
  have hxframe : x ∈ e.baseSet := by
    simpa only [e] using chartLeviCivitaGoodSet_mem_baseSet (I := I) hxgood
  have hright : extChartAt I alpha x = p.2 :=
    (extChartAt I alpha).right_inv (interior_subset hp.2)
  have hreal : TotalNabla0SRealizes (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) 3 cov nablaRic nabla2Ric := by
    simpa [cov, Ric, nablaRic, nabla2Ric, metricNablaRic, metricNabla2Ric,
      SolutionFamily.connection, SolutionFamily.ricci, SolutionOn.ricci,
      SolutionOn.family, metricCov, metricRicci] using
      (totalNabla0S_realizes (𝕜 := Real) (E := E) (H := H)
        (I := I) (M := M) 3 cov nablaRic
        (totalNabla0S_regularity (E := E) (H := H) (I := I) (M := M)
          3 cov (by
            simpa [cov, SolutionFamily.connection, SolutionOn.family, metricCov] using
              metricCov_smooth (I := I) (M := M) (S.family.metric p.1)) nablaRic))
  have hstep := totalNabla0S_apply_localFrameAt
    (I := I) cov nablaRic nabla2Ric hreal frame hframeOne e.open_baseSet
      x hxframe d slots
  have hmdiff : MDifferentiableAt I (modelWithCornersSelf Real Real)
      (fun y : M => nablaRic y
        (fun r => frame (slots r) y)) x := by
    simpa only [frame] using
      tensor0SField_localFrame_mdiffAt
        (I := I) nablaRic frame hframe e.open_baseSet x hxframe slots
  let f : M → Real := fun y => nablaRic y (fun r => frame (slots r) y)
  let gE : E → Real := F p.1
  let y0 : E := extChartAt I alpha x
  have hxchart : x ∈ (chartAt H alpha).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hxgood
  have hxint : y0 ∈ interior ((extChartAt I alpha).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hxgood
  have hinv : (extChartAt I alpha).symm y0 = x :=
    (extChartAt I alpha).left_inv hxsrc
  have htend : Tendsto (fun y : E => (extChartAt I alpha).symm y)
      (𝓝 y0) (𝓝 x) := by
    have hcont : ContinuousAt (fun y : E => (extChartAt I alpha).symm y) y0 := by
      simpa only [y0] using continuousAt_extChartAt_symm' (I := I) hxsrc
    simpa only [ContinuousAt, hinv, Function.comp_def] using hcont
  have htgt : ((extChartAt I alpha).target : Set E) ∈ 𝓝 y0 :=
    mem_of_superset (isOpen_interior.mem_nhds hxint) interior_subset
  have hscalar : scalarOnE (I := I) alpha f =ᶠ[𝓝 y0] gE := by
    filter_upwards [htgt] with y hy
    have hyframe : (extChartAt I alpha).symm y ∈
        (trivializationAt E (TangentSpace I) alpha).baseSet := by
      exact chartLeviCivitaGoodSet_mem_baseSet (I := I)
        ((mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source
          (I := I) alpha _).2 ((extChartAt I alpha).map_target hy))
    simp only [scalarOnE_def, f, gE, F, nablaRic, metricNablaRic,
      SolutionOn.family, SolutionFamily.connection, SolutionOn.ricci,
      SolutionFamily.ricci, metricCov, metricRicci, frame]
    congr 1
    funext r
    fin_cases r
    · simpa [slots, vec3, frame] using
        local_frame_eq_chart_for_nabla2Ricci (I := I) alpha hyframe a
    · simpa [slots, vec3, frame] using
        local_frame_eq_chart_for_nabla2Ricci (I := I) alpha hyframe i
    · simpa [slots, vec3, frame] using
        local_frame_eq_chart_for_nabla2Ricci (I := I) alpha hyframe j
  have hderiv : mvfderiv (I := I) f x (frame d x) =
      partialDeriv (E := E) d gE y0 := by
    have hframeD : frame d x = chartBasisVecFiber (I := I) alpha d x := by
      simpa only [frame, e] using
        local_frame_eq_chart_for_nabla2Ricci (I := I) alpha hxframe d
    rw [hframeD]
    change (mfderiv I 𝓘(Real) f x : TangentSpace I x →L[Real] Real)
        (chartBasisVecFiber (I := I) alpha d x) =
      (fderiv Real gE y0) (chartModelBasis E d)
    rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt
      (I := I) alpha (by simpa only [f] using hmdiff) hxchart hxint d]
    change (fderiv Real (scalarOnE (I := I) alpha f) y0)
        (chartModelBasis E d) =
      (fderiv Real gE y0) (chartModelBasis E d)
    rw [hscalar.fderiv_eq (𝕜 := Real)]
  rw [Fin.sum_univ_three] at hstep
  have hlocal (k : CoordinateIdx (𝕜 := Real) E) :
      frame k x = chartBasisVecFiber (I := I) alpha k x := by
    simpa only [frame, e] using
      local_frame_eq_chart_for_nabla2Ricci (I := I) alpha hxframe k
  have hchr (b c k : CoordinateIdx (𝕜 := Real) E) :
      christoffelSymbolInFrame cov frame hframeOne x b c k =
        chartChristoffel (I := I) (S.family.metric p.1)
          alpha b c k p.2 := by
    simpa only [cov, frame, hframeOne, e, hright] using
      local_chr_eq_chart_for_nabla2Ricci (I := I) (S.family.metric p.1)
        alpha hxgood b c k
  have hupdate0 (k : CoordinateIdx (𝕜 := Real) E) :
      (fun s => frame (Function.update slots (0 : Fin 3) k s) x) =
        vec3 (chartBasisVecFiber (I := I) alpha k x)
          (chartBasisVecFiber (I := I) alpha i x)
          (chartBasisVecFiber (I := I) alpha j x) := by
    funext s
    fin_cases s <;> simp [slots, Function.update, hlocal, vec3]
  have hupdate1 (k : CoordinateIdx (𝕜 := Real) E) :
      (fun s => frame (Function.update slots (1 : Fin 3) k s) x) =
        vec3 (chartBasisVecFiber (I := I) alpha a x)
          (chartBasisVecFiber (I := I) alpha k x)
          (chartBasisVecFiber (I := I) alpha j x) := by
    funext s
    fin_cases s <;> simp [slots, Function.update, hlocal, vec3]
  have hupdate2 (k : CoordinateIdx (𝕜 := Real) E) :
      (fun s => frame (Function.update slots (2 : Fin 3) k s) x) =
        vec3 (chartBasisVecFiber (I := I) alpha a x)
          (chartBasisVecFiber (I := I) alpha i x)
          (chartBasisVecFiber (I := I) alpha k x) := by
    funext s
    fin_cases s <;> simp [slots, Function.update, hlocal, vec3]
  have hinput :
      Fin.cons (frame d x) (fun r => frame (slots r) x) =
        vec4 (chartBasisVecFiber (I := I) alpha d x)
          (chartBasisVecFiber (I := I) alpha a x)
          (chartBasisVecFiber (I := I) alpha i x)
          (chartBasisVecFiber (I := I) alpha j x) := by
    have htail : (fun r : Fin 3 => frame (slots r) x) =
        vec3 (chartBasisVecFiber (I := I) alpha a x)
          (chartBasisVecFiber (I := I) alpha i x)
          (chartBasisVecFiber (I := I) alpha j x) := by
      funext r
      fin_cases r <;> simp [slots, hlocal, vec3]
    rw [hlocal d, htail]
    funext r
    fin_cases r <;> rfl
  change nabla2Ric x
      (vec4 (chartBasisVecFiber (I := I) alpha d x)
        (chartBasisVecFiber (I := I) alpha a x)
        (chartBasisVecFiber (I := I) alpha i x)
        (chartBasisVecFiber (I := I) alpha j x)) = _
  rw [← hinput, hstep]
  rw [hderiv]
  simp only [gE, y0, hright]
  simp_rw [hchr, hupdate0, hupdate1, hupdate2]
  simp only [nablaRic, metricNablaRic, SolutionOn.family,
    SolutionFamily.connection, SolutionOn.ricci, SolutionFamily.ricci,
    metricCov, metricRicci, totalNabla0S_apply, F]
  simp [slots, x]
  ring

omit [SigmaCompactSpace M] in
theorem nabla2Ricci_cont [I.Boundaryless]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 D.regular
      (fun t x => metricNabla2Ric (I := I) (M := M)
        (S.family.metric t) x) := by
  classical
  let A : (t : Real) → (x : M) → Tensor0SSpace 4 I x :=
    fun t x => metricNabla2Ric (I := I) (M := M) (S.family.metric t) x
  change tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 D.regular A
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
    (chartNabla2Ricci (I := I) S hS alpha
      (idx 0) (idx 1) (idx 2) (idx 3)).continuousOn
  refine (hraw.comp hincl (fun q hq =>
    ⟨q.1.2, chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hq⟩)).congr ?_
  intro q hq
  have hleft : (extChartAt I alpha).symm (extChartAt I alpha q.2) = q.2 :=
    (extChartAt I alpha).left_inv
      (chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hq)
  have hslots :
      (fun k => chartBasisVecFiber (I := I) alpha (idx k) q.2) =
        vec4 (chartBasisVecFiber (I := I) alpha (idx 0) q.2)
          (chartBasisVecFiber (I := I) alpha (idx 1) q.2)
          (chartBasisVecFiber (I := I) alpha (idx 2) q.2)
          (chartBasisVecFiber (I := I) alpha (idx 3) q.2) := by
    funext k
    fin_cases k <;> rfl
  simp only [Function.comp_apply, A]
  rw [hslots, hleft]

end DifferentialGeometry.PDE.RicciFlow
