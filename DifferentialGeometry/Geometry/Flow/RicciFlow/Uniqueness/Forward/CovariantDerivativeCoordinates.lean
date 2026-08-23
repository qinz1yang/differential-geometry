import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.CurvatureDifference
import DifferentialGeometry.Geometry.Coordinates.NablaComponents.Tensor0S
import DifferentialGeometry.Geometry.Connection.ChartBridge.RiemannBasisIdentityOffCentre
import DifferentialGeometry.Geometry.Curvature.MetricLeviCivitaReconcile
import DifferentialGeometry.Tensor.RSTensor.FiberMetric.Tensor0SMetricContinuity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Manifold Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


variable [SigmaCompactSpace M] [T2Space M]
variable [I.Boundaryless]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem nablaRicChartComp
    (g : SmoothRiemannianMetric I M)
    (Ric : Tensor0SField (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (n := (∞ : WithTop ℕ∞)) 2)
    (hRic : ∀ y : M, Ric y = metricRicciAt (I := I) g y)
    (α : M) (K : Fin 3 → Fin (Module.finrank Real E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    metricNabla0S (I := I) g Ric x
        (fun a : Fin 3 => chartBasisVecFiber (I := I) α (K a) x) =
      partialDeriv (E := E) (K 0)
          (chartRicciTensor (I := I) g α (K 1) (K 2))
          (extChartAt I α x) -
        ∑ m : Fin (Module.finrank Real E),
          chartChristoffel (I := I) g α (K 0) (K 1) m (extChartAt I α x) *
            chartRicciTensor (I := I) g α m (K 2) (extChartAt I α x) -
        ∑ m : Fin (Module.finrank Real E),
          chartChristoffel (I := I) g α (K 0) (K 2) m (extChartAt I α x) *
            chartRicciTensor (I := I) g α (K 1) m (extChartAt I α x) := by
  classical
  let V : Fin 2 → (y : M) → TangentSpace I y :=
    fun q y => chartBasisVecFiber (I := I) α (K q.succ) y
  let f : M → Real := fun y => Ric y (fun q : Fin 2 => V q y)
  let gE : E → Real := chartRicciTensor (I := I) g α (K 1) (K 2)
  let y₀ : E := extChartAt I α x
  obtain ⟨Xext, U, hXext, _hUopen, hxU, _hUgood, hXeq⟩ :=
    exists_globalSmooth_chartBasisVec_ext_alpha (I := I) α (K 0) hx
  let X : ContMDiffSection I E (∞ : WithTop ℕ∞)
      (TangentSpace I : M → Type _) := ⟨Xext, hXext⟩
  have hXx : X x = chartBasisVecFiber (I := I) α (K 0) x := by
    exact hXeq x hxU
  have hxbase : x ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hV_at : ∀ q : Fin 2,
      ContMDiffAt I (I.prod 𝓘(Real, E)) (∞ : WithTop ℕ∞)
        (fun y : M => (⟨y, V q y⟩ :
          TotalSpace E (TangentSpace I : M → Type _))) x := by
    intro q
    exact
      ((chartBasisVec_contMDiffOn (I := I) α (K q.succ)) x hxbase).contMDiffAt
        ((trivializationAt E (TangentSpace I) α).open_baseSet.mem_nhds hxbase)
  have hpair : MDifferentiableAt I 𝓘(Real, Real) f x := by
    exact
      (tensor0SField_eval_cmdAt_slots (I := I) Ric V hV_at).mdifferentiableAt
        (by simp)
  have hV : ∀ q : Fin 2, MDiffAt (T% (V q)) x :=
    fun q => (hV_at q).mdifferentiableAt (by simp)
  have hVmodel : ∀ q : Fin 2,
      DifferentiableWithinAt Real
        (TensorLieDeriv.tangentFieldModelInChart
          (𝕜 := Real) (I := I) x (V q))
        (Set.range I) (extChartAt I x x) :=
    fun q =>
      tangentFieldModelInChart_differentiableWithinAt_center_of_contMDiffAt
        (I := I) (V q) x (hV_at q)
  have hcoord : ∀ q : Fin 2, ∀ i : Fin (Module.finrank Real E),
      MDifferentiableAt I 𝓘(Real, Real)
        (fun p : M =>
          (Module.finBasis Real E).coord i
            (TensorLieDeriv.tangentFieldModelInChart
              (𝕜 := Real) (I := I) x (V q) (extChartAt I x p))) x :=
    fun q i =>
      tangentFieldModelInChart_coord_mdiffAt_center_of_contMDiffAt
        (I := I) (V q) x (hV_at q) i
  have hraw :=
    nabla0SFun_eval_coordFrame_moving_raw
      (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
      (s := 2) (metricCov (I := I) g) X V Ric x hpair hV hVmodel hcoord
  have hslots :
      (fun a : Fin 3 => chartBasisVecFiber (I := I) α (K a) x) =
        Fin.cons (X x) (fun q : Fin 2 => V q x) := by
    funext a
    refine Fin.cases ?_ (fun q => ?_) a
    · exact hXx.symm
    · rfl
  have hleft :
      metricNabla0S (I := I) g Ric x
          (fun a : Fin 3 => chartBasisVecFiber (I := I) α (K a) x) =
        nabla0SFun (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
          2 (metricCov (I := I) g) X Ric x (fun q : Fin 2 => V q x) := by
    rw [metricNabla0S_apply, hslots]
    exact
      totalNabla0SFun_apply_section
        (𝕜 := Real) (E := E) (H := H) (I := I) (M := M)
        2 (metricCov (I := I) g) X Ric x (fun q : Fin 2 => V q x)
  have hVslots : ∀ y : M,
      (fun q : Fin 2 => V q y) =
        vec2 (I := I)
          (chartBasisVecFiber (I := I) α (K 1) y)
          (chartBasisVecFiber (I := I) α (K 2) y) := by
    intro y
    funext q
    fin_cases q <;> rfl
  have hf_chart :
      f =ᶠ[𝓝 x] fun y : M => gE (extChartAt I α y) := by
    have hgood :
        chartLeviCivitaGoodSet (I := I) α ∈ 𝓝 x :=
      (chartLeviCivitaGoodSet_isOpen (I := I) α).mem_nhds hx
    filter_upwards [hgood] with y hy
    change Ric y (fun q : Fin 2 => V q y) =
      chartRicciTensor (I := I) g α (K 1) (K 2) (extChartAt I α y)
    rw [hVslots y, hRic y,
      metricRicciAt_apply_eq_ricciTensor (I := I) g y,
      ricciTensor_chartBasisVec_alpha_eq (I := I) g α (K 1) (K 2) hy]
  have hxchart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hxsrc : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source]
    exact hxchart
  have hxint : y₀ ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  have hinv : (extChartAt I α).symm y₀ = x :=
    (extChartAt I α).left_inv hxsrc
  have htend :
      Filter.Tendsto (fun y : E => (extChartAt I α).symm y)
        (𝓝 y₀) (𝓝 x) := by
    have hcont :
        ContinuousAt (fun y : E => (extChartAt I α).symm y) y₀ := by
      simpa only [y₀] using
        continuousAt_extChartAt_symm' (I := I) hxsrc
    simpa only [ContinuousAt, hinv, Function.comp_def] using hcont
  have htgt : ((extChartAt I α).target : Set E) ∈ 𝓝 y₀ :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hxint) interior_subset
  have hscalar :
      scalarOnE (I := I) α f =ᶠ[𝓝 y₀] gE := by
    have hcomp := htend.eventually hf_chart
    filter_upwards [hcomp, htgt] with y hy hyTarget
    simp only [scalarOnE_def]
    rw [hy, (extChartAt I α).right_inv hyTarget]
  have hderiv :
      extDerivFun (I := I) f x
          (chartBasisVecFiber (I := I) α (K 0) x) =
        partialDeriv (E := E) (K 0) gE y₀ := by
    change
      (mfderiv I 𝓘(Real) f x : TangentSpace I x →L[Real] Real)
          (chartBasisVecFiber (I := I) α (K 0) x) =
        (fderiv Real gE y₀) ((chartModelBasis E) (K 0))
    rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt
      (I := I) α hpair hxchart hxint (K 0)]
    change
      (fderiv Real (scalarOnE (I := I) α f) y₀)
          ((chartModelBasis E) (K 0)) =
        (fderiv Real gE y₀) ((chartModelBasis E) (K 0))
    rw [hscalar.fderiv_eq (𝕜 := Real)]
  have hderivX :
      extDerivFun (I := I) f x (X x) =
        partialDeriv (E := E) (K 0) gE y₀ := by
    rw [hXx, hderiv]
  have hcov : ∀ q : Fin 2,
      ((metricCov (I := I) g) (V q) x) (X x) =
        ∑ m : Fin (Module.finrank Real E),
          chartChristoffel (I := I) g α (K 0) (K q.succ) m y₀ •
            chartBasisVecFiber (I := I) α m x := by
    intro q
    rw [hXx]
    change
      (LeviCivita (I := I) g).toFun
          (fun y : M => chartBasisVecFiber (I := I) α (K q.succ) y) x
          (chartBasisVecFiber (I := I) α (K 0) x) =
        ∑ m : Fin (Module.finrank Real E),
          chartChristoffel (I := I) g α (K 0) (K q.succ) m y₀ •
            chartBasisVecFiber (I := I) α m x
    exact
      LeviCivita_chartBasisVec_alpha_basis_apply
        (I := I) g α (K 0) (K q.succ) hx
  have hterm : ∀ q : Fin 2,
      Ric x
          (Function.update (fun r : Fin 2 => V r x) q
            (((metricCov (I := I) g) (V q) x) (X x))) =
        ∑ m : Fin (Module.finrank Real E),
          chartChristoffel (I := I) g α (K 0) (K q.succ) m y₀ *
            chartRicciTensor (I := I) g α
              (if q = 0 then m else K 1)
              (if q = 1 then m else K 2) y₀ := by
    intro q
    rw [hcov q]
    rw [show
      Ric x
          (Function.update (fun r : Fin 2 => V r x) q
            (∑ m : Fin (Module.finrank Real E),
              chartChristoffel (I := I) g α (K 0) (K q.succ) m y₀ •
                chartBasisVecFiber (I := I) α m x)) =
        (Ric x).toMultilinearMap
          (Function.update (fun r : Fin 2 => V r x) q
            (∑ m : Fin (Module.finrank Real E),
              chartChristoffel (I := I) g α (K 0) (K q.succ) m y₀ •
                chartBasisVecFiber (I := I) α m x)) from rfl]
    rw [MultilinearMap.map_update_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MultilinearMap.map_update_smul]
    rw [show
      (Ric x).toMultilinearMap
          (Function.update (fun r : Fin 2 => V r x) q
            (chartBasisVecFiber (I := I) α m x)) =
        Ric x
          (Function.update (fun r : Fin 2 => V r x) q
            (chartBasisVecFiber (I := I) α m x)) from rfl]
    have hupd :
        Function.update (fun r : Fin 2 => V r x) q
            (chartBasisVecFiber (I := I) α m x) =
          vec2 (I := I)
            (chartBasisVecFiber (I := I) α
              (if q = 0 then m else K 1) x)
            (chartBasisVecFiber (I := I) α
              (if q = 1 then m else K 2) x) := by
      funext r
      fin_cases q <;> fin_cases r <;>
        simp [V, Function.update, vec2]
    rw [hupd, hRic x,
      metricRicciAt_apply_eq_ricciTensor (I := I) g x,
      ricciTensor_chartBasisVec_alpha_eq (I := I) g α
        (if q = 0 then m else K 1) (if q = 1 then m else K 2) hx,
      smul_eq_mul]
  rw [hleft, hraw]
  change extDerivFun (I := I) f x (X x) -
      (∑ q : Fin 2,
        Ric x
          (Function.update (fun r : Fin 2 => V r x) q
            (((metricCov (I := I) g) (V q) x) (X x)))) = _
  rw [hderivX, Fin.sum_univ_two, hterm 0, hterm 1]
  simp only [Fin.isValue, Fin.succ_zero_eq_one, if_true, reduceIte,
    show ((0 : Fin 2) = 1) = False by simp,
    show ((1 : Fin 2) = 0) = False by simp, gE, y₀]
  rw [show Fin.succ (1 : Fin 2) = (2 : Fin 3) by decide]
  ring

end DifferentialGeometry.PDE.RicciFlow
