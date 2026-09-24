import DifferentialGeometry.Geometry.Connection.Coordinates.CovariantDerivativeRealization
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.DifferentiatedBasisIdentityOffCenter
import DifferentialGeometry.Tensor.RSTensor.Coordinates.CoordinateBasis

set_option autoImplicit false
noncomputable section
open Bundle Filter Set
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

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

omit [SigmaCompactSpace M] in
private theorem christoffelSymbolInFrame_eq_chartChristoffel [I.Boundaryless]
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
      exact localFrame_eq_chartBasisVec (I := I) alpha hy j
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
            localFrame_eq_chartBasisVec (I := I) alpha hxbase i
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
            localFrame_eq_chartBasisVec (I := I) alpha hxbase l
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
theorem totalNabla0S_chartComponent [I.Boundaryless]
    {q : ℕ} (g : SmoothRiemannianMetric I M)
    (A : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) q)
    (nablaA : Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) (n := ∞) (q + 1))
    (hreal : TotalNabla0SRealizes (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M)
      q (metricCov (I := I) g) A nablaA)
    (p : M) {x : M} (hx : x ∈ chartLeviCivitaGoodSet (I := I) p)
    (d : CoordinateIdx (𝕜 := ℝ) E) (slots : Fin q → CoordinateIdx (𝕜 := ℝ) E) :
    nablaA x (Fin.cons (chartBasisVecFiber (I := I) p d x)
      (fun r => chartBasisVecFiber (I := I) p (slots r) x)) =
      fderiv ℝ (fun y : E => A ((extChartAt I p).symm y)
        (fun r => chartBasisVecFiber (I := I) p (slots r) ((extChartAt I p).symm y)))
        (extChartAt I p x) (chartModelBasis E d) -
      ∑ r : Fin q, ∑ k : CoordinateIdx (𝕜 := ℝ) E,
        chartChristoffel (I := I) g p d (slots r) k (extChartAt I p x) *
          A x (fun s => chartBasisVecFiber (I := I) p (Function.update slots r k s) x) := by
  classical
  let e := trivializationAt E (TangentSpace I) p
  let frame := e.localFrame (chartModelBasis E)
  let hframe := e.isLocalFrameOn_localFrame_baseSet I (∞ : WithTop ℕ∞) (chartModelBasis E)
  let hframeOne := e.isLocalFrameOn_localFrame_baseSet I (1 : WithTop ℕ∞) (chartModelBasis E)
  have hxframe : x ∈ e.baseSet := chartLeviCivitaGoodSet_mem_baseSet (I := I) hx
  have hstep := totalNabla0S_apply_localFrameAt (I := I) (metricCov (I := I) g)
    A nablaA hreal frame hframeOne e.open_baseSet x hxframe d slots
  let f : M → ℝ := fun y => A y (fun r => frame (slots r) y)
  let fE : E → ℝ := fun y => A ((extChartAt I p).symm y)
    (fun r => chartBasisVecFiber (I := I) p (slots r) ((extChartAt I p).symm y))
  let y₀ := extChartAt I p x
  have hxchart : x ∈ (chartAt H p).source := chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hxint : y₀ ∈ interior ((extChartAt I p).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  have hmdiff : MDifferentiableAt I 𝓘(ℝ) f x :=
    tensor0SField_localFrame_mdiffAt (I := I) A frame hframe e.open_baseSet x hxframe slots
  have htarget : ∀ᶠ y in 𝓝 y₀, y ∈ (extChartAt I p).target :=
    mem_of_superset (isOpen_interior.mem_nhds hxint) interior_subset
  have hscalar : scalarOnE (I := I) p f =ᶠ[𝓝 y₀] fE := by
    filter_upwards [htarget] with y hy
    have hyframe : (extChartAt I p).symm y ∈ e.baseSet :=
      chartLeviCivitaGoodSet_mem_baseSet (I := I)
        ((mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source (I := I) p _).2
          ((extChartAt I p).map_target hy))
    simp only [scalarOnE_def, f, fE]
    congr 1
    funext r
    exact localFrame_eq_chartBasisVec (I := I) p hyframe (slots r)
  have hlocal (k : CoordinateIdx (𝕜 := ℝ) E) : frame k x = chartBasisVecFiber (I := I) p k x :=
    localFrame_eq_chartBasisVec (I := I) p hxframe k
  have hderiv : mvfderiv (I := I) f x (frame d x) =
      fderiv ℝ fE y₀ (chartModelBasis E d) := by
    rw [hlocal]
    change (mfderiv I 𝓘(ℝ) f x : TangentSpace I x →L[ℝ] ℝ)
      (chartBasisVecFiber (I := I) p d x) = _
    rw [mfderiv_chartBasisVecFiber_of_mdifferentiableAt (I := I) p hmdiff hxchart hxint d]
    change fderiv ℝ (scalarOnE (I := I) p f) y₀ (chartModelBasis E d) = _
    rw [hscalar.fderiv_eq (𝕜 := ℝ)]
  have hchr (a b k : CoordinateIdx (𝕜 := ℝ) E) :
      christoffelSymbolInFrame (metricCov (I := I) g) frame hframeOne x a b k =
        chartChristoffel (I := I) g p a b k y₀ :=
    christoffelSymbolInFrame_eq_chartChristoffel (I := I) g p hx a b k
  change nablaA x (Fin.cons (frame d x) (fun r => frame (slots r) x)) =
    mvfderiv (I := I) f x (frame d x) -
      ∑ r : Fin q, ∑ k : CoordinateIdx (𝕜 := ℝ) E,
        christoffelSymbolInFrame (metricCov (I := I) g) frame hframeOne x d (slots r) k *
          A x (fun s => frame (Function.update slots r k s) x) at hstep
  rw [hderiv] at hstep
  simpa only [hchr, hlocal, fE, y₀] using hstep

end DifferentialGeometry.Geometry.Connection
