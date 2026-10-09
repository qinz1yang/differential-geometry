import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.TimeExpression
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.EndpointRiemannNorm
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Ricci.Trace
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram
import DifferentialGeometry.Geometry.Metric.TensorInner.Cotangent.Riemannian

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow Bundle.continuousMultilinearMap
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Integral.Measure DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem product_contDiffOn {ι : Type*} [Finite ι] {s q : ℕ} {x : M}
    (basis : Module.Basis ι ℝ (TangentSpace I x))
    (A : ℝ → Tensor0SSpace s I x) (B : ℝ → Tensor0SSpace q I x) (J : Set ℝ)
    (hA : ContDiffOn ℝ ∞ A J) (hB : ContDiffOn ℝ ∞ B J) :
    let P : ℝ → Tensor0SSpace (s + q) I x :=
      fun r => productFun (F := E) (E := TangentSpace I) (A r) (B r)
    ContDiffOn ℝ ∞ P J := by
  apply tensor0S_contDiffOn_of_components basis
  intro m
  let v := fun a => basis (m a)
  have ha := (tensor0SEvalCLM (I := I) (v ∘ Fin.castAdd q)).contDiff.comp_contDiffOn hA
  have hb := (tensor0SEvalCLM (I := I) (v ∘ Fin.natAdd s)).contDiff.comp_contDiffOn hB
  apply (ha.mul hb).congr
  intro r _
  exact product_fun_apply (A r) (B r) v

private theorem perm_contDiffOn {ι : Type*} [Finite ι] {s s' : ℕ} {x : M}
    (basis : Module.Basis ι ℝ (TangentSpace I x)) (T : ℝ → Tensor0SSpace s I x)
    (e : Fin s ≃ Fin s') (J : Set ℝ) (hT : ContDiffOn ℝ ∞ T J) :
    ContDiffOn ℝ ∞ (fun r => (T r).domDomCongr e) J := by
  apply tensor0S_contDiffOn_of_components basis
  intro m
  exact (tensor0SEvalCLM (I := I) ((fun a => basis (m a)) ∘ e)).contDiff.comp_contDiffOn hT

private theorem trace_contDiffOn {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ℕ} {x : M}
    (g : ℝ → SmoothRiemannianMetric I M) (T : ℝ → Tensor0SSpace (s + 2) I x)
    (basis : Module.Basis ι ℝ (TangentSpace I x)) (B : ℝ → ι → ι → ℝ) (J : Set ℝ)
    (hB : ∀ t ∈ J, MetricInverseInBasis (g t) x basis (B t))
    (hBs : ∀ i j, ContDiffOn ℝ ∞ (fun t => B t i j) J) (hT : ContDiffOn ℝ ∞ T J) :
    ContDiffOn ℝ ∞ (fun r => metricTraceFirstTwo0STensor (g r) (T r)) J := by
  apply tensor0S_contDiffOn_of_components basis
  intro m
  let v := fun a => basis (m a)
  have ht (i j : ι) := (tensor0SEvalCLM (I := I)
    (metricTraceInput (basis i) (basis j) v)).contDiff.comp_contDiffOn hT
  have hh := ContDiffOn.sum (fun (i : ι) (_ : i ∈ Finset.univ) =>
    ContDiffOn.sum (fun (j : ι) (_ : j ∈ Finset.univ) => (hBs i j).mul (ht i j)))
  apply hh.congr
  intro t htJ
  rw [component0S_apply, metricTraceFirstTwo0STensor_apply]
  exact metricTraceFirstTwo0SAt_eq_sum_basis (g t) basis (B t) (hB t htJ) (T t) v

variable [CompleteSpace E] [T2Space M] [I.Boundaryless]
section Regularity
variable {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (J : Set ℝ) (hJ : UniqueDiffOn ℝ J)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
include hJ hgram

theorem curvature_tensor_contDiffOn (a : ℕ) (x : M) :
    ContDiffOn ℝ ∞ (fun t => nablaKRm04Field S t a x) J := by
  let basis := coordinateFrameAtToBasis (I := I) x
  apply tensor0S_contDiffOn_of_components basis
  intro m
  have hh := covariantRiemannComponents_contMDiffOn S.base.metric J hJ hgram x a m
  have hs := hh.comp (contMDiffOn_id.prodMk (contMDiffOn_const (c := x)))
    (fun r hr => ⟨hr, self_mem_chartLeviCivitaGoodSet (I := I) x⟩)
  have he : (fun r => component0S basis (nablaKRm04Field S r a x) m) =
      (fun r => iterCov (S.base.metric r) 4 (metricRm04 (S.base.metric r)) a x
        (frameTuple (coordinateFrameAt (I := I) x) x m)) := by
    funext r
    unfold component0S
    rw [nablaKRm_eq_iterCov]
    apply congrArg (iterCov (S.base.metric r) 4 (metricRm04 (S.base.metric r)) a x)
    funext q
    exact coordinateFrameAt_toBasis_apply (I := I) x (m q)
  rw [he]
  exact hs.contDiffOn

theorem CurvatureExpression.eval_contDiffOn {s : ℕ} (A : CurvatureExpression s) (x : M) :
    ContDiffOn ℝ ∞ (fun t => A.eval S t x) J := by
  let basis := coordinateFrameAtToBasis (I := I) x
  let B := fun t (i j : CoordinateIdx (𝕜 := ℝ) E) =>
    inverseMetricFlatModelInChartComponent (S.base.metric t) x i j (extChartAt I x x)
  have hB (t : ℝ) (_ : t ∈ J) : MetricInverseInBasis (S.base.metric t) x basis (B t) :=
    gInvBasisAt (S.base.metric t) x (coordinateFrameAt_mem (I := I) x)
  have hBs (i j : CoordinateIdx (𝕜 := ℝ) E) : ContDiffOn ℝ ∞ (fun t => B t i j) J := by
    have hh := inverseComponents_contMDiffOn S.base.metric J hgram x i j
    have hs := hh.comp (contMDiffOn_id.prodMk (contMDiffOn_const (c := x)))
      (fun r hr => ⟨hr, self_mem_chartLeviCivitaGoodSet (I := I) x⟩)
    exact hs.contDiffOn
  induction A with
  | curvature k => exact curvature_tensor_contDiffOn S J hJ hgram k x
  | zero s => exact contDiffOn_const
  | add A B ihA ihB => exact ihA.add ihB
  | smul c A ih => exact ih.const_smul c
  | product A C ihA ihC => exact product_contDiffOn basis _ _ J ihA ihC
  | perm e A ih => exact perm_contDiffOn basis _ e J ih
  | trace A ih => exact trace_contDiffOn S.base.metric _ basis B J hB hBs ih

variable [BoundarylessManifold I M]

theorem CurvatureExpression.time_jet_contDiffOn {s : ℕ} (A : CurvatureExpression s) (b : ℕ) (x : M) :
    let U := iteratedCovariantTimeDerivWithin S.base.metric (fun t => A.eval S t x) J b
    ContDiffOn ℝ ∞ U J ∧
      ContDiffOn ℝ ∞ (fun t => normSq0S (S.base.metric t) x s (U t)) J := by
  let basis := coordinateFrameAtToBasis (I := I) x
  let B := fun t (i j : CoordinateIdx (𝕜 := ℝ) E) =>
    inverseMetricFlatModelInChartComponent (S.base.metric t) x i j (extChartAt I x x)
  have hB (t : ℝ) (_ : t ∈ J) : MetricInverseInBasis (S.base.metric t) x basis (B t) :=
    gInvBasisAt (S.base.metric t) x (coordinateFrameAt_mem (I := I) x)
  have hBs (i j : CoordinateIdx (𝕜 := ℝ) E) : ContDiffOn ℝ ∞ (fun t => B t i j) J := by
    have hh := inverseComponents_contMDiffOn S.base.metric J hgram x i j
    have hs := hh.comp (contMDiffOn_id.prodMk (contMDiffOn_const (c := x)))
      (fun r hr => ⟨hr, self_mem_chartLeviCivitaGoodSet (I := I) x⟩)
    exact hs.contDiffOn
  have hR (i j : CoordinateIdx (𝕜 := ℝ) E) :
      ContDiffOn ℝ ∞ (fun t => ricciTensor (S.base.metric t) x (basis i) (basis j)) J := by
    have hh := (tensor0SEvalCLM (I := I) (vec2 (basis i) (basis j))).contDiff.comp_contDiffOn
      (CurvatureExpression.eval_contDiffOn S J hJ hgram CurvatureExpression.ricci x)
    apply hh.congr
    intro t _
    exact ((congrArg (fun V : Tensor0SSpace 2 I x => V (vec2 (basis i) (basis j)))
      (CurvatureExpression.eval_ricci S t x)).trans
        (metricRicciAt_apply_eq_ricciTensor (S.base.metric t) x (basis i) (basis j))).symm
  have hT := CurvatureExpression.eval_contDiffOn S J hJ hgram A x
  have hu := iteratedCovariantTimeDerivWithin_contDiffOn S.base.metric _ basis B J hJ hB hBs hR hT b
  exact ⟨hu, normSq0S_contDiffOn_of_basis S.base.metric _ basis B J hB hBs hu⟩
end Regularity

variable [BoundarylessManifold I M] [NeZero (Module.finrank ℝ E)]

theorem CurvatureExpression.eval_timeIter_on {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hJ : UniqueDiffOn ℝ D.carrier)
    (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (S.base.metric p.1) x₀ p.2 i j)
        (D.carrier ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hdense : D.carrier ⊆ closure D.regular) {s : ℕ} (A : CurvatureExpression s)
    (b : ℕ) (x : M) :
    ∀ t ∈ D.carrier,
      iteratedCovariantTimeDerivWithin S.base.metric (fun r => A.eval S r x) D.carrier b t =
        (A.timeIter b).eval S t x := by
  have he : EqOn
      (iteratedCovariantTimeDerivWithin S.base.metric (fun r => A.eval S r x) D.carrier b)
      (fun r => (A.timeIter b).eval S r x) D.regular :=
    fun t ht => A.eval_timeIter S hS b ⟨t, ht⟩ x
  exact he.of_subset_closure
    (A.time_jet_contDiffOn S D.carrier hJ hgram b x).1.continuousOn
    ((A.timeIter b).eval_contDiffOn S D.carrier hJ hgram x).continuousOn D.regular_subset hdense
end DifferentialGeometry.PDE.RicciFlow
