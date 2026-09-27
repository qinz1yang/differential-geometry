import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.MetricCompatibleTimeDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.StarSum.SolutionResidual

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem tensor_deriv_of_basis {ι : Type*} [Finite ι] {s : ℕ} {x : M}
    (basis : Module.Basis ι ℝ (TangentSpace I x))
    (T : ℝ → Tensor0SSpace s I x) (Tdot : Tensor0SSpace s I x) (J : Set ℝ) (t : ℝ)
    (h : ∀ m : Fin s → ι, HasDerivWithinAt (fun r => component0S basis (T r) m)
      (component0S basis Tdot m) J t) : HasDerivWithinAt T Tdot J t := by
  classical
  let _ := Fintype.ofFinite ι
  let b := tensor0SBasis (I := I) basis s
  have hh := HasDerivWithinAt.sum (u := Finset.univ) (fun m _ => (h m).smul_const (b m))
  have he : (∑ m, fun r => component0S basis (T r) m • b m) = T := by
    funext r
    rw [Finset.sum_apply]
    simpa only [b, ← tensor0SBasis_repr] using (tensor0SBasis (I := I) basis s).sum_repr (T r)
  have he' : (∑ m, component0S basis Tdot m • b m) = Tdot := by
    simpa only [b, ← tensor0SBasis_repr] using (tensor0SBasis (I := I) basis s).sum_repr Tdot
  rw [he, he'] at hh
  exact hh

variable [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space M] [BoundarylessManifold I M]

theorem hasDerivWithinAt_curvature_canonical_residual {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (k : ℕ) (t : RealTimeInterval.RegularTime D) (x : M) :
    HasDerivWithinAt (fun r => nablaKRm04Field S r k x)
      (metricTraceFirstTwo0STensor (S.base.metric (t : ℝ))
        (nablaKRm04Field S (t : ℝ) (k + 2) x) + rmResidualField S t k x)
      D.carrier (t : ℝ) := by
  classical
  let g := S.base.metric (t : ℝ)
  let frame := smoothOrthoFrame (I := I) g x
  let U := smoothOrthoOpen (I := I) (M := M) x
  have hU : IsOpen U := smoothOrthoOpen_open (I := I) (M := M) x
  have hx : x ∈ U := mem_smoothOrthoOpen (I := I) (M := M) x
  have hframe : IsLocalFrameOn I E ∞ frame U := smoothOrtho_local (I := I) g x
  have horthU (y : M) (hy : y ∈ U) (i j : Fin (Module.finrank ℝ E)) :
      g.inner y (frame i y) (frame j y) = if i = j then (1 : ℝ) else 0 :=
    smoothOrthoFrame_orthonormal (I := I) g x (interior_subset hy) i j
  obtain ⟨hf, baseDt, chrDt, hrm, hchr, hchrId, hswap⟩ :=
    towerDataAt S hS t frame hframe hU horthU
  have hevol : ∀ j : ℕ, ∀ (y : M) (hy : y ∈ U) (m : Fin (4 + j) → Fin (Module.finrank ℝ E)),
      HasDerivWithinAt
        (fun r => tensor0SComponent (nablaKRm04Field S r j y) (fun i => frame i y) m)
        (tensor0SComponent
          (metricTrace0S2TensorInBasis (hf.toBasisAt hy) identityInvMetric
            (nablaKRm04Field S (t : ℝ) (j + 2) y) + rmResidualField S t j y)
          (fun i => frame i y) m) D.carrier (t : ℝ) := by
    intro j
    induction j with
    | zero =>
        intro y hy m
        have ho (i j : Fin (Module.finrank ℝ E)) :
            g.inner y ((hf.toBasisAt hy) i) ((hf.toBasisAt hy) j) =
              if i = j then (1 : ℝ) else 0 := by
          rw [hf.toBasisAt_coe hy i, hf.toBasisAt_coe hy j]
          exact horthU y hy i j
        simpa only [rmResidualField, hf.toBasisAt_coe hy] using
          (e0Residual S hS t (Idx := Fin (Module.finrank ℝ E))).2 y (hf.toBasisAt hy) ho m
    | succ j ih =>
        intro y hy m
        simpa only [rmResidualField] using
          (resStarNext_spec S j t frame hf hU horthU baseDt chrDt hrm hchr hchrId hswap
            (rmResidualField S t j) (rmResidualField_cost S hS t j) ih).2 y hy m
  let basis := hf.toBasisAt hx
  have horth (i j : Fin (Module.finrank ℝ E)) :
      g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
    simpa only [basis, hf.toBasisAt_coe hx] using horthU x hx i j
  let L := metricTrace0S2TensorInBasis basis identityInvMetric
    (nablaKRm04Field S (t : ℝ) (k + 2) x)
  have hd : HasDerivWithinAt (fun r => nablaKRm04Field S r k x)
      (L + rmResidualField S t k x) D.carrier (t : ℝ) := by
    apply tensor_deriv_of_basis basis
    intro m
    have hh := hevol k x hx m
    simp only [component0S_apply, tensor0SComponent, L, basis, hf.toBasisAt_coe hx] at hh ⊢
    convert hh using 1
    rfl
  have hL : metricTraceFirstTwo0STensor g (nablaKRm04Field S (t : ℝ) (k + 2) x) = L := by
    apply tensor0SSpace_ext (4 + k) x
    intro v
    rw [metricTraceFirstTwo0STensor_apply, metricTrace0S2TensorInBasis_apply]
    exact metricTraceFirstTwo0SAt_eq_sum_basis g basis identityInvMetric
      (metricInverseInBasis_identity_of_orthonormal g basis horth) _ v
  exact hd.congr_deriv (congrArg (fun V : Tensor0SSpace (4 + k) I x =>
    V + rmResidualField S t k x) hL.symm)

theorem covariantTimeDerivWithin_curvature_canonical_residual {D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (k : ℕ) (t : RealTimeInterval.RegularTime D) (x : M) :
    covariantTimeDerivWithin S.base.metric (fun r => nablaKRm04Field S r k x) D.carrier (t : ℝ) =
      metricTraceFirstTwo0STensor (S.base.metric (t : ℝ))
        (nablaKRm04Field S (t : ℝ) (k + 2) x) + rmResidualField S t k x +
      ricciTimeCorrection (S.base.metric (t : ℝ)) (nablaKRm04Field S (t : ℝ) k x) := by
  have hd := (hasDerivWithinAt_curvature_canonical_residual S hS k t x).derivWithin
    (uniqueDiffWithinAt_of_mem_nhds (D.regular_mem_nhds t.2))
  exact congrArg (fun V : Tensor0SSpace (4 + k) I x =>
    V + ricciTimeCorrection (S.base.metric (t : ℝ)) (nablaKRm04Field S (t : ℝ) k x)) hd
end DifferentialGeometry.PDE.RicciFlow
