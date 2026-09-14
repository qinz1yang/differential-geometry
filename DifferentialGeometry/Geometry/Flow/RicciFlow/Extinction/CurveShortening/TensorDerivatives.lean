import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Basic
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.TensorDerivativeAlong
import DifferentialGeometry.Tensor.Multilinear.Bundle.Evaluation

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Tensor0SBundle

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem ds_tensor_eval (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) {r : ℕ}
    (A : ℝ → Tensor0SField (I := I) (M := M) (n := ∞) r) (V : Fin r → c.Field (I := I))
    (x t : ℝ) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x)
    (hV : ∀ i, DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t) (fun y => V i y t) x) x) :
    c.ds g (fun y τ => A τ (c.lift y τ) (fun i => V i y τ)) x t =
      totalNabla0SFun r (LeviCivita (g t)) (A t) (c.lift x t)
        (Fin.cons (c.unitTangent g x t) (fun i => V i x t)) +
      ∑ i, A t (c.lift x t) (Function.update (fun j => V j x t) i (c.Ds g (V i) x t)) := by
  classical
  have hd := tensor_eval_deriv (g t) (A t) (fun y => c.lift y t) (fun i y => V i y t) x hγ hV
  change HasDerivAt (fun y => A t (c.lift y t) (fun i => V i y t))
    (totalNabla0SFun r (LeviCivita (g t)) (A t) (c.lift x t)
      (Fin.cons (c.X x t) (fun i => V i x t)) +
    ∑ i, A t (c.lift x t) (Function.update (fun j => V j x t) i (c.Dx g (V i) x t))) x at hd
  have hn : totalNabla0SFun r (LeviCivita (g t)) (A t) (c.lift x t)
      (Fin.cons (c.unitTangent g x t) (fun i => V i x t)) =
      (c.speed g x t)⁻¹ * totalNabla0SFun r (LeviCivita (g t)) (A t) (c.lift x t)
        (Fin.cons (c.X x t) (fun i => V i x t)) := by
    let N : ContinuousMultilinearMap ℝ (fun _ : Fin (r + 1) => TangentSpace I (c.lift x t)) ℝ :=
      totalNabla0SFun r (LeviCivita (g t)) (A t) (c.lift x t)
    change N.curryLeft ((c.speed g x t)⁻¹ • c.X x t) (fun i => V i x t) =
      (c.speed g x t)⁻¹ * N.curryLeft (c.X x t) (fun i => V i x t)
    exact congrArg (fun U : ContinuousMultilinearMap ℝ (fun _ : Fin r => TangentSpace I (c.lift x t)) ℝ =>
      U (fun i => V i x t)) (N.curryLeft.map_smul (c.speed g x t)⁻¹ (c.X x t))
  have hv (i : Fin r) : A t (c.lift x t) (Function.update (fun j => V j x t) i (c.Ds g (V i) x t)) =
      (c.speed g x t)⁻¹ * A t (c.lift x t) (Function.update (fun j => V j x t) i (c.Dx g (V i) x t)) := by
    change A t (c.lift x t) (Function.update (fun j => V j x t) i
      ((c.speed g x t)⁻¹ • c.Dx g (V i) x t)) = _
    exact (A t (c.lift x t)).map_update_smul (fun j => V j x t) i (c.speed g x t)⁻¹ (c.Dx g (V i) x t)
  rw [CurveMap.ds, hd.deriv, hn]
  simp_rw [hv]
  rw [mul_add, Finset.mul_sum]

omit [I.Boundaryless] [T2Space M] in
theorem contDiffAt_tensor_eval (c : CurveMap M) {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) (n := ∞) r) (V : Fin r → c.Field (I := I))
    (x t : ℝ) (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) x)
    (hV : ∀ i, ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞
      (fun y => (⟨c.lift y t, V i y t⟩ : TangentBundle I M)) x) :
    ContDiffAt ℝ ∞ (fun y => A (c.lift y t) (fun i => V i y t)) x := by
  have hh := DifferentialGeometry.TensorMultilinear.contMDiffWithinAt_section_apply_base r
    (fun y => c.lift y t) hγ.contMDiffWithinAt
    (fun y => A (c.lift y t))
    ((A.contMDiff.contMDiffAt.comp x hγ).contMDiffWithinAt (s := univ))
    (fun i y => V i y t) (fun i => (hV i).contMDiffWithinAt)
  apply contMDiffAt_iff_contDiffAt.mp
  apply contMDiffWithinAt_univ.mp
  exact hh

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap
