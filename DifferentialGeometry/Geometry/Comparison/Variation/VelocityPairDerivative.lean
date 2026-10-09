import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation.Basic
import DifferentialGeometry.Geometry.Comparison.Variation.Covariant.TwoParameterFields

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem hasDerivAt_inner_varFst_varSnd
    (g : SmoothRiemannianMetric I M)
    (f : ℝ → ℝ → M) (hf : IsSmoothVariation (I := I) f) (c : ℝ) :
    HasDerivAt (fun u ↦ g.inner (f u c) (varFst (I := I) f u c)
      (varSnd (I := I) f u c))
      (g.inner (f 0 c)
          (covDerivAlong (I := I) g (fun u ↦ f u c)
            (fun u ↦ varFst (I := I) f u c) 0)
          (varSnd (I := I) f 0 c) +
        g.inner (f 0 c) (varFst (I := I) f 0 c)
          (covDerivAlong (I := I) g (f 0)
            (fun s ↦ varFst (I := I) f 0 s) c)) 0 := by
  let node : ℝ → M := fun u ↦ f u c
  let U : (u : ℝ) → TangentSpace I (node u) := fun u ↦ varFst (I := I) f u c
  let A : (u : ℝ) → TangentSpace I (node u) := fun u ↦ varSnd (I := I) f u c
  have hnode : ContMDiff 𝓘(ℝ, ℝ) I (8 : ℕ) node :=
    hf.comp (contMDiff_id.prodMk contMDiff_const)
  have hU : DifferentiableAt ℝ (chartRepAt (I := I) node U 0) 0 := by
    change DifferentiableAt ℝ
      (fun u ↦
        (trivializationAt E (TangentSpace I) (node 0)).continuousLinearMapAt ℝ
          (node u) (U u)) 0
    simpa only [node, U, varFst] using
      DifferentialGeometry.Geometry.Riemannian.MFDerivAlongCurve.velocity_coord_diff
        (I := I) node 0 (hnode.contMDiffAt.of_le (by norm_num))
  have hA : DifferentiableAt ℝ (chartRepAt (I := I) node A 0) 0 := by
    exact slice_longitudinalField_transverse_chartRep_differentiableAt (I := I) f hf c
  have hinner := inner_deriv_at (I := I) (n := (8 : WithTop ℕ∞))
    (by norm_num) g node U A 0 hnode.contMDiffAt hU hA
  have hcomm := commute_ds_dt_intrinsic (I := I) g f hf c
  apply hinner.congr_deriv
  simpa only [node, U, A, varFst, varSnd] using
    congrArg (fun z ↦
      g.inner (f 0 c)
          (covDerivAlong (I := I) g (fun u ↦ f u c)
            (fun u ↦ varFst (I := I) f u c) 0)
          (varSnd (I := I) f 0 c) +
        g.inner (f 0 c) (varFst (I := I) f 0 c) z) hcomm

end DifferentialGeometry.Geometry.Riemannian.Variation
