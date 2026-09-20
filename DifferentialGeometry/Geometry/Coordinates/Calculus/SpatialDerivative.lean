import DifferentialGeometry.Geometry.Coordinates.Calculus.FixedBaseDerivative
import Mathlib.Analysis.Calculus.FDeriv.Prod


noncomputable section

namespace DifferentialGeometry

open Filter
open scoped Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem fderiv_chart_comp_inl_apply_eq_mvfderiv
    {f : M → ℝ → ℝ} {x p : M} {t : ℝ}
    (hp : p ∈ (chartAt H x).source)
    (hjoint : DifferentiableAt ℝ
      (fun z : E × ℝ => f ((extChartAt I x).symm z.1) z.2)
      (extChartAt I x p, t)) (v : E) :
    ((fderiv ℝ (fun z : E × ℝ => f ((extChartAt I x).symm z.1) z.2)
      (extChartAt I x p, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) v =
        mvfderiv (I := I) (fun y => f y t) p
          (TensorLieDeriv.tangentConstInChart (𝕜 := ℝ) (I := I) x v p) := by
  have hspatial := hjoint.hasFDerivAt.comp (extChartAt I x p)
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) (extChartAt I x p) t)
  have hslice : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun y => f y t) p := by
    apply (mdifferentiableAt_iff_source_of_mem_source
      (I := I) (I' := 𝓘(ℝ, ℝ)) (x := x) (x' := p) hp).mpr
    exact hspatial.differentiableAt.mdifferentiableAt.mdifferentiableWithinAt
  have hchart := mvfderiv_tangentConstInChart_eq_fderiv hp hslice v
  have hfun : writtenInExtChartAt I 𝓘(ℝ, ℝ) x (fun y => f y t) =
      (fun y : E => f ((extChartAt I x).symm y) t) := by
    funext y
    rw [writtenInExtChartAt, extChartAt_model_space_eq_id]
    rfl
  rw [hfun] at hchart
  have hchain := hspatial.fderiv
  exact (congrArg (fun L : E →L[ℝ] ℝ => L v) hchain).symm.trans hchart.symm

theorem tendsto_fderiv_chart_comp_inl_apply
    {ι : Type*} {L : Filter ι} {F : ι → M → ℝ → ℝ} {f : M → ℝ → ℝ}
    {x p : M} {t : ℝ} (hp : p ∈ (chartAt H x).source)
    (hFjoint : ∀ᶠ k in L, DifferentiableAt ℝ
      (fun z : E × ℝ => F k ((extChartAt I x).symm z.1) z.2)
      (extChartAt I x p, t))
    (hfjoint : DifferentiableAt ℝ
      (fun z : E × ℝ => f ((extChartAt I x).symm z.1) z.2)
      (extChartAt I x p, t)) (v : E)
    (hlim : Tendsto (fun k => mvfderiv (I := I) (fun y => F k y t) p
        (TensorLieDeriv.tangentConstInChart (𝕜 := ℝ) (I := I) x v p)) L
      (𝓝 (mvfderiv (I := I) (fun y => f y t) p
        (TensorLieDeriv.tangentConstInChart (𝕜 := ℝ) (I := I) x v p)))) :
    Tendsto (fun k => ((fderiv ℝ
      (fun z : E × ℝ => F k ((extChartAt I x).symm z.1) z.2)
      (extChartAt I x p, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) v) L
      (𝓝 (((fderiv ℝ (fun z : E × ℝ => f ((extChartAt I x).symm z.1) z.2)
        (extChartAt I x p, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) v)) := by
  rw [fderiv_chart_comp_inl_apply_eq_mvfderiv hp hfjoint v]
  apply hlim.congr'
  filter_upwards [hFjoint] with k hkj
  exact (fderiv_chart_comp_inl_apply_eq_mvfderiv hp hkj v).symm

end DifferentialGeometry
