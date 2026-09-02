import DifferentialGeometry.Topology.Morse.Defs
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

theorem isNondegenerateCriticalPointAt_of_hessFun_eq_smul_metric
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯) (x : M)
    (hcrit : IsCriticalPointAt I f x) {c : Real} (hc : c ≠ 0)
    (hhess : ∀ v w : TangentSpace I x,
      hessFun (I := I) g f x v w = c * g.inner x v w) :
    IsNondegenerateCriticalPointAt I f x := by
  let F : E → Real := f ∘ (extChartAt I x).symm
  let y : E := extChartAt I x x
  let e := centeredChartTangentEquiv (I := I) x
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  have hxsrc_ext : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source_eq_chartAt_source]
    exact hxsrc
  have hytgt : y ∈ (extChartAt I x).target := by
    exact (extChartAt I x).map_source hxsrc_ext
  have hyint : y ∈ interior ((extChartAt I x).target : Set E) :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) x hytgt
  have hFsmooth : ContDiffOn Real ∞ F (interior ((extChartAt I x).target : Set E)) :=
    (scalarOnE_contDiffOn (I := I) x f.contMDiff).mono interior_subset
  have hFderiv : DifferentiableAt Real (fderiv Real F) y := by
    have hsmooth : ContDiffOn Real ∞ (fderiv Real F)
        (interior ((extChartAt I x).target : Set E)) :=
      hFsmooth.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
    exact (hsmooth.contDiffAt (isOpen_interior.mem_nhds hyint)).differentiableAt (by simp)
  have hpartial : ∀ k : Fin (Module.finrank Real E),
      partialDeriv (E := E) k F y = 0 := by
    intro k
    have hbridge :=
      mfderiv_scalar_eq_chart_fderiv
        (I := I) x f hxsrc hyint
          (f.contMDiff.mdifferentiable (by simp) x)
          (centeredChartTangentBasis (I := I) x k)
    have hzero : mvfderiv (I := I) f x
        (centeredChartTangentBasis (I := I) x k) = 0 := by
      change (mfderiv I 𝓘(Real, Real) f x)
        (centeredChartTangentBasis (I := I) x k) = 0
      rw [hcrit]
      rfl
    rw [hzero, trivToE_self_apply, centeredChartTangentBasis_apply,
      ContinuousLinearEquiv.apply_symm_apply] at hbridge
    unfold partialDeriv
    simpa [F, y] using hbridge.symm
  have hiter : ∀ i j : Fin (Module.finrank Real E),
      chartIteratedPartialDeriv (I := I) x f i j y =
        chartHessianBilinAt F y (chartModelBasis E i) (chartModelBasis E j) := by
    intro i j
    let L : (E →L[Real] Real) →L[Real] Real :=
      ContinuousLinearMap.apply Real Real (chartModelBasis E j)
    have hcomp : (fun z : E => fderiv Real F z (chartModelBasis E j)) =
        L ∘ fderiv Real F := rfl
    change partialDeriv (E := E) i (partialDeriv (E := E) j F) y =
      chartHessianBilinAt F y (chartModelBasis E i) (chartModelBasis E j)
    unfold partialDeriv
    rw [hcomp, fderiv_comp y L.differentiableAt hFderiv, L.fderiv]
    rfl
  have hform : chartHessianBilinAt F y =
      (hessFun (I := I) g f x).compl₁₂ e.symm.toLinearMap e.symm.toLinearMap := by
    apply (LinearMap.ext_iff_basis (chartModelBasis E) (chartModelBasis E)).2
    intro i j
    change chartHessianBilinAt F y (chartModelBasis E i) (chartModelBasis E j) =
      hessFun (I := I) g f x (e.symm (chartModelBasis E i))
        (e.symm (chartModelBasis E j))
    rw [show e.symm (chartModelBasis E i) =
          centeredChartTangentBasis (I := I) x i by rfl,
      show e.symm (chartModelBasis E j) =
          centeredChartTangentBasis (I := I) x j by rfl,
      hessFun_basis_apply, ← hiter, chartHessianTensor_def]
    change chartIteratedPartialDeriv (I := I) x f i j y =
      chartIteratedPartialDeriv (I := I) x f i j y -
        ∑ k, chartChristoffel (I := I) g x i j k y * partialDeriv k F y
    simp [hpartial]
  refine ⟨hcrit, ?_⟩
  apply QuadraticMap.separatingLeft_of_anisotropic
  intro u hu
  have hHessZero : hessFun (I := I) g f x (e.symm u) (e.symm u) = 0 := by
    have hraw : chartHessianBilinAt F y u u = 0 := by
      have hraw' : chartHessianBilinAt
          (fun z : E => f ((extChartAt I x).symm z)) (extChartAt I x x) u u = 0 := by
        simpa [chartHessianAt] using hu
      have hfun : (fun z : E => f ((extChartAt I x).symm z)) = F := by
        funext z
        rfl
      rw [hfun] at hraw'
      simpa [y] using hraw'
    rw [hform] at hraw
    exact hraw
  rw [hhess] at hHessZero
  have hinner : g.inner x (e.symm u) (e.symm u) = 0 :=
    (mul_eq_zero.mp hHessZero).resolve_left hc
  have htangent : e.symm u = 0 := by
    by_contra hne
    exact (ne_of_gt (g.pos x (e.symm u) hne)) hinner
  apply e.symm.injective
  simpa using htangent

end DifferentialGeometry.Topology.Morse
