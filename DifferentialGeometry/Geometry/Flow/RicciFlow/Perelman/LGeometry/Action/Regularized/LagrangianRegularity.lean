import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.FirstVariation
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.FiniteIntegral
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Regularized
set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Tensor0SBundle
open MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lRegularizedScalar_contDiffOn_two
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real ↦ S.scalar (T - p.2 ^ 2) (f p.1 p.2))
      {p : Real × Real | T - p.2 ^ 2 ∈ D.regular} := by
  intro p hp
  have hfAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ f q.1 q.2) p :=
    (hf : ContMDiff _ _ (8 : Nat) _).contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ (T - q.2 ^ 2, f q.1 q.2)) p :=
    (contMDiffAt_const.sub (contMDiffAt_snd.pow 2)).prodMk hfAt
  have hscalar₀ : ContMDiffAt
      (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun q : Real × M ↦ S.scalar q.1 q.2)
      (T - p.2 ^ 2, f p.1 p.2) :=
    (scalar_joint (I := I) S hS).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds hp) Filter.univ_mem)
  have hscalarMD : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ S.scalar (T - q.2 ^ 2) (f q.1 q.2)) p :=
    (hscalar₀.of_le (by
      change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)).comp p harg
  have hscalar : ContDiffAt Real 2
      (fun q : Real × Real ↦ S.scalar (T - q.2 ^ 2) (f q.1 q.2)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalarMD
  exact hscalar.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lRegularizedSpeed_contDiffOn_two
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real ↦
        (S.base.metric (T - p.2 ^ 2)).inner (f p.1 p.2)
          (lVelocity (I := I) (f p.1) p.2)
          (lVelocity (I := I) (f p.1) p.2))
      {p : Real × Real | T - p.2 ^ 2 ∈ D.regular} := by
  intro p hp
  have hfAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ f q.1 q.2) p :=
    (hf : ContMDiff _ _ (8 : Nat) _).contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦ (T - q.2 ^ 2, f q.1 q.2)) p :=
    (contMDiffAt_const.sub (contMDiffAt_snd.pow 2)).prodMk hfAt
  have hmetric₀ := hS.smoothMetric.metricCLMSmoothAt
    (t := T - p.2 ^ 2) (x := f p.1 p.2)
    (D.regular_isOpen.mem_nhds hp)
  have hmetric : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y ↦ TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (f q.1 q.2) ((S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2))) p := by
    have hcomp := (hmetric₀.of_le (by
        change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
        exact WithTop.coe_le_coe.mpr le_top)).comp p harg
    rw [SolutionOn.family_metric] at hcomp
    with_unfolding_all exact hcomp
  have hvel : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2) : TangentBundle I M)) p := by
    simpa only [lVelocity] using
      ((velocity_totalSpace_contMDiff (I := I) (M := M) f hf) p).of_le
        (by norm_num)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun y : M ↦ TangentSpace I y)
    (E₂ := fun y : M ↦ TangentSpace I y)
    (E₃ := fun _ : M ↦ Real) hmetric hvel hvel
  have hscalar : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun q : Real × Real ↦
        (S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2)
          (lVelocity (I := I) (f q.1) q.2)) p := by
    rw [Bundle.contMDiffAt_totalSpace] at htotal
    with_unfolding_all exact htotal.2
  have hcd : ContDiffAt Real 2
      (fun q : Real × Real ↦
        (S.base.metric (T - q.2 ^ 2)).inner (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2)
          (lVelocity (I := I) (f q.1) q.2)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalar
  exact hcd.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lRegularizedLagrangian_contDiffOn_two
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real ↦ lRegularizedLagrangian S T (f p.1) p.2)
      {p : Real × Real | T - p.2 ^ 2 ∈ D.regular} := by
  have hscalar := lRegularizedScalar_contDiffOn_two (I := I) S hS T f hf
  have hspeed := lRegularizedSpeed_contDiffOn_two (I := I) S hS T f hf
  simpa only [lRegularizedLagrangian] using
    (contDiffOn_const.mul hspeed).add
      ((contDiffOn_const.mul (contDiffOn_snd.pow 2)).mul hscalar)

end DifferentialGeometry.PDE.RicciFlow.Perelman
