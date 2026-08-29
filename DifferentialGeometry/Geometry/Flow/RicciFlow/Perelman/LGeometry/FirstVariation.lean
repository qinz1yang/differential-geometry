import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.MovingMetric
import DifferentialGeometry.Geometry.Comparison.Variation.CovariantJet
import DifferentialGeometry.Geometry.Metric.Family.PairSmoothness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity
import DifferentialGeometry.Analysis.Calculus.CurveDerivative
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

section normedSpaceCompatibility

attribute [-instance] InnerProductSpace.toNormedSpace

open Bundle
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Variation
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
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lSpeedSq_contDiffOn
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (f : Real → Real → M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 1
      (fun p : Real × Real => lSpeedSq S T (f p.1) p.2)
      {p : Real × Real | T - p.2 ∈ D.regular} := by
  intro p hp
  have hfAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (1 : WithTop ℕ∞)
      (fun q : Real × Real => f q.1 q.2) p :=
    (hf : ContMDiff _ _ (8 : ℕ) _).contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (1 : WithTop ℕ∞)
      (fun q : Real × Real => (T - q.2, f q.1 q.2)) p :=
    (contMDiffAt_const.sub contMDiffAt_snd).prodMk hfAt
  have hmetric₀ := hG.metricCLMSmoothAt
    (t := T - p.2) (x := f p.1 p.2) (D.regular_isOpen.mem_nhds hp)
  have hmetric : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) (1 : WithTop ℕ∞)
      (fun q : Real × Real =>
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y => TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (f q.1 q.2) ((S.base.metric (T - q.2)).inner (f q.1 q.2))) p := by
    simpa only [SolutionOn.family_metric, Function.comp_def] using
      (hmetric₀.of_le (by simp)).comp p harg
  have hvel : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E)) (1 : WithTop ℕ∞)
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2) : TangentBundle I M)) p := by
    simpa only [lVelocity] using
      ((velocity_totalSpace_contMDiff (I := I) (M := M) f hf) p).of_le
        (by norm_num)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun y : M => TangentSpace I y)
    (E₂ := fun y : M => TangentSpace I y)
    (E₃ := fun _ : M => Real) hmetric hvel hvel
  have hscalar : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (1 : WithTop ℕ∞)
      (fun q : Real × Real => lSpeedSq S T (f q.1) q.2) p := by
    rw [Bundle.contMDiffAt_totalSpace] at htotal
    simpa only [lSpeedSq, Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.trivialization_apply] using htotal.2
  have hcd : ContDiffAt Real 1
      (fun q : Real × Real => lSpeedSq S T (f q.1) q.2) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalar
  exact hcd.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lScalar_contDiffOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M)
    (hf : ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I 1
      (fun p : Real × Real => f p.1 p.2)) :
    ContDiffOn Real 1
      (fun p : Real × Real => S.scalar (T - p.2) (f p.1 p.2))
      {p : Real × Real | T - p.2 ∈ D.regular} := by
  intro p hp
  have hfAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (1 : WithTop ℕ∞)
      (fun q : Real × Real => f q.1 q.2) p :=
    hf.contMDiffAt
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (1 : WithTop ℕ∞)
      (fun q : Real × Real => (T - q.2, f q.1 q.2)) p :=
    (contMDiffAt_const.sub contMDiffAt_snd).prodMk hfAt
  have hscalar₀ : ContMDiffAt
      (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun q : Real × M => S.scalar q.1 q.2)
      (T - p.2, f p.1 p.2) :=
    (scalar_joint (I := I) S hS).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds hp) Filter.univ_mem)
  have hscalarMD : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (1 : WithTop ℕ∞)
      (fun q : Real × Real => S.scalar (T - q.2) (f q.1 q.2)) p :=
    (hscalar₀.of_le (by simp)).comp p harg
  have hscalar : ContDiffAt Real 1
      (fun q : Real × Real => S.scalar (T - q.2) (f q.1 q.2)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalarMD
  exact hscalar.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lCore_contDiffOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 1
      (fun p : Real × Real =>
        S.scalar (T - p.2) (f p.1 p.2) + lSpeedSq S T (f p.1) p.2)
      {p : Real × Real | T - p.2 ∈ D.regular} := by
  have hf1 : ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I 1
      (fun p : Real × Real => f p.1 p.2) :=
    (hf : ContMDiff _ _ (8 : ℕ) _).of_le (by norm_num)
  exact (lScalar_contDiffOn S hS T f hf1).add
    (lSpeedSq_contDiffOn S T f hS.smoothMetric hf)

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem lSpeedSq_c2
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (f : Real → Real → M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real => lSpeedSq S T (f p.1) p.2)
      {p : Real × Real | T - p.2 ∈ D.regular} := by
  intro p hp
  have hfAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (2 : WithTop ℕ∞)
      (fun q : Real × Real => f q.1 q.2) p :=
    (hf : ContMDiff _ _ (8 : ℕ) _).contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (2 : WithTop ℕ∞)
      (fun q : Real × Real => (T - q.2, f q.1 q.2)) p :=
    (contMDiffAt_const.sub contMDiffAt_snd).prodMk hfAt
  have hmetric₀ := hG.metricCLMSmoothAt
    (t := T - p.2) (x := f p.1 p.2) (D.regular_isOpen.mem_nhds hp)
  have hmetric : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) (2 : WithTop ℕ∞)
      (fun q : Real × Real =>
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y => TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (f q.1 q.2) ((S.base.metric (T - q.2)).inner (f q.1 q.2))) p := by
    simpa only [SolutionOn.family_metric, Function.comp_def] using
      (hmetric₀.of_le (by
        change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
        exact WithTop.coe_le_coe.mpr le_top)).comp p harg
  have hvel : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E)) (2 : WithTop ℕ∞)
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2) : TangentBundle I M)) p := by
    simpa only [lVelocity] using
      ((velocity_totalSpace_contMDiff (I := I) (M := M) f hf) p).of_le
        (by norm_num)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun y : M => TangentSpace I y)
    (E₂ := fun y : M => TangentSpace I y)
    (E₃ := fun _ : M => Real) hmetric hvel hvel
  have hscalar : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun q : Real × Real => lSpeedSq S T (f q.1) q.2) p := by
    rw [Bundle.contMDiffAt_totalSpace] at htotal
    simpa only [lSpeedSq, Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.trivialization_apply] using htotal.2
  have hcd : ContDiffAt Real 2
      (fun q : Real × Real => lSpeedSq S T (f q.1) q.2) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalar
  exact hcd.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
private theorem lScalar_c2
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real => S.scalar (T - p.2) (f p.1 p.2))
      {p : Real × Real | T - p.2 ∈ D.regular} := by
  intro p hp
  have hfAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (2 : WithTop ℕ∞)
      (fun q : Real × Real => f q.1 q.2) p :=
    (hf : ContMDiff _ _ (8 : ℕ) _).contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (2 : WithTop ℕ∞)
      (fun q : Real × Real => (T - q.2, f q.1 q.2)) p :=
    (contMDiffAt_const.sub contMDiffAt_snd).prodMk hfAt
  have hscalar₀ : ContMDiffAt
      (𝓘(Real, Real).prod I) 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun q : Real × M => S.scalar q.1 q.2)
      (T - p.2, f p.1 p.2) :=
    (scalar_joint (I := I) S hS).contMDiffAt
      (prod_mem_nhds (D.regular_isOpen.mem_nhds hp) Filter.univ_mem)
  have hscalarMD : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun q : Real × Real => S.scalar (T - q.2) (f q.1 q.2)) p :=
    (hscalar₀.of_le (by
      change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
      exact WithTop.coe_le_coe.mpr le_top)).comp p harg
  have hscalar : ContDiffAt Real 2
      (fun q : Real × Real => S.scalar (T - q.2) (f q.1 q.2)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalarMD
  exact hscalar.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem lPair_c2
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (f : Real → Real → M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 2
      (fun p : Real × Real =>
        (S.base.metric (T - p.2)).inner (f p.1 p.2)
          (lVelocity (I := I) (fun u : Real => f u p.2) p.1)
          (lVelocity (I := I) (f p.1) p.2))
      {p : Real × Real | T - p.2 ∈ D.regular} := by
  have hswap : IsSmoothVariation (I := I)
      (fun a b : Real => f b a) := by
    exact (hf : ContMDiff _ _ _ _).comp
      (contMDiff_snd.prodMk contMDiff_fst)
  have hYall : ContMDiff
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E))
      (7 : ℕ)
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (fun u : Real => f u q.2) q.1) :
            TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff
      (I := I) (M := M) (fun a b : Real => f b a) hswap
    have hcomp := hbase.comp
      (contMDiff_snd.prodMk contMDiff_fst :
        ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real))
          (𝓘(Real, Real).prod 𝓘(Real, Real)) (7 : ℕ)
          (fun q : Real × Real => (q.2, q.1)))
    simpa only [Function.comp_def, lVelocity] using hcomp
  have hXall := velocity_totalSpace_contMDiff (I := I) (M := M) f hf
  intro p hp
  have hfAt : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) I (2 : WithTop ℕ∞)
      (fun q : Real × Real => f q.1 q.2) p :=
    (hf : ContMDiff _ _ (8 : ℕ) _).contMDiffAt.of_le (by norm_num)
  have harg : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (𝓘(Real, Real).prod I) (2 : WithTop ℕ∞)
      (fun q : Real × Real => (T - q.2, f q.1 q.2)) p :=
    (contMDiffAt_const.sub contMDiffAt_snd).prodMk hfAt
  have hmetric₀ := hG.metricCLMSmoothAt
    (t := T - p.2) (x := f p.1 p.2) (D.regular_isOpen.mem_nhds hp)
  have hmetric : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real))
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) (2 : WithTop ℕ∞)
      (fun q : Real × Real =>
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y => TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (f q.1 q.2) ((S.base.metric (T - q.2)).inner (f q.1 q.2))) p := by
    simpa only [SolutionOn.family_metric, Function.comp_def] using
      (hmetric₀.of_le (by
        change (↑(2 : ENat) : WithTop ENat) ≤ ↑(⊤ : ENat)
        exact WithTop.coe_le_coe.mpr le_top)).comp p harg
  have hY : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E))
      (2 : WithTop ℕ∞)
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (fun u : Real => f u q.2) q.1) :
            TangentBundle I M)) p :=
    hYall.contMDiffAt.of_le (by norm_num)
  have hX : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) (I.prod 𝓘(Real, E))
      (2 : WithTop ℕ∞)
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f q.1 q.2)
          (lVelocity (I := I) (f q.1) q.2) : TangentBundle I M)) p := by
    simpa only [lVelocity] using hXall.contMDiffAt.of_le (by norm_num)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun y : M => TangentSpace I y)
    (E₂ := fun y : M => TangentSpace I y)
    (E₃ := fun _ : M => Real) hmetric hY hX
  have hscalar : ContMDiffAt
      (𝓘(Real, Real).prod 𝓘(Real, Real)) 𝓘(Real, Real)
      (2 : WithTop ℕ∞)
      (fun q : Real × Real =>
        (S.base.metric (T - q.2)).inner (f q.1 q.2)
          (lVelocity (I := I) (fun u : Real => f u q.2) q.1)
          (lVelocity (I := I) (f q.1) q.2)) p := by
    rw [Bundle.contMDiffAt_totalSpace] at htotal
    simpa only [Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.trivialization_apply] using htotal.2
  have hcd : ContDiffAt Real 2
      (fun q : Real × Real =>
        (S.base.metric (T - q.2)).inner (f q.1 q.2)
          (lVelocity (I := I) (fun u : Real => f u q.2) q.1)
          (lVelocity (I := I) (f q.1) q.2)) p := by
    rw [← contMDiffAt_iff_contDiffAt, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hscalar
  exact hcd.contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lPair_contDiffOn
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (f : Real → Real → M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 1
      (fun tau : Real =>
        (S.base.metric (T - tau)).inner (f 0 tau)
          (lVelocity (I := I) (fun u : Real => f u tau) 0)
          (lVelocity (I := I) (f 0) tau))
      {tau : Real | T - tau ∈ D.regular} := by
  have hgamma : ContMDiff 𝓘(Real, Real) I (8 : ℕ) (f 0) := by
    have hincl : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : ℕ)
        (fun tau : Real => ((0 : Real), tau)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hfswap : IsSmoothVariation (I := I) (fun a b : Real => f b a) := by
    have hswap : ContMDiff
        (𝓘(Real, Real).prod 𝓘(Real, Real))
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : ℕ)
        (fun q : Real × Real => (q.2, q.1)) :=
      contMDiff_snd.prodMk contMDiff_fst
    exact (hf : ContMDiff _ _ _ _).comp hswap
  have hYall : ContMDiff 𝓘(Real, Real) (I.prod 𝓘(Real, E)) (7 : ℕ)
      (fun tau : Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f 0 tau)
          (lVelocity (I := I) (fun u : Real => f u tau) 0) :
            TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff
      (I := I) (M := M) (fun a b : Real => f b a) hfswap
    have hcomp := hbase.comp
      (contMDiff_id.prodMk contMDiff_const : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (7 : ℕ)
        (fun tau : Real => (tau, (0 : Real))))
    simpa only [Function.comp_def, id_eq, lVelocity] using hcomp
  have hXall : ContMDiff 𝓘(Real, Real) (I.prod 𝓘(Real, E)) (7 : ℕ)
      (fun tau : Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f 0 tau)
          (lVelocity (I := I) (f 0) tau) : TangentBundle I M)) := by
    have hbase := velocity_totalSpace_contMDiff (I := I) (M := M) f hf
    have hcomp := hbase.comp
      (contMDiff_const.prodMk contMDiff_id : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (7 : ℕ)
        (fun tau : Real => ((0 : Real), tau)))
    simpa only [Function.comp_def, lVelocity] using hcomp
  intro tau htau
  have harg : ContMDiffAt 𝓘(Real, Real) (𝓘(Real, Real).prod I)
      (1 : WithTop ℕ∞) (fun s : Real => (T - s, f 0 s)) tau :=
    (contMDiffAt_const.sub contMDiffAt_id).prodMk
      (hgamma.contMDiffAt.of_le (by norm_num))
  have hmetric₀ := hG.metricCLMSmoothAt
    (t := T - tau) (x := f 0 tau) (D.regular_isOpen.mem_nhds htau)
  have hmetric : ContMDiffAt 𝓘(Real, Real)
      (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) (1 : WithTop ℕ∞)
      (fun s : Real =>
        TotalSpace.mk' (E →L[Real] E →L[Real] Real)
          (E := fun y => TangentSpace I y →L[Real]
            TangentSpace I y →L[Real] Real)
          (f 0 s) ((S.base.metric (T - s)).inner (f 0 s))) tau := by
    simpa only [SolutionOn.family_metric, Function.comp_def] using
      (hmetric₀.of_le (by simp)).comp tau harg
  have hY : ContMDiffAt 𝓘(Real, Real) (I.prod 𝓘(Real, E))
      (1 : WithTop ℕ∞)
      (fun s : Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f 0 s)
          (lVelocity (I := I) (fun u : Real => f u s) 0) :
            TangentBundle I M)) tau :=
    (hYall tau).of_le (by norm_num)
  have hX : ContMDiffAt 𝓘(Real, Real) (I.prod 𝓘(Real, E))
      (1 : WithTop ℕ∞)
      (fun s : Real =>
        (TotalSpace.mk' E (E := TangentSpace I) (f 0 s)
          (lVelocity (I := I) (f 0) s) : TangentBundle I M)) tau :=
    (hXall tau).of_le (by norm_num)
  have htotal := ContMDiffAt.clm_bundle_apply₂
    (E₁ := fun y : M => TangentSpace I y)
    (E₂ := fun y : M => TangentSpace I y)
    (E₃ := fun _ : M => Real) hmetric hY hX
  have hscalar : ContMDiffAt 𝓘(Real, Real) 𝓘(Real, Real)
      (1 : WithTop ℕ∞)
      (fun s : Real =>
        (S.base.metric (T - s)).inner (f 0 s)
          (lVelocity (I := I) (fun u : Real => f u s) 0)
          (lVelocity (I := I) (f 0) s)) tau := by
    rw [Bundle.contMDiffAt_totalSpace] at htotal
    simpa only [Bundle.Trivial.fiberBundle_trivializationAt',
      Bundle.Trivial.trivialization_apply] using htotal.2
  exact (contMDiffAt_iff_contDiffAt.mp hscalar).contDiffWithinAt

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lScalar_var_deriv
    (S : SolutionOn (I := I) (M := M) D) (T tau : Real)
    (f : Real → Real → M)
    (hf : MDifferentiableAt 𝓘(Real, Real) I (fun u : Real => f u tau) 0) :
    HasDerivAt (fun u : Real => S.scalar (T - tau) (f u tau))
      ((S.base.metric (T - tau)).inner (f 0 tau)
        (gradientFun (I := I) (S.base.metric (T - tau))
          (S.scalar (T - tau)) (f 0 tau))
        (lVelocity (I := I) (fun u : Real => f u tau) 0)) 0 := by
  have hRsm : ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (S.scalar (T - tau)) := by
    change ContMDiff I 𝓘(Real, Real) (∞ : WithTop ℕ∞)
      (fun x : M => metricScalarAt (I := I) (M := M)
        (S.base.metric (T - tau)) x)
    exact metricScalar_smooth (I := I) (M := M) (S.base.metric (T - tau))
  have hR : MDifferentiableAt I 𝓘(Real, Real)
      (S.scalar (T - tau)) (f 0 tau) :=
    hRsm.contMDiffAt.mdifferentiableAt (by simp)
  have hraw :=
    DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along
      I (S.scalar (T - tau)) (fun u : Real => f u tau) 0 hR hf
  apply hraw.congr_deriv
  convert (inner_gradientFun (I := I) (S.base.metric (T - tau))
    (S.scalar (T - tau)) (f 0 tau)
    (lVelocity (I := I) (fun u : Real => f u tau) 0)).symm using 1 ; rfl

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [T2Space M] [SigmaCompactSpace M] in
theorem lSpeedSq_var_deriv
    (S : SolutionOn (I := I) (M := M) D) (T tau : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    HasDerivAt (fun u : Real => lSpeedSq S T (f u) tau)
      (2 * (S.base.metric (T - tau)).inner (f 0 tau)
        (covDerivAlong (I := I) (S.base.metric (T - tau))
          (fun s : Real => f 0 s)
          (fun s : Real =>
            lVelocity (I := I) (fun u : Real => f u s) 0) tau)
        (lVelocity (I := I) (f 0) tau)) 0 := by
  have hspeed := speedSq_hasDerivAt
    (I := I) (S.base.metric (T - tau)) f tau hf
  rw [commute_ds_dt_intrinsic
    (I := I) (S.base.metric (T - tau)) f hf tau] at hspeed
  simpa only [lSpeedSq, speedSq, lVelocity] using hspeed

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lDensity_deriv
    (S : SolutionOn (I := I) (M := M) D) (T tau : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    HasDerivAt
      (fun u : Real => lDensity S T (fun s : Real => f u s) tau)
      (Real.sqrt tau *
        ((S.base.metric (T - tau)).inner (f 0 tau)
            (gradientFun (I := I) (S.base.metric (T - tau))
              (S.scalar (T - tau)) (f 0 tau))
            (lVelocity (I := I) (fun u : Real => f u tau) 0) +
          2 * (S.base.metric (T - tau)).inner (f 0 tau)
            (covDerivAlong (I := I) (S.base.metric (T - tau))
              (fun s : Real => f 0 s)
              (fun s : Real =>
                lVelocity (I := I) (fun u : Real => f u s) 0) tau)
            (lVelocity (I := I) (fun s : Real => f 0 s) tau)))
      0 := by
  have hslice : ContMDiff 𝓘(Real, Real) I (8 : ℕ)
      (fun u : Real => f u tau) := by
    have hincl : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : ℕ)
        (fun u : Real => (u, tau)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hf0 : MDifferentiableAt 𝓘(Real, Real) I
      (fun u : Real => f u tau) 0 :=
    hslice.contMDiffAt.mdifferentiableAt (by norm_num)
  have hscalar := lScalar_var_deriv S T tau f hf0
  have hspeed : HasDerivAt
      (fun u : Real => lSpeedSq S T (fun s : Real => f u s) tau)
      (2 * (S.base.metric (T - tau)).inner (f 0 tau)
        (covDerivAlong (I := I) (S.base.metric (T - tau))
          (fun s : Real => f 0 s)
          (fun s : Real =>
            lVelocity (I := I) (fun u : Real => f u s) 0) tau)
        (lVelocity (I := I) (fun s : Real => f 0 s) tau)) 0 := by
    simpa only using lSpeedSq_var_deriv S T tau f hf
  have hadd := hscalar.add hspeed
  change HasDerivAt
    ((fun _ : Real => Real.sqrt tau) *
      ((fun u : Real => S.scalar (T - tau) (f u tau)) +
        fun u : Real => lSpeedSq S T (fun s : Real => f u s) tau)) _ 0
  simpa only [zero_mul, zero_add] using
    (hasDerivAt_const (x := (0 : Real)) (c := Real.sqrt tau)).mul hadd

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lLength_deriv
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular) :
    HasDerivAt
      (fun u : Real => lLength S T (fun tau : Real => f u tau) a b)
      (∫ tau in a..b,
        Real.sqrt tau *
          ((S.base.metric (T - tau)).inner (f 0 tau)
              (gradientFun (I := I) (S.base.metric (T - tau))
                (S.scalar (T - tau)) (f 0 tau))
              (lVelocity (I := I) (fun u : Real => f u tau) 0) +
            2 * (S.base.metric (T - tau)).inner (f 0 tau)
              (covDerivAlong (I := I) (S.base.metric (T - tau))
                (fun s : Real => f 0 s)
                (fun s : Real =>
                  lVelocity (I := I) (fun u : Real => f u s) 0) tau)
              (lVelocity (I := I) (fun s : Real => f 0 s) tau)))
      0 := by
  let U : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ∈ D.regular}
  let core : Real × Real → Real := fun p =>
    S.scalar (T - p.2) (f p.1 p.2) + lSpeedSq S T (f p.1) p.2
  let dens : Real → Real → Real := fun u tau =>
    Real.sqrt tau * core (u, tau)
  let dDens : Real → Real → Real := fun u tau =>
    Real.sqrt tau * fderiv Real core (u, tau) (1, 0)
  have hUopen : IsOpen U := by
    exact D.regular_isOpen.preimage (continuous_const.sub continuous_snd)
  have hcore : ContDiffOn Real 1 core U := by
    simpa only [core, U] using lCore_contDiffOn S hS T f hf
  have hdensJoint : ContinuousOn (fun p : Real × Real => dens p.1 p.2) U := by
    change ContinuousOn ((Real.sqrt ∘ Prod.snd) * core) U
    exact (Real.continuous_sqrt.comp continuous_snd).continuousOn.mul hcore.continuousOn
  have hfdCont : ContinuousOn (fderiv Real core) U :=
    hcore.continuousOn_fderiv_of_isOpen hUopen (by norm_num)
  have hdcoreCont : ContinuousOn
      (fun p : Real × Real => fderiv Real core p (1, 0)) U :=
    hfdCont.clm_apply continuousOn_const
  have hdDensJoint : ContinuousOn (fun p : Real × Real => dDens p.1 p.2) U := by
    change ContinuousOn ((Real.sqrt ∘ Prod.snd) *
      fun p : Real × Real => fderiv Real core p (1, 0)) U
    exact (Real.continuous_sqrt.comp continuous_snd).continuousOn.mul hdcoreCont
  have hdensCont (u : Real) : ContinuousOn (dens u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun tau : Real => (u, tau)) (Set.uIcc a b) :=
      continuousOn_const.prodMk continuousOn_id
    apply hdensJoint.comp hmap
    intro tau htau
    exact ht tau htau
  have hdDensCont (u : Real) : ContinuousOn (dDens u) (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun tau : Real => (u, tau)) (Set.uIcc a b) :=
      continuousOn_const.prodMk continuousOn_id
    apply hdDensJoint.comp hmap
    intro tau htau
    exact ht tau htau
  have hcoreDiff : DifferentiableOn Real core U :=
    hcore.differentiableOn (by norm_num)
  have hdensDeriv (u tau : Real) (htau : tau ∈ Set.uIcc a b) :
      HasDerivAt (fun z : Real => dens z tau) (dDens u tau) u := by
    have hpU : (u, tau) ∈ U := ht tau htau
    have hcoreAt : DifferentiableAt Real core (u, tau) :=
      (hcoreDiff (u, tau) hpU).differentiableAt (hUopen.mem_nhds hpU)
    have hslice : HasDerivAt (fun z : Real => core (z, tau))
        (fderiv Real core (u, tau) (1, 0)) u := by
      simpa only using Aux2.hasDerivAt_slice_fst
        (fun z s : Real => core (z, s)) u tau hcoreAt
    change HasDerivAt ((fun _ : Real => Real.sqrt tau) *
      fun z : Real => core (z, tau)) _ u
    simpa only [dDens, zero_mul, zero_add] using
      (hasDerivAt_const (x := u) (c := Real.sqrt tau)).mul hslice
  let K : Set (Real × Real) := Set.Icc (-1 : Real) 1 ×ˢ Set.uIcc a b
  have hKcompact : IsCompact K := by
    simpa only [K] using isCompact_Icc.prod isCompact_uIcc
  have hKsub : K ⊆ U := by
    intro p hp
    exact ht p.2 hp.2
  obtain ⟨C, hC⟩ := hKcompact.bddAbove_image (hdDensJoint.mono hKsub).norm
  let C₀ : Real := max C 0
  have hC₀ : ∀ p ∈ K, ‖dDens p.1 p.2‖ ≤ C₀ := by
    intro p hp
    exact (hC ⟨p, hp, rfl⟩).trans (le_max_left C 0)
  have hs : Set.Icc (-1 : Real) 1 ∈ 𝓝 (0 : Real) :=
    Icc_mem_nhds (by norm_num) (by norm_num)
  have hFmeas : ∀ᶠ u in 𝓝 (0 : Real),
      AEStronglyMeasurable (dens u)
        (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    Filter.Eventually.of_forall fun u =>
      (hdensCont u).aestronglyMeasurable_of_subset_isCompact
        isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hFint : IntervalIntegrable (dens 0) MeasureTheory.volume a b :=
    (hdensCont 0).intervalIntegrable
  have hF'meas : AEStronglyMeasurable (dDens 0)
      (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    (hdDensCont 0).aestronglyMeasurable_of_subset_isCompact
      isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc
  have hbound : ∀ᵐ tau ∂MeasureTheory.volume,
      tau ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        ‖dDens u tau‖ ≤ (fun _ : Real => C₀) tau :=
    Filter.Eventually.of_forall fun tau htau u hu =>
      hC₀ (u, tau) ⟨hu, Set.uIoc_subset_uIcc htau⟩
  have hboundInt : IntervalIntegrable (fun _ : Real => C₀)
      MeasureTheory.volume a b :=
    continuousOn_const.intervalIntegrable
  have hdiff : ∀ᵐ tau ∂MeasureTheory.volume,
      tau ∈ Set.uIoc a b → ∀ u ∈ Set.Icc (-1 : Real) 1,
        HasDerivAt (fun z : Real => dens z tau) (dDens u tau) u :=
    Filter.Eventually.of_forall fun tau htau u _ =>
      hdensDeriv u tau (Set.uIoc_subset_uIcc htau)
  have hparam :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := dens) (F' := dDens) (x₀ := (0 : Real))
      (s := Set.Icc (-1 : Real) 1) (a := a) (b := b)
      (bound := fun _ : Real => C₀) hs hFmeas hFint hF'meas
      hbound hboundInt hdiff
  let varDens : Real → Real := fun tau =>
    Real.sqrt tau *
      ((S.base.metric (T - tau)).inner (f 0 tau)
          (gradientFun (I := I) (S.base.metric (T - tau))
            (S.scalar (T - tau)) (f 0 tau))
          (lVelocity (I := I) (fun u : Real => f u tau) 0) +
        2 * (S.base.metric (T - tau)).inner (f 0 tau)
          (covDerivAlong (I := I) (S.base.metric (T - tau))
            (fun s : Real => f 0 s)
            (fun s : Real =>
              lVelocity (I := I) (fun u : Real => f u s) 0) tau)
          (lVelocity (I := I) (fun s : Real => f 0 s) tau))
  have hdEq : Set.EqOn (dDens 0) varDens (Set.uIcc a b) := by
    intro tau htau
    have hraw : HasDerivAt
        (fun u : Real => lDensity S T (fun s : Real => f u s) tau)
        (dDens 0 tau) 0 := by
      simpa only [dens, core, lDensity] using hdensDeriv 0 tau htau
    exact hraw.unique (by
      simpa only [varDens] using lDensity_deriv S T tau f hf)
  have hint : (∫ tau in a..b, dDens 0 tau) =
      ∫ tau in a..b, varDens tau :=
    intervalIntegral.integral_congr hdEq
  rw [hint] at hparam
  simpa only [lLength, dens, core, lDensity, varDens] using hparam.2

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lGrad_contOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M)
    (hf : ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I 1
      (fun p : Real × Real => f p.1 p.2))
    (a b : Real)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular) :
    ContinuousOn
      (fun tau : Real =>
        Real.sqrt tau *
          (S.base.metric (T - tau)).inner (f 0 tau)
            (gradientFun (I := I) (S.base.metric (T - tau))
              (S.scalar (T - tau)) (f 0 tau))
            (lVelocity (I := I) (fun u : Real => f u tau) 0))
      (Set.uIcc a b) := by
  let U : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ∈ D.regular}
  let scalar : Real × Real → Real := fun p =>
    S.scalar (T - p.2) (f p.1 p.2)
  let dScalar : Real → Real := fun tau =>
    fderiv Real scalar (0, tau) (1, 0)
  let G : Real → Real := fun tau =>
    Real.sqrt tau *
      (S.base.metric (T - tau)).inner (f 0 tau)
        (gradientFun (I := I) (S.base.metric (T - tau))
          (S.scalar (T - tau)) (f 0 tau))
        (lVelocity (I := I) (fun u : Real => f u tau) 0)
  have hUopen : IsOpen U :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_snd)
  have hscalar : ContDiffOn Real 1 scalar U := by
    simpa only [scalar, U] using lScalar_contDiffOn S hS T f hf
  have hfdScalar : ContinuousOn (fderiv Real scalar) U :=
    hscalar.continuousOn_fderiv_of_isOpen hUopen (by norm_num)
  have hpartScalar : ContinuousOn
      (fun p : Real × Real => fderiv Real scalar p (1, 0)) U :=
    hfdScalar.clm_apply continuousOn_const
  have hdScalarCont : ContinuousOn dScalar (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun tau : Real => ((0 : Real), tau))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    change ContinuousOn
      ((fun p : Real × Real => fderiv Real scalar p (1, 0)) ∘
        fun tau : Real => ((0 : Real), tau)) (Set.uIcc a b)
    exact hpartScalar.comp hmap (fun tau htau => ht tau htau)
  have hscalarDiff : DifferentiableOn Real scalar U :=
    hscalar.differentiableOn (by norm_num)
  have hfSlice (tau : Real) : MDifferentiableAt 𝓘(Real, Real) I
      (fun u : Real => f u tau) 0 := by
    have hincl : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (1 : ℕ)
        (fun u : Real => (u, tau)) :=
      contMDiff_id.prodMk contMDiff_const
    exact (hf.comp hincl).contMDiffAt.mdifferentiableAt (by norm_num)
  have hdScalarEq : ∀ tau ∈ Set.uIcc a b,
      dScalar tau =
        (S.base.metric (T - tau)).inner (f 0 tau)
          (gradientFun (I := I) (S.base.metric (T - tau))
            (S.scalar (T - tau)) (f 0 tau))
          (lVelocity (I := I) (fun u : Real => f u tau) 0) := by
    intro tau htau
    have hpU : ((0 : Real), tau) ∈ U := ht tau htau
    have hscalarAt : DifferentiableAt Real scalar (0, tau) :=
      (hscalarDiff (0, tau) hpU).differentiableAt (hUopen.mem_nhds hpU)
    have hslice : HasDerivAt (fun u : Real => scalar (u, tau))
        (dScalar tau) 0 := by
      simpa only [dScalar] using Aux2.hasDerivAt_slice_fst
        (fun u s : Real => scalar (u, s)) 0 tau hscalarAt
    exact hslice.unique (by
      simpa only [scalar] using lScalar_var_deriv S T tau f (hfSlice tau))
  have hGcont : ContinuousOn G (Set.uIcc a b) := by
    have hraw : ContinuousOn
        (fun tau : Real => Real.sqrt tau * dScalar tau) (Set.uIcc a b) :=
      continuousOn_id.sqrt.mul hdScalarCont
    apply hraw.congr
    intro tau htau
    change G tau = Real.sqrt tau * dScalar tau
    rw [hdScalarEq tau htau]
  simpa only [G] using hGcont

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [SigmaCompactSpace M] in
theorem lGrad_integrable
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M)
    (hf : ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I 1
      (fun p : Real × Real => f p.1 p.2))
    (a b : Real)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular) :
    IntervalIntegrable
      (fun tau : Real =>
        Real.sqrt tau *
          (S.base.metric (T - tau)).inner (f 0 tau)
            (gradientFun (I := I) (S.base.metric (T - tau))
              (S.scalar (T - tau)) (f 0 tau))
            (lVelocity (I := I) (fun u : Real => f u tau) 0))
      MeasureTheory.volume a b :=
  (lGrad_contOn S hS T f hf a b ht).intervalIntegrable

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lPair_deriv
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T tau : Real) (f : Real → Real → M)
    (hf : IsSmoothVariation (I := I) f) (ht : T - tau ∈ D.regular) :
    HasDerivAt
      (fun s : Real =>
        (S.base.metric (T - s)).inner (f 0 s)
          (lVelocity (I := I) (fun u : Real => f u s) 0)
          (lVelocity (I := I) (f 0) s))
      (((S.base.metric (T - tau)).inner (f 0 tau)
          (covDerivAlong (I := I) (S.base.metric (T - tau))
            (f 0) (fun s : Real =>
              lVelocity (I := I) (fun u : Real => f u s) 0) tau)
          (lVelocity (I := I) (f 0) tau) +
        (S.base.metric (T - tau)).inner (f 0 tau)
          (lVelocity (I := I) (fun u : Real => f u tau) 0)
          (covDerivAlong (I := I) (S.base.metric (T - tau))
            (f 0) (fun s : Real => lVelocity (I := I) (f 0) s) tau)) +
        2 * S.ricciAt (T - tau) (f 0 tau)
          (vec2
            (lVelocity (I := I) (fun u : Real => f u tau) 0)
            (lVelocity (I := I) (f 0) tau)))
      tau := by
  have hgamma : ContMDiff 𝓘(Real, Real) I (8 : ℕ) (f 0) := by
    have hincl : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : ℕ)
        (fun s : Real => ((0 : Real), s)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hY : DifferentiableAt Real
      (chartRepAt (I := I) (f 0)
        (fun s : Real => lVelocity (I := I) (fun u : Real => f u s) 0) tau)
      tau := by
    simpa only [lVelocity] using
      variationField_chartRep_differentiableAt
        (I := I) f hf tau
  have hX : DifferentiableAt Real
      (chartRepAt (I := I) (f 0)
        (fun s : Real => lVelocity (I := I) (f 0) s) tau) tau := by
    simpa only [lVelocity] using
      velocityField_chartRep_differentiableAt
        (I := I) f hf tau
  exact lInner_deriv S hS T (f 0)
    (fun s : Real => lVelocity (I := I) (fun u : Real => f u s) 0)
    (fun s : Real => lVelocity (I := I) (f 0) s) tau ht
    (hgamma.mdifferentiableAt (by norm_num)) hY hX

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lBdry_deriv
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (gamma : Real → M)
    (V W : ∀ tau, TangentSpace I (gamma tau)) (tau : Real)
    (ht : T - tau ∈ D.regular) (htau : 0 < tau)
    (hgamma : MDifferentiableAt 𝓘(Real, Real) I gamma tau)
    (hV : DifferentiableAt Real (chartRepAt (I := I) gamma V tau) tau)
    (hW : DifferentiableAt Real (chartRepAt (I := I) gamma W tau) tau) :
    HasDerivAt
      (fun s : Real =>
        2 * (Real.sqrt s *
          (S.base.metric (T - s)).inner (gamma s) (V s) (W s)))
      ((1 / Real.sqrt tau) *
          (S.base.metric (T - tau)).inner (gamma tau) (V tau) (W tau) +
        2 * Real.sqrt tau *
          (((S.base.metric (T - tau)).inner (gamma tau)
              (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma V tau)
              (W tau) +
            (S.base.metric (T - tau)).inner (gamma tau) (V tau)
              (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma W tau)) +
            2 * S.ricciAt (T - tau) (gamma tau) (vec2 (V tau) (W tau))))
      tau := by
  have hpair := lInner_deriv S hS T gamma V W tau ht hgamma hV hW
  have hsqrt := Real.hasDerivAt_sqrt (ne_of_gt htau)
  apply ((hsqrt.mul hpair).const_mul 2).congr_deriv
  have hsqrt_ne : Real.sqrt tau ≠ 0 := ne_of_gt (Real.sqrt_pos.2 htau)
  field_simp [hsqrt_ne]

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lInner_parts
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (gamma : Real → M)
    (V W : ∀ tau, TangentSpace I (gamma tau)) (a b : Real)
    (hpos : 0 < min a b)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular)
    (hgamma : ∀ tau ∈ Set.uIcc a b,
      MDifferentiableAt 𝓘(Real, Real) I gamma tau)
    (hV : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) gamma V tau) tau)
    (hW : ∀ tau ∈ Set.uIcc a b,
      DifferentiableAt Real (chartRepAt (I := I) gamma W tau) tau)
    (hPint : IntervalIntegrable
      (fun tau : Real =>
        (((S.base.metric (T - tau)).inner (gamma tau)
            (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma V tau)
            (W tau) +
          (S.base.metric (T - tau)).inner (gamma tau) (V tau)
            (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma W tau)) +
          2 * S.ricciAt (T - tau) (gamma tau) (vec2 (V tau) (W tau))))
      MeasureTheory.volume a b) :
    (∫ tau in a..b,
        (2 * Real.sqrt tau) *
          (((S.base.metric (T - tau)).inner (gamma tau)
              (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma V tau)
              (W tau) +
            (S.base.metric (T - tau)).inner (gamma tau) (V tau)
              (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma W tau)) +
            2 * S.ricciAt (T - tau) (gamma tau) (vec2 (V tau) (W tau))) =
      (2 * Real.sqrt b) *
          (S.base.metric (T - b)).inner (gamma b) (V b) (W b) -
        (2 * Real.sqrt a) *
          (S.base.metric (T - a)).inner (gamma a) (V a) (W a) -
        ∫ tau in a..b,
          (1 / Real.sqrt tau) *
            (S.base.metric (T - tau)).inner (gamma tau) (V tau) (W tau)) := by
  apply intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun tau : Real => 2 * Real.sqrt tau)
    (u' := fun tau : Real => 1 / Real.sqrt tau)
    (v := fun tau : Real =>
      (S.base.metric (T - tau)).inner (gamma tau) (V tau) (W tau))
    (v' := fun tau : Real =>
      (((S.base.metric (T - tau)).inner (gamma tau)
          (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma V tau)
          (W tau) +
        (S.base.metric (T - tau)).inner (gamma tau) (V tau)
          (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma W tau)) +
        2 * S.ricciAt (T - tau) (gamma tau) (vec2 (V tau) (W tau))))
  · intro tau htau
    have htau_pos : 0 < tau := lt_of_lt_of_le hpos htau.1
    apply ((Real.hasDerivAt_sqrt (ne_of_gt htau_pos)).const_mul 2).congr_deriv
    have hsqrt_ne : Real.sqrt tau ≠ 0 := ne_of_gt (Real.sqrt_pos.2 htau_pos)
    field_simp [hsqrt_ne]
  · intro tau htau
    exact lInner_deriv S hS T gamma V W tau (ht tau htau)
      (hgamma tau htau) (hV tau htau) (hW tau htau)
  · exact (continuousOn_const.div continuousOn_id.sqrt (fun tau htau =>
      ne_of_gt (Real.sqrt_pos.2 (lt_of_lt_of_le hpos htau.1)))).intervalIntegrable
  · exact hPint

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lCross_contOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (hpos : 0 < min a b)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular) :
    ContinuousOn
        (fun tau : Real =>
          2 * Real.sqrt tau *
            (S.base.metric (T - tau)).inner (f 0 tau)
              (covDerivAlong (I := I) (S.base.metric (T - tau))
                (f 0) (fun s : Real =>
                  lVelocity (I := I) (fun u : Real => f u s) 0) tau)
              (lVelocity (I := I) (f 0) tau))
        (Set.uIcc a b) ∧
      ContinuousOn
        (fun tau : Real =>
          (1 / Real.sqrt tau) *
              (S.base.metric (T - tau)).inner (f 0 tau)
                (lVelocity (I := I) (fun u : Real => f u tau) 0)
                (lVelocity (I := I) (f 0) tau) +
            2 * Real.sqrt tau *
              ((S.base.metric (T - tau)).inner (f 0 tau)
                  (lVelocity (I := I) (fun u : Real => f u tau) 0)
                  (covDerivAlong (I := I) (S.base.metric (T - tau))
                    (f 0) (fun s : Real => lVelocity (I := I) (f 0) s) tau) +
                2 * S.ricciAt (T - tau) (f 0 tau)
                  (vec2
                    (lVelocity (I := I) (fun u : Real => f u tau) 0)
                    (lVelocity (I := I) (f 0) tau))))
        (Set.uIcc a b) := by
  let U : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ∈ D.regular}
  let speed : Real × Real → Real := fun p =>
    lSpeedSq S T (f p.1) p.2
  let dSpeed : Real → Real := fun tau =>
    fderiv Real speed (0, tau) (1, 0)
  let A : Real → Real := fun tau =>
    2 * Real.sqrt tau *
      (S.base.metric (T - tau)).inner (f 0 tau)
        (covDerivAlong (I := I) (S.base.metric (T - tau))
          (f 0) (fun s : Real =>
            lVelocity (I := I) (fun u : Real => f u s) 0) tau)
        (lVelocity (I := I) (f 0) tau)
  let V : Set Real := {tau : Real | T - tau ∈ D.regular}
  let pair : Real → Real := fun tau =>
    (S.base.metric (T - tau)).inner (f 0 tau)
      (lVelocity (I := I) (fun u : Real => f u tau) 0)
      (lVelocity (I := I) (f 0) tau)
  let Q : Real → Real := fun tau =>
    (1 / Real.sqrt tau) * pair tau +
      2 * Real.sqrt tau *
        ((S.base.metric (T - tau)).inner (f 0 tau)
            (lVelocity (I := I) (fun u : Real => f u tau) 0)
            (covDerivAlong (I := I) (S.base.metric (T - tau))
              (f 0) (fun s : Real => lVelocity (I := I) (f 0) s) tau) +
          2 * S.ricciAt (T - tau) (f 0 tau)
            (vec2
              (lVelocity (I := I) (fun u : Real => f u tau) 0)
              (lVelocity (I := I) (f 0) tau)))
  have hUopen : IsOpen U :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_snd)
  have hspeed : ContDiffOn Real 1 speed U := by
    simpa only [speed, U] using
      lSpeedSq_contDiffOn S T f hS.smoothMetric hf
  have hfdSpeed : ContinuousOn (fderiv Real speed) U :=
    hspeed.continuousOn_fderiv_of_isOpen hUopen (by norm_num)
  have hpartSpeed : ContinuousOn
      (fun p : Real × Real => fderiv Real speed p (1, 0)) U :=
    hfdSpeed.clm_apply continuousOn_const
  have hdSpeedCont : ContinuousOn dSpeed (Set.uIcc a b) := by
    have hmap : ContinuousOn (fun tau : Real => ((0 : Real), tau))
        (Set.uIcc a b) := continuousOn_const.prodMk continuousOn_id
    change ContinuousOn
      ((fun p : Real × Real => fderiv Real speed p (1, 0)) ∘
        fun tau : Real => ((0 : Real), tau)) (Set.uIcc a b)
    exact hpartSpeed.comp hmap (fun tau htau => ht tau htau)
  have hspeedDiff : DifferentiableOn Real speed U :=
    hspeed.differentiableOn (by norm_num)
  have hdSpeedEq : ∀ tau ∈ Set.uIcc a b,
      dSpeed tau =
        2 * (S.base.metric (T - tau)).inner (f 0 tau)
          (covDerivAlong (I := I) (S.base.metric (T - tau))
            (fun s : Real => f 0 s)
            (fun s : Real =>
              lVelocity (I := I) (fun u : Real => f u s) 0) tau)
          (lVelocity (I := I) (f 0) tau) := by
    intro tau htau
    have hpU : ((0 : Real), tau) ∈ U := ht tau htau
    have hspeedAt : DifferentiableAt Real speed (0, tau) :=
      (hspeedDiff (0, tau) hpU).differentiableAt (hUopen.mem_nhds hpU)
    have hslice : HasDerivAt (fun u : Real => speed (u, tau))
        (dSpeed tau) 0 := by
      simpa only [dSpeed] using Aux2.hasDerivAt_slice_fst
        (fun u s : Real => speed (u, s)) 0 tau hspeedAt
    exact hslice.unique (by
      simpa only [speed] using lSpeedSq_var_deriv S T tau f hf)
  have hAcont : ContinuousOn A (Set.uIcc a b) := by
    have hraw : ContinuousOn (fun tau : Real => Real.sqrt tau * dSpeed tau)
        (Set.uIcc a b) :=
      continuousOn_id.sqrt.mul hdSpeedCont
    apply hraw.congr
    intro tau htau
    change A tau = Real.sqrt tau * dSpeed tau
    rw [hdSpeedEq tau htau]
    simp only [A]
    ring
  have hVopen : IsOpen V :=
    D.regular_isOpen.preimage (continuous_const.sub continuous_id)
  have hpair : ContDiffOn Real 1 pair V := by
    simpa only [pair, V] using
      lPair_contDiffOn S T f hS.smoothMetric hf
  have hpairCont : ContinuousOn pair (Set.uIcc a b) :=
    hpair.continuousOn.mono (fun tau htau => ht tau htau)
  have hpairDerivCont : ContinuousOn (deriv pair) (Set.uIcc a b) :=
    (hpair.continuousOn_deriv_of_isOpen hVopen (by norm_num)).mono
      (fun tau htau => ht tau htau)
  have hpairEq : ∀ tau ∈ Set.uIcc a b,
      deriv pair tau =
        ((S.base.metric (T - tau)).inner (f 0 tau)
            (covDerivAlong (I := I) (S.base.metric (T - tau))
              (f 0) (fun s : Real =>
                lVelocity (I := I) (fun u : Real => f u s) 0) tau)
            (lVelocity (I := I) (f 0) tau) +
          (S.base.metric (T - tau)).inner (f 0 tau)
            (lVelocity (I := I) (fun u : Real => f u tau) 0)
            (covDerivAlong (I := I) (S.base.metric (T - tau))
              (f 0) (fun s : Real => lVelocity (I := I) (f 0) s) tau)) +
          2 * S.ricciAt (T - tau) (f 0 tau)
            (vec2
              (lVelocity (I := I) (fun u : Real => f u tau) 0)
              (lVelocity (I := I) (f 0) tau)) := by
    intro tau htau
    simpa only [pair] using (lPair_deriv S hS T tau f hf (ht tau htau)).deriv
  let Qraw : Real → Real := fun tau =>
    (1 / Real.sqrt tau) * pair tau +
      2 * Real.sqrt tau * (deriv pair tau - dSpeed tau / 2)
  have hinvSqrt : ContinuousOn (fun tau : Real => 1 / Real.sqrt tau)
      (Set.uIcc a b) :=
    continuousOn_const.div continuousOn_id.sqrt (fun tau htau =>
      ne_of_gt (Real.sqrt_pos.2 (lt_of_lt_of_le hpos htau.1)))
  have hQrawCont : ContinuousOn Qraw (Set.uIcc a b) := by
    exact (hinvSqrt.mul hpairCont).add
      ((continuousOn_const.mul continuousOn_id.sqrt).mul
        (hpairDerivCont.sub (hdSpeedCont.div_const 2)))
  have hQeq : Set.EqOn Q Qraw (Set.uIcc a b) := by
    intro tau htau
    simp only [Q, Qraw]
    rw [hpairEq tau htau, hdSpeedEq tau htau]
    ring
  have hQcont : ContinuousOn Q (Set.uIcc a b) :=
    hQrawCont.congr fun tau htau => hQeq htau
  exact ⟨by simpa only [A] using hAcont,
    by simpa only [Q, pair] using hQcont⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lCross_integrable
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (hpos : 0 < min a b)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular) :
    IntervalIntegrable
        (fun tau : Real =>
          2 * Real.sqrt tau *
            (S.base.metric (T - tau)).inner (f 0 tau)
              (covDerivAlong (I := I) (S.base.metric (T - tau))
                (f 0) (fun s : Real =>
                  lVelocity (I := I) (fun u : Real => f u s) 0) tau)
              (lVelocity (I := I) (f 0) tau))
        MeasureTheory.volume a b ∧
      IntervalIntegrable
        (fun tau : Real =>
          (1 / Real.sqrt tau) *
              (S.base.metric (T - tau)).inner (f 0 tau)
                (lVelocity (I := I) (fun u : Real => f u tau) 0)
                (lVelocity (I := I) (f 0) tau) +
            2 * Real.sqrt tau *
              ((S.base.metric (T - tau)).inner (f 0 tau)
                  (lVelocity (I := I) (fun u : Real => f u tau) 0)
                  (covDerivAlong (I := I) (S.base.metric (T - tau))
                    (f 0) (fun s : Real => lVelocity (I := I) (f 0) s) tau) +
                2 * S.ricciAt (T - tau) (f 0 tau)
                  (vec2
                    (lVelocity (I := I) (fun u : Real => f u tau) 0)
                    (lVelocity (I := I) (f 0) tau))))
        MeasureTheory.volume a b := by
  obtain ⟨hA, hQ⟩ := lCross_contOn S hS T f hf a b hpos ht
  exact ⟨hA.intervalIntegrable, hQ.intervalIntegrable⟩

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lCross_parts
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (hpos : 0 < min a b)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular) :
    (∫ tau in a..b,
        2 * Real.sqrt tau *
          (S.base.metric (T - tau)).inner (f 0 tau)
            (covDerivAlong (I := I) (S.base.metric (T - tau))
              (f 0) (fun s : Real =>
                lVelocity (I := I) (fun u : Real => f u s) 0) tau)
            (lVelocity (I := I) (f 0) tau)) =
      2 * Real.sqrt b *
          (S.base.metric (T - b)).inner (f 0 b)
            (lVelocity (I := I) (fun u : Real => f u b) 0)
            (lVelocity (I := I) (f 0) b) -
        2 * Real.sqrt a *
          (S.base.metric (T - a)).inner (f 0 a)
            (lVelocity (I := I) (fun u : Real => f u a) 0)
            (lVelocity (I := I) (f 0) a) -
        ∫ tau in a..b,
          ((1 / Real.sqrt tau) *
              (S.base.metric (T - tau)).inner (f 0 tau)
                (lVelocity (I := I) (fun u : Real => f u tau) 0)
                (lVelocity (I := I) (f 0) tau) +
            2 * Real.sqrt tau *
              ((S.base.metric (T - tau)).inner (f 0 tau)
                  (lVelocity (I := I) (fun u : Real => f u tau) 0)
                  (covDerivAlong (I := I) (S.base.metric (T - tau))
                    (f 0) (fun s : Real => lVelocity (I := I) (f 0) s) tau) +
                2 * S.ricciAt (T - tau) (f 0 tau)
                  (vec2
                    (lVelocity (I := I) (fun u : Real => f u tau) 0)
                    (lVelocity (I := I) (f 0) tau)))) := by
  obtain ⟨hAint, hQint⟩ :=
    lCross_integrable S hS T f hf a b hpos ht
  have hgamma : ContMDiff 𝓘(Real, Real) I (8 : ℕ) (f 0) := by
    have hincl : ContMDiff 𝓘(Real, Real)
        (𝓘(Real, Real).prod 𝓘(Real, Real)) (8 : ℕ)
        (fun s : Real => ((0 : Real), s)) :=
      contMDiff_const.prodMk contMDiff_id
    exact (hf : ContMDiff _ _ _ _).comp hincl
  have hderiv : ∀ tau ∈ Set.uIcc a b,
      HasDerivAt
        (fun s : Real =>
          2 * (Real.sqrt s *
            (S.base.metric (T - s)).inner (f 0 s)
              (lVelocity (I := I) (fun u : Real => f u s) 0)
              (lVelocity (I := I) (f 0) s)))
        (2 * Real.sqrt tau *
            (S.base.metric (T - tau)).inner (f 0 tau)
              (covDerivAlong (I := I) (S.base.metric (T - tau))
                (f 0) (fun s : Real =>
                  lVelocity (I := I) (fun u : Real => f u s) 0) tau)
              (lVelocity (I := I) (f 0) tau) +
          ((1 / Real.sqrt tau) *
              (S.base.metric (T - tau)).inner (f 0 tau)
                (lVelocity (I := I) (fun u : Real => f u tau) 0)
                (lVelocity (I := I) (f 0) tau) +
            2 * Real.sqrt tau *
              ((S.base.metric (T - tau)).inner (f 0 tau)
                  (lVelocity (I := I) (fun u : Real => f u tau) 0)
                  (covDerivAlong (I := I) (S.base.metric (T - tau))
                    (f 0) (fun s : Real => lVelocity (I := I) (f 0) s) tau) +
                2 * S.ricciAt (T - tau) (f 0 tau)
                  (vec2
                    (lVelocity (I := I) (fun u : Real => f u tau) 0)
                    (lVelocity (I := I) (f 0) tau))))) tau := by
    intro tau htau
    have hY : DifferentiableAt Real
        (chartRepAt (I := I) (f 0)
          (fun s : Real => lVelocity (I := I) (fun u : Real => f u s) 0) tau)
        tau := by
      simpa only [lVelocity] using
        variationField_chartRep_differentiableAt
          (I := I) f hf tau
    have hX : DifferentiableAt Real
        (chartRepAt (I := I) (f 0)
          (fun s : Real => lVelocity (I := I) (f 0) s) tau) tau := by
      simpa only [lVelocity] using
        velocityField_chartRep_differentiableAt
          (I := I) f hf tau
    have hbd := lBdry_deriv S hS T (f 0)
      (fun s : Real => lVelocity (I := I) (fun u : Real => f u s) 0)
      (fun s : Real => lVelocity (I := I) (f 0) s) tau (ht tau htau)
      (lt_of_lt_of_le hpos htau.1)
      (hgamma.mdifferentiableAt (by norm_num)) hY hX
    apply hbd.congr_deriv
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hAint.add hQint)
  rw [intervalIntegral.integral_add hAint hQint] at hFTC
  linarith

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lLength_first_var
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (hpos : 0 < min a b)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular) :
    HasDerivAt
      (fun u : Real => lLength S T (fun tau : Real => f u tau) a b)
      (2 * Real.sqrt b *
            (S.base.metric (T - b)).inner (f 0 b)
              (lVelocity (I := I) (fun u : Real => f u b) 0)
              (lVelocity (I := I) (f 0) b) -
        2 * Real.sqrt a *
            (S.base.metric (T - a)).inner (f 0 a)
              (lVelocity (I := I) (fun u : Real => f u a) 0)
              (lVelocity (I := I) (f 0) a) +
        ∫ tau in a..b,
          Real.sqrt tau *
              (S.base.metric (T - tau)).inner (f 0 tau)
                (gradientFun (I := I) (S.base.metric (T - tau))
                  (S.scalar (T - tau)) (f 0 tau))
                (lVelocity (I := I) (fun u : Real => f u tau) 0) -
            ((1 / Real.sqrt tau) *
                (S.base.metric (T - tau)).inner (f 0 tau)
                  (lVelocity (I := I) (fun u : Real => f u tau) 0)
                  (lVelocity (I := I) (f 0) tau) +
              2 * Real.sqrt tau *
                ((S.base.metric (T - tau)).inner (f 0 tau)
                    (lVelocity (I := I) (fun u : Real => f u tau) 0)
                    (covDerivAlong (I := I) (S.base.metric (T - tau))
                      (f 0)
                      (fun s : Real => lVelocity (I := I) (f 0) s) tau) +
                  2 * S.ricciAt (T - tau) (f 0 tau)
                    (vec2
                      (lVelocity (I := I) (fun u : Real => f u tau) 0)
                      (lVelocity (I := I) (f 0) tau)))))
      0 := by
  let G : Real → Real := fun tau =>
    Real.sqrt tau *
      (S.base.metric (T - tau)).inner (f 0 tau)
        (gradientFun (I := I) (S.base.metric (T - tau))
          (S.scalar (T - tau)) (f 0 tau))
        (lVelocity (I := I) (fun u : Real => f u tau) 0)
  let A : Real → Real := fun tau =>
    2 * Real.sqrt tau *
      (S.base.metric (T - tau)).inner (f 0 tau)
        (covDerivAlong (I := I) (S.base.metric (T - tau))
          (f 0) (fun s : Real =>
            lVelocity (I := I) (fun u : Real => f u s) 0) tau)
        (lVelocity (I := I) (f 0) tau)
  let Q : Real → Real := fun tau =>
    (1 / Real.sqrt tau) *
        (S.base.metric (T - tau)).inner (f 0 tau)
          (lVelocity (I := I) (fun u : Real => f u tau) 0)
          (lVelocity (I := I) (f 0) tau) +
      2 * Real.sqrt tau *
        ((S.base.metric (T - tau)).inner (f 0 tau)
            (lVelocity (I := I) (fun u : Real => f u tau) 0)
            (covDerivAlong (I := I) (S.base.metric (T - tau))
              (f 0) (fun s : Real => lVelocity (I := I) (f 0) s) tau) +
          2 * S.ricciAt (T - tau) (f 0 tau)
            (vec2
              (lVelocity (I := I) (fun u : Real => f u tau) 0)
              (lVelocity (I := I) (f 0) tau)))
  let B : Real :=
    2 * Real.sqrt b *
        (S.base.metric (T - b)).inner (f 0 b)
          (lVelocity (I := I) (fun u : Real => f u b) 0)
          (lVelocity (I := I) (f 0) b) -
      2 * Real.sqrt a *
        (S.base.metric (T - a)).inner (f 0 a)
          (lVelocity (I := I) (fun u : Real => f u a) 0)
          (lVelocity (I := I) (f 0) a)
  have hf1 : ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I 1
      (fun p : Real × Real => f p.1 p.2) :=
    (hf : ContMDiff _ _ (8 : ℕ) _).of_le (by norm_num)
  have hGint : IntervalIntegrable G MeasureTheory.volume a b := by
    simpa only [G] using lGrad_integrable S hS T f hf1 a b ht
  obtain ⟨hAraw, hQraw⟩ :=
    lCross_integrable S hS T f hf a b hpos ht
  have hAint : IntervalIntegrable A MeasureTheory.volume a b := by
    simpa only [A] using hAraw
  have hQint : IntervalIntegrable Q MeasureTheory.volume a b := by
    simpa only [Q] using hQraw
  have hlen : HasDerivAt
      (fun u : Real => lLength S T (fun tau : Real => f u tau) a b)
      (∫ tau in a..b, G tau + A tau) 0 := by
    apply (lLength_deriv S hS T f hf a b ht).congr_deriv
    apply intervalIntegral.integral_congr
    intro tau _
    simp only [G, A]
    ring
  have hparts : (∫ tau in a..b, A tau) =
      B - ∫ tau in a..b, Q tau := by
    simpa only [A, Q, B] using
      lCross_parts S hS T f hf a b hpos ht
  have hfinal : HasDerivAt
      (fun u : Real => lLength S T (fun tau : Real => f u tau) a b)
      (B + ∫ tau in a..b, G tau - Q tau) 0 := by
    apply hlen.congr_deriv
    rw [intervalIntegral.integral_add hGint hAint, hparts,
      intervalIntegral.integral_sub hGint hQint]
    ring
  simpa only [G, Q, B] using hfinal

noncomputable def lEulerPair
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (gamma : Real → M)
    (tau : Real) (Y : TangentSpace I (gamma tau)) : Real :=
  (S.base.metric (T - tau)).inner (gamma tau) Y
      (covDerivAlong (I := I) (S.base.metric (T - tau)) gamma
        (fun s : Real => lVelocity (I := I) gamma s) tau) -
    (1 / 2 : Real) *
      (S.base.metric (T - tau)).inner (gamma tau)
        (gradientFun (I := I) (S.base.metric (T - tau))
          (S.scalar (T - tau)) (gamma tau)) Y +
    (1 / (2 * tau)) *
      (S.base.metric (T - tau)).inner (gamma tau) Y
        (lVelocity (I := I) gamma tau) +
    2 * S.ricciAt (T - tau) (gamma tau)
      (vec2 Y (lVelocity (I := I) gamma tau))

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
theorem lEulerPair_smul
    (S : SolutionOn (I := I) (M := M) D) (T : Real)
    (gamma : Real → M) (tau c : Real)
    (Y : TangentSpace I (gamma tau)) :
    lEulerPair S T gamma tau (c • Y) =
      c * lEulerPair S T gamma tau Y := by
  have hric :
      S.ricciAt (T - tau) (gamma tau)
          (vec2 (c • Y) (lVelocity (I := I) gamma tau)) =
        c * S.ricciAt (T - tau) (gamma tau)
          (vec2 Y (lVelocity (I := I) gamma tau)) := by
    have hleft : Function.update
        (vec2 Y (lVelocity (I := I) gamma tau)) (0 : Fin 2) (c • Y) =
        vec2 (c • Y) (lVelocity (I := I) gamma tau) := by
      funext i
      fin_cases i <;> simp [vec2]
    have hright : Function.update
        (vec2 Y (lVelocity (I := I) gamma tau)) (0 : Fin 2) Y =
        vec2 Y (lVelocity (I := I) gamma tau) := by
      funext i
      fin_cases i <;> simp [vec2]
    have hmap :=
      (S.ricciAt (T - tau) (gamma tau)).map_update_smul
        (vec2 Y (lVelocity (I := I) gamma tau)) (0 : Fin 2) c Y
    rw [hleft, hright] at hmap
    simpa only [smul_eq_mul] using hmap
  have hmetric_left (Z : TangentSpace I (gamma tau)) :
      (S.base.metric (T - tau)).inner (gamma tau) (c • Y) Z =
        c * (S.base.metric (T - tau)).inner (gamma tau) Y Z := by
    rw [((S.base.metric (T - tau)).inner (gamma tau)).map_smul,
      smul_apply]
    simp only [smul_eq_mul]
  have hmetric_right (Z : TangentSpace I (gamma tau)) :
      (S.base.metric (T - tau)).inner (gamma tau) Z (c • Y) =
        c * (S.base.metric (T - tau)).inner (gamma tau) Z Y := by
    rw [((S.base.metric (T - tau)).inner (gamma tau) Z).map_smul]
    simp only [smul_eq_mul]
  simp only [lEulerPair]
  rw [hmetric_left, hmetric_right, hmetric_left, hric]
  ring

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lEuler_contOn
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (hpos : 0 < min a b)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular) :
    ContinuousOn
      (fun tau : Real =>
        (-2 * Real.sqrt tau) *
          lEulerPair S T (f 0) tau
            (lVelocity (I := I) (fun u : Real => f u tau) 0))
      (Set.uIcc a b) := by
  let G : Real → Real := fun tau =>
    Real.sqrt tau *
      (S.base.metric (T - tau)).inner (f 0 tau)
        (gradientFun (I := I) (S.base.metric (T - tau))
          (S.scalar (T - tau)) (f 0 tau))
        (lVelocity (I := I) (fun u : Real => f u tau) 0)
  let Q : Real → Real := fun tau =>
    (1 / Real.sqrt tau) *
        (S.base.metric (T - tau)).inner (f 0 tau)
          (lVelocity (I := I) (fun u : Real => f u tau) 0)
          (lVelocity (I := I) (f 0) tau) +
      2 * Real.sqrt tau *
        ((S.base.metric (T - tau)).inner (f 0 tau)
            (lVelocity (I := I) (fun u : Real => f u tau) 0)
            (covDerivAlong (I := I) (S.base.metric (T - tau))
              (f 0) (fun s : Real => lVelocity (I := I) (f 0) s) tau) +
          2 * S.ricciAt (T - tau) (f 0 tau)
            (vec2
              (lVelocity (I := I) (fun u : Real => f u tau) 0)
              (lVelocity (I := I) (f 0) tau)))
  let F : Real → Real := fun tau =>
    (-2 * Real.sqrt tau) *
      lEulerPair S T (f 0) tau
        (lVelocity (I := I) (fun u : Real => f u tau) 0)
  have hf1 : ContMDiff (𝓘(Real, Real).prod 𝓘(Real, Real)) I 1
      (fun p : Real × Real => f p.1 p.2) :=
    (hf : ContMDiff _ _ (8 : Nat) _).of_le (by norm_num)
  have hG : ContinuousOn G (Set.uIcc a b) := by
    simpa only [G] using lGrad_contOn S hS T f hf1 a b ht
  have hQ : ContinuousOn Q (Set.uIcc a b) := by
    simpa only [Q] using (lCross_contOn S hS T f hf a b hpos ht).2
  have hF : ContinuousOn F (Set.uIcc a b) := by
    apply (hG.sub hQ).congr
    intro tau htau
    change F tau = G tau - Q tau
    have hcoef : Real.sqrt tau * (1 / tau) = 1 / Real.sqrt tau := by
      simpa only [div_eq_mul_inv, one_mul] using
        (Real.sqrt_div_self' (x := tau))
    simp only [F, G, Q, lEulerPair]
    rw [← hcoef]
    ring
  simpa only [F] using hF

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lEuler_var_c1
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real)
    (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f) :
    ContDiffOn Real 1
      (fun p : Real × Real =>
        (-2 * Real.sqrt p.2) *
          lEulerPair S T (f p.1) p.2
            (lVelocity (I := I) (fun u : Real => f u p.2) p.1))
      {p : Real × Real | 0 < p.2 ∧ T - p.2 ∈ D.regular} := by
  let V : Set (Real × Real) :=
    {p : Real × Real | T - p.2 ∈ D.regular}
  let U : Set (Real × Real) :=
    {p : Real × Real | 0 < p.2 ∧ T - p.2 ∈ D.regular}
  let scalar : Real × Real → Real := fun p =>
    S.scalar (T - p.2) (f p.1 p.2)
  let speed : Real × Real → Real := fun p =>
    lSpeedSq S T (f p.1) p.2
  let pair : Real × Real → Real := fun p =>
    (S.base.metric (T - p.2)).inner (f p.1 p.2)
      (lVelocity (I := I) (fun u : Real => f u p.2) p.1)
      (lVelocity (I := I) (f p.1) p.2)
  let dScalar : Real × Real → Real := fun p =>
    fderiv Real scalar p (1, 0)
  let dSpeed : Real × Real → Real := fun p =>
    fderiv Real speed p (1, 0)
  let dPair : Real × Real → Real := fun p =>
    fderiv Real pair p (0, 1)
  let raw : Real × Real → Real := fun p =>
    Real.sqrt p.2 * dScalar p -
      ((1 / Real.sqrt p.2) * pair p +
        2 * Real.sqrt p.2 * (dPair p - dSpeed p / 2))
  let euler : Real × Real → Real := fun p =>
    (-2 * Real.sqrt p.2) *
      lEulerPair S T (f p.1) p.2
        (lVelocity (I := I) (fun u : Real => f u p.2) p.1)
  have hVopen : IsOpen V := by
    exact D.regular_isOpen.preimage (continuous_const.sub continuous_snd)
  have hUopen : IsOpen U := by
    change IsOpen
      ({p : Real × Real | 0 < p.2} ∩
        {p : Real × Real | T - p.2 ∈ D.regular})
    exact (isOpen_lt continuous_const continuous_snd).inter hVopen
  have hUV : U ⊆ V := by
    intro p hp
    exact hp.2
  have hscalar2 : ContDiffOn Real 2 scalar V := by
    simpa only [scalar, V] using lScalar_c2 S hS T f hf
  have hspeed2 : ContDiffOn Real 2 speed V := by
    simpa only [speed, V] using
      lSpeedSq_c2 S T f hS.smoothMetric hf
  have hpair2 : ContDiffOn Real 2 pair V := by
    simpa only [pair, V] using lPair_c2 S T f hS.smoothMetric hf
  have hdScalarV : ContDiffOn Real 1 dScalar V := by
    have hfd : ContDiffOn Real 1 (fderiv Real scalar) V :=
      hscalar2.fderiv_of_isOpen hVopen (by norm_num)
    simpa only [dScalar] using hfd.clm_apply contDiffOn_const
  have hdSpeedV : ContDiffOn Real 1 dSpeed V := by
    have hfd : ContDiffOn Real 1 (fderiv Real speed) V :=
      hspeed2.fderiv_of_isOpen hVopen (by norm_num)
    simpa only [dSpeed] using hfd.clm_apply contDiffOn_const
  have hdPairV : ContDiffOn Real 1 dPair V := by
    have hfd : ContDiffOn Real 1 (fderiv Real pair) V :=
      hpair2.fderiv_of_isOpen hVopen (by norm_num)
    simpa only [dPair] using hfd.clm_apply contDiffOn_const
  have hpair1 : ContDiffOn Real 1 pair U :=
    (hpair2.of_le (by norm_num)).mono hUV
  have hdScalar : ContDiffOn Real 1 dScalar U := hdScalarV.mono hUV
  have hdSpeed : ContDiffOn Real 1 dSpeed U := hdSpeedV.mono hUV
  have hdPair : ContDiffOn Real 1 dPair U := hdPairV.mono hUV
  have hsnd : ContDiffOn Real 1 (fun p : Real × Real => p.2) U :=
    contDiffOn_snd
  have hsqrt : ContDiffOn Real 1
      (fun p : Real × Real => Real.sqrt p.2) U :=
    hsnd.sqrt (fun p hp => hp.1.ne')
  have hinvSqrt : ContDiffOn Real 1
      (fun p : Real × Real => 1 / Real.sqrt p.2) U :=
    contDiffOn_const.div hsqrt
      (fun p hp => (Real.sqrt_pos.2 hp.1).ne')
  have hraw : ContDiffOn Real 1 raw U := by
    simpa only [raw] using
      (hsqrt.mul hdScalar).sub
        ((hinvSqrt.mul hpair1).add
          ((contDiffOn_const.mul hsqrt).mul
            (hdPair.sub (hdSpeed.div_const 2))))
  have hscalarDiff : DifferentiableOn Real scalar V :=
    hscalar2.differentiableOn (by norm_num)
  have hspeedDiff : DifferentiableOn Real speed V :=
    hspeed2.differentiableOn (by norm_num)
  have hpairDiff : DifferentiableOn Real pair V :=
    hpair2.differentiableOn (by norm_num)
  have heq : Set.EqOn euler raw U := by
    intro p hp
    let fp : Real → Real → M := fun a tau => f (p.1 + a) tau
    have hfp : IsSmoothVariation (I := I) fp := by
      exact (hf : ContMDiff _ _ (8 : ℕ) _).comp
        ((contMDiff_const.add contMDiff_fst).prodMk contMDiff_snd)
    have hfp0 : fp 0 = f p.1 := by
      funext tau
      simp only [fp, add_zero]
    have hYshift (tau : Real) :
        lVelocity (I := I) (fun a : Real => fp a tau) 0 =
          lVelocity (I := I) (fun a : Real => f a tau) p.1 := by
      simpa only [fp, lVelocity, varFst] using
        varFst_shift (I := I) f hf p.1 tau
    have hYfun :
        (fun tau : Real =>
          lVelocity (I := I) (fun a : Real => fp a tau) 0) =
        fun tau : Real =>
          lVelocity (I := I) (fun a : Real => f a tau) p.1 :=
      funext hYshift
    have hpV : p ∈ V := hUV hp
    have hscalarAt : DifferentiableAt Real scalar p :=
      (hscalarDiff p hpV).differentiableAt (hVopen.mem_nhds hpV)
    have hspeedAt : DifferentiableAt Real speed p :=
      (hspeedDiff p hpV).differentiableAt (hVopen.mem_nhds hpV)
    have hpairAt : DifferentiableAt Real pair p :=
      (hpairDiff p hpV).differentiableAt (hVopen.mem_nhds hpV)
    have hscalarSlice : HasDerivAt
        (fun u : Real => scalar (u, p.2)) (dScalar p) p.1 := by
      simpa only [dScalar] using Aux2.hasDerivAt_slice_fst
        (fun u tau : Real => scalar (u, tau)) p.1 p.2 hscalarAt
    have hscalarShift : HasDerivAt
        (fun u : Real => scalar (p.1 + u, p.2)) (dScalar p) 0 := by
      exact HasDerivAt.comp_const_add p.1 0 (by
        simpa only [add_zero] using hscalarSlice)
    have hfpSlice : ContMDiff 𝓘(Real, Real) I (8 : ℕ)
        (fun a : Real => fp a p.2) := by
      exact (hfp : ContMDiff _ _ (8 : ℕ) _).comp
        (contMDiff_id.prodMk contMDiff_const)
    have hscalarGeom :=
      lScalar_var_deriv S T p.2 fp
        (hfpSlice.mdifferentiableAt (by norm_num))
    rw [hfp0, hYshift p.2] at hscalarGeom
    have hdScalarEq :
        dScalar p =
          (S.base.metric (T - p.2)).inner (f p.1 p.2)
            (gradientFun (I := I) (S.base.metric (T - p.2))
              (S.scalar (T - p.2)) (f p.1 p.2))
            (lVelocity (I := I) (fun u : Real => f u p.2) p.1) := by
      exact hscalarShift.unique (by
        simpa [scalar, fp, hYshift] using hscalarGeom)
    have hspeedSlice : HasDerivAt
        (fun u : Real => speed (u, p.2)) (dSpeed p) p.1 := by
      simpa only [dSpeed] using Aux2.hasDerivAt_slice_fst
        (fun u tau : Real => speed (u, tau)) p.1 p.2 hspeedAt
    have hspeedShift : HasDerivAt
        (fun u : Real => speed (p.1 + u, p.2)) (dSpeed p) 0 := by
      exact HasDerivAt.comp_const_add p.1 0 (by
        simpa only [add_zero] using hspeedSlice)
    have hspeedGeom := lSpeedSq_var_deriv S T p.2 fp hfp
    rw [hfp0, hYfun] at hspeedGeom
    have hdSpeedEq :
        dSpeed p =
          2 * (S.base.metric (T - p.2)).inner (f p.1 p.2)
            (covDerivAlong (I := I) (S.base.metric (T - p.2))
              (fun tau : Real => f p.1 tau)
              (fun tau : Real =>
                lVelocity (I := I) (fun u : Real => f u tau) p.1) p.2)
            (lVelocity (I := I) (f p.1) p.2) := by
      exact hspeedShift.unique (by
        simpa [speed, fp, hYshift] using hspeedGeom)
    have hpairSlice : HasDerivAt
        (fun tau : Real => pair (p.1, tau)) (dPair p) p.2 := by
      simpa only [dPair] using Aux2.hasDerivAt_slice_snd
        (fun u tau : Real => pair (u, tau)) p.1 p.2 hpairAt
    have hpairGeom := lPair_deriv S hS T p.2 fp hfp hp.2
    rw [hfp0, hYfun] at hpairGeom
    have hdPairEq :
        dPair p =
          ((S.base.metric (T - p.2)).inner (f p.1 p.2)
              (covDerivAlong (I := I) (S.base.metric (T - p.2))
                (fun tau : Real => f p.1 tau)
                (fun tau : Real =>
                  lVelocity (I := I) (fun u : Real => f u tau) p.1) p.2)
              (lVelocity (I := I) (f p.1) p.2) +
            (S.base.metric (T - p.2)).inner (f p.1 p.2)
              (lVelocity (I := I) (fun u : Real => f u p.2) p.1)
              (covDerivAlong (I := I) (S.base.metric (T - p.2))
                (fun tau : Real => f p.1 tau)
                (fun tau : Real => lVelocity (I := I) (f p.1) tau)
                p.2)) +
            2 * S.ricciAt (T - p.2) (f p.1 p.2)
              (vec2
                (lVelocity (I := I) (fun u : Real => f u p.2) p.1)
                (lVelocity (I := I) (f p.1) p.2)) := by
      exact hpairSlice.unique (by
        simpa [pair, fp, hYshift] using hpairGeom)
    have hcoef :
        Real.sqrt p.2 * (1 / p.2) = 1 / Real.sqrt p.2 := by
      simpa only [div_eq_mul_inv, one_mul] using
        (Real.sqrt_div_self' (x := p.2))
    dsimp only [euler, raw]
    rw [hdScalarEq, hdSpeedEq, hdPairEq]
    simp only [lEulerPair]
    rw [← hcoef]
    ring
  have hout : ContDiffOn Real 1 euler U :=
    hraw.congr (fun p hp => heq hp)
  simpa only [euler, U] using hout

omit [InnerProductSpace Real E] [NeZero (Module.finrank Real E)]
  [SigmaCompactSpace M] in
theorem lLength_euler
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (f : Real → Real → M) (hf : IsSmoothVariation (I := I) f)
    (a b : Real) (hpos : 0 < min a b)
    (ht : ∀ tau ∈ Set.uIcc a b, T - tau ∈ D.regular) :
    HasDerivAt
      (fun u : Real => lLength S T (fun tau : Real => f u tau) a b)
      (2 * Real.sqrt b *
            (S.base.metric (T - b)).inner (f 0 b)
              (lVelocity (I := I) (fun u : Real => f u b) 0)
              (lVelocity (I := I) (f 0) b) -
        2 * Real.sqrt a *
            (S.base.metric (T - a)).inner (f 0 a)
              (lVelocity (I := I) (fun u : Real => f u a) 0)
              (lVelocity (I := I) (f 0) a) +
        ∫ tau in a..b,
          (-2 * Real.sqrt tau) *
            lEulerPair S T (f 0) tau
              (lVelocity (I := I) (fun u : Real => f u tau) 0))
      0 := by
  apply (lLength_first_var S hS T f hf a b hpos ht).congr_deriv
  congr 1
  apply intervalIntegral.integral_congr
  intro tau _
  have hcoef : Real.sqrt tau * (1 / tau) = 1 / Real.sqrt tau := by
    simpa only [div_eq_mul_inv, one_mul] using
      (Real.sqrt_div_self' (x := tau))
  simp only [lEulerPair]
  rw [← hcoef]
  ring

end normedSpaceCompatibility

end DifferentialGeometry.PDE.RicciFlow.Perelman
