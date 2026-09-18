import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalCurvatureJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Tensor
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.InverseSmooth
import Mathlib.Analysis.Calculus.FDeriv.Extend

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.Coordinates
open Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff _root_.Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

private local instance terminalEvolutionC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance terminalEvolutionC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)

private theorem riemann_evolution_basis_rhs_continuousWithinAt_terminal
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (x : M)
    (m : Fin 4 → CoordinateIdx (𝕜 := ℝ) E) :
    ContinuousWithinAt (fun t =>
      (roughLap0SField (S.family.metric t) (S.base.rm04 t) x -
        (2 : ℝ) • curvatureQuadraticCombination (S.family.metric t) (S.base.rm04 t) x -
        ricciDrift04 (S.family.metric t) x)
          (fun q => coordinateFrameAtToBasis (I := I) x (m q))) (Set.Iio b) b := by
  classical
  let basis := coordinateFrameAtToBasis (I := I) x
  let gInv := fun t => coordInv S x t x
  have hinv (t : ℝ) : MetricInverseInBasis (S.family.metric t) x basis (gInv t) :=
    coordInvReal S x t
  have hb : b ∈ D.carrier := hslab ⟨hab.le, le_rfl⟩
  have hnear : D.carrier ∈ 𝓝[<] b :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hab) (Set.Ioo_subset_Icc_self.trans hslab)
  have hInv (i j : CoordinateIdx (𝕜 := ℝ) E) :
      ContinuousWithinAt (fun t => gInv t i j) (Set.Iio b) b := by
    have hmap : ContinuousOn (fun t : ℝ => (t, x)) D.carrier :=
      (continuous_id.prodMk continuous_const).continuousOn
    have hc := (coordInvContOn S hS x i j).comp hmap
      (fun t ht => ⟨ht, coordinateFrameAt_mem (I := I) x⟩)
    simpa only [Function.comp_def, gInv] using
      (hc b hb).mono_of_mem_nhdsWithin hnear
  have hRm (v : Fin 4 → TangentSpace I x) :
      ContinuousWithinAt (fun t => S.base.rm04 t x v) (Set.Iio b) b := by
    simpa only [nablaKRm04Field_zero] using
      (solution_nablaKRm04_eval_continuousWithinAt_terminal
        S hS hab hslab hreg 0 x v).mono Set.Iio_subset_Iic_self
  have hRic (v w : TangentSpace I x) :
      ContinuousWithinAt (fun t => metricRicciAt (S.family.metric t) x (vec2 v w))
        (Set.Iio b) b := by
    have hc : ContinuousOn (fun t => S.ricci t x (vec2 v w)) D.carrier := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact hS.ricciCont.eval_continuous (P := {t : ℝ // t ∈ D.carrier})
        (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
        (fun t => t.2) continuous_const
        (v := fun k _ => vec2 v w k) (fun _ => continuous_const)
    exact (hc b hb).mono_of_mem_nhdsWithin hnear
  have hL : ContinuousWithinAt (fun t => roughLap0SField (S.family.metric t)
      (S.base.rm04 t) x (fun q => basis (m q))) (Set.Iio b) b := by
    have heq (t : ℝ) : roughLap0SField (S.family.metric t) (S.base.rm04 t) x
        (fun q => basis (m q)) =
        ∑ i, ∑ j, gInv t i j * nablaKRm04Field S t 2 x
          (metricTraceInput (basis i) (basis j) (fun q => basis (m q))) := by
      change roughLap0STensor (S.family.metric t) (nablaKRm04Field S t 2 x) _ = _
      rw [roughLap0STensor_apply, metricTraceFirstTwo0SAt_eq_sum_basis
        (S.family.metric t) basis (gInv t) (hinv t)]
      rfl
    simp_rw [heq]
    exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      (hInv i j).mul ((solution_nablaKRm04_eval_continuousWithinAt_terminal
        S hS hab hslab hreg 2 x _).mono Set.Iio_subset_Iic_self)
  have hQ : ContinuousWithinAt (fun t => curvatureQuadraticCombination
      (S.family.metric t) (S.base.rm04 t) x (fun q => basis (m q))) (Set.Iio b) b := by
    have heq (t : ℝ) := curvatureQuadraticCombination_component
      (S.family.metric t) basis (gInv t) (hinv t) (S.base.rm04 t) m
    simp only [component0S_apply] at heq
    simp_rw [heq]
    refine ((ContinuousWithinAt.sub ?_ ?_).add ?_).sub ?_
    all_goals
      exact tendsto_finsetSum _ fun f _ => tendsto_finsetSum _ fun r _ =>
        tendsto_finsetSum _ fun e _ => tendsto_finsetSum _ fun q _ =>
          (((hInv f r).mul (hInv e q)).mul (hRm _)).mul (hRm _)
  have hDrift : ContinuousWithinAt (fun t => ricciDrift04 (S.family.metric t) x
      (fun q => basis (m q))) (Set.Iio b) b := by
    have hv : vec4 (basis (m 0)) (basis (m 1)) (basis (m 2)) (basis (m 3)) =
        fun q => basis (m q) := by
      funext q
      fin_cases q <;> rfl
    have heq (t : ℝ) := ricciDrift_comp (S.family.metric t) basis (gInv t)
      (hinv t) (m 0) (m 1) (m 2) (m 3)
    rw [hv] at heq
    change ContinuousWithinAt (fun t => Tensor0SSpace.eval
      (ricciDrift04 (S.family.metric t) x) (fun q => basis (m q))) (Set.Iio b) b
    simp_rw [heq]
    refine ((ContinuousWithinAt.add ?_ ?_).add ?_).add ?_
    all_goals
      refine tendsto_finsetSum _ fun p _ => ContinuousWithinAt.mul ?_ ?_
      · exact tendsto_finsetSum _ fun i _ => (hInv p i).mul (hRic _ _)
      · exact hRm _
  convert (hL.sub (continuousWithinAt_const.mul hQ)).sub hDrift using 1 <;> rfl

theorem riemann_tensor_hasDerivWithinAt_terminal_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (x : M) :
    HasDerivWithinAt (fun t => S.base.rm04 t x)
      (roughLap0SField (S.family.metric b) (S.base.rm04 b) x -
        (2 : ℝ) • curvatureQuadraticCombination (S.family.metric b) (S.base.rm04 b) x -
        ricciDrift04 (S.family.metric b) x) (Set.Iic b) b := by
  let e := tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x
  let rhs := fun t => roughLap0SField (S.family.metric t) (S.base.rm04 t) x -
    (2 : ℝ) • curvatureQuadraticCombination (S.family.metric t) (S.base.rm04 t) x -
    ricciDrift04 (S.family.metric t) x
  have hd : HasDerivWithinAt (fun t => e (S.base.rm04 t x)) (e (rhs b)) (Set.Iic b) b := by
    apply ContinuousMultilinearMap.hasDerivWithinAt_of_basis_eval
      (coordinateFrameAtToBasis (I := I) x)
    intro m
    let v := fun q => coordinateFrameAtToBasis (I := I) x (m q)
    have hint (t : ℝ) (ht : t ∈ Set.Ioo a b) :
        HasDerivAt (fun s => S.base.rm04 s x v) (rhs t v) t := by
      simpa only [rhs, Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply, smul_eq_mul]
        using riemann_hasDerivAt_of_solution S hS ⟨t, hreg ht⟩ x v
    have hcont : ContinuousWithinAt (fun t => S.base.rm04 t x v) (Set.Ioo a b) b := by
      have h := solution_nablaKRm04_eval_continuousWithinAt_terminal
        S hS hab hslab hreg 0 x v
      simpa only [nablaKRm04Field_zero] using h.mono
        (fun _ ht => ht.2.le : Set.Ioo a b ⊆ Set.Iic b)
    refine hasDerivWithinAt_Iic_of_tendsto_deriv (s := Set.Ioo a b)
      (fun t ht => (hint t ht).differentiableAt.differentiableWithinAt)
      hcont (Ioo_mem_nhdsLT hab) ?_
    exact (riemann_evolution_basis_rhs_continuousWithinAt_terminal
      S hS hab hslab hreg x m).tendsto.congr'
        (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hab)
          fun t ht => (hint t ht).deriv).symm
  exact e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt b hd

theorem riemann_hasDerivWithinAt_terminal_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hab : a < b) (hslab : Set.Icc a b ⊆ D.carrier)
    (hreg : Set.Ioo a b ⊆ D.regular) (x : M) (v : Fin 4 → TangentSpace I x) :
    HasDerivWithinAt (fun t => S.base.rm04 t x v)
      (roughLap0SField (S.family.metric b) (S.base.rm04 b) x v -
        2 * curvatureQuadraticCombination (S.family.metric b) (S.base.rm04 b) x v -
        ricciDrift04 (S.family.metric b) x v) (Set.Iic b) b := by
  let e := tensor0SSpaceFiberContinuousLinearEquiv (I := I) 4 x
  let ev := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 4 => TangentSpace I x) ℝ v
  have h := (ev.comp e.toContinuousLinearMap).hasFDerivAt.comp_hasDerivWithinAt b
    (riemann_tensor_hasDerivWithinAt_terminal_of_solution S hS hab hslab hreg x)
  change HasDerivWithinAt (fun t => S.base.rm04 t x v)
    ((roughLap0SField (S.family.metric b) (S.base.rm04 b) x -
      (2 : ℝ) • curvatureQuadraticCombination (S.family.metric b) (S.base.rm04 b) x -
      ricciDrift04 (S.family.metric b) x) v) (Set.Iic b) b at h
  simpa only [Tensor0SSpace.sub_apply, Tensor0SSpace.smul_apply, smul_eq_mul] using h

end DifferentialGeometry.PDE.RicciFlow
