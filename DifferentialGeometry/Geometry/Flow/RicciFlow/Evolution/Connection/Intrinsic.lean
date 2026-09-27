import DifferentialGeometry.Geometry.Connection.LeviCivita.Variation.MetricDerivative
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.Expansion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Connection.TensorNabla.Iterated.Linearity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

theorem leviCivita_variation_pair_eq_neg_ricci_cov_deriv
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M) (v w z : TangentSpace I x) :
    (S.family.metric t).inner x (leviCivitaVariation S.family.metric t x w v) z =
      -totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
        (Fin.cons v (vec2 w z)) -
      totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
        (Fin.cons w (vec2 v z)) +
      totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
        (Fin.cons z (vec2 v w)) := by
  have hderiv : ∀ y a b, HasDerivAt (fun s => (S.family.metric s).inner y a b)
      (((-2 : ℝ) • S.ricci t) y (vec2 a b)) (t : ℝ) := by
    intro y a b
    simpa [ContMDiffSection.coe_smul, Tensor0SSpace.smul_apply,
      SolutionOn.ricci, SolutionOn.ricciAt] using metricDerivAt S hS t y a b
  have hc := leviCivita_variation_koszul_of_metricFamilySmoothOn hS.smoothMetric
    (D.regular_isOpen.mem_nhds t.2) ((-2 : ℝ) • S.ricci t) hderiv x v w z
  rw [totalNabla0SFun_smul] at hc
  simp only [Tensor0SSpace.smul_apply, smul_eq_mul] at hc
  linarith

theorem leviCivita_hasDerivAt_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime)
    {Y : (x : M) → TangentSpace I x} {x : M}
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% Y) x)
    (v : TangentSpace I x) :
    HasDerivAt (fun s => (LeviCivita (S.family.metric s)) Y x v)
      (leviCivitaVariation S.family.metric t x (Y x) v) (t : ℝ) := by
  apply leviCivita_hasDerivAt_of_metric_deriv S.family.metric ((-2 : ℝ) • S.ricci t)
    (t : ℝ) ?_ ?_ hY v
  · intro y a b
    simpa [ContMDiffSection.coe_smul, Tensor0SSpace.smul_apply,
      SolutionOn.ricci, SolutionOn.ricciAt] using metricDerivAt S hS t y a b
  · intro X Z y
    simpa using (hS.smoothMetric.pairSmoothAt (x := y)
      (D.regular_isOpen.mem_nhds t.2) ![X, Z]).of_le
        (show (2 : WithTop ℕ∞) ≤ ∞ from by
          change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
          exact WithTop.coe_le_coe.mpr le_top)

end DifferentialGeometry.PDE.RicciFlow

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]

theorem leviCivita_variation_coeff_eq_neg_ricci_cov_deriv
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M)
    {Idx : Type*} [Fintype Idx] (b : Module.Basis Idx ℝ (TangentSpace I x)) (i j k : Idx) :
    b.repr (leviCivitaVariation S.family.metric t x (b j) (b i)) k =
      -∑ l, basisInvMetric (I := I) (S.family.metric t) x b k l *
        (totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
            (Fin.cons (b i) (vec2 (b j) (b l))) +
          totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
            (Fin.cons (b j) (vec2 (b i) (b l))) -
          totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
            (Fin.cons (b l) (vec2 (b i) (b j)))) := by
  classical
  rw [basis_repr_eq_sum_inv_inner (S.family.metric t) x b _
    (basisInvMetric_isInverse (S.family.metric t) x b), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [leviCivita_variation_pair_eq_neg_ricci_cov_deriv S hS t x]
  ring

theorem leviCivita_coeff_hasDerivAt_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) (t : D.RegularTime) (x : M)
    {Idx : Type*} [Fintype Idx] (b : Module.Basis Idx ℝ (TangentSpace I x))
    (Y : Idx → (x : M) → TangentSpace I x)
    (hY : ∀ j, MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (T% (Y j)) x)
    (hYx : ∀ j, Y j x = b j) (i j k : Idx) :
    HasDerivAt (fun s => b.repr ((LeviCivita (S.family.metric s)) (Y j) x (b i)) k)
      (-∑ l, basisInvMetric (I := I) (S.family.metric t) x b k l *
        (totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
            (Fin.cons (b i) (vec2 (b j) (b l))) +
          totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
            (Fin.cons (b j) (vec2 (b i) (b l))) -
          totalNabla0SFun 2 (LeviCivita (S.family.metric t)) (S.ricci t) x
            (Fin.cons (b l) (vec2 (b i) (b j))))) (t : ℝ) := by
  let c := (b.coord k).toContinuousLinearMap
  have hd := c.hasFDerivAt.comp_hasDerivAt (t : ℝ)
    (leviCivita_hasDerivAt_of_solution S hS t (hY j) (b i))
  change HasDerivAt (fun s => b.repr ((LeviCivita (S.family.metric s)) (Y j) x (b i)) k)
    (b.repr (leviCivitaVariation S.family.metric t x (Y j x) (b i)) k) (t : ℝ) at hd
  simpa only [hYx, leviCivita_variation_coeff_eq_neg_ricci_cov_deriv S hS t x b] using hd

end DifferentialGeometry.PDE.RicciFlow
