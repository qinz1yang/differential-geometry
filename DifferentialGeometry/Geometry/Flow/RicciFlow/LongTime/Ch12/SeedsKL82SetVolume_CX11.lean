import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import DifferentialGeometry.Geometry.Measure.MetricComparison
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82EventDistance_CX11

set_option autoImplicit false

noncomputable section

open Set Manifold MeasureTheory DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
  DifferentialGeometry.PDE.RicciFlow
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold ThreeModel ∞ M] [T2Space M]
  {D : RealTimeInterval}

/-- A one-sided Ricci lower bound gives forward metric growth at a fixed point.
The estimate is local in space and permits both endpoints of a smooth slab. -/
theorem inner_le_exp_of_ricci_lower_CX11
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    {a b k : ℝ} (hab : a ≤ b) (hcar : Icc a b ⊆ D.carrier)
    (hreg : Ioo a b ⊆ D.regular) (x : M) (v : TangentSpace ThreeModel x)
    (hRic : ∀ t ∈ Icc a b,
      -k * (S.base.metric t).inner x v v ≤ ricciTensor (S.base.metric t) x v v) :
    (S.base.metric b).inner x v v ≤
      Real.exp (2 * k * (b - a)) * (S.base.metric a).inner x v v := by
  let f : ℝ → ℝ := fun t => (S.base.metric t).inner x v v
  have hpde := metricPDE_Icc S hS hcar hreg
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun r => Real.exp (-2 * k * r) * f r)
        (Real.exp (-2 * k * t) *
          (-2 * ricciTensor (S.base.metric t) x v v - 2 * k * f t)) (Icc a b) t := by
    convert (((hasDerivAt_id t).const_mul (-2 * k)).exp.hasDerivWithinAt.mul
      (hpde t ht x v v)) using 1 <;> first | rfl | (dsimp [f]; ring)
  have hanti : AntitoneOn (fun r => Real.exp (-2 * k * r) * f r) (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    · intro t ht
      exact (hd t ht).continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).mono interior_subset
    · intro t ht
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hh := hRic t (interior_subset ht)
      dsimp [f]
      linarith
  have hh := mul_le_mul_of_nonneg_left
    (hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab) (Real.exp_pos (2 * k * b)).le
  have he (r : ℝ) : Real.exp (2 * k * b) * (Real.exp (-2 * k * r) * f r) =
      Real.exp (2 * k * (b - r)) * f r := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he, he, sub_self, mul_zero, Real.exp_zero, one_mul] at hh
  exact hh

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- Volume distortion of a fixed measurable set from a Ricci lower bound only on
that set. With `k = 2 / r0²`, the factor is exactly `exp (6 (b-a) / r0²)`.
No upper curvature bound or completeness is required. -/
theorem setVolume_le_exp_of_ricci_lower_CX11 [SigmaCompactSpace M]
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    {a b k : ℝ} (hab : a ≤ b) (hcar : Icc a b ⊆ D.carrier)
    (hreg : Ioo a b ⊆ D.regular) {A : Set M} (hA : MeasurableSet A)
    (hRic : ∀ t ∈ Icc a b, ∀ x ∈ A, ∀ v : TangentSpace ThreeModel x,
      -k * (S.base.metric t).inner x v v ≤ ricciTensor (S.base.metric t) x v v) :
    riemannianVolumeMeasure ThreeModel M (S.base.metric b) A ≤
      ENNReal.ofReal (Real.exp (3 * k * (b - a))) *
        riemannianVolumeMeasure ThreeModel M (S.base.metric a) A := by
  have hh := Geometry.Measure.riemannianVolumeMeasure_apply_le_of_inner_le
    (S.base.metric a) (S.base.metric b) (Real.exp_pos (2 * k * (b - a))) hA
    (fun x hx v => inner_le_exp_of_ricci_lower_CX11 S hS hab hcar hreg x v
      (fun t ht => hRic t ht x hx v))
  have he : Real.sqrt (Real.exp (2 * k * (b - a)) ^ Module.finrank ℝ ThreeSpace) =
      Real.exp (3 * k * (b - a)) := by
    rw [show Module.finrank ℝ ThreeSpace = 3 by simp [ThreeSpace]]
    rw [← Real.exp_nat_mul, ← Real.exp_half]
    congr 1
    ring
  rwa [he] at hh

/-- The same comparison written in the backward direction needed for traced
sets. Multiplication in `ℝ≥0∞` keeps the result valid without finite-volume assumptions. -/
theorem setVolume_ge_exp_of_ricci_lower_CX11 [SigmaCompactSpace M]
    (S : SolutionOn (I := ThreeModel) (M := M) D) (hS : IsSolutionOn S)
    {a b k : ℝ} (hab : a ≤ b) (hcar : Icc a b ⊆ D.carrier)
    (hreg : Ioo a b ⊆ D.regular) {A : Set M} (hA : MeasurableSet A)
    (hRic : ∀ t ∈ Icc a b, ∀ x ∈ A, ∀ v : TangentSpace ThreeModel x,
      -k * (S.base.metric t).inner x v v ≤ ricciTensor (S.base.metric t) x v v) :
    ENNReal.ofReal (Real.exp (-(3 * k * (b - a)))) *
        riemannianVolumeMeasure ThreeModel M (S.base.metric b) A ≤
      riemannianVolumeMeasure ThreeModel M (S.base.metric a) A := by
  have hh := mul_le_mul'
    (le_refl (ENNReal.ofReal (Real.exp (-(3 * k * (b - a))))))
    (setVolume_le_exp_of_ricci_lower_CX11 S hS hab hcar hreg hA hRic)
  rwa [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul] at hh

end GC.LongTime.Ch12
