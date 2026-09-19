import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Connection.DifferenceTimeDerivative
import DifferentialGeometry.Geometry.Connection.VariationNorm
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open MeasureTheory Filter Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem intervalIntegrable_connectionVariationSpeed_pairing_of_metric_comparison
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {T c : ℝ} (hT : 0 ≤ T)
    (hcarrier : Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : Ioc (0 : ℝ) T ⊆ D.regular)
    (x : M) (u w v : TangentSpace I x)
    (hlow : ∀ s ∈ Ioc (0 : ℝ) T, ∀ z : TangentSpace I x,
      Real.sqrt ((S.base.metric 0).inner x z z) ≤
        Real.exp c * Real.sqrt ((S.base.metric s).inner x z z))
    (hup : ∀ s ∈ Ioc (0 : ℝ) T, ∀ z : TangentSpace I x,
      Real.sqrt ((S.base.metric s).inner x z z) ≤
        Real.exp c * Real.sqrt ((S.base.metric 0).inner x z z))
    (hint : IntervalIntegrable
      (fun s => Real.sqrt (nablaKRm04NormSqIntrinsic S 1 s x)) volume 0 T) :
    IntervalIntegrable
      (fun s => (S.base.metric 0).inner x (connectionVariationSpeed S s x u w) v)
      volume 0 T := by
  let f : ℝ → ℝ := fun s =>
    (S.base.metric 0).inner x (connectionVariationSpeed S s x u w) v
  let F : ℝ → ℝ := fun s => (S.base.metric 0).inner x
    (CovariantDerivative.difference
      (LeviCivita (S.base.metric s)) (LeviCivita (S.base.metric 0)) x u w) v
  have heq : deriv F =ᵐ[volume.restrict (uIoc 0 T)] f := by
    rw [uIoc_of_le hT]
    refine ae_restrict_of_ae_eq_of_ae_restrict Ioo_ae_eq_Ioc ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun s hs => ?_
    exact ((hasDerivWithinAt_connectionDifference_pairing_of_mem_Ioc S hS
      hcarrier hregular ⟨hs.1, hs.2.le⟩ x u w v).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)).deriv
  have hmeas : AEStronglyMeasurable f (volume.restrict (uIoc 0 T)) :=
    (aestronglyMeasurable_deriv F _).congr heq
  let cn : ℝ := Real.sqrt ((Module.finrank ℝ E : ℝ) ^ 5)
  let C : ℝ := 3 * cn * Real.exp (3 * c) *
    Real.sqrt ((S.base.metric 0).inner x u u) *
    Real.sqrt ((S.base.metric 0).inner x w w) *
    Real.sqrt ((S.base.metric 0).inner x v v)
  apply (hint.const_mul C).mono_fun' hmeas
  change ∀ᵐ s ∂volume.restrict (uIoc 0 T),
    ‖f s‖ ≤ C * Real.sqrt (nablaKRm04NormSqIntrinsic S 1 s x)
  rw [uIoc_of_le hT, ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun s hs => ?_
  have hscc : s ∈ Icc (0 : ℝ) T := ⟨hs.1.le, hs.2⟩
  have hspeed := norm_connection_variation_le_of_metric_comparison
    (S.base.metric 0) (S.base.metric s) x (nablaRicci S s x)
    (connectionVariationSpeed S s x u w) u w
    (r := cn * Real.sqrt (nablaKRm04NormSqIntrinsic S 1 s x)) (c := c)
    (fun z => connectionVariationKoszulOn_connectionVariationSpeed S T s hscc x u w z)
    (nablaRicciNormBoundOn_nablaRicci S T s hscc x)
    (hlow s hs) (hup s hs)
  rw [Real.norm_eq_abs]
  calc |f s|
      ≤ Real.sqrt ((S.base.metric 0).inner x
          (connectionVariationSpeed S s x u w) (connectionVariationSpeed S s x u w)) *
          Real.sqrt ((S.base.metric 0).inner x v v) :=
        DifferentialGeometry.Analysis.Laplacian.abs_metric_inner_le_sqrt_metric_quadratic
          (S.base.metric 0) x (connectionVariationSpeed S s x u w) v
    _ ≤ (3 * (cn * Real.sqrt (nablaKRm04NormSqIntrinsic S 1 s x)) *
          Real.exp (3 * c) * Real.sqrt ((S.base.metric 0).inner x u u) *
          Real.sqrt ((S.base.metric 0).inner x w w)) *
          Real.sqrt ((S.base.metric 0).inner x v v) :=
        mul_le_mul_of_nonneg_right hspeed (Real.sqrt_nonneg _)
    _ = C * Real.sqrt (nablaKRm04NormSqIntrinsic S 1 s x) := by
        dsimp [C]
        ring

end DifferentialGeometry.PDE.RicciFlow

end

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open MeasureTheory Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem intervalIntegrable_connectionVariationSpeed_pairing_of_curvature_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {T K : ℝ} (hT : 0 ≤ T)
    (hcarrier : Icc (0 : ℝ) T ⊆ D.carrier)
    (hregular : Ioc (0 : ℝ) T ⊆ D.regular)
    (x : M) (u w v : TangentSpace I x)
    (hcurv : ∀ s ∈ Icc (0 : ℝ) T, nablaKRm04NormSqIntrinsic S 0 s x ≤ K)
    (hint : IntervalIntegrable
      (fun s => Real.sqrt (nablaKRm04NormSqIntrinsic S 1 s x)) volume 0 T) :
    IntervalIntegrable
      (fun s => (S.base.metric 0).inner x (connectionVariationSpeed S s x u w) v)
      volume 0 T := by
  let L : ℝ := (Module.finrank ℝ E : ℝ) ^ 2 * Real.sqrt K
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hcurv0 : ∀ s ∈ Icc (0 : ℝ) T,
      DifferentialGeometry.Tensor0SBundle.normSq0S (S.base.metric s) x 4
        (S.base.rm04 s x) ≤ K := by
    intro s hs
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero]
      using hcurv s hs
  have hric : ∀ s ∈ Icc (0 : ℝ) T, ∀ y ∈ ({x} : Set M),
      ∀ z : TangentSpace I y,
      |ricciTensor (S.base.metric s) y z z| ≤ L * (S.base.metric s).inner y z z := by
    intro s hs y hy z
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact ricci_quadratic_form_bound_of_solution_curvature_bound S x z (hcurv0 s hs)
  have hpde := metricPDE_Icc S hS hcarrier (fun _ h => hregular ⟨h.1, h.2.le⟩)
  have hequiv := metricEquiv_Icc_on (fun s => S.base.metric s) {x} hpde hric
  have hsqrt {a b c : ℝ} (h : a ≤ Real.exp (2 * c) * b) :
      Real.sqrt a ≤ Real.exp c * Real.sqrt b := by
    have hrw : Real.exp (2 * c) * b = Real.exp c ^ 2 * b := by
      rw [show (2 : ℝ) * c = c + c by ring, Real.exp_add]
      ring
    rw [hrw] at h
    calc Real.sqrt a ≤ Real.sqrt (Real.exp c ^ 2 * b) := Real.sqrt_le_sqrt h
      _ = Real.exp c * Real.sqrt b := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.exp_nonneg c)]
  apply intervalIntegrable_connectionVariationSpeed_pairing_of_metric_comparison
    S hS hT hcarrier hregular x u w v (c := L * T) ?_ ?_ hint
  · intro s hs z
    have hlo : Real.exp (-(2 * L * s)) * (S.base.metric 0).inner x z z ≤
        (S.base.metric s).inner x z z := by
      simpa only [sub_zero] using (hequiv s ⟨hs.1.le, hs.2⟩ x (by simp) z).1
    have hmul := mul_le_mul_of_nonneg_left hlo (Real.exp_pos (2 * L * s)).le
    have heq : Real.exp (2 * L * s) *
        (Real.exp (-(2 * L * s)) * (S.base.metric 0).inner x z z) =
        (S.base.metric 0).inner x z z := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    rw [heq] at hmul
    have hcompare : (S.base.metric 0).inner x z z ≤
        Real.exp (2 * (L * s)) * (S.base.metric s).inner x z z := by
      simpa only [mul_assoc] using hmul
    exact (hsqrt hcompare).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hL)) (Real.sqrt_nonneg _))
  · intro s hs z
    have hupper : (S.base.metric s).inner x z z ≤
        Real.exp (2 * (L * s)) * (S.base.metric 0).inner x z z := by
      simpa only [sub_zero, mul_assoc] using
        (hequiv s ⟨hs.1.le, hs.2⟩ x (by simp) z).2
    exact (hsqrt hupper).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hL)) (Real.sqrt_nonneg _))

end DifferentialGeometry.PDE.RicciFlow

end
