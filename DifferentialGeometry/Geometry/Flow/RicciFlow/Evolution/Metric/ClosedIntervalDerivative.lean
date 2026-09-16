import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.CoefficientEvolution
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Coordinates.MetricComparison

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem metric_inner_hasDerivWithinAt_on_closed_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b t : ℝ} (hab : a < b) (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular) (ht : t ∈ Icc a b)
    (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt (fun s => (S.base.metric s).inner x v w)
      (-2 * S.ricciAt t x (vec2 v w)) (Icc a b) t := by
  have hint (s : ℝ) (hs : s ∈ Ioo a b) :
      HasDerivAt (fun r => (S.base.metric r).inner x v w)
        (-2 * S.ricciAt s x (vec2 v w)) s :=
    metricDerivAt S hS ⟨s, hregular hs⟩ x v w
  have hRic : ContinuousOn (fun s => S.ricciAt s x (vec2 v w)) D.carrier := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact hS.ricciCont.eval_continuous (P := {s : ℝ // s ∈ D.carrier})
      (τ := Subtype.val) (b := fun _ => x) continuous_subtype_val
      (fun s => s.2) continuous_const (v := fun i _ => vec2 v w i)
      (fun _ => continuous_const)
  have hsub : Ioo a b ⊆ D.carrier := Ioo_subset_Icc_self.trans hcarrier
  have hmetric (s : ℝ) (hs : s ∈ Icc a b) :
      ContinuousWithinAt (fun r => (S.base.metric r).inner x v w) (Ioo a b) s :=
    (hS.smoothMetric.coeff_cont x v w s (hcarrier hs)).mono hsub
  have hrhs (s : ℝ) (hs : s ∈ Icc a b) :
      ContinuousWithinAt (fun r => -2 * S.ricciAt r x (vec2 v w)) (Ioo a b) s :=
    continuousWithinAt_const.mul ((hRic s (hcarrier hs)).mono hsub)
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · have hright := hasDerivWithinAt_Ici_of_tendsto_deriv (s := Ioo a b)
      (fun s hs => (hint s hs).differentiableAt.differentiableWithinAt)
      (hmetric a ⟨le_rfl, hab.le⟩) (Ioo_mem_nhdsGT hab)
      (((hrhs a ⟨le_rfl, hab.le⟩).mono_of_mem_nhdsWithin
        (Ioo_mem_nhdsGT hab)).tendsto.congr'
          (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsGT hab)
            fun s hs => (hint s hs).deriv).symm)
    exact hright.mono Icc_subset_Ici_self
  · rcases lt_or_eq_of_le ht.2 with htb | htb
    · exact (hint t ⟨hat, htb⟩).hasDerivWithinAt
    · subst t
      have hleft := hasDerivWithinAt_Iic_of_tendsto_deriv (s := Ioo a b)
        (fun s hs => (hint s hs).differentiableAt.differentiableWithinAt)
        (hmetric b ⟨hab.le, le_rfl⟩) (Ioo_mem_nhdsLT hab)
        (((hrhs b ⟨hab.le, le_rfl⟩).mono_of_mem_nhdsWithin
          (Ioo_mem_nhdsLT hab)).tendsto.congr'
            (Filter.eventuallyEq_of_mem (Ioo_mem_nhdsLT hab)
              fun s hs => (hint s hs).deriv).symm)
      exact hleft.mono Icc_subset_Iic_self


omit [T2Space M] in
theorem norm_ricci_pairing_le_of_metric_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (gRef : SmoothRiemannianMetric I M) {t B C Rv Rw : ℝ}
    (hB : 0 ≤ B) (x : M) (v w : TangentSpace I x)
    (hmetric : ∀ u : TangentSpace I x,
      (S.base.metric t).inner x u u ≤ B * gRef.inner x u u)
    (hRic : Real.sqrt (normSq0S (S.base.metric t) x 2 (S.ricciAt t x)) ≤ C)
    (hv : Real.sqrt (gRef.inner x v v) ≤ Rv)
    (hw : Real.sqrt (gRef.inner x w w) ≤ Rw) :
    ‖-2 * S.ricciAt t x (vec2 v w)‖ ≤ 2 * C * B * (Rv * Rw) := by
  have hC : 0 ≤ C := (Real.sqrt_nonneg _).trans hRic
  have hRv : 0 ≤ Rv := (Real.sqrt_nonneg _).trans hv
  have hRw : 0 ≤ Rw := (Real.sqrt_nonneg _).trans hw
  have hv' : Real.sqrt ((S.base.metric t).inner x v v) ≤ Real.sqrt B * Rv := by
    calc
      _ ≤ Real.sqrt (B * gRef.inner x v v) := Real.sqrt_le_sqrt (hmetric v)
      _ = Real.sqrt B * Real.sqrt (gRef.inner x v v) := Real.sqrt_mul hB _
      _ ≤ _ := mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg B)
  have hw' : Real.sqrt ((S.base.metric t).inner x w w) ≤ Real.sqrt B * Rw := by
    calc
      _ ≤ Real.sqrt (B * gRef.inner x w w) := Real.sqrt_le_sqrt (hmetric w)
      _ = Real.sqrt B * Real.sqrt (gRef.inner x w w) := Real.sqrt_mul hB _
      _ ≤ _ := mul_le_mul_of_nonneg_left hw (Real.sqrt_nonneg B)
  have hprod : Real.sqrt ((S.base.metric t).inner x v v) *
      Real.sqrt ((S.base.metric t).inner x w w) ≤ B * (Rv * Rw) := by
    calc
      _ ≤ (Real.sqrt B * Rv) * (Real.sqrt B * Rw) :=
        mul_le_mul hv' hw' (Real.sqrt_nonneg _) (by positivity)
      _ = (Real.sqrt B) ^ 2 * (Rv * Rw) := by ring
      _ = B * (Rv * Rw) := by rw [Real.sq_sqrt hB]
  have heval := abs_apply_le_norm0S (S.base.metric t) x 2 (S.ricciAt t x) (vec2 v w)
  have heval' : |S.ricciAt t x (vec2 v w)| ≤ C * (B * (Rv * Rw)) := by
    calc
      _ ≤ Real.sqrt (normSq0S (S.base.metric t) x 2 (S.ricciAt t x)) *
          (Real.sqrt ((S.base.metric t).inner x v v) *
            Real.sqrt ((S.base.metric t).inner x w w)) := by
        simpa [Fin.prod_univ_two, vec2] using heval
      _ ≤ C * (B * (Rv * Rw)) :=
        mul_le_mul hRic hprod (by positivity) hC
  rw [Real.norm_eq_abs, abs_mul, show |(-2 : ℝ)| = 2 by norm_num]
  calc
    _ ≤ 2 * (C * (B * (Rv * Rw))) := mul_le_mul_of_nonneg_left heval' (by norm_num)
    _ = _ := by ring

end DifferentialGeometry.PDE.RicciFlow
