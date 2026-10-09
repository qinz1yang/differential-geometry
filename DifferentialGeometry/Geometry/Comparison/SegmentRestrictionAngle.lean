import DifferentialGeometry.Geometry.Comparison.CanonicalGermAngle
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem germComparisonAngle_IccExtend_forward
    {X : Type*} [MetricSpace X] {a b h : ℝ} (hh : h ∈ Icc a b) (hhb : h < b)
    (κ : ℝ) (γ : ℝ → X) (σ : Icc a b → X) :
    germComparisonAngle κ γ (IccExtend (sub_nonneg.mpr hh.2)
      (fun s : Icc (0 : ℝ) (b - h) => IccExtend (hh.1.trans hh.2) σ (h + s))) =
    germComparisonAngle κ γ (fun s => IccExtend (hh.1.trans hh.2) σ (h + s)) := by
  apply germComparisonAngle_congr_on (r := 1) (s := b - h) zero_lt_one (sub_pos.mpr hhb)
    (fun _ _ => rfl)
  intro t ht
  exact IccExtend_of_mem _ _ ⟨ht.1.le, ht.2⟩

theorem germComparisonAngle_IccExtend_backward
    {X : Type*} [MetricSpace X] {a b h : ℝ} (hh : h ∈ Icc a b) (hah : a < h)
    (κ : ℝ) (γ : ℝ → X) (σ : Icc a b → X) :
    germComparisonAngle κ γ (IccExtend (sub_nonneg.mpr hh.1)
      (fun s : Icc (0 : ℝ) (h - a) => IccExtend (hh.1.trans hh.2) σ (h - s))) =
    germComparisonAngle κ γ (fun s => IccExtend (hh.1.trans hh.2) σ (h - s)) := by
  apply germComparisonAngle_congr_on (r := 1) (s := h - a) zero_lt_one (sub_pos.mpr hah)
    (fun _ _ => rfl)
  intro t ht
  exact IccExtend_of_mem _ _ ⟨ht.1.le, ht.2⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
