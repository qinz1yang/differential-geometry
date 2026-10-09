import DifferentialGeometry.Geometry.Metric.ConeDistance
import DifferentialGeometry.Topology.Compactness.MapLimits
import Mathlib.Topology.Homeomorph.Defs

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace Metric

variable {Y : Type*} [MetricSpace Y] [CompactSpace Y]
  {T : Type*} [PseudoMetricSpace T] {a b lambda : ℝ}

theorem isEmbedding_of_scaled_cone_distance
    (ha : 0 < a) (hlambda : 0 < lambda) (D : Set (ℝ × Y))
    (hD : ∀ x ∈ D, x.1 ∈ Icc a b)
    (F : D → T)
    (hmetric : ∀ x y : D, dist (F x) (F y) =
      lambda * coneDistance (x : ℝ × Y) (y : ℝ × Y)) :
    Topology.IsEmbedding F := by
  have hself (x : D) : coneDistance (x : ℝ × Y) (x : ℝ × Y) = 0 :=
    coneDistance_self (x : ℝ × Y)
  have hcont : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hc : Continuous (fun y : D => lambda * coneDistance (y : ℝ × Y) (x : ℝ × Y)) :=
      continuous_const.mul (continuous_coneDistance.comp
        (continuous_subtype_val.prodMk continuous_const))
    simpa only [hmetric, hself, mul_zero] using hc.tendsto x
  have hinj : Function.Injective F := by
    intro x y hxy
    have h := hmetric x y
    rw [hxy, dist_self] at h
    have hz : coneDistance (x : ℝ × Y) (y : ℝ × Y) = 0 :=
      (mul_eq_zero.mp h.symm).resolve_left hlambda.ne'
    exact Subtype.ext ((coneDistance_eq_zero_iff (ha.trans_le (hD x x.property).1)
      (ha.trans_le (hD y y.property).1)).mp hz)
  let e : D ≃ range F := Equiv.ofInjective F hinj
  let B := Icc a b × Y
  let P : B → ℝ × Y := fun z => (z.1.1, z.2)
  let inv : range F → B := fun z => (⟨((e.symm z : D) : ℝ × Y).1,
    hD (e.symm z) (e.symm z).property⟩, ((e.symm z : D) : ℝ × Y).2)
  have hP : Continuous P := (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hback (z : range F) : F (e.symm z) = (z : T) :=
    congrArg Subtype.val (e.apply_symm_apply z)
  have hinv : Continuous inv := by
    apply Topology.continuous_of_compact_separating_kernel
      (fun z : B × B => lambda * coneDistance (P z.1) (P z.2))
      (continuous_const.mul (continuous_coneDistance.comp
        ((hP.comp continuous_fst).prodMk (hP.comp continuous_snd))))
      ?_ inv ?_
    · intro x y h
      have hz := (mul_eq_zero.mp h).resolve_left hlambda.ne'
      have heq := (coneDistance_eq_zero_iff (ha.trans_le x.1.2.1)
        (ha.trans_le y.1.2.1)).mp hz
      change ((x.1.1, x.2) : ℝ × Y) = (y.1.1, y.2) at heq
      exact Prod.ext (Subtype.ext (congrArg Prod.fst heq))
        (congrArg (fun z : ℝ × Y => z.2) heq)
    · intro x y
      change lambda * coneDistance ((e.symm x : D) : ℝ × Y)
        ((e.symm y : D) : ℝ × Y) = dist (x : T) (y : T)
      rw [← hmetric, hback, hback]
  have hinve : Continuous (e.symm : range F → D) := by
    apply Topology.IsEmbedding.subtypeVal.continuous_iff.mpr
    exact hP.comp hinv
  let he : D ≃ₜ range F := { e with
    continuous_toFun := hcont.subtype_mk (fun x => mem_range_self x)
    continuous_invFun := hinve }
  exact Topology.IsEmbedding.subtypeVal.comp he.isEmbedding

end Metric
