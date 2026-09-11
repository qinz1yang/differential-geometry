import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace DifferentialGeometry.Geometry.Metric

section Busemann

variable {M : Type*} [PseudoMetricSpace M] {gamma : ℝ → M}

def busemannFunction (gamma : ℝ → M) (x : M) : ℝ :=
  ⨅ t : ℝ, dist x (gamma t) - t

private theorem busemann_approx_lower (hgamma : Isometry gamma) (x : M) (t : ℝ) :
    -dist x (gamma 0) ≤ dist x (gamma t) - t := by
  have htriangle := dist_triangle (gamma 0) x (gamma t)
  rw [hgamma.dist_eq, Real.dist_eq, zero_sub, abs_neg,
    dist_comm (gamma 0) x] at htriangle
  linarith [le_abs_self t]

private theorem busemann_approx_bddBelow (hgamma : Isometry gamma) (x : M) :
    BddBelow (Set.range (fun t : ℝ ↦ dist x (gamma t) - t)) := by
  refine ⟨-dist x (gamma 0), ?_⟩
  rintro _ ⟨t, rfl⟩
  exact busemann_approx_lower hgamma x t

private theorem busemann_approx_antitone (hgamma : Isometry gamma) (x : M) :
    Antitone (fun t : ℝ ↦ dist x (gamma t) - t) := by
  intro s t hst
  have htriangle := dist_triangle x (gamma s) (gamma t)
  rw [hgamma.dist_eq, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr hst)] at htriangle
  linarith

theorem busemannFunction_tendsto (hgamma : Isometry gamma) (x : M) :
    Tendsto (fun t : ℝ ↦ dist x (gamma t) - t) atTop
      (𝓝 (busemannFunction gamma x)) :=
  tendsto_atTop_ciInf (busemann_approx_antitone hgamma x)
    (busemann_approx_bddBelow hgamma x)

theorem busemannFunction_bounds (hgamma : Isometry gamma) (x : M) :
    -dist x (gamma 0) ≤ busemannFunction gamma x ∧
      busemannFunction gamma x ≤ dist x (gamma 0) := by
  constructor
  · exact le_ciInf (busemann_approx_lower hgamma x)
  · simpa only [busemannFunction, sub_zero] using ciInf_le (busemann_approx_bddBelow hgamma x) 0

private theorem busemann_le_add_dist (hgamma : Isometry gamma) (x y : M) :
    busemannFunction gamma x ≤ busemannFunction gamma y + dist x y := by
  have hlower : busemannFunction gamma x - dist x y ≤ busemannFunction gamma y := by
    apply le_ciInf
    intro t
    have hx : busemannFunction gamma x ≤ dist x (gamma t) - t :=
      ciInf_le (busemann_approx_bddBelow hgamma x) t
    have htriangle := dist_triangle x y (gamma t)
    linarith
  linarith

theorem busemannFunction_lipschitz (hgamma : Isometry gamma) :
    LipschitzWith 1 (busemannFunction gamma) := by
  apply LipschitzWith.mk_one
  intro x y
  rw [Real.dist_eq, abs_le]
  constructor
  · have h := busemann_le_add_dist hgamma y x
    rw [dist_comm y x] at h
    linarith
  · have h := busemann_le_add_dist hgamma x y
    linarith

theorem busemannFunction_apply_line (hgamma : Isometry gamma) (s : ℝ) :
    busemannFunction gamma (gamma s) = -s := by
  apply le_antisymm
  · simpa only [busemannFunction, dist_self, zero_sub] using
      ciInf_le (busemann_approx_bddBelow hgamma (gamma s)) s
  · apply le_ciInf
    intro t
    rw [hgamma.dist_eq, Real.dist_eq]
    linarith [neg_le_abs (s - t)]

private theorem busemann_reverse_isometry (hgamma : Isometry gamma) :
    Isometry (fun t : ℝ ↦ gamma (-t)) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [hgamma.dist_eq, Real.dist_eq, Real.dist_eq]
  have hneg : -s - -t = -(s - t) := by ring
  rw [hneg, abs_neg]

theorem busemannFunction_reverse_apply_line (hgamma : Isometry gamma) (s : ℝ) :
    busemannFunction (fun t : ℝ ↦ gamma (-t)) (gamma s) = s := by
  simpa only [neg_neg] using
    busemannFunction_apply_line (busemann_reverse_isometry hgamma) (-s)

theorem busemannFunction_add_reverse_nonneg (hgamma : Isometry gamma) (x : M) :
    0 ≤ busemannFunction gamma x + busemannFunction (fun t : ℝ ↦ gamma (-t)) x := by
  have htriangle (u v : ℝ) :
      0 ≤ (dist x (gamma u) - u) + (dist x (gamma (-v)) - v) := by
    have h := dist_triangle (gamma u) x (gamma (-v))
    rw [hgamma.dist_eq, Real.dist_eq, dist_comm (gamma u) x] at h
    linarith [le_abs_self (u - -v)]
  have hreverse (u : ℝ) :
      -(dist x (gamma u) - u) ≤ busemannFunction (fun t : ℝ ↦ gamma (-t)) x := by
    apply le_ciInf
    intro v
    linarith [htriangle u v]
  have hforward :
      -busemannFunction (fun t : ℝ ↦ gamma (-t)) x ≤ busemannFunction gamma x := by
    apply le_ciInf
    intro u
    linarith [hreverse u]
  linarith

end Busemann

end DifferentialGeometry.Geometry.Metric
end
