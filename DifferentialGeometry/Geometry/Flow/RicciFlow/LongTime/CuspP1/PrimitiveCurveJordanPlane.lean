import DifferentialGeometry.Topology.Homeomorph.JordanAnnulus
import DifferentialGeometry.Topology.PlanarJordan.Transport
import DifferentialGeometry.Topology.PlanarJordan.AmbientExtension
import DifferentialGeometry.Topology.PlanarJordan.CompactRegion
import DifferentialGeometry.Topology.LoopSpace.HomeomorphismOrientation
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

set_option autoImplicit false
noncomputable section
open Set Metric Schoenflies DifferentialGeometry.Topology DifferentialGeometry.Topology.PlanarJordan
namespace GC.LongTime.CuspP1

/-- Standard identification `ℂ ≃ₜ Plane`. -/
def planeHomeo_CPP2 : ℂ ≃ₜ Plane := Complex.orthonormalBasisOneI.repr.toHomeomorph

theorem planeHomeo_norm_CPP2 (z : ℂ) : ‖planeHomeo_CPP2 z‖ = ‖z‖ :=
  Complex.orthonormalBasisOneI.repr.norm_map z

theorem planeHomeo_zero_CPP2 : planeHomeo_CPP2 0 = 0 :=
  map_zero Complex.orthonormalBasisOneI.repr

theorem planeHomeo_symm_ne_zero_CPP2 {x : Plane} (hx : x ≠ 0) : planeHomeo_CPP2.symm x ≠ 0 := by
  intro h
  apply hx
  rw [← planeHomeo_CPP2.apply_symm_apply x, h, planeHomeo_zero_CPP2]

/-- Round circles are Jordan curves. -/
theorem isJordanCurve_sphere_CPP2 {r : ℝ} (hr : 0 < r) : IsJordanCurve (sphere (0 : Plane) r) := by
  have hJ : IsJordanCurve (sphere (0 : Plane) 1) := by
    simpa only [Subtype.range_coe] using isJordanCurve_range_of_isEmbedding_circle
      (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : sphere (0 : Plane) 1 → Plane))
  let s : Plane ≃ₜ Plane := Homeomorph.smulOfNeZero r hr.ne'
  have hs : s '' sphere (0 : Plane) 1 = sphere 0 r := by
    change (r • ·) '' sphere (0 : Plane) 1 = sphere 0 r
    rw [image_smul, smul_sphere' hr.ne']
    simp [abs_of_pos hr]
  exact hs ▸ isJordanCurve_image s hJ

theorem inside_sphere_CPP2 {r : ℝ} (hr : 0 < r) : inside (sphere (0 : Plane) r) = ball 0 r := by
  have hfr := frontier_closedBall (0 : Plane) hr.ne'
  have hi : (interior (closedBall (0 : Plane) r)).Nonempty := by
    rw [interior_closedBall (0 : Plane) hr.ne']
    exact nonempty_ball.mpr hr
  have hh := interior_eq_inside_frontier_of_isCompact
    (isCompact_closedBall (0 : Plane) r) (hfr.symm ▸ isJordanCurve_sphere_CPP2 hr) hi
  simpa only [hfr, interior_closedBall (0 : Plane) hr.ne'] using hh.symm

theorem closure_inside_sphere_CPP2 {r : ℝ} (hr : 0 < r) :
    closure (inside (sphere (0 : Plane) r)) = closedBall 0 r := by
  rw [inside_sphere_CPP2 hr, closure_ball (0 : Plane) hr.ne']

theorem unit_mem_CPP2 {z : ℂ} (hz : z ≠ 0) : z / (‖z‖ : ℂ) ∈ Submonoid.unitSphere ℂ := by
  show z / (‖z‖ : ℂ) ∈ sphere (0 : ℂ) 1
  rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, norm_norm]
  exact div_self (norm_ne_zero_iff.mpr hz)

/-- Unit direction of a complex number (junk value `1` at `0`). -/
def dirOf_CPP2 (z : ℂ) : Circle :=
  if hz : z = 0 then 1 else ⟨z / (‖z‖ : ℂ), unit_mem_CPP2 hz⟩

theorem coe_dirOf_CPP2 {z : ℂ} (hz : z ≠ 0) : (dirOf_CPP2 z : ℂ) = z / (‖z‖ : ℂ) := by
  simp [dirOf_CPP2, hz]

theorem dirOf_mul_CPP2 {r : ℝ} (hr : 0 < r) (c : Circle) : dirOf_CPP2 ((r : ℂ) * c) = c := by
  have hne : (r : ℂ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast hr.ne') c.coe_ne_zero
  apply Circle.ext
  rw [coe_dirOf_CPP2 hne, norm_mul, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_of_nonneg hr.le]
  have : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem continuous_dirOf_comp_CPP2 {X : Type*} [TopologicalSpace X] {f : X → ℂ}
    (hf : Continuous f) (h0 : ∀ x, f x ≠ 0) : Continuous (fun x => dirOf_CPP2 (f x)) := by
  have : (fun x => dirOf_CPP2 (f x)) = fun x =>
      (⟨f x / (‖f x‖ : ℂ), unit_mem_CPP2 (h0 x)⟩ : Circle) := by
    funext x
    apply Circle.ext
    rw [coe_dirOf_CPP2 (h0 x)]
  rw [this]
  refine Continuous.subtype_mk ?_ _
  exact hf.div (Complex.continuous_ofReal.comp hf.norm) (fun x => by
    exact_mod_cast norm_ne_zero_iff.mpr (h0 x))

end GC.LongTime.CuspP1
