import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import Mathlib.Topology.MetricSpace.Isometry

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry.KleinerLottApprox

variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
variable {p : X} {q : Y} {z : Z} {ε δ R : ℝ}

noncomputable def mapTargetBallIsometry (f : KleinerLottApprox p q ε)
    (hR : 0 < R) (e : ball q R ≃ᵢ ball z R)
    (he : (e ⟨q, mem_ball_self hR⟩).val = z)
    (hbudget : 3 * ε ≤ δ) (hδ : δ < 1)
    (hdomain : δ⁻¹ + 2 * ε ≤ ε⁻¹) (hchart : δ⁻¹ + ε < R) :
    KleinerLottApprox p z δ := by
  classical
  have hε := f.error_pos
  have hδ0 : 0 < δ := by linarith
  have hin (x : X) (hx : x ∈ ball p δ⁻¹) : x ∈ ball p ε⁻¹ := by
    change dist x p < _ at hx ⊢
    linarith
  have hchartin (x : X) (hx : x ∈ ball p δ⁻¹) : f.toFun x ∈ ball q R := by
    have hr := (abs_le.mp (f.radial_error x (hin x hx))).2
    change dist x p < _ at hx
    change dist (f.toFun x) q < _
    linarith
  let F : X → Z := fun x => if hx : f.toFun x ∈ ball q R then (e ⟨f.toFun x, hx⟩).val else z
  have hF (x : X) (hx : f.toFun x ∈ ball q R) : F x = (e ⟨f.toFun x, hx⟩).val := by
    simp only [F, dite_eq_left hx]
  have hedist (y : ball q R) : dist (e y).val z = dist y.val q := by
    have h := e.dist_eq y ⟨q, mem_ball_self hR⟩
    change dist (e y).val (e ⟨q, mem_ball_self hR⟩).val = dist y.val q at h
    simpa only [he] using h
  refine ⟨hδ0, hδ, F, ?_, ?_, ?_⟩
  · rw [hF p (by rw [f.basepoint]; exact mem_ball_self hR)]
    simpa only [f.basepoint] using he
  · intro x hx y hy
    rw [hF x (hchartin x hx), hF y (hchartin y hy), ← Subtype.dist_eq, e.dist_eq]
    exact (f.distortion x (hin x hx) y (hin y hy)).trans (by linarith)
  · intro y hy
    have hyR : y ∈ ball z R := by change dist y z < _; linarith
    let y₀ := e.symm ⟨y, hyR⟩
    have hy₀ : dist y₀.val q = dist y z := by
      rw [← hedist y₀]
      simp only [y₀, e.apply_symm_apply]
    obtain ⟨x, hx, hd⟩ := f.coverage_witness y₀.val (by rw [hy₀]; linarith)
    have hr := (abs_le.mp (f.radial_error x hx)).1
    have ht := dist_triangle (f.toFun x) y₀.val q
    rw [dist_comm (f.toFun x) y₀.val, hy₀] at ht
    have hxin : x ∈ ball p δ⁻¹ := by change dist x p < _; linarith
    have hxR := hchartin x hxin
    have htarget : dist y (F x) < 2 * ε := by
      rw [hF x hxR]
      have h := e.dist_eq y₀ ⟨f.toFun x, hxR⟩
      change dist (e y₀).val (e ⟨f.toFun x, hxR⟩).val = dist y₀.val (f.toFun x) at h
      simpa only [y₀, e.apply_symm_apply] using h.trans_lt hd
    exact (infDist_le_dist_of_mem (show F x ∈ F '' ball p δ⁻¹ from ⟨x, hxin, rfl⟩)).trans
      (by linarith)

theorem mapTargetBallIsometry_apply (f : KleinerLottApprox p q ε)
    (hR : 0 < R) (e : ball q R ≃ᵢ ball z R)
    (he : (e ⟨q, mem_ball_self hR⟩).val = z)
    (hbudget : 3 * ε ≤ δ) (hδ : δ < 1)
    (hdomain : δ⁻¹ + 2 * ε ≤ ε⁻¹) (hchart : δ⁻¹ + ε < R)
    (x : X) (hx : f.toFun x ∈ ball q R) :
    (f.mapTargetBallIsometry hR e he hbudget hδ hdomain hchart).toFun x =
      (e ⟨f.toFun x, hx⟩).val := by
  classical
  simp only [mapTargetBallIsometry, dite_eq_left hx]

end GC.MetricGeometry.KleinerLottApprox
