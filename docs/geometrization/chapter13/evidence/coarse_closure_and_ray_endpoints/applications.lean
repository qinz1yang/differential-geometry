import DifferentialGeometry.Geometry.Metric.CoarseClosure
import DifferentialGeometry.Geometry.Metric.Approximation.RayTargetRescaling
import DifferentialGeometry.Geometry.Metric.Approximation.IsometricKleinerLottApproximation
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open Set Metric GC.MetricGeometry

namespace CoarseRayRegression

private noncomputable def jump (x : ℝ) : ℝ := if x = 0 then 1 else 0

theorem closure_retains_the_coarse_defect : jump 0 ≤ 1 ∧ ¬ jump 0 ≤ 0 := by
  have hcoarse (x : ℝ) (_hx : x ∈ (univ : Set ℝ)) (y : ℝ) (_hy : y ∈ (univ : Set ℝ)) :
      |jump x - jump y| ≤ dist x y + 1 := by
    have hb : |jump x - jump y| ≤ 1 := by
      unfold jump
      split_ifs <;> norm_num
    exact hb.trans (by linarith [dist_nonneg (x := x) (y := y)])
  have hh := le_on_closure_of_coarse_bound (s := Iio (0 : ℝ)) (U := univ) isOpen_univ
    (f := jump) (A := 0) (δ := 1)
    (by intro x hx; have hn : x ≠ 0 := ne_of_lt hx.1; simp [jump, hn]) hcoarse
    (x := 0) (by simp)
  exact ⟨by simpa only [zero_add] using hh, by norm_num [jump]⟩

theorem original_border_buffer {X : Type*} [PseudoMetricSpace X]
    {s : Set X} {p x : X} {f : X → ℝ} {Δ τ δ : ℝ} (hΔ : 0 < Δ)
    (hδ : δ < τ * Δ / 2)
    (hsource : ∀ y ∈ s ∩ ball p (191 * Δ), f y < τ * Δ / 2)
    (hcoarse : ∀ y ∈ ball p (191 * Δ), ∀ z ∈ ball p (191 * Δ),
      |f y - f z| ≤ dist y z + δ)
    (hx : x ∈ closure s ∩ ball p (190 * Δ)) : f x < τ * Δ := by
  have hx' : x ∈ closure s ∩ ball p (191 * Δ) :=
    ⟨hx.1, by have hr : dist x p < 190 * Δ := hx.2; change dist x p < 191 * Δ; linarith⟩
  have hh := le_on_closure_of_coarse_bound isOpen_ball (fun y hy => (hsource y hy).le) hcoarse hx'
  linarith

private abbrev Ray := Ici (0 : ℝ)
private noncomputable def oldPoint : Ray := ⟨1 / 10, by norm_num⟩
private noncomputable def newPoint : Ray := ⟨1 / 1000000, by norm_num⟩

private noncomputable def rayMap : KleinerLottApprox oldPoint oldPoint (1 / 1000000) :=
  (IsometryEquiv.refl Ray).toKleinerLottApprox rfl (by norm_num) (by norm_num)

theorem actual_ray_clips_and_repairs :
    let : MetricSpace Ray := (inferInstance : MetricSpace Ray).rescale 1 (by norm_num)
    ∃ g : KleinerLottApprox newPoint (⟨0, by norm_num⟩ : Icc (0 : ℝ) 800) (1 / 200),
      (g.toFun newPoint).val = 0 ∧
      (g.toFun ⟨100, by norm_num⟩).val = 100 ∧
      (g.toFun ⟨1000, by norm_num⟩).val = 800 := by
  have hh := rayMap.exists_strong_edge_ray_model newPoint (Δ := 1) (δ := 1 / 200)
    (e := 1 / 1000000) (θ := 0) (c := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [oldPoint, newPoint, Subtype.dist_eq, Real.dist_eq])
    (by norm_num [oldPoint]) (by norm_num) (by norm_num) (by change (1 / 1000000 : ℝ) ≤ 2 * (1 / 1000000) + 0; norm_num)
  dsimp only at hh
  rw [show max (201 * (1 : ℝ)) (4 / (1 / 200)) = 800 by norm_num] at hh
  let : MetricSpace Ray := (inferInstance : MetricSpace Ray).rescale 1 (by norm_num)
  obtain ⟨hD, g, _, hg, hv⟩ := hh
  refine ⟨g, congrArg Subtype.val hg, ?_, ?_⟩
  · have he := hv ⟨100, by norm_num⟩ (by intro h; have := congrArg Subtype.val h; norm_num [newPoint] at this)
    change _ = min (1 * (100 : ℝ)) 800 at he
    norm_num at he
    exact he
  · have he := hv ⟨1000, by norm_num⟩ (by intro h; have := congrArg Subtype.val h; norm_num [newPoint] at this)
    change _ = min (1 * (1000 : ℝ)) 800 at he
    norm_num at he
    exact he

end CoarseRayRegression

#print axioms CoarseRayRegression.closure_retains_the_coarse_defect

#print axioms CoarseRayRegression.original_border_buffer

#print axioms CoarseRayRegression.actual_ray_clips_and_repairs
