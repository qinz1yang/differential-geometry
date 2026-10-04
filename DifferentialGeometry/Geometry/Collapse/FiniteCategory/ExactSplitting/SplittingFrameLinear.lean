import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingFrame
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.CoerciveBilinearInverse

/-!
# The linear frame of an exact metric splitting

The Riesz inverse of the actual metric applied to the coordinate differential yields the
canonical lifted coordinate directions. Its pairing, right inverse and exponential identities
retain the original metric splitting map.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set WithLp
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.ExactSplitting

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M] {r : ℕ∞}
  {F Y : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace Y]

local instance frameModelComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [I.Boundaryless] [IsRiemannianManifold I M] [CompleteSpace M] in
private theorem frameMetricCoercive
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (x : M) : IsCoercive (g.inner x : E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.isCoercive_of_posDef (g.inner x) (fun w hw => g.pos x w hw)

def splittingFrame
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) : F →L[ℝ] TangentSpace I x :=
  (tangentSpaceCastModel I x).symm.toContinuousLinearMap.comp
    ((frameMetricCoercive g x).sharpCLM.comp
      (((ContinuousLinearMap.compL ℝ E F ℝ).flip
        (mvfderiv I (fun y => (e y).fst) x : E →L[ℝ] F)).comp (innerSL ℝ)))

omit [FiniteDimensional ℝ F] [I.Boundaryless]
  [IsRiemannianManifold I M] [CompleteSpace M] in
theorem inner_splittingFrame_left
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) (u : F) (w : TangentSpace I x) :
    g.inner x (splittingFrame g e x u) w = inner ℝ u (mvfderiv I (fun y => (e y).fst) x w) := by
  change (g.inner x : E →L[ℝ] E →L[ℝ] ℝ)
    ((frameMetricCoercive g x).sharp
      ((innerSL ℝ u).comp (mvfderiv I (fun y => (e y).fst) x : E →L[ℝ] F))) w = _
  rw [(frameMetricCoercive g x).apply_sharp]
  rfl

omit [FiniteDimensional ℝ E] in
private theorem pairing_eq_zero_of_nonnegative
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hs : ∀ v w : E, B v w = B w v)
    (hn : ∀ v : E, 0 ≤ B v v) {x : E} (hx : B x x = 0) (y : E) : B x y = 0 := by
  let a := B x y
  let b := B y y
  have hb : 0 ≤ b := hn y
  have hd : b + 1 ≠ 0 := by positivity
  have ht := hn (x - (a / (b + 1)) • y)
  have he : B (x - (a / (b + 1)) • y) (x - (a / (b + 1)) • y) =
      -2 * a ^ 2 / (b + 1) + a ^ 2 * b / (b + 1) ^ 2 := by
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, hx, hs y x]
    change 0 - a / (b + 1) * a - a / (b + 1) * (a - a / (b + 1) * b) = _
    field_simp [hd]
    ring
  rw [he] at ht
  have hm := mul_nonneg ht (sq_nonneg (b + 1))
  have hc : (-2 * a ^ 2 / (b + 1) + a ^ 2 * b / (b + 1) ^ 2) * (b + 1) ^ 2 =
      -(b + 2) * a ^ 2 := by
    field_simp
    ring
  rw [hc] at hm
  have ha : a ^ 2 = 0 := by
    by_contra hne
    have hpos : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm hne)
    have hp := mul_pos (show 0 < b + 2 by linarith) hpos
    linarith
  exact sq_eq_zero_iff.mp ha

private theorem frame_eq_unit_lift [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) {u : F} (hu : ‖u‖ = 1) :
    ∃ w : E, g.inner x w w = 1 ∧ mvfderiv I (fun y => (e y).fst) x w = u ∧
      (splittingFrame g e x u : E) = w := by
  obtain ⟨w, hw, hD, hline⟩ := exists_unit_line_expMap_forall g hr hnorm e x hu
  let G : E →L[ℝ] E →L[ℝ] ℝ := g.inner x
  let D : E →L[ℝ] F := mvfderiv I (fun y => (e y).fst) x
  let P : E →L[ℝ] E →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ E F ℝ).flip D).comp
      ((innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ).comp D)
  let B : E →L[ℝ] E →L[ℝ] ℝ := G - P
  have hs : ∀ v z : E, B v z = B z v := by
    intro v z
    change G v z - inner ℝ (D v) (D z) = G z v - inner ℝ (D z) (D v)
    rw [real_inner_comm]
    exact congrArg (fun a => a - inner ℝ (D z) (D v)) (g.symm x v z)
  have hn : ∀ v : E, 0 ≤ B v v := by
    intro v
    have hle := norm_mvfderiv_splitting_fst_le g hr hnorm e x v
    have hsq := mul_self_le_mul_self (norm_nonneg _) hle
    rw [Real.mul_self_sqrt (g.inner_self_nonneg' x v)] at hsq
    change 0 ≤ G v v - inner ℝ (D v) (D v)
    rw [real_inner_self_eq_norm_sq]
    change ‖D v‖ * ‖D v‖ ≤ G v v at hsq
    nlinarith only [hsq]
  have hw0 : B w w = 0 := by
    change g.inner x w w - inner ℝ (mvfderiv I (fun y => (e y).fst) x w)
      (mvfderiv I (fun y => (e y).fst) x w) = 0
    rw [hw, hD, real_inner_self_eq_norm_sq, hu]
    norm_num
  have hp : ∀ v : E, g.inner x w v = inner ℝ u (D v) := by
    intro v
    have h := pairing_eq_zero_of_nonnegative hs hn hw0 v
    change G w v - inner ℝ (D w) (D v) = 0 at h
    change D w = u at hD
    rw [hD] at h
    exact sub_eq_zero.mp h
  refine ⟨w, hw, hD, ?_⟩
  apply (frameMetricCoercive g x).bilin_injective
  apply ContinuousLinearMap.ext
  intro v
  exact (inner_splittingFrame_left g e x u v).trans (hp v).symm

theorem mvfderiv_splittingFrame [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) (u : F) :
    mvfderiv I (fun y => (e y).fst) x (splittingFrame g e x u) = u := by
  let D : E →L[ℝ] F := mvfderiv I (fun y => (e y).fst) x
  let X : F →L[ℝ] E := splittingFrame g e x
  have hunit : ∀ v : F, ‖v‖ = 1 → D (X v) = v := by
    intro v hv
    obtain ⟨w, hw, hD, hX⟩ := frame_eq_unit_lift g hr hnorm e x hv
    change X v = w at hX
    rw [hX]
    exact hD
  change D (X u) = u
  by_cases hu : u = 0
  · rw [hu, map_zero, map_zero]
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hv : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
  have hrepr : ‖u‖ • (‖u‖⁻¹ • u) = u := by rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
  nth_rw 1 [← hrepr]
  rw [map_smul, map_smul, hunit _ hv, hrepr]

theorem inner_splittingFrame [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) (u v : F) :
    g.inner x (splittingFrame g e x u) (splittingFrame g e x v) = inner ℝ u v := by
  rw [inner_splittingFrame_left, mvfderiv_splittingFrame g hr hnorm]

theorem expMap_splittingFrame [NeZero (Module.finrank ℝ E)]
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (e : M ≃ᵢ WithLp 2 (F × Y)) (x : M) (u : F) (s : ℝ) :
    g.expMap (⟨x, s • splittingFrame g e x u⟩ : TangentBundle I M) =
      e.symm (toLp 2 ((e x).fst + s • u, (e x).snd)) := by
  let X : F →L[ℝ] E := splittingFrame g e x
  have hexp : ∀ v : F, g.expMap (⟨x, X v⟩ : TangentBundle I M) =
      e.symm (toLp 2 ((e x).fst + v, (e x).snd)) := by
    intro v
    by_cases hv : v = 0
    · subst v
      simp only [map_zero, add_zero]
      erw [g.expMap_zero (one_le_two.trans hr)]
      exact (e.symm_apply_apply x).symm
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    let v₀ : F := ‖v‖⁻¹ • v
    have hv₀ : ‖v₀‖ = 1 := by
      dsimp only [v₀]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn]
    obtain ⟨w, hw, hD, hline⟩ := exists_unit_line_expMap_forall g hr hnorm e x hv₀
    have hXunit : g.inner x (X v₀) (X v₀) = 1 := by
      have h := inner_splittingFrame g hr hnorm e x v₀ v₀
      change g.inner x (X v₀) (X v₀) = inner ℝ v₀ v₀ at h
      erw [h]
      rw [real_inner_self_eq_norm_sq, hv₀]
      norm_num
    have hDX : mvfderiv I (fun y => (e y).fst) x (X v₀) = v₀ :=
      mvfderiv_splittingFrame g hr hnorm e x v₀
    have hXeq : X v₀ = w := eq_of_mvfderiv_splitting_fst_eq g hr hnorm e x
      hv₀ hXunit hw hDX hD
    have hrepr : ‖v‖ • v₀ = v := by
      dsimp only [v₀]
      rw [smul_smul, mul_inv_cancel₀ hn, one_smul]
    have h := hline ‖v‖ (norm_nonneg _)
    rw [← hXeq] at h
    have hscale : ‖v‖ • X v₀ = X v := by rw [← map_smul, hrepr]
    erw [hscale] at h
    rw [hrepr] at h
    exact h
  have h := hexp (s • u)
  have hscale : X (s • u) = s • X u := map_smul X s u
  erw [hscale] at h
  exact h

end DifferentialGeometry.Geometry.ExactSplitting
