import DifferentialGeometry.Geometry.Comparison.ExpandedIntrinsicEightRadialComparison

set_option autoImplicit false

open Set Metric Real Topology
namespace DifferentialGeometry.Geometry.Comparison.Toponogov

private theorem radial_prefix_mem_three_halves
    {X : Type*} [MetricSpace X] {o q x : X} {R : ℝ}
    (hq : q ∈ ball o (R / 2)) (hx : x ∈ closedBall o R)
    (σ : Icc (0 : ℝ) (dist q x) → X) (hσ : Isometry σ)
    (hσ0 : σ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = q)
    (hσend : σ ⟨dist q x, ⟨dist_nonneg, le_rfl⟩⟩ = x)
    (u : Icc (0 : ℝ) (dist q x)) : σ u ∈ closedBall o (3 * R / 2) := by
  have hrad : dist q (σ u) = u.val := by
    have h := hσ.dist_eq ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ u
    simpa only [hσ0, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg u.property.1] using h
  have htail : dist (σ u) x = dist q x - u.val := by
    have h := hσ.dist_eq u ⟨dist q x, ⟨dist_nonneg, le_rfl⟩⟩
    simpa only [hσend, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr u.property.2), neg_sub] using h
  have hleft := dist_triangle (σ u) q o
  rw [dist_comm (σ u) q, hrad] at hleft
  have hright := dist_triangle (σ u) x o
  rw [htail] at hright
  have hAupper := dist_triangle q o x
  rw [dist_comm o x] at hAupper
  have hqo : dist q o < R / 2 := hq
  have hxo : dist x o ≤ R := hx
  change dist (σ u) o ≤ 3 * R / 2
  linarith

private theorem radial_prefix_cross_dist_le_five_halves
    {X : Type*} [MetricSpace X] {o q x y : X} {R : ℝ}
    (hq : q ∈ ball o (R / 2)) (hx : x ∈ closedBall o R) (hy : y ∈ closedBall o R)
    (γ : Icc (0 : ℝ) (dist q x) → X) (β : Icc (0 : ℝ) (dist q y) → X)
    (hγ : Isometry γ) (hβ : Isometry β)
    (hγ0 : γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = q)
    (hβ0 : β ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = q)
    (hγend : γ ⟨dist q x, ⟨dist_nonneg, le_rfl⟩⟩ = x)
    (hβend : β ⟨dist q y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    (u : Icc (0 : ℝ) (dist q x)) (v : Icc (0 : ℝ) (dist q y)) :
    dist (γ u) (β v) ≤ 5 * R / 2 := by
  have hγrad : dist q (γ u) = u.val := by
    have h := hγ.dist_eq ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ u
    simpa only [hγ0, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg u.property.1] using h
  have hβrad : dist q (β v) = v.val := by
    have h := hβ.dist_eq ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ v
    simpa only [hβ0, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg v.property.1] using h
  have hγtail : dist (γ u) x = dist q x - u.val := by
    have h := hγ.dist_eq u ⟨dist q x, ⟨dist_nonneg, le_rfl⟩⟩
    simpa only [hγend, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr u.property.2), neg_sub] using h
  have hβtail : dist y (β v) = dist q y - v.val := by
    have h := hβ.dist_eq ⟨dist q y, ⟨dist_nonneg, le_rfl⟩⟩ v
    simpa only [hβend, Subtype.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr v.property.2)] using h
  have hfirst := dist_triangle (γ u) q (β v)
  rw [dist_comm (γ u) q, hγrad, hβrad] at hfirst
  have hsecond := dist_triangle (γ u) x (β v)
  have hthird := dist_triangle x y (β v)
  rw [hγtail] at hsecond
  rw [hβtail] at hthird
  have hA := dist_triangle q o x
  have hB := dist_triangle q o y
  have hxy := dist_triangle x o y
  rw [dist_comm o x] at hA
  rw [dist_comm o y] at hB hxy
  have hqo : dist q o < R / 2 := hq
  have hxo : dist x o ≤ R := hx
  have hyo : dist y o ≤ R := hy
  linarith

theorem exists_same_radial_lifts_intrinsic_8_buffer
    {X : Type*} [MetricSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {R : ℝ} (hR : 0 < R)
    {q x y : X} (hq : q ∈ ball o (R / 2))
    (hx : x ∈ closedBall o R) (hy : y ∈ closedBall o R)
    (γ : Icc (0 : ℝ) (dist q x) → X) (β : Icc (0 : ℝ) (dist q y) → X)
    (hγ : Isometry γ) (hβ : Isometry β)
    (hγ0 : γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = q)
    (hβ0 : β ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = q)
    (hγend : γ ⟨dist q x, ⟨dist_nonneg, le_rfl⟩⟩ = x)
    (hβend : β ⟨dist q y, ⟨dist_nonneg, le_rfl⟩⟩ = y) :
    ∃ Γ : Icc (0 : ℝ) (dist q x) → ball o (8 * R),
      ∃ Β : Icc (0 : ℝ) (dist q y) → ball o (8 * R),
        (∀ u, (Γ u : X) = γ u) ∧ (∀ v, (Β v : X) = β v) ∧
        @Isometry (Icc (0 : ℝ) (dist q x)) (ball o (8 * R)) inferInstance
          (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)).toPseudoEMetricSpace Γ ∧
        @Isometry (Icc (0 : ℝ) (dist q y)) (ball o (8 * R)) inferInstance
          (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)).toPseudoEMetricSpace Β ∧
        ∀ u v, @dist (ball o (8 * R))
          (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)).toDist
          (Γ u) (Β v) = dist (γ u) (β v) := by
  have hγmem (u : Icc (0 : ℝ) (dist q x)) : γ u ∈ closedBall o (3 * R / 2) :=
    radial_prefix_mem_three_halves hq hx γ hγ hγ0 hγend u
  have hβmem (v : Icc (0 : ℝ) (dist q y)) : β v ∈ closedBall o (3 * R / 2) :=
    radial_prefix_mem_three_halves hq hy β hβ hβ0 hβend v
  let Γ : Icc (0 : ℝ) (dist q x) → ball o (8 * R) := fun u => ⟨γ u, by
    have hd : dist (γ u) o ≤ 3 * R / 2 := hγmem u
    change dist (γ u) o < 8 * R
    linarith⟩
  let Β : Icc (0 : ℝ) (dist q y) → ball o (8 * R) := fun v => ⟨β v, by
    have hd : dist (β v) o ≤ 3 * R / 2 := hβmem v
    change dist (β v) o < 8 * R
    linarith⟩
  let m := intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)
  have hdist (a b : ball o (8 * R)) (ha : (a : X) ∈ closedBall o (3 * R / 2))
      (hb : (b : X) ∈ closedBall o (3 * R / 2)) : @dist _ m.toDist a b = dist (a : X) (b : X) :=
    intrinsicBall_dist_eq_on_inner_closedBall hcurves o (by positivity) (a := a) (b := b)
      (by positivity : 0 < 3 * R / 2)
      (by rw [dist_self]; linarith : dist o o + 4 * (3 * R / 2) < 8 * R) ha hb
  refine ⟨Γ, Β, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_⟩
  · apply @Isometry.of_dist_eq _ _ inferInstance m.toPseudoMetricSpace
    intro u v
    rw [hdist (Γ u) (Γ v) (hγmem u) (hγmem v)]
    exact hγ.dist_eq u v
  · apply @Isometry.of_dist_eq _ _ inferInstance m.toPseudoMetricSpace
    intro u v
    rw [hdist (Β u) (Β v) (hβmem u) (hβmem v)]
    exact hβ.dist_eq u v
  · intro u v
    exact hdist (Γ u) (Β v) (hγmem u) (hβmem v)

end DifferentialGeometry.Geometry.Comparison.Toponogov


open Set Metric Real Topology
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
variable (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
  ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
    eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
variable (o : X) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
variable [LocallyCompactSpace (ball o (8 * R))]
variable (hlocal : ∀ z : ball o (8 * R), ∃ Ω : Set (ball o (8 * R)),
  @IsOpen (ball o (8 * R))
    (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
  @fourPointComparison (ball o (8 * R))
    (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)) κ Ω ∧ z ∈ Ω)

include hcurves hκ hR hlocal

theorem comparisonAngleNegCurvature_le_of_nested_radial_prefixes_intrinsic_8_buffer
    {q x y : X} (hq : q ∈ ball o (R / 2))
    (hx : x ∈ closedBall o R) (hy : y ∈ closedBall o R)
    (γ : Icc (0 : ℝ) (dist q x) → X) (β : Icc (0 : ℝ) (dist q y) → X)
    (hγ : Isometry γ) (hβ : Isometry β)
    (hγ0 : γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = q)
    (hβ0 : β ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = q)
    (hγend : γ ⟨dist q x, ⟨dist_nonneg, le_rfl⟩⟩ = x)
    (hβend : β ⟨dist q y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    {s t u v : ℝ} (hs : 0 < s) (hsu : s ≤ u) (hu : u ≤ dist q x)
    (ht : 0 < t) (htv : t ≤ v) (hv : v ≤ dist q y) :
    comparisonAngleNegCurvature κ u v
        (dist (γ ⟨u, ⟨hs.le.trans hsu, hu⟩⟩) (β ⟨v, ⟨ht.le.trans htv, hv⟩⟩)) ≤
      comparisonAngleNegCurvature κ s t
        (dist (γ ⟨s, ⟨hs.le, hsu.trans hu⟩⟩) (β ⟨t, ⟨ht.le, htv.trans hv⟩⟩)) := by
  have hu0 : 0 < u := hs.trans_le hsu
  have hv0 : 0 < v := ht.trans_le htv
  let γ' : Icc (0 : ℝ) u → X := fun w => γ ⟨w.val, ⟨w.property.1, w.property.2.trans hu⟩⟩
  let β' : Icc (0 : ℝ) v → X := fun w => β ⟨w.val, ⟨w.property.1, w.property.2.trans hv⟩⟩
  have hγ' : Isometry γ' := hγ.comp (Isometry.of_dist_eq fun _ _ => rfl)
  have hβ' : Isometry β' := hβ.comp (Isometry.of_dist_eq fun _ _ => rfl)
  have hγ'0 : γ' ⟨0, ⟨le_rfl, hu0.le⟩⟩ = q := hγ0
  have hβ'0 : β' ⟨0, ⟨le_rfl, hv0.le⟩⟩ = q := hβ0
  have hγrad (w : Icc (0 : ℝ) u) : dist q (γ' w) = w.val := by
    rw [← hγ'0, hγ'.dist_eq, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg w.property.1]
  have hβrad (w : Icc (0 : ℝ) v) : dist q (β' w) = w.val := by
    rw [← hβ'0, hβ'.dist_eq, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg w.property.1]
  have hγmem (w : Icc (0 : ℝ) u) : γ' w ∈ closedBall o (3 * R / 2) :=
    radial_prefix_mem_three_halves hq hx γ hγ hγ0 hγend _
  have hβmem (w : Icc (0 : ℝ) v) : β' w ∈ closedBall o (3 * R / 2) :=
    radial_prefix_mem_three_halves hq hy β hβ hβ0 hβend _
  have hcross (w : Icc (0 : ℝ) u) (r : Icc (0 : ℝ) v) : dist (γ' w) (β' r) ≤ 5 * R / 2 :=
    radial_prefix_cross_dist_le_five_halves hq hx hy γ β hγ hβ hγ0 hβ0 hγend hβend _ _
  have hfirst := comparisonAngleNegCurvature_le_of_expanded_intrinsic_8_buffer_segment
    hcurves o hκ hR hlocal hu0 γ' hγ' hγmem
    (hβmem ⟨v, ⟨hv0.le, le_rfl⟩⟩)
    (by rw [dist_comm]; exact hcross _ _) (by rw [dist_comm]; exact hcross _ _)
    (by rw [hγ'0]; exact dist_pos.mp (by rw [hβrad]; exact hv0)) ⟨hs, hsu⟩
  rw [hγ'0, hβrad] at hfirst
  have hsecond := comparisonAngleNegCurvature_le_of_expanded_intrinsic_8_buffer_segment
    hcurves o hκ hR hlocal hv0 β' hβ' hβmem
    (hγmem ⟨s, ⟨hs.le, hsu⟩⟩) (hcross _ _) (hcross _ _)
    (by rw [hβ'0]; exact dist_pos.mp (by rw [hγrad]; exact hs)) ⟨ht, htv⟩
  rw [hβ'0, hγrad] at hsecond
  have hsecond' : comparisonAngleNegCurvature κ s v
      (dist (γ' ⟨s, ⟨hs.le, hsu⟩⟩) (β' ⟨v, ⟨hv0.le, le_rfl⟩⟩)) ≤
      comparisonAngleNegCurvature κ s t
      (dist (γ' ⟨s, ⟨hs.le, hsu⟩⟩) (β' ⟨t, ⟨ht.le, htv⟩⟩)) := by
    simpa only [comparisonAngleNegCurvature_comm κ v s,
      comparisonAngleNegCurvature_comm κ t s, dist_comm] using hsecond
  exact hfirst.trans hsecond'

theorem modelSideNegCurvature_le_of_nested_radial_prefixes_intrinsic_8_buffer
    {q x y : X} (hq : q ∈ ball o (R / 2))
    (hx : x ∈ closedBall o R) (hy : y ∈ closedBall o R)
    (γ : Icc (0 : ℝ) (dist q x) → X) (β : Icc (0 : ℝ) (dist q y) → X)
    (hγ : Isometry γ) (hβ : Isometry β)
    (hγ0 : γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = q)
    (hβ0 : β ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = q)
    (hγend : γ ⟨dist q x, ⟨dist_nonneg, le_rfl⟩⟩ = x)
    (hβend : β ⟨dist q y, ⟨dist_nonneg, le_rfl⟩⟩ = y)
    {s t u v : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u) (hu : u ≤ dist q x)
    (ht : 0 ≤ t) (htv : t ≤ v) (hv : v ≤ dist q y) :
    modelSideNegCurvature κ s t
        (comparisonAngleNegCurvature κ u v
          (dist (γ ⟨u, ⟨hs.trans hsu, hu⟩⟩) (β ⟨v, ⟨ht.trans htv, hv⟩⟩))) ≤
      dist (γ ⟨s, ⟨hs, hsu.trans hu⟩⟩) (β ⟨t, ⟨ht, htv.trans hv⟩⟩) := by
  have hγrad (w : Icc (0 : ℝ) (dist q x)) : dist q (γ w) = w.val := by
    have h := hγ.dist_eq ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ w
    simpa only [hγ0, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg w.property.1] using h
  have hβrad (w : Icc (0 : ℝ) (dist q y)) : dist q (β w) = w.val := by
    have h := hβ.dist_eq ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ w
    simpa only [hβ0, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg w.property.1] using h
  by_cases hs0 : s = 0
  · subst s
    rw [hγ0, modelSideNegCurvature_zero_left hκ.le ht, hβrad]
  by_cases ht0 : t = 0
  · subst t
    rw [hβ0, modelSideNegCurvature_zero_right hκ.le hs, dist_comm, hγrad]
  have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hangle := comparisonAngleNegCurvature_le_of_nested_radial_prefixes_intrinsic_8_buffer
    hcurves o hκ hR hlocal hq hx hy γ β hγ hβ hγ0 hβ0 hγend hβend hspos hsu hu htpos htv hv
  have hlo : |s - t| ≤ dist (γ ⟨s, ⟨hs, hsu.trans hu⟩⟩) (β ⟨t, ⟨ht, htv.trans hv⟩⟩) := by
    simpa only [dist_comm _ q, hγrad, hβrad] using
      abs_dist_sub_le (γ ⟨s, ⟨hs, hsu.trans hu⟩⟩) (β ⟨t, ⟨ht, htv.trans hv⟩⟩) q
  have hhi : dist (γ ⟨s, ⟨hs, hsu.trans hu⟩⟩) (β ⟨t, ⟨ht, htv.trans hv⟩⟩) ≤ s + t := by
    simpa only [dist_comm _ q, hγrad, hβrad] using
      dist_triangle (γ ⟨s, ⟨hs, hsu.trans hu⟩⟩) q (β ⟨t, ⟨ht, htv.trans hv⟩⟩)
  calc
    _ ≤ modelSideNegCurvature κ s t
        (comparisonAngleNegCurvature κ s t
          (dist (γ ⟨s, ⟨hs, hsu.trans hu⟩⟩) (β ⟨t, ⟨ht, htv.trans hv⟩⟩))) :=
      modelSideNegCurvature_mono_angle hκ.le hs ht
        (comparisonAngleNegCurvature_mem_Icc _ _ _ _).1
        (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2 hangle
    _ = _ := modelSideNegCurvature_comparisonAngle hκ.le hspos htpos hlo hhi

end DifferentialGeometry.Geometry.Comparison.Toponogov
