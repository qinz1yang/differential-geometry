import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.InsertionMetric
import DifferentialGeometry.Geometry.Metric.InterpolationNorm
import DifferentialGeometry.Geometry.Metric.ReferenceNormComparison
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Flat
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Bundle TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance (O : Opens (S2 × ℝ)) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC O.isOpen)
private local instance (O : Opens E3) : SigmaCompactSpace O :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) O.isOpen)

private theorem fixed_collar_le_old {A B T : ℝ} (hAB : 2 * A < B) (hTB : T < B) :
    insertionCylinder A T ≤ DifferentialGeometry.Geometry.Neck.openCylinder B := by
  intro q hq
  change -2 * A < q.2 ∧ q.2 < T at hq
  change -B < q.2 ∧ q.2 < B
  constructor <;> linarith [hq.1, hq.2]

private theorem fixed_collar_le_collar {A B T : ℝ} (hTB : T < B) :
    insertionCylinder A T ≤ insertionCylinder A B := by
  intro q hq
  exact ⟨hq.1, lt_trans hq.2 (by linarith)⟩

private theorem fixed_annulus_le_ball {A B T : ℝ} (hT : 0 ≤ T) (hTB : T < B) :
    insertionAnnulus A T ≤ insertionBall B := by
  intro x hx
  change ‖x‖ < transitionEnd + B
  have hu := hx.2
  rw [conformalRadius_cylindrical hT] at hu
  linarith

private theorem inner_le_ball {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    insertionInner A ≤ insertionBall B :=
  le_trans le_sup_left (le_of_eq (insertionInner_sup_annulus hA hAB))

private def collarReference (A T : ℝ) : SmoothRiemannianMetric IC (insertionCylinder A T) :=
  (roundCylinderMetric (E := E3) (n := 2)).restrictOpen (insertionCylinder A T)

private def collarFactor (A T : ℝ) (q : insertionCylinder A T) : ℝ := conformalFactor q.val.2
private theorem smooth_collarFactor (A T : ℝ) : ContMDiff IC 𝓘(ℝ) ∞ (collarFactor A T) :=
  contDiff_conformalFactor.contMDiff.comp
    (contMDiff_snd.comp (contMDiff_subtype_val (U := insertionCylinder A T)))

private def collarCutoff (A T : ℝ) (q : insertionCylinder A T) : ℝ := insertionCutoff A q.val.2
private theorem smooth_collarCutoff (A T : ℝ) : ContMDiff IC 𝓘(ℝ) ∞ (collarCutoff A T) := by
  have hc : ContDiff ℝ ∞ (insertionCutoff A) := by unfold insertionCutoff; fun_prop
  exact hc.contMDiff.comp
    (contMDiff_snd.comp (contMDiff_subtype_val (U := insertionCylinder A T)))
private theorem collarCutoff_mem (A T : ℝ) (q : insertionCylinder A T) :
    collarCutoff A T q ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private def collarCap (A T : ℝ) : SmoothRiemannianMetric IC (insertionCylinder A T) :=
  conformalMetricOfContDiff (collarReference A T) (collarFactor A T) (smooth_collarFactor A T)

private def collarInterpolation {A B T η : ℝ}
    (hAB : 2 * A < B) (hTB : T < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    SmoothRiemannianMetric IC (insertionCylinder A T) :=
  conformalMetricOfContDiff
    ((h.restrictOpenOfSubset (fixed_collar_le_old hAB hTB)).convexComb
      (scaleMetric η hη (collarReference A T)) (collarCutoff A T)
      (smooth_collarCutoff A T) (collarCutoff_mem A T))
    (collarFactor A T) (smooth_collarFactor A T)

private theorem pullback_cap_fixed_collar (A T : ℝ) :
    Diffeomorph.pullbackMetricCross (metric.restrictOpen (insertionAnnulus A T))
      (insertionChart A T) = collarCap A T := by
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
    collarCap, conformalMetricOfContDiff_inner, collarReference, SmoothRiemannianMetric.restrictOpen_inner]
  have hm := congrArg₂ (fun v w : E3 => metric.inner (conformalMap q.val) v w)
    (conformalChart_mfderiv_eq_ambient q.val v) (conformalChart_mfderiv_eq_ambient q.val w)
  have hp := hm.symm.trans (conformalChart_metric_inner_exp q.val v w)
  simpa only [insertionChart_apply, insertionChart_mfderiv, collarFactor] using! hp

private theorem pullback_inserted_fixed_collar {A B T η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hT : 0 ≤ T) (hTB : T < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    Diffeomorph.pullbackMetricCross
      ((insertedMetric hA hAB hη h).restrictOpenOfSubset (fixed_annulus_le_ball hT hTB))
      (insertionChart A T) = collarInterpolation hAB hTB hη h := by
  apply SmoothRiemannianMetric.ext_inner
  intro q v w
  rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictSubset_inner,
    collarInterpolation, conformalMetricOfContDiff_inner, convexComb_inner,
    SmoothRiemannianMetric.restrictSubset_inner, scaleMetric_inner,
    collarReference, SmoothRiemannianMetric.restrictOpen_inner]
  have hp := insertedMetric_interpolation hA hAB hη h
    (Opens.inclusion (fixed_collar_le_collar hTB) q) v w
  erw [insertionMap_mfderiv hA hAB (Opens.inclusion (fixed_collar_le_collar hTB) q) v,
    insertionMap_mfderiv hA hAB (Opens.inclusion (fixed_collar_le_collar hTB) q) w] at hp
  simpa only [insertionChart_mfderiv, collarFactor, collarCutoff, smul_eq_mul, mul_assoc] using! hp

private theorem collar_norm_eq_ball {A B T η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hT : 0 ≤ T) (hTB : T < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (j : ℕ) (q : insertionCylinder A T) :
    metricDerivNorm j (collarInterpolation hAB hTB hη h) (collarCap A T) (collarCap A T) q =
      metricDerivNorm j (insertedMetric hA hAB hη h)
        (metric.restrictOpen (insertionBall B)) (metric.restrictOpen (insertionBall B))
        (Opens.inclusion (fixed_annulus_le_ball hT hTB) (insertionChart A T q)) := by
  have hp := metricDerivNorm_pullbackCross
    ((insertedMetric hA hAB hη h).restrictOpenOfSubset (fixed_annulus_le_ball hT hTB))
    ((metric.restrictOpen (insertionBall B)).restrictOpenOfSubset (fixed_annulus_le_ball hT hTB))
    ((metric.restrictOpen (insertionBall B)).restrictOpenOfSubset (fixed_annulus_le_ball hT hTB))
    (insertionChart A T) j q
  rw [metricDerivNorm_flat, SmoothRiemannianMetric.restrictOpen_flat,
    pullback_inserted_fixed_collar hA hAB hT hTB hη h, pullback_cap_fixed_collar A T] at hp
  exact hp

private theorem pullback_inner_eq_scale {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    (insertedMetric hA hAB hη h).restrictOpenOfSubset (inner_le_ball hA hAB) =
      scaleMetric η hη (metric.restrictOpen (insertionInner A)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [SmoothRiemannianMetric.restrictSubset_inner, scaleMetric_inner,
    SmoothRiemannianMetric.restrictOpen_inner]
  exact insertedMetric_inner_of_inner hA hAB hη h
    (Opens.inclusion (inner_le_ball hA hAB) x) x.property v w

private theorem inner_norm {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (j : ℕ) (x : insertionBall B) (hx : ‖(x : E3)‖ < conformalRadius (-7 * A / 4)) :
    metricDerivNorm j (insertedMetric hA hAB hη h)
      (metric.restrictOpen (insertionBall B)) (metric.restrictOpen (insertionBall B)) x =
      if j = 0 then |η - 1| * Real.sqrt 3 else 0 := by
  let y : insertionInner A := ⟨x.val, hx⟩
  have hp := metricDerivNorm_flat (inner_le_ball hA hAB)
    (insertedMetric hA hAB hη h) (metric.restrictOpen (insertionBall B))
    (metric.restrictOpen (insertionBall B)) j y
  rw [pullback_inner_eq_scale, SmoothRiemannianMetric.restrictOpen_flat,
    metricDerivNorm_scaleMetric_self] at hp
  simpa [E3, y] using hp.symm

private def outerBand (A D T : ℝ) : Set (insertionCylinder A T) :=
  {q | q.val.2 ∈ Icc (-7 * A / 4) D}

private theorem compact_outerBand {A D T : ℝ} (hA : 0 < A) (hDT : D < T) : IsCompact (outerBand A D T) := by
  rw [Subtype.isCompact_iff]
  have himage : Subtype.val '' outerBand A D T = (univ : Set S2) ×ˢ Icc (-7 * A / 4) D := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨mem_univ _, hp⟩
    · intro hq
      have hu : q ∈ insertionCylinder A T := by
        change -2 * A < q.2 ∧ q.2 < T
        constructor <;> linarith [hq.2.1, hq.2.2]
      exact ⟨⟨q, hu⟩, hq.2, rfl⟩
  rw [himage]
  exact isCompact_univ.prod isCompact_Icc

private theorem original_error_bound {A B D T : ℝ} (hA : 0 < A) (hAB : 2 * A < B) (hTB : T < B)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) (k : ℕ) :
    metricDerivENormSupOn (outerBand A D T) k
      (h.restrictOpenOfSubset (fixed_collar_le_old hAB hTB)) (collarReference A T) (collarReference A T) ≤
    metricDerivENormSupOn {q : DifferentialGeometry.Geometry.Neck.openCylinder B | q.val.2 ∈ Icc (-2 * A) D} k h
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B))
      ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B)) := by
  apply (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
  intro j hj q hq
  have hn := metricDerivNorm_flat (fixed_collar_le_old hAB hTB) h
    ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B))
    ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B)) j q
  rw [SmoothRiemannianMetric.restrictOpen_flat] at hn
  rw [show collarReference A T = (roundCylinderMetric (E := E3) (n := 2)).restrictOpen
    (insertionCylinder A T) from rfl, hn]
  apply ofReal_metricDerivNorm_le_sup _ k _ _ _ hj
  change -2 * A ≤ q.val.2 ∧ q.val.2 ≤ D
  exact ⟨by linarith [hq.1], hq.2⟩

private theorem exists_insertedMetric_error_bound_of_lt (A : ℝ) (hA : 0 < A) (D T : ℝ) (hT : 0 ≤ T) (hDT : D < T) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ) (hAB : 2 * A < B), T < B → ∀ (η : ℝ) (hη : 0 < η)
      (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)),
    metricDerivENormSupOn {x : insertionBall B | ‖(x : E3)‖ ≤ conformalRadius D} k
      (insertedMetric hA hAB hη h) (metric.restrictOpen (insertionBall B))
      (metric.restrictOpen (insertionBall B)) ≤
    ENNReal.ofReal C *
      (metricDerivENormSupOn {q : DifferentialGeometry.Geometry.Neck.openCylinder B | q.val.2 ∈ Icc (-2 * A) D} k h
        ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B))
        ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B)) +
      ENNReal.ofReal |η - 1|) := by
  obtain ⟨Ci, hCi, hi⟩ := exists_metricDerivENormSupOn_conformal_convexComb_bound
    (collarReference A T) (collarReference A T) (collarFactor A T) (smooth_collarFactor A T)
    (collarCutoff A T) (smooth_collarCutoff A T) (collarCutoff_mem A T) (compact_outerBand hA hDT) k
  obtain ⟨Cr, hCr, hr⟩ := exists_metricDerivENormSupOn_reference_comparison
    (collarReference A T) (collarCap A T) (compact_outerBand hA hDT) k
  let C : ℝ := max (Cr * Ci) (Real.sqrt 3)
  have hC : 0 < C := (mul_pos hCr hCi).trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro B hAB hTB η hη h
  let N := metricDerivENormSupOn
    {q : DifferentialGeometry.Geometry.Neck.openCylinder B | q.val.2 ∈ Icc (-2 * A) D} k h
    ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B))
    ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B))
  have houter : metricDerivENormSupOn (outerBand A D T) k
      (collarInterpolation hAB hTB hη h) (collarCap A T) (collarCap A T) ≤
      ENNReal.ofReal C * (N + ENNReal.ofReal |η - 1|) := by
    have hi' := hi (h.restrictOpenOfSubset (fixed_collar_le_old hAB hTB)) η hη
    have hr' := hr (collarInterpolation hAB hTB hη h) (collarCap A T)
    change metricDerivENormSupOn (outerBand A D T) k
      (collarInterpolation hAB hTB hη h) (collarCap A T) (collarReference A T) ≤ _ at hi'
    calc
      _ ≤ ENNReal.ofReal Cr * (ENNReal.ofReal Ci *
          (metricDerivENormSupOn (outerBand A D T) k
            (h.restrictOpenOfSubset (fixed_collar_le_old hAB hTB))
            (collarReference A T) (collarReference A T) + ENNReal.ofReal |η - 1|)) :=
        hr'.trans (by gcongr)
      _ ≤ ENNReal.ofReal Cr * (ENNReal.ofReal Ci * (N + ENNReal.ofReal |η - 1|)) := by
        gcongr
        exact original_error_bound hA hAB hTB h k
      _ = ENNReal.ofReal (Cr * Ci) * (N + ENNReal.ofReal |η - 1|) := by
        rw [ENNReal.ofReal_mul hCr.le, mul_assoc]
      _ ≤ _ := by gcongr; exact le_max_left _ _
  apply (metricDerivENormSupOn_le_iff _ _ _ _ _ _).mpr
  intro j hj x hx
  by_cases hinner : ‖(x : E3)‖ < conformalRadius (-7 * A / 4)
  · rw [inner_norm hA hAB hη h j x hinner]
    by_cases hj0 : j = 0
    · rw [ite_eq_left hj0, ENNReal.ofReal_mul (abs_nonneg _), mul_comm]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _))
        (le_add_of_nonneg_left (by positivity))
    · rw [ite_eq_right hj0, ENNReal.ofReal_zero]
      exact bot_le
  · have hxlow : conformalRadius (-2 * A) < ‖(x : E3)‖ :=
      (strictMono_conformalRadius (by linarith : -2 * A < -7 * A / 4)).trans_le (not_lt.mp hinner)
    have hxhigh : ‖(x : E3)‖ < conformalRadius T :=
      hx.trans_lt (strictMono_conformalRadius hDT)
    let y : insertionAnnulus A T := ⟨x.val, hxlow, hxhigh⟩
    let q : insertionCylinder A T := (insertionChart A T).symm y
    have hv : conformalMap q.val = x.val := by
      exact congrArg Subtype.val ((insertionChart A T).apply_symm_apply y)
    have hn : conformalRadius q.val.2 = ‖(x : E3)‖ := by
      rw [← conformalMap_norm, hv]
    have hq : q ∈ outerBand A D T := by
      constructor
      · apply strictMono_conformalRadius.le_iff_le.mp
        rw [hn]
        exact not_lt.mp hinner
      · apply strictMono_conformalRadius.le_iff_le.mp
        rw [hn]
        exact hx
    have he : Opens.inclusion (fixed_annulus_le_ball hT hTB) (insertionChart A T q) = x :=
      Subtype.ext hv
    have hpoint := ofReal_metricDerivNorm_le_sup (outerBand A D T) k
      (collarInterpolation hAB hTB hη h) (collarCap A T) (collarCap A T) hj hq
    rw [collar_norm_eq_ball hA hAB hT hTB hη h j q, he] at hpoint
    exact hpoint.trans houter

theorem exists_insertedMetric_core_error_bound (A : ℝ) (hA : 0 < A) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ) (hAB : 2 * A < B) (η : ℝ) (hη : 0 < η)
      (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)),
    metricDerivENormSupOn {x : insertionBall B | ‖(x : E3)‖ ≤ conformalRadius (-A)} k
      (insertedMetric hA hAB hη h) (metric.restrictOpen (insertionBall B))
      (metric.restrictOpen (insertionBall B)) ≤
    ENNReal.ofReal C *
      (metricDerivENormSupOn {q : DifferentialGeometry.Geometry.Neck.openCylinder B | q.val.2 ∈ Icc (-2 * A) (-A)} k h
        ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B))
        ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B)) +
      ENNReal.ofReal |η - 1|) := by
  obtain ⟨C, hC, hb⟩ := exists_insertedMetric_error_bound_of_lt A hA (-A) 0
    (le_refl 0) (by linarith) k
  refine ⟨C, hC, ?_⟩
  intro B hAB η hη h
  exact hb B hAB (by linarith) η hη h

theorem exists_insertedMetric_ball_error_bound (A : ℝ) (hA : 0 < A) (D : ℝ) (hD : 0 ≤ D) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : ℝ) (hAB : 2 * A < B), D + 1 < B → ∀ (η : ℝ) (hη : 0 < η)
      (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)),
    metricDerivENormSupOn {x : insertionBall B | ‖(x : E3)‖ ≤ transitionEnd + D} k
      (insertedMetric hA hAB hη h) (metric.restrictOpen (insertionBall B))
      (metric.restrictOpen (insertionBall B)) ≤
    ENNReal.ofReal C *
      (metricDerivENormSupOn {q : DifferentialGeometry.Geometry.Neck.openCylinder B | q.val.2 ∈ Icc (-2 * A) D} k h
        ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B))
        ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (DifferentialGeometry.Geometry.Neck.openCylinder B)) +
      ENNReal.ofReal |η - 1|) := by
  simpa only [conformalRadius_cylindrical hD] using
    exists_insertedMetric_error_bound_of_lt A hA D (D + 1) (by linarith) (by linarith) k

end DifferentialGeometry.PDE.RicciFlow.StandardCap
