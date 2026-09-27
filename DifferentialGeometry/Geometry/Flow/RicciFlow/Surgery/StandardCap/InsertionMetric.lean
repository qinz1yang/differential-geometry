import DifferentialGeometry.Geometry.Neck.PointwiseChart
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.ConformalChart
import DifferentialGeometry.Geometry.Metric.Gluing
import DifferentialGeometry.Geometry.Metric.Conformal.Basic
import DifferentialGeometry.Geometry.Metric.Construction.ConvexCombination
import DifferentialGeometry.Geometry.Metric.Pullback.Cross
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff
import DifferentialGeometry.Geometry.Metric.RoundCylinder

set_option autoImplicit false
noncomputable section
open Set Bundle TopologicalSpace Manifold DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

def insertionCylinder (A B : ℝ) : Opens (S2 × ℝ) :=
  ⟨{q | q.2 ∈ Ioo (-2 * A) B}, isOpen_Ioo.preimage continuous_snd⟩

def insertionAnnulus (A B : ℝ) : Opens E3 :=
  ⟨{x | conformalRadius (-2 * A) < ‖x‖ ∧ ‖x‖ < conformalRadius B},
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)⟩

def insertionInner (A : ℝ) : Opens E3 :=
  ⟨{x | ‖x‖ < conformalRadius (-7 * A / 4)}, isOpen_lt continuous_norm continuous_const⟩

def insertionBall (B : ℝ) : Opens E3 :=
  ⟨{x | ‖x‖ < transitionEnd + B}, isOpen_lt continuous_norm continuous_const⟩

private theorem insertionCylinder_le_original {A B : ℝ} (hAB : 2 * A < B) :
    insertionCylinder A B ≤ DifferentialGeometry.Geometry.Neck.openCylinder B := by
  intro q hq
  change -2 * A < q.2 ∧ q.2 < B at hq
  change -B < q.2 ∧ q.2 < B
  exact ⟨by linarith [hq.1], hq.2⟩

private theorem insertionAnnulus_le_punctured (A B : ℝ) :
    insertionAnnulus A B ≤ puncturedSpace := by
  intro x hx
  apply norm_pos_iff.mp
  exact (conformalRadius_pos (-2 * A)).trans hx.1

private theorem insertionChart_forward_mem (A B : ℝ) (q : insertionCylinder A B) :
    conformalMap q.val ∈ insertionAnnulus A B := by
  change conformalRadius (-2 * A) < ‖conformalMap q.val‖ ∧
    ‖conformalMap q.val‖ < conformalRadius B
  rw [conformalMap_norm]
  exact ⟨strictMono_conformalRadius q.property.1, strictMono_conformalRadius q.property.2⟩

private theorem insertionChart_inverse_mem (A B : ℝ) (x : insertionAnnulus A B) :
    conformalChart.symm (Opens.inclusion (insertionAnnulus_le_punctured A B) x) ∈
      insertionCylinder A B := by
  have hn := conformalChart_norm
    (conformalChart.symm (Opens.inclusion (insertionAnnulus_le_punctured A B) x))
  rw [conformalChart.apply_symm_apply] at hn
  change -2 * A < (conformalChart.symm _).2 ∧ (conformalChart.symm _).2 < B
  constructor
  · apply strictMono_conformalRadius.lt_iff_lt.mp
    rw [← hn]
    exact x.property.1
  · apply strictMono_conformalRadius.lt_iff_lt.mp
    rw [← hn]
    exact x.property.2

def insertionChart (A B : ℝ) :
    insertionCylinder A B ≃ₘ⟮IC, 𝓡 3⟯ insertionAnnulus A B where
  toFun q := ⟨conformalMap q.val, insertionChart_forward_mem A B q⟩
  invFun x := ⟨conformalChart.symm (Opens.inclusion (insertionAnnulus_le_punctured A B) x),
    insertionChart_inverse_mem A B x⟩
  left_inv q := by
    apply Subtype.ext
    exact conformalChart.symm_apply_apply q.val
  right_inv x := by
    apply Subtype.ext
    exact congrArg (fun y : puncturedSpace => (y : E3))
      (conformalChart.apply_symm_apply (Opens.inclusion (insertionAnnulus_le_punctured A B) x))
  contMDiff_toFun _ := codRestr_contMDiffAt
    (insertionChart_forward_mem A B)
    (conformalMap_smooth.comp (contMDiff_subtype_val (U := insertionCylinder A B))).contMDiffAt
  contMDiff_invFun _ := codRestr_contMDiffAt
    (insertionChart_inverse_mem A B)
    (conformalChart.symm.contMDiff.comp
      (contMDiff_inclusion (insertionAnnulus_le_punctured A B))).contMDiffAt

theorem insertionChart_apply (A B : ℝ) (q : insertionCylinder A B) :
    (insertionChart A B q : E3) = conformalMap q.val := rfl

theorem image_conformalMap_insertionCylinder (A B : ℝ) :
    conformalMap '' (insertionCylinder A B : Set (S2 × ℝ)) = (insertionAnnulus A B : Set E3) := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact insertionChart_forward_mem A B ⟨q, hq⟩
  · intro hx
    obtain ⟨q, hq⟩ := (insertionChart A B).surjective ⟨x, hx⟩
    exact ⟨q.val, q.property, congrArg Subtype.val hq⟩

theorem insertionChart_mfderiv (A B : ℝ) (q : insertionCylinder A B)
    (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (insertionChart A B) q v =
      mfderiv IC (𝓡 3) conformalMap q.val v := by
  have hleft := mfderiv_comp q
    ((contMDiff_subtype_val (I := 𝓡 3) (U := insertionAnnulus A B)).mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((insertionChart A B).contMDiff.mdifferentiableAt (by decide))
  have hright := mfderiv_comp q
    (conformalMap_smooth.mdifferentiableAt (by decide))
    ((contMDiff_subtype_val (I := IC) (U := insertionCylinder A B)).mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0))
  have h := hleft.symm.trans hright
  rw [mfderiv_subtype_val, mfderiv_subtype_val] at h
  exact congrArg (fun D => D v) h

theorem insertionInner_sup_annulus {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    insertionInner A ⊔ insertionAnnulus A B = insertionBall B := by
  have hB : 0 < B := by linarith
  have hlow : conformalRadius (-2 * A) < conformalRadius (-7 * A / 4) :=
    strictMono_conformalRadius (by linarith)
  have hhigh : conformalRadius (-7 * A / 4) < conformalRadius B :=
    strictMono_conformalRadius (by linarith)
  ext x
  change (‖x‖ < conformalRadius (-7 * A / 4) ∨
    conformalRadius (-2 * A) < ‖x‖ ∧ ‖x‖ < conformalRadius B) ↔
      ‖x‖ < transitionEnd + B
  rw [← conformalRadius_cylindrical hB.le]
  constructor
  · rintro (hx | hx)
    · exact hx.trans hhigh
    · exact hx.2
  · intro hx
    by_cases hi : ‖x‖ < conformalRadius (-7 * A / 4)
    · exact Or.inl hi
    · exact Or.inr ⟨hlow.trans_le (not_lt.mp hi), hx⟩

def insertionCutoff (A z : ℝ) : ℝ := Real.smoothTransition (2 * (z + 7 * A / 4) / A)

private theorem contDiff_insertionCutoff (A : ℝ) : ContDiff ℝ ∞ (insertionCutoff A) := by
  unfold insertionCutoff
  fun_prop

private theorem insertionCutoff_zero {A z : ℝ} (hA : 0 < A) (hz : z ≤ -7 * A / 4) :
    insertionCutoff A z = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hA.le

private theorem insertionCutoff_one {A z : ℝ} (hA : 0 < A) (hz : -5 * A / 4 ≤ z) :
    insertionCutoff A z = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ hA).mpr
  linarith

private theorem insertionCutoff_mem (A z : ℝ) : insertionCutoff A z ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

private theorem smooth_cutoff_collar (A B : ℝ) :
    ContMDiff IC 𝓘(ℝ) ∞ (fun q : insertionCylinder A B => insertionCutoff A q.val.2) :=
  (contDiff_insertionCutoff A).contMDiff.comp
    (contMDiff_snd.comp (contMDiff_subtype_val (U := insertionCylinder A B)))

private theorem smooth_factor_collar (A B : ℝ) :
    ContMDiff IC 𝓘(ℝ) ∞ (fun q : insertionCylinder A B => conformalFactor q.val.2) :=
  contDiff_conformalFactor.contMDiff.comp
    (contMDiff_snd.comp (contMDiff_subtype_val (U := insertionCylinder A B)))

private def insertionCollarMetric {A B η : ℝ} (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    SmoothRiemannianMetric IC (insertionCylinder A B) :=
  conformalMetricOfContDiff
    ((h.restrictOpenOfSubset (insertionCylinder_le_original hAB)).convexComb
      (scaleMetric η hη ((roundCylinderMetric (E := E3) (n := 2)).restrictOpen (insertionCylinder A B)))
      (fun q => insertionCutoff A q.val.2) (smooth_cutoff_collar A B)
      (fun q => insertionCutoff_mem A q.val.2))
    (fun q => conformalFactor q.val.2) (smooth_factor_collar A B)

private theorem insertionCollarMetric_inner {A B η : ℝ} (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (v w : TangentSpace IC q) :
    (insertionCollarMetric hAB hη h).inner q v w =
      Real.exp (2 * conformalFactor q.val.2) *
        (insertionCutoff A q.val.2 *
          h.inner (Opens.inclusion (insertionCylinder_le_original hAB) q) v w +
        (1 - insertionCutoff A q.val.2) * η *
          (roundCylinderMetric (E := E3) (n := 2)).inner q.val v w) := by
  unfold insertionCollarMetric
  rw [conformalMetricOfContDiff_inner, convexComb_inner, scaleMetric_inner,
    SmoothRiemannianMetric.restrictSubset_inner, SmoothRiemannianMetric.restrictOpen_inner]
  simp only [smul_eq_mul]
  ring

private def insertionAnnulusMetric {A B η : ℝ} (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    SmoothRiemannianMetric (𝓡 3) (insertionAnnulus A B) :=
  Diffeomorph.pullbackMetricCross (insertionCollarMetric hAB hη h) (insertionChart A B).symm

private theorem insertionChart_inverse_deriv (A B : ℝ) (q : insertionCylinder A B)
    (v : TangentSpace IC q) :
    mfderiv (𝓡 3) IC (insertionChart A B).symm (insertionChart A B q)
      (mfderiv IC (𝓡 3) (insertionChart A B) q v) = v := by
  have hchain := mfderiv_comp q
    ((insertionChart A B).symm.contMDiff.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((insertionChart A B).contMDiff.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
  have hid : (insertionChart A B).symm ∘ (insertionChart A B) = id :=
    funext (insertionChart A B).symm_apply_apply
  rw [hid, mfderiv_id] at hchain
  exact (congrArg (fun D => D v) hchain).symm

private theorem insertionChart_deriv_surjective (A B : ℝ) (q : insertionCylinder A B) :
    Function.Surjective (mfderiv IC (𝓡 3) (insertionChart A B) q) := by
  exact ((insertionChart A B).mfderivToContinuousLinearEquiv (by decide) q).surjective

private theorem insertionAnnulusMetric_chart_inner {A B η : ℝ}
    (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (v w : TangentSpace IC q) :
    (insertionAnnulusMetric hAB hη h).inner (insertionChart A B q)
      (mfderiv IC (𝓡 3) (insertionChart A B) q v)
      (mfderiv IC (𝓡 3) (insertionChart A B) q w) =
      (insertionCollarMetric hAB hη h).inner q v w := by
  rw [insertionAnnulusMetric, Diffeomorph.pullbackMetricCross_inner,
    insertionChart_inverse_deriv, insertionChart_inverse_deriv]
  rw [(insertionChart A B).symm_apply_apply]

private theorem insertionAnnulusMetric_inner_of_inner {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (x : insertionAnnulus A B) (hx : ‖(x : E3)‖ < conformalRadius (-7 * A / 4))
    (v w : TangentSpace (𝓡 3) x) :
    (insertionAnnulusMetric hAB hη h).inner x v w = η * metric.inner (x : E3) v w := by
  obtain ⟨q, rfl⟩ := (insertionChart A B).surjective x
  obtain ⟨a, rfl⟩ := insertionChart_deriv_surjective A B q v
  obtain ⟨b, rfl⟩ := insertionChart_deriv_surjective A B q w
  change ‖conformalMap q.val‖ < conformalRadius (-7 * A / 4) at hx
  rw [conformalMap_norm] at hx
  have hz : q.val.2 < -7 * A / 4 := strictMono_conformalRadius.lt_iff_lt.mp hx
  have hcap : metric.inner (insertionChart A B q : E3)
      (mfderiv IC (𝓡 3) (insertionChart A B) q a)
      (mfderiv IC (𝓡 3) (insertionChart A B) q b) =
      Real.exp (2 * conformalFactor q.val.2) *
        (roundCylinderMetric (E := E3) (n := 2)).inner q.val a b := by
    have hm := congrArg₂ (fun v w : E3 => metric.inner (conformalMap q.val) v w)
      (conformalChart_mfderiv_eq_ambient q.val a) (conformalChart_mfderiv_eq_ambient q.val b)
    have hp := hm.symm.trans (conformalChart_metric_inner_exp q.val a b)
    simpa only [insertionChart_apply, insertionChart_mfderiv] using! hp
  calc
    _ = (insertionCollarMetric hAB hη h).inner q a b :=
      insertionAnnulusMetric_chart_inner hAB hη h q a b
    _ = η * (Real.exp (2 * conformalFactor q.val.2) *
        (roundCylinderMetric (E := E3) (n := 2)).inner q.val a b) := by
      rw [insertionCollarMetric_inner, insertionCutoff_zero hA hz.le]
      ring
    _ = _ := congrArg (fun t : ℝ => η * t) hcap.symm

private def insertionInnerMetric (A : ℝ) {η : ℝ} (hη : 0 < η) :
    SmoothRiemannianMetric (𝓡 3) (insertionInner A) :=
  (scaleMetric η hη metric).restrictOpen (insertionInner A)

private theorem insertionMetric_overlap {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (x : E3) (hi : x ∈ insertionInner A) (ha : x ∈ insertionAnnulus A B)
    (v w : TangentSpace (𝓡 3) x) :
    (insertionInnerMetric A hη).inner ⟨x, hi⟩ v w =
      (insertionAnnulusMetric hAB hη h).inner ⟨x, ha⟩ v w := by
  exact (insertionAnnulusMetric_inner_of_inner hA hAB hη h ⟨x, ha⟩ hi v w).symm

private def insertionUnionMetric {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    SmoothRiemannianMetric (𝓡 3) ↥(insertionInner A ⊔ insertionAnnulus A B) :=
  glueMetric (insertionInner A) (insertionAnnulus A B)
    (insertionInnerMetric A hη) (insertionAnnulusMetric hAB hη h)
    (insertionMetric_overlap hA hAB hη h)

def insertedMetric {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    SmoothRiemannianMetric (𝓡 3) (insertionBall B) :=
  (insertionUnionMetric hA hAB hη h).restrictOpenOfSubset
    (le_of_eq (insertionInner_sup_annulus hA hAB).symm)

def insertionMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    insertionCylinder A B → insertionBall B :=
  Opens.inclusion (le_trans le_sup_right (le_of_eq (insertionInner_sup_annulus hA hAB))) ∘
    insertionChart A B

theorem insertionMap_apply {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : insertionCylinder A B) :
    (insertionMap hA hAB q : E3) = conformalMap q.val := rfl

theorem contMDiff_insertionMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    ContMDiff IC (𝓡 3) ∞ (insertionMap hA hAB) :=
  (contMDiff_inclusion
    (le_trans le_sup_right (le_of_eq (insertionInner_sup_annulus hA hAB)))).comp
      (insertionChart A B).contMDiff

theorem injective_insertionMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    Function.Injective (insertionMap hA hAB) := by
  intro x y hxy
  apply (insertionChart A B).injective
  apply Subtype.ext
  exact congrArg (fun z : insertionBall B => z.val) hxy

theorem range_insertionMap {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B) :
    range (insertionMap hA hAB) =
      {x : insertionBall B | x.val ∈ insertionAnnulus A B} := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    exact (insertionChart A B q).property
  · intro hx
    refine ⟨(insertionChart A B).symm ⟨x.val, hx⟩, ?_⟩
    apply Subtype.ext
    change ((insertionChart A B) ((insertionChart A B).symm ⟨x.val, hx⟩)).val = x.val
    rw [(insertionChart A B).apply_symm_apply]

private theorem insertionMap_mfderiv_chart {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : insertionCylinder A B) (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (insertionMap hA hAB) q v =
      mfderiv IC (𝓡 3) (insertionChart A B) q v := by
  rw [insertionMap, mfderiv_comp q
    ((contMDiff_inclusion _).mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((insertionChart A B).contMDiff.mdifferentiableAt (by decide)), mfderiv_opens_incl]
  rfl

theorem insertionMap_mfderiv {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : insertionCylinder A B) (v : TangentSpace IC q) :
    mfderiv IC (𝓡 3) (insertionMap hA hAB) q v =
      mfderiv IC (𝓡 3) conformalMap q.val v :=
  (insertionMap_mfderiv_chart hA hAB q v).trans (insertionChart_mfderiv A B q v)

theorem insertionMap_mfderiv_injective {A B : ℝ} (hA : 0 < A) (hAB : 2 * A < B)
    (q : insertionCylinder A B) :
    Function.Injective (mfderiv IC (𝓡 3) (insertionMap hA hAB) q) := by
  intro v w hvw
  apply ((insertionChart A B).mfderivToContinuousLinearEquiv (by decide) q).injective
  exact (insertionMap_mfderiv_chart hA hAB q v).symm.trans
    (hvw.trans (insertionMap_mfderiv_chart hA hAB q w))

theorem insertedMetric_inner_of_inner {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (x : insertionBall B) (hx : ‖(x : E3)‖ < conformalRadius (-7 * A / 4))
    (v w : TangentSpace (𝓡 3) x) :
    (insertedMetric hA hAB hη h).inner x v w = η * metric.inner (x : E3) v w := by
  change (insertionUnionMetric hA hAB hη h).inner
    (Opens.inclusion (le_of_eq (insertionInner_sup_annulus hA hAB).symm) x) v w = _
  have heq : Opens.inclusion (le_of_eq (insertionInner_sup_annulus hA hAB).symm) x =
      Opens.inclusion le_sup_left (⟨x.val, hx⟩ : insertionInner A) := Subtype.ext rfl
  rw [heq]
  exact glueMetric_inner_left (insertionInner A) (insertionAnnulus A B)
    (insertionInnerMetric A hη) (insertionAnnulusMetric hAB hη h)
    (insertionMetric_overlap hA hAB hη h) ⟨x.val, hx⟩ v w

theorem insertedMetric_interpolation {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (v w : TangentSpace IC q) :
    (insertedMetric hA hAB hη h).inner (insertionMap hA hAB q)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q w) =
      Real.exp (2 * conformalFactor q.val.2) *
        (insertionCutoff A q.val.2 *
          h.inner (Opens.inclusion (insertionCylinder_le_original hAB) q) v w +
        (1 - insertionCutoff A q.val.2) * η *
          (roundCylinderMetric (E := E3) (n := 2)).inner q.val v w) := by
  rw [insertionMap_mfderiv_chart, insertionMap_mfderiv_chart]
  change (glueMetric (insertionInner A) (insertionAnnulus A B)
    (insertionInnerMetric A hη) (insertionAnnulusMetric hAB hη h)
    (insertionMetric_overlap hA hAB hη h)).inner
      (Opens.inclusion le_sup_right (insertionChart A B q))
      (mfderiv IC (𝓡 3) (insertionChart A B) q v)
      (mfderiv IC (𝓡 3) (insertionChart A B) q w) = _
  rw [glueMetric_inner_right, insertionAnnulusMetric_chart_inner]
  exact insertionCollarMetric_inner hAB hη h q v w

theorem insertedMetric_retained {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B))
    (q : insertionCylinder A B) (hq : 0 ≤ q.val.2) (v w : TangentSpace IC q) :
    (insertedMetric hA hAB hη h).inner (insertionMap hA hAB q)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q v)
      (mfderiv IC (𝓡 3) (insertionMap hA hAB) q w) =
      h.inner (Opens.inclusion (insertionCylinder_le_original hAB) q) v w := by
  rw [insertedMetric_interpolation, insertionCutoff_one hA (by linarith),
    conformalFactor_eq_zero_of_nonneg hq]
  ring_nf
  simp only [Real.exp_zero, one_mul]

theorem zero_mem_insertionBall {B : ℝ} (hB : 0 ≤ B) : (0 : E3) ∈ insertionBall B := by
  change ‖(0 : E3)‖ < transitionEnd + B
  rw [norm_zero]
  linarith [transitionEnd_pos]

theorem insertedMetric_smooth_at_tip {A B η : ℝ}
    (hA : 0 < A) (hAB : 2 * A < B) (hη : 0 < η)
    (h : SmoothRiemannianMetric IC (DifferentialGeometry.Geometry.Neck.openCylinder B)) :
    ContMDiffAt (𝓡 3) ((𝓡 3).prod 𝓘(ℝ, E3 →L[ℝ] E3 →L[ℝ] ℝ)) ∞
      (fun x : insertionBall B => TotalSpace.mk' (E3 →L[ℝ] E3 →L[ℝ] ℝ)
        (E := fun y : insertionBall B => TangentSpace (𝓡 3) y →L[ℝ]
          TangentSpace (𝓡 3) y →L[ℝ] ℝ) x ((insertedMetric hA hAB hη h).inner x))
      ⟨0, zero_mem_insertionBall (by linarith)⟩ :=
  (insertedMetric hA hAB hη h).contMDiff.contMDiffAt

end DifferentialGeometry.PDE.RicciFlow.StandardCap
