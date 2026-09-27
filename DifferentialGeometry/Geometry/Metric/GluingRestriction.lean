import DifferentialGeometry.Geometry.Metric.FamilyGluing
import DifferentialGeometry.Geometry.Metric.Euclidean.Construction
import DifferentialGeometry.Geometry.Metric.Conformal.OfContDiff

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry TopologicalSpace ContinuousLinearMap
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Metric
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
variable {ι : Type*} (U : ι → Opens M) (g : ∀ i, SmoothRiemannianMetric I (U i))

theorem glueMetricFamilyOn_inner_of_mem (V : Opens M) (hU : ∀ i, U i ≤ V)
    (hcover : ∀ x : V, ∃ i, x.val ∈ U i)
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w)
    (i : ι) (x : V) (hx : (x : M) ∈ U i) (v w : TangentSpace I (x : M)) :
    (glueMetricFamilyOn U g V hU hcover heq).inner x v w =
      (g i).inner ⟨x, hx⟩ v w :=
  glueMetricFamilyOn_inner U g V hU hcover heq i ⟨x, hx⟩ v w

theorem glueMetricFamilyOn_restrict_piece (V : Opens M) (hU : ∀ i, U i ≤ V)
    (hcover : ∀ x : V, ∃ i, x.val ∈ U i)
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w)
    (i : ι) :
    (glueMetricFamilyOn U g V hU hcover heq).restrictOpenOfSubset (hU i) = g i := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  exact glueMetricFamilyOn_inner U g V hU hcover heq i x v w

theorem mfderiv_glueMetricFamilyOn_inner (V : Opens M) (hU : ∀ i, U i ≤ V)
    (hcover : ∀ x : V, ∃ i, x.val ∈ U i)
    (heq : ∀ (i j : ι) (x : M) (hi : x ∈ U i) (hj : x ∈ U j) (v w : TangentSpace I x),
      (g i).inner ⟨x, hi⟩ v w = (g j).inner ⟨x, hj⟩ v w)
    (i : ι) (X Y : ContMDiffSection I E ∞ (TangentSpace I : V → Type _)) (x : U i) :
    mfderiv I 𝓘(ℝ) (fun y : U i =>
        (glueMetricFamilyOn U g V hU hcover heq).inner (Opens.inclusion (hU i) y)
          (X (Opens.inclusion (hU i) y)) (Y (Opens.inclusion (hU i) y))) x =
      mfderiv I 𝓘(ℝ) (fun y : U i =>
        (g i).inner y (X (Opens.inclusion (hU i) y)) (Y (Opens.inclusion (hU i) y))) x := by
  have hfun : (fun y : U i =>
        (glueMetricFamilyOn U g V hU hcover heq).inner (Opens.inclusion (hU i) y)
          (X (Opens.inclusion (hU i) y)) (Y (Opens.inclusion (hU i) y))) =
      (fun y : U i =>
        (g i).inner y (X (Opens.inclusion (hU i) y)) (Y (Opens.inclusion (hU i) y))) := by
    funext y
    exact glueMetricFamilyOn_inner U g V hU hcover heq i y _ _
  rw [hfun]

private def tm {x : ℝ} (v : TangentSpace 𝓘(ℝ) x) : ℝ := v

private def lineFormL : ℝ →L[ℝ] (ℝ →L[ℝ] ℝ →L[ℝ] ℝ) :=
  smulRight (1 : ℝ →L[ℝ] ℝ)
    (smulRight (smulRight (1 : ℝ →L[ℝ] ℝ) (1 : ℝ)) (1 : ℝ →L[ℝ] ℝ))

private def lineForm (c : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := lineFormL c

private theorem lineForm_apply (c v w : ℝ) : lineForm c v w = c * (v * w) := by
  simp only [lineForm, lineFormL, smulRight_apply, one_apply_eq_self, smul_apply, smul_eq_mul]
  ring

private abbrev standardLineMetric : SmoothRiemannianMetric 𝓘(ℝ) ℝ :=
  DifferentialGeometry.Geometry.Riemannian.smoothMetricOfBilinearField (fun _ : ℝ => lineForm 1)
    (fun _ v w => by rw [lineForm_apply, lineForm_apply]; ring)
    (fun _ v hv => by rw [lineForm_apply]; exact mul_pos zero_lt_one (mul_self_pos.mpr hv))
    contDiff_const

private theorem standardLineMetric_inner (x v w : ℝ) :
    standardLineMetric.inner x v w = v * w := by
  rw [DifferentialGeometry.Geometry.Riemannian.smoothMetricOfBilinearField_inner, lineForm_apply,
    one_mul]

private theorem standardLineMetric_inner_tm (x : ℝ) (v w : TangentSpace 𝓘(ℝ) x) :
    standardLineMetric.inner x v w = tm v * tm w := by
  simpa only [tm] using standardLineMetric_inner x (tm v) (tm w)

private abbrev bumpLineMetric : SmoothRiemannianMetric 𝓘(ℝ) ℝ :=
  conformalMetricOfContDiff standardLineMetric (fun t : ℝ => Real.smoothTransition (t - 2))
    ((Real.smoothTransition.contDiff.contMDiff).comp (contMDiff_id.sub contMDiff_const))

private theorem bumpLineMetric_inner (x v w : ℝ) :
    bumpLineMetric.inner x v w =
      Real.exp (2 * Real.smoothTransition (x - 2)) * (v * w) := by
  change Real.exp (2 * Real.smoothTransition (x - 2)) * standardLineMetric.inner x v w =
    Real.exp (2 * Real.smoothTransition (x - 2)) * (v * w)
  rw [standardLineMetric_inner]

private theorem bumpLineMetric_inner_tm (x : ℝ) (v w : TangentSpace 𝓘(ℝ) x) :
    bumpLineMetric.inner x v w =
      Real.exp (2 * Real.smoothTransition (x - 2)) * (tm v * tm w) := by
  change Real.exp (2 * Real.smoothTransition (x - 2)) * standardLineMetric.inner x v w = _
  rw [standardLineMetric_inner_tm]

private theorem scaleMetric_two_standardLineMetric_inner (x : ℝ) (v w : TangentSpace 𝓘(ℝ) x) :
    (scaleMetric 2 (by norm_num) standardLineMetric).inner x v w = 2 * (tm v * tm w) := by
  rw [scaleMetric_inner, standardLineMetric_inner_tm]

theorem exists_nontrivial_glueMetric :
    ∃ (U V : Opens ℝ) (gU : SmoothRiemannianMetric 𝓘(ℝ) U) (gV : SmoothRiemannianMetric 𝓘(ℝ) V)
      (_ : ∀ (x : ℝ) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace 𝓘(ℝ) x),
        gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w),
      ∃ x : V, ∃ v : ℝ, v ≠ 0 ∧ gV.inner x v v ≠ v * v := by
  refine ⟨⟨Ioo (0 : ℝ) 2, isOpen_Ioo⟩, ⟨Ioo (1 : ℝ) 3, isOpen_Ioo⟩,
    standardLineMetric.restrictOpen _, bumpLineMetric.restrictOpen _, ?_, ?_⟩
  · intro x hxU hxV v w
    have hx2 : x - 2 ≤ 0 := by
      have := hxU.2
      linarith
    change standardLineMetric.inner x v w = bumpLineMetric.inner x v w
    rw [standardLineMetric_inner_tm, bumpLineMetric_inner_tm, Real.smoothTransition.zero_of_nonpos hx2,
      mul_zero, Real.exp_zero, one_mul]
  · refine ⟨⟨5 / 2, by norm_num⟩, 1, one_ne_zero, ?_⟩
    change bumpLineMetric.inner (5 / 2) (1 : ℝ) (1 : ℝ) ≠ (1 : ℝ) * 1
    rw [bumpLineMetric_inner]
    have hp : 0 < Real.smoothTransition ((5 : ℝ) / 2 - 2) :=
      Real.smoothTransition.pos_of_pos (by norm_num)
    have hgt : 1 < Real.exp (2 * Real.smoothTransition ((5 : ℝ) / 2 - 2)) :=
      Real.one_lt_exp_iff.mpr (by linarith)
    intro h
    simp only [mul_one] at h
    exact (ne_of_gt hgt) h

theorem exists_inner_ne_of_scaleMetric_two :
    ∃ (U V : Opens ℝ) (gU : SmoothRiemannianMetric 𝓘(ℝ) U) (gV : SmoothRiemannianMetric 𝓘(ℝ) V),
      ¬ ∀ (x : ℝ) (hxU : x ∈ U) (hxV : x ∈ V) (v w : TangentSpace 𝓘(ℝ) x),
          gU.inner ⟨x, hxU⟩ v w = gV.inner ⟨x, hxV⟩ v w := by
  refine ⟨⊤, ⊤, standardLineMetric.restrictOpen ⊤,
    (scaleMetric 2 (by norm_num) standardLineMetric).restrictOpen ⊤, ?_⟩
  intro h
  let v : TangentSpace 𝓘(ℝ) (0 : ℝ) := show TangentSpace 𝓘(ℝ) (0 : ℝ) from (1 : ℝ)
  have hv : tm v = 1 := rfl
  have h0 := h 0 trivial trivial v v
  change standardLineMetric.inner (0 : ℝ) v v =
    (scaleMetric 2 (by norm_num) standardLineMetric).inner (0 : ℝ) v v at h0
  rw [standardLineMetric_inner_tm, scaleMetric_two_standardLineMetric_inner, hv] at h0
  norm_num at h0

end DifferentialGeometry.Geometry.Metric
