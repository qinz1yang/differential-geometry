import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MobiusBlockAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarBundleMobius

/-!
# The twisted chart of the Möbius circle bundle

Lane MD5b, step (1) of `exists_syncedMobiusPiece` (plan item T5 of lane MD5).

The chart sends `((z, t), v)` to the class in `mobiusBundleSet ⊆ L(4, -1)` whose model points
(`modelPoint`, `SF/MobiusRefibration.lean`) are `(z, u)` and `modelDeck (z, u)`, where
`u = annulusPt t v = exp ((2t - 1) L(v)) v` and `L(v) = arcosh (8 - Re v²) / 2` (`halfWidth`).
Since `‖u + u⁻¹‖² = 2 cosh (2 log ‖u‖) + 2 Re v²` and `2 cosh (2 L(v)) = 16 - 2 Re v²`, the
condition `‖joukowski u‖ ≤ 3` is `|2t - 1| ≤ 1`, with equality exactly at `t ∈ {0, 1}`; the map
`(t, v) ↦ u` is injective with inverse `(annulusTime u, u / ‖u‖)`, and
`annulusPt (1 - t) v̄ = u⁻¹`, so `mobiusDeck` covers `modelDeck` (`modelOf_mobiusDeck`).
The value is the image of any sphere point with these model points (`exists_sphere_modelPoint`);
`projection_eq_iff_modelPoint` gives `chart_eq_chart_iff` and `surjective_chart`, and
`mobiusBundleSet_isBoundaryPoint_iff_base` gives `isBoundaryPoint_chart_iff`.

Smoothness. Near `p₀` the lift `liftPair m u = c (m (u - 1), m (u + 1))` with the local square
root `m = κ₀ + k κ̄₀` of `k = -z v̄` (`m² = k ‖m‖²`, `κ₀² = k(p₀)`) is a smooth sphere-valued map
(`contMDiffAt_sphere`, a pointwise form of `ContMDiff.codRestrict_sphere`) with model point
`(z, u)`, so `contMDiff_chart` follows. For `exists_localSection`, `branchPoint z₀` picks the model
point `(z, u)` with `Re (z z̄₀) > 0`; it is invariant under `σ`, descends by `lensDescend`, and is
smooth where `Re (z z̄₀) ≠ 0`; the section is `invPoint = ((z, annulusTime u), u / ‖u‖)` on that
open set.
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

namespace MobiusModelChart

private def halfWidth (v : ℂ) : ℝ := Real.arcosh (8 - (v ^ 2).re) / 2

private theorem re_sq_le_one {v : ℂ} (hv : ‖v‖ = 1) : (v ^ 2).re ≤ 1 := by
  have h : v.re ^ 2 + v.im ^ 2 = 1 := by
    have h1 := Complex.sq_norm v
    rw [hv, Complex.normSq_apply] at h1
    linarith
  rw [sq, Complex.mul_re]
  nlinarith [sq_nonneg v.im]

private theorem halfWidth_pos {v : ℂ} (hv : ‖v‖ = 1) : 0 < halfWidth v := by
  have := re_sq_le_one hv
  exact div_pos (Real.arcosh_pos (by linarith)) two_pos

private theorem cosh_two_halfWidth {v : ℂ} (hv : ‖v‖ = 1) :
    Real.cosh (2 * halfWidth v) = 8 - (v ^ 2).re := by
  have := re_sq_le_one hv
  rw [halfWidth, mul_div_cancel₀ _ two_ne_zero, Real.cosh_arcosh (by linarith)]

private theorem norm_sq_add_inv {v : ℂ} (hv : ‖v‖ = 1) (x : ℝ) :
    ‖(Real.exp x : ℂ) * v + ((Real.exp x : ℂ) * v)⁻¹‖ ^ 2 =
      2 * Real.cosh (2 * x) + 2 * (v ^ 2).re := by
  have h : v.re ^ 2 + v.im ^ 2 = 1 := by
    have h1 := Complex.sq_norm v
    rw [hv, Complex.normSq_apply] at h1
    linarith
  have hinv : v⁻¹ = conj v := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hv]; simp
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  rw [mul_inv, hinv, ← Complex.ofReal_inv, ← Real.exp_neg, Real.cosh_eq, Complex.sq_norm,
    Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.conj_re, Complex.conj_im, sq]
  have h2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by rw [← Real.exp_add]; ring_nf
  rw [h2, h3]
  linear_combination (Real.exp x * Real.exp x + Real.exp (-x) * Real.exp (-x)) * h + 0 * he
    + (2 * v.re * v.re  - 2 * v.im * v.im) * he


private theorem norm_joukowski_eq (u : ℂ) : ‖joukowski u‖ = 3 / 4 * ‖u + u⁻¹‖ := by
  rw [joukowski, norm_mul]
  norm_num

private theorem norm_joukowski_exp_le_iff {v : ℂ} (hv : ‖v‖ = 1) (x : ℝ) :
    ‖joukowski ((Real.exp x : ℂ) * v)‖ ≤ 3 ↔ |x| ≤ halfWidth v := by
  have hL := halfWidth_pos hv
  have hc := cosh_two_halfWidth hv
  have hN := norm_sq_add_inv hv x
  set N := ‖(Real.exp x : ℂ) * v + ((Real.exp x : ℂ) * v)⁻¹‖
  have hN0 : 0 ≤ N := norm_nonneg _
  rw [norm_joukowski_eq]
  have e1 : 3 / 4 * N ≤ 3 ↔ N ^ 2 ≤ 4 ^ 2 := by
    rw [pow_le_pow_iff_left₀ hN0 (by norm_num) two_ne_zero]
    constructor <;> intro h <;> linarith
  have e2 : |x| ≤ halfWidth v ↔ |2 * x| ≤ |2 * halfWidth v| := by
    rw [abs_mul, abs_mul, abs_of_pos hL, abs_two]
    constructor <;> intro h <;> linarith
  rw [e1, e2, ← Real.cosh_le_cosh, hN, hc]
  constructor <;> intro h <;> linarith

private theorem norm_joukowski_exp_eq_iff {v : ℂ} (hv : ‖v‖ = 1) (x : ℝ) :
    ‖joukowski ((Real.exp x : ℂ) * v)‖ = 3 ↔ |x| = halfWidth v := by
  have hL := halfWidth_pos hv
  have hc := cosh_two_halfWidth hv
  have hN := norm_sq_add_inv hv x
  set N := ‖(Real.exp x : ℂ) * v + ((Real.exp x : ℂ) * v)⁻¹‖
  have hN0 : 0 ≤ N := norm_nonneg _
  rw [norm_joukowski_eq]
  have e1 : 3 / 4 * N = 3 ↔ N ^ 2 = 4 ^ 2 := by
    rw [pow_left_inj₀ hN0 (by norm_num) two_ne_zero]
    constructor <;> intro h <;> linarith
  have e2 : |x| = halfWidth v ↔ |2 * x| = |2 * halfWidth v| := by
    rw [abs_mul, abs_mul, abs_of_pos hL, abs_two]
    constructor <;> intro h <;> linarith
  have e3 : |2 * x| = |2 * halfWidth v| ↔
      Real.cosh (2 * x) = Real.cosh (2 * halfWidth v) := by
    rw [le_antisymm_iff, le_antisymm_iff, Real.cosh_le_cosh, Real.cosh_le_cosh]
  rw [e1, e2, e3, hN, hc]
  constructor <;> intro h <;> linarith

private def annulusPt (t : ℝ) (v : ℂ) : ℂ := (Real.exp ((2 * t - 1) * halfWidth v) : ℂ) * v

private theorem annulusPt_ne_zero (t : ℝ) {v : ℂ} (hv : v ≠ 0) : annulusPt t v ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') hv

private theorem norm_annulusPt (t : ℝ) {v : ℂ} (hv : ‖v‖ = 1) :
    ‖annulusPt t v‖ = Real.exp ((2 * t - 1) * halfWidth v) := by
  rw [annulusPt, norm_mul, hv, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

private theorem norm_joukowski_annulusPt_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {v : ℂ}
    (hv : ‖v‖ = 1) : ‖joukowski (annulusPt t v)‖ ≤ 3 := by
  rw [annulusPt, norm_joukowski_exp_le_iff hv, abs_mul, abs_of_pos (halfWidth_pos hv)]
  have h : |2 * t - 1| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  nlinarith [halfWidth_pos hv]

private theorem norm_joukowski_annulusPt_eq_iff (t : ℝ) {v : ℂ} (hv : ‖v‖ = 1) :
    ‖joukowski (annulusPt t v)‖ = 3 ↔ t = 0 ∨ t = 1 := by
  have hL := halfWidth_pos hv
  rw [annulusPt, norm_joukowski_exp_eq_iff hv, abs_mul, abs_of_pos hL]
  constructor
  · intro h
    have h1 : |2 * t - 1| = 1 := by
      have := mul_right_cancel₀ hL.ne' (h.trans (one_mul _).symm)
      exact this
    rcases abs_eq (zero_le_one) |>.mp h1 with h2 | h2
    · right; linarith
    · left; linarith
  · rintro (h | h) <;> subst h <;> norm_num

private theorem halfWidth_conj (v : ℂ) : halfWidth (conj v) = halfWidth v := by
  rw [halfWidth, halfWidth, ← map_pow, Complex.conj_re]

private theorem inv_eq_conj {v : ℂ} (hv : ‖v‖ = 1) : v⁻¹ = conj v := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hv]
  simp

private theorem annulusPt_symm (t : ℝ) {v : ℂ} (hv : ‖v‖ = 1) :
    annulusPt (1 - t) (conj v) = (annulusPt t v)⁻¹ := by
  rw [annulusPt, annulusPt, halfWidth_conj, mul_inv, inv_eq_conj hv, ← Complex.ofReal_inv,
    ← Real.exp_neg]
  congr 3
  ring

private theorem annulusPt_inj {t t' : ℝ} {v v' : ℂ} (hv : ‖v‖ = 1) (hv' : ‖v'‖ = 1)
    (h : annulusPt t v = annulusPt t' v') : t = t' ∧ v = v' := by
  have hn := congrArg norm h
  rw [norm_annulusPt t hv, norm_annulusPt t' hv'] at hn
  have hvv : v = v' := by
    have h2 := h
    rw [annulusPt, annulusPt, hn] at h2
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') h2
  subst hvv
  refine ⟨?_, rfl⟩
  have h3 := Real.exp_injective hn
  have hL := halfWidth_pos hv
  have h4 := mul_right_cancel₀ hL.ne' h3
  linarith

private def annulusTime (u : ℂ) : ℝ := (1 + Real.log ‖u‖ / halfWidth (u / (‖u‖ : ℂ))) / 2

private theorem norm_div_norm {u : ℂ} (hu : u ≠ 0) : ‖u / (‖u‖ : ℂ)‖ = 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr hu)]

private theorem annulusPt_annulusTime {u : ℂ} (hu : u ≠ 0) :
    annulusPt (annulusTime u) (u / (‖u‖ : ℂ)) = u := by
  have hL := halfWidth_pos (norm_div_norm hu)
  have hn : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu)
  have e : (2 * annulusTime u - 1) * halfWidth (u / (‖u‖ : ℂ)) = Real.log ‖u‖ := by
    rw [annulusTime]
    field_simp
    ring
  rw [annulusPt, e, Real.exp_log (norm_pos_iff.mpr hu), mul_div_cancel₀ _ hn]

private theorem annulusTime_mem {u : ℂ} (hu : u ≠ 0) (hJ : ‖joukowski u‖ ≤ 3) :
    annulusTime u ∈ Icc (0 : ℝ) 1 := by
  have hv := norm_div_norm hu
  have hL := halfWidth_pos hv
  have h := hJ
  rw [← annulusPt_annulusTime hu, annulusPt, norm_joukowski_exp_le_iff hv, abs_mul,
    abs_of_pos hL] at h
  have h2 : |2 * annulusTime u - 1| ≤ 1 := by
    by_contra hc
    rw [not_le] at hc
    nlinarith
  rw [abs_le] at h2
  exact ⟨by linarith, by linarith⟩

private def modelOf (p : (Circle × unitInterval) × Circle) : ℂ × ℂ :=
  ((p.1.1 : ℂ), annulusPt (p.1.2 : ℝ) (p.2 : ℂ))

private theorem modelOf_mobiusDeck (p : (Circle × unitInterval) × Circle) :
    modelOf (mobiusDeck p) = modelDeck (modelOf p) := by
  refine Prod.ext ?_ ?_
  · simp [modelOf, mobiusDeck, modelDeck]
  · change annulusPt (1 - (p.1.2 : ℝ)) ((p.2⁻¹ : Circle) : ℂ) = (annulusPt (p.1.2 : ℝ) p.2)⁻¹
    rw [Circle.coe_inv_eq_conj, annulusPt_symm _ (Circle.norm_coe _)]

private theorem modelOf_injective : Function.Injective modelOf := by
  intro p q h
  have h1 : (p.1.1 : ℂ) = q.1.1 := congrArg Prod.fst h
  obtain ⟨h2, h3⟩ := annulusPt_inj (Circle.norm_coe p.2) (Circle.norm_coe q.2) (congrArg Prod.snd h)
  exact Prod.ext (Prod.ext (Circle.ext h1) (Subtype.ext h2)) (Circle.ext h3)

private theorem modelDeck_modelDeck (q : ℂ × ℂ) : modelDeck (modelDeck q) = q := by
  simp [modelDeck]

private theorem exists_lift (p : (Circle × unitInterval) × Circle) :
    ∃ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      bundleQuartic (lensPair x) ≤ 0 ∧ modelPoint (lensPair x) = modelOf p :=
  exists_sphere_modelPoint _ _ (Circle.norm_coe _) (annulusPt_ne_zero _ (Circle.coe_ne_zero _))
    (norm_joukowski_annulusPt_le p.1.2.2 (Circle.norm_coe _))

private def chartLift (p : (Circle × unitInterval) × Circle) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
  Classical.choose (exists_lift p)

private theorem chartLift_spec (p : (Circle × unitInterval) × Circle) :
    bundleQuartic (lensPair (chartLift p)) ≤ 0 ∧ modelPoint (lensPair (chartLift p)) = modelOf p :=
  Classical.choose_spec (exists_lift p)

private theorem lensUp_mem {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1}
    (hx : bundleQuartic (lensPair x) ≤ 0) :
    lensUp.{u} (mobiusLensGroup.projection x) ∈ mobiusBundleSet.{u} :=
  hx

def chart (p : (Circle × unitInterval) × Circle) : mobiusBundleSet.{u} :=
  ⟨lensUp (mobiusLensGroup.projection (chartLift p)), lensUp_mem (chartLift_spec p).1⟩

private theorem chart_eq_iff (p : (Circle × unitInterval) × Circle)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (hx : bundleQuartic (lensPair x) ≤ 0) :
    chart.{u} p = ⟨lensUp (mobiusLensGroup.projection x), lensUp_mem hx⟩ ↔
      modelPoint (lensPair x) = modelOf p ∨ modelPoint (lensPair x) = modelDeck (modelOf p) := by
  rw [← (chartLift_spec p).2, ← projection_eq_iff_modelPoint _ _ (chartLift_spec p).1 hx]
  constructor
  · intro h
    exact congrArg lensDown.{u} (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (congrArg lensUp.{u} h)

theorem chart_eq_chart_iff (p q : (Circle × unitInterval) × Circle) :
    chart.{u} p = chart q ↔ q = p ∨ q = mobiusDeck p := by
  change chart.{u} p = ⟨lensUp (mobiusLensGroup.projection (chartLift q)),
    lensUp_mem (chartLift_spec q).1⟩ ↔ _
  rw [chart_eq_iff _ _ (chartLift_spec q).1, (chartLift_spec q).2, ← modelOf_mobiusDeck]
  exact or_congr modelOf_injective.eq_iff modelOf_injective.eq_iff

private theorem modelPoint_props {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1}
    (hx : bundleQuartic (lensPair x) ≤ 0) :
    ‖(modelPoint (lensPair x)).1‖ = 1 ∧ (modelPoint (lensPair x)).2 ≠ 0 ∧
      ‖joukowski (modelPoint (lensPair x)).2‖ ≤ 3 := by
  have hab := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero x) hx
  obtain ⟨h1, h2⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hab
  refine ⟨?_, ?_, ?_⟩
  · change ‖modelFibrePoint (lensPair x)‖ = 1
    rw [modelFibrePoint, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr hab)]
  · change modelAnnulusPoint (lensPair x) ≠ 0
    exact div_ne_zero (neg_ne_zero.mpr h2) h1
  · change ‖joukowski (modelAnnulusPoint (lensPair x))‖ ≤ 3
    rw [joukowski_modelAnnulusPoint hab]
    exact (bundleQuartic_nonpos_iff hab).mp hx

private def invPoint (q : ℂ × ℂ) : (Circle × unitInterval) × Circle :=
  ((unitOf q.1, Set.projIcc 0 1 zero_le_one (annulusTime q.2)), unitOf q.2)

private theorem coe_unitOf_eq {u : ℂ} (hu : u ≠ 0) : (unitOf u : ℂ) = u / (‖u‖ : ℂ) := by
  rw [coe_unitOf hu, Complex.real_smul, div_eq_inv_mul, Complex.ofReal_inv]

private theorem modelOf_invPoint {q : ℂ × ℂ} (hz : ‖q.1‖ = 1) (hu : q.2 ≠ 0)
    (hJ : ‖joukowski q.2‖ ≤ 3) : modelOf (invPoint q) = q := by
  have hz0 : q.1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact zero_ne_one hz
  refine Prod.ext ?_ ?_
  · change (unitOf q.1 : ℂ) = q.1
    rw [coe_unitOf_eq hz0, hz, Complex.ofReal_one, div_one]
  · change annulusPt (Set.projIcc 0 1 zero_le_one (annulusTime q.2) : ℝ) (unitOf q.2 : ℂ) = q.2
    rw [Set.projIcc_of_mem _ (annulusTime_mem hu hJ), coe_unitOf_eq hu, annulusPt_annulusTime hu]

private theorem valid_of_eq {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1}
    (hx : bundleQuartic (lensPair x) ≤ 0) {q : ℂ × ℂ}
    (hq : q = modelPoint (lensPair x) ∨ q = modelDeck (modelPoint (lensPair x))) :
    ‖q.1‖ = 1 ∧ q.2 ≠ 0 ∧ ‖joukowski q.2‖ ≤ 3 := by
  obtain ⟨h1, h2, h3⟩ := modelPoint_props hx
  rcases hq with hq | hq
  · rw [hq]
    exact ⟨h1, h2, h3⟩
  · rw [hq]
    refine ⟨by rw [modelDeck, norm_neg]; exact h1, inv_ne_zero h2, ?_⟩
    change ‖joukowski (modelPoint (lensPair x)).2⁻¹‖ ≤ 3
    rw [joukowski, inv_inv, add_comm]
    exact h3

private theorem chart_invPoint (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (hx : bundleQuartic (lensPair x) ≤ 0) {q : ℂ × ℂ}
    (hq : q = modelPoint (lensPair x) ∨ q = modelDeck (modelPoint (lensPair x))) :
    chart.{u} (invPoint q) = ⟨lensUp (mobiusLensGroup.projection x), lensUp_mem hx⟩ := by
  have hp := valid_of_eq hx hq
  rw [chart_eq_iff _ _ hx, modelOf_invPoint hp.1 hp.2.1 hp.2.2]
  rcases hq with hq | hq
  · exact Or.inl hq.symm
  · right
    rw [hq, modelDeck_modelDeck]

theorem surjective_chart : Function.Surjective chart.{u} := by
  intro y
  obtain ⟨x, hx, hq⟩ := exists_sphere_rep y
  refine ⟨invPoint (modelPoint (lensPair x)), ?_⟩
  rw [chart_invPoint x hq (Or.inl rfl)]
  refine Subtype.ext ?_
  change lensUp (mobiusLensGroup.projection x) = y.val
  rw [← hx]
  rfl

theorem isBoundaryPoint_chart_iff (p : (Circle × unitInterval) × Circle) :
    (𝓡∂ 3).IsBoundaryPoint (chart.{u} p) ↔ ((p.1.2 : ℝ) = 0 ∨ (p.1.2 : ℝ) = 1) := by
  have hc := chartLift_spec p
  have hab := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero _) hc.1
  rw [mobiusBundleSet_isBoundaryPoint_iff_base, mobiusBundleBase_eq (x := chartLift p) rfl,
    ← joukowski_modelAnnulusPoint hab]
  change ‖joukowski (modelPoint (lensPair (chartLift p))).2‖ = 3 ↔ _
  rw [hc.2]
  exact norm_joukowski_annulusPt_eq_iff _ (Circle.norm_coe _)

private theorem contMDiffAt_sphere {E' H' M : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]
    {g : M → Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1} {x : M}
    (h : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ∞
      (fun y => (g y : EuclideanSpace ℝ (Fin 4))) x) :
    ContMDiffAt I (𝓡 3) ∞ g x := by
  rw [contMDiffAt_iff_target]
  refine ⟨Topology.IsInducing.subtypeVal.continuousAt_iff.mpr h.continuousAt, ?_⟩
  let U : _ ≃ₗᵢ[ℝ] _ :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton 3 (ne_zero_of_mem_unit_sphere (-(g x)))).repr
  have H₁ : ContDiffOn ℝ ∞ (U ∘ stereoToFun (-(g x : EuclideanSpace ℝ (Fin 4))))
      {y | innerSL ℝ (-(g x : EuclideanSpace ℝ (Fin 4))) y ≠ (1 : ℝ)} :=
    (U.contDiff.contDiffOn (s := univ)).comp_inter contDiffOn_stereoToFun |>.mono
      (fun y hy => ⟨hy, trivial⟩)
  have hmem : (g x : EuclideanSpace ℝ (Fin 4)) ∈
      {y | innerSL ℝ (-(g x : EuclideanSpace ℝ (Fin 4))) y ≠ (1 : ℝ)} := by
    simp only [mem_ofPred_eq, innerSL_apply_apply, inner_neg_left, real_inner_self_eq_norm_sq,
      norm_eq_of_mem_sphere (g x)]
    norm_num
  have hopen : IsOpen {y : EuclideanSpace ℝ (Fin 4) |
      innerSL ℝ (-(g x : EuclideanSpace ℝ (Fin 4))) y ≠ (1 : ℝ)} :=
    isOpen_ne_fun (innerSL ℝ _).continuous continuous_const
  have H₂ : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      ((U ∘ stereoToFun (-(g x : EuclideanSpace ℝ (Fin 4)))) ∘
        fun y => (g y : EuclideanSpace ℝ (Fin 4))) x :=
    ContDiffAt.comp_contMDiffAt (f := fun y => (g y : EuclideanSpace ℝ (Fin 4))) (x := x)
      (H₁.contDiffAt (hopen.mem_nhds hmem)) h
  convert H₂ using 1
  funext y
  rfl
private def liftScale (m u : ℂ) : ℝ := (Real.sqrt (‖m‖ ^ 2 * (2 * ‖u‖ ^ 2 + 2)))⁻¹

private def liftPair (m u : ℂ) : ℂ × ℂ :=
  ((liftScale m u : ℂ) * m * (u - 1), (liftScale m u : ℂ) * m * (u + 1))

private theorem norm_sq_sub_add (u : ℂ) : ‖u - 1‖ ^ 2 + ‖u + 1‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.add_re,
    Complex.one_re, Complex.sub_im, Complex.add_im, Complex.one_im]
  ring

private theorem liftScale_pos {m : ℂ} (hm : m ≠ 0) (u : ℂ) : 0 < liftScale m u := by
  have : 0 < ‖m‖ := norm_pos_iff.mpr hm
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

private theorem liftPair_norm {m : ℂ} (hm : m ≠ 0) (u : ℂ) :
    ‖(liftPair m u).1‖ ^ 2 + ‖(liftPair m u).2‖ ^ 2 = 1 := by
  have hm' : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hX : 0 < ‖m‖ ^ 2 * (2 * ‖u‖ ^ 2 + 2) := by positivity
  have hc : liftScale m u ^ 2 * (‖m‖ ^ 2 * (2 * ‖u‖ ^ 2 + 2)) = 1 := by
    rw [liftScale, inv_pow, Real.sq_sqrt hX.le, inv_mul_cancel₀ hX.ne']
  simp only [liftPair, norm_mul, Complex.norm_real, Real.norm_of_nonneg (liftScale_pos hm u).le,
    mul_pow]
  rw [← hc, ← norm_sq_sub_add]
  ring

private theorem lensPair_symm_liftPair_mem {m : ℂ} (hm : m ≠ 0) (u : ℂ) :
    lensPair.symm (liftPair m u) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h := norm_sq_eq_lensPair (lensPair.symm (liftPair m u))
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (h.trans (liftPair_norm hm u))

private theorem modelPoint_liftPair {m u z : ℂ} (hm : m ≠ 0) (hu : u ≠ 0) (hz : ‖z‖ = 1)
    (hsq : m ^ 2 * u = -(z * ((‖m‖ ^ 2 * ‖u‖ : ℝ) : ℂ))) :
    modelPoint (liftPair m u) = (z, u) := by
  have hc := liftScale_pos hm u
  have hc0 : (liftScale m u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hR : 0 < 4 * liftScale m u ^ 2 * ‖m‖ ^ 2 * ‖u‖ := by
    have := norm_pos_iff.mpr hm
    have := norm_pos_iff.mpr hu
    positivity
  have e : (liftPair m u).1 ^ 2 - (liftPair m u).2 ^ 2 =
      ((4 * liftScale m u ^ 2 * ‖m‖ ^ 2 * ‖u‖ : ℝ) : ℂ) * z := by
    have hsq' := hsq
    push_cast at hsq'
    simp only [liftPair]
    push_cast
    linear_combination (-4 * (liftScale m u : ℂ) ^ 2) * hsq'
  refine Prod.ext ?_ ?_
  · change modelFibrePoint (liftPair m u) = z
    have hR0 : ((4 * liftScale m u ^ 2 * ‖m‖ ^ 2 * ‖u‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hR.ne'
    rw [modelFibrePoint, e, norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le, hz, mul_one]
    field_simp
  · change modelAnnulusPoint (liftPair m u) = u
    simp only [modelAnnulusPoint, liftPair]
    have h2 : (liftScale m u : ℂ) * m * (u - 1) - (liftScale m u : ℂ) * m * (u + 1) =
        -2 * ((liftScale m u : ℂ) * m) := by ring
    rw [h2, div_eq_iff (mul_ne_zero (by norm_num) (mul_ne_zero hc0 hm))]
    ring

private theorem sq_localRoot {κ k : ℂ} (hk : ‖k‖ = 1) :
    (κ + k * conj κ) ^ 2 = k * ((‖κ + k * conj κ‖ ^ 2 : ℝ) : ℂ) := by
  have hk' : k * conj k = 1 := by
    rw [Complex.mul_conj', hk]
    simp
  push_cast
  rw [← Complex.mul_conj', map_add, map_mul, Complex.conj_conj]
  linear_combination (-(κ ^ 2 + k * κ * conj κ)) * hk'

private theorem localLift_props {m z v : ℂ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hz : ‖z‖ = 1)
    (hv : ‖v‖ = 1) (hm : m ≠ 0) (hsq : m ^ 2 = -(z * conj v) * ((‖m‖ ^ 2 : ℝ) : ℂ)) :
    bundleQuartic (liftPair m (annulusPt t v)) ≤ 0 ∧
      modelPoint (liftPair m (annulusPt t v)) = (z, annulusPt t v) := by
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at hv
    exact zero_ne_one hv
  have hu := annulusPt_ne_zero t hv0
  have hvv : conj v * v = 1 := by
    rw [Complex.conj_mul', hv]
    simp
  have hmp : modelPoint (liftPair m (annulusPt t v)) = (z, annulusPt t v) := by
    refine modelPoint_liftPair hm hu hz ?_
    rw [hsq, norm_annulusPt t hv, annulusPt]
    set R := Real.exp ((2 * t - 1) * halfWidth v)
    push_cast
    linear_combination (-(z * (‖m‖ : ℂ) ^ 2 * (R : ℂ))) * hvv
  refine ⟨?_, hmp⟩
  have hab : (liftPair m (annulusPt t v)).1 ^ 2 - (liftPair m (annulusPt t v)).2 ^ 2 ≠ 0 := by
    intro h0
    have h1 : modelFibrePoint (liftPair m (annulusPt t v)) = z := congrArg Prod.fst hmp
    rw [modelFibrePoint, h0, zero_div] at h1
    rw [← h1, norm_zero] at hz
    exact zero_ne_one hz
  rw [bundleQuartic_nonpos_iff hab, ← joukowski_modelAnnulusPoint hab]
  change ‖joukowski (modelPoint (liftPair m (annulusPt t v))).2‖ ≤ 3
  rw [hmp]
  exact norm_joukowski_annulusPt_le ht hv

private theorem contDiffAt_halfWidth {v : ℂ} (hv : ‖v‖ = 1) : ContDiffAt ℝ ∞ halfWidth v := by
  have h1 : (1 : ℝ) < 8 - (v ^ 2).re := by linarith [re_sq_le_one hv]
  have hg : ContDiff ℝ ∞ (fun w : ℂ => 8 - (w ^ 2).re) :=
    contDiff_const.sub (Complex.reCLM.contDiff.comp (contDiff_id.pow 2))
  exact ((Real.contDiffAt_arcosh h1).comp v hg.contDiffAt).div_const 2

private theorem contDiffAt_annulusPt {q : ℝ × ℂ} (hv : ‖q.2‖ = 1) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => annulusPt q.1 q.2) q := by
  have hL : ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => halfWidth q.2) q :=
    (contDiffAt_halfWidth hv).comp q contDiffAt_snd
  have hE : ContDiffAt ℝ ∞ (fun q : ℝ × ℂ => Real.exp ((2 * q.1 - 1) * halfWidth q.2)) q :=
    Real.contDiff_exp.contDiffAt.comp q
      (((contDiffAt_const.mul contDiffAt_fst).sub contDiffAt_const).mul hL)
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp q hE).mul contDiffAt_snd

private theorem contDiffAt_liftScale {q : ℂ × ℂ} (hm : q.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => liftScale q.1 q.2) q := by
  have hX : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => ‖q.1‖ ^ 2 * (2 * ‖q.2‖ ^ 2 + 2)) q :=
    (((contDiff_norm_sq ℝ).comp contDiff_fst).mul
      ((contDiff_const.mul ((contDiff_norm_sq ℝ).comp contDiff_snd)).add contDiff_const)).contDiffAt
  have hpos : 0 < ‖q.1‖ ^ 2 * (2 * ‖q.2‖ ^ 2 + 2) := by
    have := norm_pos_iff.mpr hm
    positivity
  exact (hX.sqrt hpos.ne').inv (Real.sqrt_pos.mpr hpos).ne'

private theorem contDiffAt_liftPair {q : ℂ × ℂ} (hm : q.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => liftPair q.1 q.2) q := by
  have hc : ContDiffAt ℝ ∞ (fun q : ℂ × ℂ => (liftScale q.1 q.2 : ℂ)) q :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp q (contDiffAt_liftScale hm)
  exact ((hc.mul contDiffAt_fst).mul (contDiffAt_snd.sub contDiffAt_const)).prodMk
    ((hc.mul contDiffAt_fst).mul (contDiffAt_snd.add contDiffAt_const))

private def localRaw (κ : ℂ) (q : ℂ × ℝ × ℂ) : EuclideanSpace ℝ (Fin 4) :=
  lensPair.symm (liftPair (κ + -(q.1 * conj q.2.2) * conj κ) (annulusPt q.2.1 q.2.2))

private theorem contDiffAt_localRaw (κ : ℂ) {q : ℂ × ℝ × ℂ} (hv : ‖q.2.2‖ = 1)
    (hm : κ + -(q.1 * conj q.2.2) * conj κ ≠ 0) : ContDiffAt ℝ ∞ (localRaw κ) q := by
  have hmq : ContDiffAt ℝ ∞ (fun q : ℂ × ℝ × ℂ => κ + -(q.1 * conj q.2.2) * conj κ) q :=
    contDiffAt_const.add ((contDiffAt_fst.mul (Complex.conjLIE.contDiff.contDiffAt.comp q
      (contDiffAt_snd.comp q contDiffAt_snd))).neg.mul contDiffAt_const)
  have hu : ContDiffAt ℝ ∞ (fun q : ℂ × ℝ × ℂ => annulusPt q.2.1 q.2.2) q :=
    (contDiffAt_annulusPt hv).comp q contDiffAt_snd
  have hl0 : ContDiffAt ℝ ∞ (fun r : ℂ × ℂ => liftPair r.1 r.2)
      (κ + -(q.1 * conj q.2.2) * conj κ, annulusPt q.2.1 q.2.2) :=
    contDiffAt_liftPair (q := (κ + -(q.1 * conj q.2.2) * conj κ, annulusPt q.2.1 q.2.2)) hm
  have h := lensPair.symm.contDiff.contDiffAt.comp q (hl0.comp q (hmq.prodMk hu))
  exact h

private theorem contMDiff_coords : ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) 𝓘(ℝ, ℂ × ℝ × ℂ) ∞
    (fun p : (Circle × unitInterval) × Circle => ((p.1.1 : ℂ), ((p.1.2 : ℝ), (p.2 : ℂ)))) := by
  have h1 : ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (Circle × unitInterval) × Circle => (p.1.1 : ℂ)) :=
    contMDiff_circle_coe.comp (contMDiff_fst.comp contMDiff_fst)
  have h2 : ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : (Circle × unitInterval) × Circle => (p.1.2 : ℝ)) :=
    (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := 1)).comp (contMDiff_snd.comp contMDiff_fst)
  have h3 : ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) 𝓘(ℝ, ℂ) ∞
      (fun p : (Circle × unitInterval) × Circle => (p.2 : ℂ)) :=
    contMDiff_circle_coe.comp contMDiff_snd
  exact h1.prodMk_space (h2.prodMk_space h3)

theorem contMDiff_chart :
    ContMDiff (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) (𝓡∂ 3) ∞ chart.{u} := by
  refine (mobiusBundleAtlas.contMDiff_iff_subtype_val _).mpr fun p₀ => ?_
  obtain ⟨κ, hκ⟩ := exists_circle_sq_eq (k := -((p₀.1.1 : ℂ) * conj (p₀.2 : ℂ))) (by
    rw [norm_neg, norm_mul, Complex.norm_conj, Circle.norm_coe, Circle.norm_coe, one_mul])
  set m : (Circle × unitInterval) × Circle → ℂ :=
    fun p => (κ : ℂ) + -((p.1.1 : ℂ) * conj (p.2 : ℂ)) * conj (κ : ℂ) with hmdef
  have hm₀ : m p₀ ≠ 0 := by
    have hκκ : (κ : ℂ) * conj (κ : ℂ) = 1 := by
      rw [Complex.mul_conj', Circle.norm_coe]
      simp
    have h2 : m p₀ = 2 * κ := by
      simp only [hmdef]
      rw [← hκ]
      linear_combination (κ : ℂ) * hκκ
    rw [h2]
    exact mul_ne_zero two_ne_zero (Circle.coe_ne_zero κ)
  have hmc : Continuous m :=
    (continuous_const.add ((continuous_fst.mul (Complex.continuous_conj.comp
      (continuous_snd.comp continuous_snd))).neg.mul continuous_const)).comp
      contMDiff_coords.continuous
  have hW : IsOpen {p | m p ≠ 0} := isOpen_ne_fun hmc continuous_const
  let S : (Circle × unitInterval) × Circle → Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 :=
    fun p => if h : m p ≠ 0 then
      ⟨lensPair.symm (liftPair (m p) (annulusPt p.1.2 p.2)), lensPair_symm_liftPair_mem h _⟩
    else chartLift p
  have hSv : ∀ p, m p ≠ 0 →
      (S p : EuclideanSpace ℝ (Fin 4)) = lensPair.symm (liftPair (m p) (annulusPt p.1.2 p.2)) := by
    intro p hp
    simp only [S, dite_eq_left hp]
  have hS : ContMDiffAt (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) (𝓡 3) ∞ S p₀ := by
    apply contMDiffAt_sphere
    have hraw := ContDiffAt.comp_contMDiffAt
      (f := fun p : (Circle × unitInterval) × Circle => ((p.1.1 : ℂ), ((p.1.2 : ℝ), (p.2 : ℂ))))
      (contDiffAt_localRaw (κ : ℂ) (Circle.norm_coe p₀.2) hm₀) (contMDiff_coords p₀)
    apply hraw.congr_of_eventuallyEq
    filter_upwards [hW.mem_nhds hm₀] with p hp
    exact hSv p hp
  have hsq : ∀ p, m p ^ 2 = -((p.1.1 : ℂ) * conj (p.2 : ℂ)) * ((‖m p‖ ^ 2 : ℝ) : ℂ) := by
    intro p
    exact sq_localRoot (by
      rw [norm_neg, norm_mul, Complex.norm_conj, Circle.norm_coe, Circle.norm_coe, one_mul])
  have heq : ∀ p, m p ≠ 0 →
      (chart.{u} p).val = lensUp.{u} (mobiusLensGroup.projection (S p)) := by
    intro p hp
    have hprops := localLift_props p.1.2.2 (Circle.norm_coe _) (Circle.norm_coe _) hp (hsq p)
    have hl : lensPair (S p) = liftPair (m p) (annulusPt p.1.2 p.2) := by
      rw [hSv p hp]
      exact lensPair.apply_symm_apply _
    have hQ : bundleQuartic (lensPair (S p)) ≤ 0 := by
      rw [hl]
      exact hprops.1
    have h := (chart_eq_iff p (S p) hQ).mpr (Or.inl (by rw [hl, hprops.2]; rfl))
    exact congrArg Subtype.val h
  have hcomp : ContMDiffAt (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) (𝓡 3) ∞
      (fun p => lensUp.{u} (mobiusLensGroup.projection (S p))) p₀ :=
    contMDiff_lensUp.contMDiffAt.comp p₀
      (mobiusLensGroup.projection_isLocalDiffeomorph.contMDiff.contMDiffAt.comp p₀ hS)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [hW.mem_nhds hm₀] with p hp
  exact heq p hp

private theorem contDiffAt_modelFibrePoint {q : ℂ × ℂ} (hab : q.1 ^ 2 - q.2 ^ 2 ≠ 0) :
    ContDiffAt ℝ ∞ modelFibrePoint q := by
  have he : modelFibrePoint = (fun p : ℂ × ℂ => p.1 ^ 2 - p.2 ^ 2) *
      (fun p : ℂ × ℂ => ((‖p.1 ^ 2 - p.2 ^ 2‖ : ℝ) : ℂ))⁻¹ :=
    funext fun p => div_eq_mul_inv _ _
  rw [he]
  have hm : ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => p.1 ^ 2 - p.2 ^ 2) q :=
    (contDiffAt_fst.pow 2).sub (contDiffAt_snd.pow 2)
  have hn' : ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => ‖p.1 ^ 2 - p.2 ^ 2‖) q :=
    (contDiffAt_norm ℝ hab).comp q hm
  have hn : ContDiffAt ℝ ∞ (fun p : ℂ × ℂ => ((‖p.1 ^ 2 - p.2 ^ 2‖ : ℝ) : ℂ)) q :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp q hn'
  exact hm.mul (hn.inv (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hab)))

private theorem contDiffAt_modelAnnulusPoint {q : ℂ × ℂ} (h : q.1 - q.2 ≠ 0) :
    ContDiffAt ℝ ∞ modelAnnulusPoint q := by
  have he : modelAnnulusPoint = (fun p : ℂ × ℂ => -(p.1 + p.2)) *
      (fun p : ℂ × ℂ => p.1 - p.2)⁻¹ :=
    funext fun p => div_eq_mul_inv _ _
  rw [he]
  exact (contDiffAt_fst.add contDiffAt_snd).neg.mul ((contDiffAt_fst.sub contDiffAt_snd).inv h)

private theorem contDiffAt_modelPoint {q : ℂ × ℂ} (hab : q.1 ^ 2 - q.2 ^ 2 ≠ 0) :
    ContDiffAt ℝ ∞ modelPoint q :=
  (contDiffAt_modelFibrePoint hab).prodMk
    (contDiffAt_modelAnnulusPoint (sub_ne_zero_of_sq_sub_sq_ne_zero hab).1)

private theorem contDiffAt_modelDeck {q : ℂ × ℂ} (h : q.2 ≠ 0) : ContDiffAt ℝ ∞ modelDeck q :=
  contDiffAt_fst.neg.prodMk (contDiffAt_snd.inv h)

private def branchPoint (z₀ : ℂ) (q : ℂ × ℂ) : ℂ × ℂ :=
  if 0 < ((modelPoint q).1 * conj z₀).re then modelPoint q
  else if ((modelPoint q).1 * conj z₀).re < 0 then modelDeck (modelPoint q) else 0

private theorem re_modelDeck (z₀ : ℂ) (q : ℂ × ℂ) :
    ((modelDeck q).1 * conj z₀).re = -(q.1 * conj z₀).re := by
  simp [modelDeck]

private theorem branchPoint_lensUnitAction (z₀ : ℂ) :
    ∀ ε : Circle, ε ^ 4 = 1 → ∀ q, branchPoint z₀ (lensUnitAction ε q) = branchPoint z₀ q := by
  intro ε hε q
  rcases sq_eq_one_or_neg_one hε with h | h
  · rw [branchPoint, branchPoint, modelPoint_lensUnitAction_of_sq_eq_one h]
  · rw [branchPoint, branchPoint, modelPoint_lensUnitAction_of_sq_eq_neg_one h, re_modelDeck,
      modelDeck_modelDeck]
    split_ifs <;> first | rfl | (exfalso; linarith)

private theorem branchPoint_eq {z₀ : ℂ} {q : ℂ × ℂ} (hr : ((modelPoint q).1 * conj z₀).re ≠ 0) :
    branchPoint z₀ q = modelPoint q ∨ branchPoint z₀ q = modelDeck (modelPoint q) := by
  rw [branchPoint]
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd (le_antisymm (not_lt.mp h1) (not_lt.mp h2)) hr

private theorem contDiffAt_branchPoint (z₀ : ℂ) {q : ℂ × ℂ} (hab : q.1 ^ 2 - q.2 ^ 2 ≠ 0)
    (hr : ((modelPoint q).1 * conj z₀).re ≠ 0) : ContDiffAt ℝ ∞ (branchPoint z₀) q := by
  have hc : ContinuousAt (fun q : ℂ × ℂ => ((modelPoint q).1 * conj z₀).re) q :=
    Complex.continuous_re.continuousAt.comp
      ((contDiffAt_modelFibrePoint hab).continuousAt.mul continuousAt_const)
  rcases hr.lt_or_gt with hr | hr
  · have hu : (modelPoint q).2 ≠ 0 := by
      obtain ⟨h1, h2⟩ := sub_ne_zero_of_sq_sub_sq_ne_zero hab
      exact div_ne_zero (neg_ne_zero.mpr h2) h1
    have hd : ContDiffAt ℝ ∞ (modelDeck ∘ modelPoint) q :=
      (contDiffAt_modelDeck hu).comp q (contDiffAt_modelPoint hab)
    apply hd.congr_of_eventuallyEq
    filter_upwards [hc.eventually_lt continuousAt_const hr] with q' hq'
    rw [branchPoint, ite_eq_right (not_lt.mpr hq'.le), ite_eq_left hq']
    rfl
  · apply (contDiffAt_modelPoint hab).congr_of_eventuallyEq
    filter_upwards [continuousAt_const.eventually_lt hc hr] with q' hq'
    rw [branchPoint, ite_eq_left hq']

private def sqFn (z₀ : ℂ) (q : ℂ × ℂ) : ℝ := ((modelPoint q).1 * conj z₀).re ^ 2

private theorem sqFn_lensUnitAction (z₀ : ℂ) :
    ∀ ε : Circle, ε ^ 4 = 1 → ∀ q, sqFn z₀ (lensUnitAction ε q) = sqFn z₀ q := by
  intro ε hε q
  rcases sq_eq_one_or_neg_one hε with h | h
  · rw [sqFn, sqFn, modelPoint_lensUnitAction_of_sq_eq_one h]
  · rw [sqFn, sqFn, modelPoint_lensUnitAction_of_sq_eq_neg_one h, re_modelDeck, neg_sq]

private theorem contDiffAt_sqFn (z₀ : ℂ) {q : ℂ × ℂ} (hab : q.1 ^ 2 - q.2 ^ 2 ≠ 0) :
    ContDiffAt ℝ ∞ (sqFn z₀) q :=
  (Complex.reCLM.contDiff.contDiffAt.comp q
    ((contDiffAt_modelFibrePoint hab).mul contDiffAt_const)).pow 2

private theorem contDiffAt_annulusTime {u : ℂ} (hu : u ≠ 0) : ContDiffAt ℝ ∞ annulusTime u := by
  have hn : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu)
  have hlog : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log ‖w‖) u :=
    (Real.contDiffAt_log.mpr (norm_ne_zero_iff.mpr hu)).comp u (contDiffAt_norm ℝ hu)
  have hdiv : ContDiffAt ℝ ∞ (fun w : ℂ => w / (‖w‖ : ℂ)) u := by
    have he : (fun w : ℂ => w / (‖w‖ : ℂ)) = (fun w : ℂ => w) * (fun w : ℂ => ((‖w‖ : ℝ) : ℂ))⁻¹ :=
      funext fun w => div_eq_mul_inv _ _
    rw [he]
    exact contDiffAt_id.mul
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp u (contDiffAt_norm ℝ hu)).inv hn)
  have hL := (contDiffAt_halfWidth (norm_div_norm hu)).comp u hdiv
  exact ((contDiffAt_const.add (hlog.div hL (halfWidth_pos (norm_div_norm hu)).ne')).div_const 2)

theorem exists_localSection (x₀ : mobiusBundleSet.{u}) :
    ∃ V : Set mobiusBundleSet.{u}, IsOpen V ∧ x₀ ∈ V ∧
      ∃ s : mobiusBundleSet.{u} → (Circle × unitInterval) × Circle,
        ContMDiffOn (𝓡∂ 3) (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) ∞ s V ∧ ∀ x ∈ V, chart (s x) = x := by
  obtain ⟨w₀, hw₀, hq₀⟩ := exists_sphere_rep x₀
  set z₀ := (modelPoint (lensPair w₀)).1 with hz₀
  let H : mobiusBundleSet.{u} → ℂ × ℂ :=
    fun x => lensDescend (branchPoint z₀) (branchPoint_lensUnitAction z₀) (lensDown x.val)
  let G : mobiusBundleSet.{u} → ℝ :=
    fun x => lensDescend (sqFn z₀) (sqFn_lensUnitAction z₀) (lensDown x.val)
  have hH : ∀ x : mobiusBundleSet.{u}, ∀ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      lensDown x.val = mobiusLensGroup.projection w → H x = branchPoint z₀ (lensPair w) := by
    intro x w hw
    change lensDescend _ _ (lensDown x.val) = _
    rw [hw]
    rfl
  have hG : ∀ x : mobiusBundleSet.{u}, ∀ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      lensDown x.val = mobiusLensGroup.projection w → G x = sqFn z₀ (lensPair w) := by
    intro x w hw
    change lensDescend _ _ (lensDown x.val) = _
    rw [hw]
    rfl
  have hGm : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ G := by
    intro x
    obtain ⟨w, hw, hq⟩ := exists_sphere_rep x
    have h := contMDiffAt_lensDescend (sqFn_lensUnitAction z₀) w (contDiffAt_sqFn z₀
      (sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero w) hq))
    rw [← hw] at h
    exact h.comp x (contMDiff_lensDown.comp mobiusBundleAtlas.contMDiff_subtype_val).contMDiffAt
  set V : Set mobiusBundleSet.{u} := G ⁻¹' Ioi 0 with hV
  have hrV : ∀ x ∈ V, ∀ w : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1,
      lensDown x.val = mobiusLensGroup.projection w →
        ((modelPoint (lensPair w)).1 * conj z₀).re ≠ 0 := by
    intro x hx w hw h0
    have h1 : G x = 0 := by
      rw [hG x w hw, sqFn, h0]
      ring
    have h2 : 0 < G x := hx
    linarith
  have hvalid : ∀ x ∈ V, ‖(H x).1‖ = 1 ∧ (H x).2 ≠ 0 ∧ ‖joukowski (H x).2‖ ≤ 3 := by
    intro x hx
    obtain ⟨w, hw, hq⟩ := exists_sphere_rep x
    rw [hH x w hw]
    exact valid_of_eq hq (branchPoint_eq (hrV x hx w hw))
  refine ⟨V, isOpen_Ioi.preimage hGm.continuous, ?_, fun x => invPoint (H x), ?_, ?_⟩
  · change 0 < G x₀
    rw [hG x₀ w₀ hw₀, sqFn, ← hz₀, Complex.mul_conj', (modelPoint_props hq₀).1]
    norm_num
  · intro x hx
    obtain ⟨w, hw, hq⟩ := exists_sphere_rep x
    have hab := sq_sub_sq_ne_zero_of_bundleQuartic_nonpos (lensPair_ne_zero w) hq
    have hHx : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℂ × ℂ) ∞ H x := by
      have h := contMDiffAt_lensDescend (branchPoint_lensUnitAction z₀) w
        (contDiffAt_branchPoint z₀ hab (hrV x hx w hw))
      rw [← hw] at h
      exact h.comp x (contMDiff_lensDown.comp mobiusBundleAtlas.contMDiff_subtype_val).contMDiffAt
    obtain ⟨h1, h2, h3⟩ := hvalid x hx
    have hH1 : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞ (fun y => (H y).1) x :=
      contDiff_fst.comp_contMDiffAt hHx
    have hH2 : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℂ) ∞ (fun y => (H y).2) x :=
      contDiff_snd.comp_contMDiffAt hHx
    have hne1 : (H x).1 ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    have c1 : ContMDiffAt (𝓡∂ 3) (𝓡 1) ∞ (fun y => unitOf (H y).1) x :=
      (contMDiffOn_unitOf.contMDiffAt ((isOpen_ne_fun continuous_id continuous_const).mem_nhds
        hne1)).comp x hH1
    have c3 : ContMDiffAt (𝓡∂ 3) (𝓡 1) ∞ (fun y => unitOf (H y).2) x :=
      (contMDiffOn_unitOf.contMDiffAt ((isOpen_ne_fun continuous_id continuous_const).mem_nhds
        h2)).comp x hH2
    have hT : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ (fun y => annulusTime (H y).2) x :=
      ContDiffAt.comp_contMDiffAt (f := fun y => (H y).2) (x := x) (contDiffAt_annulusTime h2)
        hH2
    have hmaps : MapsTo (fun y => annulusTime (H y).2) V (Icc (0 : ℝ) 1) := by
      intro y hy
      obtain ⟨-, k2, k3⟩ := hvalid y hy
      exact annulusTime_mem k2 k3
    have c2 : ContMDiffWithinAt (𝓡∂ 3) (𝓡∂ 1) ∞
        (fun y => Set.projIcc (0 : ℝ) 1 zero_le_one (annulusTime (H y).2)) V x :=
      (contMDiffOn_projIcc _ (hmaps hx)).comp x hT.contMDiffWithinAt hmaps
    exact (c1.contMDiffWithinAt.prodMk c2).prodMk c3.contMDiffWithinAt
  · intro x hx
    obtain ⟨w, hw, hq⟩ := exists_sphere_rep x
    change chart (invPoint (H x)) = x
    rw [hH x w hw, chart_invPoint w hq (branchPoint_eq (hrV x hx w hw))]
    refine Subtype.ext ?_
    change lensUp (mobiusLensGroup.projection w) = x.val
    rw [← hw]
    rfl

end MobiusModelChart

end GC.Seifert
