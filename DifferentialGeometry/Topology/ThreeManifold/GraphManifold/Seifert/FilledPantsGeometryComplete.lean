import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryClassify
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentComplete

/-!
# Completeness data of the two-cone fold

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §3.4,
with review 21 §4.4). The exhaustion `twoConeExhaust` of the interior of the block is the outer
exhaustion `D.outerExhaust ‖u‖` of A4D2's `ConeFoldDescentExhaust`, read through the punctured
chart `C.puncturedChart` (zero on the central fibres of the tubes). Pulled back by the fold it is
`D.outerExhaust ‖f z‖` over the main domain, the same with `σ₀ z` over its mirror, and zero over
the cone discs (`exhaustFn_of_main`, `exhaustFn_of_mirrorMain`, `exhaustFn_of_discOne`, ...), so
it is smooth on the fold domain (`contDiffOn_exhaustFn`) and equal to the coordinate `p 1 = log y`
high in the outer cusp (`exhaustFn_eq_cuspInf`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace TwoConeFold

namespace Fold

open ConeShape

theorem zOf_eq_mk (p : ModelCoordinates) : zOf p = ⟨p 0, Real.exp (p 1)⟩ := coe_logPoint' p

theorem re_zOf (p : ModelCoordinates) : (zOf p).re = p 0 := by rw [zOf_eq_mk]

theorem im_zOf (p : ModelCoordinates) : (zOf p).im = Real.exp (p 1) := by rw [zOf_eq_mk]

section Heights

variable {σ : ConeShape}

theorem im_ge_of_mem_triangle {z : ℂ} (hz : z ∈ σ.triangle) :
    min (Real.sin σ.θ₁) (Real.sin σ.θ₂) / 4 ≤ z.im := by
  have h0 : 0 ≤ z.re := hz.2 0
  have h1 : 0 ≤ σ.width - z.re := hz.2 1
  have h2 : 0 ≤ (z.re - σ.centre) ^ 2 + z.im ^ 2 - 1 / 16 := hz.2 2
  have hs1 := σ.sin_θ₁_pos.le
  have hs2 : 0 ≤ Real.sin σ.θ₂ :=
    Real.sin_nonneg_of_nonneg_of_le_pi σ.θ₂_nonneg (by linarith [σ.θ₂_le, Real.pi_pos])
  have hc1 := σ.cos_θ₁_nonneg
  have hc2 := σ.cos_θ₂_nonneg
  have e1 := Real.sin_sq_add_cos_sq σ.θ₁
  have e2 := Real.sin_sq_add_cos_sq σ.θ₂
  have hW : σ.width = (Real.cos σ.θ₁ + Real.cos σ.θ₂) / 4 := rfl
  have hC : σ.centre = Real.cos σ.θ₂ / 4 := rfl
  set s := min (Real.sin σ.θ₁) (Real.sin σ.θ₂) / 4 with hs
  have hs0 : 0 ≤ s := by positivity
  have hsa : s ≤ Real.sin σ.θ₁ / 4 := by rw [hs]; gcongr; exact min_le_left _ _
  have hsb : s ≤ Real.sin σ.θ₂ / 4 := by rw [hs]; gcongr; exact min_le_right _ _
  have hsq : s ^ 2 ≤ z.im ^ 2 := by
    rcases le_total z.re σ.centre with hr | hr
    · have : (z.re - σ.centre) ^ 2 ≤ σ.centre ^ 2 := by nlinarith
      nlinarith
    · have : (z.re - σ.centre) ^ 2 ≤ (Real.cos σ.θ₁ / 4) ^ 2 := by nlinarith
      nlinarith
  by_contra h
  push Not at h
  have := hz.1
  nlinarith

theorem im_ge_of_mem_domain {z : ℂ} (hz : z ∈ σ.domain) :
    min (Real.sin σ.θ₁) (Real.sin σ.θ₂) / 4 ≤ z.im := by
  rcases σ.mem_domain_iff.1 hz with h | h
  · exact im_ge_of_mem_triangle h
  · have := im_ge_of_mem_triangle h
    rwa [refl_zero_im] at this

theorem low_pos (hθ : 0 < σ.θ₂) : 0 < min (Real.sin σ.θ₁) (Real.sin σ.θ₂) / 4 :=
  div_pos (lt_min σ.sin_θ₁_pos
    (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [σ.θ₂_le, Real.pi_pos]))) (by norm_num)

theorem one_lt_topHeight (D : σ.FoldData) : 1 < D.topHeight := by
  have h : 0 < Real.log (D.outerY₂ + 1) + 1 := by
    have := Real.log_nonneg (by linarith [D.outerY₂_pos] : (1 : ℝ) ≤ D.outerY₂ + 1)
    linarith
  exact lt_of_lt_of_le (Real.one_lt_exp_iff.2 h) (le_max_right _ _)

theorem exhaust_cusp (D : σ.FoldData) {z : ℂ} (hzU : z ∈ D.U) (him : D.topHeight < z.im) :
    D.outerExhaust ‖D.f z‖ = Real.log z.im := by
  rw [D.norm_f_cuspInf z hzU (lt_of_le_of_lt (le_max_left _ _) him)]
  exact D.outerExhaust_outerProfile (le_trans (le_max_right _ _) him.le)

theorem ne_vertex_of_high (D : σ.FoldData) {z : ℂ} (him : D.topHeight < z.im) :
    z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  have h1 := one_lt_topHeight D
  have hs1 := Real.sin_le_one σ.θ₁
  have hs2 := Real.sin_le_one σ.θ₂
  constructor
  · rintro rfl
    rw [vertexOne_im] at him
    linarith
  · rintro rfl
    rw [vertexTwo_im] at him
    linarith

end Heights

section Exhaust

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d) (hk : d.k = 3)
  (hj : ∀ m : Fin d.fillingCount, (C.port (.inr m)).val ≠ 0)
  (hp : ∀ m : Fin d.fillingCount, 0 < (d.fillingSlope m).1)
  {σ : ConeShape} (D : σ.FoldData)

open Classical in
def twoConeExhaust (x : W.pieceInterior ⊤) : ℝ :=
  if h : ∃ y ∈ C.puncturedDomain, C.puncturedChart hk y = x then
    D.outerExhaust ‖(Classical.choose h).1‖
  else 0

include hj hp in
theorem twoConeExhaust_puncturedChart {y : ℂ × Circle} (hy : y ∈ C.puncturedDomain) :
    twoConeExhaust C hk D (C.puncturedChart hk y) = D.outerExhaust ‖y.1‖ := by
  have h : ∃ y' ∈ C.puncturedDomain, C.puncturedChart hk y' = C.puncturedChart hk y :=
    ⟨y, hy, rfl⟩
  unfold twoConeExhaust
  rw [dite_eq_left h]
  have hs := Classical.choose_spec h
  rw [C.puncturedChart_injOn hk hj hp hs.1 hy hs.2]

include hj hp in
theorem twoConeExhaust_tubeMap_zero (m : Fin d.fillingCount) (w : Circle) :
    twoConeExhaust C hk D (C.tubeMap m (0, w)) = 0 := by
  unfold twoConeExhaust
  rw [dite_eq_right]
  rintro ⟨y, hy, heq⟩
  exact C.puncturedChart_ne_tubeMap_zero hk hj hp hy m w heq

theorem outerExhaust_eq_zero_of_le_two {r : ℝ} (hr : r ≤ 2) : D.outerExhaust r = 0 :=
  D.outerExhaust_eq_zero (lt_of_le_of_lt hr
    (D.outerProfile_props (by linarith [D.outerY₂_pos])).1)

include hj hp in
theorem twoConeExhaust_tubeMap (m : Fin d.fillingCount) {v : ℂ} (hv : ‖v‖ < 1) (w : Circle) :
    twoConeExhaust C hk D (C.tubeMap m (v, w)) = 0 := by
  by_cases h0 : v = 0
  · rw [h0]
    exact twoConeExhaust_tubeMap_zero C hk hj hp D m w
  have hdist : ‖(C.seamDir m (v, w)).1 - C.tubeCentre m‖ < 1 / 2 := by
    rw [SeifertBlockCharts.seamDir, norm_seamFwd_sub]
    have : ‖v‖ ^ d.fillingOrder m < 1 :=
      pow_lt_one₀ (norm_nonneg _) hv (SeifertBlockCharts.fillingOrder_pos (hp m)).ne'
    change ‖v‖ ^ d.fillingOrder m / 2 < 1 / 2
    linarith
  have hne : (C.seamDir m (v, w)).1 ≠ C.tubeCentre m := by
    rw [SeifertBlockCharts.seamDir]
    exact seamFwd_fst_ne h0
  have hmem : C.seamDir m (v, w) ∈ C.puncturedDomain :=
    C.mem_puncturedDomain.2 (Or.inr ⟨m, by linarith [C.half_lt_collarRadius (hp m)], hne⟩)
  rw [← puncturedChart_seamDir C hk hj hp (y := (v, w)) h0 hv,
    twoConeExhaust_puncturedChart C hk hj hp D hmem]
  apply outerExhaust_eq_zero_of_le_two
  have hc := C.norm_tubeCentre hk (hj m)
  have := norm_le_norm_add_norm_sub' (C.seamDir m (v, w)).1 (C.tubeCentre m)
  linarith

end Exhaust

section Pull

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (m₁ m₂ : Fin d.fillingCount) (hk : d.k = 3)
  (hj : ∀ m : Fin d.fillingCount, (C.port (.inr m)).val ≠ 0)
  (hp : ∀ m : Fin d.fillingCount, 0 < (d.fillingSlope m).1)
  {σ : ConeShape} (D : σ.FoldData)
  (hθ₁ : σ.θ₁ * (chartNumbers C m₁ m₂).p₁ = Real.pi)
  (hθ₂ : σ.θ₂ * (chartNumbers C m₁ m₂).p₂ = Real.pi)
  (hc₁ : C.tubeCentre m₁ = ((3 / 2 : ℝ) : ℂ)) (hc₂ : C.tubeCentre m₂ = ((-(3 / 2) : ℝ) : ℂ))

def exhaustFn (q : ModelCoordinates) : ℝ :=
  twoConeExhaust C hk D (foldMap C m₁ m₂ hk D hθ₁ hθ₂ q)

include hj hp hc₁ hc₂ in
theorem exhaustFn_of_main {q : ModelCoordinates} (hm : zOf q ∈ mainSet D hθ₁ hθ₂) :
    exhaustFn C m₁ m₂ hk D hθ₁ hθ₂ q = D.outerExhaust ‖D.f (zOf q)‖ := by
  unfold exhaustFn
  rw [foldMap_of_main C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hm,
    twoConeExhaust_puncturedChart C hk hj hp D
      (liftT_mem_puncturedDomain C m₁ m₂ hk hp D hθ₁ hθ₂ hc₁ hc₂ hm)]
  rfl

include hj hp hc₁ hc₂ in
theorem exhaustFn_of_mirrorMain {q : ModelCoordinates}
    (hm : zOf q ∈ mirrorSet σ (mainSet D hθ₁ hθ₂)) :
    exhaustFn C m₁ m₂ hk D hθ₁ hθ₂ q = D.outerExhaust ‖D.f (σ.refl 0 (zOf q))‖ := by
  unfold exhaustFn
  rw [foldMap_of_mirrorMain C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hm,
    twoConeExhaust_puncturedChart C hk hj hp D
      (liftS_mem_puncturedDomain C m₁ m₂ hk hp D hθ₁ hθ₂ hc₁ hc₂ hm)]
  change D.outerExhaust ‖conj (D.f (zOf (flipMap (chartNumbers C m₁ m₂).c₀ q)))‖ = _
  rw [norm_conj, refl_zero_zOf_flip]

include hj hp in
theorem exhaustFn_of_discOne {q : ModelCoordinates} (hd : zOf q ∈ discOne D hθ₁) :
    exhaustFn C m₁ m₂ hk D hθ₁ hθ₂ q = 0 := by
  unfold exhaustFn
  rw [foldMap_of_discOne C m₁ m₂ hk D hθ₁ hθ₂ hd]
  exact twoConeExhaust_tubeMap C hk hj hp D m₁ (norm_tubeOne_fst C m₁ m₂ D hθ₁ hd) _

include hj hp in
theorem exhaustFn_of_mirrorDiscOne {q : ModelCoordinates}
    (hd : zOf q ∈ mirrorSet σ (discOne D hθ₁)) : exhaustFn C m₁ m₂ hk D hθ₁ hθ₂ q = 0 := by
  unfold exhaustFn
  rw [foldMap_of_mirrorDiscOne C m₁ m₂ hk D hθ₁ hθ₂ hd]
  exact twoConeExhaust_tubeMap C hk hj hp D m₁ (norm_tubeOneS_fst C m₁ m₂ D hθ₁ hd) _

include hj hp in
theorem exhaustFn_of_discTwo {q : ModelCoordinates} (hd : zOf q ∈ discTwo D hθ₂) :
    exhaustFn C m₁ m₂ hk D hθ₁ hθ₂ q = 0 := by
  unfold exhaustFn
  rw [foldMap_of_discTwo C m₁ m₂ hk D hθ₁ hθ₂ hd]
  exact twoConeExhaust_tubeMap C hk hj hp D m₂ (norm_tubeTwo_fst C m₁ m₂ D hθ₂ hd) _

theorem contDiff_rhoZero (c : ℝ) : ContDiff ℝ ∞ (rhoZero c) :=
  contMDiff_iff_contDiff.1 (rhoZero c).contMDiff

include hj hp hc₁ hc₂ in
theorem contDiffOn_exhaustFn :
    ContDiffOn ℝ ∞ (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂) (foldDomain C m₁ m₂ D hθ₁ hθ₂) := by
  intro q hq
  apply ContDiffAt.contDiffWithinAt
  have hz : Continuous zOf := contDiff_zOf.continuous
  have hzero : ∀ S : Set ℂ, IsOpen S → zOf q ∈ S →
      (∀ q' : ModelCoordinates, zOf q' ∈ S → exhaustFn C m₁ m₂ hk D hθ₁ hθ₂ q' = 0) →
      ContDiffAt ℝ ∞ (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂) q := fun S hS hqS h0 =>
    contDiffAt_const.congr_of_eventuallyEq
      (eventually_of_mem ((hS.preimage hz).mem_nhds hqS) fun q' hq' => h0 q' hq')
  rcases hq with (((h | h) | h) | h) | h
  · have hev : exhaustFn C m₁ m₂ hk D hθ₁ hθ₂ =ᶠ[𝓝 q]
        fun q' => D.outerExhaust ‖D.f (zOf q')‖ :=
      eventually_of_mem (((isOpen_mainSet D hθ₁ hθ₂).preimage hz).mem_nhds h) fun q' hq' =>
        exhaustFn_of_main C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hq'
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have hf : ContDiffAt ℝ ∞ D.f (zOf q) :=
      D.contDiffOn_f.contDiffAt (D.isOpen_U.mem_nhds (mainSet_props D hθ₁ hθ₂ h).1)
    exact (D.contDiffAt_outerExhaust_norm (norm_f_lt_three_of_mainSet D hθ₁ hθ₂ h)).comp q
      (hf.comp q contDiff_zOf.contDiffAt)
  · have hev : exhaustFn C m₁ m₂ hk D hθ₁ hθ₂ =ᶠ[𝓝 q]
        fun q' => D.outerExhaust ‖D.f (zOf (rhoZero 0 q'))‖ :=
      eventually_of_mem (((isOpen_mirrorSet (isOpen_mainSet D hθ₁ hθ₂)).preimage hz).mem_nhds h)
        fun q' hq' => by
          rw [exhaustFn_of_mirrorMain C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hq']
          change _ = D.outerExhaust ‖D.f (zOf (rhoZero 0 q'))‖
          rw [zOf_rhoZero (σ := σ)]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have h' : zOf (rhoZero 0 q) ∈ mainSet D hθ₁ hθ₂ := by rw [zOf_rhoZero]; exact h.2
    have hf : ContDiffAt ℝ ∞ D.f (zOf (rhoZero 0 q)) :=
      D.contDiffOn_f.contDiffAt (D.isOpen_U.mem_nhds (mainSet_props D hθ₁ hθ₂ h').1)
    exact (D.contDiffAt_outerExhaust_norm (norm_f_lt_three_of_mainSet D hθ₁ hθ₂ h')).comp q
      (hf.comp q (contDiff_zOf.contDiffAt.comp q (contDiff_rhoZero 0).contDiffAt))
  · exact hzero _ (isOpen_discOne D hθ₁) h fun q' hq' =>
      exhaustFn_of_discOne C m₁ m₂ hk hj hp D hθ₁ hθ₂ hq'
  · exact hzero _ (isOpen_mirrorSet (isOpen_discOne D hθ₁)) h fun q' hq' =>
      exhaustFn_of_mirrorDiscOne C m₁ m₂ hk hj hp D hθ₁ hθ₂ hq'
  · exact hzero _ (isOpen_discTwo D hθ₂) h fun q' hq' =>
      exhaustFn_of_discTwo C m₁ m₂ hk hj hp D hθ₁ hθ₂ hq'

theorem domain_subset_baseDomain {z : ℂ} (hz : z ∈ σ.domain) : z ∈ baseDomain D hθ₁ hθ₂ := by
  rcases σ.mem_domain_iff.1 hz with hT | hT
  · rcases triangle_subset D hθ₁ hθ₂ hT with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inr h
  · have him : 0 < z.im := by have := hT.1; rwa [refl_zero_im] at this
    rcases triangle_subset D hθ₁ hθ₂ hT with (h | h) | h
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨him, h⟩)))
    · exact Or.inl (Or.inr ⟨him, h⟩)
    · refine Or.inr ⟨him, ?_⟩
      rw [← σ.refl_zero_refl_zero z, σ.coneDisc_vertexTwo_refl_zero, norm_conj]
      exact h.2

include hj hp hc₁ hc₂ in
theorem exhaustFn_eq_cuspInf {p₀ : ModelCoordinates} (hp₀ : zOf p₀ ∈ σ.domain)
    (hhigh : D.topHeight < Real.exp (p₀ 1)) :
    exhaustFn C m₁ m₂ hk D hθ₁ hθ₂ =ᶠ[𝓝 p₀] fun q => q 1 := by
  have hz : Continuous zOf := contDiff_zOf.continuous
  have hO : IsOpen {q : ModelCoordinates | D.topHeight < Real.exp (q 1)} :=
    isOpen_lt continuous_const (Real.continuous_exp.comp (PiLp.continuous_apply 2 _ 1))
  by_cases hT : zOf p₀ ∈ σ.triangle
  · have hv := ne_vertex_of_high D (by rw [im_zOf]; exact hhigh : D.topHeight < (zOf p₀).im)
    have hm := triangle_diff_subset_mainSet D hθ₁ hθ₂ hT hv.1 hv.2
    refine eventually_of_mem ((((isOpen_mainSet D hθ₁ hθ₂).preimage hz).inter hO).mem_nhds
      ⟨hm, hhigh⟩) fun q hq => ?_
    rw [exhaustFn_of_main C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hq.1,
      exhaust_cusp D (mainSet_props D hθ₁ hθ₂ hq.1).1 (by rw [im_zOf]; exact hq.2), im_zOf,
      Real.log_exp]
  · have hT' := (σ.mem_domain_iff.1 hp₀).resolve_left hT
    have hv := ne_vertex_of_high D (z := σ.refl 0 (zOf p₀))
      (by rw [refl_zero_im, im_zOf]; exact hhigh)
    have hm : zOf p₀ ∈ mirrorSet σ (mainSet D hθ₁ hθ₂) :=
      ⟨zOf_im_pos p₀, triangle_diff_subset_mainSet D hθ₁ hθ₂ hT' hv.1 hv.2⟩
    refine eventually_of_mem ((((isOpen_mirrorSet (isOpen_mainSet D hθ₁ hθ₂)).preimage
      hz).inter hO).mem_nhds ⟨hm, hhigh⟩) fun q hq => ?_
    rw [exhaustFn_of_mirrorMain C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hq.1,
      exhaust_cusp D (mainSet_props D hθ₁ hθ₂ hq.1.2).1
        (by rw [refl_zero_im, im_zOf]; exact hq.2),
      refl_zero_im, im_zOf, Real.log_exp]

end Pull

end Fold

end TwoConeFold

end GC.Seifert
