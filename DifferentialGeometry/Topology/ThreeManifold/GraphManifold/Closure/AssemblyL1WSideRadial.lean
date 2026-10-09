import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideCompress

/-!
# Chapter-14 assembly, item L1, group G3b: the radial compression of the closed ball

`radialCompress l a r = 1 + compress l a (r - 1) - l a (1 - φ (8 r - 1))` (`φ` the smooth
transition): the identity for `r ≤ 1/8` and for `r ≥ 1`, equal to `1 + compress l a (r - 1)` for
`r ≥ 1/4` (provided `l (1/2 + a) ≤ 3/4`), with positive derivative. The radial map
`x ↦ x + ((ρ ‖x‖ - ‖x‖) / ‖x‖) x` of a profile `ρ` that is the identity near `0` is smooth;
`radialCompressDiffeo` is the diffeomorphism of `ℝ³` of the profile `radialCompress l a` (inverse:
the radial map of the inverse profile). It preserves the closed unit ball, and on `{‖x‖ ≥ 1/4}` it is
the cap chart compression: `capMap b (T x) = ((capMap b x).1, compress l a (capMap b x).2)`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint Manifold
open scoped Manifold ContDiff Topology InnerProductSpace

namespace GC.GraphManifold.Assembly

variable {l a : ℝ}

/-- The radial compression profile. -/
def radialCompress (l : ℝ) {a : ℝ} (ha : 0 ≤ a) (r : ℝ) : ℝ :=
  1 + compress l ha (r - 1) - l * a * (1 - Real.smoothTransition (8 * r - 1))

theorem radialCompress_of_le (hl : 0 < l) (ha : 0 ≤ a) (hla : l * (1 / 2 + a) ≤ 3 / 4) {r : ℝ}
    (hr : r ≤ 1 / 8) : radialCompress l ha r = r := by
  rw [radialCompress, compress_eq_add hl ha (by nlinarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

theorem radialCompress_of_quarter_le (ha : 0 ≤ a) {r : ℝ} (hr : 1 / 4 ≤ r) :
    radialCompress l ha r = 1 + compress l ha (r - 1) := by
  rw [radialCompress, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem radialCompress_of_one_le (hl : 0 < l) (ha : 0 ≤ a) {r : ℝ} (hr : 1 ≤ r) :
    radialCompress l ha r = r := by
  rw [radialCompress_of_quarter_le ha (by linarith), compress_of_nonneg hl ha (by linarith)]
  ring

theorem contDiff_radialCompress (ha : 0 ≤ a) : ContDiff ℝ ∞ (radialCompress l ha) :=
  ((contDiff_const.add ((contDiff_compress ha).comp (contDiff_id.sub contDiff_const))).sub
    (contDiff_const.mul (contDiff_const.sub ((Real.smoothTransition.contDiff (n := ⊤)).comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)))))

theorem hasDerivAt_radialCompress_pos (hl : 0 < l) (ha : 0 ≤ a) (r : ℝ) :
    ∃ d : ℝ, 0 < d ∧ HasDerivAt (radialCompress l ha) d r := by
  obtain ⟨dc, hdc, hc⟩ := hasDerivAt_compress hl ha (r - 1)
  have h1 : HasDerivAt (fun r : ℝ => compress l ha (r - 1)) dc r := hc.comp_sub_const r 1
  have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (8 * r - 1)) (8 * r - 1) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) _).hasDerivAt
  have h3 : HasDerivAt (fun r : ℝ => Real.smoothTransition (8 * r - 1))
      (deriv Real.smoothTransition (8 * r - 1) * 8) r := by
    have h4 : HasDerivAt (fun r : ℝ => 8 * r - 1) 8 r := by
      simpa using ((hasDerivAt_id r).const_mul (8 : ℝ)).sub_const 1
    exact h2.comp r h4
  have h5 : HasDerivAt (radialCompress l ha)
      (0 + dc - l * a * (0 - deriv Real.smoothTransition (8 * r - 1) * 8)) r :=
    ((hasDerivAt_const r (1 : ℝ)).add h1).sub ((hasDerivAt_const r (1 : ℝ)).sub h3 |>.const_mul (l * a))
  refine ⟨_, ?_, h5⟩
  have hs : 0 ≤ deriv Real.smoothTransition (8 * r - 1) := Real.smoothTransition.monotone.deriv_nonneg
  have hla : 0 ≤ l * a := mul_nonneg hl.le ha
  nlinarith

theorem strictMono_radialCompress (hl : 0 < l) (ha : 0 ≤ a) : StrictMono (radialCompress l ha) := by
  apply strictMono_of_deriv_pos
  intro r
  obtain ⟨d, hd, hD⟩ := hasDerivAt_radialCompress_pos hl ha r
  rw [hD.deriv]
  exact hd

theorem surjective_radialCompress (hl : 0 < l) (ha : 0 ≤ a) (hla : l * (1 / 2 + a) ≤ 3 / 4) :
    Surjective (radialCompress l ha) := by
  refine (contDiff_radialCompress ha).continuous.surjective ?_ ?_
  · refine tendsto_id.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with r hr
    exact (radialCompress_of_one_le hl ha hr).symm
  · refine tendsto_id.congr' ?_
    filter_upwards [eventually_le_atBot (1 / 8)] with r hr
    exact (radialCompress_of_le hl ha hla hr).symm

/-- The radial compression profile as an order isomorphism of `ℝ`. -/
def radialCompressIso (hl : 0 < l) (ha : 0 ≤ a) (hla : l * (1 / 2 + a) ≤ 3 / 4) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective (radialCompress l ha) (strictMono_radialCompress hl ha)
    (surjective_radialCompress hl ha hla)

theorem radialCompressIso_apply (hl : 0 < l) (ha : 0 ≤ a) (hla : l * (1 / 2 + a) ≤ 3 / 4) (r : ℝ) :
    radialCompressIso hl ha hla r = radialCompress l ha r :=
  rfl

theorem contDiff_radialCompressIso_symm (hl : 0 < l) (ha : 0 ≤ a) (hla : l * (1 / 2 + a) ≤ 3 / 4) :
    ContDiff ℝ ∞ (radialCompressIso hl ha hla).symm := by
  apply Homeomorph.contDiff_symm_deriv (radialCompressIso hl ha hla).toHomeomorph
    (f' := deriv (radialCompress l ha))
  · intro r
    obtain ⟨d, hd, hD⟩ := hasDerivAt_radialCompress_pos hl ha r
    rw [hD.deriv]
    exact hd.ne'
  · intro r
    exact ((contDiff_radialCompress ha).differentiable (by simp) r).hasDerivAt
  · exact contDiff_radialCompress ha

theorem radialCompressIso_symm_of_le (hl : 0 < l) (ha : 0 ≤ a) (hla : l * (1 / 2 + a) ≤ 3 / 4)
    {t : ℝ} (ht : t ≤ 1 / 8) : (radialCompressIso hl ha hla).symm t = t := by
  conv_lhs => rw [← radialCompress_of_le hl ha hla ht, ← radialCompressIso_apply hl ha hla]
  exact OrderIso.symm_apply_apply _ _

/-! ## Radial maps of `ℝ³` -/

/-- The radial map of a profile `f`: `x ↦ x + ((f ‖x‖ - ‖x‖) / ‖x‖) • x`. -/
def radialScaleMap (f : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  x + ((f ‖x‖ - ‖x‖) / ‖x‖) • x

theorem radialScaleMap_eq_smul (f : ℝ → ℝ) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    radialScaleMap f x = (f ‖x‖ / ‖x‖) • x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h : x + ((f ‖x‖ - ‖x‖) / ‖x‖) • x = (1 + (f ‖x‖ - ‖x‖) / ‖x‖) • x := by
    rw [add_smul, one_smul]
  rw [radialScaleMap, h]
  congr 1
  field_simp
  ring

theorem radialScaleMap_zero (f : ℝ → ℝ) : radialScaleMap f 0 = 0 := by
  simp [radialScaleMap]

theorem contDiff_radialScaleMap {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {δ : ℝ} (hδ : 0 < δ)
    (hfδ : ∀ r, r < δ → f r = r) : ContDiff ℝ ∞ (radialScaleMap f) := by
  have hs : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ (Fin 3) => (f ‖x‖ - ‖x‖) / ‖x‖) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : ‖x‖ < δ
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
      rw [hfδ ‖y‖ hy, sub_self, zero_div]
    · have hx0 : x ≠ 0 := by
        intro h
        rw [h, norm_zero] at hx
        exact hx hδ
      have hn : ContDiffAt ℝ ∞ (fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖) x := contDiffAt_norm ℝ hx0
      exact ((hf.contDiffAt.comp x hn).sub hn).div hn (norm_ne_zero_iff.mpr hx0)
  exact contDiff_id.add (hs.smul contDiff_id)

theorem norm_radialScaleMap {f : ℝ → ℝ} (hf : ∀ r, 0 < r → 0 < f r) {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ≠ 0) : ‖radialScaleMap f x‖ = f ‖x‖ := by
  rw [radialScaleMap_eq_smul f hx, norm_smul]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [Real.norm_of_nonneg (div_nonneg (hf _ hn).le hn.le)]
  field_simp

theorem radialScaleMap_radialMap {f g : ℝ → ℝ} (hg : ∀ r, 0 < r → 0 < g r)
    (hfg : ∀ r, 0 < r → f (g r) = r) (x : EuclideanSpace ℝ (Fin 3)) :
    radialScaleMap f (radialScaleMap g x) = x := by
  by_cases hx : x = 0
  · rw [hx, radialScaleMap_zero, radialScaleMap_zero]
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hgx : radialScaleMap g x ≠ 0 := by
      rw [radialScaleMap_eq_smul g hx]
      exact smul_ne_zero (div_pos (hg _ hn) hn).ne' hx
    have hng : ‖radialScaleMap g x‖ = g ‖x‖ := norm_radialScaleMap hg hx
    rw [radialScaleMap_eq_smul f hgx, hng, radialScaleMap_eq_smul g hx, smul_smul, hfg _ hn]
    have hgp := hg _ hn
    rw [show ‖x‖ / g ‖x‖ * (g ‖x‖ / ‖x‖) = 1 by field_simp, one_smul]

/-! ## The radial compression diffeomorphism -/

theorem radialCompress_pos (hl : 0 < l) (ha : 0 ≤ a) (hla : l * (1 / 2 + a) ≤ 3 / 4) {r : ℝ}
    (hr : 0 < r) : 0 < radialCompress l ha r := by
  have h := strictMono_radialCompress hl ha hr
  rwa [radialCompress_of_le hl ha hla (by norm_num : (0 : ℝ) ≤ 1 / 8)] at h

theorem radialCompressIso_symm_pos (hl : 0 < l) (ha : 0 ≤ a) (hla : l * (1 / 2 + a) ≤ 3 / 4)
    {t : ℝ} (ht : 0 < t) : 0 < (radialCompressIso hl ha hla).symm t := by
  have h := (radialCompressIso hl ha hla).symm.strictMono ht
  rwa [radialCompressIso_symm_of_le hl ha hla (by norm_num : (0 : ℝ) ≤ 1 / 8)] at h

/-- **The radial compression of `ℝ³`.** -/
def radialCompressDiffeo (hl : 0 < l) (ha : 0 ≤ a) (hla : l * (1 / 2 + a) ≤ 3 / 4) :
    EuclideanSpace ℝ (Fin 3) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun := radialScaleMap (radialCompress l ha)
  invFun := radialScaleMap (radialCompressIso hl ha hla).symm
  left_inv x := radialScaleMap_radialMap (fun r hr => radialCompress_pos hl ha hla hr)
    (fun r _ => OrderIso.symm_apply_apply (radialCompressIso hl ha hla) r) x
  right_inv x := radialScaleMap_radialMap (fun r hr => radialCompressIso_symm_pos hl ha hla hr)
    (fun r _ => OrderIso.apply_symm_apply (radialCompressIso hl ha hla) r) x
  contMDiff_toFun := (contDiff_radialScaleMap (contDiff_radialCompress ha) (by norm_num : (0 : ℝ) < 1 / 8)
    (fun r hr => radialCompress_of_le hl ha hla hr.le)).contMDiff
  contMDiff_invFun := (contDiff_radialScaleMap (contDiff_radialCompressIso_symm hl ha hla)
    (by norm_num : (0 : ℝ) < 1 / 8)
    (fun r hr => radialCompressIso_symm_of_le hl ha hla hr.le)).contMDiff

theorem radialCompressDiffeo_apply (hl : 0 < l) (ha : 0 ≤ a) (hla : l * (1 / 2 + a) ≤ 3 / 4)
    (x : EuclideanSpace ℝ (Fin 3)) :
    radialCompressDiffeo hl ha hla x = radialScaleMap (radialCompress l ha) x :=
  rfl

theorem norm_radialCompressDiffeo (hl : 0 < l) (ha : 0 ≤ a) (hla : l * (1 / 2 + a) ≤ 3 / 4)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    ‖radialCompressDiffeo hl ha hla x‖ = radialCompress l ha ‖x‖ := by
  rw [radialCompressDiffeo_apply]
  exact norm_radialScaleMap (fun r hr => radialCompress_pos hl ha hla hr) hx

theorem radialCompressDiffeo_image_closedBall (hl : 0 < l) (ha : 0 ≤ a)
    (hla : l * (1 / 2 + a) ≤ 3 / 4) :
    radialCompressDiffeo hl ha hla '' closedBall 0 1 = closedBall 0 1 := by
  have hiff : ∀ x : EuclideanSpace ℝ (Fin 3),
      ‖radialCompressDiffeo hl ha hla x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
    intro x
    by_cases hx : x = 0
    · rw [hx, radialCompressDiffeo_apply, radialScaleMap_zero, norm_zero]
    · rw [norm_radialCompressDiffeo hl ha hla hx]
      conv_lhs => rw [← radialCompress_of_one_le hl ha (le_refl (1 : ℝ))]
      exact (strictMono_radialCompress hl ha).le_iff_le
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact mem_closedBall_zero_iff.mpr ((hiff x).mpr (mem_closedBall_zero_iff.mp hx))
  · intro hy
    refine ⟨(radialCompressDiffeo hl ha hla).symm y, ?_, by simp⟩
    apply mem_closedBall_zero_iff.mpr
    rw [← hiff, Diffeomorph.apply_symm_apply]
    exact mem_closedBall_zero_iff.mp hy

/-- The direction of a positive multiple. -/
theorem sphereDirection_smul_of_pos (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) {c : ℝ} (hc : 0 < c) :
    DifferentialGeometry.Topology.Manifold.sphereDirection v (c • x) =
      DifferentialGeometry.Topology.Manifold.sphereDirection v x := by
  apply Subtype.ext
  rw [DifferentialGeometry.Topology.Manifold.coe_sphereDirection v (smul_ne_zero hc.ne' hx),
    DifferentialGeometry.Topology.Manifold.coe_sphereDirection v hx, norm_smul,
    Real.norm_of_nonneg hc.le, smul_smul]
  congr 1
  field_simp

theorem southCapMap_smul_of_pos {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) {c : ℝ} (hc : 0 < c) :
    southCapMap (c • x) = ((southCapMap x).1, c * ‖x‖ - 1) := by
  rw [southCapMap_apply, southCapMap_apply, sphereDirection_smul_of_pos _ hx hc, norm_smul,
    Real.norm_of_nonneg hc.le]

/-- **The radial compression is the compression in the cap charts** (on `{‖x‖ ≥ 1/4}`). -/
theorem capMap_radialCompressDiffeo (hl : 0 < l) (ha : 0 ≤ a) (hla : l * (1 / 2 + a) ≤ 3 / 4)
    (b : Bool) {x : EuclideanSpace ℝ (Fin 3)} (hx : 1 / 4 ≤ ‖x‖) :
    capMap b (radialCompressDiffeo hl ha hla x) =
      ((capMap b x).1, compress l ha (capMap b x).2) := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    norm_num at hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hc : 0 < radialCompress l ha ‖x‖ / ‖x‖ := div_pos (radialCompress_pos hl ha hla hn) hn
  have hcx : radialCompress l ha ‖x‖ / ‖x‖ * ‖x‖ - 1 = compress l ha (‖x‖ - 1) := by
    rw [div_mul_cancel₀ _ hn.ne', radialCompress_of_quarter_le ha hx]
    ring
  rw [radialCompressDiffeo_apply, radialScaleMap_eq_smul _ hx0]
  cases b
  · change southCapMap _ = ((southCapMap x).1, compress l ha (southCapMap x).2)
    rw [southCapMap_smul_of_pos hx0 hc, hcx]
    rfl
  · change southCapMap (reflectThree _) =
      ((southCapMap (reflectThree x)).1, compress l ha (southCapMap (reflectThree x)).2)
    have hr0 : reflectThree x ≠ 0 := fun h => hx0 (reflectThree.map_eq_zero_iff.mp h)
    rw [LinearIsometryEquiv.map_smul, southCapMap_smul_of_pos hr0 hc, norm_reflectThree, hcx,
      southCapMap_apply (reflectThree x), norm_reflectThree]

end GC.GraphManifold.Assembly
