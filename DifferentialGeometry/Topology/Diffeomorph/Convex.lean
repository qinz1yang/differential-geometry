import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.FiniteDimension
import DifferentialGeometry.Topology.Diffeomorph.Radial
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

open Set
open scoped Topology ContDiff Manifold

namespace Real

private theorem convex_neg_at_zero_neg_between {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hzero : f 0 < 0)
    {r s : ℝ} (hr : 0 < r) (hrs : r < s) (hfs : f s ≤ 0) : f r < 0 := by
  have hs : 0 < s := hr.trans hrs
  have htpos : 0 < r / s := div_pos hr hs
  have htlt : r / s < 1 := (div_lt_one hs).mpr hrs
  have h := hf.2 (Set.mem_univ 0) (Set.mem_univ s)
    (sub_pos.mpr htlt).le htpos.le (by ring : 1 - r / s + r / s = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ r hs.ne'] at h
  have hn := mul_neg_of_pos_of_neg (sub_pos.mpr htlt) hzero
  have hn' := mul_nonpos_of_nonneg_of_nonpos htpos.le hfs
  linarith

private theorem convex_neg_at_zero_unique_positive_root {f : ℝ → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hzero : f 0 < 0)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hfa : f a = 0) (hfb : f b = 0) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact False.elim ((convex_neg_at_zero_neg_between hf hzero ha hab hfb.le).ne hfa)
  · exact hab
  · exact False.elim ((convex_neg_at_zero_neg_between hf hzero hb hba hfa.le).ne hfb)

private theorem convex_value_sub_le_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ConvexOn ℝ Set.univ f) {c p : E} (hp : DifferentiableAt ℝ f p) :
    f p - f c ≤ fderiv ℝ f p (p - c) := by
  have hconv : ConvexOn ℝ Set.univ (f ∘ AffineMap.lineMap (k := ℝ) c p) := by
    simpa only [Set.preimage_univ] using hf.comp_affineMap (AffineMap.lineMap (k := ℝ) c p)
  have hd : HasFDerivAt f (fderiv ℝ f p) (AffineMap.lineMap (k := ℝ) c p (1 : ℝ)) := by
    simpa only [AffineMap.lineMap_apply_one] using hp.hasFDerivAt
  have hline := hd.comp_hasDerivAt 1 (AffineMap.hasDerivAt_lineMap (a := c) (b := p))
  have h := hconv.slope_le_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    (by norm_num : (0 : ℝ) < 1) hline
  simpa only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_one,
    AffineMap.lineMap_apply_zero, sub_zero, div_one] using h

private theorem convex_sublevel_exists_unique_ray_root
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hc : Continuous f)
    (hb : Bornology.IsBounded {x : E | f x ≤ 0})
    {c v : E} (hneg : f c < 0) (hv : v ≠ 0) :
    ∃! r : ℝ, 0 < r ∧ f (r • v + c) = 0 := by
  obtain ⟨M, hM, hbound⟩ := hb.exists_pos_norm_lt
  let b : ℝ := (M + ‖c‖ + 1) / ‖v‖
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hbpos : 0 < b := div_pos (by positivity) hn
  have hfar : 0 < f (b • v + c) := by
    by_contra h
    have hp := hbound (b • v + c) (le_of_not_gt h)
    have hnorm : ‖b • v‖ ≤ ‖b • v + c‖ + ‖c‖ := by
      simpa only [add_sub_cancel_right] using norm_sub_le (b • v + c) c
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hbpos] at hnorm
    have heq : b * ‖v‖ = M + ‖c‖ + 1 := div_mul_cancel₀ _ hn.ne'
    rw [heq] at hnorm
    linarith
  have hconv : ConvexOn ℝ univ (fun r : ℝ => f (r • v + c)) := by
    have h := hf.comp_affineMap (AffineMap.lineMap (k := ℝ) c (v + c))
    rw [preimage_univ] at h
    convert! h using 1
    funext r
    simp [AffineMap.lineMap_apply_module']
  have hzero : f ((0 : ℝ) • v + c) < 0 := by simpa only [zero_smul, zero_add] using hneg
  have hcont : Continuous (fun r : ℝ => f (r • v + c)) :=
    hc.comp ((continuous_id.smul continuous_const).add continuous_const)
  obtain ⟨r, hr, hroot⟩ := intermediate_value_Icc hbpos.le hcont.continuousOn
    ⟨hzero.le, hfar.le⟩
  have hrpos : 0 < r := by
    by_contra h
    have hrzero : r = 0 := le_antisymm (le_of_not_gt h) hr.1
    rw [hrzero] at hroot
    exact hzero.ne hroot
  refine ⟨r, ⟨hrpos, hroot⟩, ?_⟩
  intro s hs
  exact convex_neg_at_zero_unique_positive_root hconv hzero hs.1 hrpos hs.2 hroot

private theorem convex_ray_root_derivative_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) {c v : E} {r : ℝ} (hr : 0 < r)
    (hneg : f c < 0) (hroot : f (r • v + c) = 0)
    (hd : DifferentiableAt ℝ f (r • v + c)) :
    0 < fderiv ℝ f (r • v + c) v := by
  have h := convex_value_sub_le_fderiv hf hd (c := c)
  rw [hroot, add_sub_cancel_right, map_smul, smul_eq_mul] at h
  nlinarith

end Real

namespace Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private noncomputable def convexSublevelRadius (f : E → ℝ) (c v : E) : ℝ := by
  classical
  exact if h : ∃ r : ℝ, 0 < r ∧ f (r • v + c) = 0 then Classical.choose h else 0

private theorem convexSublevelRadius_spec {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hc : Continuous f)
    (hb : Bornology.IsBounded {x : E | f x ≤ 0})
    {c v : E} (hneg : f c < 0) (hv : v ≠ 0) :
    0 < convexSublevelRadius f c v ∧ f (convexSublevelRadius f c v • v + c) = 0 := by
  have hex := (convex_sublevel_exists_unique_ray_root hf hc hb hneg hv).exists
  rw [convexSublevelRadius, dif_pos hex]
  exact Classical.choose_spec hex

private theorem convexSublevelRadius_ray_convex {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (c v : E) :
    ConvexOn ℝ univ (fun r : ℝ => f (r • v + c)) := by
  have h := hf.comp_affineMap (AffineMap.lineMap (k := ℝ) c (v + c))
  rw [preimage_univ] at h
  convert! h using 1
  funext r
  simp [AffineMap.lineMap_apply_module']

private theorem convexSublevelRadius_sublevel_iff {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hc : Continuous f)
    (hb : Bornology.IsBounded {x : E | f x ≤ 0})
    {c v : E} (hneg : f c < 0) (hv : v ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    f (r • v + c) ≤ 0 ↔ r ≤ convexSublevelRadius f c v := by
  obtain ⟨hRpos, hRroot⟩ := convexSublevelRadius_spec hf hc hb hneg hv
  have hzero : f ((0 : ℝ) • v + c) < 0 := by
    simpa only [zero_smul, zero_add] using hneg
  have hconv := convexSublevelRadius_ray_convex hf c v
  constructor
  · intro h
    by_contra hn
    exact (convex_neg_at_zero_neg_between hconv hzero hRpos (lt_of_not_ge hn) h).ne hRroot
  · intro h
    have hs : Convex ℝ {s : ℝ | f (s • v + c) ≤ 0} := by
      simpa only [mem_univ, true_and] using hconv.convex_le 0
    exact hs.ordConnected.out hzero.le hRroot.le ⟨hr, h⟩

private theorem convexSublevelRadius_contDiffAt [CompleteSpace E] {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hc : ContDiff ℝ ∞ f)
    (hb : Bornology.IsBounded {x : E | f x ≤ 0})
    {c v : E} (hneg : f c < 0) (hv : v ≠ 0) :
    ContDiffAt ℝ ∞ (convexSublevelRadius f c) v := by
  let x : ℝ := convexSublevelRadius f c v
  let p : E := x • v + c
  let F : E × ℝ → ℝ := fun z => f (z.2 • z.1 + c)
  have hF : ContDiff ℝ ∞ F := hc.comp
    ((contDiff_snd.smul contDiff_fst).add contDiff_const)
  obtain ⟨hxpos, hxroot⟩ := convexSublevelRadius_spec hf hc.continuous hb hneg hv
  have hFx : F (v, x) = 0 := hxroot
  let d : ℝ := fderiv ℝ f p v
  have hd : 0 < d := convex_ray_root_derivative_pos hf hxpos hneg hxroot
    (hc.differentiable (by simp) p)
  have hscalar : HasDerivAt (fun r : ℝ => f (r • v + c)) d x := by
    have hpath := ((hasDerivAt_id x).smul_const v).add_const c
    have hchain := (hc.differentiable (by simp) p).hasFDerivAt.comp_hasDerivAt x hpath
    convert! hchain using 1
    simp only [one_smul, d]
  have hpartial : fderiv ℝ F (v, x) ∘L ContinuousLinearMap.inr ℝ E ℝ =
      ContinuousLinearMap.toSpanSingleton ℝ d := by
    have hrestrict := (hF.differentiable (by simp) (v, x)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) v x)
    exact hrestrict.unique hscalar.hasFDerivAt
  have hi : (fderiv ℝ F (v, x) ∘L ContinuousLinearMap.inr ℝ E ℝ).IsInvertible := by
    rw [hpartial]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 d hd.ne'), ?_⟩
    ext
    simp
  let ψ : E → ℝ := hF.contDiffAt.implicitFunction (by simp) hi
  have hψ : ContDiffAt ℝ ∞ ψ v := hF.contDiffAt.contDiffAt_implicitFunction (by simp) hi
  have hψself : ψ v = x := hF.contDiffAt.implicitFunction_apply_self (by simp) hi
  have hψbase : 0 < ψ v := by rw [hψself]; exact hxpos
  have hψpos : ∀ᶠ w in nhds v, 0 < ψ w :=
    hψ.continuousAt.eventually (eventually_gt_nhds hψbase)
  apply hψ.congr_of_eventuallyEq
  filter_upwards [hF.contDiffAt.eventually_apply_implicitFunction (by simp) hi,
    hψpos, eventually_ne_nhds hv] with w hw hwpos hwne
  exact (convex_sublevel_exists_unique_ray_root hf hc.continuous hb hneg hwne).unique
    (convexSublevelRadius_spec hf hc.continuous hb hneg hwne) ⟨hwpos, hw.trans hFx⟩

end Real

namespace Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem convexSublevelRadius_zero_iff {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hc : Continuous f)
    (hb : Bornology.IsBounded {x : E | f x ≤ 0})
    {c v : E} (hneg : f c < 0) (hv : v ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    f (r • v + c) = 0 ↔ r = convexSublevelRadius f c v := by
  obtain ⟨hRpos, hRroot⟩ := convexSublevelRadius_spec hf hc hb hneg hv
  have hzero : f ((0 : ℝ) • v + c) < 0 := by
    simpa only [zero_smul, zero_add] using hneg
  constructor
  · intro h
    have hrpos : 0 < r := by
      by_contra hn
      have hrzero : r = 0 := le_antisymm (le_of_not_gt hn) hr
      rw [hrzero] at h
      exact hzero.ne h
    exact convex_neg_at_zero_unique_positive_root (convexSublevelRadius_ray_convex hf c v)
      hzero hrpos hRpos h hRroot
  · rintro rfl
    exact hRroot

private theorem convexSublevelRadius_neg_iff {f : E → ℝ}
    (hf : ConvexOn ℝ univ f) (hc : Continuous f)
    (hb : Bornology.IsBounded {x : E | f x ≤ 0})
    {c v : E} (hneg : f c < 0) (hv : v ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    f (r • v + c) < 0 ↔ r < convexSublevelRadius f c v := by
  obtain ⟨hRpos, hRroot⟩ := convexSublevelRadius_spec hf hc hb hneg hv
  have hzero : f ((0 : ℝ) • v + c) < 0 := by
    simpa only [zero_smul, zero_add] using hneg
  have hconv := convexSublevelRadius_ray_convex hf c v
  constructor
  · intro h
    by_contra hn
    rcases (le_of_not_gt hn).eq_or_lt with heq | hlt
    · exact h.ne (heq ▸ hRroot)
    · exact (convex_neg_at_zero_neg_between hconv hzero hRpos hlt h.le).ne hRroot
  · intro h
    rcases hr.eq_or_lt with heq | hpos
    · simpa only [← heq] using hzero
    · exact convex_neg_at_zero_neg_between hconv hzero hpos h hRroot.le

end Real

namespace Real

private theorem exists_smooth_convex_sublevel_radius
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} [Fact (Module.finrank ℝ E = d + 1)]
    {f : E → ℝ} (hf : ConvexOn ℝ univ f) (hc : ContDiff ℝ ∞ f)
    (hb : Bornology.IsBounded {x : E | f x ≤ 0}) {c : E} (hneg : f c < 0) :
    ∃ R : Metric.sphere (0 : E) 1 → ℝ,
      ContMDiff (𝓡 d) 𝓘(ℝ, ℝ) ∞ R ∧
      (∀ θ : Metric.sphere (0 : E) 1, 0 < R θ) ∧
      ∀ (θ : Metric.sphere (0 : E) 1) (r : ℝ), 0 ≤ r →
        (f (r • θ.val + c) < 0 ↔ r < R θ) ∧
        (f (r • θ.val + c) = 0 ↔ r = R θ) ∧
        (f (r • θ.val + c) ≤ 0 ↔ r ≤ R θ) := by
  let : FiniteDimensional ℝ E := Module.finite_of_finrank_eq_succ
    (Fact.out : Module.finrank ℝ E = d + 1)
  let R : Metric.sphere (0 : E) 1 → ℝ := fun θ => convexSublevelRadius f c θ.val
  refine ⟨R, ?_, ?_, ?_⟩
  · intro θ
    exact (convexSublevelRadius_contDiffAt hf hc hb hneg (ne_zero_of_mem_unit_sphere θ)).comp_contMDiffAt
      (f := fun η : Metric.sphere (0 : E) 1 => η.val) (x := θ) (contMDiff_coe_sphere θ)
  · exact fun θ => (convexSublevelRadius_spec hf hc.continuous hb hneg
      (ne_zero_of_mem_unit_sphere θ)).1
  · intro θ r hr
    exact ⟨convexSublevelRadius_neg_iff hf hc.continuous hb hneg
        (ne_zero_of_mem_unit_sphere θ) hr,
      convexSublevelRadius_zero_iff hf hc.continuous hb hneg
        (ne_zero_of_mem_unit_sphere θ) hr,
      convexSublevelRadius_sublevel_iff hf hc.continuous hb hneg
        (ne_zero_of_mem_unit_sphere θ) hr⟩

end Real

namespace Diffeomorph

private theorem exists_diffeomorph_convex_sublevel_of_rank_succ
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} [Fact (Module.finrank ℝ E = d + 1)]
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hc : ContDiff ℝ ∞ f)
    (hb : Bornology.IsBounded {x : E | f x ≤ 0}) {c : E} (hneg : f c < 0) :
    ∃ F : E ≃ₘ[ℝ] E,
      F 0 = c ∧ F.symm c = 0 ∧
      F '' Metric.closedBall (0 : E) 1 = {x : E | f x ≤ 0} ∧
      F '' Metric.ball (0 : E) 1 = {x : E | f x < 0} ∧
      F '' Metric.sphere (0 : E) 1 = {x : E | f x = 0} := by
  let D : E ≃ₘ[ℝ] E :=
    { toEquiv := Equiv.addRight c
      contMDiff_toFun := (contDiff_id.add contDiff_const).contMDiff
      contMDiff_invFun := (contDiff_id.add contDiff_const).contMDiff }
  have hD (x : E) : D x = x + c := rfl
  obtain ⟨R, hR, hRpos, hregions⟩ :=
    Real.exists_smooth_convex_sublevel_radius (d := d) hf hc hb hneg
  have hdecomp (z : E) (hz : z ≠ c) :
      ∃ θ : Metric.sphere (0 : E) 1, ∃ s : ℝ, 0 < s ∧ z = s • θ.val + c := by
    let p := homeomorphUnitSphereProd E (⟨z - c, sub_ne_zero.mpr hz⟩ : ({0}ᶜ : Set E))
    have hp : p.2.val • p.1.val = z - c :=
      congrArg Subtype.val ((homeomorphUnitSphereProd E).symm_apply_apply
        ⟨z - c, sub_ne_zero.mpr hz⟩)
    exact ⟨p.1, p.2.val, p.2.property, by rw [hp, sub_add_cancel]⟩
  have hclosed : D ''
      {z | z = 0 ∨ ∃ θ : Metric.sphere (0 : E) 1,
        ∃ s : ℝ, 0 < s ∧ s ≤ R θ ∧ z = s • θ.val} = {z : E | f z ≤ 0} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | ⟨θ, s, hs, hsr, rfl⟩
      · change f (D 0) ≤ 0
        rw [hD, zero_add]
        exact hneg.le
      · exact (hregions θ s hs.le).2.2.mpr hsr
    · intro hz
      by_cases hzc : z = c
      · refine ⟨0, Or.inl rfl, ?_⟩
        simpa only [hD, zero_add] using hzc.symm
      · obtain ⟨θ, s, hs, rfl⟩ := hdecomp z hzc
        exact ⟨s • θ.val, Or.inr ⟨θ, s, hs, (hregions θ s hs.le).2.2.mp hz, rfl⟩, hD _⟩
  have hopen : D ''
      {z | z = 0 ∨ ∃ θ : Metric.sphere (0 : E) 1,
        ∃ s : ℝ, 0 < s ∧ s < R θ ∧ z = s • θ.val} = {z : E | f z < 0} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with rfl | ⟨θ, s, hs, hsr, rfl⟩
      · change f (D 0) < 0
        rw [hD, zero_add]
        exact hneg
      · exact (hregions θ s hs.le).1.mpr hsr
    · intro hz
      by_cases hzc : z = c
      · refine ⟨0, Or.inl rfl, ?_⟩
        simpa only [hD, zero_add] using hzc.symm
      · obtain ⟨θ, s, hs, rfl⟩ := hdecomp z hzc
        exact ⟨s • θ.val, Or.inr ⟨θ, s, hs, (hregions θ s hs.le).1.mp hz, rfl⟩, hD _⟩
  have hboundary : D '' Set.range
      (fun θ : Metric.sphere (0 : E) 1 => R θ • θ.val) = {z : E | f z = 0} := by
    ext z
    constructor
    · rintro ⟨x, ⟨θ, rfl⟩, rfl⟩
      exact (hregions θ (R θ) (hRpos θ).le).2.1.mpr rfl
    · intro hz
      have hzc : z ≠ c := by
        rintro rfl
        exact hneg.ne hz
      obtain ⟨θ, s, hs, rfl⟩ := hdecomp z hzc
      have hsR : s = R θ := (hregions θ s hs.le).2.1.mp hz
      exact ⟨R θ • θ.val, ⟨θ, rfl⟩, by rw [← hsR, hD]⟩
  obtain ⟨G, hzero, _, _, hball, hopenball, hsphere⟩ :=
    exists_diffeomorph_eq_smul_on_sphere (d := d) R hR hRpos
  let F := G.trans D
  have hFzero : F 0 = c := by change D (G 0) = c; rw [hzero, hD, zero_add]
  refine ⟨F, hFzero, ?_, ?_, ?_, ?_⟩
  · rw [← hFzero, Diffeomorph.symm_apply_apply]
  · change (D ∘ G) '' Metric.closedBall (0 : E) 1 = _
    rw [Set.image_comp, hball]
    exact hclosed
  · change (D ∘ G) '' Metric.ball (0 : E) 1 = _
    rw [Set.image_comp, hopenball]
    exact hopen
  · change (D ∘ G) '' Metric.sphere (0 : E) 1 = _
    rw [Set.image_comp, hsphere]
    exact hboundary

end Diffeomorph

namespace Diffeomorph

theorem exists_diffeomorph_convex_sublevel
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (hc : ContDiff ℝ ∞ f)
    (hb : Bornology.IsBounded {x : E | f x ≤ 0}) {c : E} (hneg : f c < 0) :
    ∃ F : E ≃ₘ[ℝ] E,
      F 0 = c ∧ F.symm c = 0 ∧
      F '' Metric.closedBall (0 : E) 1 = {x : E | f x ≤ 0} ∧
      F '' Metric.ball (0 : E) 1 = {x : E | f x < 0} ∧
      F '' Metric.sphere (0 : E) 1 = {x : E | f x = 0} := by
  rcases subsingleton_or_nontrivial E with h | h
  · let : Subsingleton E := h
    have hfzero : f (0 : E) < 0 := by simpa only [Subsingleton.elim c 0] using hneg
    refine ⟨Diffeomorph.refl 𝓘(ℝ, E) E ∞, Subsingleton.elim _ _,
      Subsingleton.elim _ _, ?_, ?_, ?_⟩
    · change (id : E → E) '' Metric.closedBall 0 1 = _
      rw [Set.image_id]
      ext x
      simp [Metric.mem_closedBall, Subsingleton.elim x 0, hfzero.le]
    · change (id : E → E) '' Metric.ball 0 1 = _
      rw [Set.image_id]
      ext x
      simp [Metric.mem_ball, Subsingleton.elim x 0, hfzero]
    · change (id : E → E) '' Metric.sphere 0 1 = _
      rw [Set.image_id]
      ext x
      simp [Subsingleton.elim x 0, hfzero.ne]
  · let : Nontrivial E := h
    have hpos : 0 < Module.finrank ℝ E :=
      (Module.finrank_pos_iff_of_free ℝ E).mpr inferInstance
    obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    let : Fact (Module.finrank ℝ E = d + 1) := ⟨hd⟩
    exact exists_diffeomorph_convex_sublevel_of_rank_succ (d := d) hf hc hb hneg

end Diffeomorph
