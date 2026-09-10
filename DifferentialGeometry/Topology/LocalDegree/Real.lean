import DifferentialGeometry.Topology.LocalDegree.ZeroSphere
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inverse

set_option autoImplicit false

open Filter Metric Set
open scoped Topology

noncomputable section

namespace Poincare.LocalDegree

structure RealIsolatingRadius (f : ℝ → ℝ) (x R : ℝ) : Prop where
  pos : 0 < R
  continuousOn : ContinuousOn f (closedBall x R)
  zero_iff : ∀ y ∈ closedBall x R, f y = 0 ↔ y = x


def realIsolatedZero (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ R, RealIsolatingRadius f x R

namespace RealIsolatingRadius

variable {f g : ℝ → ℝ} {x R : ℝ} (h : RealIsolatingRadius f x R)

include h


theorem zero : f x = 0 := (h.zero_iff x (mem_closedBall_self h.pos.le)).mpr rfl


theorem nonzero (y : ℝ) (hy : y ∈ closedBall x R) (hne : y ≠ x) : f y ≠ 0 :=
  mt (h.zero_iff y hy).mp hne


theorem mono {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) : RealIsolatingRadius f x r where
  pos := hr
  continuousOn := h.continuousOn.mono (closedBall_subset_closedBall hrR)
  zero_iff y hy := h.zero_iff y (closedBall_subset_closedBall hrR hy)


theorem congr (hfg : EqOn f g (closedBall x R)) : RealIsolatingRadius g x R where
  pos := h.pos
  continuousOn := h.continuousOn.congr hfg.symm
  zero_iff y hy := by rw [← hfg hy]; exact h.zero_iff y hy

end RealIsolatingRadius

private def radiusSphereMap {f : ℝ → ℝ} {x R : ℝ} (h : RealIsolatingRadius f x R) :
    C(ZeroSphere, ZeroSphere) :=
  sphereMap f x R h.continuousOn h.nonzero ⟨R, h.pos, le_rfl⟩

private theorem radius_degree_eq {f : ℝ → ℝ} {x R S : ℝ}
    (hR : RealIsolatingRadius f x R) (hS : RealIsolatingRadius f x S) :
    zeroSphereDegree (radiusSphereMap hR) = zeroSphereDegree (radiusSphereMap hS) := by
  let r : ℝ := min R S
  have hr : 0 < r := lt_min hR.pos hS.pos
  have hrR : r ≤ R := min_le_left _ _
  have hrS : r ≤ S := min_le_right _ _
  calc
    zeroSphereDegree (radiusSphereMap hR) =
        zeroSphereDegree (sphereMap f x R hR.continuousOn hR.nonzero ⟨r, hr, hrR⟩) :=
      zeroSphereDegree_sphereMap_eq _ _ _ _ _ _ _
    _ = zeroSphereDegree (sphereMap f x S hS.continuousOn hS.nonzero ⟨r, hr, hrS⟩) := by
      congr 1
    _ = zeroSphereDegree (radiusSphereMap hS) :=
      zeroSphereDegree_sphereMap_eq _ _ _ _ _ _ _

def realLocalDegree (f : ℝ → ℝ) (x : ℝ) (h : realIsolatedZero f x) : ℤ :=
  zeroSphereDegree (radiusSphereMap h.choose_spec)

theorem realLocalDegree_eq_sphereDegree {f : ℝ → ℝ} {x : ℝ} (h : realIsolatedZero f x)
    {R : ℝ} (hR : RealIsolatingRadius f x R) (r : Ioc (0 : ℝ) R) :
    realLocalDegree f x h = zeroSphereDegree (sphereMap f x R hR.continuousOn hR.nonzero r) := by
  exact (radius_degree_eq h.choose_spec hR).trans
    (zeroSphereDegree_sphereMap_eq _ _ _ _ _ _ _)

theorem realLocalDegree_smul_generator {f : ℝ → ℝ} {x : ℝ} (h : realIsolatedZero f x)
    {R : ℝ} (hR : RealIsolatingRadius f x R) (r : Ioc (0 : ℝ) R) :
    realLocalDegree f x h • zeroSphereGenerator =
      zeroSphereReducedMap (sphereMap f x R hR.continuousOn hR.nonzero r) zeroSphereGenerator := by
  rw [realLocalDegree_eq_sphereDegree h hR r]
  exact zeroSphereDegree_smul_generator _

theorem realIsolatedZero_of_nhds {f : ℝ → ℝ} {x : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 x) (hc : ContinuousOn f s) (hz : f x = 0)
    (hzero : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0) : realIsolatedZero f x := by
  have hs' : ∀ᶠ y in 𝓝 x, y ∈ s := hs
  have hn := hs'.and (eventually_nhdsWithin_iff.mp hzero)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨ε / 2, ?_⟩
  have hsub : closedBall x (ε / 2) ⊆ s ∩ {y | y ≠ x → f y ≠ 0} := by
    intro y hy
    apply hball
    exact (closedBall_subset_ball (by linarith)) hy
  exact {
    pos := by positivity
    continuousOn := hc.mono (fun y hy ↦ (hsub hy).1)
    zero_iff := fun y hy ↦ ⟨fun hfy ↦ by
      by_contra hne
      exact (hsub hy).2 hne hfy, fun hyx ↦ hyx ▸ hz⟩ }


theorem realIsolatedZero_congr {f g : ℝ → ℝ} {x : ℝ} (hfg : f =ᶠ[𝓝 x] g) :
    realIsolatedZero f x ↔ realIsolatedZero g x := by
  suffices transfer : ∀ {f g : ℝ → ℝ}, f =ᶠ[𝓝 x] g →
      realIsolatedZero f x → realIsolatedZero g x from
    ⟨transfer hfg, transfer hfg.symm⟩
  intro f g hfg ⟨R, hR⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hfg
  let r := min R (ε / 2)
  have hr : 0 < r := lt_min hR.pos (by positivity)
  have hrr : r ≤ R := min_le_left _ _
  refine ⟨r, (hR.mono hr hrr).congr ?_⟩
  intro y hy
  exact hball (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _)
    (by linarith)) hy)


theorem realLocalDegree_congr {f g : ℝ → ℝ} {x : ℝ}
    (hf : realIsolatedZero f x) (hg : realIsolatedZero g x) (hfg : f =ᶠ[𝓝 x] g) :
    realLocalDegree f x hf = realLocalDegree g x hg := by
  let R := hf.choose
  have hR : RealIsolatingRadius f x R := hf.choose_spec
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hfg
  let r := min R (ε / 2)
  have hr : 0 < r := lt_min hR.pos (by positivity)
  have hrr : r ≤ R := min_le_left _ _
  have heq : EqOn f g (closedBall x r) := fun y hy ↦
    hball (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith)) hy)
  have hfr := hR.mono hr hrr
  have hgr := hfr.congr heq
  rw [realLocalDegree_eq_sphereDegree hf hfr ⟨r, hr, le_rfl⟩,
    realLocalDegree_eq_sphereDegree hg hgr ⟨r, hr, le_rfl⟩]
  congr 1
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  simp only [sphereMap_apply]
  rw [heq (by
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.le, norm_eq_of_mem_sphere v, mul_one])]

private theorem normalized_eq_one_iff (a : ℝ) : ‖a‖⁻¹ * a = 1 ↔ 0 < a := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · simp [Real.norm_eq_abs, abs_of_neg ha, inv_neg, ha.ne, not_lt_of_gt ha]
    norm_num
  · norm_num
  · simp [Real.norm_of_nonneg ha.le, inv_mul_cancel₀ ha.ne', ha]

private theorem sphereMap_eq_positive_iff {f : ℝ → ℝ} {x R : ℝ}
    (hR : RealIsolatingRadius f x R) (r : Ioc (0 : ℝ) R) (v : ZeroSphere) :
    sphereMap f x R hR.continuousOn hR.nonzero r v = zeroSpherePositive ↔
      0 < f (x + (r : ℝ) * (v : ℝ)) := by
  rw [Subtype.ext_iff, sphereMap_apply]
  exact normalized_eq_one_iff _

theorem realLocalDegree_eq_endpoints {f : ℝ → ℝ} {x : ℝ} (h : realIsolatedZero f x)
    {R : ℝ} (hR : RealIsolatingRadius f x R) (r : Ioc (0 : ℝ) R) :
    realLocalDegree f x h =
      (if 0 < f (x + (r : ℝ)) then 1 else 0) -
        (if 0 < f (x - (r : ℝ)) then 1 else 0) := by
  rw [realLocalDegree_eq_sphereDegree h hR r, zeroSphereDegree_eq]
  simp only [sphereMap_eq_positive_iff hR r zeroSpherePositive,
    sphereMap_eq_positive_iff hR r zeroSphereNegative]
  simp [zeroSpherePositive, zeroSphereNegative, sub_eq_add_neg]


theorem realIsolatedZero_of_hasDerivAt {f : ℝ → ℝ} {x d : ℝ} {s : Set ℝ}
    (hs : s ∈ 𝓝 x) (hc : ContinuousOn f s) (hz : f x = 0)
    (hd : HasDerivAt f d x) (hne : d ≠ 0) : realIsolatedZero f x :=
  realIsolatedZero_of_nhds hs hc hz (hd.eventually_ne hne)

private theorem exists_radius_property {f : ℝ → ℝ} {x R : ℝ} (hR : 0 < R)
    {P : ℝ → Prop} (hP : ∀ᶠ y in 𝓝[≠] x, P (slope f x y)) :
    ∃ r : Ioc (0 : ℝ) R,
      P (slope f x (x + (r : ℝ))) ∧ P (slope f x (x - (r : ℝ))) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hP)
  let r : ℝ := min R (ε / 2)
  have hr : 0 < r := lt_min hR (by positivity)
  have hrε : r < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨⟨r, hr, min_le_left _ _⟩, ?_, ?_⟩
  · apply hball
    · simpa [mem_ball, Real.dist_eq, abs_of_pos hr] using hrε
    · change x + r ≠ x
      linarith
  · apply hball
    · simpa [mem_ball, Real.dist_eq, show x - r - x = -r by ring, abs_of_pos hr] using hrε
    · change x - r ≠ x
      linarith

theorem realLocalDegree_eq_sign_of_hasDerivAt {f : ℝ → ℝ} {x d : ℝ}
    (h : realIsolatedZero f x) (hd : HasDerivAt f d x) (hne : d ≠ 0) :
    realLocalDegree f x h = (SignType.sign d : ℤ) := by
  let R := h.choose
  have hR : RealIsolatingRadius f x R := h.choose_spec
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · obtain ⟨r, hp, hm⟩ := exists_radius_property hR.pos
      (hd.tendsto_slope.eventually (eventually_lt_nhds hneg))
    have hp' : f (x + (r : ℝ)) < 0 := by
      have hs : f (x + (r : ℝ)) / (r : ℝ) < 0 := by
        simpa [slope_def_field, hR.zero] using hp
      rcases div_neg_iff.mp hs with h | h
      · exact (not_lt_of_gt r.property.1 h.2).elim
      · exact h.1
    have hm' : 0 < f (x - (r : ℝ)) := by
      have hs : f (x - (r : ℝ)) / -(r : ℝ) < 0 := by
        simpa [slope_def_field, hR.zero, show x - (r : ℝ) - x = -(r : ℝ) by ring] using hm
      rcases div_neg_iff.mp hs with h | h
      · exact h.1
      · linarith [r.property.1, h.2]
    rw [realLocalDegree_eq_endpoints h hR r]
    simp [not_lt_of_gt hp', hm', sign_neg hneg]
  · obtain ⟨r, hp, hm⟩ := exists_radius_property hR.pos
      (hd.tendsto_slope.eventually (eventually_gt_nhds hpos))
    have hp' : 0 < f (x + (r : ℝ)) := by
      have hs : 0 < f (x + (r : ℝ)) / (r : ℝ) := by
        simpa [slope_def_field, hR.zero] using hp
      exact (div_pos_iff_of_pos_right r.property.1).mp hs
    have hm' : f (x - (r : ℝ)) < 0 := by
      have hs : 0 < f (x - (r : ℝ)) / -(r : ℝ) := by
        simpa [slope_def_field, hR.zero, show x - (r : ℝ) - x = -(r : ℝ) by ring] using hm
      rcases div_pos_iff.mp hs with h | h
      · linarith [r.property.1, h.2]
      · exact h.1
    rw [realLocalDegree_eq_endpoints h hR r]
    simp [hp', not_lt_of_gt hm', sign_pos hpos]


theorem realLocalDegree_eq_sign_deriv {f : ℝ → ℝ} {x : ℝ}
    (h : realIsolatedZero f x) (hd : DifferentiableAt ℝ f x) (hne : deriv f x ≠ 0) :
    realLocalDegree f x h = (SignType.sign (deriv f x) : ℤ) :=
  realLocalDegree_eq_sign_of_hasDerivAt h hd.hasDerivAt hne

end Poincare.LocalDegree
