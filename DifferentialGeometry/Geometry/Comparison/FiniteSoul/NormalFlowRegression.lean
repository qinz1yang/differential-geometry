import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalFlowMap
import DifferentialGeometry.Topology.Manifold.AddCircle

/-!
# Regression for the restated LFR46: the reviewer's flat `S¹ × ℝ²` example (lane CMS3-FLOW2, G3)

External review `docs/geometrization/chapter13/out/review-finite-soul-three.md` §12 (P0 FLOW),
disposition D1: the frozen `exists_finite_normalFlowMap` is false. Take the flat
`M = (ℝ/ℤ) × ℝ²`, `S = (ℝ/ℤ) × {0}`, `B = ℝ/ℤ`, the trivial rank-two bundle, and the base map
`b(t) = (f(t), 0)` with `f(t) = t − sin(2πt)/(2π)`: `f` descends to a bijection of the circle but
`f'(0) = 0`. With `ι(t, w) = (b t, w)` every frozen hypothesis holds, yet a `C¹` diffeomorphism `e`
with `e(s, 0) = b s` would make `proj ∘ e⁻¹` a `C¹` left inverse of `b`, which is impossible.

This file checks, on the smooth carrier `AddCircle 1 × EuclideanSpace ℝ (Fin 2)`:

* `flatSoulBase`, `flatSoulBase_coe`: the base map and its lift `t ↦ (f t, 0)`;
* `injective_flatSoulBase`, `range_flatSoulBase`: `b` is injective with range the soul `S` (the frozen
  hypotheses on `b` hold);
* `not_flatSoulBase_leftInverse` — **the regression**: no left inverse of `b` is `C^n` (`n ≠ 0`) at the
  points of `S`, i.e. the restated hypothesis `hbinv` REJECTS this `b`;
* `not_exists_diffeomorph_flatSoulBase`: no `C^n` diffeomorphism from ANY fibre bundle over the circle
  restricts to `b` on the zero section, i.e. the frozen conclusion is unsatisfiable for this data;
* `injective_mfderiv_of_leftInverse_soulBase`: conversely, `hbinv` makes every base map an immersion (the
  non-degeneracy the restated LFR46 needs); `injective_mfderiv_of_diffeomorph_zeroSection`: so does
  the LFR46 conclusion `e(s, 0) = b s` (the reviewer's argument).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.FiniteSoul

/-! ### A left inverse forces an injective differential (generic) -/

section Generic

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- **`hbinv` makes the base map an immersion**: a left inverse `R` of `b`, differentiable at `b s`,
forces `d b_s` to be injective. -/
theorem injective_mfderiv_of_leftInverse_soulBase {b : B → M} {R : M → B} (hRb : ∀ s, R (b s) = s) {s : B}
    (hb : MDifferentiableAt IB IM b s) (hR : MDifferentiableAt IM IB R (b s)) :
    Injective (mfderiv IB IM b s) := by
  have hcomp : mfderiv IB IB (R ∘ b) s = (mfderiv IM IB R (b s)).comp (mfderiv IB IM b s) :=
    mfderiv_comp s hR hb
  have hid : R ∘ b = id := funext hRb
  rw [hid, mfderiv_id] at hcomp
  intro v w hvw
  have h := congrArg (mfderiv IM IB R (b s)) hvw
  have hv : ContinuousLinearMap.id ℝ (TangentSpace IB s) v =
      (mfderiv IM IB R (b s)) (mfderiv IB IM b s v) := by rw [hcomp]; rfl
  have hw : ContinuousLinearMap.id ℝ (TangentSpace IB s) w =
      (mfderiv IM IB R (b s)) (mfderiv IB IM b s w) := by rw [hcomp]; rfl
  have hvw' := hv.trans (h.trans hw.symm)
  simpa using hvw'

/-- **The LFR46 conclusion makes the base map an immersion**: if a `C^n` diffeomorphism (`n ≠ 0`)
from a vector bundle restricts to `b` on the zero section, then `d b_s` is injective (the left inverse
is `proj ∘ e⁻¹`). -/
theorem injective_mfderiv_of_diffeomorph_zeroSection {n : ℕ∞ω} (hn : n ≠ 0)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ s, AddCommMonoid (V s)] [∀ s, Module ℝ (V s)] [∀ s, TopologicalSpace (V s)]
    [FiberBundle F V] [VectorBundle ℝ F V]
    (e : TotalSpace F V ≃ₘ^n⟮IB.prod 𝓘(ℝ, F), IM⟯ M) {b : B → M}
    (he : ∀ s, e ⟨s, 0⟩ = b s) (s : B) : Injective (mfderiv IB IM b s) := by
  have hb : b = fun s => e (zeroSection F V s) := funext fun s => (he s).symm
  have hbd : MDifferentiableAt IB IM b s := by
    rw [hb]
    exact ((e.contMDiff.comp (Bundle.contMDiff_zeroSection ℝ V)).contMDiffAt).mdifferentiableAt hn
  refine injective_mfderiv_of_leftInverse_soulBase (R := fun x => (e.symm x).proj) (fun s => ?_) hbd
    (((Bundle.contMDiff_proj V).comp e.symm.contMDiff).contMDiffAt.mdifferentiableAt hn)
  rw [← he s, e.symm_apply_apply]

end Generic

/-! ### The flat example -/

/-- The reviewer's reparametrization `f(t) = t − sin(2πt)/(2π)`. -/
def flatReparam (t : ℝ) : ℝ := t - Real.sin (2 * Real.pi * t) / (2 * Real.pi)

theorem flatReparam_add_int (t : ℝ) (k : ℤ) : flatReparam (t + k) = flatReparam t + k := by
  unfold flatReparam
  have h : Real.sin (2 * Real.pi * (t + k)) = Real.sin (2 * Real.pi * t) := by
    rw [show 2 * Real.pi * (t + k) = 2 * Real.pi * t + (k : ℝ) * (2 * Real.pi) by ring,
      Real.sin_add_int_mul_two_pi]
  rw [h]
  ring

theorem periodic_flatReparam :
    Periodic (fun t : ℝ => ((flatReparam t : ℝ) : AddCircle (1 : ℝ))) 1 := by
  intro t
  change ((flatReparam (t + 1) : ℝ) : AddCircle (1 : ℝ)) = ((flatReparam t : ℝ) : AddCircle (1 : ℝ))
  have h := flatReparam_add_int t 1
  rw [Int.cast_one] at h
  rw [h, AddCircle.coe_add_period]

/-- `f` is injective on `ℝ`: `|sin a − sin b| < |a − b|` for `a ≠ b`. -/
theorem injective_flatReparam : Injective flatReparam := by
  intro t t' h
  by_contra hne
  have hpi : 0 < 2 * Real.pi := by positivity
  have hsub : Real.sin (2 * Real.pi * t) - Real.sin (2 * Real.pi * t') = 2 * Real.pi * (t - t') := by
    unfold flatReparam at h
    have h2 : (t - Real.sin (2 * Real.pi * t) / (2 * Real.pi)) * (2 * Real.pi) =
        (t' - Real.sin (2 * Real.pi * t') / (2 * Real.pi)) * (2 * Real.pi) := by rw [h]
    rw [sub_mul, sub_mul, div_mul_cancel₀ _ hpi.ne', div_mul_cancel₀ _ hpi.ne'] at h2
    linarith
  have hx : (2 * Real.pi * t - 2 * Real.pi * t') / 2 ≠ 0 := by
    intro h0
    apply hne
    have : 2 * Real.pi * (t - t') = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hpi.ne'
    · linarith
  have hlt := Real.abs_sin_lt_abs hx
  rw [Real.sin_sub_sin] at hsub
  have hcos := Real.abs_cos_le_one ((2 * Real.pi * t + 2 * Real.pi * t') / 2)
  have habs : |2 * Real.pi * (t - t')| ≤
      2 * |Real.sin ((2 * Real.pi * t - 2 * Real.pi * t') / 2)| := by
    rw [← hsub, abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg (Real.sin ((2 * Real.pi * t - 2 * Real.pi * t') / 2))]
  have heq : |(2 * Real.pi * t - 2 * Real.pi * t') / 2| = |2 * Real.pi * (t - t')| / 2 := by
    rw [abs_div, abs_two]
    congr 1
    ring_nf
  rw [heq] at hlt
  linarith

/-- The degenerate base map `b(t) = (f t, 0)` of the flat `S¹ × ℝ²`. -/
def flatSoulBase (s : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ) × EuclideanSpace ℝ (Fin 2) :=
  (periodic_flatReparam.lift s, 0)

theorem flatSoulBase_coe (t : ℝ) :
    flatSoulBase (t : AddCircle (1 : ℝ)) = (((flatReparam t : ℝ) : AddCircle (1 : ℝ)), 0) := by
  unfold flatSoulBase
  rw [periodic_flatReparam.lift_coe]

/-- The soul `S¹ × {0}`. -/
def flatSoul : Set (AddCircle (1 : ℝ) × EuclideanSpace ℝ (Fin 2)) := {x | x.2 = 0}

/-- **The frozen hypotheses on `b` hold**: `b` is injective. -/
theorem injective_flatSoulBase : Injective flatSoulBase := by
  intro s s' h
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective s
  obtain ⟨t', rfl⟩ := QuotientAddGroup.mk_surjective s'
  have h1 := congrArg Prod.fst h
  change (flatSoulBase (t : AddCircle (1 : ℝ))).1 = (flatSoulBase (t' : AddCircle (1 : ℝ))).1 at h1
  rw [flatSoulBase_coe, flatSoulBase_coe] at h1
  obtain ⟨k, hk⟩ := (QuotientAddGroup.eq (s := AddSubgroup.zmultiples (1 : ℝ))).mp h1
  have hk' : (k : ℝ) = -flatReparam t + flatReparam t' := by simpa using hk
  have hf : flatReparam t' = flatReparam (t + k) := by
    rw [flatReparam_add_int]
    linarith
  have ht : t' = t + k := injective_flatReparam hf
  change ((t : ℝ) : AddCircle (1 : ℝ)) = ((t' : ℝ) : AddCircle (1 : ℝ))
  rw [ht]
  exact (QuotientAddGroup.eq (s := AddSubgroup.zmultiples (1 : ℝ))).mpr
    (AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by simp⟩)

/-- **The frozen hypotheses on `b` hold**: `range b = S`. -/
theorem range_flatSoulBase : range flatSoulBase = flatSoul := by
  ext ⟨y, w⟩
  constructor
  · rintro ⟨s, hs⟩
    rw [← hs]
    rfl
  · intro hw
    change w = 0 at hw
    subst hw
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective y
    have hcont : Continuous flatReparam := by
      unfold flatReparam
      fun_prop
    have hpi : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three]
    have hlo : flatReparam (t - 1) ≤ t := by
      unfold flatReparam
      have h := Real.neg_one_le_sin (2 * Real.pi * (t - 1))
      have : -(Real.sin (2 * Real.pi * (t - 1)) / (2 * Real.pi)) ≤ 1 / (2 * Real.pi) := by
        rw [← neg_div]
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
      linarith
    have hhi : t ≤ flatReparam (t + 1) := by
      unfold flatReparam
      have h := Real.sin_le_one (2 * Real.pi * (t + 1))
      have : Real.sin (2 * Real.pi * (t + 1)) / (2 * Real.pi) ≤ 1 / (2 * Real.pi) :=
        div_le_div_of_nonneg_right h (by positivity)
      linarith
    obtain ⟨t', -, ht'⟩ := intermediate_value_Icc (by linarith : t - 1 ≤ t + 1)
      hcont.continuousOn ⟨hlo, hhi⟩
    refine ⟨(t' : AddCircle (1 : ℝ)), ?_⟩
    rw [flatSoulBase_coe, ht']

/-- `f'(0) = 0`. -/
theorem hasDerivAt_flatReparam_zero : HasDerivAt flatReparam 0 0 := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h0 : HasDerivAt (fun t : ℝ => 2 * Real.pi * t) (2 * Real.pi) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 * Real.pi)
  have h1 : HasDerivAt (fun t : ℝ => Real.sin (2 * Real.pi * t))
      (Real.cos (2 * Real.pi * 0) * (2 * Real.pi)) 0 :=
    (Real.hasDerivAt_sin (2 * Real.pi * 0)).comp (0 : ℝ) h0
  have h2 := (hasDerivAt_id' (0 : ℝ)).sub (h1.div_const (2 * Real.pi))
  exact h2.congr_deriv (by rw [mul_zero, Real.cos_zero, one_mul, div_self hpi, sub_self])

/-- **The regression.** The restated hypothesis `hbinv` rejects the reviewer's base map: no left
inverse of `b` is `C^n` (`n ≠ 0`) at the points of the soul. -/
theorem not_flatSoulBase_leftInverse {n : ℕ∞ω} (hn : n ≠ 0) :
    ¬ ∃ R : AddCircle (1 : ℝ) × EuclideanSpace ℝ (Fin 2) → AddCircle (1 : ℝ),
      (∀ s, R (flatSoulBase s) = s) ∧
        ∀ x ∈ flatSoul, ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) 𝓘(ℝ, ℝ) n R x := by
  rintro ⟨R, hRb, hR⟩
  set k : ℝ → AddCircle (1 : ℝ) × EuclideanSpace ℝ (Fin 2) :=
    fun t => (((flatReparam t : ℝ) : AddCircle (1 : ℝ)), 0) with hk
  have hk0 : k 0 ∈ flatSoul := rfl
  have hRk : MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) 𝓘(ℝ, ℝ) R (k 0) :=
    (hR _ hk0).mdifferentiableAt hn
  -- `k` has zero derivative at `0`
  have hf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) flatReparam 0 ((1 : ℝ →L[ℝ] ℝ).smulRight (0 : ℝ)) :=
    hasMFDerivAt_iff_hasFDerivAt.mpr hasDerivAt_flatReparam_zero.hasFDerivAt
  have hcoe : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) (flatReparam 0)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) (flatReparam 0)) :=
    (AddCircle.contMDiff_coe.mdifferentiableAt (by simp)).hasMFDerivAt
  have hfst := hcoe.comp 0 hf
  have hkd := hfst.prodMk (hasMFDerivAt_const (I := 𝓘(ℝ, ℝ))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) (0 : EuclideanSpace ℝ (Fin 2)) (0 : ℝ))
  have hcomp := hRk.hasMFDerivAt.comp 0 hkd
  have hRkfun : R ∘ k = fun t : ℝ => (t : AddCircle (1 : ℝ)) := by
    funext t
    change R (k t) = (t : AddCircle (1 : ℝ))
    rw [hk]
    dsimp only
    rw [← flatSoulBase_coe, hRb]
  rw [hRkfun] at hcomp
  have hzero := hcomp.mfderiv
  have hinj := (AddCircle.bijective_mfderiv_coe 0).1
  have h10 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) 0 (1 : ℝ) =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) 0 (0 : ℝ) := by
    rw [hzero]
    refine congrArg (mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) 𝓘(ℝ, ℝ) R (k 0)) ?_
    refine Prod.ext ?_ rfl
    refine congrArg (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ)))
      (flatReparam 0)) ?_
    change (1 : ℝ →L[ℝ] ℝ) 1 • (0 : ℝ) = (1 : ℝ →L[ℝ] ℝ) 0 • (0 : ℝ)
    rw [smul_zero, smul_zero]
  exact one_ne_zero (α := ℝ) (hinj h10)

/-- **The frozen conclusion is unsatisfiable for this data**: no `C^n` diffeomorphism (`n ≠ 0`) from
the total space of any fibre bundle over the circle restricts to `b` on the zero section (otherwise
`proj ∘ e⁻¹` would be a `C^n` left inverse of `b`). -/
theorem not_exists_diffeomorph_flatSoulBase {n : ℕ∞ω} (hn : n ≠ 0)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {V : AddCircle (1 : ℝ) → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ s, AddCommMonoid (V s)] [∀ s, TopologicalSpace (V s)] [FiberBundle F V]
    (e : TotalSpace F V ≃ₘ^n⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, F),
      𝓘(ℝ, ℝ).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))⟯ AddCircle (1 : ℝ) × EuclideanSpace ℝ (Fin 2)) :
    ¬ ∀ s, e ⟨s, 0⟩ = flatSoulBase s := by
  intro he
  apply not_flatSoulBase_leftInverse hn
  refine ⟨fun x => (e.symm x).proj, fun s => ?_, fun x _ => ?_⟩
  · rw [← he s]
    dsimp only
    rw [e.symm_apply_apply]
  · exact ((Bundle.contMDiff_proj V).comp e.symm.contMDiff).contMDiffAt

end DifferentialGeometry.Geometry.FiniteSoul
