import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCircleBase
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersFn

/-!
# FC39 producer, packet P0 (gate 1): the S³ circle kind, the four defining functions

Part B of the circle kind of the S³ inhabitant: the four faces of `C₁ = [1, 4]²` in the base
`(1/2, 8)²` of `sphereCircleBundle`, with the ADAPTED defining functions (lead decision 02:45):
in the draft order `N, S, B, T` (`circFaceEquiv`, index `(axis, side)`)

  `N = 1 − 16/ψ²`, `S = 1 − ψ²`, `B = −(q₀ + 3/5)`, `T = q₀ − 3/5`  (`q₀ = (r² − 4)/(r² + 4)`),

i.e. `circFaceFn a σ = −circSlack a σ ∘ (axis a coordinate)`. Smooth on the whole base, every
derivative nonzero (`circFaceFn_mfderiv_ne_zero`), at most two zeros at a point, the two active
differentials independent, and `C₁ = {all ≤ 0}` (`sphereCircleCbase_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-! ## The two coordinate functionals -/

/-- The coordinate functional of the axis `a` (`false` = `ψ`, `true` = `r`). -/
def circCoordL : Bool → (E2 →L[ℝ] ℝ)
  | false => (ContinuousLinearMap.fst ℝ ℝ ℝ).comp sphereCircleEquiv.toContinuousLinearMap
  | true => (ContinuousLinearMap.snd ℝ ℝ ℝ).comp sphereCircleEquiv.toContinuousLinearMap

theorem circCoordL_false (p : E2) : circCoordL false p = (sphereCircleEquiv p).1 :=
  rfl

theorem circCoordL_true (p : E2) : circCoordL true p = (sphereCircleEquiv p).2 :=
  rfl

theorem circCoordL_mem_wide (a : Bool) (c : sphereCircleBaseOpens) :
    circCoordL a c.val ∈ sphereCircleWide := by
  cases a
  · exact c.2.1
  · exact c.2.2

theorem circCoordL_pos (a : Bool) (c : sphereCircleBaseOpens) : 0 < circCoordL a c.val :=
  sphereCircleWide_pos (circCoordL_mem_wide a c)

theorem circCoordL_symm (a : Bool) (u v : ℝ) :
    circCoordL a (sphereCircleEquiv.symm (u, v)) = if a then v else u := by
  cases a <;> simp [circCoordL]

/-- Two functionals `α • L_a`, `β • L_a'` on different axes with nonzero coefficients are jointly
onto `ℝ × ℝ`. -/
theorem surjective_circCoordL_pair {a a' : Bool} (h : a ≠ a') {α β : ℝ} (hα : α ≠ 0)
    (hβ : β ≠ 0) : Surjective fun w : E2 => ((α • circCoordL a) w, (β • circCoordL a') w) := by
  intro q
  cases a <;> cases a'
  · exact absurd rfl h
  · refine ⟨sphereCircleEquiv.symm (q.1 / α, q.2 / β), ?_⟩
    simp only [smul_apply, circCoordL_symm, smul_eq_mul, Bool.false_eq_true,
      ite_false, ite_true]
    rw [mul_div_cancel₀ _ hα, mul_div_cancel₀ _ hβ]
  · refine ⟨sphereCircleEquiv.symm (q.2 / β, q.1 / α), ?_⟩
    simp only [smul_apply, circCoordL_symm, smul_eq_mul, Bool.false_eq_true,
      ite_false, ite_true]
    rw [mul_div_cancel₀ _ hα, mul_div_cancel₀ _ hβ]
  · exact absurd rfl h

/-- A combination `α • L_ψ + β • L_r` vanishes only for `α = β = 0`. -/
theorem circCoordL_combination_eq_zero {α β : ℝ}
    (h : α • circCoordL false + β • circCoordL true = 0) : α = 0 ∧ β = 0 := by
  have h1 := congrArg (fun L : E2 →L[ℝ] ℝ => L (sphereCircleEquiv.symm (1, 0))) h
  have h2 := congrArg (fun L : E2 →L[ℝ] ℝ => L (sphereCircleEquiv.symm (0, 1))) h
  simp only [add_apply, smul_apply, circCoordL_symm,
    smul_eq_mul, Bool.false_eq_true, ite_false, ite_true, zero_apply] at h1 h2
  constructor <;> linarith

theorem circCoordL_smul_ne_zero (a : Bool) {α : ℝ} (hα : α ≠ 0) : α • circCoordL a ≠ 0 := by
  intro h
  cases a
  · have := (circCoordL_combination_eq_zero (α := α) (β := 0) (by rw [h, zero_smul, add_zero])).1
    exact hα this
  · have := (circCoordL_combination_eq_zero (α := 0) (β := α) (by rw [h, zero_smul, zero_add])).2
    exact hα this

/-! ## Base functions of one axis -/

/-- The derivative of a function of one axis on the base. -/
theorem hasMFDerivAt_circAxis (g : ℝ → ℝ) (a : Bool) (c : sphereCircleBaseOpens) {g' : ℝ}
    (hg : HasDerivAt g g' (circCoordL a c.val)) :
    HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (fun c : sphereCircleBaseOpens => g (circCoordL a c.val)) c
      (g' • circCoordL a) := by
  have hF : HasFDerivAt (fun p : E2 => g (circCoordL a p)) (g' • circCoordL a) c.val := by
    have h := hg.hasFDerivAt.comp c.val (circCoordL a).hasFDerivAt
    refine h.congr_fderiv ?_
    ext v
    simp [smul_eq_mul, mul_comm]
  have hM : HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (fun p : E2 => g (circCoordL a p)) c.val
      (g' • circCoordL a) := hasMFDerivAt_iff_hasFDerivAt.2 hF
  exact hM.comp c (hasMFDerivAt_subtype_val (I := 𝓡 2) sphereCircleBaseOpens c)

/-- Smoothness of a function of one axis on the base. -/
theorem contMDiffAt_circAxis (g : ℝ → ℝ) (a : Bool) (c : sphereCircleBaseOpens)
    (hg : ContDiffAt ℝ ∞ g (circCoordL a c.val)) :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun c : sphereCircleBaseOpens => g (circCoordL a c.val)) c := by
  have hF : ContDiffAt ℝ ∞ (fun p : E2 => g (circCoordL a p)) c.val :=
    hg.comp c.val (circCoordL a).contDiff.contDiffAt
  exact (contMDiffAt_iff_contDiffAt.2 hF).comp c contMDiff_subtype_val.contMDiffAt

/-! ## The four defining functions -/

/-- **The defining function of the face `(a, σ)`**: `−slack` of the axis `a` at the side `σ`. -/
def circFaceFn (a σ : Bool) (c : sphereCircleBaseOpens) : ℝ :=
  -circSlack a σ (circCoordL a c.val)

theorem hasMFDerivAt_circFaceFn (a σ : Bool) (c : sphereCircleBaseOpens) :
    HasMFDerivAt (𝓡 2) 𝓘(ℝ, ℝ) (circFaceFn a σ) c
      ((-circSlackDeriv a σ (circCoordL a c.val)) • circCoordL a) :=
  hasMFDerivAt_circAxis (fun t => -circSlack a σ t) a c
    (hasDerivAt_circSlack a σ (circCoordL_pos a c)).neg

theorem contMDiff_circFaceFn (a σ : Bool) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (circFaceFn a σ) :=
  fun c => contMDiffAt_circAxis (fun t => -circSlack a σ t) a c
    (contDiffAt_circSlack a σ (circCoordL_pos a c)).neg

theorem circFaceFn_mfderiv_ne_zero (a σ : Bool) (c : sphereCircleBaseOpens) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (circFaceFn a σ) c ≠ 0 := by
  rw [(hasMFDerivAt_circFaceFn a σ c).mfderiv]
  exact circCoordL_smul_ne_zero a (neg_ne_zero.2 (circSlackDeriv_ne_zero a σ (circCoordL_pos a c)))

theorem circFaceFn_eq_zero_iff {a σ : Bool} {c : sphereCircleBaseOpens} :
    circFaceFn a σ c = 0 ↔ circCoordL a c.val = circEndVal σ := by
  rw [circFaceFn, neg_eq_zero]
  exact circSlack_eq_zero_iff a (circCoordL_pos a c)

theorem circFaceFn_nonpos_false {a : Bool} {c : sphereCircleBaseOpens} :
    circFaceFn a false c ≤ 0 ↔ 1 ≤ circCoordL a c.val := by
  rw [circFaceFn, neg_nonpos]
  exact circSlack_false_nonneg_iff a (circCoordL_pos a c)

theorem circFaceFn_nonpos_true {a : Bool} {c : sphereCircleBaseOpens} :
    circFaceFn a true c ≤ 0 ↔ circCoordL a c.val ≤ 4 := by
  rw [circFaceFn, neg_nonpos]
  exact circSlack_true_nonneg_iff a (circCoordL_pos a c)

/-! ## The face index `Fin 4 ≃ (axis, side)` in the draft order `N, S, B, T` -/

/-- The face index: `N = (ψ, 4) ↦ 0`, `S = (ψ, 1) ↦ 1`, `B = (r, 1) ↦ 2`, `T = (r, 4) ↦ 3`. -/
def circFaceEquiv : Bool × Bool ≃ Fin 4 where
  toFun p := ⟨(if p.1 then 2 else 0) + (if p.1 = p.2 then 1 else 0), by
    rcases p with ⟨_ | _, _ | _⟩ <;> decide⟩
  invFun l := (decide (2 ≤ l.val), decide (l.val = 0 ∨ l.val = 3))
  left_inv := by decide
  right_inv := by decide

/-- **The four defining functions** of the S³ circle region, in the draft order `N, S, B, T`. -/
def circDefining (l : Fin 4) : sphereCircleBaseOpens → ℝ :=
  circFaceFn (circFaceEquiv.symm l).1 (circFaceEquiv.symm l).2

theorem circDefining_face (a σ : Bool) :
    circDefining (circFaceEquiv (a, σ)) = circFaceFn a σ := by
  rw [circDefining, Equiv.symm_apply_apply]

theorem circDefining_smooth (l : Fin 4) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (circDefining l) :=
  contMDiff_circFaceFn _ _

theorem circDefining_regular (l : Fin 4) (c : sphereCircleBaseOpens) :
    mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (circDefining l) c ≠ 0 :=
  circFaceFn_mfderiv_ne_zero _ _ c

theorem circEndVal_eq_four_iff {σ : Bool} : circEndVal σ = 4 ↔ σ = true := by
  cases σ <;> norm_num [circEndVal]

/-- A zero of the face `l` fixes its side: `l = (a, [coordinate a = 4])`. -/
theorem circDefining_zero_index {l : Fin 4} {c : sphereCircleBaseOpens}
    (h : circDefining l c = 0) :
    l = circFaceEquiv ((circFaceEquiv.symm l).1,
      decide (circCoordL (circFaceEquiv.symm l).1 c.val = 4)) := by
  have hz := circFaceFn_eq_zero_iff.1 h
  rw [hz]
  have hσ : decide (circEndVal (circFaceEquiv.symm l).2 = 4) = (circFaceEquiv.symm l).2 := by
    rcases (circFaceEquiv.symm l).2 with _ | _ <;> norm_num [circEndVal]
  rw [hσ, Prod.mk.eta, Equiv.apply_symm_apply]

/-- **Depth `≤ 2`**: one zero per axis at most. -/
theorem circDefining_depth (c : sphereCircleBaseOpens) :
    (Finset.univ.filter fun l => circDefining l c = 0).card ≤ 2 := by
  classical
  let A : Finset (Fin 4) :=
    {circFaceEquiv (false, decide (circCoordL false c.val = 4)),
      circFaceEquiv (true, decide (circCoordL true c.val = 4))}
  have hsub : (Finset.univ.filter fun l => circDefining l c = 0) ⊆ A := by
    intro l hl
    have h := circDefining_zero_index (Finset.mem_filter.1 hl).2
    rcases ha : (circFaceEquiv.symm l).1 with _ | _ <;> rw [ha] at h <;> rw [h] <;> simp [A]
  refine (Finset.card_le_card hsub).trans ?_
  exact (Finset.card_insert_le _ _).trans (by simp)

/-- Two distinct zeros lie on different axes. -/
theorem circDefining_axes_ne {l l' : Fin 4} {c : sphereCircleBaseOpens} (hne : l ≠ l')
    (h : circDefining l c = 0) (h' : circDefining l' c = 0) :
    (circFaceEquiv.symm l).1 ≠ (circFaceEquiv.symm l').1 := by
  intro ha
  have e := circDefining_zero_index h
  have e' := circDefining_zero_index h'
  rw [ha] at e
  exact hne (e.trans e'.symm)

/-- **Independence** of the two active differentials. -/
theorem circDefining_independent (c : sphereCircleBaseOpens) (l l' : Fin 4) (hne : l ≠ l')
    (h : circDefining l c = 0) (h' : circDefining l' c = 0) :
    Surjective fun w : TangentSpace (𝓡 2) c =>
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (circDefining l) c w,
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (circDefining l') c w) := by
  have hax := circDefining_axes_ne hne h h'
  rw [circDefining, circDefining, (hasMFDerivAt_circFaceFn _ _ c).mfderiv,
    (hasMFDerivAt_circFaceFn _ _ c).mfderiv]
  exact surjective_circCoordL_pair hax
    (neg_ne_zero.2 (circSlackDeriv_ne_zero _ _ (circCoordL_pos _ c)))
    (neg_ne_zero.2 (circSlackDeriv_ne_zero _ _ (circCoordL_pos _ c)))

/-- **`C₁ = [1, 4]²` is the set where all four defining functions are `≤ 0`.** -/
theorem sphereCircleCbase_eq :
    sphereCircleCbase = {c | ∀ l, circDefining l c ≤ 0} := by
  ext c
  constructor
  · intro hc l
    obtain ⟨⟨hψ1, hψ4⟩, hr1, hr4⟩ := hc
    rw [← circFaceEquiv.apply_symm_apply l, circDefining_face]
    rcases (circFaceEquiv.symm l) with ⟨_ | _, _ | _⟩
    · exact circFaceFn_nonpos_false.2 hψ1
    · exact circFaceFn_nonpos_true.2 hψ4
    · exact circFaceFn_nonpos_false.2 hr1
    · exact circFaceFn_nonpos_true.2 hr4
  · intro hc
    have h := fun a σ => hc (circFaceEquiv (a, σ))
    simp only [circDefining_face] at h
    exact ⟨⟨circFaceFn_nonpos_false.1 (h false false),
      circFaceFn_nonpos_true.1 (h false true)⟩,
      circFaceFn_nonpos_false.1 (h true false),
      circFaceFn_nonpos_true.1 (h true true)⟩

end GC.GraphManifold.Assembly.FC39P0
