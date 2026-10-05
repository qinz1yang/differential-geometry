import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyMonodromyOrientation
import DifferentialGeometry.Topology.Manifold.AddCircle.DiffeomorphLift
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Topology.Manifold.AddCircle.Descent
import DifferentialGeometry.Topology.Manifold.Diffeomorph.InverseFamily
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Chapter-14 assembly, D2S1 input (b1): `Diff⁺(S¹)` is connected

Frozen statement: `build-logs/scratch/ASM-D2S1/D2S1Inputs.lean` (`exists_circleIsotopy_of_preservesOrientation`).
An orientation-preserving diffeomorphism `f` of the circle is joined to the identity by a jointly
smooth isotopy (with jointly smooth inverses), constant `= f` for `t < 1/3` and `= id` for `t > 2/3`.

Route. Conjugate by `AddCircle.diffeomorphCircle` to `ψ : ℝ/ℤ → ℝ/ℤ` and lift (`AddCircle/DiffeomorphLift.lean`):
`ψ ↑t = ↑(F t)` or `ψ ↑t = −↑(F t)` with `F (t + 1) = F t + 1`, `F' > 0`.
* The negative branch contradicts orientation: `t + F t` takes an integer value at some `t₀`, so `↑t₀`
  is a fixed point of `ψ` with `dψ = −F'(t₀) < 0`; conjugating back, `f` has a fixed point where the
  determinant of `df` is negative, while `f` preserves the orientation of the connected circle
  (`preservesOrientation_iff_det_mfderiv_pos_of_apply_eq`, group G1).
* Positive branch: `Λ s = F + τ(s) (id − F)` with `τ = smoothTransition (3 s − 1)` is, for each `s`, a
  smooth increasing bijection of `ℝ` commuting with `+1` (inverse smooth by the one-dimensional inverse
  function theorem `Homeomorph.contDiff_symm_deriv`); it descends to the circle. Joint smoothness
  descends through `AddCircle.contMDiffOn_of_comp_coe`; the inverses are jointly smooth by the tree's
  `contMDiffOn_diffeomorph_family_symm` (inverse function theorem on `(s, z) ↦ (s, L s z)`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

/-! ## The straight-line homotopy of lifts -/

/-- The homotopy of lifts `F + τ(s) (id − F)`, `τ = smoothTransition (3 s − 1)`: `F` for `s ≤ 1/3`,
the identity for `s ≥ 2/3`. -/
def circleLiftHomotopy (F : ℝ → ℝ) (s t : ℝ) : ℝ :=
  F t + Real.smoothTransition (3 * s - 1) * (t - F t)

theorem circleLiftHomotopy_of_le (F : ℝ → ℝ) {s : ℝ} (hs : s ≤ 1 / 3) (t : ℝ) :
    circleLiftHomotopy F s t = F t := by
  unfold circleLiftHomotopy
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul, add_zero]

theorem circleLiftHomotopy_of_ge (F : ℝ → ℝ) {s : ℝ} (hs : 2 / 3 ≤ s) (t : ℝ) :
    circleLiftHomotopy F s t = t := by
  unfold circleLiftHomotopy
  rw [Real.smoothTransition.one_of_one_le (by linarith), one_mul]
  ring

theorem circleLiftHomotopy_add_one {F : ℝ → ℝ} (hper : ∀ t, F (t + 1) = F t + 1) (s t : ℝ) :
    circleLiftHomotopy F s (t + 1) = circleLiftHomotopy F s t + 1 := by
  unfold circleLiftHomotopy
  rw [hper]
  ring

theorem contDiff_circleLiftHomotopy {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => circleLiftHomotopy F p.1 p.2) := by
  unfold circleLiftHomotopy
  have hτ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Real.smoothTransition (3 * p.1 - 1)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_fst).sub contDiff_const)
  exact (hF.comp contDiff_snd).add (hτ.mul (contDiff_snd.sub (hF.comp contDiff_snd)))

theorem hasDerivAt_circleLiftHomotopy {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (s t : ℝ) :
    HasDerivAt (circleLiftHomotopy F s)
      (deriv F t + Real.smoothTransition (3 * s - 1) * (1 - deriv F t)) t := by
  have hd : HasDerivAt F (deriv F t) t := (hF.differentiable (by simp) t).hasDerivAt
  exact hd.add (((hasDerivAt_id t).sub hd).const_mul _)

theorem circleLiftHomotopy_deriv_pos {F : ℝ → ℝ} (hpos : ∀ t, 0 < deriv F t) (s t : ℝ) :
    0 < deriv F t + Real.smoothTransition (3 * s - 1) * (1 - deriv F t) := by
  have h0 := Real.smoothTransition.nonneg (3 * s - 1)
  have h1 := Real.smoothTransition.le_one (3 * s - 1)
  have hF := hpos t
  rcases h0.lt_or_eq with h | h
  · nlinarith [mul_nonneg (sub_nonneg.mpr h1) hF.le]
  · rw [← h, zero_mul, add_zero]
    exact hF

theorem strictMono_circleLiftHomotopy {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hpos : ∀ t, 0 < deriv F t) (s : ℝ) : StrictMono (circleLiftHomotopy F s) :=
  strictMono_of_deriv_pos fun t => by
    rw [(hasDerivAt_circleLiftHomotopy hF s t).deriv]
    exact circleLiftHomotopy_deriv_pos hpos s t

theorem continuous_circleLiftHomotopy {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (s : ℝ) :
    Continuous (circleLiftHomotopy F s) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_circleLiftHomotopy hF s t).continuousAt

theorem surjective_circleLiftHomotopy {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t, F (t + 1) = F t + 1) (s : ℝ) : Surjective (circleLiftHomotopy F s) := by
  intro y
  set g := circleLiftHomotopy F s with hg
  have hperiodic : Periodic (fun t => g t - t) 1 := by
    intro t
    simp only [hg, circleLiftHomotopy_add_one hper]
    ring
  have hint : ∀ n : ℤ, g n = g 0 + n := by
    intro n
    have h := hperiodic.int_mul n 0
    simp only [zero_add, mul_one, sub_zero] at h
    linarith
  set n : ℤ := ⌊y - g 0⌋ with hn
  have hlo : g n ≤ y := by
    rw [hint]
    linarith [Int.floor_le (y - g 0)]
  have hhi : y ≤ g ((n : ℝ) + 1) := by
    have h := hint (n + 1)
    push_cast at h
    rw [h]
    linarith [Int.lt_floor_add_one (y - g 0)]
  obtain ⟨c, -, hc⟩ := intermediate_value_Icc (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)
    (continuous_circleLiftHomotopy hF s).continuousOn ⟨hlo, hhi⟩
  exact ⟨c, hc⟩

/-- The homotopy at time `s` as a homeomorphism of `ℝ`. -/
def circleLiftHomeomorph {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hper : ∀ t, F (t + 1) = F t + 1)
    (hpos : ∀ t, 0 < deriv F t) (s : ℝ) : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective (circleLiftHomotopy F s)
    (strictMono_circleLiftHomotopy hF hpos s) (surjective_circleLiftHomotopy hF hper s)).toHomeomorph

theorem circleLiftHomeomorph_apply {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t, F (t + 1) = F t + 1) (hpos : ∀ t, 0 < deriv F t) (s t : ℝ) :
    circleLiftHomeomorph hF hper hpos s t = circleLiftHomotopy F s t :=
  rfl

theorem contDiff_circleLiftHomeomorph_symm {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t, F (t + 1) = F t + 1) (hpos : ∀ t, 0 < deriv F t) (s : ℝ) :
    ContDiff ℝ ∞ ((circleLiftHomeomorph hF hper hpos s).symm : ℝ → ℝ) :=
  (circleLiftHomeomorph hF hper hpos s).contDiff_symm_deriv
    (fun t => (circleLiftHomotopy_deriv_pos hpos s t).ne')
    (fun t => hasDerivAt_circleLiftHomotopy hF s t)
    ((contDiff_circleLiftHomotopy hF).comp (contDiff_const.prodMk contDiff_id))

theorem circleLiftHomeomorph_symm_add_one {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t, F (t + 1) = F t + 1) (hpos : ∀ t, 0 < deriv F t) (s u : ℝ) :
    (circleLiftHomeomorph hF hper hpos s).symm (u + 1) =
      (circleLiftHomeomorph hF hper hpos s).symm u + 1 := by
  apply (circleLiftHomeomorph hF hper hpos s).injective
  rw [Homeomorph.apply_symm_apply, circleLiftHomeomorph_apply, circleLiftHomotopy_add_one hper,
    ← circleLiftHomeomorph_apply hF hper hpos, Homeomorph.apply_symm_apply]

/-! ## Descent to `ℝ/ℤ` -/

/-- The map of `ℝ/ℤ` induced by a map of `ℝ` commuting with `+1`. -/
def addCircleDescent (g : ℝ → ℝ) (hg : ∀ t, g (t + 1) = g t + 1) :
    AddCircle (1 : ℝ) → AddCircle (1 : ℝ) :=
  Periodic.lift (f := fun t : ℝ => (g t : AddCircle (1 : ℝ))) (c := (1 : ℝ)) (fun t => by
    change ((g (t + 1) : ℝ) : AddCircle (1 : ℝ)) = (g t : AddCircle (1 : ℝ))
    rw [hg, AddCircle.coe_add_period])

theorem addCircleDescent_coe (g : ℝ → ℝ) (hg : ∀ t, g (t + 1) = g t + 1) (t : ℝ) :
    addCircleDescent g hg (t : AddCircle (1 : ℝ)) = (g t : AddCircle (1 : ℝ)) :=
  rfl

theorem contMDiff_addCircleDescent {g : ℝ → ℝ} (hg : ∀ t, g (t + 1) = g t + 1)
    (hgs : ContDiff ℝ ∞ g) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (addCircleDescent g hg) := by
  apply AddCircle.isLocalDiffeomorph_coe.contMDiff_of_comp_of_surjective
    QuotientAddGroup.mk_surjective
  change ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => (g t : AddCircle (1 : ℝ)))
  exact AddCircle.contMDiff_coe.comp hgs.contMDiff

/-- The diffeomorphism of `ℝ/ℤ` induced by the homotopy at time `s`. -/
def circleLiftHomotopyDiffeomorph {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t, F (t + 1) = F t + 1) (hpos : ∀ t, 0 < deriv F t) (s : ℝ) :
    AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ) where
  toFun := addCircleDescent (circleLiftHomeomorph hF hper hpos s)
    (circleLiftHomotopy_add_one hper s)
  invFun := addCircleDescent (circleLiftHomeomorph hF hper hpos s).symm
    (circleLiftHomeomorph_symm_add_one hF hper hpos s)
  left_inv z := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
    change (((circleLiftHomeomorph hF hper hpos s).symm
      (circleLiftHomeomorph hF hper hpos s t) : ℝ) : AddCircle (1 : ℝ)) = t
    rw [Homeomorph.symm_apply_apply]
  right_inv z := by
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective z
    change ((circleLiftHomeomorph hF hper hpos s
      ((circleLiftHomeomorph hF hper hpos s).symm t) : ℝ) : AddCircle (1 : ℝ)) = t
    rw [Homeomorph.apply_symm_apply]
  contMDiff_toFun := contMDiff_addCircleDescent (circleLiftHomotopy_add_one hper s)
    ((contDiff_circleLiftHomotopy hF).comp (contDiff_const.prodMk contDiff_id))
  contMDiff_invFun := contMDiff_addCircleDescent (circleLiftHomeomorph_symm_add_one hF hper hpos s)
    (contDiff_circleLiftHomeomorph_symm hF hper hpos s)

theorem circleLiftHomotopyDiffeomorph_coe {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t, F (t + 1) = F t + 1) (hpos : ∀ t, 0 < deriv F t) (s t : ℝ) :
    circleLiftHomotopyDiffeomorph hF hper hpos s (t : AddCircle (1 : ℝ)) =
      (circleLiftHomotopy F s t : AddCircle (1 : ℝ)) :=
  rfl

theorem contMDiff_circleLiftHomotopyDiffeomorph {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t, F (t + 1) = F t + 1) (hpos : ∀ t, 0 < deriv F t) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × AddCircle (1 : ℝ) => circleLiftHomotopyDiffeomorph hF hper hpos p.1 p.2) := by
  have h := AddCircle.contMDiffOn_of_comp_coe (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ))
    (U := (univ : Set ℝ))
    (f := fun p : ℝ × AddCircle (1 : ℝ) => circleLiftHomotopyDiffeomorph hF hper hpos p.1 p.2) (by
      refine ContMDiff.contMDiffOn ?_
      change ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × ℝ => (circleLiftHomotopy F p.1 p.2 : AddCircle (1 : ℝ)))
      exact AddCircle.contMDiff_coe.comp ((contDiff_circleLiftHomotopy hF).contMDiff.comp
        (contMDiff_fst.prodMk_space contMDiff_snd)))
  rw [univ_prod_univ] at h
  exact contMDiffOn_univ.mp h

/-- The isotopy on the circle: `AddCircle.diffeomorphCircle`-conjugate of the descended homotopy. -/
def circleIsotopyFamily {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (hper : ∀ t, F (t + 1) = F t + 1)
    (hpos : ∀ t, 0 < deriv F t) (s : ℝ) : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle :=
  AddCircle.diffeomorphCircle.symm.trans
    ((circleLiftHomotopyDiffeomorph hF hper hpos s).trans AddCircle.diffeomorphCircle)

theorem circleIsotopyFamily_apply {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t, F (t + 1) = F t + 1) (hpos : ∀ t, 0 < deriv F t) (s : ℝ) (z : Circle) :
    circleIsotopyFamily hF hper hpos s z = AddCircle.diffeomorphCircle
      (circleLiftHomotopyDiffeomorph hF hper hpos s (AddCircle.diffeomorphCircle.symm z)) :=
  rfl

theorem contMDiff_circleIsotopyFamily {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t, F (t + 1) = F t + 1) (hpos : ∀ t, 0 < deriv F t) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
      (fun q : ℝ × Circle => circleIsotopyFamily hF hper hpos q.1 q.2) := by
  have h1 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ℝ × Circle => (q.1, AddCircle.diffeomorphCircle.symm q.2)) :=
    contMDiff_fst.prodMk (AddCircle.diffeomorphCircle.symm.contMDiff.comp contMDiff_snd)
  have hfun : (fun q : ℝ × Circle => circleIsotopyFamily hF hper hpos q.1 q.2) =
      (AddCircle.diffeomorphCircle : AddCircle (1 : ℝ) → Circle) ∘
        ((fun p : ℝ × AddCircle (1 : ℝ) => circleLiftHomotopyDiffeomorph hF hper hpos p.1 p.2) ∘
          (fun q : ℝ × Circle => (q.1, AddCircle.diffeomorphCircle.symm q.2))) := by
    funext q
    rfl
  rw [hfun]
  exact AddCircle.diffeomorphCircle.contMDiff.comp
    ((contMDiff_circleLiftHomotopyDiffeomorph hF hper hpos).comp h1)

theorem contMDiff_circleIsotopyFamily_symm {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t, F (t + 1) = F t + 1) (hpos : ∀ t, 0 < deriv F t) :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
      (fun q : ℝ × Circle => (circleIsotopyFamily hF hper hpos q.1).symm q.2) := by
  have h := DifferentialGeometry.Topology.Manifold.contMDiffOn_diffeomorph_family_symm
    (circleIsotopyFamily hF hper hpos) isOpen_univ
    (contMDiff_circleIsotopyFamily hF hper hpos).contMDiffOn
  rw [univ_prod_univ, contMDiffOn_univ] at h
  exact h

/-! ## The negative branch reverses orientation -/

theorem det_eq_of_apply_eq_smul {A : ℝ →L[ℝ] ℝ} {v c : ℝ} (hv : v ≠ 0) (hA : A v = c * v) :
    LinearMap.det A.toLinearMap = c := by
  have h1 : A 1 = c := by
    have h := hA
    rw [show v = v • (1 : ℝ) by simp, map_smul, smul_eq_mul, smul_eq_mul, mul_one] at h
    exact mul_left_cancel₀ hv (h.trans (mul_comm c v))
  have hA' : A.toLinearMap = c • LinearMap.id := by
    apply LinearMap.ext_ring
    simp [h1]
  rw [hA', LinearMap.det_smul, LinearMap.det_id, Module.finrank_self, pow_one, mul_one]

/-- If the lift of the conjugated circle map is orientation-reversing (`ψ ↑t = −↑(F t)` with `F`
increasing), then `f` does not preserve any orientation of the circle. -/
theorem not_preservesOrientation_of_neg_lift (o : ManifoldOrientation (𝓡 1) Circle 1)
    (f : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) {F : ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hper : ∀ t, F (t + 1) = F t + 1) (hpos : ∀ t, 0 < deriv F t)
    (hneg : ∀ t : ℝ, AddCircle.diffeomorphCircle.symm (f (AddCircle.diffeomorphCircle
      (t : AddCircle (1 : ℝ)))) = -(F t : AddCircle (1 : ℝ))) :
    ¬ f.preservesOrientation o o := by
  intro hf
  set C := AddCircle.diffeomorphCircle
  -- a fixed point of the lift: `t₀ + F t₀ ∈ ℤ`
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, ∃ n : ℤ, t₀ + F t₀ = n := by
    have hcont : Continuous (fun t : ℝ => t + F t) :=
      continuous_id.add (hF.continuous)
    have h1 : (fun t : ℝ => t + F t) 1 = F 0 + 2 := by
      simp only
      have := hper 0
      rw [zero_add] at this
      rw [this]
      ring
    obtain ⟨c, -, hc⟩ := intermediate_value_Icc (zero_le_one' ℝ) hcont.continuousOn
      (show ((⌈F 0⌉ : ℤ) : ℝ) ∈ Icc ((fun t : ℝ => t + F t) 0) ((fun t : ℝ => t + F t) 1) from by
        rw [h1]
        simp only [zero_add]
        exact ⟨Int.le_ceil _, by linarith [Int.ceil_lt_add_one (F 0)]⟩)
    exact ⟨c, ⌈F 0⌉, hc⟩
  obtain ⟨n, hn⟩ := ht₀
  have hcoe : ((-F t₀ : ℝ) : AddCircle (1 : ℝ)) = (t₀ : AddCircle (1 : ℝ)) := by
    rw [show -F t₀ = t₀ + (-n : ℤ) • (1 : ℝ) by rw [zsmul_eq_mul]; push_cast; linarith,
      AddCircle.coe_add,
      AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]
  let ψ : AddCircle (1 : ℝ) → AddCircle (1 : ℝ) := fun w => C.symm (f (C w))
  have hψ : ∀ t : ℝ, ψ t = ((-F t : ℝ) : AddCircle (1 : ℝ)) := by
    intro t
    rw [QuotientAddGroup.mk_neg]
    exact hneg t
  have hψfix : ψ t₀ = t₀ := by rw [hψ, hcoe]
  set z₀ : Circle := C (t₀ : AddCircle (1 : ℝ)) with hz₀
  have hfz₀ : f z₀ = z₀ := by
    have h := congrArg C hψfix
    simpa only [ψ, Diffeomorph.apply_symm_apply] using h
  -- `df` at the fixed point has positive determinant
  have hdetf := (preservesOrientation_iff_det_mfderiv_pos_of_apply_eq o z₀ hfz₀).mp hf
  -- differentiability data
  have hmdψ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ψ (t₀ : AddCircle (1 : ℝ)) :=
    ((C.symm.contMDiff.comp (f.contMDiff.comp C.contMDiff)).mdifferentiableAt (by simp))
  have hmdC : ∀ w, MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 1) C w :=
    fun w => C.contMDiff.mdifferentiableAt (by simp)
  have hmdf : MDifferentiableAt (𝓡 1) (𝓡 1) f z₀ := f.contMDiff.mdifferentiableAt (by simp)
  -- `dψ = −F'(t₀)` on the line
  let Dψ : ℝ →L[ℝ] ℝ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ψ (t₀ : AddCircle (1 : ℝ))
  set v : ℝ := AddCircle.parameterTangent (t₀ : AddCircle (1 : ℝ)) with hv
  have hv0 : v ≠ 0 := AddCircle.parameterTangent_ne_zero _
  have hDψ : Dψ v = -deriv F t₀ * v := by
    have h1 := AddCircle.mfderiv_comp_coe hmdψ
    have hfun : (fun y : ℝ => ψ (y : AddCircle (1 : ℝ))) =
        (fun y : ℝ => (y : AddCircle (1 : ℝ))) ∘ (fun y => -F y) := by
      funext y
      exact hψ y
    rw [hfun] at h1
    have hmdcoe : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y : ℝ => (y : AddCircle (1 : ℝ)))
        (-F t₀) := AddCircle.contMDiff_coe.mdifferentiableAt (by simp)
    have hmdneg : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y => -F y) t₀ :=
      (hF.neg.contMDiff).mdifferentiableAt (by simp)
    have h2 := mfderiv_comp_apply t₀ hmdcoe hmdneg (1 : ℝ)
    have hneg' : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y => -F y) t₀ (1 : ℝ) = -deriv F t₀ := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ (fun y => -F y) t₀ 1 = -deriv F t₀
      rw [fderiv_apply_one_eq_deriv]
      exact (hF.differentiable (by simp) t₀).hasDerivAt.neg.deriv
    rw [hneg'] at h2
    let D : ℝ →L[ℝ] ℝ := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y : ℝ => (y : AddCircle (1 : ℝ))) (-F t₀)
    have hlin : D (-deriv F t₀) = -deriv F t₀ * D 1 := by
      rw [← smul_eq_mul, ← D.map_smul, smul_eq_mul, mul_one]
    have hD1 : D 1 = v := by
      change mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y : ℝ => (y : AddCircle (1 : ℝ))) (-F t₀) (1 : ℝ) = v
      rw [← AddCircle.parameterTangent_coe, hcoe]
    have h3 : D (-deriv F t₀) = -deriv F t₀ * v := by rw [hlin, hD1]
    exact h1.symm.trans (h2.trans h3)
  have hdetψ : LinearMap.det Dψ.toLinearMap = -deriv F t₀ := det_eq_of_apply_eq_smul hv0 hDψ
  -- conjugation by `dC`
  let e : ℝ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 1) :=
    (C.mfderivToContinuousLinearEquiv (by simp) (t₀ : AddCircle (1 : ℝ))).toLinearEquiv
  let Df : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) := mfderiv (𝓡 1) (𝓡 1) f z₀
  have hconjpt : ∀ u : ℝ, Df (e u) = e (Dψ u) := by
    intro u
    have hfun : (f : Circle → Circle) ∘ C = C ∘ ψ := by
      funext w
      simp only [Function.comp_apply, ψ, Diffeomorph.apply_symm_apply]
    have h1 := mfderiv_comp_apply_of_eq (t₀ : AddCircle (1 : ℝ)) hmdf (hmdC _) rfl u
    have h2 := mfderiv_comp_apply_of_eq (t₀ : AddCircle (1 : ℝ)) (hmdC (t₀ : AddCircle (1 : ℝ)))
      hmdψ hψfix u
    rw [hfun] at h1
    exact h1.symm.trans h2
  have hconj : (e : ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin 1)) ∘ₗ Dψ.toLinearMap ∘ₗ
      (e.symm : EuclideanSpace ℝ (Fin 1) →ₗ[ℝ] ℝ) = Df.toLinearMap := by
    apply LinearMap.ext
    intro w
    obtain ⟨u, rfl⟩ := e.surjective w
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_coe]
    exact (hconjpt u).symm
  have hdetf' : LinearMap.det Df.toLinearMap = -deriv F t₀ := by
    rw [← hconj, LinearMap.det_conj, hdetψ]
  have hpos₀ := hpos t₀
  change 0 < LinearMap.det Df.toLinearMap at hdetf
  linarith

/-! ## The isotopy -/

/-- **D2S1 input (b1)**: `Diff⁺(S¹)` is connected: an orientation-preserving diffeomorphism of the
circle is joined to the identity by a jointly smooth isotopy (inverses jointly smooth), equal to `f`
for `t < ε` and to the identity for `t > 1 − ε`. -/
theorem exists_circleIsotopy_of_preservesOrientation (o : ManifoldOrientation (𝓡 1) Circle 1)
    (f : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) (hf : f.preservesOrientation o o) :
    ∃ L : ℝ → (Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle),
      ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 1) ∞ (fun x : Circle × ℝ => L x.2 x.1) ∧
      ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 1) ∞ (fun x : Circle × ℝ => (L x.2).symm x.1) ∧
      ∃ ε : ℝ, 0 < ε ∧ (∀ t x, t < ε → L t x = f x) ∧ (∀ t x, 1 - ε < t → L t x = x) := by
  set C := AddCircle.diffeomorphCircle
  let ψ : AddCircle (1 : ℝ) ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ AddCircle (1 : ℝ) := (C.trans f).trans C.symm
  obtain ⟨F, hper, hpos, hbranch⟩ := AddCircle.exists_increasing_diffeomorphism_lift_or_neg ψ
  have hFs : ContDiff ℝ ∞ (F : ℝ → ℝ) := F.contMDiff.contDiff
  have hψF : ∀ t : ℝ, ψ (t : AddCircle (1 : ℝ)) = (F t : AddCircle (1 : ℝ)) := by
    rcases hbranch with h | h
    · exact h
    · exact absurd hf (not_preservesOrientation_of_neg_lift o f hFs hper hpos h)
  have hswap : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 1)) ∞
      (fun x : Circle × ℝ => (x.2, x.1)) := contMDiff_snd.prodMk contMDiff_fst
  refine ⟨circleIsotopyFamily hFs hper hpos, ?_, ?_, 1 / 3, by norm_num, ?_, ?_⟩
  · have hfun : (fun x : Circle × ℝ => circleIsotopyFamily hFs hper hpos x.2 x.1) =
        (fun q : ℝ × Circle => circleIsotopyFamily hFs hper hpos q.1 q.2) ∘
          (fun x : Circle × ℝ => (x.2, x.1)) := rfl
    rw [hfun]
    exact (contMDiff_circleIsotopyFamily hFs hper hpos).comp hswap
  · have hfun : (fun x : Circle × ℝ => (circleIsotopyFamily hFs hper hpos x.2).symm x.1) =
        (fun q : ℝ × Circle => (circleIsotopyFamily hFs hper hpos q.1).symm q.2) ∘
          (fun x : Circle × ℝ => (x.2, x.1)) := rfl
    rw [hfun]
    exact (contMDiff_circleIsotopyFamily_symm hFs hper hpos).comp hswap
  · intro t x ht
    have hΨ : ∀ w, circleLiftHomotopyDiffeomorph hFs hper hpos t w = ψ w := by
      intro w
      obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective w
      change (circleLiftHomotopy F t u : AddCircle (1 : ℝ)) = ψ (u : AddCircle (1 : ℝ))
      rw [circleLiftHomotopy_of_le F (by linarith) u, hψF]
    rw [circleIsotopyFamily_apply, hΨ]
    change C (C.symm (f (C (C.symm x)))) = f x
    rw [Diffeomorph.apply_symm_apply, Diffeomorph.apply_symm_apply]
  · intro t x ht
    have hΨ : ∀ w, circleLiftHomotopyDiffeomorph hFs hper hpos t w = w := by
      intro w
      obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective w
      change (circleLiftHomotopy F t u : AddCircle (1 : ℝ)) = (u : AddCircle (1 : ℝ))
      rw [circleLiftHomotopy_of_ge F (by linarith)]
    rw [circleIsotopyFamily_apply, hΨ, Diffeomorph.apply_symm_apply]

end GC.GraphManifold.Assembly
