import DifferentialGeometry.Geometry.Exponential.Flat.BasedRotations
import DifferentialGeometry.Geometry.Exponential.Flat.NearConjugateAxes

/-!
# Translation restriction for small rotations in free Euclidean actions

Actual axes and their distances give a contraction argument for a discrete cocompact free
Euclidean action. The translation conclusion is derived from the action, rather than supplied
as a small-rotation assumption.
-/

set_option autoImplicit false

noncomputable section

open Set Submodule

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V]

def affineAxisPoint (g : V ≃ᵃⁱ[ℝ] V) : V := (exists_affineAxis_point g).choose

def affineAxisVector (g : V ≃ᵃⁱ[ℝ] V) : V :=
  (exists_affineAxis_point g).choose_spec.choose

theorem affineAxisPoint_apply (g : V ≃ᵃⁱ[ℝ] V) :
    g (affineAxisPoint g) = affineAxisPoint g + affineAxisVector g :=
  (exists_affineAxis_point g).choose_spec.choose_spec.1

theorem affineAxisVector_fixed (g : V ≃ᵃⁱ[ℝ] V) :
    g.linearIsometryEquiv (affineAxisVector g) = affineAxisVector g :=
  (exists_affineAxis_point g).choose_spec.choose_spec.2

def affineAxis (g : V ≃ᵃⁱ[ℝ] V) : Set V :=
  {p | g.linearIsometryEquiv (g p - p) = g p - p}

theorem mem_affineAxis_iff {g : V ≃ᵃⁱ[ℝ] V} {p : V} :
    p ∈ affineAxis g ↔ g p = p + affineAxisVector g := by
  constructor
  · intro hp
    have hq := affine_axis_vector_unique g (affineAxisPoint_apply g)
      (affineAxisVector_fixed g) (p := affineAxisPoint g) (p' := p)
      (q' := g p - p) (by abel) hp
    rw [hq]
    abel
  · intro hp
    change g.linearIsometryEquiv (g p - p) = g p - p
    rw [hp, add_sub_cancel_left, affineAxisVector_fixed]

theorem affineAxis_nonempty (g : V ≃ᵃⁱ[ℝ] V) : (affineAxis g).Nonempty :=
  ⟨affineAxisPoint g, mem_affineAxis_iff.mpr (affineAxisPoint_apply g)⟩

theorem affineAxisVector_conjugate (g k : V ≃ᵃⁱ[ℝ] V) :
    affineAxisVector (k * g * k⁻¹) = k.linearIsometryEquiv (affineAxisVector g) := by
  obtain ⟨hp, hq⟩ := affine_axis_conjugate g k
    (affineAxisPoint_apply g) (affineAxisVector_fixed g)
  exact affine_axis_vector_unique (k * g * k⁻¹)
    (affineAxisPoint_apply _) (affineAxisVector_fixed _) hp hq

theorem affineAxis_sub_vector (g : V ≃ᵃⁱ[ℝ] V) {p : V} (hp : p ∈ affineAxis g) :
    p - affineAxisVector g ∈ affineAxis g := by
  apply mem_affineAxis_iff.mpr
  have hf := affineIsometry_apply g (p - affineAxisVector g)
  have hfp := affineIsometry_apply g p
  rw [mem_affineAxis_iff.mp hp] at hfp
  rw [g.linearIsometryEquiv.map_sub, affineAxisVector_fixed] at hf
  linear_combination (norm := abel) hf - hfp

theorem affineAxis_image (g k : V ≃ᵃⁱ[ℝ] V) {p : V} (hp : p ∈ affineAxis g) :
    k p ∈ affineAxis (k * g * k⁻¹) := by
  apply mem_affineAxis_iff.mpr
  rw [affineAxisVector_conjugate]
  exact (affine_axis_conjugate g k (mem_affineAxis_iff.mp hp)
    (affineAxisVector_fixed g)).1

theorem affine_axis_contraction (g k : V ≃ᵃⁱ[ℝ] V) {p p' : V}
    (hp : p ∈ affineAxis g) (hp' : p' ∈ affineAxis (k * g * k⁻¹)) :
    ‖(k * g * k⁻¹) (p - affineAxisVector g) - p‖ ≤
      affineRotationNorm g * ‖p - p'‖ + affineRotationNorm k * ‖affineAxisVector g‖ := by
  let h := k * g * k⁻¹
  let q := affineAxisVector g
  have hpval := mem_affineAxis_iff.mp hp'
  rw [affineAxisVector_conjugate] at hpval
  have hformula := affine_axis_displacement_formula h hpval (p - q)
  have hfixed : h.linearIsometryEquiv (k.linearIsometryEquiv q) =
      k.linearIsometryEquiv q := by
    exact (affine_axis_conjugate g k (mem_affineAxis_iff.mp hp)
      (affineAxisVector_fixed g)).2
  have heq : h (p - q) - p =
      (affineLinearOperator h - ContinuousLinearMap.id ℝ V) (p - p') +
        h.linearIsometryEquiv ((affineLinearOperator k - ContinuousLinearMap.id ℝ V) q) := by
    change h (p - q) - p = (h.linearIsometryEquiv (p - p') - (p - p')) +
      h.linearIsometryEquiv (k.linearIsometryEquiv q - q)
    simp only [h.linearIsometryEquiv.map_sub, hfixed]
    dsimp [q] at hformula ⊢
    rw [h.linearIsometryEquiv.map_sub, h.linearIsometryEquiv.map_sub] at hformula
    linear_combination (norm := abel) hformula
  rw [heq]
  have hb := (norm_add_le
    ((affineLinearOperator h - ContinuousLinearMap.id ℝ V) (p - p'))
    (h.linearIsometryEquiv ((affineLinearOperator k - ContinuousLinearMap.id ℝ V) q)))
    |>.trans (add_le_add (ContinuousLinearMap.le_opNorm _ _)
      (by simpa only [LinearIsometryEquiv.norm_map] using
        ContinuousLinearMap.le_opNorm (affineLinearOperator k - ContinuousLinearMap.id ℝ V) q))
  change ‖(affineLinearOperator h - ContinuousLinearMap.id ℝ V) (p - p') +
    h.linearIsometryEquiv ((affineLinearOperator k - ContinuousLinearMap.id ℝ V) q)‖ ≤
    affineRotationNorm h * ‖p - p'‖ + affineRotationNorm k * ‖q‖ at hb
  simpa only [h, affineRotationNorm_conjugate] using hb

theorem smallRotation_is_translation (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {a : G | ‖(a : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ B})
    (hcov : ∀ x : V, ∃ k : G, ‖x - (k : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R)
    (hfree : ∀ a : G, a ≠ 1 → ∀ x : V, (a : V ≃ᵃⁱ[ℝ] V) x ≠ x)
    (g : G) (hrot : affineRotationNorm (g : V ≃ᵃⁱ[ℝ] V) < 1 / 4) :
    (g : V ≃ᵃⁱ[ℝ] V).linearIsometryEquiv = 1 := by
  classical
  let q := affineAxisVector (g : V ≃ᵃⁱ[ℝ] V)
  let p₀ := affineAxisPoint (g : V ≃ᵃⁱ[ℝ] V)
  obtain ⟨η, c, hη, hc, hsep⟩ :=
    exists_near_conjugate_axis_separation G hdisc hcov hfree g q
  let ε := min (min η 1) (c / (8 * (‖q‖ + 1)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεη : ε ≤ η := (min_le_left _ _).trans (min_le_left _ _)
  have hεone : ε ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hεq : ε * ‖q‖ < c / 4 := by
    have hb : ε * (8 * (‖q‖ + 1)) ≤ c :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith [norm_nonneg q]
  let C : Set G := {h | ∃ k : G, affineRotationNorm (k : V ≃ᵃⁱ[ℝ] V) < ε ∧
    h = k * g * k⁻¹ ∧ h ≠ g}
  by_contra hnot
  have hC : C.Nonempty := by
    by_contra he
    have hcomm : ∀ k : G, affineRotationNorm (k : V ≃ᵃⁱ[ℝ] V) < ε →
        k * g * k⁻¹ = g := by
      intro k hk
      by_contra hne
      exact he ⟨k * g * k⁻¹, k, hk, rfl, hne⟩
    let F := ((g : V ≃ᵃⁱ[ℝ] V).linearIsometryEquiv : V →ₗ[ℝ] V) - LinearMap.id
    have hspan := smallRotation_displacements_span_at G hcov hε p₀
    have hle : Submodule.span ℝ {v | ∃ k : G,
        affineRotationNorm (k : V ≃ᵃⁱ[ℝ] V) < ε ∧ (k : V ≃ᵃⁱ[ℝ] V) p₀ - p₀ = v} ≤
        F.ker := by
      apply Submodule.span_le.mpr
      rintro v ⟨k, hk, rfl⟩
      have haxis := affineAxis_image (g : V ≃ᵃⁱ[ℝ] V) (k : V ≃ᵃⁱ[ℝ] V)
        (mem_affineAxis_iff.mpr (affineAxisPoint_apply (g : V ≃ᵃⁱ[ℝ] V)))
      change (k : V ≃ᵃⁱ[ℝ] V) p₀ ∈ affineAxis
        ((k * g * k⁻¹ : G) : V ≃ᵃⁱ[ℝ] V) at haxis
      rw [hcomm k hk] at haxis
      have heq := (g : V ≃ᵃⁱ[ℝ] V).map_vsub ((k : V ≃ᵃⁱ[ℝ] V) p₀) p₀
      rw [mem_affineAxis_iff.mp haxis, affineAxisPoint_apply] at heq
      exact sub_eq_zero.mpr (by simpa [F] using heq)
    rw [hspan] at hle
    have hz : F = 0 := LinearMap.ker_eq_top.mp (top_le_iff.mp hle)
    apply hnot
    ext v
    have hv := congrArg (fun L : V →ₗ[ℝ] V => L v) hz
    exact sub_eq_zero.mp hv
  let D : Set ℝ := {r | ∃ h ∈ C, ∃ p ∈ affineAxis (g : V ≃ᵃⁱ[ℝ] V),
    ∃ p' ∈ affineAxis (h : V ≃ᵃⁱ[ℝ] V), r = ‖p - p'‖}
  have hD : D.Nonempty := by
    obtain ⟨h, hh⟩ := hC
    obtain ⟨p, hp⟩ := affineAxis_nonempty (g : V ≃ᵃⁱ[ℝ] V)
    obtain ⟨p', hp'⟩ := affineAxis_nonempty (h : V ≃ᵃⁱ[ℝ] V)
    exact ⟨‖p - p'‖, h, hh, p, hp, p', hp', rfl⟩
  have hDc : ∀ r ∈ D, c ≤ r := by
    rintro r ⟨h, ⟨k, hk, heq, hne⟩, p, hp, p', hp', rfl⟩
    by_contra hlt
    subst h
    have hp'val := mem_affineAxis_iff.mp hp'
    change (↑k * ↑g * (↑k)⁻¹ : V ≃ᵃⁱ[ℝ] V) p' =
      p' + affineAxisVector (↑k * ↑g * (↑k)⁻¹) at hp'val
    rw [affineAxisVector_conjugate] at hp'val
    exact hne (hsep k (hk.trans_le hεη) p p'
      (mem_affineAxis_iff.mp hp) hp'val (lt_of_not_ge hlt))
  have hDb : BddBelow D := ⟨c, hDc⟩
  let d := sInf D
  have hcd : c ≤ d := le_csInf hD hDc
  have hd : 0 < d := hc.trans_le hcd
  obtain ⟨r, hr, hrd⟩ := (csInf_lt_iff hDb hD).mp (by linarith : sInf D < 2 * d)
  obtain ⟨h, hh, p, hp, p', hp', rfl⟩ := hr
  obtain ⟨k, hk, heq, hne⟩ := hh
  subst h
  let h : G := k * g * k⁻¹
  let k' : G := h * g⁻¹
  have hk' : affineRotationNorm (k' : V ≃ᵃⁱ[ℝ] V) < ε := by
    have hb := affineRotationNorm_commutator (k : V ≃ᵃⁱ[ℝ] V) (g : V ≃ᵃⁱ[ℝ] V)
    change affineRotationNorm (k' : V ≃ᵃⁱ[ℝ] V) ≤
      2 * affineRotationNorm (k : V ≃ᵃⁱ[ℝ] V) * affineRotationNorm
        (g : V ≃ᵃⁱ[ℝ] V) at hb
    have hkg : 0 ≤ affineRotationNorm (k : V ≃ᵃⁱ[ℝ] V) := norm_nonneg _
    nlinarith
  have hconj : k' * g * k'⁻¹ = h * g * h⁻¹ := by dsimp [k']; group
  have hnewne : h * g * h⁻¹ ≠ g := by
    intro hn
    have hcomm : Commute (g : V ≃ᵃⁱ[ℝ] V) (h : V ≃ᵃⁱ[ℝ] V) := by
      have he : g * h = h * g := by
        have hv := congrArg (fun a : G => a * h) hn
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using hv.symm
      exact congrArg Subtype.val he
    have hdifference := nearConjugate_axis_points (g : V ≃ᵃⁱ[ℝ] V)
      (k : V ≃ᵃⁱ[ℝ] V) (hk.trans_le hεone) hcomm
      (mem_affineAxis_iff.mp hp) (affineAxisVector_fixed _) (mem_affineAxis_iff.mp hp')
      (affineAxisVector_fixed _)
    have hgp' : (g : V ≃ᵃⁱ[ℝ] V) p' = p' + q := by
      have hv := (g : V ≃ᵃⁱ[ℝ] V).map_vsub p p'
      rw [mem_affineAxis_iff.mp hp] at hv
      change (g : V ≃ᵃⁱ[ℝ] V).linearIsometryEquiv (p - p') =
        p + affineAxisVector (g : V ≃ᵃⁱ[ℝ] V) - (g : V ≃ᵃⁱ[ℝ] V) p' at hv
      rw [hdifference] at hv
      dsimp [q]
      linear_combination (norm := abel) hv
    have hp'val := mem_affineAxis_iff.mp hp'
    change (↑k * ↑g * (↑k)⁻¹ : V ≃ᵃⁱ[ℝ] V) p' =
      p' + affineAxisVector (↑k * ↑g * (↑k)⁻¹) at hp'val
    rw [affineAxisVector_conjugate] at hp'val
    exact hne (hsep k (hk.trans_le hεη) p' p' hgp' hp'val
      (by simpa using hc))
  have hnew : h * g * h⁻¹ ∈ C := ⟨k', hk', hconj.symm, hnewne⟩
  let x := p - q
  have hx : x ∈ affineAxis (g : V ≃ᵃⁱ[ℝ] V) := affineAxis_sub_vector _ hp
  have hy : (h : V ≃ᵃⁱ[ℝ] V) x ∈ affineAxis ((h * g * h⁻¹ : G) : V ≃ᵃⁱ[ℝ] V) :=
    affineAxis_image _ _ hx
  have hb := affine_axis_contraction (g : V ≃ᵃⁱ[ℝ] V) (k : V ≃ᵃⁱ[ℝ] V) hp hp'
  have hkq : affineRotationNorm (k : V ≃ᵃⁱ[ℝ] V) * ‖q‖ < c / 4 :=
    (mul_le_mul_of_nonneg_right hk.le (norm_nonneg q)).trans_lt hεq
  have hsmall : ‖(h : V ≃ᵃⁱ[ℝ] V) x - p‖ < d := by
    have hmul := mul_lt_mul_of_pos_right hrot (by positivity : 0 < 2 * d)
    have hrnon := norm_nonneg (p - p')
    have hgrot : 0 ≤ affineRotationNorm (g : V ≃ᵃⁱ[ℝ] V) := norm_nonneg _
    change ‖(h : V ≃ᵃⁱ[ℝ] V) x - p‖ ≤
      affineRotationNorm (g : V ≃ᵃⁱ[ℝ] V) * ‖p - p'‖ +
        affineRotationNorm (k : V ≃ᵃⁱ[ℝ] V) * ‖q‖ at hb
    nlinarith
  have hmem : ‖p - (h : V ≃ᵃⁱ[ℝ] V) x‖ ∈ D := ⟨h * g * h⁻¹, hnew, p, hp,
    (h : V ≃ᵃⁱ[ℝ] V) x, hy, rfl⟩
  have hdist : ‖p - (h : V ≃ᵃⁱ[ℝ] V) x‖ < d := by
    rw [norm_sub_rev]
    exact hsmall
  exact (not_lt_of_ge (csInf_le hDb hmem)) hdist

theorem affineTranslationModule_span_eq_top (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {a : G | ‖(a : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ B})
    (hcov : ∀ x : V, ∃ k : G, ‖x - (k : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R)
    (hfree : ∀ a : G, a ≠ 1 → ∀ x : V, (a : V ≃ᵃⁱ[ℝ] V) x ≠ x) :
    Submodule.span ℝ (affineTranslationModule G : Set V) = ⊤ := by
  have hs := smallRotation_displacements_span G hcov (by norm_num : (0 : ℝ) < 1 / 4)
  apply top_le_iff.mp
  rw [← hs]
  apply Submodule.span_mono
  rintro v ⟨g, hg, rfl⟩
  apply mem_affineTranslationModule.mpr
  have hlin := smallRotation_is_translation G hdisc hcov hfree g hg
  have heq : AffineIsometryEquiv.constVAdd ℝ V ((g : V ≃ᵃⁱ[ℝ] V) 0) = g := by
    ext x
    rw [affineIsometry_apply (g : V ≃ᵃⁱ[ℝ] V) x, hlin]
    change (g : V ≃ᵃⁱ[ℝ] V) 0 + x = x + (g : V ≃ᵃⁱ[ℝ] V) 0
    exact add_comm _ _
  rw [heq]
  exact g.property

end DifferentialGeometry.Geometry.FlatSurface
