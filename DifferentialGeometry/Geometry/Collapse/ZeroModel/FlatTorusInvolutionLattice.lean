import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.GroupTheory.Archimedean
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Glide reflections of a plane lattice: the affine glide–lattice normal form

Lane LFR54-Q0, group G3 (lattice algebra; the form frozen by external review 41, §5.3). Let `E`
be a two-dimensional real inner product space, `Λ ⊆ E` a discrete full-rank `ℤ`-lattice and
`σ z = A z + b` with `A` orthogonal, `A Λ ⊆ Λ`, `A² = 1`, `det A < 0`, `A b + b ∈ Λ` (so `σ²` is a
lattice translation) and `σ` free MODULO `Λ`: `A z + b - z ∉ Λ` for every `z`. Then
(`exists_glide_lattice_normal_form`) `Λ = ℤ u ⊕ ℤ v` for an orthogonal pair `u, v` with
`A u = u`, `A v = -v`, and `A q + b - q = (j + ½) u` for some `q` and some integer `j`.

The proof is the projection argument of §5.4: `P₊ λ = ⟪u₀, λ⟫ u₀` lies in `½ (Λ ∩ E₊)`, freeness
is `P₊ b ∉ P₊ Λ`, and with `2 P₊ b ∈ Λ ∩ E₊` this forces `P₊ Λ = Λ ∩ E₊` and the splitting
`Λ = (Λ ∩ E₊) ⊕ (Λ ∩ E₋)`; the two line lattices are cyclic
(`AddSubgroup.cyclic_of_isolated_zero`, `exists_pos_mem_iff_of_isolated_zero`).

`glide_free_plane_not_free_quotient` is the negative test of §5.5: fixed-point freeness in the
plane does not give freeness on the quotient.
-/

set_option autoImplicit false

noncomputable section

open Module Set
open scoped InnerProductSpace

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

/-- A uniformly discrete nonzero additive subgroup of `ℝ` is `ℤ a` for some `a > 0`. -/
theorem exists_pos_mem_iff_of_isolated_zero (P : AddSubgroup ℝ) {ε : ℝ} (hε : 0 < ε)
    (hdisc : ∀ t ∈ P, |t| < ε → t = 0) {t₀ : ℝ} (ht₀ : t₀ ∈ P) (ht₀0 : t₀ ≠ 0) :
    ∃ a : ℝ, 0 < a ∧ ∀ t, t ∈ P ↔ ∃ m : ℤ, t = m * a := by
  have hd : Disjoint (P : Set ℝ) (Set.Ioo 0 ε) := by
    rw [Set.disjoint_left]
    rintro t ht ⟨h0, h1⟩
    have h := hdisc t ht (by rw [abs_of_pos h0]; exact h1)
    rw [h] at h0
    exact lt_irrefl 0 h0
  obtain ⟨c, hc⟩ := AddSubgroup.cyclic_of_isolated_zero hε hd
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [hc, AddSubgroup.mem_closure_singleton] at ht₀
    obtain ⟨n, hn⟩ := ht₀
    rw [smul_zero] at hn
    exact ht₀0 hn.symm
  refine ⟨|c|, abs_pos.mpr hc0, fun t => ?_⟩
  rw [hc, AddSubgroup.mem_closure_singleton]
  constructor
  · rintro ⟨n, rfl⟩
    rcases abs_choice c with h | h
    · exact ⟨n, by rw [h, zsmul_eq_mul]⟩
    · exact ⟨-n, by rw [h, zsmul_eq_mul]; push_cast; ring⟩
  · rintro ⟨m, rfl⟩
    rcases abs_choice c with h | h
    · exact ⟨m, by rw [h, zsmul_eq_mul]⟩
    · exact ⟨-m, by rw [h, zsmul_eq_mul]; push_cast; ring⟩

section Plane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- In a two-dimensional inner product space, an orthonormal pair decomposes every vector. -/
theorem eq_inner_smul_add_inner_smul_of_orthonormal (hV : finrank ℝ V = 2) {u w : V}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫_ℝ = 0) (v : V) :
    v = ⟪u, v⟫_ℝ • u + ⟪w, v⟫_ℝ • w := by
  have hon : Orthonormal ℝ ![u, w] := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hu, hw, huw, real_inner_comm u w]
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range ![u, w]) := by
    rw [hon.linearIndependent.span_eq_top_of_card_eq_finrank (by simp [hV])]
  let bo : OrthonormalBasis (Fin 2) ℝ V := OrthonormalBasis.mk hon hsp
  have h := bo.sum_repr' v
  rw [Fin.sum_univ_two] at h
  simp only [bo, OrthonormalBasis.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h.symm

/-- **Affine glide–lattice normal form** (review 41, §5.3). Let `Λ` be a discrete full-rank
lattice of a two-dimensional inner product space `E`, `A` an orthogonal involution with
`A Λ ⊆ Λ` and `det A < 0`, and `b` with `A b + b ∈ Λ` such that `z ↦ A z + b` has no fixed point
modulo `Λ`. Then `Λ = ℤ u ⊕ ℤ v` for an orthogonal pair with `A u = u`, `A v = -v`, and
`A q + b - q = (j + ½) u` for some `q` and some integer `j`.

Proof (§5.4): `u` spans `ℤ`-generator of `Λ ∩ E₊`; every `λ + A λ = 2 P₊ λ` lies in `Λ ∩ E₊`, so
`P₊ Λ ⊆ ½ ℤ u`; freeness says `P₊ b ∉ P₊ Λ` (the `E₋`-component of `A z + b - z` is arbitrary),
which together with `2 P₊ b ∈ ℤ u` forces `P₊ b ∈ (ℤ + ½) u` and `P₊ Λ = ℤ u`; then
`P₋ λ = λ - P₊ λ ∈ Λ ∩ E₋ = ℤ v`. -/
theorem exists_glide_lattice_normal_form (hV : finrank ℝ V = 2) (Λ : Submodule ℤ V)
    [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (A : V ≃ₗᵢ[ℝ] V) (b : V) (hAΛ : ∀ l ∈ Λ, A l ∈ Λ) (hA2 : ∀ z, A (A z) = z)
    (hdet : LinearMap.det (A.toLinearEquiv : V →ₗ[ℝ] V) < 0) (hb : A b + b ∈ Λ)
    (hfree : ∀ z, A z + b - z ∉ Λ) :
    ∃ (u v q : V) (j : ℤ), LinearIndependent ℝ ![u, v] ∧ ⟪u, v⟫_ℝ = 0 ∧
      (∀ z, z ∈ Λ ↔ ∃ m n : ℤ, z = m • u + n • v) ∧ A u = u ∧ A v = -v ∧
      A q + b - q = ((j : ℝ) + 1 / 2) • u := by
  -- uniform discreteness
  obtain ⟨ε, hε, hdisc0⟩ := Metric.isOpen_singleton_iff.mp (isOpen_discrete ({0} : Set Λ))
  have hdisc : ∀ l ∈ Λ, ‖l‖ < ε → l = 0 := fun l hl hlt => by
    have h := hdisc0 ⟨l, hl⟩ (by rw [dist_zero_right]; exact hlt)
    exact congrArg Subtype.val h
  have hL1 : ∃ y, A y ≠ y := by
    by_contra hcon
    push Not at hcon
    have hid : (A.toLinearEquiv : V →ₗ[ℝ] V) = LinearMap.id := LinearMap.ext hcon
    rw [hid, LinearMap.det_id] at hdet
    exact absurd hdet (by norm_num)
  -- the axis
  have hnotneg : ∃ x, x + A x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hfree ((1 / 2 : ℝ) • b)
    have h1 : A ((1 / 2 : ℝ) • b) = -((1 / 2 : ℝ) • b) :=
      eq_neg_of_add_eq_zero_right (hcon _)
    rw [h1]
    have h2 : -((1 / 2 : ℝ) • b) + b - (1 / 2 : ℝ) • b = 0 := by
      rw [neg_add_eq_sub, sub_sub, ← add_smul]
      norm_num
    rw [h2]
    exact Λ.zero_mem
  obtain ⟨x₁, hx₁⟩ := hnotneg
  obtain ⟨x₂, hx₂⟩ := hL1
  have hx₂' : x₂ - A x₂ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx₂)
  obtain ⟨u, hu_def⟩ : ∃ u : V, u = ‖x₁ + A x₁‖⁻¹ • (x₁ + A x₁) := ⟨_, rfl⟩
  obtain ⟨w, hw_def⟩ : ∃ w : V, w = ‖x₂ - A x₂‖⁻¹ • (x₂ - A x₂) := ⟨_, rfl⟩
  have hu : ‖u‖ = 1 := by
    rw [hu_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx₁)]
  have hw : ‖w‖ = 1 := by
    rw [hw_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx₂')]
  have hLu : A u = u := by
    rw [hu_def, LinearIsometryEquiv.map_smul, map_add, hA2, add_comm]
  have hLw : A w = -w := by
    rw [hw_def, LinearIsometryEquiv.map_smul, map_sub, hA2, ← smul_neg, neg_sub]
  have huw : ⟪u, w⟫_ℝ = 0 := by
    have h := A.inner_map_map u w
    rw [hLu, hLw, inner_neg_right] at h
    linarith
  have hdec := eq_inner_smul_add_inner_smul_of_orthonormal hV hu hw huw
  -- `A` in the frame `(u, w)`
  have hLv : ∀ v, A v = ⟪u, v⟫_ℝ • u - ⟪w, v⟫_ℝ • w := fun v => by
    conv_lhs => rw [hdec v]
    rw [map_add, LinearIsometryEquiv.map_smul, LinearIsometryEquiv.map_smul, hLu, hLw, smul_neg,
      sub_eq_add_neg]
  have hplus : ∀ v, v + A v = (2 * ⟪u, v⟫_ℝ) • u := fun v => by
    have hv := hdec v
    rw [hLv]
    calc v + (⟪u, v⟫_ℝ • u - ⟪w, v⟫_ℝ • w) =
        (⟪u, v⟫_ℝ • u + ⟪w, v⟫_ℝ • w) + (⟪u, v⟫_ℝ • u - ⟪w, v⟫_ℝ • w) := by rw [← hv]
      _ = (2 * ⟪u, v⟫_ℝ) • u := by rw [mul_smul, two_smul]; abel
  have hminus : ∀ v, v - A v = (2 * ⟪w, v⟫_ℝ) • w := fun v => by
    have hv := hdec v
    rw [hLv]
    calc v - (⟪u, v⟫_ℝ • u - ⟪w, v⟫_ℝ • w) =
        (⟪u, v⟫_ℝ • u + ⟪w, v⟫_ℝ • w) - (⟪u, v⟫_ℝ • u - ⟪w, v⟫_ℝ • w) := by rw [← hv]
      _ = (2 * ⟪w, v⟫_ℝ) • w := by rw [mul_smul, two_smul]; abel
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = ⟪u, b⟫_ℝ := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = ⟪w, b⟫_ℝ := ⟨_, rfl⟩
  have hbdec : b = β • u + γ • w := by rw [hβ, hγ]; exact hdec b
  -- freeness along the normal line: `P₊ b ∉ P₊ Λ`
  have hfree' : ∀ t : ℝ, β • u + t • w ∉ Λ := by
    intro t ht
    apply hfree (((γ - t) / 2) • w)
    have h : A (((γ - t) / 2) • w) + b - ((γ - t) / 2) • w = β • u + t • w := by
      rw [LinearIsometryEquiv.map_smul, hLw, smul_neg]
      conv_lhs => rw [hbdec]
      rw [show γ • w = ((γ - t) / 2) • w + ((γ - t) / 2) • w + t • w by
        rw [← add_smul, ← add_smul]; congr 1; ring]
      abel
    rw [h]
    exact ht
  -- the two line subgroups `Λ ∩ E₊`, `Λ ∩ E₋`
  let Pu : AddSubgroup ℝ := Λ.toAddSubgroup.comap (LinearMap.toSpanSingleton ℝ V u).toAddMonoidHom
  let Pw : AddSubgroup ℝ := Λ.toAddSubgroup.comap (LinearMap.toSpanSingleton ℝ V w).toAddMonoidHom
  have hPu : ∀ t, t ∈ Pu ↔ t • u ∈ Λ := fun t => Iff.rfl
  have hPw : ∀ t, t ∈ Pw ↔ t • w ∈ Λ := fun t => Iff.rfl
  have hdiscu : ∀ t ∈ Pu, |t| < ε → t = 0 := by
    intro t ht hlt
    have h0 := hdisc _ ((hPu t).mp ht) (by rw [norm_smul, hu, mul_one, Real.norm_eq_abs]; exact hlt)
    rcases smul_eq_zero.mp h0 with h | h
    · exact h
    · rw [h, norm_zero] at hu
      exact absurd hu zero_ne_one
  have hdiscw : ∀ t ∈ Pw, |t| < ε → t = 0 := by
    intro t ht hlt
    have h0 := hdisc _ ((hPw t).mp ht) (by rw [norm_smul, hw, mul_one, Real.norm_eq_abs]; exact hlt)
    rcases smul_eq_zero.mp h0 with h | h
    · exact h
    · rw [h, norm_zero] at hw
      exact absurd hw zero_ne_one
  have h2β : 2 * β ∈ Pu := by
    rw [hPu, hβ, ← hplus]
    rwa [add_comm]
  have hβ0 : β ≠ 0 := by
    intro h0
    apply hfree' 0
    rw [h0, zero_smul, zero_smul, add_zero]
    exact Λ.zero_mem
  obtain ⟨a, ha, hPu_iff⟩ :=
    exists_pos_mem_iff_of_isolated_zero Pu hε hdiscu h2β (mul_ne_zero two_ne_zero hβ0)
  -- full rank: a lattice point off the axis
  have hl₀ : ∃ l ∈ Λ, ⟪w, l⟫_ℝ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hle : Submodule.span ℝ (Λ : Set V) ≤ LinearMap.ker (innerₛₗ ℝ w) :=
      Submodule.span_le.mpr fun l hl => by
        simp only [SetLike.mem_coe, LinearMap.mem_ker, innerₛₗ_apply_apply]
        exact hcon l hl
    rw [IsZLattice.span_top] at hle
    have hw0 := hle (Submodule.mem_top (x := w))
    rw [LinearMap.mem_ker, innerₛₗ_apply_apply, real_inner_self_eq_norm_sq, hw] at hw0
    norm_num at hw0
  obtain ⟨l₀, hl₀, hl₀w⟩ := hl₀
  have h2w : 2 * ⟪w, l₀⟫_ℝ ∈ Pw := by
    rw [hPw, ← hminus]
    exact Λ.sub_mem hl₀ (hAΛ l₀ hl₀)
  obtain ⟨d, hd, hPw_iff⟩ :=
    exists_pos_mem_iff_of_isolated_zero Pw hε hdiscw h2w (mul_ne_zero two_ne_zero hl₀w)
  -- parity: `P₊ b ∈ (ℤ + ½) a u`
  obtain ⟨m₀, hm₀⟩ := (hPu_iff _).mp h2β
  have hodd : ∀ j : ℤ, β ≠ j * a := by
    intro j hj
    apply hfree' 0
    rw [zero_smul, add_zero, ← hPu, hPu_iff]
    exact ⟨j, hj⟩
  obtain ⟨k, hk⟩ : ∃ k : ℤ, β = (k + 1 / 2) * a := by
    rcases Int.even_or_odd m₀ with ⟨j, hj⟩ | ⟨j, hj⟩
    · exfalso
      apply hodd j
      rw [hj] at hm₀
      push_cast at hm₀
      linarith
    · refine ⟨j, ?_⟩
      rw [hj] at hm₀
      push_cast at hm₀
      linarith
  -- `P₊ Λ = ℤ a u` and `P₋ Λ = ℤ d w`
  have hcoordu : ∀ l ∈ Λ, ∃ m : ℤ, ⟪u, l⟫_ℝ = m * a := by
    intro l hl
    have h2 : 2 * ⟪u, l⟫_ℝ ∈ Pu := by
      rw [hPu, ← hplus]
      exact Λ.add_mem hl (hAΛ l hl)
    obtain ⟨j, hj⟩ := (hPu_iff _).mp h2
    rcases Int.even_or_odd j with ⟨i, hi⟩ | ⟨i, hi⟩
    · refine ⟨i, ?_⟩
      rw [hi] at hj
      push_cast at hj
      linarith
    · exfalso
      rw [hi] at hj
      push_cast at hj
      have hka : ((k - i : ℤ) : ℝ) * a ∈ Pu := (hPu_iff _).mpr ⟨k - i, rfl⟩
      have hl' : l + (((k - i : ℤ) : ℝ) * a) • u ∈ Λ := Λ.add_mem hl ((hPu _).mp hka)
      apply hfree' (⟪w, l⟫_ℝ)
      have heq : l + (((k - i : ℤ) : ℝ) * a) • u = β • u + ⟪w, l⟫_ℝ • w := by
        conv_lhs => rw [hdec l]
        rw [hk, show ⟪u, l⟫_ℝ = (i + 1 / 2) * a by linarith]
        rw [add_right_comm, ← add_smul]
        congr 2
        push_cast
        ring
      rw [← heq]
      exact hl'
  have hcoordw : ∀ l ∈ Λ, ∃ n : ℤ, ⟪w, l⟫_ℝ = n * d := by
    intro l hl
    obtain ⟨m, hm⟩ := hcoordu l hl
    have hmu : ⟪u, l⟫_ℝ • u ∈ Λ := (hPu _).mp ((hPu_iff _).mpr ⟨m, hm⟩)
    have hw' : ⟪w, l⟫_ℝ • w ∈ Λ := by
      have h := Λ.sub_mem hl hmu
      have hl' := hdec l
      rwa [show l - ⟪u, l⟫_ℝ • u = ⟪w, l⟫_ℝ • w by
        calc l - ⟪u, l⟫_ℝ • u = (⟪u, l⟫_ℝ • u + ⟪w, l⟫_ℝ • w) - ⟪u, l⟫_ℝ • u := by rw [← hl']
          _ = ⟪w, l⟫_ℝ • w := by abel] at h
    exact (hPw_iff _).mp ((hPw _).mpr hw')
  -- the normal form
  have hau : a • u ∈ Λ := (hPu _).mp ((hPu_iff _).mpr ⟨1, by rw [Int.cast_one, one_mul]⟩)
  have hdw : d • w ∈ Λ := (hPw _).mp ((hPw_iff _).mpr ⟨1, by rw [Int.cast_one, one_mul]⟩)
  refine ⟨a • u, d • w, (γ / 2) • w, k, ?_, ?_, fun z => ⟨fun hz => ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun z => ⟪u, z⟫_ℝ) hst
    have h2 := congrArg (fun z => ⟪w, z⟫_ℝ) hst
    have huw' : ⟪w, u⟫_ℝ = 0 := by rw [real_inner_comm]; exact huw
    simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu, hw, huw,
      huw', inner_zero_right] at h1 h2
    constructor
    · nlinarith [mul_pos ha ha]
    · nlinarith [mul_pos hd hd]
  · rw [real_inner_smul_left, real_inner_smul_right, huw, mul_zero, mul_zero]
  · obtain ⟨m, hm⟩ := hcoordu z hz
    obtain ⟨n, hn⟩ := hcoordw z hz
    refine ⟨m, n, ?_⟩
    conv_lhs => rw [hdec z]
    rw [hm, hn, ← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ, smul_smul, smul_smul]
  · rintro ⟨m, n, rfl⟩
    exact Λ.add_mem (Λ.smul_mem m hau) (Λ.smul_mem n hdw)
  · rw [LinearIsometryEquiv.map_smul, hLu]
  · rw [LinearIsometryEquiv.map_smul, hLw, smul_neg]
  · rw [LinearIsometryEquiv.map_smul, hLw, smul_neg, hbdec,
      show -((γ / 2) • w) + (β • u + γ • w) - (γ / 2) • w = β • u by
        rw [show γ • w = (γ / 2) • w + (γ / 2) • w by rw [← add_smul]; congr 1; ring]
        abel,
      hk, smul_smul]

end Plane

/-- **Negative test (review 41, §5.5).** For `Λ = ℤ (1, 0) + ℤ (½, 1)`, `A = diag (1, -1)` and
`b = (½, 0)`: `A Λ ⊆ Λ`, `A b + b ∈ Λ`, and `z ↦ A z + b` has no fixed point in the plane, but it
has one modulo `Λ`: `A z + b - z ∈ Λ` at `z = (0, -½)`. So the freeness hypothesis of
`exists_glide_lattice_normal_form` cannot be weakened to plane fixed-point freeness. -/
theorem glide_free_plane_not_free_quotient :
    let Λ : Submodule ℤ (ℝ × ℝ) := Submodule.span ℤ {((1 : ℝ), (0 : ℝ)), ((1 / 2 : ℝ), (1 : ℝ))}
    let A : ℝ × ℝ → ℝ × ℝ := fun z => (z.1, -z.2)
    let b : ℝ × ℝ := ((1 / 2 : ℝ), (0 : ℝ))
    (∀ l ∈ Λ, A l ∈ Λ) ∧ A b + b ∈ Λ ∧ (∀ z, A z + b ≠ z) ∧
      A ((0 : ℝ), (-1 / 2 : ℝ)) + b - ((0 : ℝ), (-1 / 2 : ℝ)) ∈ Λ := by
  intro Λ A b
  have h10 : ((1 : ℝ), (0 : ℝ)) ∈ Λ := Submodule.subset_span (by simp)
  have hh1 : ((1 / 2 : ℝ), (1 : ℝ)) ∈ Λ := Submodule.subset_span (by simp)
  let A' : (ℝ × ℝ) →ₗ[ℤ] (ℝ × ℝ) :=
    { toFun := A
      map_add' := fun x y => by simp only [A, Prod.fst_add, Prod.snd_add, neg_add, Prod.mk_add_mk]
      map_smul' := fun m x => by
        simp only [A, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, Prod.smul_mk, smul_neg] }
  refine ⟨fun l hl => ?_, ?_, fun z hz => ?_, ?_⟩
  · have hle : Λ ≤ Λ.comap A' := by
      refine Submodule.span_le.mpr ?_
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · change A ((1 : ℝ), (0 : ℝ)) ∈ Λ
        simpa [A] using h10
      · change A ((1 / 2 : ℝ), (1 : ℝ)) ∈ Λ
        have h := Λ.sub_mem h10 hh1
        have he : ((1 : ℝ), (0 : ℝ)) - ((1 / 2 : ℝ), (1 : ℝ)) = A ((1 / 2 : ℝ), (1 : ℝ)) := by
          simp only [A, Prod.mk_sub_mk]
          norm_num
        rwa [he] at h
    exact hle hl
  · have he : A b + b = ((1 : ℝ), (0 : ℝ)) := by
      simp only [A, b, Prod.mk_add_mk]
      norm_num
    rw [he]
    exact h10
  · have h1 := congrArg Prod.fst hz
    simp only [A, b, Prod.fst_add] at h1
    linarith
  · have he : A ((0 : ℝ), (-1 / 2 : ℝ)) + b - ((0 : ℝ), (-1 / 2 : ℝ)) =
        ((1 / 2 : ℝ), (1 : ℝ)) := by
      simp only [A, b, Prod.mk_add_mk, Prod.mk_sub_mk]
      norm_num
    rw [he]
    exact hh1

end DifferentialGeometry.Geometry.Collapse.ZeroModel
