import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Topology.Covering.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# The period lattice of a developing map

For a homeomorphism `φ : E ≃ₜ F` (normed spaces, `E` two-dimensional) turning the periods
`v₁, v₂` (a basis of `E`) into translations by `l₁, l₂`, with a uniformly bounded inverse
derivative, the image lattice `Λ = ℤ l₁ + ℤ l₂` is uniformly discrete and coercive:
`‖n₁ v₁ + n₂ v₂‖ ≤ K ‖n₁ l₁ + n₂ l₂‖`. Consequences: a positive gap, attainment of
`min_{λ ∈ Λ} ‖z − λ‖`, and (for any space `X`) a continuous open surjection `V → X` whose fibres are
the `Λ`-orbits of a uniformly discrete subgroup `Λ` is a covering map.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Function

namespace DifferentialGeometry.Analysis

section Shift

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- An equivariance `f (y + a) = f y + b` iterates to integer multiples. -/
theorem apply_add_zsmul_of_apply_add {f : A → B} {a : A} {b : B}
    (h : ∀ y, f (y + a) = f y + b) (n : ℤ) (y : A) : f (y + n • a) = f y + n • b := by
  induction n using Int.induction_on generalizing y with
  | zero => simp
  | succ n ih => rw [add_smul, one_smul, ← add_assoc, h, ih, add_smul, one_smul, add_assoc]
  | pred n ih =>
    have h' := h (y + (-(n : ℤ) - 1) • a)
    have e : y + (-(n : ℤ) - 1) • a + a = y + (-(n : ℤ)) • a := by
      rw [sub_smul, one_smul]
      abel
    rw [e, ih] at h'
    rw [eq_sub_of_add_eq h'.symm, sub_smul, one_smul]
    abel

/-- Equivariance along two periods iterates to the lattice. -/
theorem apply_add_lattice {f : A → B} {a₁ a₂ : A} {b₁ b₂ : B}
    (h₁ : ∀ y, f (y + a₁) = f y + b₁) (h₂ : ∀ y, f (y + a₂) = f y + b₂) (n₁ n₂ : ℤ) (y : A) :
    f (y + (n₁ • a₁ + n₂ • a₂)) = f y + (n₁ • b₁ + n₂ • b₂) := by
  rw [← add_assoc, apply_add_zsmul_of_apply_add h₂, apply_add_zsmul_of_apply_add h₁, add_assoc]

end Shift

section Lattice

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The inverse of a homeomorphism with uniformly bounded inverse derivative is Lipschitz. -/
theorem norm_symm_sub_le {φ : E ≃ₜ F} {φ' : E → E ≃L[ℝ] F}
    (hφ : ∀ y, HasFDerivAt φ (φ' y : E →L[ℝ] F) y) {K : ℝ}
    (hK : ∀ y, ‖((φ' y).symm : F →L[ℝ] E)‖ ≤ K) (w w' : F) :
    ‖φ.symm w - φ.symm w'‖ ≤ K * ‖w - w'‖ := by
  have hd : ∀ z, HasFDerivAt φ.symm ((φ' (φ.symm z)).symm : F →L[ℝ] E) z := fun z =>
    HasFDerivAt.of_local_left_inverse φ.symm.continuous.continuousAt (hφ (φ.symm z))
      (Filter.Eventually.of_forall fun z' => φ.apply_symm_apply z')
  exact convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hd z).hasFDerivWithinAt) (fun z _ => hK _) (mem_univ w') (mem_univ w)

variable [FiniteDimensional ℝ E]

private theorem exists_coordinate_bound (hE : Module.finrank ℝ E = 2) {v₁ v₂ : E}
    (hli : LinearIndependent ℝ ![v₁, v₂]) :
    ∃ C : ℝ, 0 < C ∧ ∀ n₁ n₂ : ℤ, |(n₁ : ℝ)| ≤ C * ‖n₁ • v₁ + n₂ • v₂‖ ∧
      |(n₂ : ℝ)| ≤ C * ‖n₁ • v₁ + n₂ • v₂‖ := by
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hE])
  have h0 : B 0 = v₁ := by simp [B]
  have h1 : B 1 = v₂ := by simp [B]
  let c₁ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (B.coord 0)
  let c₂ : E →L[ℝ] ℝ := LinearMap.toContinuousLinearMap (B.coord 1)
  have hc : ∀ n₁ n₂ : ℤ, c₁ (n₁ • v₁ + n₂ • v₂) = n₁ ∧ c₂ (n₁ • v₁ + n₂ • v₂) = n₂ := by
    intro n₁ n₂
    simp only [c₁, c₂, LinearMap.coe_toContinuousLinearMap', map_add, map_zsmul, ← h0, ← h1,
      Module.Basis.coord_apply, Module.Basis.repr_self]
    simp
  refine ⟨‖c₁‖ + ‖c₂‖ + 1, by positivity, fun n₁ n₂ => ⟨?_, ?_⟩⟩
  · rw [← (hc n₁ n₂).1, ← Real.norm_eq_abs]
    refine (c₁.le_opNorm _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    linarith [norm_nonneg c₂]
  · rw [← (hc n₁ n₂).2, ← Real.norm_eq_abs]
    refine (c₂.le_opNorm _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    linarith [norm_nonneg c₁]

/-- Coercivity of the image lattice: `|nᵢ| ≤ C ‖n₁ l₁ + n₂ l₂‖`. -/
theorem exists_lattice_coercive (hE : Module.finrank ℝ E = 2) {v₁ v₂ : E}
    (hli : LinearIndependent ℝ ![v₁, v₂]) {φ : E ≃ₜ F} {φ' : E → E ≃L[ℝ] F}
    (hφ : ∀ y, HasFDerivAt φ (φ' y : E →L[ℝ] F) y) {K : ℝ}
    (hK : ∀ y, ‖((φ' y).symm : F →L[ℝ] E)‖ ≤ K) {l₁ l₂ : F}
    (h₁ : ∀ y, φ (y + v₁) = φ y + l₁) (h₂ : ∀ y, φ (y + v₂) = φ y + l₂) :
    ∃ C : ℝ, 0 < C ∧ ∀ n₁ n₂ : ℤ, |(n₁ : ℝ)| ≤ C * ‖n₁ • l₁ + n₂ • l₂‖ ∧
      |(n₂ : ℝ)| ≤ C * ‖n₁ • l₁ + n₂ • l₂‖ := by
  obtain ⟨C, hC, hcoord⟩ := exists_coordinate_bound hE hli
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have hv : ∀ n₁ n₂ : ℤ, ‖n₁ • v₁ + n₂ • v₂‖ ≤ K * ‖n₁ • l₁ + n₂ • l₂‖ := by
    intro n₁ n₂
    have h := norm_symm_sub_le hφ hK (φ (0 + (n₁ • v₁ + n₂ • v₂))) (φ 0)
    rw [φ.symm_apply_apply, φ.symm_apply_apply, apply_add_lattice h₁ h₂] at h
    simpa using h
  refine ⟨C * K + 1, by positivity, fun n₁ n₂ => ⟨?_, ?_⟩⟩ <;>
  · have h1 := hcoord n₁ n₂
    have h2 := hv n₁ n₂
    have h3 := norm_nonneg (n₁ • l₁ + n₂ • l₂)
    nlinarith [mul_le_mul_of_nonneg_left h2 hC.le]

/-- A positive gap of the image lattice. -/
theorem exists_lattice_gap (hE : Module.finrank ℝ E = 2) {v₁ v₂ : E}
    (hli : LinearIndependent ℝ ![v₁, v₂]) {φ : E ≃ₜ F} {φ' : E → E ≃L[ℝ] F}
    (hφ : ∀ y, HasFDerivAt φ (φ' y : E →L[ℝ] F) y) {K : ℝ}
    (hK : ∀ y, ‖((φ' y).symm : F →L[ℝ] E)‖ ≤ K) {l₁ l₂ : F}
    (h₁ : ∀ y, φ (y + v₁) = φ y + l₁) (h₂ : ∀ y, φ (y + v₂) = φ y + l₂) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ n₁ n₂ : ℤ, n₁ • l₁ + n₂ • l₂ ≠ 0 → μ ≤ ‖n₁ • l₁ + n₂ • l₂‖ := by
  obtain ⟨C, hC, hco⟩ := exists_lattice_coercive hE hli hφ hK h₁ h₂
  refine ⟨C⁻¹, by positivity, fun n₁ n₂ hne => ?_⟩
  have hn : n₁ ≠ 0 ∨ n₂ ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (by simp [h.1, h.2])
  have key : 1 ≤ C * ‖n₁ • l₁ + n₂ • l₂‖ := by
    rcases hn with h | h
    · exact le_trans (by exact_mod_cast Int.one_le_abs h) (hco n₁ n₂).1
    · exact le_trans (by exact_mod_cast Int.one_le_abs h) (hco n₁ n₂).2
  rw [inv_le_iff_one_le_mul₀ hC]
  linarith [mul_comm C ‖n₁ • l₁ + n₂ • l₂‖]

/-- The distance to the image lattice is attained. -/
theorem exists_lattice_min (hE : Module.finrank ℝ E = 2) {v₁ v₂ : E}
    (hli : LinearIndependent ℝ ![v₁, v₂]) {φ : E ≃ₜ F} {φ' : E → E ≃L[ℝ] F}
    (hφ : ∀ y, HasFDerivAt φ (φ' y : E →L[ℝ] F) y) {K : ℝ}
    (hK : ∀ y, ‖((φ' y).symm : F →L[ℝ] E)‖ ≤ K) {l₁ l₂ : F}
    (h₁ : ∀ y, φ (y + v₁) = φ y + l₁) (h₂ : ∀ y, φ (y + v₂) = φ y + l₂) (z : F) :
    ∃ n : ℤ × ℤ, ∀ n' : ℤ × ℤ,
      ‖z - (n.1 • l₁ + n.2 • l₂)‖ ≤ ‖z - (n'.1 • l₁ + n'.2 • l₂)‖ := by
  obtain ⟨C, hC, hco⟩ := exists_lattice_coercive hE hli hφ hK h₁ h₂
  set N : ℕ := ⌈C * (2 * ‖z‖)⌉₊
  let S : Finset (ℤ × ℤ) := Finset.Icc (-(N : ℤ)) N ×ˢ Finset.Icc (-(N : ℤ)) N
  have hS0 : ((0 : ℤ), (0 : ℤ)) ∈ S := by simp [S]
  obtain ⟨n, hnS, hmin⟩ := S.exists_min_image (fun n : ℤ × ℤ => ‖z - (n.1 • l₁ + n.2 • l₂)‖)
    ⟨_, hS0⟩
  refine ⟨n, fun n' => ?_⟩
  by_cases hn' : n' ∈ S
  · exact hmin n' hn'
  · refine (hmin _ hS0).trans ?_
    simp only [zero_smul, add_zero, sub_zero]
    by_contra hlt
    push Not at hlt
    apply hn'
    have hL : ‖n'.1 • l₁ + n'.2 • l₂‖ ≤ 2 * ‖z‖ := by
      have := norm_sub_norm_le (n'.1 • l₁ + n'.2 • l₂) z
      rw [norm_sub_rev] at this
      linarith
    have hbound : ∀ m : ℤ, |(m : ℝ)| ≤ C * ‖n'.1 • l₁ + n'.2 • l₂‖ → -(N : ℤ) ≤ m ∧ m ≤ N := by
      intro m hm
      have hmN : |(m : ℝ)| ≤ N :=
        hm.trans ((mul_le_mul_of_nonneg_left hL hC.le).trans (Nat.le_ceil _))
      rw [abs_le] at hmN
      constructor <;> [exact_mod_cast hmN.1; exact_mod_cast hmN.2]
    simp only [S, Finset.mem_product, Finset.mem_Icc]
    exact ⟨hbound _ (hco n'.1 n'.2).1, hbound _ (hco n'.1 n'.2).2⟩

end Lattice

section Covering

variable {V X : Type*} [NormedAddCommGroup V] [TopologicalSpace X]

/-- **Lattice quotients are coverings.** A continuous open surjection whose fibres are the orbits
of a uniformly discrete additive subgroup is a covering map. -/
theorem isCoveringMap_of_lattice_quotient {Ψ : V → X} (hcont : Continuous Ψ)
    (hopen : IsOpenMap Ψ) (hsurj : Surjective Ψ) {Λ : AddSubgroup V}
    (hinv : ∀ w, ∀ l ∈ Λ, Ψ (w + l) = Ψ w) (hfib : ∀ w w', Ψ w = Ψ w' → w' - w ∈ Λ)
    {μ : ℝ} (hμ : 0 < μ) (hgap : ∀ l ∈ Λ, l ≠ 0 → μ ≤ ‖l‖) : IsCoveringMap Ψ := by
  have hdisc : DiscreteTopology Λ := by
    refine discreteTopology_iff_isOpen_singleton.mpr fun l => ?_
    refine isOpen_induced_iff.mpr ⟨ball l.1 μ, isOpen_ball, ?_⟩
    ext l'
    simp only [mem_preimage, mem_ball, mem_singleton_iff]
    constructor
    · intro h
      by_contra hne
      have hsub : l'.1 - l.1 ∈ Λ := Λ.sub_mem l'.2 l.2
      have hne' : l'.1 - l.1 ≠ 0 := fun h0 => hne (Subtype.ext (sub_eq_zero.mp h0))
      have := hgap _ hsub hne'
      rw [← dist_eq_norm] at this
      linarith
    · rintro rfl
      exact mem_ball_self hμ
  have hne' : Nonempty (X → V) := ⟨surjInv hsurj⟩
  set ρ := μ / 4 with hρ
  have hρpos : 0 < ρ := by positivity
  refine IsCoveringMap.mk Ψ (fun _ => Λ) (fun x => IsOpen.trivializationDiscrete (ι := Λ)
      (fun l => ball (surjInv hsurj x + l.1) ρ) (Ψ '' ball (surjInv hsurj x) ρ)
      (hopen _ isOpen_ball) ?_ ?_ ?_ ?_ ?_) fun x => ?_
  · intro l W hWV
    constructor
    · intro hW
      exact (hW.preimage hcont).inter isOpen_ball
    · intro hW
      have himage : Ψ '' (Ψ ⁻¹' W ∩ ball (surjInv hsurj x + l.1) ρ) = W := by
        refine Subset.antisymm (fun _ ⟨z, hz, h⟩ => h ▸ hz.1) fun w hw => ?_
        obtain ⟨z, hz, rfl⟩ := hWV hw
        refine ⟨z + l.1, ⟨?_, ?_⟩, hinv z l.1 l.2⟩
        · rw [mem_preimage, hinv z l.1 l.2]; exact hw
        · rw [mem_ball, dist_add_right]; exact hz
      rw [← himage]
      exact hopen _ hW
  · intro l z hz z' hz' h
    have hsub := hfib z z' h
    by_contra hne
    have hne' : z' - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hg := hgap _ hsub hne'
    have hd : dist z' z < 2 * ρ :=
      (dist_triangle z' (surjInv hsurj x + l.1) z).trans_lt (by
        linarith [mem_ball.mp hz, mem_ball.mp hz', dist_comm (surjInv hsurj x + l.1) z])
    rw [dist_eq_norm] at hd
    linarith
  · rintro l _ ⟨z, hz, rfl⟩
    refine ⟨z + l.1, ?_, hinv z l.1 l.2⟩
    rw [mem_ball, dist_add_right]
    exact hz
  · intro l l' hll'
    refine Set.disjoint_left.mpr fun z hz hz' => hll' (Subtype.ext ?_)
    by_contra hne
    have hsub : l'.1 - l.1 ∈ Λ := Λ.sub_mem l'.2 l.2
    have hne' : l'.1 - l.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have hg := hgap _ hsub hne'
    have hd : dist (surjInv hsurj x + l'.1) (surjInv hsurj x + l.1) < 2 * ρ :=
      (dist_triangle _ z _).trans_lt (by
        linarith [mem_ball.mp hz, mem_ball.mp hz', dist_comm (surjInv hsurj x + l'.1) z])
    rw [dist_add_left, dist_eq_norm] at hd
    linarith
  · rintro z ⟨z', hz', hzz'⟩
    have hsub := hfib z' z hzz'
    refine mem_iUnion.mpr ⟨⟨z - z', hsub⟩, ?_⟩
    simp only [mem_ball]
    rw [show surjInv hsurj x + (z - z') = z + (surjInv hsurj x - z') by abel, dist_eq_norm,
      show z - (z + (surjInv hsurj x - z')) = z' - surjInv hsurj x by abel, ← dist_eq_norm]
    exact hz'
  · exact ⟨surjInv hsurj x, mem_ball_self hρpos, surjInv_eq hsurj x⟩

end Covering

end DifferentialGeometry.Analysis
