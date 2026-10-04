import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Basic.Real.Basic

/-!
# EDP05/EDP06 kernels: independent face differentials and the descended base coordinates

Frozen blueprint master207B, EDP05 (lines 7040–7090) and EDP06 (lines 7092–7133), linear-algebra
steps at one point.

* `ne_zero_of_comp_ne_zero` (EDP05): "The ambient defining differential for `M₂` is nonzero. Since
  it is `D(b ∘ f₂)`, one has `db ≠ 0`."
* `pair_surjective_smul_left` (EDP05): "`db` is a nonzero multiple of `dg_i`. EDP04 gives
  independence of `dg_i` and `dT` at the vertical boundary. Therefore `d(b ∘ f₂)` and `dT` are
  independent." Independence of two functionals is surjectivity of the pair map to `ℝ²`; the same
  surjectivity solves EDP04's equations `Dg_i(X) = 1`, `DT(X) = 0`.
* `bijective_of_comp_surjective_of_finrank_eq_two` (EDP06): "`(g_i, T)` is a smooth function of `E`
  ... Its source differential has rank two by EDP04, and `E` is a submersion to the two-dimensional
  `B₁`. Its descended differential on `B₁` is therefore invertible."
* `corner_base_pair_bijective` (EDP06/FDC03): at a corner the base differentials of the two face
  equations `b(g_i)` (with `b' ≠ 0`) and `T - 4Δ` form an invertible pair on the base.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Collapse.EdgeDisk

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- EDP05: a functional whose composite with a linear map is nonzero is nonzero. -/
theorem ne_zero_of_comp_ne_zero (A : V →ₗ[ℝ] W) (b : W →ₗ[ℝ] ℝ) (h : b ∘ₗ A ≠ 0) : b ≠ 0 := by
  intro hb
  apply h
  rw [hb, LinearMap.zero_comp]

/-- EDP05: replacing one of two independent functionals by a nonzero multiple keeps them
independent (the pair map to `ℝ²` stays onto). -/
theorem pair_surjective_smul_left (g T : V →ₗ[ℝ] ℝ) {c : ℝ} (hc : c ≠ 0)
    (h : Function.Surjective fun v => (g v, T v)) :
    Function.Surjective fun v => (c * g v, T v) := by
  intro y
  obtain ⟨v, hv⟩ := h (y.1 / c, y.2)
  refine ⟨v, ?_⟩
  simp only [Prod.mk.injEq] at hv
  change (c * g v, T v) = y
  rw [hv.1, hv.2, mul_div_cancel₀ _ hc]

/-- EDP06: if a linear map `L` from a two-dimensional space to `ℝ²` becomes onto after
precomposition, it is bijective. -/
theorem bijective_of_comp_surjective_of_finrank_eq_two [FiniteDimensional ℝ W]
    (hW : Module.finrank ℝ W = 2) (A : V →ₗ[ℝ] W) (L : W →ₗ[ℝ] ℝ × ℝ)
    (h : Function.Surjective (L ∘ₗ A)) : Function.Bijective L := by
  have hsurj : Function.Surjective L := by
    intro y
    obtain ⟨v, hv⟩ := h y
    exact ⟨A v, hv⟩
  have hdim : Module.finrank ℝ W = Module.finrank ℝ (ℝ × ℝ) := by
    rw [hW, Module.finrank_prod, Module.finrank_self]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

/-- EDP06/FDC03, corner: with base coordinates `L = (dg_i, dT)` descended from a rank-two source
pair and `b' ≠ 0`, the base differentials `(b' dg_i, dT)` of the two face equations are an
invertible pair. -/
theorem corner_base_pair_bijective [FiniteDimensional ℝ W] (hW : Module.finrank ℝ W = 2)
    (A : V →ₗ[ℝ] W) (L : W →ₗ[ℝ] ℝ × ℝ) (h : Function.Surjective (L ∘ₗ A)) {c : ℝ}
    (hc : c ≠ 0) : Function.Bijective fun w => (c * (L w).1, (L w).2) := by
  have hL := bijective_of_comp_surjective_of_finrank_eq_two hW A L h
  let M : W →ₗ[ℝ] ℝ × ℝ :=
    (c • LinearMap.fst ℝ ℝ ℝ ∘ₗ L).prod (LinearMap.snd ℝ ℝ ℝ ∘ₗ L)
  have hM : ∀ w, M w = (c * (L w).1, (L w).2) := fun w => rfl
  have hsurj : Function.Surjective M := by
    have := pair_surjective_smul_left (LinearMap.fst ℝ ℝ ℝ ∘ₗ L) (LinearMap.snd ℝ ℝ ℝ ∘ₗ L) hc
      (by
        intro y
        obtain ⟨w, hw⟩ := hL.2 y
        exact ⟨w, by simp [hw]⟩)
    intro y
    obtain ⟨w, hw⟩ := this y
    exact ⟨w, by rw [hM]; simpa using hw⟩
  have hdim : Module.finrank ℝ W = Module.finrank ℝ (ℝ × ℝ) := by
    rw [hW, Module.finrank_prod, Module.finrank_self]
  have hbij : Function.Bijective M :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩
  have hfun : (fun w => (c * (L w).1, (L w).2)) = ⇑M := funext fun w => (hM w).symm
  rw [hfun]
  exact hbij

end DifferentialGeometry.Geometry.Collapse.EdgeDisk
