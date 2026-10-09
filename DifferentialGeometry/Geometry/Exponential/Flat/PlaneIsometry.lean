import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Plane isometries and lattices (shared by SF4 and the flat-torus lane SF-FT)

* `isometry_of_fderiv_norm_le`, `exists_affineIsometryEquiv_of_fderiv_norm_le`: a bijection of a
  real normed space which is differentiable, with inverse differentiable, and whose derivatives
  never increase norms, is an affine isometry (mean value inequality and Mazur–Ulam).
* `linearIsometryEquiv_eq_refl_of_fixed_vector`, `linearIsometryEquiv_apply_eq_of_fixedPoint_free`,
  `apply_eq_add_of_fixedPoint_free`: in a two-dimensional inner product space, an affine isometry with
  orientation-preserving linear part and no fixed point is a translation.
* `isZLattice_of_cocompact`, `exists_basis_span_eq_of_discrete_of_cocompact`: a discrete subgroup
  whose translates of a ball cover the space has an `ℝ`-basis that is a `ℤ`-basis of it.
-/

set_option autoImplicit false

noncomputable section

open Set Module Submodule

namespace DifferentialGeometry.Geometry.FlatSurface

section MeanValue

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A differentiable map whose derivative never increases norms is `1`-Lipschitz. -/
theorem dist_le_of_fderiv_norm_le {f : V → V} (hf : Differentiable ℝ f)
    (hf' : ∀ y v, ‖fderiv ℝ f y v‖ ≤ ‖v‖) (x y : V) : dist (f x) (f y) ≤ dist x y := by
  have hb : ∀ z ∈ (univ : Set V), ‖fderiv ℝ f z‖ ≤ 1 := fun z _ =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [one_mul]; exact hf' z v
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := f) (hf := fun z _ => hf z)
    (bound := hb) (hs := convex_univ) (xs := mem_univ y) (ys := mem_univ x)
  rw [one_mul] at h
  rwa [dist_eq_norm, dist_eq_norm]

/-- A bijection which is differentiable both ways with norm-nonincreasing derivatives is an
isometry. -/
theorem isometry_of_fderiv_norm_le (f : V ≃ V) (hf : Differentiable ℝ f)
    (hf' : ∀ y v, ‖fderiv ℝ f y v‖ ≤ ‖v‖) (hfs : Differentiable ℝ f.symm)
    (hfs' : ∀ y v, ‖fderiv ℝ f.symm y v‖ ≤ ‖v‖) : Isometry f := by
  refine Isometry.of_dist_eq fun x y => le_antisymm (dist_le_of_fderiv_norm_le hf hf' x y) ?_
  have h := dist_le_of_fderiv_norm_le hfs hfs' (f x) (f y)
  rwa [f.symm_apply_apply, f.symm_apply_apply] at h

/-- Mazur–Ulam form: such a bijection is an affine isometry. -/
theorem exists_affineIsometryEquiv_of_fderiv_norm_le (f : V ≃ V) (hf : Differentiable ℝ f)
    (hf' : ∀ y v, ‖fderiv ℝ f y v‖ ≤ ‖v‖) (hfs : Differentiable ℝ f.symm)
    (hfs' : ∀ y v, ‖fderiv ℝ f.symm y v‖ ≤ ‖v‖) : ∃ A : V ≃ᵃⁱ[ℝ] V, ⇑A = ⇑f := by
  let e : V ≃ᵢ V := ⟨f, isometry_of_fderiv_norm_le f hf hf' hfs hfs'⟩
  exact ⟨e.toRealAffineIsometryEquiv, by rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv]; rfl⟩

end MeanValue

section Plane

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- In dimension two, an orientation-preserving linear isometry fixing a nonzero vector is the
identity. -/
theorem linearIsometryEquiv_eq_refl_of_fixed_vector (hV : finrank ℝ V = 2) (L : V ≃ₗᵢ[ℝ] V)
    (hdet : 0 < LinearMap.det ((L : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V)) {v : V} (hv : v ≠ 0)
    (hLv : L v = v) (w : V) : L w = w := by
  classical
  have : Fact (finrank ℝ V = 1 + 1) := ⟨hV⟩
  set K : Submodule ℝ V := (ℝ ∙ v)ᗮ
  have hK : finrank ℝ K = 1 := finrank_orthogonal_span_singleton hv
  obtain ⟨w₀, hw₀ne⟩ : ∃ w₀ : K, w₀ ≠ 0 := by
    have : 0 < finrank ℝ K := by rw [hK]; exact one_pos
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp this
    exact ⟨x, hx⟩
  have hLK : L (w₀ : V) ∈ K := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    have h0 : inner ℝ v (w₀ : V) = 0 :=
      (Submodule.mem_orthogonal_singleton_iff_inner_right).mp w₀.2
    rw [← hLv, LinearIsometryEquiv.inner_map_map, h0]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w₀ hw₀ne).mp hK ⟨L w₀, hLK⟩
  have hc' : L (w₀ : V) = c • (w₀ : V) := by
    have := congrArg Subtype.val hc
    simpa using this.symm
  have hw₀V : (w₀ : V) ≠ 0 := fun h => hw₀ne (Subtype.ext h)
  have hvw : inner ℝ v (w₀ : V) = 0 :=
    (Submodule.mem_orthogonal_singleton_iff_inner_right).mp w₀.2
  have hli : LinearIndependent ℝ ![v, (w₀ : V)] := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ?_
    · intro i; fin_cases i <;> simpa
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · simpa using hvw
      · simpa [real_inner_comm] using hvw
      · exact absurd rfl hij
  have hcard : Fintype.card (Fin 2) = finrank ℝ V := by simp [hV]
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = v := by simp [b]
  have hb1 : b 1 = (w₀ : V) := by simp [b]
  have hL0 : L (b 0) = b 0 := by rw [hb0, hLv]
  have hL1 : L (b 1) = c • b 1 := by rw [hb1, hc']
  have hdetc : LinearMap.det ((L : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V) = c := by
    rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply]
    erw [hL0, hL1]
    simp [Basis.repr_self]
  have hnorm : ‖c • (w₀ : V)‖ = ‖(w₀ : V)‖ := by rw [← hc', L.norm_map]
  rw [norm_smul, Real.norm_eq_abs] at hnorm
  have habs : |c| = 1 := by
    have hpos : 0 < ‖(w₀ : V)‖ := norm_pos_iff.mpr hw₀V
    nlinarith [hnorm, abs_nonneg c]
  have hc1 : c = 1 := by
    rcases abs_eq (zero_le_one) |>.mp habs with h | h
    · exact h
    · rw [hdetc, h] at hdet; norm_num at hdet
  have hLb : ∀ i, L (b i) = b i := by
    intro i; fin_cases i
    · simpa [hb0] using hLv
    · simp only [Fin.mk_one, hb1]; rw [hc', hc1, one_smul]
  have hext : (L : V →ₗ[ℝ] V) = LinearMap.id := b.ext fun i => by simpa using hLb i
  simpa using LinearMap.congr_fun hext w

/-- In dimension two, an affine isometry with orientation-preserving linear part and without
fixed points has trivial linear part. -/
theorem linearIsometryEquiv_apply_eq_of_fixedPoint_free (hV : finrank ℝ V = 2) (A : V ≃ᵃⁱ[ℝ] V)
    (hdet : 0 < LinearMap.det ((A.linearIsometryEquiv : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V))
    (hfree : ∀ y, A y ≠ y) (v : V) : A.linearIsometryEquiv v = v := by
  set L := A.linearIsometryEquiv
  have hA : ∀ y, A y = L y + A 0 := fun y => by
    simpa using A.map_vadd (0 : V) y
  by_contra hne
  let T : V →ₗ[ℝ] V := ((L : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V) - LinearMap.id
  have hT : ∀ w, T w = L w - w := fun w => rfl
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hw0
    have hLw : L w = w := by rw [hT, sub_eq_zero] at hw; exact hw
    exact hne (linearIsometryEquiv_eq_refl_of_fixed_vector hV L hdet hw0 hLw v)
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hinj) (-(A 0))
  apply hfree y
  rw [hA y]
  rw [hT] at hy
  linear_combination (norm := abel) hy

/-- In dimension two, an orientation-preserving affine isometry without fixed points is a
translation. -/
theorem apply_eq_add_of_fixedPoint_free (hV : finrank ℝ V = 2) (A : V ≃ᵃⁱ[ℝ] V)
    (hdet : 0 < LinearMap.det ((A.linearIsometryEquiv : V ≃ₗ[ℝ] V) : V →ₗ[ℝ] V))
    (hfree : ∀ y, A y ≠ y) (y : V) : A y = y + A 0 := by
  have := A.map_vadd (0 : V) y
  simp only [vadd_eq_add, add_zero] at this
  rw [this, linearIsometryEquiv_apply_eq_of_fixedPoint_free hV A hdet hfree y]

end Plane

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A discrete subgroup whose `R`-neighbourhood is the whole space spans the space. -/
theorem isZLattice_of_cocompact (L : Submodule ℤ V) [DiscreteTopology L] {R : ℝ}
    (hcov : ∀ y : V, ∃ l ∈ L, ‖y - l‖ ≤ R) : IsZLattice ℝ L := by
  refine ⟨?_⟩
  by_contra hne
  obtain ⟨f, hf0, hfker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by
    by_contra h; push Not at h; exact hf0 (LinearMap.ext h)
  let F : V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap f
  set C := ‖F‖
  have hRpos : 0 ≤ R := by
    obtain ⟨l, -, hl⟩ := hcov 0; exact (norm_nonneg _).trans hl
  set t : ℝ := (C * R + 1) / f u
  obtain ⟨l, hl, hdist⟩ := hcov (t • u)
  have hfl : f l = 0 := hfker (Submodule.subset_span hl)
  have hval : f (t • u - l) = C * R + 1 := by
    rw [map_sub, map_smul, hfl, sub_zero, smul_eq_mul, div_mul_cancel₀ _ hu]
  have hbound : |f (t • u - l)| ≤ C * R := by
    have h1 : |f (t • u - l)| ≤ C * ‖t • u - l‖ := by
      have := F.le_opNorm (t • u - l)
      simpa [F, Real.norm_eq_abs] using this
    exact h1.trans (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))
  rw [hval, abs_of_pos (by positivity)] at hbound
  linarith

/-- A discrete cocompact subgroup has an `ℝ`-basis of the space which `ℤ`-spans it. -/
theorem exists_basis_span_eq_of_discrete_of_cocompact (L : Submodule ℤ V) [DiscreteTopology L]
    {R : ℝ} (hcov : ∀ y : V, ∃ l ∈ L, ‖y - l‖ ≤ R) :
    ∃ b : Basis (Fin (finrank ℝ V)) ℝ V, span ℤ (range b) = L := by
  have := isZLattice_of_cocompact L hcov
  let b₀ := Module.Free.chooseBasis ℤ L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = finrank ℝ V := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  let b₁ : Basis (Fin (finrank ℝ V)) ℤ L := b₀.reindex (Fintype.equivFinOfCardEq hcard)
  exact ⟨b₁.ofZLatticeBasis ℝ L, b₁.ofZLatticeBasis_span ℝ L⟩

end Lattice

end DifferentialGeometry.Geometry.FlatSurface
