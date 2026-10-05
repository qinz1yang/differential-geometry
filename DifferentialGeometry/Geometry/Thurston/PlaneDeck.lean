import DifferentialGeometry.Geometry.Exponential.Flat.PlaneIsometry
import DifferentialGeometry.Geometry.Exponential.Flat.AffineTranslations
import DifferentialGeometry.Geometry.Thurston.CyclicCovector
import DifferentialGeometry.Geometry.Exponential.Flat.Bieberbach
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Actual zero-increment deck actions on an invariant plane

An orientation-preserving free affine isometry in dimension three that preserves an onto real
coordinate and has zero coordinate increment restricts to a genuine free plane isometry. Its
quotient linear map is the identity, so the actual plane determinant is positive. The plane
translation theorem and ambient orthogonality then show that the original map is a translation.
-/

set_option autoImplicit false

noncomputable section

open Module Function

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V]

theorem affine_translation_of_zero_coordinate (hdim : finrank ℝ V = 3)
    (ell : V →L[ℝ] ℝ) (hel : Surjective ell) (γ : V ≃ᵃⁱ[ℝ] V)
    (hlin : ∀ v, ell (γ.linearIsometryEquiv v) = ell v) (hzero : ell (γ 0) = 0)
    (hdet : 0 < LinearMap.det γ.linearIsometryEquiv.toLinearEquiv.toLinearMap)
    (hfree : ∀ x, γ x ≠ x) (x : V) : γ x = x + γ 0 := by
  classical
  let K := ell.toLinearMap.ker
  let A := γ.linearIsometryEquiv
  have hker : ∀ v ∈ K, A v ∈ K := by
    intro v hv
    change ell (A v) = 0
    rw [hlin]
    exact hv
  have hinv (v : V) : ell (A⁻¹ v) = ell v := by
    have h := hlin (A⁻¹ v)
    change ell (A (A⁻¹ v)) = ell (A⁻¹ v) at h
    have hc : A (A⁻¹ v) = v := by
      change (A * A⁻¹) v = v
      rw [mul_inv_cancel]
      rfl
    rw [hc] at h
    exact h.symm
  let L : K →ₗᵢ[ℝ] K :=
    { A.toLinearEquiv.toLinearMap.restrict hker with norm_map' := fun v => A.norm_map v }
  have hs : Surjective L := by
    intro v
    have hv : A⁻¹ (v : V) ∈ K := by
      change ell (A⁻¹ (v : V)) = 0
      rw [hinv]
      exact v.property
    exact ⟨⟨A⁻¹ v, hv⟩, by apply Subtype.ext; exact A.apply_symm_apply v⟩
  let B : K ≃ₗᵢ[ℝ] K := LinearIsometryEquiv.ofSurjective L hs
  let f : K → K := fun v => ⟨γ v, by
    change ell (γ (v : V)) = 0
    rw [affineIsometry_apply, map_add, hlin, hzero, add_zero]
    exact v.property⟩
  let D : K ≃ᵃⁱ[ℝ] K := AffineIsometryEquiv.mk' f B 0 (by
    intro v
    apply Subtype.ext
    change γ (v : V) = A ((v : V) - 0) + γ 0
    simpa using affineIsometry_apply γ v)
  have hkdim : finrank ℝ K = 2 := by
    have hn : ell.toLinearMap ≠ 0 := LinearMap.surjective_iff_ne_zero.mp hel
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hn
    change finrank ℝ K + 1 = finrank ℝ V at h
    omega
  have hq : K.mapQ K A.toLinearEquiv.toLinearMap hker = LinearMap.id := by
    apply LinearMap.ext
    intro v
    refine Submodule.Quotient.induction_on K v ?_
    intro w
    change Submodule.Quotient.mk (A w) = Submodule.Quotient.mk w
    apply (Submodule.Quotient.eq K).mpr
    change ell (A w - w) = 0
    rw [map_sub, hlin, sub_self]
  have hBdet : 0 < LinearMap.det B.toLinearEquiv.toLinearMap := by
    have he := LinearMap.det_eq_det_mul_det K A.toLinearEquiv.toLinearMap hker
    rw [hq, LinearMap.det_id, mul_one] at he
    change 0 < LinearMap.det (A.toLinearEquiv.toLinearMap.restrict hker)
    rw [← he]
    exact hdet
  have hDdet : 0 < LinearMap.det D.linearIsometryEquiv.toLinearEquiv.toLinearMap := by
    simpa only [D, AffineIsometryEquiv.linearIsometryEquiv_mk'] using hBdet
  have hDfree (v : K) : D v ≠ v := by
    intro he
    exact hfree v (congrArg Subtype.val he)
  have hfix (v : V) (hv : v ∈ K) : A v = v := by
    have h := linearIsometryEquiv_apply_eq_of_fixedPoint_free hkdim D hDdet hDfree ⟨v, hv⟩
    exact congrArg Subtype.val h
  have hAx : A x = x := by
    let w := A x - x
    have hw : w ∈ K := by change ell (A x - x) = 0; rw [map_sub, hlin, sub_self]
    have hwfix := hfix w hw
    have hi := A.inner_map_map x w
    rw [hwfix] at hi
    have hz : inner ℝ w w = 0 := by
      change inner ℝ (A x - x) w = 0
      rw [inner_sub_left, hi, sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)
  rw [affineIsometry_apply, hAx]

theorem exists_cyclicAffine_planeCoordinate {ι : Type*} [instIndex : Finite ι]
    (hdim : finrank ℝ V = 3) (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) (b : Basis ι ℝ V)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (g : G) (hg : g ≠ 1) (hfree : ∀ γ : G, γ ≠ 1 → ∀ x, γ.val x ≠ x)
    (hdet : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearEquiv.toLinearMap)
    (p : ℕ) (hp : 0 < p) (horder : g.val.linearIsometryEquiv ^ p = 1)
    (hcyclic : ∀ γ : G, ∃ k : ℤ,
      γ.val.linearIsometryEquiv = g.val.linearIsometryEquiv ^ k) :
    ∃ ell : V →L[ℝ] ℝ, Surjective ell ∧
      (∀ γ : G, ∀ v, ell (γ.val.linearIsometryEquiv v) = ell v) ∧
      (∀ γ : G, ∃ m : ℤ, ell (γ.val 0) = m) ∧
      ∀ γ : G, ell (γ.val 0) = 0 → ∀ x, γ.val x = x + γ.val 0 := by
  obtain ⟨ell, hel, hlin, hint, _hlat⟩ :=
    exists_cyclicAffine_integerCovector G b hb g (hfree g hg) p hp horder hcyclic
  refine ⟨ell, hel, hlin, hint, ?_⟩
  intro γ hzero x
  by_cases he : γ = 1
  · subst γ
    simp
  · exact affine_translation_of_zero_coordinate hdim ell hel γ.val
      (hlin γ) hzero (hdet γ) (hfree γ he) x

theorem exists_cyclicFreeAction_planeCoordinate (hdim : finrank ℝ V = 3)
    (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {a : G | ‖(a : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ B})
    (hcov : ∀ x : V, ∃ k : G, ‖x - (k : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : V, γ.val x ≠ x)
    (hdet : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearEquiv.toLinearMap)
    (g : G) (hg : g ≠ 1)
    (hcyclic : ∀ γ : G, ∃ k : ℤ,
      γ.val.linearIsometryEquiv = g.val.linearIsometryEquiv ^ k) :
    ∃ ell : V →L[ℝ] ℝ, Surjective ell ∧
      (∀ γ : G, ∀ v, ell (γ.val.linearIsometryEquiv v) = ell v) ∧
      (∀ γ : G, ∃ m : ℤ, ell (γ.val 0) = m) ∧
      ∀ γ : G, ell (γ.val 0) = 0 → ∀ x, γ.val x = x + γ.val 0 := by
  obtain ⟨b, hb, hfinite⟩ := exists_bieberbach_lattice G hdisc hcov hfree
  let φ := affineLinearHom.comp G.subtype
  let instQuotient : Finite (G ⧸ φ.ker) := hfinite
  let instRange : Finite φ.range :=
    Finite.of_equiv (G ⧸ φ.ker) (QuotientGroup.quotientKerEquivRange φ).toEquiv
  let a : φ.range := ⟨φ g, ⟨g, rfl⟩⟩
  obtain ⟨p, hp, hporder⟩ := (isOfFinOrder_of_finite a).exists_pow_eq_one
  have horder : g.val.linearIsometryEquiv ^ p = 1 := congrArg Subtype.val hporder
  exact exists_cyclicAffine_planeCoordinate hdim G b hb g hg hfree hdet p hp horder hcyclic

theorem exists_cyclicDeck_planeCoordinate (hdim : finrank ℝ V = 3)
    (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {a : G | ‖(a : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ B})
    (hcov : ∀ x : V, ∃ k : G, ‖x - (k : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : V, γ.val x ≠ x)
    (hdet : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearEquiv.toLinearMap)
    (hcyclic : IsCyclic (affineLinearHom.comp G.subtype).range) :
    ∃ ell : V →L[ℝ] ℝ, Surjective ell ∧
      (∀ γ : G, ∀ v, ell (γ.val.linearIsometryEquiv v) = ell v) ∧
      (∀ γ : G, ∃ m : ℤ, ell (γ.val 0) = m) ∧
      ∀ γ : G, ell (γ.val 0) = 0 → ∀ x, γ.val x = x + γ.val 0 := by
  classical
  let φ := affineLinearHom.comp G.subtype
  let instCyclic : IsCyclic φ.range := hcyclic
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := φ.range)
  obtain ⟨g, hg⟩ := a.property
  have hgen (γ : G) : ∃ k : ℤ,
      γ.val.linearIsometryEquiv = g.val.linearIsometryEquiv ^ k := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (ha ⟨φ γ, ⟨γ, rfl⟩⟩)
    refine ⟨k, ?_⟩
    have hv := congrArg Subtype.val hk
    change a.val ^ k = φ γ at hv
    rw [← hg] at hv
    exact hv.symm
  by_cases hgone : g = 1
  · have htrivial (γ : G) : γ.val.linearIsometryEquiv = 1 := by
      obtain ⟨k, hk⟩ := hgen γ
      rw [hk, hgone]
      change (1 : V ≃ₗᵢ[ℝ] V) ^ k = 1
      simp
    obtain ⟨b, hb, _hf⟩ := exists_bieberbach_lattice G hdisc hcov hfree
    let i : Fin (finrank ℝ V) := ⟨0, by omega⟩
    have hbi : b i ∈ affineTranslationModule G := by
      rw [← hb]
      exact Submodule.subset_span ⟨i, rfl⟩
    let g' : G := ⟨AffineIsometryEquiv.constVAdd ℝ V (b i), hbi⟩
    have hg' : g' ≠ 1 := by
      intro he
      have hz := congrArg (fun a : G => a.val 0) he
      have hb0 : b i = 0 := by simpa [g'] using hz
      exact b.ne_zero i hb0
    have hgen' (γ : G) : ∃ k : ℤ,
        γ.val.linearIsometryEquiv = g'.val.linearIsometryEquiv ^ k := by
      exact ⟨0, by simpa using htrivial γ⟩
    exact exists_cyclicFreeAction_planeCoordinate hdim G hdisc hcov hfree hdet g' hg' hgen'
  · exact exists_cyclicFreeAction_planeCoordinate hdim G hdisc hcov hfree hdet g hgone hgen

end DifferentialGeometry.Geometry.FlatSurface
