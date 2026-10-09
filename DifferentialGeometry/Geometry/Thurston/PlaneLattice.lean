import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import DifferentialGeometry.Geometry.Thurston.PlaneDeck

/-!
# Constructed lattices in integer coordinate hyperplanes

The kernel of an onto real coordinate that is integer on a full lattice contains a full
lattice of its own. Integer combinations of the original basis explicitly span that kernel;
its discreteness comes from the actual inclusion into the original lattice.
-/

set_option autoImplicit false

noncomputable section

open Module Function Submodule
open scoped BigOperators

namespace DifferentialGeometry.Geometry.FlatSurface

section Normed

variable {V : Type*} [instV : NormedAddCommGroup V] [instSpace : NormedSpace ℝ V]
  {ι : Type*} [instIndex : Finite ι]

theorem integerHyperplane_isZLattice (b : Basis ι ℝ V) (ell : V →L[ℝ] ℝ)
    (hel : Surjective ell) (hint : ∀ i, ∃ m : ℤ, ell (b i) = m) :
    let L := ZLattice.comap ℝ (span ℤ (Set.range b)) ell.toLinearMap.ker.subtype
    ∃ hD : DiscreteTopology L, let _instDiscrete : DiscreteTopology L := hD
      IsZLattice ℝ L := by
  classical
  let instFintype : Fintype ι := Fintype.ofFinite ι
  let K := ell.toLinearMap.ker
  let L := ZLattice.comap ℝ (span ℤ (Set.range b)) K.subtype
  let instDiscrete : DiscreteTopology L :=
    ZLattice.comap_discreteTopology ℝ (span ℤ (Set.range b))
      K.subtypeL.continuous K.subtype_injective
  refine ⟨instDiscrete, ⟨?_⟩⟩
  choose m hm using hint
  obtain ⟨i, hi⟩ : ∃ i, (m i : ℝ) ≠ 0 := by
    by_contra! hz
    have he : ell.toLinearMap = 0 := b.ext (by intro i; simp [hm, hz])
    obtain ⟨v, hv⟩ := hel 1
    have h0 : ell v = 0 := LinearMap.congr_fun he v
    linarith
  let w : ι → K := fun j => ⟨m i • b j - m j • b i, by
    change ell (m i • b j - m j • b i) = 0
    simp only [map_sub, map_zsmul, zsmul_eq_mul, hm]
    ring⟩
  have hw (j : ι) : w j ∈ L := by
    change m i • b j - m j • b i ∈ span ℤ (Set.range b)
    have hj : b j ∈ span ℤ (Set.range b) := subset_span ⟨j, rfl⟩
    have hi : b i ∈ span ℤ (Set.range b) := subset_span ⟨i, rfl⟩
    exact (span ℤ (Set.range b)).sub_mem
      ((span ℤ (Set.range b)).smul_mem (m i) hj)
      ((span ℤ (Set.range b)).smul_mem (m j) hi)
  apply top_unique
  intro v hv
  have he : (∑ j, (b.repr (v : V) j / (m i : ℝ)) • w j) = v := by
    apply Subtype.ext
    change K.subtype (∑ j, (b.repr (v : V) j / (m i : ℝ)) • w j) = K.subtype v
    rw [map_sum]
    simp only [map_smul]
    change (∑ j, (b.repr (v : V) j / (m i : ℝ)) •
      (m i • b j - m j • b i)) = (v : V)
    simp_rw [smul_sub, ← Int.cast_smul_eq_zsmul ℝ, smul_smul]
    rw [Finset.sum_sub_distrib]
    have hfirst : (∑ j, (b.repr (v : V) j / (m i : ℝ) * (m i : ℝ)) • b j) = v := by
      simp_rw [div_mul_cancel₀ _ hi]
      exact b.sum_repr v
    rw [hfirst, ← Finset.sum_smul]
    have hs : ∑ j, b.repr (v : V) j * (m j : ℝ) = 0 := by
      have h := congrArg ell (b.sum_repr (v : V))
      rw [map_sum] at h
      simp only [map_smul, hm, smul_eq_mul] at h
      exact h.trans v.property
    have hs' : ∑ j, b.repr (v : V) j / (m i : ℝ) * (m j : ℝ) = 0 := by
      simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div, hs, zero_div]
    rw [hs', zero_smul, sub_zero]
  rw [← he]
  exact (span ℝ (L : Set K)).sum_mem (fun j _hj =>
    (span ℝ (L : Set K)).smul_mem _ (subset_span (hw j)))

theorem exists_integerHyperplane_basis [instFD : FiniteDimensional ℝ V]
    (hdim : finrank ℝ V = 3) (b : Basis ι ℝ V) (ell : V →L[ℝ] ℝ)
    (hel : Surjective ell) (hint : ∀ i, ∃ m : ℤ, ell (b i) = m) :
    ∃ c : Basis (Fin 2) ℝ ell.toLinearMap.ker,
      span ℤ (Set.range c) =
        ZLattice.comap ℝ (span ℤ (Set.range b)) ell.toLinearMap.ker.subtype := by
  let K := ell.toLinearMap.ker
  let L := ZLattice.comap ℝ (span ℤ (Set.range b)) K.subtype
  obtain ⟨hD, hL⟩ := integerHyperplane_isZLattice b ell hel hint
  let instDiscrete : DiscreteTopology L := hD
  let instLattice : IsZLattice ℝ L := hL
  let instFinite : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let instFree : Module.Free ℤ L := ZLattice.module_free ℝ L
  have hK : finrank ℝ K = 2 := by
    have hn : ell.toLinearMap ≠ 0 := LinearMap.surjective_iff_ne_zero.mp hel
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hn
    change finrank ℝ K + 1 = finrank ℝ V at h
    omega
  have hLrank : finrank ℤ L = 2 := (ZLattice.rank ℝ L).trans hK
  let b0 := Module.finBasis ℤ L
  let c := b0.ofZLatticeBasis ℝ L
  let e : Fin (finrank ℤ L) ≃ Fin 2 := Equiv.cast (congrArg Fin hLrank)
  refine ⟨c.reindex e, ?_⟩
  rw [c.range_reindex]
  exact b0.ofZLatticeBasis_span ℝ

end Normed

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V]

theorem exists_cyclicDeck_planeLattice (hdim : finrank ℝ V = 3)
    (G : Subgroup (V ≃ᵃⁱ[ℝ] V)) {R : ℝ}
    (hdisc : ∀ B : ℝ, Set.Finite {a : G | ‖(a : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ B})
    (hcov : ∀ x : V, ∃ k : G, ‖x - (k : V ≃ᵃⁱ[ℝ] V) 0‖ ≤ R)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : V, γ.val x ≠ x)
    (hdet : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearEquiv.toLinearMap)
    (hcyclic : IsCyclic (affineLinearHom.comp G.subtype).range) :
    ∃ (ell : V →L[ℝ] ℝ) (c : Basis (Fin 2) ℝ ell.toLinearMap.ker),
      Surjective ell ∧
      (∀ γ : G, ∀ v, ell (γ.val.linearIsometryEquiv v) = ell v) ∧
      (∀ γ : G, ∃ m : ℤ, ell (γ.val 0) = m) ∧
      (∀ γ : G, ell (γ.val 0) = 0 → ∀ x, γ.val x = x + γ.val 0) ∧
      span ℤ (Set.range c) = ZLattice.comap ℝ (affineTranslationModule G)
        ell.toLinearMap.ker.subtype := by
  obtain ⟨ell, hel, hlin, hint, hkernel⟩ :=
    exists_cyclicDeck_planeCoordinate hdim G hdisc hcov hfree hdet hcyclic
  obtain ⟨b, hb, _hf⟩ := exists_bieberbach_lattice G hdisc hcov hfree
  have hintb (i : Fin (finrank ℝ V)) : ∃ m : ℤ, ell (b i) = m := by
    have hbi : b i ∈ affineTranslationModule G := by
      rw [← hb]
      exact subset_span ⟨i, rfl⟩
    obtain ⟨m, hm⟩ := hint ⟨AffineIsometryEquiv.constVAdd ℝ V (b i), hbi⟩
    exact ⟨m, by simpa using hm⟩
  obtain ⟨c, hc⟩ := exists_integerHyperplane_basis hdim b ell hel hintb
  refine ⟨ell, c, hel, hlin, hint, hkernel, ?_⟩
  rw [hb] at hc
  exact hc

end DifferentialGeometry.Geometry.FlatSurface
