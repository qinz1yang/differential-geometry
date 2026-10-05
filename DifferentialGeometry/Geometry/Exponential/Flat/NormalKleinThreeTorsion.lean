import DifferentialGeometry.Geometry.Exponential.Flat.FourElementRepresentationAverage
import DifferentialGeometry.Geometry.Exponential.Flat.KleinAutomorphismCycle
import DifferentialGeometry.Geometry.Exponential.Flat.OrderThreeLineHolonomy
import DifferentialGeometry.Geometry.Exponential.Flat.TetrahedralTorsion

/-!
An actual normal four-element half-turn point subgroup and a nontrivial order-three motion
cannot occur in a free positive lattice affine group. Conjugation has an actual three-cycle;
its internally derived zero average supplies the genuine tetrahedral torsion obstruction.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem four_cycle_average_trace (K : Type*) [instG : Group K]
    [instF : Fintype K] (hc : Fintype.card K = 4) (T : MulAut K) (hT3 : T ^ 3 = 1)
    (a : K) (ha : T a ≠ a) (rho : K →* (E3 ≃ₗᵢ[ℝ] E3))
    (L : E3 ≃ₗᵢ[ℝ] E3) (hconj : ∀ d, rho (T d) = L * rho d * L⁻¹)
    (hsum : ∀ v : E3, (∑ d : K, rho d v) = 0) :
    ∀ v : E3, L v = v → rho a v + L (rho a v) + (L ^ 2) (rho a v) = -v := by
  classical
  have h3 : T (T (T a)) = a := congrArg (fun f : MulAut K => f a) hT3
  have ha1 : a ≠ 1 := by intro he; simp only [he, map_one] at ha; exact ha rfl
  have ht1 : T a ≠ 1 := by
    intro he
    exact ha1 (T.injective (he.trans T.map_one.symm))
  have htt1 : T (T a) ≠ 1 := by
    intro he
    exact ht1 (T.injective (he.trans T.map_one.symm))
  have htta : T (T a) ≠ a := by
    intro he
    have hh := congrArg T he
    rw [h3] at hh
    exact ha hh.symm
  have httt : T (T a) ≠ T a := by intro he; exact ha (T.injective he)
  have hu : (Finset.univ : Finset K) = {1, a, T a, T (T a)} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hx : x = 1
    · exact Or.inl hx
    · exact Or.inr ((four_group_automorphism_cycle hc T hT3 a ha).mp hx)
  intro v hv
  have hiv : L.symm v = v := by
    apply L.injective
    rw [L.apply_symm_apply, hv]
  have hTv (d : K) : rho (T d) v = L (rho d v) := by
    rw [hconj]
    change L (rho d (L.symm v)) = L (rho d v)
    exact congrArg (fun w : E3 => L (rho d w)) hiv
  have he := hsum v
  rw [hu] at he
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton,
    Ne.symm ha1, Ne.symm ht1, Ne.symm htt1, Ne.symm htta, Ne.symm httt, Ne.symm ha,
    or_self, not_false_eq_true, map_one, LinearIsometryEquiv.coe_one, id_eq] at he
  rw [hTv, hTv, hTv] at he
  change rho a v + L (rho a v) + L (L (rho a v)) = -v
  apply add_eq_zero_iff_eq_neg.mp
  calc
    _ = v + (rho a v + (L (rho a v) + L (L (rho a v)))) := by abel
    _ = 0 := he


theorem affineFree_normalKlein_three_obstruction (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (K : Subgroup (affineLinearHom.comp G.subtype).range)
    [instK : Fintype K] [instN : K.Normal] (hc : Fintype.card K = 4)
    (htwo : ∀ a : K, a.val.val ^ 2 = 1) (g : G)
    (hg3 : g.val.linearIsometryEquiv ^ 3 = 1) (hgn : g.val.linearIsometryEquiv ≠ 1) :
    False := by
  classical
  let H := (affineLinearHom.comp G.subtype).range
  let L := g.val.linearIsometryEquiv
  let rho := H.subtype.comp K.subtype
  have hrho : Function.Injective rho :=
    Subtype.val_injective.comp Subtype.val_injective
  have hpK (a : K) : 0 < LinearMap.det (rho a).toLinearMap := by
    obtain ⟨k, hk⟩ := a.val.property
    change k.val.linearIsometryEquiv = a.val.val at hk
    change 0 < LinearMap.det a.val.val.toLinearMap
    rw [← hk]
    exact hpos k
  have hsum := faithful_four_involutive_sum_zero K hc rho hrho hpK htwo
  let r : H := (affineLinearHom.comp G.subtype).rangeRestrict g
  let nr : Subgroup.normalizer (K : Set H) :=
    ⟨r, by rw [K.normalizer_eq_top]; exact Subgroup.mem_top r⟩
  let T := K.normalizerMonoidHom nr
  have hn3 : nr ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hg3
  have hT3 : T ^ 3 = 1 := by
    change (K.normalizerMonoidHom nr) ^ 3 = 1
    rw [← map_pow, hn3, map_one]
  have hconj (a : K) : rho (T a) = L * rho a * L⁻¹ := rfl
  have hg : g ≠ 1 := by intro he; apply hgn; rw [he]; rfl
  obtain ⟨p, q, hp, hfix⟩ := exists_affineAxis_point g.val
  have hq : q ≠ 0 := by
    intro he
    exact hfree g hg p (by simpa only [he, add_zero] using hp)
  have hm : ∃ a : K, T a ≠ a := by
    by_contra hn
    have hTfix (a : K) : T a = a := by
      by_contra he
      exact hn ⟨a, he⟩
    have hfixed (a : K) : rho a q = q := by
      have he := hconj a
      rw [hTfix] at he
      have hm := congrArg (fun R : E3 ≃ₗᵢ[ℝ] E3 => R * L) he
      have hmul : rho a * L = L * rho a := by
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm
      have hcL : rho a * L * (rho a)⁻¹ = L := by
        rw [hmul, mul_assoc, mul_inv_cancel, mul_one]
      rcases orderThree_normalizer_preserves_axis L (rho a) hg3 hgn (hpos g)
          (Or.inl hcL) q hq hfix with he | he
      · exact he
      · exfalso
        obtain ⟨k, hk⟩ := a.val.property
        change k.val.linearIsometryEquiv = rho a at hk
        have hk2 : k.val.linearIsometryEquiv ^ 2 = 1 := by rw [hk]; exact htwo a
        have hkq : k.val.linearIsometryEquiv q = -q := by rw [hk]; exact he
        have hkgq : (k * g).val.linearIsometryEquiv q = -q := by
          change k.val.linearIsometryEquiv (L q) = -q
          rw [hfix]
          exact hkq
        have hkg2 := affineFree_lineReverse_involution G b hb hfree (k * g)
          (hpos (k * g)) q hq hkgq
        change (k.val.linearIsometryEquiv * L) ^ 2 = 1 at hkg2
        have hki := involutions_product_conjugate_inverse k.val.linearIsometryEquiv
          L hk2 hkg2
        exact affineFree_dihedralThree_obstruction G hfree g k hg3 hgn (hpos g)
          hk2 hki q hq hfix hkq
    have he := hsum q
    simp_rw [hfixed] at he
    have hzN : (4 : ℕ) • q = 0 := by
      simpa only [Finset.sum_const, Finset.card_univ, hc] using he
    have hcast : (4 : ℝ) • q = (4 : ℕ) • q := Nat.cast_smul_eq_nsmul ℝ 4 q
    have hz : (4 : ℝ) • q = 0 := hcast.trans hzN
    exact hq ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  obtain ⟨a, ha⟩ := hm
  obtain ⟨k, hk⟩ := a.val.property
  change k.val.linearIsometryEquiv = rho a at hk
  apply affineFree_tetrahedral_obstruction G hfree g k hg3 hgn
  intro v hv
  rw [hk]
  exact four_cycle_average_trace K hc T hT3 a ha rho L hconj hsum v hv

end DifferentialGeometry.Geometry.FlatSurface
