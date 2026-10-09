import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFiniteAlgebra
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFiniteAbelianization
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFiniteTriangleGroup

/-!
# Finite central extensions with spherical triangle filling relations

The fibre quotient is an actual image of the spherical triangle group. The original relations
also make the abelianization finite. Schur's theorem then proves finiteness of the group.
This is an algebraic consumer; actual manifold generator and relation identifications are separate.
-/

set_option autoImplicit false
noncomputable section

universe u v

namespace GC.Seifert

private theorem closedTriangleGenerators_map
    {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (x : Fin 3 → G) (z : G)
    (hgen : Subgroup.closure (Set.range x ∪ {z}) = ⊤) :
    Subgroup.closure (Set.range (fun i => f (x i)) ∪ {f z}) = ⊤ := by
  have hs : f '' (Set.range x ∪ {z}) = Set.range (fun i => f (x i)) ∪ {f z} := by
    simp only [Set.image_union, ← Set.range_comp', Set.image_singleton]
  rw [← hs, ← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective f hf]

theorem finite_closedTriangleCentralExtension
    (G : Type u) [Group G] (x : Fin 3 → G) (z : G)
    (p : Fin 3 → ℕ) (q : Fin 3 → ℤ) (hp : ∀ i, 2 ≤ p i)
    (hgen : Subgroup.closure (Set.range x ∪ {z}) = ⊤)
    (hboundary : x 0 * x 2 * x 1 = 1)
    (hfill : ∀ i, x i ^ p i * z ^ q i = 1)
    (hz : ∀ g : G, g * z = z * g)
    (hchi : 1 < (1 : ℝ) / p 0 + 1 / p 1 + 1 / p 2)
    (heuler : q 0 * (p 1 : ℤ) * p 2 + q 1 * (p 0 : ℤ) * p 2 +
      q 2 * (p 0 : ℤ) * p 1 ≠ 0) : Finite G := by
  have hcentral : Subgroup.zpowers z ≤ Subgroup.center G :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_center_iff.mpr hz)
  let : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center hcentral
  let π : G →* G ⧸ Subgroup.zpowers z := QuotientGroup.mk' (Subgroup.zpowers z)
  have hπz : π z = 1 := (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z)
  have hπfill : ∀ i, π (x i) ^ p i = 1 := by
    intro i
    have h := congrArg π (hfill i)
    simpa only [map_mul, map_pow, map_zpow, hπz, one_zpow, mul_one, map_one] using h
  have hπboundary : π (x 0) * (π (x 2) * π (x 1)) = 1 := by
    simpa only [map_mul, map_one, mul_assoc] using congrArg π hboundary
  have hπzero : π (x 0) = (π (x 2) * π (x 1))⁻¹ :=
    eq_inv_of_mul_eq_one_left hπboundary
  have hπyx : (π (x 2) * π (x 1)) ^ p 0 = 1 := by
    have h := hπfill 0
    rw [hπzero, inv_pow, inv_eq_one] at h
    exact h
  let f := sphericalTriangleHom (p 1) (p 2) (p 0) (π (x 1)) (π (x 2))
    (hπfill 1) (hπfill 2) hπyx
  have hsurj : Function.Surjective f := by
    have hle : Subgroup.closure (Set.range x ∪ {z}) ≤ f.range.comap π := by
      apply (Subgroup.closure_le (f.range.comap π)).mpr
      intro g hg
      rcases hg with hg | hg
      · obtain ⟨i, rfl⟩ := hg
        fin_cases i
        · refine ⟨(sphericalTriangleY (p 1) (p 2) (p 0) *
            sphericalTriangleX (p 1) (p 2) (p 0))⁻¹, ?_⟩
          simp only [map_inv, map_mul, sphericalTriangleHom_X, sphericalTriangleHom_Y, f]
          exact hπzero.symm
        · exact ⟨sphericalTriangleX (p 1) (p 2) (p 0), sphericalTriangleHom_X _ _ _ _ _ _ _ _⟩
        · exact ⟨sphericalTriangleY (p 1) (p 2) (p 0), sphericalTriangleHom_Y _ _ _ _ _ _ _ _⟩
      · obtain rfl := hg
        exact ⟨1, (map_one f).trans hπz.symm⟩
    rw [hgen] at hle
    intro g
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.zpowers z) g
    exact hle (Subgroup.mem_top a)
  have hchiQ : (1 : ℚ) < 1 / p 0 + 1 / p 1 + 1 / p 2 := by
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_one, Rat.cast_add, Rat.cast_div, Rat.cast_natCast] using hchi
  have : Finite (SphericalTriangleGroup (p 1) (p 2) (p 0)) :=
    finite_sphericalTriangleGroup (p 1) (p 2) (p 0) (hp 1) (hp 2) (hp 0) (by linarith)
  have : Finite (G ⧸ Subgroup.zpowers z) := Finite.of_surjective f hsurj
  let a : G →* Abelianization G := Abelianization.of
  have ha : Function.Surjective a := by
    intro g
    induction g using Quotient.inductionOn with
    | h g => exact ⟨g, rfl⟩
  have hab : a (x 0) * a (x 2) * a (x 1) = 1 := by
    simpa only [map_mul, map_one] using congrArg a hboundary
  have haf : ∀ i, a (x i) ^ p i * a z ^ q i = 1 := by
    intro i
    simpa only [map_mul, map_pow, map_zpow, map_one] using congrArg a (hfill i)
  have : Finite (Abelianization G) := finite_closedTriangleAbelianGroup (Abelianization G)
    (fun i => a (x i)) (a z) p q (fun i => Nat.lt_of_lt_of_le (by decide) (hp i))
    (closedTriangleGenerators_map a ha x z hgen)
    hab haf heuler
  exact finite_of_finite_fibreQuotient_abelianization z hz

end GC.Seifert
