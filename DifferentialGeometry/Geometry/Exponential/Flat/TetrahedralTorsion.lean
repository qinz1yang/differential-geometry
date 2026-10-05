import DifferentialGeometry.Geometry.Exponential.Flat.AffineScrewPeriods

/-!
The actual tetrahedral cycle and half-turn relation forces a torsion lift in a free affine group.
The cube translation is rotated inside the actual translation module, and its corrected lift
has order dividing three. No primitive axis or diagonal integer lattice is supplied as input.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V]

theorem affineFree_tetrahedral_obstruction (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : V, γ.val x ≠ x) (g k : G)
    (hA : g.val.linearIsometryEquiv ^ 3 = 1) (hne : g.val.linearIsometryEquiv ≠ 1)
    (htrace : ∀ v : V, g.val.linearIsometryEquiv v = v →
      k.val.linearIsometryEquiv v + g.val.linearIsometryEquiv (k.val.linearIsometryEquiv v) +
        (g.val.linearIsometryEquiv ^ 2) (k.val.linearIsometryEquiv v) = -v) : False := by
  have hg : g ≠ 1 := by
    intro h
    apply hne
    simp only [h, Subgroup.coe_one]
    rfl
  obtain ⟨p, q, hq0, hp, hq, h3q, hu, hpow⟩ :=
    exists_affineScrew_period G hfree g hg 3 (by decide) hA
  let u := (3 : ℝ) • q
  have hfix : g.val.linearIsometryEquiv u = u := by rw [map_smul, hq]
  have hv := affineTranslationModule_linear_mem G k hu
  let v := k.val.linearIsometryEquiv u
  let a : G := ⟨AffineIsometryEquiv.constVAdd ℝ V v * g.val, G.mul_mem hv g.property⟩
  have ha (x : V) : a.val x = v + g.val x := rfl
  have hlin : a.val.linearIsometryEquiv = g.val.linearIsometryEquiv := by
    change affineLinearHom (AffineIsometryEquiv.constVAdd ℝ V v * g.val) = _
    rw [map_mul]
    rfl
  have han : a ≠ 1 := by
    intro he
    apply hne
    rw [← hlin, he]
    rfl
  have hgadd (x y : V) : g.val (x + y) = g.val.linearIsometryEquiv x + g.val y :=
    g.val.map_vadd y x
  have hsum : v + g.val.linearIsometryEquiv v +
      g.val.linearIsometryEquiv (g.val.linearIsometryEquiv v) = -u := htrace u hfix
  have hpoint : (a.val ^ 3) p = p := by
    change v + g.val (v + g.val (v + g.val p)) = p
    simp only [hgadd]
    change v + (g.val.linearIsometryEquiv v +
      (g.val.linearIsometryEquiv (g.val.linearIsometryEquiv v) + (g.val ^ 3) p)) = p
    rw [affineAxis_pow_apply g.val hp hq]
    change v + (g.val.linearIsometryEquiv v +
      (g.val.linearIsometryEquiv (g.val.linearIsometryEquiv v) + (p + u))) = p
    rw [← add_assoc, ← add_assoc, hsum]
    abel
  have hL3 : (a.val ^ 3).linearIsometryEquiv = 1 := by
    change affineLinearHom (a.val ^ 3) = 1
    rw [map_pow]
    change a.val.linearIsometryEquiv ^ 3 = 1
    rw [hlin]
    exact hA
  have hz : (a.val ^ 3) 0 = 0 := by
    rw [affineIsometry_apply, hL3] at hpoint
    change p + (a.val ^ 3) 0 = p at hpoint
    exact add_eq_left.mp hpoint
  have hae : a ^ 3 = 1 := by
    apply Subtype.ext
    apply AffineIsometryEquiv.ext
    intro x
    change (a.val ^ 3) x = x
    rw [affineIsometry_apply, hL3, hz]
    exact add_zero x
  exact affineFree_no_finiteOrder G hfree han
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, hae⟩)

end DifferentialGeometry.Geometry.FlatSurface
