import DifferentialGeometry.Geometry.Exponential.Flat.EuclideanAxis
import Mathlib.GroupTheory.Torsion

/-!
Actual powers of a Euclidean screw motion translate its constructed axis. Freeness excludes
finite-order nonidentity elements. A positive period of the actual linear part produces a
nonzero vector in the actual translation module, without supplying a lattice or axis.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V]

theorem affineAxis_pow_apply (g : V ≃ᵃⁱ[ℝ] V) {p q : V}
    (hp : g p = p + q) (hq : g.linearIsometryEquiv q = q) (n : ℕ) :
    (g ^ n) p = p + (n : ℝ) • q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    change g ((g ^ n) p) = p + ((n + 1 : ℕ) : ℝ) • q
    rw [ih]
    have hv := g.map_vadd p ((n : ℝ) • q)
    change g ((n : ℝ) • q + p) = g.linearIsometryEquiv ((n : ℝ) • q) + g p at hv
    change g (p + (n : ℝ) • q) = _
    rw [add_comm p, hv, map_smul, hq, hp, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel

variable [instFD : FiniteDimensional ℝ V]

theorem affineFree_no_finiteOrder (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : V, g.val x ≠ x) {g : G} (hg : g ≠ 1) :
    ¬ IsOfFinOrder g := by
  intro ht
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp ht
  obtain ⟨p, q, hp, hq⟩ := exists_affineAxis_point g.val
  have hv : (g.val ^ n) p = p := by
    have h := congrArg (fun γ : G => γ.val p) hpow
    simpa using h
  have hz : (n : ℝ) • q = 0 := by
    rw [affineAxis_pow_apply g.val hp hq] at hv
    exact add_eq_left.mp hv
  have hq0 : q = 0 := (smul_eq_zero.mp hz).resolve_left (by exact_mod_cast hn.ne')
  exact hfree g hg p (by simpa only [hq0, add_zero] using hp)

theorem exists_affineScrew_period (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : V, g.val x ≠ x)
    (g : G) (hg : g ≠ 1) (n : ℕ) (hn : 0 < n)
    (hlin : g.val.linearIsometryEquiv ^ n = 1) :
    ∃ p q : V, q ≠ 0 ∧ g.val p = p + q ∧ g.val.linearIsometryEquiv q = q ∧
      (n : ℝ) • q ≠ 0 ∧ (n : ℝ) • q ∈ affineTranslationModule G ∧
      g.val ^ n = AffineIsometryEquiv.constVAdd ℝ V ((n : ℝ) • q) := by
  obtain ⟨p, q, hp, hq⟩ := exists_affineAxis_point g.val
  have hq0 : q ≠ 0 := by
    intro hz
    exact hfree g hg p (by simpa only [hz, add_zero] using hp)
  have he : g.val ^ n = AffineIsometryEquiv.constVAdd ℝ V ((n : ℝ) • q) := by
    have hL : (g.val ^ n).linearIsometryEquiv = 1 := by
      change affineLinearHom (g.val ^ n) = 1
      rw [map_pow]
      exact hlin
    have hzero : (g.val ^ n) 0 = (n : ℝ) • q := by
      have h := affineAxis_pow_apply g.val hp hq n
      rw [affineIsometry_apply, hL] at h
      change p + (g.val ^ n) 0 = p + (n : ℝ) • q at h
      exact add_left_cancel h
    ext x
    rw [affineIsometry_apply, hL, hzero]
    change x + (n : ℝ) • q = (n : ℝ) • q + x
    exact add_comm x _
  refine ⟨p, q, hq0, hp, hq, ?_, ?_, he⟩
  · exact smul_ne_zero (by exact_mod_cast hn.ne') hq0
  · change AffineIsometryEquiv.constVAdd ℝ V ((n : ℝ) • q) ∈ G
    rw [← he]
    exact G.pow_mem g.property n

end DifferentialGeometry.Geometry.FlatSurface
