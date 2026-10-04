import DifferentialGeometry.Topology.Manifold.LensSpaceAction
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.StandardPrimes

/-!
# Lens space groups `L(p, q)`

For `p ≥ 1` and an integer `q` coprime to `p`, the cyclic group `ℤ/p` acts on
`S³ ⊂ ℂ²` by `(z, w) ↦ (ζ z, ζ^q w)` with `ζ = exp (2πi/p)`. The action is free, so its
image is a `SphericalSpaceFormGroup` (`lensSpaceFormGroup p q hpq`) of order `p` whose
quotient is the lens space `L(p, q)`; for `q = 1` it is the group `lensSpaceGroup p` of
`L(p, 1)`. The quotient is a standard factor, hence prime.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Metric
open scoped Manifold ContDiff

namespace GC.Seifert

def lensCoordinates : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] WithLp 2 (ℂ × ℂ) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finSumFinEquiv (m := 2) (n := 2)).symm).trans
    (Complex.orthonormalBasisOneI.prod Complex.orthonormalBasisOneI).repr.symm

def lensPairRotation (u v : Circle) :
    EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  lensCoordinates.trans
    ((LinearIsometryEquiv.withLpProdCongr 2 (rotation u) (rotation v)).trans
      lensCoordinates.symm)

theorem lensCoordinates_lensPairRotation (u v : Circle) (x : EuclideanSpace ℝ (Fin 4)) :
    lensCoordinates (lensPairRotation u v x) =
      WithLp.toLp 2 ((u : ℂ) * (lensCoordinates x).fst, (v : ℂ) * (lensCoordinates x).snd) := by
  simp [lensPairRotation, LinearIsometryEquiv.withLpProdCongr_apply, rotation_apply]

theorem lensPairRotation_one : lensPairRotation 1 1 = 1 := by
  ext1 x
  apply lensCoordinates.injective
  rw [lensCoordinates_lensPairRotation]
  simp only [Circle.coe_one, one_mul, LinearIsometryEquiv.coe_one, id]
  rfl

theorem lensPairRotation_mul (u u' v v' : Circle) :
    lensPairRotation (u * u') (v * v') = lensPairRotation u v * lensPairRotation u' v' := by
  ext1 x
  apply lensCoordinates.injective
  rw [LinearIsometryEquiv.coe_mul, Function.comp_apply, lensCoordinates_lensPairRotation,
    lensCoordinates_lensPairRotation, lensCoordinates_lensPairRotation]
  simp [mul_assoc]

private theorem circle_eq_one_of_mul_eq_self {u : Circle} {z : ℂ} (hz : z ≠ 0)
    (h : (u : ℂ) * z = z) : u = 1 := by
  have h0 : ((u : ℂ) - 1) * z = 0 := by rw [sub_mul, one_mul, h, sub_self]
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact Subtype.ext (by simpa using sub_eq_zero.mp h1)
  · exact absurd h1 hz

theorem lensPairRotation_left_eq_one {u v : Circle} {x : EuclideanSpace ℝ (Fin 4)}
    (hx : (lensCoordinates x).fst ≠ 0) (h : lensPairRotation u v x = x) : u = 1 := by
  have h1 := congrArg (fun y => (lensCoordinates y).fst) h
  simp only [lensCoordinates_lensPairRotation, WithLp.toLp_fst] at h1
  exact circle_eq_one_of_mul_eq_self hx h1

theorem lensPairRotation_right_eq_one {u v : Circle} {x : EuclideanSpace ℝ (Fin 4)}
    (hx : (lensCoordinates x).snd ≠ 0) (h : lensPairRotation u v x = x) : v = 1 := by
  have h1 := congrArg (fun y => (lensCoordinates y).snd) h
  simp only [lensCoordinates_lensPairRotation, WithLp.toLp_snd] at h1
  exact circle_eq_one_of_mul_eq_self hx h1

def lensSpaceFormAction (p : ℕ) [NeZero p] (q : ℤ) :
    Multiplicative (ZMod p) →*
      (EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) where
  toFun k := lensPairRotation (ZMod.toCircle (Multiplicative.toAdd k))
    (ZMod.toCircle ((q : ZMod p) * Multiplicative.toAdd k))
  map_one' := by
    rw [toAdd_one, mul_zero, AddChar.map_zero_eq_one, lensPairRotation_one]
  map_mul' k k' := by
    rw [toAdd_mul, mul_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      lensPairRotation_mul]

theorem lensSpaceFormAction_apply (p : ℕ) [NeZero p] (q : ℤ) (k : Multiplicative (ZMod p)) :
    lensSpaceFormAction p q k = lensPairRotation (ZMod.toCircle (Multiplicative.toAdd k))
      (ZMod.toCircle ((q : ZMod p) * Multiplicative.toAdd k)) := rfl

theorem lensCoordinates_lensSpaceFormAction (p : ℕ) [NeZero p] (q k : ℤ)
    (x : EuclideanSpace ℝ (Fin 4)) :
    lensCoordinates (lensSpaceFormAction p q (Multiplicative.ofAdd (k : ZMod p)) x) =
      WithLp.toLp 2
        (Complex.exp (2 * Real.pi * Complex.I * k / p) * (lensCoordinates x).fst,
          Complex.exp (2 * Real.pi * Complex.I * (q * k : ℤ) / p) * (lensCoordinates x).snd) := by
  rw [lensSpaceFormAction_apply, lensCoordinates_lensPairRotation, toAdd_ofAdd,
    ZMod.toCircle_intCast, ← Int.cast_mul, ZMod.toCircle_intCast]

theorem lensSpaceFormAction_injective (p : ℕ) [NeZero p] (q : ℤ) :
    Function.Injective (lensSpaceFormAction p q) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  set x := lensCoordinates.symm (WithLp.toLp 2 ((1 : ℂ), (0 : ℂ))) with hx
  have hfst : (lensCoordinates x).fst ≠ 0 := by simp [hx]
  have hfix : lensSpaceFormAction p q k x = x := by rw [hk, LinearIsometryEquiv.coe_one, id]
  have h1 := lensPairRotation_left_eq_one hfst hfix
  rw [← AddChar.map_zero_eq_one (ZMod.toCircle (N := p))] at h1
  exact Multiplicative.toAdd.injective (ZMod.injective_toCircle h1)

private theorem isUnit_intCast_of_isCoprime {p : ℕ} {q : ℤ} (hpq : IsCoprime (p : ℤ) q) :
    IsUnit (q : ZMod p) := by
  obtain ⟨a, b, hab⟩ := hpq
  have h := congrArg (Int.cast : ℤ → ZMod p) hab
  rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    mul_zero, zero_add, Int.cast_one] at h
  exact IsUnit.of_mul_eq_one_right _ h

theorem lensSpaceFormAction_eq_one_of_apply_eq_self {p : ℕ} [NeZero p] {q : ℤ}
    (hpq : IsCoprime (p : ℤ) q) {k : Multiplicative (ZMod p)} {x : EuclideanSpace ℝ (Fin 4)}
    (hx : x ≠ 0) (h : lensSpaceFormAction p q k x = x) : k = 1 := by
  rw [lensSpaceFormAction_apply] at h
  have hx' : lensCoordinates x ≠ 0 := fun h0 =>
    hx (lensCoordinates.injective (by rw [h0, map_zero]))
  apply Multiplicative.toAdd.injective
  rw [toAdd_one]
  by_cases h1 : (lensCoordinates x).fst = 0
  · have h2 : (lensCoordinates x).snd ≠ 0 := fun h2 => hx' (by
      rw [WithLp.ext_iff, WithLp.ofLp_zero, Prod.ext_iff]
      exact ⟨by simpa using h1, by simpa using h2⟩)
    have h3 := lensPairRotation_right_eq_one h2 h
    rw [← AddChar.map_zero_eq_one (ZMod.toCircle (N := p))] at h3
    exact (isUnit_intCast_of_isCoprime hpq).mul_right_eq_zero.mp (ZMod.injective_toCircle h3)
  · have h3 := lensPairRotation_left_eq_one h1 h
    rw [← AddChar.map_zero_eq_one (ZMod.toCircle (N := p))] at h3
    exact ZMod.injective_toCircle h3

theorem lensSpaceFormAction_one (p : ℕ) [NeZero p] :
    lensSpaceFormAction p 1 = lensSpaceAction p := by
  refine MonoidHom.ext fun k => ?_
  rw [lensSpaceFormAction_apply, Int.cast_one, one_mul]
  rfl

private theorem lensSpaceFormAction_range_free {p : ℕ} [NeZero p] {q : ℤ}
    (hpq : IsCoprime (p : ℤ) q) (γ : (lensSpaceFormAction p q).range)
    (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
    (hx : Geometry.sphereDiffeo (n := 3) γ.val x = x) : γ = 1 := by
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp γ.2
  have hxval : γ.val (x : EuclideanSpace ℝ (Fin 4)) = (x : EuclideanSpace ℝ (Fin 4)) := by
    have h := congrArg Subtype.val hx
    simpa only [Geometry.sphereDiffeo_coe] using h
  have hx0 : (x : EuclideanSpace ℝ (Fin 4)) ≠ 0 := by
    intro h
    have h1 := mem_sphere_zero_iff_norm.mp x.2
    rw [h, norm_zero] at h1
    norm_num at h1
  rw [← hk] at hxval
  have hval : γ.val = 1 := by
    rw [← hk, lensSpaceFormAction_eq_one_of_apply_eq_self hpq hx0 hxval, map_one]
  exact Subtype.ext (by simpa using hval)

def lensSpaceFormGroup (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q) :
    SphericalSpaceFormGroup where
  group := (lensSpaceFormAction p q).range
  finite := Finite.of_surjective
    (fun k : Multiplicative (ZMod p) =>
      (⟨lensSpaceFormAction p q k, MonoidHom.mem_range.mpr ⟨k, rfl⟩⟩ :
        (lensSpaceFormAction p q).range))
    (fun γ => by
      obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp γ.2
      exact ⟨k, Subtype.ext hk⟩)
  positive := by
    intro γ
    by_cases h : γ = 1
    · have hv : γ.val = 1 := congrArg Subtype.val h
      rw [hv]
      exact Geometry.sphereDiffeo_preservesOrientation_of_det_eq_one _ (by
        change LinearMap.det (1 : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin 4)) = 1
        exact LinearMap.det_id)
    · exact Geometry.sphereDiffeo_preservesOrientation_of_fixed_point_free _
        (fun x hx => h (lensSpaceFormAction_range_free hpq γ x hx))
  free := fun γ x hx => lensSpaceFormAction_range_free hpq γ x hx

theorem lensSpaceFormGroup_group (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q) :
    (lensSpaceFormGroup p q hpq).group = (lensSpaceFormAction p q).range := rfl

def lensSpaceFormGroupEquiv (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q) :
    Multiplicative (ZMod p) ≃* (lensSpaceFormGroup p q hpq).group :=
  MonoidHom.ofInjective (lensSpaceFormAction_injective p q)

theorem lensSpaceFormGroupEquiv_apply (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q)
    (k : Multiplicative (ZMod p)) :
    ((lensSpaceFormGroupEquiv p q hpq k : (lensSpaceFormGroup p q hpq).group) :
      EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) = lensSpaceFormAction p q k :=
  rfl

theorem lensSpaceFormGroup_card (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q) :
    Nat.card (lensSpaceFormGroup p q hpq).group = p := by
  rw [← Nat.card_congr (lensSpaceFormGroupEquiv p q hpq).toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card]

instance instIsCyclicLensSpaceFormGroup (p : ℕ) [NeZero p] (q : ℤ)
    (hpq : IsCoprime (p : ℤ) q) : IsCyclic (lensSpaceFormGroup p q hpq).group :=
  isCyclic_of_surjective (lensSpaceFormGroupEquiv p q hpq) (MulEquiv.surjective _)

theorem lensSpaceFormGroup_group_eq_zpowers (p : ℕ) [NeZero p] (q : ℤ)
    (hpq : IsCoprime (p : ℤ) q) :
    (lensSpaceFormGroup p q hpq).group =
      Subgroup.zpowers (lensSpaceFormAction p q (Multiplicative.ofAdd 1)) := by
  rw [lensSpaceFormGroup_group, MonoidHom.range_eq_map, ← MonoidHom.map_zpowers]
  congr 1
  symm
  refine (Subgroup.eq_top_iff' _).mpr fun k => ?_
  refine Subgroup.mem_zpowers_iff.mpr ⟨(Multiplicative.toAdd k).val, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul, mul_one, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem lensSpaceFormGroup_one (p : ℕ) [NeZero p] :
    lensSpaceFormGroup p 1 isCoprime_one_right = lensSpaceGroup p := by
  have h : (lensSpaceFormGroup p 1 isCoprime_one_right).group = (lensSpaceGroup p).group := by
    rw [lensSpaceFormGroup_group, lensSpaceFormAction_one]
    rfl
  generalize lensSpaceFormGroup p 1 isCoprime_one_right = G at h
  generalize lensSpaceGroup p = H at h
  cases G
  cases H
  cases h
  rfl

theorem lensSpaceFormGroup_fundamentalGroup_card (p : ℕ) [NeZero p] (q : ℤ)
    (hpq : IsCoprime (p : ℤ) q) (x : (lensSpaceFormGroup p q hpq).manifold.Carrier) :
    Nat.card (FundamentalGroup (lensSpaceFormGroup p q hpq).manifold.Carrier x) = p := by
  rw [Nat.card_congr ((lensSpaceFormGroup p q hpq).fundamentalGroupManifoldEquiv x).toEquiv,
    lensSpaceFormGroup_card p q hpq]

theorem isStandardFactor_lensSpaceFormGroup (p : ℕ) [NeZero p] (q : ℤ)
    (hpq : IsCoprime (p : ℤ) q) : isStandardFactor (lensSpaceFormGroup p q hpq).manifold :=
  isStandardFactor_spherical _

theorem isPrime_lensSpaceFormGroup (p : ℕ) [NeZero p] (q : ℤ) (hpq : IsCoprime (p : ℤ) q) :
    GC.Endpoint.IsPrime (lensSpaceFormGroup p q hpq).manifold :=
  GC.Endpoint.isPrime_of_isStandardFactor _ (isStandardFactor_lensSpaceFormGroup p q hpq)

end GC.Seifert
