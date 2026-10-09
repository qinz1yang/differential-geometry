import DifferentialGeometry.Topology.ThreeManifold.TorusCut.TorusCylinder
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.TorusGluing
import DifferentialGeometry.Topology.FundamentalGroup.BasepointChange
import DifferentialGeometry.Topology.LoopSpace.CircleDegree

/-!
# Primitive curve on the torus: algebraic reduction (lane CP1-P)

`hprim` of `exists_primitive_meridian_top_CPQ` is reduced to the single planar-topology statement
"an embedded essential loop on `Torus` has coprime coordinates in `H₁ = ℤ²`" (`hcop` below).
This file proves the pure algebra: coprime vector => automorphism of `ℤ²` sending it to `(1,1)`,
and the transport through the base-point change `π₁(Torus,(1,1)) ≅ π₁(Torus, γ 0)`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Topology
namespace GC.LongTime.CuspP1

/-- Bezout automorphism of `ℤ × ℤ` sending a coprime `(p,q)` to `(1,1)`. -/
def coprimeNormalizer_CPP (p q a b : ℤ) (hab : a * p + b * q = 1) :
    Multiplicative ℤ × Multiplicative ℤ ≃* Multiplicative ℤ × Multiplicative ℤ :=
  { toFun := fun z =>
      (Multiplicative.ofAdd (a * z.1.toAdd + b * z.2.toAdd),
       Multiplicative.ofAdd (- q * z.1.toAdd + p * z.2.toAdd))
    invFun := fun w =>
      (Multiplicative.ofAdd (p * w.1.toAdd - b * w.2.toAdd),
       Multiplicative.ofAdd (q * w.1.toAdd + a * w.2.toAdd))
    left_inv := by
      rintro ⟨x, y⟩
      obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective x
      obtain ⟨y, rfl⟩ := Multiplicative.ofAdd.surjective y
      simp only [toAdd_ofAdd, Prod.mk.injEq]
      constructor
      · apply congrArg Multiplicative.ofAdd
        linear_combination x * hab
      · apply congrArg Multiplicative.ofAdd
        linear_combination y * hab
    right_inv := by
      rintro ⟨u, w⟩
      obtain ⟨u, rfl⟩ := Multiplicative.ofAdd.surjective u
      obtain ⟨w, rfl⟩ := Multiplicative.ofAdd.surjective w
      simp only [toAdd_ofAdd, Prod.mk.injEq]
      constructor
      · apply congrArg Multiplicative.ofAdd
        linear_combination u * hab
      · apply congrArg Multiplicative.ofAdd
        linear_combination w * hab
    map_mul' := by
      rintro ⟨x, y⟩ ⟨x', y'⟩
      simp only [Prod.mk_mul_mk, toAdd_mul, toAdd_ofAdd, Prod.mk.injEq]
      constructor <;> (apply congrArg Multiplicative.ofAdd; simp only [toAdd_ofAdd]; ring) }

theorem coprimeNormalizer_CPP_apply (p q a b : ℤ) (hab : a * p + b * q = 1) :
    coprimeNormalizer_CPP p q a b hab (Multiplicative.ofAdd p, Multiplicative.ofAdd q) =
      (Multiplicative.ofAdd 1, 1) := by
  simp only [coprimeNormalizer_CPP, MulEquiv.coe_mk, Equiv.coe_fn_mk, toAdd_ofAdd, Prod.mk.injEq]
  constructor
  · apply congrArg Multiplicative.ofAdd; linear_combination hab
  · change Multiplicative.ofAdd _ = Multiplicative.ofAdd (0 : ℤ)
    apply congrArg Multiplicative.ofAdd
    ring

/-- REDUCTION.  `hprim` follows from the planar-topology input `hcop`: for an embedded essential
loop, the `ℤ²`-class (read through any path from `(1,1)`) has coprime coordinates. -/
theorem primitive_of_coprime_CPP
    (hcop : ∀ γ : freeLoop GC.Endpoint.Torus, Topology.IsEmbedding γ → ¬ γ.Nullhomotopic →
      ∀ β : Path ((1 : Circle), (1 : Circle)) (γ 0),
        IsCoprime
          (torusFundamentalGroup
            (fundamentalGroupChangeBasepoint β (loopDegreeClass γ 1))).1.toAdd
          (torusFundamentalGroup
            (fundamentalGroupChangeBasepoint β (loopDegreeClass γ 1))).2.toAdd) :
    ∀ γ : freeLoop GC.Endpoint.Torus, Topology.IsEmbedding γ → ¬ γ.Nullhomotopic →
      ∃ e : FundamentalGroup GC.Endpoint.Torus (γ 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
        e (loopDegreeClass γ 1) = (Multiplicative.ofAdd 1, 1) := by
  intro γ hγ hn
  obtain ⟨β⟩ : Nonempty (Path ((1 : Circle), (1 : Circle)) (γ 0)) :=
    ⟨PathConnectedSpace.somePath _ _⟩
  have hc := hcop γ hγ hn β
  obtain ⟨a, b, hab⟩ := hc
  have hc := hcop γ hγ hn β
  set v := torusFundamentalGroup
    (fundamentalGroupChangeBasepoint β (loopDegreeClass γ 1)) with hv
  refine ⟨((fundamentalGroupChangeBasepoint β).trans
    torusFundamentalGroup).trans (coprimeNormalizer_CPP _ _ a b hab), ?_⟩
  change coprimeNormalizer_CPP _ _ a b hab (torusFundamentalGroup
    (fundamentalGroupChangeBasepoint β (loopDegreeClass γ 1))) = _
  have : v = (Multiplicative.ofAdd v.1.toAdd, Multiplicative.ofAdd v.2.toAdd) := rfl
  exact (congrArg (coprimeNormalizer_CPP _ _ a b hab) this).trans
    (coprimeNormalizer_CPP_apply _ _ a b hab)

end GC.LongTime.CuspP1
