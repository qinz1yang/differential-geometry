import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortMeridianLattice
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortMeridianCover
import DifferentialGeometry.Topology.FundamentalGroup.BasepointChange
import DifferentialGeometry.Topology.FundamentalGroup.TorusSlope

/-!
# CP1-A3 (G1): closed geodesic of a prescribed primitive class on a flat torus
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology Set Function GC.Endpoint
open scoped Manifold ContDiff ContinuousMap
namespace GC.LongTime.CuspP1

/-- An automorphism of `ℤ²` sending `w` to `(1, 0)` forces `w` to be primitive. -/
theorem isCoprime_of_map_eq_CPA3
    (ρ : Multiplicative ℤ × Multiplicative ℤ ≃* Multiplicative ℤ × Multiplicative ℤ)
    (w : Multiplicative ℤ × Multiplicative ℤ) (hw : ρ w = (Multiplicative.ofAdd 1, 1)) :
    IsCoprime w.1.toAdd w.2.toAdd := by
  let f : Multiplicative ℤ × Multiplicative ℤ →* Multiplicative ℤ :=
    (MonoidHom.fst _ _).comp ρ.toMonoidHom
  have hw' : w = ((Multiplicative.ofAdd 1, 1) : Multiplicative ℤ × Multiplicative ℤ) ^ w.1.toAdd *
      ((1, Multiplicative.ofAdd 1) : Multiplicative ℤ × Multiplicative ℤ) ^ w.2.toAdd := by
    refine Prod.ext ?_ ?_
    · simp [← ofAdd_zsmul]
    · simp [← ofAdd_zsmul]
  have hf : f w = Multiplicative.ofAdd 1 := by
    change (ρ w).1 = _
    rw [hw]
  rw [hw', map_mul, map_zpow, map_zpow] at hf
  refine ⟨(f (Multiplicative.ofAdd 1, 1)).toAdd, (f (1, Multiplicative.ofAdd 1)).toAdd, ?_⟩
  have := congrArg Multiplicative.toAdd hf
  simp only [toAdd_mul, toAdd_zpow, toAdd_ofAdd, smul_eq_mul] at this
  linarith

/-- `z ↦ (z^a, z^b)` is injective for coprime `a, b`. -/
theorem slope_injective_CPA3 {a b : ℤ} (hab : IsCoprime a b) :
    Function.Injective (Circle.slopeContinuousMap ![a, b]) := by
  obtain ⟨r, s, hrs⟩ := hab
  intro z u h
  have h1 : z ^ a = u ^ a := congrArg Prod.fst h
  have h2 : z ^ b = u ^ b := congrArg Prod.snd h
  have key : ∀ x : Circle, x = (x ^ a) ^ r * (x ^ b) ^ s := by
    intro x
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm a r, mul_comm b s, hrs, zpow_one]
  rw [key z, key u, h1, h2]

end GC.LongTime.CuspP1
