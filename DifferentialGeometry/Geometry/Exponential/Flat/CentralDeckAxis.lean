import DifferentialGeometry.Geometry.Exponential.Flat.EuclideanAxis
import Mathlib.GroupTheory.Subgroup.Center

/-!
The unique displacement vector of a central nonidentity free affine deck motion is nonzero
and fixed by the whole actual linear group. Conjugation constructs the transformed axis and
uniqueness identifies its vector, without a supplied invariant direction or holonomy type.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V]

theorem exists_centralDeck_fixedVector (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : V, γ.val x ≠ x)
    (g : G) (hg : g ≠ 1) (hc : g ∈ Subgroup.center G) :
    ∃ q : V, q ≠ 0 ∧ ∀ γ : G, γ.val.linearIsometryEquiv q = q := by
  obtain ⟨p, q, hp, hq⟩ := exists_affineAxis_point g.val
  refine ⟨q, ?_, ?_⟩
  · intro hz
    exact hfree g hg p (by simpa only [hz, add_zero] using hp)
  · intro γ
    have he : γ.val * g.val * γ.val⁻¹ = g.val := by
      have hcomm := congrArg Subtype.val (Subgroup.mem_center_iff.mp hc γ)
      calc
        γ.val * g.val * γ.val⁻¹ = g.val * γ.val * γ.val⁻¹ :=
          congrArg (fun a => a * γ.val⁻¹) hcomm
        _ = g.val := by rw [mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨hp', hq'⟩ := affine_axis_conjugate g.val γ.val hp hq
    rw [he] at hp' hq'
    exact (affine_axis_vector_unique g.val hp hq hp' hq').symm

end DifferentialGeometry.Geometry.FlatSurface
