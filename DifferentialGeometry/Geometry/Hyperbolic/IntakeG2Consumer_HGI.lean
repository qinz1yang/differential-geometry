import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Lattices.Margulis
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Lattices.ThickPartCompactness
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.Margulis

/-!
# Consumer of the G2 intake (S-HG-INTAKE, suffix `_HGI`)

Algebraic Margulis lemma in dimension three (`PO 3 1`), and thick-part compactness of a
lattice quotient, instantiated at `n = 3`.
-/

set_option autoImplicit false

open DifferentialGeometry DifferentialGeometry.Hyperbolic
open DifferentialGeometry.ProjectiveOrthogonalGroup

theorem margulis_constant_three_HGI :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Γ : Subgroup (PO 3 1), IsDiscrete (SetLike.coe Γ) →
      ∀ x : HUpper 3, Group.IsVirtuallyNilpotent (Margulis.smallSubgroup (by norm_num) Γ ε x) :=
  Margulis.exists_margulis_constant (by norm_num)

example :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      ∀ (Γ : Subgroup (Hyperboloid (EuclideanSpace ℝ (Fin 3)) ≃ᵢ
          Hyperboloid (EuclideanSpace ℝ (Fin 3)))) [DiscreteTopology Γ]
        (x : Hyperboloid (EuclideanSpace ℝ (Fin 3))),
        let L := Subgroup.closure
          {g : Γ | dist ((g : Hyperboloid (EuclideanSpace ℝ (Fin 3)) ≃ᵢ
            Hyperboloid (EuclideanSpace ℝ (Fin 3))) x) x < ε}
        ∃ H : Subgroup L, Group.IsNilpotent H ∧ ENat.card (L ⧸ H) ≤ (N : ℕ∞) :=
  Hyperboloid.margulis_lemma
