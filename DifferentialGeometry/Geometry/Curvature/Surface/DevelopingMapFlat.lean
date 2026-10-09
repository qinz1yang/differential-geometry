import DifferentialGeometry.Geometry.Curvature.Surface.DevelopingMap
import DifferentialGeometry.Geometry.Curvature.Surface.DivergenceForm

/-!
# The developing map of a doubly periodic flat coefficient field (FT1)

A doubly periodic `C²` positive symmetric coefficient field on a two-dimensional space with
vanishing chart curvature has a closed connection form (divergence identity
`K √D = ∂₂ P − ∂₁ Q` of `DivergenceForm.lean`), hence a developing map
(`exists_developing_of_closed_connection`): a homeomorphism `φ : E ≃ₜ ℂ`, `C¹`, isometric from `b`
to the Euclidean plane, turning the periods into translations of `ℂ`.

The target plane is `ℂ` (the sheet's `EuclideanSpace ℝ (Fin 2)` is replaced by `ℂ`, which makes
the rotation part of the equivariance a scalar).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {b : E → E →L[ℝ] E →L[ℝ] ℝ} {v₁ v₂ : E}

/-- Flatness closes the connection form: `∂₂ P = ∂₁ Q`. -/
theorem surfaceConnection_closed_of_flat (hE : Module.finrank ℝ E = 2) (hb : ContDiff ℝ 2 b)
    (hsymm : ∀ y u v, b y u v = b y v u) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    (hli : LinearIndependent ℝ ![v₁, v₂]) (hflat : ∀ y, coefficientSectional b y v₁ v₂ = 0)
    (y : E) :
    fderiv ℝ (surfaceConnectionP b v₁ v₂) y v₂ = fderiv ℝ (surfaceConnectionQ b v₁ v₂) y v₁ := by
  have h := coefficientSectional_mul_sqrt_eq_fderiv_sub hE hb hsymm hpos hli y
  rw [hflat y, zero_mul] at h
  linarith

/-- **FT1: developing map of a doubly periodic flat coefficient field** (with the derivative,
its continuity, and a uniform bound for its inverse). -/
theorem exists_developing_of_periodic_flat' (hE : Module.finrank ℝ E = 2)
    (hb : ContDiff ℝ 2 b) (hsymm : ∀ y u v, b y u v = b y v u)
    (hpos : ∀ y v, v ≠ 0 → 0 < b y v v) (hli : LinearIndependent ℝ ![v₁, v₂])
    (hper₁ : ∀ y, b (y + v₁) = b y) (hper₂ : ∀ y, b (y + v₂) = b y)
    (hflat : ∀ y, coefficientSectional b y v₁ v₂ = 0) :
    ∃ (φ : E ≃ₜ ℂ) (φ' : E → E ≃L[ℝ] ℂ) (l₁ l₂ : ℂ) (K : ℝ),
      (∀ y, HasFDerivAt φ (φ' y : E →L[ℝ] ℂ) y) ∧ Continuous (fun y => (φ' y : E →L[ℝ] ℂ)) ∧
      (∀ y u w, inner ℝ (φ' y u) (φ' y w) = b y u w) ∧
      (∀ y, ‖((φ' y).symm : ℂ →L[ℝ] E)‖ ≤ K) ∧
      (∀ y, φ (y + v₁) = φ y + l₁) ∧ ∀ y, φ (y + v₂) = φ y + l₂ :=
  exists_developing_of_closed_connection hE hb hsymm hpos hli hper₁ hper₂
    (surfaceConnection_closed_of_flat hE hb hsymm hpos hli hflat)

/-- **FT1, sheet form** (SF-B's statement with target `ℂ`): a `C¹` homeomorphism `E ≃ₜ ℂ`
pulling the Euclidean inner product back to `b` and turning the periods into translations. -/
theorem exists_developing_of_periodic_flat (hE : Module.finrank ℝ E = 2)
    (hb : ContDiff ℝ 2 b) (hsymm : ∀ y u v, b y u v = b y v u)
    (hpos : ∀ y v, v ≠ 0 → 0 < b y v v) (hli : LinearIndependent ℝ ![v₁, v₂])
    (hper₁ : ∀ y, b (y + v₁) = b y) (hper₂ : ∀ y, b (y + v₂) = b y)
    (hflat : ∀ y, coefficientSectional b y v₁ v₂ = 0) :
    ∃ (φ : E ≃ₜ ℂ) (l₁ l₂ : ℂ),
      ContDiff ℝ 1 φ ∧
      (∀ y u v, inner ℝ (fderiv ℝ φ y u) (fderiv ℝ φ y v) = b y u v) ∧
      (∀ y, φ (y + v₁) = φ y + l₁) ∧ (∀ y, φ (y + v₂) = φ y + l₂) := by
  obtain ⟨φ, φ', l₁, l₂, -, hφ, hc, hin, -, h₁, h₂⟩ :=
    exists_developing_of_periodic_flat' hE hb hsymm hpos hli hper₁ hper₂ hflat
  have hfd : fderiv ℝ φ = fun y => (φ' y : E →L[ℝ] ℂ) := funext fun y => (hφ y).fderiv
  refine ⟨φ, l₁, l₂, contDiff_one_iff_fderiv.mpr ⟨fun y => (hφ y).differentiableAt, ?_⟩,
    fun y u v => ?_, h₁, h₂⟩
  · rw [hfd]
    exact hc
  · rw [hfd]
    exact hin y u v

end DifferentialGeometry.Analysis
