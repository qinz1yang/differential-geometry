import DifferentialGeometry.Topology.Manifold.SmoothModelTransport
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Manifold

variable {𝕜 E F H H' M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace H']
  [TopologicalSpace M] [ChartedSpace H M]

def diffeomorphTransHomeomorph
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
    (e : H ≃ₜ H') (L : E ≃L[𝕜] F) (hc : ∀ y, J (e y) = L (I y)) (n : ℕ∞ω) :
    letI := chartedSpaceTransHomeomorph (M := M) e
    Diffeomorph I J M M n := by
  letI := chartedSpaceTransHomeomorph (M := M) e
  exact {
    toEquiv := Equiv.refl M
    contMDiff_toFun := (contMDiff_chartedSpaceTransHomeomorph_iff I J e L hc I).mpr
      contMDiff_id
    contMDiff_invFun := (contMDiff_chartedSpaceTransHomeomorph_iff I J e L hc J).mp
      contMDiff_id }

theorem diffeomorphTransHomeomorph_apply
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
    (e : H ≃ₜ H') (L : E ≃L[𝕜] F) (hc : ∀ y, J (e y) = L (I y)) (n : ℕ∞ω)
    (x : M) :
    letI := chartedSpaceTransHomeomorph (M := M) e
    diffeomorphTransHomeomorph I J e L hc n x = x := rfl

theorem diffeomorphTransHomeomorph_symm_apply
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
    (e : H ≃ₜ H') (L : E ≃L[𝕜] F) (hc : ∀ y, J (e y) = L (I y)) (n : ℕ∞ω)
    (x : M) :
    letI := chartedSpaceTransHomeomorph (M := M) e
    (diffeomorphTransHomeomorph I J e L hc n).symm x = x := rfl

theorem diffeomorphTransHomeomorph_mfderiv
    (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 F H')
    (e : H ≃ₜ H') (L : E ≃L[𝕜] F) (hc : ∀ y, J (e y) = L (I y)) (n : ℕ∞ω)
    (x : M) :
    letI := chartedSpaceTransHomeomorph (M := M) e
    mfderiv I J (diffeomorphTransHomeomorph I J e L hc n) x = L.toContinuousLinearMap := by
  let := chartedSpaceTransHomeomorph (M := M) e
  change mfderiv I J (id : M → M) x = _
  rw [mfderiv_chartedSpaceTransHomeomorph I J e L hc I, mfderiv_id]
  ext v
  rfl

end DifferentialGeometry.Manifold
