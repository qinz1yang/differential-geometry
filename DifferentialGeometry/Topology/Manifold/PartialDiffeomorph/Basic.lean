import Mathlib.Geometry.Manifold.LocalDiffeomorph

open scoped ContDiff

namespace DifferentialGeometry.PartialDiffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
variable {m n : WithTop ℕ∞}

def ofLE (Φ : PartialDiffeomorph I J M N n) (h : m ≤ n) :
    PartialDiffeomorph I J M N m where
  toPartialEquiv := Φ.toPartialEquiv
  open_source := Φ.open_source
  open_target := Φ.open_target
  contMDiffOn_toFun := Φ.contMDiffOn_toFun.of_le h
  contMDiffOn_invFun := Φ.contMDiffOn_invFun.of_le h

@[simp]
theorem ofLE_toPartialEquiv (Φ : PartialDiffeomorph I J M N n) (h : m ≤ n) :
    (ofLE Φ h).toPartialEquiv = Φ.toPartialEquiv := rfl

end DifferentialGeometry.PartialDiffeomorph
