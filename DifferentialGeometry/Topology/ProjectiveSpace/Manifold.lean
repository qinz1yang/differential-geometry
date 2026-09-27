import DifferentialGeometry.Topology.ProjectiveSpace.Real
import DifferentialGeometry.Topology.Manifold.Quotient
import DifferentialGeometry.Topology.Covering.SimplyConnected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {n : Nat} [Fact (Module.finrank Real E = n + 1)]

instance realProjectiveSpaceAntipodalGroupContMDiffConstSMul :
    ContMDiffConstSMul (𝓡 n) ∞ (realProjectiveSpaceAntipodalGroup E)
      (Metric.sphere (0 : E) 1) where
  contMDiff_const_smul gamma := by
    change ContMDiff (𝓡 n) (𝓡 n) ∞
      (gamma.1 : Metric.sphere (0 : E) 1 → Metric.sphere (0 : E) 1)
    rcases realProjectiveSpaceAntipodalGroup_eq_one_or_generator gamma with h | h
    · rw [h]
      exact contMDiff_id
    · rw [h]
      exact contMDiff_neg_sphere

theorem realProjectiveSpaceQuotientMap_isLocalDiffeomorph :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞
      (realProjectiveSpaceQuotientMap (E := E)) :=
  MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul (𝓡 n)

theorem not_simplyConnectedSpace_realProjectiveSpace (hn : 1 ≤ n) :
    ¬ SimplyConnectedSpace (RealProjectiveSpace E) := by
  intro h
  let _ : SimplyConnectedSpace (RealProjectiveSpace E) := h
  have hdim : 1 < Module.finrank Real E := by
    rw [show Module.finrank Real E = n + 1 from Fact.out]
    omega
  let _ : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (lt_trans Nat.zero_lt_one hdim)
  let _ : LocallyPathConnectedSpace (RealProjectiveSpace E) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace Real (Fin n)) _
  let _ : PreconnectedSpace (Metric.sphere (0 : E) 1) :=
    Subtype.preconnectedSpace
      (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank hdim) 0 1)
  obtain ⟨x, hx⟩ := NormedSpace.sphere_nonempty (E := E).2 zero_le_one
  let y : Metric.sphere (0 : E) 1 := ⟨x, hx⟩
  let _ : Nonempty (Metric.sphere (0 : E) 1) := ⟨y⟩
  have hinj := (realProjectiveSpaceQuotientMap_isCoveringMap (E := E)).bijective_sc.1
  have heq : realProjectiveSpaceQuotientMap
      (realProjectiveSpaceAntipodalHomeomorph E y) =
        realProjectiveSpaceQuotientMap y := by
    apply realProjectiveSpaceQuotientMap_eq_iff.mpr
    exact Or.inr (realProjectiveSpaceAntipodalHomeomorph_coe y)
  exact realProjectiveSpaceAntipodalHomeomorph_fixed_point_free y (hinj heq)

theorem not_simplyConnectedSpace_realProjectivePlane :
    ¬ SimplyConnectedSpace RealProjectivePlane := by
  let _ : Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) :=
    ⟨by simp⟩
  exact not_simplyConnectedSpace_realProjectiveSpace (E := EuclideanSpace Real (Fin 3))
    (n := 2) (by decide)

end DifferentialGeometry
