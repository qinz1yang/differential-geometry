import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open Surgery.Topology (ThreeSpace)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps : ℝ} {x : M} {t a b : ℝ}

def OrderedNeckChain.singleInterval (nk : StrongNeck S eps x t)
    (hab : a < b) (ha : -eps⁻¹ < a) (hb : b < eps⁻¹) :
    OrderedNeckChain S eps t (nk.map '' (univ ×ˢ Icc a b)) where
  count := 1
  count_pos := by norm_num
  centers := fun _ => x
  necks := fun _ => nk
  lo := fun _ => a
  hi := fun _ => b
  lo_lt_hi := fun _ => hab
  inside := fun _ y hy => nk.domain ⟨hy.1, ha.trans_le hy.2.1, hy.2.2.trans_lt hb⟩
  swept_eq := (iUnion_const _).symm
  transition_increasing := by intro i j hij; simp at hij

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
