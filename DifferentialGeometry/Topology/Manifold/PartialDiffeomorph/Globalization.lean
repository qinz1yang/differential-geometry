import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

noncomputable section

open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section PartialDiffeomorph

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [TopologicalSpace N] [ChartedSpace H N]
variable {n : WithTop ℕ∞}

theorem partialDiffeomorph_target_eq_univ_of_compact_source
    [T2Space N] [PreconnectedSpace N]
    (e : PartialDiffeomorph I I M N n)
    (hcompact : IsCompact e.source) (hne : e.source.Nonempty) :
    e.target = Set.univ := by
  have himage : (e : M → N) '' e.source = e.target :=
    e.toPartialEquiv.image_source_eq_target
  have htargetCompact : IsCompact e.target := by
    rw [← himage]
    exact hcompact.image_of_continuousOn e.contMDiffOn_toFun.continuousOn
  have htargetNonempty : e.target.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨e x, e.map_source' hx⟩
  exact IsClopen.eq_univ ⟨htargetCompact.isClosed, e.open_target⟩ htargetNonempty

def globalDiffeomorphOfUniv (e : PartialDiffeomorph I I M N n)
    (hsource : e.source = Set.univ) (htarget : e.target = Set.univ) :
    Diffeomorph I I M N n where
  toFun := e
  invFun := e.symm
  left_inv x := e.left_inv' (by rw [hsource]; exact Set.mem_univ x)
  right_inv y := e.right_inv' (by rw [htarget]; exact Set.mem_univ y)
  contMDiff_toFun := by
    change ContMDiff I I n (e : M → N)
    apply contMDiffOn_univ.mp
    simpa only [hsource] using e.contMDiffOn_toFun
  contMDiff_invFun := by
    change ContMDiff I I n (e.symm : N → M)
    apply contMDiffOn_univ.mp
    have hinverse : ContMDiffOn I I n (e.symm : N → M) e.target :=
      e.symm.contMDiffOn_toFun
    simpa only [htarget] using hinverse

end PartialDiffeomorph


end

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
