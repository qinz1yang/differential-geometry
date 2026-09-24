import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveComponentModels
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Descent
import Mathlib.Topology.Homeomorph.Quotient

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {Z : Type*} [TopologicalSpace Z] [ChartedSpace ThreeSpace Z]
  [IsManifold I3 ∞ Z]

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

theorem ProjectivePresentation.isLocalDiffeomorph (pr : ProjectivePresentation Z) :
    IsLocalDiffeomorph (𝓡 3) I3 ∞ pr.quotient := by
  intro x
  apply DifferentialGeometry.Topology.isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible_mfderiv
    isOpen_univ (mem_univ x) pr.smooth.contMDiffOn
  exact ⟨(LinearEquiv.ofBijective (mfderiv (𝓡 3) I3 pr.quotient x).toLinearMap
    (pr.local_diffeo x)).toContinuousLinearEquiv, rfl⟩

theorem ProjectivePresentation.exists_realProjectiveThree_diffeomorph
    (pr : ProjectivePresentation Z) :
    ∃ e : RealProjectiveThreeSpace ≃ₘ⟮I3, I3⟯ Z,
      ∀ a : Sphere 3, e (realProjectiveSpaceQuotientMap a) = pr.quotient a := by
  let f : C(Sphere 3, Z) := ⟨pr.quotient, pr.smooth.continuous⟩
  let q : C(Sphere 3, RealProjectiveThreeSpace) :=
    ⟨realProjectiveSpaceQuotientMap,
      (realProjectiveSpaceQuotientMap_isLocalDiffeomorph (n := 3)).contMDiff.continuous⟩
  have hq : IsQuotientMap q := (realProjectiveSpaceQuotientMap_isLocalDiffeomorph (n := 3)).isOpenMap.isQuotientMap
    q.continuous realProjectiveSpaceQuotientMap_surjective
  have hf : IsQuotientMap f := pr.isLocalDiffeomorph.isOpenMap.isQuotientMap f.continuous pr.onto
  have hker (x y : Sphere 3) : Setoid.ker q x y ↔ Setoid.ker f x y :=
    (realProjectiveSpaceQuotientMap_eq_iff (x := x) (y := y)).trans (pr.fibers x y).symm
  let e : Quotient (Setoid.ker q) ≃ₜ Quotient (Setoid.ker f) :=
    Homeomorph.Quotient.congrRight hker
  let d := (hq.homeomorph.symm.trans e).trans hf.homeomorph
  have hd (a : Sphere 3) : d (realProjectiveSpaceQuotientMap a) = pr.quotient a := by
    have ha : hq.homeomorph (Quotient.mk (Setoid.ker q) a) = q a := rfl
    change hf.homeomorph (e (hq.homeomorph.symm (q a))) = f a
    rw [← ha, hq.homeomorph.symm_apply_apply]
    rfl
  obtain ⟨D, hD⟩ := KappaSolutions.exists_diffeomorph_of_homeomorph_comp_localDiffeomorph
    q (realProjectiveSpaceQuotientMap_isLocalDiffeomorph (n := 3)) realProjectiveSpaceQuotientMap_surjective
    f pr.isLocalDiffeomorph d hd
  exact ⟨D, fun a => (congrFun hD (realProjectiveSpaceQuotientMap a)).trans (hd a)⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
