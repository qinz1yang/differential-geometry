import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckRestriction

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {U : TopologicalSpace.Opens M} {D : RealTimeInterval}
  {S : SolutionOn (I := I3) (M := M) D} {S' : SolutionOn (I := I3) (M := U) D}
  {eps t : ℝ} {x : U}

def StrongNeck.restrictOpen (nk : StrongNeck S eps (x : M) t)
    (hS : ∀ τ, S'.base.metric τ = (S.base.metric τ).restrictOpen U)
    (hmap : nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ U) :
    StrongNeck S' eps x t := by
  let i := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) U ⟨x⟩
  have hitarget : i.target = (U : Set M) := U.openPartialHomeomorphSubtypeCoe_target ⟨x⟩
  let F := nk.map.trans i.symm
  have hdom : univ ×ˢ Ioo (-eps⁻¹) eps⁻¹ ⊆ F.source := by
    intro y hy
    change y ∈ (nk.map.trans i.symm).source
    rw [PartialDiffeomorph.trans_source]
    refine ⟨nk.domain hy, ?_⟩
    change nk.map y ∈ i.target
    rw [hitarget]
    exact hmap ⟨y, hy, rfl⟩
  have hval (y : Cylinder) (hy : y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) :
      (F y : M) = nk.map y := by
    change (((nk.map.trans i.symm) y) : M) = nk.map y
    rw [PartialDiffeomorph.trans_apply]
    apply i.right_inv'
    rw [hitarget]
    exact hmap ⟨y, hy, rfl⟩
  have hdf (y : Cylinder) (hy : y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) :
      mfderiv IC I3 F y = mfderiv IC I3 nk.map y := by
    have hlocal : (fun z => (F z : M)) =ᶠ[𝓝 y] nk.map :=
      Filter.eventuallyEq_of_mem ((isOpen_univ.prod isOpen_Ioo).mem_nhds hy) hval
    have hFd := (F.contMDiffOn_toFun.contMDiffAt
      (F.open_source.mem_nhds (hdom hy))).mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
    have hcomp := mfderiv_comp y (hasMFDerivAt_subtype_val (I := I3) U (F y)).mdifferentiableAt hFd
    rw [mfderiv_subtype_val] at hcomp
    have heq : mfderiv IC I3 (fun z => (F z : M)) y = mfderiv IC I3 nk.map y :=
      hlocal.mfderiv_eq
    ext v
    have hc : mfderiv IC I3 (fun z => (F z : M)) y v = mfderiv IC I3 F y v :=
      DFunLike.congr_fun hcomp v
    exact hc.symm.trans (DFunLike.congr_fun heq v)
  have hR : S'.scalar t x = S.scalar t (x : M) := by
    change metricScalarAt (S'.base.metric t) x = metricScalarAt (S.base.metric t) (x : M)
    rw [hS t]
    exact metricScalarAt_restrictOpen _ U x
  have hQ : 0 < S'.scalar t x := hR.symm ▸ nk.Q_pos
  refine
    { eps_pos := nk.eps_pos
      eps_small := nk.eps_small
      Q_pos := hQ
      cylinder := nk.cylinder
      map := F
      center := nk.center
      center_eq := ?_
      domain := hdom
      time_domain := by rw [hR]; exact nk.time_domain
      comparison := ?_ }
  · apply Subtype.ext
    exact (hval (nk.center, 0) ⟨mem_univ _, neg_lt_zero.mpr (inv_pos.mpr nk.eps_pos),
      inv_pos.mpr nk.eps_pos⟩).trans nk.center_eq
  · refine
      { pullback := nk.comparison.pullback
        pullback_eq := ?_
        jet := nk.comparison.jet
        jet_zero := nk.comparison.jet_zero
        jet_succ := nk.comparison.jet_succ
        equivalence := nk.comparison.equivalence
        close := nk.comparison.close }
    intro τ y hy v
    rw [nk.comparison.pullback_eq τ y hy v]
    simp only [rescaledMetric, scaleMetric_inner, hS, SmoothRiemannianMetric.restrictOpen_inner,
      hR, hdf y hy]
    exact congrArg (fun w => S.scalar t (x : M) * ((S.base.metric (parabolicTime t
      (S.scalar t (x : M)) τ)).inner w) _ _) (hval y hy).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
