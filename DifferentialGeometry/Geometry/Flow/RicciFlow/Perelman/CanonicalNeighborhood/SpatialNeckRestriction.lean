import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] {g : SmoothRiemannianMetric I3 M}
  {U : TopologicalSpace.Opens M} {x : U} {eps : ℝ}

def SpatialNeck.restrictOpen (nk : SpatialNeck g eps (x : M))
    (hmap : nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ U) :
    SpatialNeck (g.restrictOpen U) eps x := by
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
  have hR : metricScalarAt (g.restrictOpen U) x = metricScalarAt g (x : M) :=
    metricScalarAt_restrictOpen g U x
  have hQ : 0 < metricScalarAt (g.restrictOpen U) x := hR.symm ▸ nk.Q_pos
  refine
    { eps_pos := nk.eps_pos
      eps_small := nk.eps_small
      Q_pos := hQ
      cylinder := nk.cylinder
      map := F
      center := nk.center
      center_eq := ?_
      domain := hdom
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
    intro t y hy v
    rw [nk.comparison.pullback_eq t y hy v, scaleMetric_inner, scaleMetric_inner,
      SmoothRiemannianMetric.restrictOpen_inner, hR, hdf y hy, hval y hy]
    rfl

@[simp]
theorem SpatialNeck.restrictOpen_map_source (nk : SpatialNeck g eps (x : M))
    (hmap : nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ U) :
    (nk.restrictOpen hmap).map.source = nk.map.source ∩ nk.map ⁻¹' (U : Set M) := by
  change (nk.map.trans
    (DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) U ⟨x⟩).symm).source = _
  rw [PartialDiffeomorph.trans_source]
  change nk.map.source ∩ nk.map ⁻¹' (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).target = _
  rw [U.openPartialHomeomorphSubtypeCoe_target]

@[simp]
theorem SpatialNeck.restrictOpen_map_coe (nk : SpatialNeck g eps (x : M))
    (hmap : nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ U)
    {y : Cylinder} (hy : nk.map y ∈ U) :
    ((nk.restrictOpen hmap).map y : M) = nk.map y := by
  let i := DifferentialGeometry.Topology.PartialDiffeomorph.subtypeVal (I := I3) U ⟨x⟩
  change (((nk.map.trans i.symm) y) : M) = nk.map y
  rw [PartialDiffeomorph.trans_apply]
  apply i.right_inv'
  change nk.map y ∈ (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).target
  rwa [U.openPartialHomeomorphSubtypeCoe_target]

@[simp]
theorem SpatialNeck.restrictOpen_map_symm (nk : SpatialNeck g eps (x : M))
    (hmap : nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) ⊆ U) (y : U) :
    (nk.restrictOpen hmap).map.symm y = nk.map.symm (y : M) := rfl

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
