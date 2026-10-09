import DifferentialGeometry.Geometry.Collapse.LocalExport.EdgeDiskPacket
import DifferentialGeometry.Topology.Manifold.DiskModelChartExtension
import DifferentialGeometry.Topology.Manifold.SubmersionFiber
import DifferentialGeometry.Topology.Ehresmann.SideBoundaryInterval
import DifferentialGeometry.Topology.Manifold.RegularLevel.RegularSublevelBoundaryRegular

/-!
# The slice of an edge disk packet: the fibre's chart across the rim and its two-sided collar

Lane POLAR-2 (row-side input of the both-sides polar collar, lane POLAR-1). For an edge disk packet
`P` (LC84, `EdgeDiskPacket`; slab re-charted on `ℝ × ℝ²`, fibre `{η_p = 0, H ≤ 4Δ}` with its
regular-sublevel structure and disk model `P.diskModel`):

* `EdgeDiskPacket.slabRegular`: the open part of the slab where `η_p` is a submersion (it contains
  the fibre by `regular_fibre`); `EdgeDiskPacket.Slice`: the level `{η_p = 0}` inside it, a
  boundaryless surface (`EdgeDiskPacket.sliceChartedSpace`, model `ℝ²`, the regular-level charts
  `submersionFiberChartedSpace`); `EdgeDiskPacket.fibreToSlice`: the inclusion of the fibre, a
  smooth injective immersion;
* `EdgeDiskPacket.exists_sliceChart`: the chart `j` of the slice on a neighbourhood of the closed
  unit disk with `j = P.diskModel` on the disk (the disk model extended across the rim,
  `exists_partialDiffeomorph_extend_diskModel`);
* `EdgeDiskPacket.exists_polarCollar_twoSided`: POLAR-1's both-sides polar collar on it, for the raw
  height `H`: a re-modelled disk model `D` (equal to `P.diskModel` on the rim and on
  `‖z‖ ≤ 1 - η`) and a collar `C` of the slice on the annulus `{|‖z‖ - 1| < δ}` with
  `H (C z) = 4Δ + κ (‖z‖ - 1)` on BOTH sides of the rim, `C = P.diskModel` on the rim circle and
  `D = C` on the inner side (`exists_diskModel_polar_twoSided_of_immersion`; `dH ≠ 0` on the rim
  from `regularSublevel_mfderiv_ne_zero`). The re-modelled packet is `{P with diskModel := D}`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Filter Metric Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open DifferentialGeometry.Manifold DifferentialGeometry.Manifold.RegularLevel
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

section Packet

variable {M : Type*} [mM : MetricSpace M] [ChartedSpace E3 M] [IsManifold 𝓘(ℝ, E3) ∞ M]
  [SigmaCompactSpace M] [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E3 (fun x : M => TangentSpace 𝓘(ℝ, E3) x)]
  {g : SmoothRiemannianMetric 𝓘(ℝ, E3) M} {hEnorm : IsMetricNorm g}
  {Δ σ μ b γ β : ℝ} {A : Set M} {ρ F : M → ℝ}

/-- The open part of the slab where the edge coordinate `η_p` is a submersion. -/
def EdgeDiskPacket.slabRegular (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) :
    TopologicalSpace.Opens P.slabOpen :=
  letI := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  ⟨{y | Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) (fun y : P.slabOpen => P.coord y) y)},
    Ehresmann.isOpen_setOf_surjective_mfderiv P.contMDiff_coord_slab⟩

/-- The regular slice `{η_p = 0}` of the slab (inside `slabRegular`). -/
abbrev EdgeDiskPacket.Slice (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) : Type _ :=
  {y : P.slabRegular // P.coord ((y : P.slabOpen) : M) = 0}

/-- On `slabRegular`, `η_p` is a submersion with complement `ℝ²` at every point of its zero
level. -/
theorem EdgeDiskPacket.isSubmersionAt_coord_slabRegular
    (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) :
    letI := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
    letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
    ∀ x : P.slabRegular, P.coord ((x : P.slabOpen) : M) = 0 →
      Manifold.IsSubmersionAtOfComplement E2 (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
        (fun y : P.slabRegular => P.coord ((y : P.slabOpen) : M)) x := by
  let _ := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  intro x _
  have hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun y : P.slabRegular => P.coord ((y : P.slabOpen) : M)) :=
    P.contMDiff_coord_slab.comp contMDiff_subtype_val
  have hs : Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ)
      (fun y : P.slabRegular => P.coord ((y : P.slabOpen) : M)) x) :=
    Ehresmann.surjective_mfderiv_comp_opens_val P.slabRegular x
      ((P.contMDiff_coord_slab (x : P.slabOpen)).mdifferentiableAt (by simp)) x.2
  have hdim : Module.finrank ℝ (Fin (Module.finrank ℝ (ℝ × E2) - Module.finrank ℝ ℝ) → ℝ) =
      Module.finrank ℝ E2 := by
    rw [Module.finrank_fin_fun, Module.finrank_prod, finrank_euclideanSpace_fin,
      Module.finrank_self]
  exact (Topology.Manifold.isSubmersionAtOfComplement_of_surjective_mfderiv _ hf x hs).trans_F
    (ContinuousLinearEquiv.ofFinrankEq hdim)

/-- The charted space (over `ℝ²`) of the regular slice: the regular-level charts of `η_p`. -/
@[reducible]
def EdgeDiskPacket.sliceChartedSpace (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) :
    ChartedSpace E2 P.Slice :=
  letI := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  Topology.Manifold.submersionFiberChartedSpace _ 0 P.isSubmersionAt_coord_slabRegular

/-- The regular slice is a smooth surface. -/
theorem EdgeDiskPacket.slice_isManifold (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) :
    letI := P.sliceChartedSpace
    IsManifold (𝓡 2) ∞ P.Slice := by
  let _ := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  exact Topology.Manifold.submersionFiberIsManifold _ 0 P.isSubmersionAt_coord_slabRegular

/-- The inclusion of the slice into the slab is smooth. -/
theorem EdgeDiskPacket.contMDiff_sliceVal (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) :
    letI := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
    letI := P.sliceChartedSpace
    ContMDiff (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (fun s : P.Slice => ((s.1 : P.slabRegular) : P.slabOpen)) := by
  let _ := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  let _ := P.sliceChartedSpace
  exact contMDiff_subtype_val.comp
    (Topology.Manifold.contMDiff_submersionFiberInclusion _ 0 P.isSubmersionAt_coord_slabRegular)

/-- The inclusion of the fibre `{η_p = 0, H ≤ 4Δ}` into the regular slice. -/
def EdgeDiskPacket.fibreToSlice (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) :
    {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} → P.Slice :=
  fun y => ⟨⟨y.1, P.regular_fibre y.1 y.2.1 y.2.2⟩, y.2.1⟩

theorem EdgeDiskPacket.injective_fibreToSlice (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) :
    Injective P.fibreToSlice := by
  intro y y' h
  apply Subtype.ext
  exact congrArg (fun s : P.Slice => ((s.1 : P.slabRegular) : P.slabOpen)) h

/-- The inclusion of the fibre into the slice is smooth. -/
theorem EdgeDiskPacket.contMDiff_fibreToSlice (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) :
    letI := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
    letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
    letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
      P.contMDiff_height_slab P.regular_fibre P.regular_boundary
    letI := P.sliceChartedSpace
    ContMDiff (𝓡∂ (1 + 1)) (𝓡 2) ∞ P.fibreToSlice := by
  let _ := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
    P.contMDiff_height_slab P.regular_fibre P.regular_boundary
  let _ := P.sliceChartedSpace
  have hv : ContMDiff (𝓡∂ (1 + 1)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞
      (Subtype.val : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} →
        P.slabOpen) :=
    regularSublevel_contMDiff_val finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
      P.contMDiff_height_slab P.regular_fibre P.regular_boundary
  let gU : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} →
      P.slabRegular := fun y => ⟨y.1, P.regular_fibre y.1 y.2.1 y.2.2⟩
  have hgU : ContMDiff (𝓡∂ (1 + 1)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ gU :=
    (ContMDiff.subtypeVal_comp_iff P.slabRegular gU).mp hv
  exact Topology.Manifold.contMDiff_submersionFiberCorestrict _ 0
    P.isSubmersionAt_coord_slabRegular gU hgU (fun z => z.2.1)

/-- The inclusion of the fibre into the slice is an immersion. -/
theorem EdgeDiskPacket.injective_mfderiv_fibreToSlice
    (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) :
    letI := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
    letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
    letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
      P.contMDiff_height_slab P.regular_fibre P.regular_boundary
    letI := P.sliceChartedSpace
    ∀ y : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y},
      Injective (mfderiv (𝓡∂ (1 + 1)) (𝓡 2) P.fibreToSlice y) := by
  let _ := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
    P.contMDiff_height_slab P.regular_fibre P.regular_boundary
  let _ := P.sliceChartedSpace
  intro y
  let pr : P.Slice → P.slabOpen := fun s => ((s.1 : P.slabRegular) : P.slabOpen)
  have hAd : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℝ).prod (𝓡 2)) pr (P.fibreToSlice y) :=
    (P.contMDiff_sliceVal _).mdifferentiableAt (by simp)
  have hιd : MDifferentiableAt (𝓡∂ (1 + 1)) (𝓡 2) P.fibreToSlice y :=
    (P.contMDiff_fibreToSlice y).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp y hAd hιd
  have hval := regularSublevel_mfderiv_val_injective finrank_real_prod_euclideanTwo
    P.contMDiff_coord_slab P.contMDiff_height_slab P.regular_fibre P.regular_boundary y
  intro u v huv
  apply hval
  change mfderiv (𝓡∂ (1 + 1)) (𝓘(ℝ, ℝ).prod (𝓡 2)) (pr ∘ P.fibreToSlice) y u =
    mfderiv (𝓡∂ (1 + 1)) (𝓘(ℝ, ℝ).prod (𝓡 2)) (pr ∘ P.fibreToSlice) y v
  rw [hcomp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, huv]

/-- **The chart of the packet fibre in the slice.** The disk model of an edge disk packet extends
across the rim: a partial diffeomorphism `j` from a neighbourhood of the closed unit disk into the
regular slice `{η_p = 0}` of the slab with `j = P.diskModel` on the disk. -/
theorem EdgeDiskPacket.exists_sliceChart (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F) :
    letI := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
    letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
    letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
      P.contMDiff_height_slab P.regular_fibre P.regular_boundary
    letI := P.sliceChartedSpace
    ∃ j : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 P.Slice ∞,
      closedBall (0 : E2) 1 ⊆ j.source ∧
      ∀ z : ClosedCell 2, (((j (z : E2)).1 : P.slabOpen) : M) = ((P.diskModel z).1 : M) := by
  let _ := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
    P.contMDiff_height_slab P.regular_fibre P.regular_boundary
  let _ := P.sliceChartedSpace
  have _ : IsManifold (𝓡 2) ∞ P.Slice := P.slice_isManifold
  obtain ⟨j, hjs, hjD⟩ := Topology.Manifold.exists_partialDiffeomorph_extend_diskModel (m := 1)
    P.diskModel P.fibreToSlice P.contMDiff_fibreToSlice P.injective_fibreToSlice
    P.injective_mfderiv_fibreToSlice
  refine ⟨j, hjs, fun z => ?_⟩
  rw [hjD z]
  rfl

/-- **The both-sides polar collar of the packet fibre in the slice.** For `κ > 0` and
`0 < η < 1`: a re-modelled disk model `D` of the fibre (equal to `P.diskModel` on the rim circle and
on `‖z‖ ≤ 1 - η`) and a partial diffeomorphism `C` from the annulus `{|‖z‖ - 1| < δ}` into the
regular slice `{η_p = 0}` with `H (C z) = 4Δ + κ (‖z‖ - 1)` on BOTH sides of the rim,
`C = P.diskModel` on the rim circle and `D = C` on the inner side `1 - δ < ‖z‖`. -/
theorem EdgeDiskPacket.exists_polarCollar_twoSided (P : EdgeDiskPacket g hEnorm Δ σ μ b γ β A ρ F)
    {κ : ℝ} (hκ : 0 < κ) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) :
    letI := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
    letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
    letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
      P.contMDiff_height_slab P.regular_fibre P.regular_boundary
    letI := P.sliceChartedSpace
    ∃ δ : ℝ, 0 < δ ∧ δ < η ∧
      ∃ D : ClosedCell 2 ≃ₘ⟮𝓡∂ (1 + 1), 𝓡∂ (1 + 1)⟯
        {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y},
      ∃ C : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 P.Slice ∞,
        C.source = {z : E2 | |‖z‖ - 1| < δ} ∧
        (∀ z ∈ C.source,
          edgeRowHeight Δ F ρ (((C z).1 : P.slabOpen) : M) = 4 * Δ + κ * (‖z‖ - 1)) ∧
        (∀ z : ClosedCell 2, ‖(z : E2)‖ = 1 →
          (((C (z : E2)).1 : P.slabOpen) : M) = ((P.diskModel z).1 : M)) ∧
        (∀ z : ClosedCell 2, 1 - δ < ‖(z : E2)‖ →
          ((D z).1 : M) = (((C (z : E2)).1 : P.slabOpen) : M)) ∧
        (∀ z : ClosedCell 2, ‖(z : E2)‖ = 1 → ((D z).1 : M) = ((P.diskModel z).1 : M)) ∧
        (∀ z : ClosedCell 2, ‖(z : E2)‖ ≤ 1 - η → ((D z).1 : M) = ((P.diskModel z).1 : M)) := by
  let _ := chartedSpaceTransHomeomorph (M := P.slabOpen) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ P.slabOpen := edgeSource_isManifold
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo P.contMDiff_coord_slab
    P.contMDiff_height_slab P.regular_fibre P.regular_boundary
  let _ := P.sliceChartedSpace
  have _ : IsManifold (𝓡 2) ∞ P.Slice := P.slice_isManifold
  let T : P.Slice → ℝ := fun s => edgeRowHeight Δ F ρ (((s.1 : P.slabRegular) : P.slabOpen) : M)
  have hT : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ T := by
    have h1 : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun s : P.Slice =>
        4 * Δ - (4 * Δ - edgeRowHeight Δ F ρ (((s.1 : P.slabRegular) : P.slabOpen) : M))) :=
      contMDiff_const.sub (P.contMDiff_height_slab.comp P.contMDiff_sliceVal)
    have h2 : (fun s : P.Slice =>
        4 * Δ - (4 * Δ - edgeRowHeight Δ F ρ (((s.1 : P.slabRegular) : P.slabOpen) : M))) = T :=
      funext fun s => by ring
    rw [h2] at h1
    exact h1
  have hbd : ∀ y : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y},
      (𝓡∂ (1 + 1)).IsBoundaryPoint y → edgeRowHeight Δ F ρ y = 4 * Δ :=
    fun y hy => P.boundary_level.1 y hy
  have hreg : ∀ y : {y : P.slabOpen // P.coord y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y},
      (𝓡∂ (1 + 1)).IsBoundaryPoint y → mfderiv (𝓡 2) 𝓘(ℝ, ℝ) T (P.fibreToSlice y) ≠ 0 := by
    intro y hy h0
    have hne := regularSublevel_mfderiv_ne_zero finrank_real_prod_euclideanTwo
      P.contMDiff_coord_slab P.contMDiff_height_slab P.regular_fibre P.regular_boundary y
      (by rw [hbd y hy, sub_self])
    apply hne
    have hTd : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) T (P.fibreToSlice y) :=
      (hT _).mdifferentiableAt (by simp)
    have hιd : MDifferentiableAt (𝓡∂ (1 + 1)) (𝓡 2) P.fibreToSlice y :=
      (P.contMDiff_fibreToSlice y).mdifferentiableAt (by simp)
    have hc : HasMFDerivAt (𝓡∂ (1 + 1)) 𝓘(ℝ, ℝ) (T ∘ P.fibreToSlice) y 0 := by
      have h1 := (hTd.comp y hιd).hasMFDerivAt
      rw [mfderiv_comp y hTd hιd, h0, ContinuousLinearMap.zero_comp] at h1
      exact h1
    have h2 := (hasMFDerivAt_const (I := 𝓡∂ (1 + 1)) (4 * Δ) y).sub hc
    exact h2.mfderiv.trans (sub_zero _)
  obtain ⟨δ, hδ0, hδη, D, C, hCs, hCT, hCS, hCD, hDS, hDη⟩ :=
    Topology.Manifold.exists_diskModel_polar_twoSided_of_immersion (m := 1) P.diskModel
      P.fibreToSlice P.contMDiff_fibreToSlice P.injective_fibreToSlice
      P.injective_mfderiv_fibreToSlice (T := T) (V := univ) isOpen_univ (fun _ _ => mem_univ _)
      hT.contMDiffOn (c := 4 * Δ) (fun y hy => hbd y hy)
      (fun y _ => by
        change edgeRowHeight Δ F ρ y ≤ 4 * Δ
        linarith [y.2.2])
      hreg hκ hη0 hη1
  refine ⟨δ, hδ0, hδη, D, C, hCs, fun z hz => (hCT z hz).2, fun z hz => ?_, fun z hz => ?_,
    fun z hz => ?_, fun z hz => ?_⟩
  · rw [hCS z hz]
    rfl
  · rw [← hCD z hz]
    rfl
  · rw [hDS z hz]
  · rw [hDη z hz]

end Packet

end DifferentialGeometry.Geometry.Collapse
