import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeDiskChartOED
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeDiskConsumerOED

/-!
# The edge disk chart from a local record: a compiled consumer (lane O-EDGEDISK, G1b)

`modelCylinder_smoothDiskChartAt_OED`: `smoothDiskChartAt_of_localRecord_OED` on the model edge
piece `M = N = ℝ² × ℝ¹` (`ι = id`), stage map `f = pr₂ : M → ℝ¹`, height `T (v, x) = ‖v‖²` at the
level `a = 1`, source `X = {T ≤ 1}` (not open), base `B = ℝ¹`, the trivial record
`κ = id`, `σ₀ = id`, `Dset = Wb = Mk = O' = Pi = univ`, and the standard disk `ψ w = (w, 0)` over
`y = 0`: the conclusion is the disk-chart contract `SmoothDiskChartAt_BIFc` at `0` with rim
`{‖v‖ = 1}`. The cross-model argument `hιc` is discharged by
`isSmoothEmbedding_comp_diskChart_of_boundaryless_OED`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Topology Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ¹" => EuclideanSpace ℝ (Fin 1)

/-- **The model edge piece through the M-level edge disk chart.** -/
theorem modelCylinder_smoothDiskChartAt_OED :
    SmoothDiskChartAt_BIFc 𝓘(ℝ, ℝ² × ℝ¹) 1 (Prod.snd : ℝ² × ℝ¹ → ℝ¹)
      (fun z => ‖z.1‖ ^ 2) 1 {z | z ∈ univ ∧ ‖z.1‖ ^ 2 ≤ 1} univ 0 := by
  have hdim : Module.finrank ℝ (ℝ² × ℝ¹) = 1 + 1 + 1 := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  have hnorm : ∀ v : ℝ², ‖v‖ ^ 2 ≤ 1 ↔ ‖v‖ ≤ 1 :=
    fun v => pow_le_one_iff_of_nonneg (norm_nonneg v) two_ne_zero
  have hT : ContMDiff 𝓘(ℝ, ℝ² × ℝ¹) 𝓘(ℝ, ℝ) ∞ (fun z : ℝ² × ℝ¹ => ‖z.1‖ ^ 2) :=
    ((contDiff_norm_sq ℝ).comp contDiff_fst).contMDiff
  refine smoothDiskChartAt_of_localRecord_OED hdim id IsEmbedding.id
    (isSmoothEmbedding_comp_diskChart_of_boundaryless_OED (IsSmoothEmbedding.id))
    (Prod.snd : ℝ² × ℝ¹ → ℝ¹) (fun z => ‖z.1‖ ^ 2) 1 univ {z | z ∈ univ ∧ ‖z.1‖ ^ 2 ≤ 1} univ
    (ContinuousLinearMap.id ℝ ℝ¹) id univ univ univ univ isOpen_univ (inter_univ _).symm
    isOpen_univ isOpen_univ isOpen_univ contDiffOn_id (fun b _ => ⟨⟨mem_univ _, mem_univ _⟩, rfl⟩)
    (fun b _ => ⟨mem_univ _, rfl⟩) rfl (fun z _ => ⟨z, rfl⟩) ?_ isOpen_univ continuous_snd
    contDiff_snd.contMDiff hT ?_ ?_ ?_ (mem_univ _) (mem_univ _) (mem_univ _)
    (fun w => ((w : ℝ²), (0 : ℝ¹))) (Handle.closedCellInclusion_isSmoothEmbedding 1).prodMk_zero
    ?_ ?_
  · ext x
    exact ⟨fun _ => mem_univ _, fun _ => ⟨(0, x), ⟨mem_univ _, by simp⟩, rfl⟩⟩
  · intro x _ _ _
    rw [mfderiv_eq_fderiv]
    change Surjective (fderiv ℝ (Prod.snd : ℝ² × ℝ¹ → ℝ¹) x)
    rw [fderiv_snd]
    intro a
    exact ⟨(0, a), rfl⟩
  · intro x _ hx _ _
    have h := surjective_mfderiv_pair_const_sub_OED 1
      (((contDiff_snd.contMDiff : ContMDiff 𝓘(ℝ, ℝ² × ℝ¹) 𝓘(ℝ, ℝ¹) ∞
        (Prod.snd : ℝ² × ℝ¹ → ℝ¹)) x).mdifferentiableAt (by simp))
      (((contMDiff_const.sub hT) x).mdifferentiableAt (by simp))
      (modelCylinder_pair_surjective_OED x (by
        change ‖x.1‖ ^ 2 = 1 at hx
        rw [hx]
        ring))
    have heq : (fun z : ℝ² × ℝ¹ => (z.2, (1 : ℝ) - (1 - ‖z.1‖ ^ 2))) =
        fun z : ℝ² × ℝ¹ => ((ContinuousLinearMap.id ℝ ℝ¹) ((id z).2), ‖(id z).1‖ ^ 2) := by
      funext z
      refine Prod.ext rfl ?_
      change (1 : ℝ) - (1 - ‖z.1‖ ^ 2) = ‖z.1‖ ^ 2
      ring
    rw [heq] at h
    exact h
  · intro Kc _ hK
    have heq : {z : ℝ² × ℝ¹ | z ∈ univ ∧ ‖z.1‖ ^ 2 ≤ 1} ∩ Prod.snd ⁻¹' Kc =
        closedBall (0 : ℝ²) 1 ×ˢ Kc := by
      ext z
      rw [mem_prod, mem_closedBall_zero_iff, ← hnorm]
      exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨mem_univ _, h.1⟩, h.2⟩⟩
    rw [heq]
    exact (isCompact_closedBall 0 1).prod hK
  · ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨⟨mem_univ _, (hnorm _).mpr w.2⟩, rfl⟩
    · rintro ⟨⟨-, h2⟩, h3⟩
      exact ⟨⟨z.1, (hnorm _).mp h2⟩, Prod.ext rfl h3.symm⟩
  · intro w
    exact pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero

end DifferentialGeometry.Geometry.Collapse
