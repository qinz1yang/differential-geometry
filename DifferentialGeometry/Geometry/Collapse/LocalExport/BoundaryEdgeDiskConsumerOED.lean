import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryEdgeDiskKernelOED
import DifferentialGeometry.Topology.Handle.Embedding
import DifferentialGeometry.Topology.Embedding.Graph

/-!
# The edge disk kernel (c): a compiled consumer on the model solid cylinder (lane O-EDGEDISK, G1)

`modelCylinder_diskChart_OED`: the kernel `exists_diskChart_of_sideBoundary_trivialization_OED`
applied to the model edge piece `ℝ² × ℝ¹` with `P = pr₂`, side function `Bh (v, x) = 1 - ‖v‖²`,
`R = univ`, `b₀ = 0`, `ε = 1`, and the standard closed disk `ψ w = (w, 0)` as the whole fibre over
`0`: the region `{|x| < 1/2, ‖v‖ ≤ 1}` gets a smooth product chart `ℝ¹ × D²` with rim
`{‖v‖ = 1}`. This shows that the kernel's hypotheses (submersion of `P` on `{Bh ≥ 0}`, of `(P, Bh)`
on the side boundary `{Bh = 0}`, properness, a standard disk onto the whole fibre with rim
`{Bh = 0}`) are satisfiable and mutually consistent.
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

/-- The side function of the model cylinder has the derivative `(v, x) ↦ -2 ⟪v₀, v⟫`. -/
theorem modelCylinder_pair_surjective_OED (z : ℝ² × ℝ¹) (hz : 1 - ‖z.1‖ ^ 2 = 0) :
    Surjective (mfderiv 𝓘(ℝ, ℝ² × ℝ¹) 𝓘(ℝ, ℝ¹ × ℝ)
      (fun y : ℝ² × ℝ¹ => (y.2, 1 - ‖y.1‖ ^ 2)) z) := by
  have hd : HasFDerivAt (fun y : ℝ² × ℝ¹ => (y.2, 1 - ‖y.1‖ ^ 2))
      ((ContinuousLinearMap.snd ℝ ℝ² ℝ¹).prod
        (-(2 • (innerSL ℝ z.1).comp (ContinuousLinearMap.fst ℝ ℝ² ℝ¹)))) z :=
    hasFDerivAt_snd.prodMk ((hasFDerivAt_fst.norm_sq).const_sub 1)
  rw [mfderiv_eq_fderiv, hd.fderiv]
  intro q
  refine ⟨(-(q.2 / 2) • z.1, q.1), ?_⟩
  have hn : ‖z.1‖ ^ 2 = 1 := by linarith
  refine Prod.ext rfl ?_
  change -(2 • (innerSL ℝ z.1) (-(q.2 / 2) • z.1)) = q.2
  rw [innerSL_apply_apply, inner_smul_right, real_inner_self_eq_norm_sq, hn, nsmul_eq_mul]
  ring

/-- **The model edge piece through the edge disk kernel.** -/
theorem modelCylinder_diskChart_OED :
    ∃ ε' : ℝ, 0 < ε' ∧ ball (0 : ℝ¹) ε' ⊆ ball (0 : ℝ¹) 1 ∧
      ∃ Φ : ℝ¹ × ClosedCell 2 → ℝ² × ℝ¹,
        IsSmoothEmbedding ((𝓡 1).prod (𝓡∂ 2)) 𝓘(ℝ, ℝ² × ℝ¹) ∞ Φ ∧
        range Φ = {z | z ∈ univ ∧ z.2 ∈ ball (0 : ℝ¹) ε' ∧ 0 ≤ 1 - ‖z.1‖ ^ 2} ∧
        (∀ x w, (Φ (x, w)).2 = OpenPartialHomeomorph.univBall (0 : ℝ¹) ε' x) ∧
        ∀ x w, 1 - ‖(Φ (x, w)).1‖ ^ 2 = 0 ↔ ‖(w : ℝ²)‖ = 1 := by
  have hdim : Module.finrank ℝ (ℝ² × ℝ¹) = 1 + 1 + 1 := by
    rw [Module.finrank_prod, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  have hnorm : ∀ v : ℝ², 0 ≤ 1 - ‖v‖ ^ 2 ↔ ‖v‖ ≤ 1 := by
    intro v
    rw [sub_nonneg, pow_le_one_iff_of_nonneg (norm_nonneg v) two_ne_zero]
  refine exists_diskChart_of_sideBoundary_trivialization_OED hdim
    (Prod.snd : ℝ² × ℝ¹ → ℝ¹) (fun z => 1 - ‖z.1‖ ^ 2) contDiff_snd.contMDiff
    (contDiff_const.sub ((contDiff_norm_sq ℝ).comp contDiff_fst)).contMDiff univ isOpen_univ
    one_pos ?_ ?_ ?_ (fun w => ((w : ℝ²), (0 : ℝ¹)))
    (Handle.closedCellInclusion_isSmoothEmbedding 1).prodMk_zero ?_ ?_
  · intro x _ _
    rw [mfderiv_eq_fderiv, fderiv_snd]
    intro a
    exact ⟨(0, a), rfl⟩
  · intro x _ hx
    exact modelCylinder_pair_surjective_OED x hx
  · intro K _ hK
    have heq : {x : ℝ² × ℝ¹ | x ∈ univ ∧ x.2 ∈ K ∧ 0 ≤ 1 - ‖x.1‖ ^ 2} =
        closedBall (0 : ℝ²) 1 ×ˢ K := by
      ext x
      rw [mem_prod, mem_closedBall_zero_iff, ← hnorm]
      exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨mem_univ _, h.2, h.1⟩⟩
    rw [heq]
    exact (isCompact_closedBall 0 1).prod hK
  · ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨mem_univ _, rfl, (hnorm _).mpr w.2⟩
    · rintro ⟨-, h2, h3⟩
      exact ⟨⟨z.1, (hnorm _).mp h3⟩, Prod.ext rfl h2.symm⟩
  · intro w
    rw [sub_eq_zero, eq_comm, pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]

end DifferentialGeometry.Geometry.Collapse
