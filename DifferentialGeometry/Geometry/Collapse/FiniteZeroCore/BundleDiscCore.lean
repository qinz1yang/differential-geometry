import DifferentialGeometry.Geometry.Collapse.SublevelCore.PointNormalFlowRadius
import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenDiscCoreType

/-!
# The disc-core data of a smooth bundle carrier at every scale (LC55 binding for LFR49)

Frozen blueprint master207A, LFR49 (A:29096): "In the smooth coordinates of the actual normal-flow
map, every radial fiber crosses this boundary exactly once … Its compactly supported vertical
isotopy therefore gives the ACTUAL smooth disk-bundle identification". On LFR47's carrier the
normal-flow map is a SMOOTH diffeomorphism `D : TotalSpace F V ≃ N` (`TransportedCarrier.diffeomorph`),
so the fibre radius `u = ‖(D⁻¹ ·).2‖` is a core coordinate in the sense of the LC61 kernels:

`bundle_disc_core_data` (statement T5 of lane LFR49): `u` is continuous, proper, nonnegative,
smooth where positive, and for EVERY `T > 0` the interior of `{u ≤ T}` is diffeomorphic to the
whole carrier (`exists_partialDiffeomorph_discCore_interior`, then `D`). No metric of the carrier
enters, so the finite order of LFR47's metric is irrelevant here.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.VectorBundle

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [CompactSpace B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB ∞ F V]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- **LC55 disc-core binding (every scale).** For a smooth diffeomorphism `D` from the total
space of a smooth Riemannian bundle over a compact base (LFR47's carrier map), the fibre radius
`u = ‖(D⁻¹ ·).2‖` is a continuous proper core coordinate, nonnegative, smooth where positive, and
for every `T > 0` the interior of the core `{u ≤ T}` is diffeomorphic to the whole carrier. -/
theorem bundle_disc_core_data
    (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) :
    Continuous (fun y => ‖(D.symm y).2‖) ∧ (∀ T, IsCompact {y | ‖(D.symm y).2‖ ≤ T}) ∧
      (∀ y, 0 ≤ ‖(D.symm y).2‖) ∧
      ContMDiffOn IN 𝓘(ℝ, ℝ) ∞ (fun y => ‖(D.symm y).2‖) {y | 0 < ‖(D.symm y).2‖} ∧
      ∀ T : ℝ, 0 < T → ∃ Ψ : PartialDiffeomorph IN IN N N ∞,
        Ψ.source = interior {y | ‖(D.symm y).2‖ ≤ T} ∧ Ψ.target = univ := by
  have hsub : {y : N | 0 < ‖(D.symm y).2‖} ⊆ {y : N | (D.symm y).2 ≠ 0} :=
    fun y hy => norm_pos_iff.mp hy
  refine ⟨continuous_discCoreRadius_of_isContMDiffRiemannianBundle D, isCompact_discCore D,
    fun y => norm_nonneg _, (contMDiffOn_discCoreRadius_off_zero D).mono hsub, fun T hT => ?_⟩
  obtain ⟨Ψ, hΨs, hΨt⟩ := exists_partialDiffeomorph_discCore_interior D hT
  refine ⟨Ψ.trans D.toPartialDiffeomorph, ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source, hΨs]
    exact inter_eq_left.mpr fun x _ => mem_univ _
  · apply eq_univ_of_forall
    intro y
    refine ⟨mem_univ y, ?_⟩
    change D.symm y ∈ Ψ.target
    rw [hΨt]
    exact mem_univ _

end DifferentialGeometry.Geometry.Collapse
