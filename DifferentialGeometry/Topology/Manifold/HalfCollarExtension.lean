import DifferentialGeometry.Topology.Manifold.CompactBicollar
import DifferentialGeometry.Topology.Manifold.CompactProductBoundaryExtension
import DifferentialGeometry.Topology.Manifold.HalfClosedIntervalLocalDiffeomorph

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

variable {F HS S E HM M : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace HS] {J : ModelWithCorners ℝ F HS} [J.Boundaryless]
  [TopologicalSpace S] [ChartedSpace HS S] [IsManifold J ∞ S]
  [T2Space S] [CompactSpace S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace HM] {I : ModelWithCorners ℝ E HM} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M] [T2Space M]

theorem exists_smoothTwoSidedCollar_of_halfClosedInterval
    {w : ℝ} (hw : 0 < w) (c : S × Ico (0 : ℝ) w → M)
    (hc : letI := Manifold.halfClosedIntervalChartedSpace hw
      ContMDiff (J.prod (𝓡∂ 1)) I ∞ c)
    (hinj : Function.Injective (fun s => c (s, ⟨0, le_rfl, hw⟩)))
    (hderiv : letI := Manifold.halfClosedIntervalChartedSpace hw
      ∀ s, Function.Bijective (mfderiv (J.prod (𝓡∂ 1)) I c (s, ⟨0, le_rfl, hw⟩))) :
    ∃ d : SmoothTwoSidedCollar J I (fun s => c (s, ⟨0, le_rfl, hw⟩)),
      ∃ hwidth : d.radius ≤ w, ∀ p (hp : 0 ≤ p.2.val),
        d.toFun p = c (p.1, ⟨p.2.val, hp, p.2.property.2.trans_le hwidth⟩) := by
  let r := w / 2
  have hr : 0 < r := half_pos hw
  have hrw : r < w := half_lt_self hw
  obtain ⟨Φ, N, hN, hKN, hΦ, heq⟩ :=
    exists_contMDiffOn_extension_prod_Ico hr.le hrw c hc
  have hzero : ∀ s, (s, (0 : ℝ)) ∈ N :=
    fun s => hKN ⟨mem_univ s, le_rfl, hr.le⟩
  have hloc := Manifold.isLocalDiffeomorphAt_of_eqOn_halfClosedInterval
    hr hrw c Φ hN hzero hΦ heq hderiv
  obtain ⟨d, hdr, hd⟩ := exists_smoothTwoSidedCollar_eq_of_localDiffeomorphAt_zero
    hinj Φ Φ.continuous (fun s => heq s 0 ⟨le_rfl, hr.le⟩) hloc r hr
  refine ⟨d, hdr.trans hrw.le, ?_⟩
  intro p hp
  exact (hd p).trans (heq p.1 p.2.val ⟨hp, p.2.property.2.le.trans hdr⟩)

end DifferentialGeometry.Topology
