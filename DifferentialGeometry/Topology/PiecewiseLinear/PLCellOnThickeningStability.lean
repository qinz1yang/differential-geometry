import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnStability
import Mathlib.Topology.MetricSpace.Thickening

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M₁ M₂ : Type*} [TopologicalSpace M₁]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem exists_cthickening_subset_image_interior_stable_of_isPLCellOn
    {S B K : Set M₁} {F : M₁ → M₂}
    (hS : IsPLCellOn 3 S B) (hFc : ContinuousOn F S) (hFi : InjOn F S)
    (hK : IsCompact K) (hKS : K ⊆ S \ B) :
    ∃ δ > 0, ∀ G : M₁ → M₂, IsPLHomeomorphInto 3 G S →
      (∀ z ∈ S, dist (F z) (G z) < δ) →
      Metric.cthickening δ (F '' K) ⊆ interior (G '' S) := by
  let _ : LocallyCompactSpace M₁ :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) M₁
  have hKI : K ⊆ interior S := by
    rw [← hS.sdiff_boundary_eq_interior]
    exact hKS
  obtain ⟨L, hL, hKL, hLS⟩ := exists_compact_between hK isOpen_interior hKI
  have hILS : interior L ⊆ S := interior_subset.trans (hLS.trans interior_subset)
  have hopen : IsOpen (F '' interior L) :=
    isOpen_image_of_continuousOn_injOn (E := EuclideanSpace ℝ (Fin 3)) isOpen_interior
      (hFc.mono hILS) (hFi.mono hILS)
  have hFK : IsCompact (F '' K) :=
    hK.image_of_continuousOn (hFc.mono (hKI.trans interior_subset))
  obtain ⟨r, hr, hrK⟩ := hFK.exists_cthickening_subset_open hopen (image_mono hKL)
  have hLB : L ⊆ S \ B := by
    rw [hS.sdiff_boundary_eq_interior]
    exact hLS
  obtain ⟨s, hs, hstable⟩ :=
    exists_dist_lt_image_interior_stable_of_isPLCellOn hS hFc hFi hL hLB
  refine ⟨min r s, lt_min hr hs, fun G hG hclose => ?_⟩
  exact (Metric.cthickening_mono (min_le_left r s) (F '' K)).trans
    (hrK.trans ((image_mono interior_subset).trans
      (hstable G hG (fun z hz => (hclose z hz).trans_le (min_le_right r s)))))

end DifferentialGeometry.Topology.PiecewiseLinear
