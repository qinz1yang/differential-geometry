import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.LateSliceSplice
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem finite_chart_balls
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ∃ s : Finset M, ∃ R : M → Real, ∃ v : ENNReal,
      s.Nonempty ∧ 0 < v ∧
        (∀ p ∈ s, 0 < R p ∧
          Metric.closedBall ((extChartAt I p) p) (R p) ⊆
            interior (extChartAt I p).target ∧
          v ≤ riemannianVolumeMeasure (I := I) (M := M) g
            ((extChartAt I p).symm ''
              Metric.ball ((extChartAt I p) p) (R p))) ∧
        ∀ x : M, ∃ p ∈ s,
          x ∈ (chartAt H p).source ∧
            (extChartAt I p) x ∈
              Metric.ball ((extChartAt I p) p) (R p) := by
  classical
  have hlocal : ∀ p : M, ∃ r : Real, 0 < r ∧
      Metric.closedBall ((extChartAt I p) p) r ⊆
        interior (extChartAt I p).target := by
    intro p
    have hpTarget : (extChartAt I p) p ∈ (extChartAt I p).target :=
      (extChartAt I p).map_source (mem_extChartAt_source (I := I) p)
    have hpInt : (extChartAt I p) p ∈ interior (extChartAt I p).target :=
      by
        rw [(isOpen_extChartAt_target (I := I) p).interior_eq]
        exact hpTarget
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp
      (isOpen_interior.mem_nhds hpInt)
    refine ⟨δ / 2, half_pos hδ, ?_⟩
    exact (Metric.closedBall_subset_ball (half_lt_self hδ)).trans hδsub
  choose R hRpos hRtarget using hlocal
  let U : M → Set M := fun p ↦
    (extChartAt I p).symm '' Metric.ball ((extChartAt I p) p) (R p)
  have hballTarget : ∀ p : M,
      Metric.ball ((extChartAt I p) p) (R p) ⊆
        (extChartAt I p).target := by
    intro p z hz
    exact interior_subset (hRtarget p (Metric.ball_subset_closedBall hz))
  have hUopen : ∀ p : M, IsOpen (U p) := by
    intro p
    change IsOpen ((extChartAt I p).symm ''
      Metric.ball ((extChartAt I p) p) (R p))
    rw [(extChartAt I p).symm_image_eq_source_inter_preimage (hballTarget p)]
    exact isOpen_extChartAt_preimage' (I := I) p Metric.isOpen_ball
  have hpU : ∀ p : M, p ∈ U p := by
    intro p
    refine ⟨(extChartAt I p) p, Metric.mem_ball_self (hRpos p), ?_⟩
    exact (extChartAt I p).left_inv (mem_extChartAt_source (I := I) p)
  have hcover : (univ : Set M) ⊆ ⋃ p : M, U p := by
    intro p _hp
    exact mem_iUnion.mpr ⟨p, hpU p⟩
  obtain ⟨s, hsCover⟩ :=
    (isCompact_univ : IsCompact (univ : Set M)).elim_finite_subcover
      U hUopen hcover
  have hsne : s.Nonempty := by
    have hx := hsCover (mem_univ x₀)
    rw [mem_iUnion₂] at hx
    obtain ⟨p, hp, _⟩ := hx
    exact ⟨p, hp⟩
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  let v : ENNReal := s.inf' hsne (fun p ↦ μ (U p))
  have hvpos : 0 < v := by
    rw [show v = s.inf' hsne (fun p ↦ μ (U p)) from rfl,
      Finset.lt_inf'_iff]
    intro p _hp
    exact (hUopen p).measure_pos μ ⟨p, hpU p⟩
  have hvle : ∀ p ∈ s, v ≤ μ (U p) := by
    intro p hp
    exact Finset.inf'_le (fun q ↦ μ (U q)) hp
  refine ⟨s, R, v, hsne, hvpos, ?_, ?_⟩
  · intro p hp
    exact ⟨hRpos p, hRtarget p, hvle p hp⟩
  · intro x
    have hx := hsCover (mem_univ x)
    rw [mem_iUnion₂] at hx
    obtain ⟨p, hp, z, hz, hzx⟩ := hx
    have hzTarget : z ∈ (extChartAt I p).target := hballTarget p hz
    have hxSource : x ∈ (extChartAt I p).source := by
      rw [← hzx]
      exact (extChartAt I p).map_target hzTarget
    refine ⟨p, hp, ?_, ?_⟩
    · simpa only [extChartAt_source] using hxSource
    · rw [← hzx, (extChartAt I p).right_inv hzTarget]
      exact hz

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
