import DifferentialGeometry.Geometry.Curvature.RescaledPointPicking
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import DifferentialGeometry.Topology.Manifold.ConnectedComponent
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

theorem exists_rescaled_scalar_point_selection_in_component
    {M : ℕ → Type*} [∀ n, TopologicalSpace (M n)] [∀ n, ChartedSpace H (M n)]
    [∀ n, IsManifold I ∞ (M n)] [∀ n, T2Space (M n)]
    (g : ∀ n, SmoothRiemannianMetric I (M n)) (p y : ∀ n, M n)
    (A : ℕ → ℝ) (hA : ∀ n, 0 < A n) {D : ℝ} (hD : 0 ≤ D)
    (hcompact : ∀ n, IsCompact
      (riemannianClosedBallOf (scaleMetric (A n) (hA n) (g n)) (p n) (D + 1)))
    (hy : ∀ n, riemannianEDistOf (scaleMetric (A n) (hA n) (g n)) (p n) (y n) ≤ ENNReal.ofReal D)
    (hfy : ∀ n, 0 < metricScalarAt (g n) (y n))
    (hlim : Tendsto (fun n => metricScalarAt (g n) (y n) / A n) atTop atTop) :
    ∃ (x : ∀ n, M n) (r : ℕ → ℝ),
      (∀ n, 0 < r n ∧ r n < (D + 1)/Real.sqrt (A n) ∧
        riemannianEDistOf (g n) (p n) (x n) < ENNReal.ofReal ((D + 1)/Real.sqrt (A n)) ∧
        0 < metricScalarAt (g n) (x n)) ∧
      Tendsto (fun n => metricScalarAt (g n) (x n) / A n) atTop atTop ∧
      Tendsto (fun n => metricScalarAt (g n) (x n) * r n ^ 2) atTop atTop ∧
      (∀ n, IsCompact (riemannianClosedBallOf (g n) (x n) (r n))) ∧
      ∀ n z, z ∈ riemannianClosedBallOf (g n) (x n) (r n) →
        riemannianEDistOf (g n) (p n) z < ENNReal.ofReal ((D + 1)/Real.sqrt (A n)) ∧
          metricScalarAt (g n) z ≤ (16/9 : ℝ) * metricScalarAt (g n) (x n) := by
  let U := fun n => connectedComponentOpen (I := I) (p n)
  let gc := fun n => (g n).restrictOpen (U n)
  let pc : ∀ n, U n := fun n => connectedComponentPoint (p n)
  have hC : ∀ n, ConnectedSpace (U n) := fun n => connectedComponentOpen_connectedSpace (p n)
  let _ : ∀ n, ConnectedSpace (U n) := hC
  have hscaled (n : ℕ) : scaleMetric (A n) (hA n) (gc n) =
      (scaleMetric (A n) (hA n) (g n)).restrictOpen (U n) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rfl
  have hdist (n : ℕ) (x z : U n) : riemannianEDistOf (gc n) x z =
      riemannianEDistOf (g n) x.val z.val := Metric.edistOf_restrictOpen_connCompOpen _ _ _ _
  have hdscaled (n : ℕ) (x z : U n) :
      riemannianEDistOf (scaleMetric (A n) (hA n) (gc n)) x z =
        riemannianEDistOf (scaleMetric (A n) (hA n) (g n)) x.val z.val := by
    rw [hscaled]
    exact Metric.edistOf_restrictOpen_connCompOpen _ _ _ _
  have hyU (n : ℕ) : y n ∈ U n :=
    Metric.edistOf_ball_subset_connCompOpen (scaleMetric (A n) (hA n) (g n)) (p n) (D+1)
      (lt_of_le_of_lt (hy n) ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)))
  let yc : ∀ n, U n := fun n => ⟨y n,hyU n⟩
  have hcpt (n : ℕ) : IsCompact
      (riemannianClosedBallOf (scaleMetric (A n) (hA n) (gc n)) (pc n) (D+1)) := by
    have heq : riemannianClosedBallOf (scaleMetric (A n) (hA n) (gc n)) (pc n) (D+1) =
        (Subtype.val : U n → M n) ⁻¹' riemannianClosedBallOf
          (scaleMetric (A n) (hA n) (g n)) (p n) (D+1) := by
      ext z
      exact Iff.of_eq (congrArg (fun d => d ≤ ENNReal.ofReal (D+1)) (hdscaled n (pc n) z))
    rw [heq]
    exact (isClosed_connectedComponent (x := p n)).isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage
      (hcompact n)
  obtain ⟨x,r,hr,hQ,hQr,hcompactr,hbound⟩ := exists_rescaled_scalar_point_selection gc pc yc A hA hD hcpt
    (fun n => by rw [hdscaled]; exact hy n)
    (fun n => by rw [CheegerGromovCompactness.metricScalarAt_restrictOpen]; exact hfy n)
    (by simpa only [gc,CheegerGromovCompactness.metricScalarAt_restrictOpen] using hlim)
  refine ⟨fun n => (x n).val,r,?_,?_,?_,?_,?_⟩
  · intro n
    have hh := hr n
    rw [hdist,CheegerGromovCompactness.metricScalarAt_restrictOpen] at hh
    exact hh
  · simpa only [gc,CheegerGromovCompactness.metricScalarAt_restrictOpen] using hQ
  · simpa only [gc,CheegerGromovCompactness.metricScalarAt_restrictOpen] using hQr
  · intro n
    have himg : (Subtype.val : U n → M n) '' riemannianClosedBallOf (gc n) (x n) (r n) =
        riemannianClosedBallOf (g n) (x n).val (r n) := by
      ext z
      constructor
      · rintro ⟨z,hz,rfl⟩
        change riemannianEDistOf (g n) (x n).val z.val ≤ ENNReal.ofReal (r n)
        rw [← hdist]
        exact hz
      · intro hz
        have hzC : z ∈ U n := by
          have hz' := Metric.edistOf_ball_subset_connCompOpen (g n) (x n).val (r n+1)
            (lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by linarith [(hr n).1])).mpr (by linarith)))
          change z ∈ connectedComponent (p n)
          change z ∈ connectedComponent (x n).val at hz'
          rwa [← connectedComponent_eq (x n).property] at hz'
        refine ⟨⟨z,hzC⟩,?_,rfl⟩
        change riemannianEDistOf (gc n) (x n) ⟨z,hzC⟩ ≤ ENNReal.ofReal (r n)
        rw [hdist]
        exact hz
    rw [← himg]
    exact (hcompactr n).image continuous_subtype_val
  · intro n z hz
    have hzC : z ∈ U n := by
      have hz' := Metric.edistOf_ball_subset_connCompOpen (g n) (x n).val (r n+1)
        (lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff (by linarith [(hr n).1])).mpr (by linarith)))
      change z ∈ connectedComponent (p n)
      change z ∈ connectedComponent (x n).val at hz'
      rwa [← connectedComponent_eq (x n).property] at hz'
    have hb := hbound n ⟨z,hzC⟩ (by
      change riemannianEDistOf (gc n) (x n) ⟨z,hzC⟩ ≤ ENNReal.ofReal (r n)
      rw [hdist]
      exact hz)
    rw [hdist,CheegerGromovCompactness.metricScalarAt_restrictOpen,
      CheegerGromovCompactness.metricScalarAt_restrictOpen] at hb
    exact hb

end DifferentialGeometry.Geometry.Curvature
