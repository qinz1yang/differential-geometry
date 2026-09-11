import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CompleteTriangleEquality

set_option autoImplicit false
noncomputable section
open Bundle Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] [ConnectedSpace M]

theorem exists_intrinsicGeodesic_eq_metric_segment
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    {L : ℝ} (hL : 0 < L) (f : Icc (0 : ℝ) L → M)
    (hdist : ∀ s t, riemannianEDist I (f s) (f t) = ENNReal.ofReal |(s : ℝ) - t|) :
    ∃ u : TangentSpace I (f ⟨0, ⟨le_rfl, hL.le⟩⟩),
      g.inner _ u u = 1 ∧ ∀ s, f s = intrinsicGeodesic g hEnorm _ u s := by
  let zero : Icc (0 : ℝ) L := ⟨0, ⟨le_rfl, hL.le⟩⟩
  let r : ℝ := min (L / 2) (expDiffeoRadius g hEnorm (f zero) / 2)
  have hr : 0 < r := lt_min (half_pos hL) (half_pos (expDiffeoRadius_pos g hEnorm _))
  have hrL : r < L := (min_le_left _ _).trans_lt (half_lt_self hL)
  have hrExp : r < expDiffeoRadius g hEnorm (f zero) :=
    (min_le_right _ _).trans_lt (half_lt_self (expDiffeoRadius_pos g hEnorm _))
  let restrict (s : Icc (0 : ℝ) r) : Icc (0 : ℝ) L :=
    ⟨s, ⟨s.property.1, s.property.2.trans hrL.le⟩⟩
  obtain ⟨u, hu, heq⟩ := exists_intrinsicGeodesic_eq_short_metric_segment g hEnorm hr
    (fun s => f (restrict s)) hrExp (fun s t => hdist (restrict s) (restrict t))
  refine ⟨u, hu, ?_⟩
  intro s
  by_cases hsr : (s : ℝ) ≤ r
  · exact heq ⟨s, ⟨s.property.1, hsr⟩⟩
  · have hrs : r < (s : ℝ) := not_le.mp hsr
    let middle : Icc (0 : ℝ) L := ⟨r, ⟨hr.le, hrL.le⟩⟩
    have hmiddle : f middle = intrinsicGeodesic g hEnorm (f zero) u r :=
      heq ⟨r, ⟨hr.le, le_rfl⟩⟩
    have hfull : riemannianEDist I (f zero) (f s) =
        ENNReal.ofReal (r + ((s : ℝ) - r)) := by
      rw [hdist]
      congr 1
      change |(0 : ℝ) - s| = r + ((s : ℝ) - r)
      rw [zero_sub, abs_neg, abs_of_nonneg s.property.1]
      ring
    have hremaining : riemannianEDist I (intrinsicGeodesic g hEnorm (f zero) u r) (f s) =
        ENNReal.ofReal ((s : ℝ) - r) := by
      rw [← hmiddle, hdist]
      congr 1
      change |r - (s : ℝ)| = (s : ℝ) - r
      rw [abs_of_nonpos (sub_nonpos.mpr hrs.le)]
      ring
    have hcontinue := intrinsicGeodesic_continues_of_distance_add g hEnorm
      (f zero) (f s) u hu hr (sub_pos.mpr hrs) hfull hremaining
    simpa only [show r + ((s : ℝ) - r) = s by ring] using hcontinue.symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
