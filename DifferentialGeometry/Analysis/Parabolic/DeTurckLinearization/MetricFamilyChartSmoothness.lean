import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.JointSmoothness
import DifferentialGeometry.Analysis.Parabolic.DeTurckLinearization.MetricFamilyChartLinearization

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

noncomputable section

open Set Function
open scoped ContDiff Manifold BigOperators

namespace DifferentialGeometry.PDE.DeTurck.DeTurckLinearization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (gfam : ℝ → SmoothRiemannianMetric I M) (α : M)

omit [NeZero (Module.finrank ℝ E)] in
lemma chartDeTurckVFComp_joint_contDiffAt {S : Set ℝ}
    (hG : chartGramFamilyJointSmoothOn (I := I) gfam α S)
    (g_bg : SmoothRiemannianMetric I M) (k : Fin (Module.finrank ℝ E))
    {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k r.2) (s₀, y₀) := by
  have hbg : ∀ a b : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞
        (fun r : ℝ × E => chartChristoffel (I := I) g_bg α a b k r.2) (s₀, y₀) := by
    intro a b
    have hbase : ContDiffAt ℝ ∞ (chartChristoffel (I := I) g_bg α a b k) y₀ :=
      (chartChristoffel_contDiffOn_interior (I := I) g_bg α a b k).contDiffAt
        (isOpen_interior.mem_nhds hy)
    have hcomp : (fun r : ℝ × E => chartChristoffel (I := I) g_bg α a b k r.2) =
        (chartChristoffel (I := I) g_bg α a b k) ∘ (fun r : ℝ × E => r.2) := rfl
    rw [hcomp]
    exact ContDiffAt.comp (s₀, y₀) hbase contDiffAt_snd
  have heq : (fun r : ℝ × E => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k r.2) =
      (fun r : ℝ × E => ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        chartInvGramOnE (I := I) (gfam r.1) α a b r.2 *
          (chartChristoffel (I := I) (gfam r.1) α a b k r.2 -
            chartChristoffel (I := I) g_bg α a b k r.2)) := by
    funext r; rw [chartDeTurckVFComp_def]
  rw [heq]
  refine ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ => ?_))
  exact (chartInvGramOnE_joint_contDiffAt (I := I) gfam α hG a b hs hy).mul
    ((chartChristoffel_joint_contDiffAt (I := I) gfam α hG a b k hs hy).sub (hbg a b))

omit [NeZero (Module.finrank ℝ E)] in
lemma partial_chartDeTurckVFComp_joint_contDiffAt {S : Set ℝ}
    (hG : chartGramFamilyJointSmoothOn (I := I) gfam α S)
    (g_bg : SmoothRiemannianMetric I M) (m k : Fin (Module.finrank ℝ E))
    {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E =>
        DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) m (fun y => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k y) r.2)
      (s₀, y₀) :=
  partialDeriv_joint_contDiffAt (fun s y => chartDeTurckVFComp (I := I) (gfam s) g_bg α k y) m
    (chartDeTurckVFComp_joint_contDiffAt (I := I) gfam α hG g_bg k hs hy)

omit [NeZero (Module.finrank ℝ E)] in
lemma chartLieDeTurckComp_joint_contDiffAt {S : Set ℝ}
    (hG : chartGramFamilyJointSmoothOn (I := I) gfam α S)
    (g_bg : SmoothRiemannianMetric I M) (i j : Fin (Module.finrank ℝ E))
    {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartLieDeTurckComp (I := I) (gfam r.1) g_bg α i j r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartLieDeTurckComp (I := I) (gfam r.1) g_bg α i j r.2) =
      (fun r : ℝ × E =>
        (∑ k : Fin (Module.finrank ℝ E),
            chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k r.2 *
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) k (fun y => chartGramOnE (I := I) (gfam r.1) α i j y) r.2)
        + (∑ k : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) (gfam r.1) α k j r.2 *
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) i
                (fun y => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k y) r.2)
        + (∑ k : Fin (Module.finrank ℝ E),
            chartGramOnE (I := I) (gfam r.1) α i k r.2 *
              DifferentialGeometry.Tensor.Coordinates.partialDeriv (E := E) j
                (fun y => chartDeTurckVFComp (I := I) (gfam r.1) g_bg α k y) r.2)) := by
    funext r; rw [chartLieDeTurckComp_def]
  rw [heq]
  refine ((ContDiffAt.sum (fun k _ => ?_)).add (ContDiffAt.sum (fun k _ => ?_))).add
    (ContDiffAt.sum (fun k _ => ?_))
  · exact (chartDeTurckVFComp_joint_contDiffAt (I := I) gfam α hG g_bg k hs hy).mul
      (partialDeriv_joint_contDiffAt (fun s y => chartGramOnE (I := I) (gfam s) α i j y) k
        (hG i j hs hy))
  · exact (hG k j hs hy).mul
      (partial_chartDeTurckVFComp_joint_contDiffAt (I := I) gfam α hG g_bg i k hs hy)
  · exact (hG i k hs hy).mul
      (partial_chartDeTurckVFComp_joint_contDiffAt (I := I) gfam α hG g_bg j k hs hy)

omit [NeZero (Module.finrank ℝ E)] in
lemma chartDeTurckRicciRHS_joint_contDiffAt {S : Set ℝ}
    (hG : chartGramFamilyJointSmoothOn (I := I) gfam α S)
    (g_bg : SmoothRiemannianMetric I M) (i k : Fin (Module.finrank ℝ E))
    {s₀ : ℝ} {y₀ : E} (hs : s₀ ∈ S)
    (hy : y₀ ∈ interior (extChartAt I α).target) :
    ContDiffAt ℝ ∞
      (fun r : ℝ × E => chartDeTurckRicciRHS (I := I) (gfam r.1) g_bg α i k r.2) (s₀, y₀) := by
  have heq : (fun r : ℝ × E => chartDeTurckRicciRHS (I := I) (gfam r.1) g_bg α i k r.2) =
      (fun r : ℝ × E => -2 * chartRicciTensor (I := I) (gfam r.1) α i k r.2 +
        chartLieDeTurckComp (I := I) (gfam r.1) g_bg α i k r.2) := by
    funext r; rw [chartDeTurckRicciRHS_def]
  rw [heq]
  exact (contDiffAt_const.mul (chartRicciTensor_joint_contDiffAt (I := I) gfam α hG i k hs hy)).add
    (chartLieDeTurckComp_joint_contDiffAt (I := I) gfam α hG g_bg i k hs hy)

end DifferentialGeometry.PDE.DeTurck.DeTurckLinearization
