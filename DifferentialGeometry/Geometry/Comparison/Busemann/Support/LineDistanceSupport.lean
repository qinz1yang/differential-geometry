import DifferentialGeometry.Geometry.Comparison.Busemann.Support.SmoothDistanceLaplacian
import DifferentialGeometry.Geometry.Comparison.Busemann.Support.SupportHessianOrder

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology NNReal ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Topology

section Metric

variable {X : Type*} [MetricSpace X]

def lineDistanceSupport (eta : ℝ → X) (R : ℝ) (x : X) : ℝ :=
  R - dist x (eta R)

private theorem reverse_isometry {eta : ℝ → X} (heta : Isometry eta) :
    Isometry (fun t : ℝ => eta (-t)) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [heta.dist_eq, dist_neg_neg]


theorem lineDistanceSupport_mono {eta : ℝ → X} (heta : Isometry eta)
    {R S : ℝ} (hRS : R ≤ S) (x : X) :
    lineDistanceSupport eta R x ≤ lineDistanceSupport eta S x := by
  have h := dist_triangle x (eta R) (eta S)
  rw [heta.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hRS), neg_sub] at h
  dsimp only [lineDistanceSupport]
  linarith


theorem lineDistanceSupport_on_line {eta : ℝ → X} (heta : Isometry eta)
    {s R : ℝ} (hsR : s ≤ R) : lineDistanceSupport eta R (eta s) = s := by
  rw [lineDistanceSupport, heta.dist_eq, Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr hsR), neg_sub]
  ring


theorem lineDistanceSupport_reverse_on_line {eta : ℝ → X} (heta : Isometry eta)
    {s S : ℝ} (hsS : -s ≤ S) :
    lineDistanceSupport (fun t => eta (-t)) S (eta s) = -s := by
  have h := lineDistanceSupport_on_line (reverse_isometry heta) hsS
  simpa only [neg_neg] using h


theorem lineDistanceSupport_opposite_sum_nonpos {eta : ℝ → X} (heta : Isometry eta)
    {R S : ℝ} (hRS : 0 ≤ R + S) (x : X) :
    lineDistanceSupport eta R x + lineDistanceSupport (fun t => eta (-t)) S x ≤ 0 := by
  have h := dist_triangle (eta R) x (eta (-S))
  rw [heta.dist_eq, Real.dist_eq, sub_neg_eq_add, abs_of_nonneg hRS,
    dist_comm (eta R) x] at h
  change R - dist x (eta R) + (S - dist x (eta (-S))) ≤ 0
  linarith

end Metric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

private theorem shifted_line_isometry
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u)) (s : ℝ) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    Isometry (fun t : ℝ≥0 => intrinsicGeodesic (I := I) g hEnorm (eta s)
      (curveVelocity (I := I) eta s) (t : ℝ)) := by
  have hcont : (fun t => intrinsicGeodesic (I := I) g hEnorm p u (t + s)) =
      intrinsicGeodesic (I := I) g hEnorm (intrinsicGeodesic (I := I) g hEnorm p u s)
        (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm p u) s) := by
    with_unfolding_all exact intrinsicGeodesic_continuation (I := I) g hEnorm p u s
  apply Isometry.of_dist_eq
  intro a b
  rw [← hcont]
  change dist (intrinsicGeodesic (I := I) g hEnorm p u ((a : ℝ) + s))
    (intrinsicGeodesic (I := I) g hEnorm p u ((b : ℝ) + s)) = dist a b
  rw [hiso.dist_eq, dist_add_right]
  rfl

private theorem shifted_line_endpoint
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (s R : ℝ) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    intrinsicGeodesic (I := I) g hEnorm (eta s)
      (curveVelocity (I := I) eta s) (R - s) = eta R := by
  have hcont : (fun t => intrinsicGeodesic (I := I) g hEnorm p u (t + s)) =
      intrinsicGeodesic (I := I) g hEnorm (intrinsicGeodesic (I := I) g hEnorm p u s)
        (curveVelocity (I := I) (intrinsicGeodesic (I := I) g hEnorm p u) s) := by
    with_unfolding_all exact intrinsicGeodesic_continuation (I := I) g hEnorm p u s
  have h := congrFun hcont (R - s)
  simpa only [sub_add_cancel] using h.symm

private theorem intrinsic_reverse
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) :
    intrinsicGeodesic (I := I) g hEnorm p (-u) =
      fun t => intrinsicGeodesic (I := I) g hEnorm p u (-t) := by
  funext t
  simpa only [neg_one_smul, neg_one_mul] using
    intrinsicGeo_smul_apply (I := I) g hEnorm p u (-1) t

theorem exists_open_smooth_lineDistanceSupport
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (s R : ℝ) (hsR : s < R) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    ∃ U : Set M, IsOpen U ∧ eta s ∈ U ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (lineDistanceSupport eta R) U := by
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  have hv : g.inner (eta s) (curveVelocity (I := I) eta s)
      (curveVelocity (I := I) eta s) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u s).trans hu
  obtain ⟨U, hU, hq, hd⟩ := exists_open_smooth_dist_from_intrinsic_ray (I := I) g hEnorm
    (eta s) (curveVelocity (I := I) eta s) hv
    (shifted_line_isometry (I := I) g hEnorm p u hiso s) (R - s) (sub_pos.mpr hsR)
  rw [shifted_line_endpoint (I := I) g hEnorm p u s R] at hd
  exact ⟨U, hU, hq, contMDiffOn_const.sub hd⟩

theorem exists_open_smooth_reverse_lineDistanceSupport
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (s S : ℝ) (hsS : -s < S) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    ∃ U : Set M, IsOpen U ∧ eta s ∈ U ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (lineDistanceSupport (fun t => eta (-t)) S) U := by
  have hnegUnit : g.inner p (-u) (-u) = 1 := by
    simpa only [map_neg, neg_apply, neg_neg] using hu
  have hnegIso : Isometry (intrinsicGeodesic (I := I) g hEnorm p (-u)) := by
    rw [intrinsic_reverse (I := I) g hEnorm p u]
    exact reverse_isometry hiso
  have h := exists_open_smooth_lineDistanceSupport (I := I) g hEnorm p (-u)
    hnegUnit hnegIso (-s) S hsS
  simpa only [intrinsic_reverse (I := I) g hEnorm p u, neg_neg] using h

theorem lineDistanceSupport_laplacian_ge
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (s R : ℝ) (hsR : s < R) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u;
    -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (R - s)) ≤
      laplacian (I := I) (LeviCivita (I := I) g) g (lineDistanceSupport eta R) (eta s) := by
  let eta := intrinsicGeodesic (I := I) g hEnorm p u
  have hv : g.inner (eta s) (curveVelocity (I := I) eta s)
      (curveVelocity (I := I) eta s) = 1 :=
    (intrinsicGeodesic_speedSq_eq (I := I) g hEnorm p u s).trans hu
  have h := intrinsic_ray_support_laplacian_ge (I := I) g hEnorm hRic
    (eta s) (curveVelocity (I := I) eta s) hv
    (shifted_line_isometry (I := I) g hEnorm p u hiso s) s (R - s) (sub_pos.mpr hsR)
  have heq : (fun y => s + (R - s) - dist y
      (intrinsicGeodesic (I := I) g hEnorm (eta s) (curveVelocity (I := I) eta s) (R - s))) =
      lineDistanceSupport eta R := by
    funext y
    rw [shifted_line_endpoint (I := I) g hEnorm p u s R]
    dsimp only [lineDistanceSupport]
    ring
  rw [heq] at h
  exact h

theorem reverse_lineDistanceSupport_laplacian_ge
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (hRic : ∀ y : M, ∀ w : TangentSpace I y, 0 ≤ ricciTensor (I := I) g y w w)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (s S : ℝ) (hsS : -s < S) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u;
    -(((Module.finrank ℝ E - 1 : ℕ) : ℝ) / (S + s)) ≤
      laplacian (I := I) (LeviCivita (I := I) g) g
        (lineDistanceSupport (fun t => eta (-t)) S) (eta s) := by
  have hnegUnit : g.inner p (-u) (-u) = 1 := by
    simpa only [map_neg, neg_apply, neg_neg] using hu
  have hnegIso : Isometry (intrinsicGeodesic (I := I) g hEnorm p (-u)) := by
    rw [intrinsic_reverse (I := I) g hEnorm p u]
    exact reverse_isometry hiso
  have h := lineDistanceSupport_laplacian_ge (I := I) g hEnorm hRic p (-u)
    hnegUnit hnegIso (-s) S hsS
  simpa only [intrinsic_reverse (I := I) g hEnorm p u, neg_neg, sub_neg_eq_add] using h

theorem lineDistanceSupport_hessian_mono
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (s R S : ℝ) (hsR : s < R) (hRS : R ≤ S)
    (v : TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p u s)) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    hessFun (I := I) g (lineDistanceSupport eta R) (eta s) v v ≤
      hessFun (I := I) g (lineDistanceSupport eta S) (eta s) v v := by
  obtain ⟨U, hU, hpU, hf⟩ :=
    exists_open_smooth_lineDistanceSupport (I := I) g hEnorm p u hu hiso s R hsR
  obtain ⟨V, hV, hpV, hh⟩ :=
    exists_open_smooth_lineDistanceSupport (I := I) g hEnorm p u hu hiso s S (hsR.trans_le hRS)
  apply hessFun_le_of_smooth_upper_support (I := I) g hEnorm (hU.inter hV)
    (hf.mono inter_subset_left) (hh.mono inter_subset_right) ⟨hpU, hpV⟩
  · rw [lineDistanceSupport_on_line hiso hsR.le,
      lineDistanceSupport_on_line hiso (hsR.le.trans hRS)]
  · exact Eventually.of_forall (lineDistanceSupport_mono hiso hRS)

theorem reverse_lineDistanceSupport_hessian_mono
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (s R S : ℝ) (hsR : -s < R) (hRS : R ≤ S)
    (v : TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p u s)) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    hessFun (I := I) g (lineDistanceSupport (fun t => eta (-t)) R) (eta s) v v ≤
      hessFun (I := I) g (lineDistanceSupport (fun t => eta (-t)) S) (eta s) v v := by
  have hnegUnit : g.inner p (-u) (-u) = 1 := by
    simpa only [map_neg, neg_apply, neg_neg] using hu
  have hnegIso : Isometry (intrinsicGeodesic (I := I) g hEnorm p (-u)) := by
    rw [intrinsic_reverse (I := I) g hEnorm p u]
    exact reverse_isometry hiso
  have h := lineDistanceSupport_hessian_mono (I := I) g hEnorm p (-u)
    hnegUnit hnegIso (-s) R S hsR hRS v
  have hpoint : intrinsicGeodesic (I := I) g hEnorm p (-u) (-s) =
      intrinsicGeodesic (I := I) g hEnorm p u s := by
    simpa only [neg_neg] using congrFun (intrinsic_reverse (I := I) g hEnorm p u) (-s)
  change hessFun (I := I) g
      (lineDistanceSupport (intrinsicGeodesic (I := I) g hEnorm p (-u)) R)
      (intrinsicGeodesic (I := I) g hEnorm p (-u) (-s)) (v : E) (v : E) ≤
    hessFun (I := I) g
      (lineDistanceSupport (intrinsicGeodesic (I := I) g hEnorm p (-u)) S)
      (intrinsicGeodesic (I := I) g hEnorm p (-u) (-s)) (v : E) (v : E) at h
  rw [hpoint] at h
  simpa only [intrinsic_reverse (I := I) g hEnorm p u, neg_neg] using h

theorem lineDistanceSupport_opposite_hessian_nonpos
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (u : TangentSpace I p) (hu : g.inner p u u = 1)
    (hiso : Isometry (intrinsicGeodesic (I := I) g hEnorm p u))
    (s R S : ℝ) (hsR : s < R) (hsS : -s < S)
    (v : TangentSpace I (intrinsicGeodesic (I := I) g hEnorm p u s)) :
    let eta := intrinsicGeodesic (I := I) g hEnorm p u
    hessFun (I := I) g (lineDistanceSupport eta R) (eta s) v v +
      hessFun (I := I) g (lineDistanceSupport (fun t => eta (-t)) S) (eta s) v v ≤ 0 := by
  obtain ⟨U, hU, hpU, hf⟩ :=
    exists_open_smooth_lineDistanceSupport (I := I) g hEnorm p u hu hiso s R hsR
  obtain ⟨V, hV, hpV, hh⟩ :=
    exists_open_smooth_reverse_lineDistanceSupport (I := I) g hEnorm p u hu hiso s S hsS
  apply hessFun_add_nonpos_of_zero_contact (I := I) g hEnorm (hU.inter hV)
    (hf.mono inter_subset_left) (hh.mono inter_subset_right) ⟨hpU, hpV⟩
  · rw [lineDistanceSupport_on_line hiso hsR.le,
      lineDistanceSupport_reverse_on_line hiso hsS.le, add_neg_cancel]
  · have hRS : 0 ≤ R + S := by linarith
    exact Eventually.of_forall (lineDistanceSupport_opposite_sum_nonpos hiso hRS)

end DifferentialGeometry.Geometry.Topology

end
