import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryShortSegment
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryGeodesicConcavity
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryHessianNeighborhood

/-!
Actual short minimum-length ambient geodesics between distinct points on the positive
side of a tangent-negative defining function stay strictly on that side at interior times.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  [ambientDimension : NeZero (Module.finrank ℝ E)]

omit ambientFinite ambientDimension in
attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
private theorem boundary_ambient_edist_separates
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) (a b : E)
    (hzero : riemannianEDistOf g a b = 0) : a = b := by
  let ambientMetric : RiemannianBundle (fun x : E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨g.toRiemannianMetric⟩
  let ambientContinuous : IsContinuousRiemannianBundle E
      (fun x : E => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun x v w => rfl⟩⟩
  let em : EMetricSpace E := EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) E
  apply em.eq_of_edist_eq_zero
  exact hzero

theorem exists_boundary_convex_segment (g : SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (u : E → ℝ) (hu : ContDiff ℝ ∞ u) (p : E) (hp : u p = 0) (O : Set E)
    (hO : IsOpen O) (hpO : p ∈ O)
    (hH : ∀ v : E, fderiv ℝ u p v = 0 → v ≠ 0 → abstractHessian g u p v v < 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ a ∈ riemannianClosedBallOf g p r,
      ∀ b ∈ riemannianClosedBallOf g p r, a ≠ b → 0 ≤ u a → 0 ≤ u b →
      ∃ γ : ℝ → E, γ 0 = a ∧ γ 1 = b ∧ ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ ∧
        (∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ O) ∧
        metricPathELength g γ 0 1 = riemannianEDistOf g a b ∧
        IsGeodesicOn g γ (Icc (0 : ℝ) 1) ∧ ∀ t ∈ Ioo (0 : ℝ) 1, 0 < u (γ t) := by
  obtain ⟨C, δ, hc, hδ, hnegative, hsign⟩ :=
    exists_boundary_defining_hessian_neighborhood g u hu p hp hH
  let F : E → ℝ := fun y => u y - C * (u y) ^ 2
  have hF : ContDiff ℝ ∞ F := hu.sub (contDiff_const.mul (hu.pow 2))
  obtain ⟨r, hr, hsegments⟩ := exists_boundary_short_segment g p (Metric.ball p δ ∩ O)
    (Metric.isOpen_ball.inter hO) ⟨Metric.mem_ball_self hδ, hpO⟩
  refine ⟨r, hr, ?_⟩
  intro a ha b hb hab hua hub
  obtain ⟨γ, hstart, hend, hsmooth, hmem, hlength, hgeo, hspeed⟩ := hsegments a ha b hb
  have hzero : riemannianEDistOf g a b ≠ 0 := fun hz =>
    hab (boundary_ambient_edist_separates g a b hz)
  change riemannianEDistOf g p a ≤ ENNReal.ofReal r at ha
  change riemannianEDistOf g p b ≤ ENNReal.ofReal r at hb
  have hap : riemannianEDistOf g a p ≤ ENNReal.ofReal r := by
    simpa only [riemannianEDistOf_comm g a p] using ha
  have hbound := (riemannianEDistOf_triangle g a p b).trans (add_le_add hap hb)
  have hfinite : riemannianEDistOf g a b ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.ofReal_ne_top⟩) hbound
  have hd : 0 < (riemannianEDistOf g a b).toReal := ENNReal.toReal_pos hzero hfinite
  have hvelocity (t : ℝ) : mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t 1 = deriv γ t := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ γ t 1 = deriv γ t
    exact fderiv_apply_one_eq_deriv
  have hvel : ∀ t ∈ Ioo (0 : ℝ) 1, deriv γ t ≠ 0 := by
    intro t ht hv
    let v : TangentSpace 𝓘(ℝ, E) (γ t) := mfderiv 𝓘(ℝ) 𝓘(ℝ, E) γ t 1
    have hvzero : v = 0 := (hvelocity t).trans hv
    have hnormzero : g.inner (γ t) v v = 0 := by
      rw [hvzero, map_zero]
    have hs := hspeed t (Ioo_subset_Icc_self ht)
    exact (ne_of_gt (sq_pos_of_pos hd)) (hs.symm.trans hnormzero)
  have hfirst : 0 ≤ F (γ 0) := (hsign (γ 0) (hmem 0 (by norm_num)).1).mpr
    (by simpa only [hstart] using hua)
  have hlast : 0 ≤ F (γ 1) := (hsign (γ 1) (hmem 1 (by norm_num)).1).mpr
    (by simpa only [hend] using hub)
  have hγ2 : ContDiffOn ℝ 2 γ (Ioo (0 : ℝ) 1) :=
    ((contMDiff_iff_contDiff.mp hsmooth).of_le (by simp)).contDiffOn
  have hpos := boundary_geodesic_pos g F hF γ 0 1 (by norm_num)
    hsmooth.continuous.continuousOn hγ2
    (fun t ht => hgeo t (Ioo_subset_Icc_self ht))
    (fun t ht v hv => hnegative (γ t) (hmem t (Ioo_subset_Icc_self ht)).1 v hv)
    hvel hfirst hlast
  refine ⟨γ, hstart, hend, hsmooth, fun t ht => (hmem t ht).2, hlength, hgeo, ?_⟩
  intro t ht
  exact (hpos t ht).trans_le (sub_le_self _ (mul_nonneg hc.le (sq_nonneg (u (γ t)))))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
