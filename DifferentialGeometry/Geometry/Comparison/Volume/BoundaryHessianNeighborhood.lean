import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryDefiningHessian
import DifferentialGeometry.Tensor.BilinearForm.Coordinates

/-!
An actual smooth ambient covariant Hessian negative definite at a point stays negative
definite on a neighborhood, using smooth dual covariant derivatives and tensor charts.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Connection

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]

private theorem boundary_ambient_hessian_continuous
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) (u : E → ℝ) (hu : ContDiff ℝ ∞ u) (p : E) :
    ContinuousAt (fun y : E =>
      ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun z : E => TangentSpace 𝓘(ℝ, E) z →L[ℝ]
          TangentSpace 𝓘(ℝ, E) z →L[ℝ] ℝ) p)
        ⟨y, abstractHessian g u y⟩).2) p := by
  let D := cotangentCov (LeviCivita g)
  let dualSmooth : CovariantDerivative.ContMDiffCovariantDerivative D ∞ := inferInstance
  have hdu := cotangentCov_mvfderiv_smooth (I := 𝓘(ℝ, E)) hu.contMDiff
  have hH : ContMDiff 𝓘(ℝ, E)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : E => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y
        (abstractHessian g u y)) := by
    apply contMDiffOn_univ.mp
    apply dualSmooth.contMDiff.contMDiff
    simpa only [ENat.coe_top_add_one] using hdu.contMDiffOn
  have hcoord := (contMDiffAt_section (IB := 𝓘(ℝ, E))
    (F := E →L[ℝ] E →L[ℝ] ℝ)
    (E := fun y : E => TangentSpace 𝓘(ℝ, E) y →L[ℝ]
      TangentSpace 𝓘(ℝ, E) y →L[ℝ] ℝ) p).mp (hH p)
  exact hcoord.continuousAt

theorem boundary_hessian_negative_neighborhood
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) (u : E → ℝ) (hu : ContDiff ℝ ∞ u) (p : E)
    (hneg : ∀ v : E, v ≠ 0 → abstractHessian g u p v v < 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball p r, ∀ v : E, v ≠ 0 →
      abstractHessian g u y v v < 0 := by
  let B : E → E →L[ℝ] E →L[ℝ] ℝ := fun y =>
    ((trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun z : E => TangentSpace 𝓘(ℝ, E) z →L[ℝ]
        TangentSpace 𝓘(ℝ, E) z →L[ℝ] ℝ) p) ⟨y, abstractHessian g u y⟩).2
  have hB (y : E) (v w : E) : B y v w = abstractHessian g u y v w := by
    have hy : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) p).baseSet := by
      simp [TangentBundle.trivializationAt_baseSet]
    dsimp only [B]
    rw [BilinearForm.trivializationAt_apply p hy,
      TangentBundle.symmL_model_space]
    rfl
  have hH : ContinuousAt (fun y => -B y) p :=
    (boundary_ambient_hessian_continuous g u hu p).neg
  have hp : -B p ∈
      {A : E →L[ℝ] E →L[ℝ] ℝ | ∀ v : E, v ≠ 0 → 0 < A v v} := by
    intro v hv
    simpa only [neg_apply, hB] using neg_pos.mpr (hneg v hv)
  have hnear := hH.eventually (Analysis.isOpen_pos_diagonal.mem_nhds hp)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨r, hr, fun y hy v hv => ?_⟩
  have hn := hball (by simpa only [Metric.mem_ball] using hy) v hv
  simpa only [neg_apply, neg_pos, hB] using hn

theorem exists_boundary_defining_hessian_neighborhood
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) E) (u : E → ℝ) (hu : ContDiff ℝ ∞ u)
    (p : E) (hp : u p = 0)
    (hneg : ∀ v : E, fderiv ℝ u p v = 0 → v ≠ 0 → abstractHessian g u p v v < 0) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧
      (∀ y ∈ Metric.ball p r, ∀ v : E, v ≠ 0 →
        abstractHessian g (fun z => u z - C * (u z) ^ 2) y v v < 0) ∧
      ∀ y ∈ Metric.ball p r, (0 ≤ u y - C * (u y) ^ 2 ↔ 0 ≤ u y) := by
  have hdu (v : TangentSpace 𝓘(ℝ, E) p) :
      mvfderiv 𝓘(ℝ, E) u p v = fderiv ℝ u p (v : E) := by
    unfold mvfderiv
    rw [mfderiv_eq_fderiv]
    rfl
  obtain ⟨C, hc, hH, hsign⟩ :=
    exists_boundary_defining_hessian_correction g u hu.contMDiff p hp (by
      intro v hz hv
      apply hneg v ?_ hv
      rw [← hdu v]
      exact hz)
  have hF : ContDiff ℝ ∞ (fun z => u z - C * (u z) ^ 2) :=
    hu.sub (contDiff_const.mul (hu.pow 2))
  obtain ⟨r, hr, hcollar⟩ := boundary_hessian_negative_neighborhood g
    (fun z => u z - C * (u z) ^ 2) hF p hH
  obtain ⟨δ, hδ, hδsign⟩ := Metric.eventually_nhds_iff.mp hsign
  refine ⟨C, min r δ, hc, lt_min hr hδ, ?_, ?_⟩
  · intro y hy v hv
    apply hcollar y ?_ v hv
    exact (Metric.mem_ball.mp hy).trans_le (min_le_left r δ)
  · intro y hy
    exact hδsign ((Metric.mem_ball.mp hy).trans_le (min_le_right r δ))

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
