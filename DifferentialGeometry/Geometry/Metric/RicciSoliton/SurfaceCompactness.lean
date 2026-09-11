import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Compactness
import DifferentialGeometry.Geometry.Metric.RicciSoliton.GaussianRigidity
import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceIdentities

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [ConnectedSpace M]

theorem normalizedGradientRicciSoliton_compactSpace_of_finrank_eq_two_of_not_isGaussian
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnot : ¬ isGaussianGradientRicciSoliton (E := E) g f 1) :
    CompactSpace M := by
  let _ : NeZero (Module.finrank Real E) := ⟨by omega⟩
  obtain ⟨c, hc⟩ :=
    normalizedGradientRicciSoliton_exists_scalar_eq_const_mul_exp_of_finrank_eq_two
      (I := I) h hdim
  have hscalar : ∀ x : M, 0 < metricScalarAt (I := I) (M := M) g x :=
    normalizedGradientRicciSoliton_scalar_pos_of_not_isGaussian (I := I) h hnot
  have hpotential : ∀ x : M, 0 < f x :=
    normalizedGradientRicciSoliton_potential_pos_of_not_isGaussian (I := I) h hnot
  have hcpos : 0 < c := by
    let x : M := Classical.arbitrary M
    have hx := hscalar x
    rw [hc x] at hx
    rcases (mul_pos_iff.mp hx) with hpos | hneg
    · exact hpos.1
    · exact False.elim (not_lt_of_ge (Real.exp_pos (f x)).le hneg.2)
  have hRic : Riemannian.BonnetMyers.RicciBoundedBelow (I := I) g
      (((Module.finrank Real E : Real) - 1) * (c / 2)) := by
    intro x v
    rw [hdim]
    norm_num
    rw [ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two
      (I := I) g hdim x v v, hc x]
    have hexp : 1 ≤ Real.exp (f x) := Real.one_le_exp (hpotential x).le
    have hcoef : c / 2 ≤ c * Real.exp (f x) / 2 := by
      nlinarith
    have hinner : 0 ≤ g.inner x v v := by
      by_cases hv : v = 0
      · subst v
        simp
      · exact (g.pos x v hv).le
    exact mul_le_mul_of_nonneg_right hcoef hinner
  exact Riemannian.BonnetMyers.bonnet_myers_compactSpace_of_complete_metric
    (I := I) g h.1 (by omega) (by positivity) hRic

theorem gradientRicciSoliton_compactSpace_of_finrank_eq_two_of_not_isGaussian
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {sigma : Real}
    (hdim : Module.finrank Real E = 2)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma)
    (hnot : ¬ isGaussianGradientRicciSoliton (E := E) g f sigma) :
    CompactSpace M := by
  let _ : NeZero (Module.finrank Real E) := ⟨by omega⟩
  obtain ⟨C, hnormalized⟩ :=
    gradientRicciSoliton_exists_normalized (I := I) hcomplete hsol hsigma
  let gHat : SmoothRiemannianMetric I M := scaleMetric (I := I) sigma hsigma g
  let fHat : C^∞⟮I, M; Real⟯ := f + ContMDiffMap.const (C / sigma)
  have hnotHat : ¬ isGaussianGradientRicciSoliton (E := E) gHat fHat 1 := by
    intro hGaussian
    have hGaussianMetric : isGaussianGradientRicciSoliton (E := E) gHat f 1 :=
      (isGaussianGradientRicciSoliton_add_const (I := I) (g := gHat)
        (f := f) (σ := 1) (C / sigma)).mp hGaussian
    exact hnot
      ((isGaussianGradientRicciSoliton_scaleMetric (I := I) hsigma).mp
        hGaussianMetric)
  exact normalizedGradientRicciSoliton_compactSpace_of_finrank_eq_two_of_not_isGaussian
    (I := I) hnormalized hdim hnotHat

end DifferentialGeometry.Geometry
