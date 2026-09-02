import DifferentialGeometry.Topology.Morse.Riemannian
import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceIdentities
import DifferentialGeometry.Geometry.Operator.HessianExtrema

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator
open DifferentialGeometry.Topology.Morse

variable {E : Type} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [ConnectedSpace M]

theorem normalizedGradientRicciSoliton_isNondegenerateCriticalPointAt_of_finrank_eq_two_of_not_constant
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (x : M)
    (hcrit : IsCriticalPointAt I f x) :
    IsNondegenerateCriticalPointAt I f x := by
  apply isNondegenerateCriticalPointAt_of_hessFun_eq_smul_metric
    (c := (1 - metricScalarAt (I := I) (M := M) g x) / 2) g f x hcrit
  · intro hzero
    apply hnonconstant
    have hscalarx : metricScalarAt (I := I) (M := M) g x = 1 := by
      linarith
    have hgradx : gradFun (I := I) g f x = 0 :=
      gradFun_eq_zero_of_mfderiv_eq_zero (I := I) g f hcrit
    have hf :=
      normalizedGradientRicciSoliton_potential_eq_one_of_finrank_eq_two_of_scalar_eq_one_of_gradient_eq_zero
        (I := I) h hdim x hscalarx hgradx
    intro y z
    rw [hf y, hf z]
  · intro v w
    exact normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
      (I := I) h hdim x v w

theorem normalizedGradientRicciSoliton_metricScalarAt_lt_one_at_local_min_of_finrank_eq_two_of_not_constant
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (x : M)
    (hmin : IsLocalMin f x) :
    metricScalarAt (I := I) (M := M) g x < 1 := by
  have hgradx : gradFun (I := I) g f x = 0 := by
    exact gradientFun_eq_zero_of_isLocalMin (I := I) g hmin
      ((f.contMDiff x).mdifferentiableAt (by simp))
  have hscalarNe : metricScalarAt (I := I) (M := M) g x ≠ 1 := by
    intro hscalarx
    apply hnonconstant
    have hf :=
      normalizedGradientRicciSoliton_potential_eq_one_of_finrank_eq_two_of_scalar_eq_one_of_gradient_eq_zero
        (I := I) h hdim x hscalarx hgradx
    intro y z
    rw [hf y, hf z]
  have hfinrank : Module.finrank Real (TangentSpace I x) = 2 := by
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  let _ : Nontrivial (TangentSpace I x) :=
    Module.nontrivial_of_finrank_pos (by rw [hfinrank]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace I x)
  have hhess := hessFun_apply_self_nonneg_at_spatial_min
    (I := I) g hmin f.contMDiff v
  rw [normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
    (I := I) h hdim x v v] at hhess
  have hinner : 0 < g.inner x v v := g.pos x v hv
  have hle : metricScalarAt (I := I) (M := M) g x ≤ 1 := by
    nlinarith
  exact lt_of_le_of_ne hle hscalarNe

theorem normalizedGradientRicciSoliton_one_lt_metricScalarAt_at_local_max_of_finrank_eq_two_of_not_constant
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) (x : M)
    (hmax : IsLocalMax f x) :
    1 < metricScalarAt (I := I) (M := M) g x := by
  have hgradx : gradFun (I := I) g f x = 0 := by
    exact gradientFun_eq_zero_of_isLocalMax (I := I) g hmax
      ((f.contMDiff x).mdifferentiableAt (by simp))
  have hscalarNe : metricScalarAt (I := I) (M := M) g x ≠ 1 := by
    intro hscalarx
    apply hnonconstant
    have hf :=
      normalizedGradientRicciSoliton_potential_eq_one_of_finrank_eq_two_of_scalar_eq_one_of_gradient_eq_zero
        (I := I) h hdim x hscalarx hgradx
    intro y z
    rw [hf y, hf z]
  have hfinrank : Module.finrank Real (TangentSpace I x) = 2 := by
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  let _ : Nontrivial (TangentSpace I x) :=
    Module.nontrivial_of_finrank_pos (by rw [hfinrank]; norm_num)
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace I x)
  have hhess := hessFun_apply_self_nonpos_at_spatial_max
    (I := I) g hmax f.contMDiff v
  rw [normalizedGradientRicciSoliton_hessFun_of_finrank_eq_two
    (I := I) h hdim x v v] at hhess
  have hinner : 0 < g.inner x v v := g.pos x v hv
  have hle : 1 ≤ metricScalarAt (I := I) (M := M) g x := by
    nlinarith
  exact lt_of_le_of_ne hle hscalarNe.symm

theorem normalizedGradientRicciSoliton_exists_potential_extrema_with_scalar_lt_one_and_one_lt_of_compact_of_finrank_eq_two_of_not_constant
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2)
    (hnonconstant : ¬ ∀ y z : M, f y = f z) :
    ∃ xmin xmax : M,
      IsMinOn f univ xmin ∧ IsMaxOn f univ xmax ∧
      metricScalarAt (I := I) (M := M) g xmin < 1 ∧
      1 < metricScalarAt (I := I) (M := M) g xmax := by
  obtain ⟨xmin, _, hmin⟩ :=
    (isCompact_univ : IsCompact (univ : Set M)).exists_isMinOn
      univ_nonempty f.contMDiff.continuous.continuousOn
  obtain ⟨xmax, _, hmax⟩ :=
    (isCompact_univ : IsCompact (univ : Set M)).exists_isMaxOn
      univ_nonempty f.contMDiff.continuous.continuousOn
  refine ⟨xmin, xmax, hmin, hmax, ?_, ?_⟩
  · exact
      normalizedGradientRicciSoliton_metricScalarAt_lt_one_at_local_min_of_finrank_eq_two_of_not_constant
        (I := I) h hdim hnonconstant xmin (hmin.isLocalMin (by simp))
  · exact
      normalizedGradientRicciSoliton_one_lt_metricScalarAt_at_local_max_of_finrank_eq_two_of_not_constant
        (I := I) h hdim hnonconstant xmax (hmax.isLocalMax (by simp))

end DifferentialGeometry.Geometry
