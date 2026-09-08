import DifferentialGeometry.Analysis.Integration.WeightedLaplacian
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Anisotropy

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M] [I.Boundaryless]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem gradientRicciSoliton_ricciReactionDefectAt_eq_zero_of_compact_of_finrank_eq_three
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    (hscalar : ∀ y : M, 0 < metricScalarAt (I := I) g y)
    (hdim : Module.finrank Real E = 3) :
    ∀ x : M, ricciReactionDefectAt (I := I) g x = 0 := by
  let _ : NeZero (Module.finrank Real E) := ⟨by rw [hdim]; norm_num⟩
  let R : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => metricScalarAt (I := I) g y,
      metricScalar_smooth (I := I) (M := M) g⟩
  let A : C^∞⟮I, M; Real⟯ := ricciAnisotropy (I := I) g hscalar
  let U : C^∞⟮I, M; Real⟯ := R * R
  let k : M → Real := fun y =>
    (U y * weightedLaplacian (I := I) g f A y +
      g.inner y (gradFun (I := I) g U y) (gradFun (I := I) g A y)) *
        Real.exp (-f y)
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  have hintegral : ∫ y, k y ∂μ = 0 := by
    simpa only [k, μ] using
      (integral_mul_weightedLaplacian_add_inner_grad_eq_zero_of_compact
        (I := I) (M := M) g f U A)
  let V : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := gradG (I := I) g A
  have hweighted : ContMDiff I (modelWithCornersSelf Real Real) ∞
      (weightedLaplacian (I := I) g f A) :=
    weightedLaplacian_contMDiff (I := I) g f A
  have hinner : ContMDiff I (modelWithCornersSelf Real Real) ∞
      (fun y : M =>
        g.inner y (gradFun (I := I) g U y) (gradFun (I := I) g A y)) := by
    have hact := tangentSectionAction_contMDiff (I := I) V U.contMDiff
    have heq : (fun y : M =>
        g.inner y (gradFun (I := I) g U y) (gradFun (I := I) g A y)) =
        tangentSectionAction (I := I) V U := by
      funext y
      rw [tangentSectionAction_eq_inner_grad_g (I := I) g U V y]
      simp only [V, grad_g_apply]
      exact g.symm y _ _
    rw [heq]
    exact hact
  have hkcont : Continuous k := by
    exact ((U.contMDiff.continuous.mul hweighted.continuous).add hinner.continuous).mul
      (Real.continuous_exp.comp f.contMDiff.continuous.neg)
  have hkint : Integrable k μ := by
    exact Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure
      (I := I) g hkcont (HasCompactSupport.of_compactSpace _)
  have hkformula (y : M) :
      k y =
        R y ^ 2 *
          (2 * R y ^ (-4 : Real) *
              normSq0S (I := I) g y 3 (ricciGradientCouplingAt (I := I) g y) +
            4 * R y ^ (-3 : Real) * ricciReactionDefectAt (I := I) g y) *
          Real.exp (-f y) := by
    have hRpos : 0 < R y := by
      change 0 < metricScalarAt (I := I) g y
      exact hscalar y
    have hidentity := gradientRicciSoliton_ricci_anisotropy_identity
      (I := I) (M := M) h hscalar y
    change weightedLaplacian (I := I) g f A y +
          2 * R y ^ (-1 : Real) *
            g.inner y (gradFun (I := I) g R y) (gradFun (I := I) g A y) =
        2 * R y ^ (-4 : Real) *
            normSq0S (I := I) g y 3 (ricciGradientCouplingAt (I := I) g y) +
          4 * R y ^ (-3 : Real) * ricciReactionDefectAt (I := I) g y at hidentity
    have hRdiff : MDifferentiableAt I (modelWithCornersSelf Real Real)
        (R : M → Real) y :=
      (R.contMDiff y).mdifferentiableAt (by simp)
    have hgradU :
        gradFun (I := I) g U y =
          (2 * R y) • gradFun (I := I) g R y := by
      change gradientFun (I := I) g (fun z : M => R z * R z) y = _
      simpa only [Connection.gradient_eq_gradFun] using
        (gradientFun_mul_self (I := I) g hRdiff)
    have hUval : U y = R y * R y := rfl
    dsimp only [k]
    rw [hUval, hgradU]
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [← hidentity, Real.rpow_neg_one]
    field_simp [hRpos.ne']
  have hknonneg : 0 ≤ k := by
    intro y
    rw [hkformula y]
    have hRpos : 0 < R y := by
      change 0 < metricScalarAt (I := I) g y
      exact hscalar y
    have hdimy : Module.finrank Real (TangentSpace I y) = 3 := by
      rw [show Module.finrank Real (TangentSpace I y) = Module.finrank Real E from rfl]
      exact hdim
    have hdefect : 0 ≤ ricciReactionDefectAt (I := I) g y :=
      ricciReactionDefectAt_nonneg_of_finrank_eq_three (I := I) (M := M) g y hdimy
    have hnorm :
        0 ≤ normSq0S (I := I) g y 3 (ricciGradientCouplingAt (I := I) g y) :=
      normSq0S_nonneg (I := I) g y 3 _
    have hm4 : 0 ≤ R y ^ (-4 : Real) := Real.rpow_nonneg hRpos.le _
    have hm3 : 0 ≤ R y ^ (-3 : Real) := Real.rpow_nonneg hRpos.le _
    positivity
  have hae : k =ᵐ[μ] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg hknonneg hkint).mp hintegral
  let _ : μ.IsOpenPosMeasure :=
    riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
  have heq : k = 0 := (Continuous.ae_eq_iff_eq μ hkcont continuous_const).mp hae
  intro x
  have hkzero : k x = 0 := congrFun heq x
  rw [hkformula x] at hkzero
  have hRpos : 0 < R x := by
    change 0 < metricScalarAt (I := I) g x
    exact hscalar x
  have hexp : 0 < Real.exp (-f x) := Real.exp_pos _
  have hsumzero :
      2 * R x ^ (-4 : Real) *
          normSq0S (I := I) g x 3 (ricciGradientCouplingAt (I := I) g x) +
        4 * R x ^ (-3 : Real) * ricciReactionDefectAt (I := I) g x = 0 := by
    rcases mul_eq_zero.mp hkzero with hleft | hexpzero
    · rcases mul_eq_zero.mp hleft with hRzero | hsum
      · exact False.elim ((pow_ne_zero 2 hRpos.ne') hRzero)
      · exact hsum
    · exact False.elim (hexp.ne' hexpzero)
  have hdimx : Module.finrank Real (TangentSpace I x) = 3 := by
    rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
    exact hdim
  have hdefect : 0 ≤ ricciReactionDefectAt (I := I) g x :=
    ricciReactionDefectAt_nonneg_of_finrank_eq_three (I := I) (M := M) g x hdimx
  have hnorm :
      0 ≤ normSq0S (I := I) g x 3 (ricciGradientCouplingAt (I := I) g x) :=
    normSq0S_nonneg (I := I) g x 3 _
  have hm4 : 0 ≤ R x ^ (-4 : Real) := Real.rpow_nonneg hRpos.le _
  have hfirst :
      0 ≤ 2 * R x ^ (-4 : Real) *
        normSq0S (I := I) g x 3 (ricciGradientCouplingAt (I := I) g x) := by
    positivity
  have hm3 : 0 ≤ R x ^ (-3 : Real) := Real.rpow_nonneg hRpos.le _
  have hsecond :
      0 ≤ 4 * R x ^ (-3 : Real) * ricciReactionDefectAt (I := I) g x := by
    positivity
  have hsecondzero :
      4 * R x ^ (-3 : Real) * ricciReactionDefectAt (I := I) g x = 0 := by
    nlinarith [hfirst, hsecond]
  have hcoefficient : 4 * R x ^ (-3 : Real) ≠ 0 := by
    positivity
  exact (mul_eq_zero.mp hsecondzero).resolve_left hcoefficient

end DifferentialGeometry.Geometry
