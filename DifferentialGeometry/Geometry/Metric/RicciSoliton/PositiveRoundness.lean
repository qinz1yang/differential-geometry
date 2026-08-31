import DifferentialGeometry.Geometry.Metric.RicciSoliton.CompactAnisotropy

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff

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
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem gradientRicciSoliton_constant_sectional_curvature_of_compact_of_finrank_eq_three_of_sectional_pos
    [CompactSpace M] [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {sigma : Real}
    (h : gradientRicciSoliton (I := I) g f sigma)
    (hdim : Module.finrank Real E = 3)
    (hsec : ∀ (x : M) (v w : TangentSpace I x),
      LinearIndependent Real (vec2 (I := I) v w) →
        0 < metricRm04StdAt (I := I) (M := M) g x v w w v) :
    ∀ (x : M) (v w : TangentSpace I x),
      metricRm04StdAt (I := I) (M := M) g x v w w v =
        (sigma / 4) *
          (g.inner x v v * g.inner x w w -
            g.inner x v w * g.inner x v w) := by
  cases isEmpty_or_nonempty M
  · intro x
    exact isEmptyElim x
  · have hdimAt (x : M) : Module.finrank Real (TangentSpace I x) = 3 := by
      rw [show Module.finrank Real (TangentSpace I x) = Module.finrank Real E from rfl]
      exact hdim
    have hscalar : ∀ x : M, 0 < metricScalarAt (I := I) (M := M) g x := by
      intro x
      exact metricScalarAt_pos_of_sectional_pos_of_finrank_eq_three
        (I := I) (M := M) g x (hdimAt x) (hsec x)
    have hdefect : ∀ x : M, ricciReactionDefectAt (I := I) g x = 0 :=
      gradientRicciSoliton_ricciReactionDefectAt_eq_zero_of_compact_of_finrank_eq_three
        (I := I) (M := M) h hscalar hdim
    have hEin : ∀ (x : M) (v w : TangentSpace I x),
        metricRicciAt (I := I) (M := M) g x (vec2 (I := I) v w) =
          (metricScalarAt (I := I) (M := M) g x / 3) * g.inner x v w := by
      intro x
      exact metricRicciAt_eq_scalar_div_three_of_ricciReactionDefectAt_eq_zero_of_sectional_pos
        (I := I) (M := M) g x (hdimAt x) (hdefect x) (hsec x)
    have hdScalar :
        ∀ x : M, ∀ X : TangentSpace I x,
          differential1FormFun (I := I)
              (fun y : M => metricScalarAt (I := I) (M := M) g y)
              x (fun _ : Fin 1 => X) = 0 := by
      intro x X
      obtain ⟨basis, _lambda, _mu, _nu, horth, _hdiag⟩ :=
        exists_orthonormal_curvature_eigenframe
          (I := I) (M := M) g x (hdimAt x)
      have hinv : MetricInverseInBasisGen (I := I) g x basis delta3 :=
        orthonormal_invBasis3 (I := I) g basis horth
      exact dScalar_zero_ein3_at (I := I) (M := M) g basis delta3 hinv hEin X
    obtain ⟨R0, hR0⟩ :=
      metricScalar_const_of_dScalar_zero (I := I) (M := M) g hdScalar
    let mu : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
    let _ : IsFiniteMeasure mu :=
      riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
    let _ : mu.IsOpenPosMeasure :=
      riemannianVolumeMeasure_isOpenPosMeasure (I := I) (M := M) g
    have hmuPos : 0 < mu.real univ := by
      apply ENNReal.toReal_pos
      · exact (isOpen_univ.measure_pos mu univ_nonempty).ne'
      · exact measure_ne_top mu univ
    have hf :
        (⟨fun x : M => f x, f.contMDiff⟩ : C^∞⟮I, M; Real⟯) = f := by
      ext x
      rfl
    have hlap :
        ∫ x, ΔG (I := I) g f x ∂mu = 0 := by
      simpa only [mu, hf] using
        laplacian_integral_eq_zero (I := I) (M := M) g f.contMDiff
    have hlapPoint (x : M) :
        ΔG (I := I) g f x = 3 * sigma / 2 - R0 := by
      have htrace := gradientRicciSoliton_trace (I := I) h x
      rw [hR0 x, hdim] at htrace
      norm_num at htrace ⊢
      linarith
    have hlapConst :
        ∫ x, ΔG (I := I) g f x ∂mu =
          mu.real univ * (3 * sigma / 2 - R0) := by
      calc
        ∫ x, ΔG (I := I) g f x ∂mu =
            ∫ _x : M, 3 * sigma / 2 - R0 ∂mu := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall hlapPoint
        _ = mu.real univ * (3 * sigma / 2 - R0) := by
          rw [MeasureTheory.integral_const, smul_eq_mul]
    have hR0sigma : R0 = 3 * sigma / 2 := by
      rw [hlap] at hlapConst
      nlinarith
    intro x v w
    calc
      metricRm04StdAt (I := I) (M := M) g x v w w v =
          (metricScalarAt (I := I) (M := M) g x / 6) *
            (g.inner x v v * g.inner x w w -
              g.inner x v w * g.inner x v w) :=
        metricRm04StdAt_eq_scalar_div_six_of_finrank_eq_three_of_einstein
          (I := I) (M := M) g x (hdimAt x) (hEin x) v w
      _ = (sigma / 4) *
            (g.inner x v v * g.inner x w w -
              g.inner x v w * g.inner x v w) := by
        rw [hR0 x, hR0sigma]
        ring

end DifferentialGeometry.Geometry
