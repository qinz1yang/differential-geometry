import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Rellich

noncomputable section

namespace DifferentialGeometry.Analysis.Laplacian

open Bundle MeasureTheory
open Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [CompactSpace M]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_tangentSectionAction_mul_exp_eq_zero_of_conformal_of_liouville
    (hn : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (u K : C^∞⟮I, M; Real⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : Geometry.IsConformalVectorField g X) {k : Real}
    (hK : ∀ x, ΔG g u x + K x * Real.exp (2 * u x) = k)
    (hdiv : ∀ x, ΔG g ⟨divergenceG g X, divergence_g_contMDiff g X⟩ x =
      -(2 * k) * divergenceG g X x) :
    (∫ x, tangentSectionAction X K x * Real.exp (2 * u x)
      ∂riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let d : C^∞⟮I, M; Real⟯ := ⟨divergenceG g X, divergence_g_contMDiff g X⟩
  let a := tangentSectionAction X u
  let L := ΔG g u
  let e : M → Real := fun x => Real.exp (2 * u x)
  let j : M → Real := fun x => tangentSectionAction X K x * e x
  have he : ContMDiff I 𝓘(Real) ∞ e :=
    Real.contDiff_exp.contMDiff.comp (contMDiff_const.mul u.contMDiff)
  have ha : Continuous a := (tangentSectionAction_contMDiff X u.contMDiff).continuous
  have hL : Continuous L := (Δ_g_contMDiff g u).continuous
  have hj : Continuous j := (tangentSectionAction_contMDiff X K.contMDiff).continuous.mul he.continuous
  have hi {f : M → Real} (hf : Continuous f) : Integrable f μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g hf
      (HasCompactSupport.of_compactSpace f)
  have heX (x : M) : tangentSectionAction X e x = 2 * e x * a x := by
    have hu := (u.contMDiff.mdifferentiableAt (by simp) :
      MDifferentiableAt I 𝓘(Real) (u : M → Real) x).hasMFDerivAt
    have htwo : HasMFDerivAt I 𝓘(Real) (fun y : M => 2 * u y) x
        ((2 : Real) • mfderiv I 𝓘(Real) u x) := hu.const_smul 2
    have hx := ((Real.hasDerivAt_exp (2 * u x)).hasFDerivAt.hasMFDerivAt.comp x htwo).mfderiv
    have happly := congrArg (fun F : TangentSpace I x →L[Real] Real => F (X x)) hx
    change tangentSectionAction X e x =
      (2 * tangentSectionAction X u x) * Real.exp (2 * u x) at happly
    dsimp only [e, a]
    rw [happly]
    ring
  have hprod := integral_tangentSectionAction_mul_add_eq_neg g K.contMDiff he X
    (HasCompactSupport.of_compactSpace X)
  have hleft : (∫ x, tangentSectionAction X K x * e x +
        K x * tangentSectionAction X e x ∂μ) =
      (∫ x, j x ∂μ) + 2 * k * (∫ x, a x ∂μ) - 2 * ∫ x, L x * a x ∂μ := by
    calc
      _ = ∫ x, (j x + 2 * k * a x) - 2 * (L x * a x) ∂μ := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun x => ?_
        dsimp only
        rw [heX]
        have hk : K x * e x = k - L x := by dsimp only [e, L]; linarith [hK x]
        calc
          tangentSectionAction X K x * e x + K x * (2 * e x * a x) =
              tangentSectionAction X K x * e x + 2 * (K x * e x) * a x := by ring
          _ = tangentSectionAction X K x * e x + 2 * (k - L x) * a x := by rw [hk]
          _ = j x + 2 * k * a x - 2 * (L x * a x) := by dsimp [j]; ring
      _ = _ := by
        have h₁ := integral_sub ((hi hj).add ((hi ha).const_mul (2 * k)))
          ((hi (hL.mul ha)).const_mul 2)
        have h₂ := integral_add (hi hj) ((hi ha).const_mul (2 * k))
        have h₁' : (∫ x, (j x + 2 * k * a x) - 2 * (L x * a x) ∂μ) =
            (∫ x, (j x + 2 * k * a x) ∂μ) - ∫ x, 2 * (L x * a x) ∂μ := by
          simpa only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] using h₁
        rw [h₁', h₂, integral_const_mul, integral_const_mul]
  have hright : (∫ x, K x * e x * divergenceG g X x ∂μ) =
      k * (∫ x, d x ∂μ) - ∫ x, L x * d x ∂μ := by
    calc
      _ = ∫ x, k * d x - L x * d x ∂μ := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun x => ?_
        dsimp only
        have hk : K x * e x = k - L x := by dsimp only [e, L]; linarith [hK x]
        rw [hk]
        change (k - L x) * d x = _
        ring
      _ = _ := by
        have h₁ := integral_sub ((hi d.contMDiff.continuous).const_mul k)
          (hi (hL.mul d.contMDiff.continuous))
        have h₁' : (∫ x, k * d x - L x * d x ∂μ) =
            (∫ x, k * d x ∂μ) - ∫ x, L x * d x ∂μ := by
          simpa only [Pi.sub_apply, Pi.mul_apply] using h₁
        rw [h₁', integral_const_mul]
  change (∫ x, tangentSectionAction X K x * e x +
    K x * tangentSectionAction X e x ∂μ) = -∫ x, K x * e x * divergenceG g X x ∂μ at hprod
  rw [hleft, hright] at hprod
  have hd : (∫ x, d x ∂μ) = 0 :=
    integral_divergence_eq_zero_of_hasCompactSupport g X (HasCompactSupport.of_compactSpace X)
  have hLa : (∫ x, L x * a x ∂μ) = 0 :=
    integral_laplacian_mul_tangentSectionAction_eq_zero_of_conformal_of_finrank_eq_two hn g u X hX
  have haint : (∫ x, a x ∂μ) = -∫ x, u x * d x ∂μ :=
    integral_tangentSectionAction_eq_neg_integral_smul_divergence g u.contMDiff X
      (HasCompactSupport.of_compactSpace X)
  have hgreen := green_second_integral_smul_laplacian_sub_eq_zero g u.contMDiff d.contMDiff
  change (∫ x, u x * ΔG g d x - d x * L x ∂μ) = 0 at hgreen
  have hgreen_eq : (∫ x, u x * ΔG g d x - d x * L x ∂μ) =
      -(2 * k) * (∫ x, u x * d x ∂μ) - ∫ x, L x * d x ∂μ := by
    calc
      _ = ∫ x, -(2 * k) * (u x * d x) - L x * d x ∂μ := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall fun x => ?_
        dsimp only
        have hx : ΔG g d x = -(2 * k) * d x := hdiv x
        rw [hx]
        ring
      _ = _ := by
        have h₁ := integral_sub
          ((hi (u.contMDiff.continuous.mul d.contMDiff.continuous)).const_mul (-(2 * k)))
          (hi (hL.mul d.contMDiff.continuous))
        have h₁' : (∫ x, (-(2 * k)) * (u x * d x) - L x * d x ∂μ) =
            (∫ x, (-(2 * k)) * (u x * d x) ∂μ) - ∫ x, L x * d x ∂μ := by
          simpa only [Pi.sub_apply, Pi.mul_apply] using h₁
        rw [h₁', integral_const_mul]
  rw [hgreen_eq] at hgreen
  rw [hd, hLa, haint] at hprod
  change (∫ x, j x ∂μ) = 0
  linarith

theorem tangentSectionAction_eq_zero_of_nonneg_of_conformal_of_liouville
    (hn : Module.finrank Real E = 2) (g : SmoothRiemannianMetric I M)
    (u K : C^∞⟮I, M; Real⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (hX : Geometry.IsConformalVectorField g X) {k : Real}
    (hK : ∀ x, ΔG g u x + K x * Real.exp (2 * u x) = k)
    (hdiv : ∀ x, ΔG g ⟨divergenceG g X, divergence_g_contMDiff g X⟩ x =
      -(2 * k) * divergenceG g X x)
    (hXK : ∀ x, 0 ≤ tangentSectionAction X K x) :
    tangentSectionAction X K = 0 := by
  let μ := riemannianVolumeMeasure (I := I) (M := M) g
  let f : M → Real := fun x => tangentSectionAction X K x * Real.exp (2 * u x)
  let : μ.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure g
  have hcont : Continuous f := (tangentSectionAction_contMDiff X K.contMDiff).continuous.mul
    (Real.continuous_exp.comp (continuous_const.mul u.contMDiff.continuous))
  have hint : Integrable f μ :=
    Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure g hcont
      (HasCompactSupport.of_compactSpace f)
  have hz : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg
    (fun x => mul_nonneg (hXK x) (Real.exp_pos _).le) hint).mp
      (integral_tangentSectionAction_mul_exp_eq_zero_of_conformal_of_liouville hn g u K X
        hX hK hdiv)
  have heq : f = 0 := μ.eq_of_ae_eq hz hcont continuous_const
  funext x
  exact (mul_eq_zero.mp (congrFun heq x)).resolve_right (Real.exp_ne_zero _)

end DifferentialGeometry.Analysis.Laplacian
