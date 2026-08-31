import DifferentialGeometry.Geometry.Curvature.Bochner.ScalarBochner
import DifferentialGeometry.Geometry.Metric.RicciSoliton.WeightedRicci
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian.Product

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff BigOperators

namespace DifferentialGeometry.Geometry

open Connection Curvature Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
    [SigmaCompactSpace M] [T2Space M] [I.Boundaryless] [IsManifold I ∞ M] in
private theorem contMDiff_rpow_of_pos
    {u : C^∞⟮I, M; Real⟯} {p : Real} (hpos : ∀ y : M, 0 < u y) :
    ContMDiff I 𝓘(Real, Real) ∞ (fun y : M => u y ^ p) := by
  intro y
  exact (Real.contDiffAt_rpow_const_of_ne (p := p) (hpos y).ne').comp_contMDiffAt
    u.contMDiff.contMDiffAt

noncomputable def ricciNormSqScalarRatio
    (g : SmoothRiemannianMetric I M)
    (hscalar : ∀ y : M, 0 < metricScalarAt (I := I) g y) :
    C^∞⟮I, M; Real⟯ :=
  let Ric := metricRicci (I := I) (M := M) g
  let R : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => metricScalarAt (I := I) g y,
      metricScalar_smooth (I := I) (M := M) g⟩
  ⟨fun y : M => normSq0S (I := I) g y 2 (Ric y) * R y ^ (-2 : Real),
    (normSq0S_smooth (I := I) g Ric).mul
      (contMDiff_rpow_of_pos (I := I) hscalar)⟩

noncomputable def ricciAnisotropy
    (g : SmoothRiemannianMetric I M)
    (hscalar : ∀ y : M, 0 < metricScalarAt (I := I) g y) :
    C^∞⟮I, M; Real⟯ :=
  ricciNormSqScalarRatio (I := I) g hscalar -
    ContMDiffMap.const (Module.finrank Real E : Real)⁻¹

noncomputable def ricciGradientCouplingAt
    (g : SmoothRiemannianMetric I M) (x : M) :
    Tensor0SSpace (𝕜 := Real) (E := E) (H := H) (I := I) 3 x :=
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let Ric := metricRicci (I := I) (M := M) g
  let nablaRic := totalNabla0S (I := I) 2 cov Ric
    (totalNabla0S_reg (I := I) 2 cov hcov Ric)
  metricScalarAt (I := I) g x • nablaRic x -
    Tensor0SSpace.product
      (differential1FormFun (I := I)
        (fun y : M => metricScalarAt (I := I) g y) x)
      (Ric x)

noncomputable def ricciReactionDefectAt
    (g : SmoothRiemannianMetric I M) (x : M) : Real :=
  let Ric := metricRicci (I := I) (M := M) g
  normSq0S (I := I) g x 2 (Ric x) ^ 2 -
    metricScalarAt (I := I) g x *
      inner0S (I := I) g x 2
        (curvatureRicciContractionAt (I := I) (M := M) g x) (Ric x)

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] [I.Boundaryless] in
private theorem two_mul_inner_nablaRic_product_dscalar_eq_gradient_inner
    (g : SmoothRiemannianMetric I M) (x : M) :
    let cov := LeviCivita (I := I) g
    let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
      simpa [cov, LeviCivita] using
        (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
          (I := I) (M := M) g)
    let Ric := metricRicci (I := I) (M := M) g
    let nablaRic := totalNabla0S (I := I) 2 cov Ric
      (totalNabla0S_reg (I := I) 2 cov hcov Ric)
    let R : C^∞⟮I, M; Real⟯ :=
      ⟨fun y : M => metricScalarAt (I := I) g y,
        metricScalar_smooth (I := I) (M := M) g⟩
    let S : C^∞⟮I, M; Real⟯ :=
      ⟨fun y : M => normSq0S (I := I) g y 2 (Ric y),
        normSq0S_smooth (I := I) g Ric⟩
    2 * inner0S (I := I) g x 3 (nablaRic x)
        (Tensor0SSpace.product
          (differential1FormFun (I := I) R x) (Ric x)) =
      g.inner x (gradFun (I := I) g S x) (gradFun (I := I) g R x) := by
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let Ric := metricRicci (I := I) (M := M) g
  let nablaRic := totalNabla0S (I := I) 2 cov Ric
    (totalNabla0S_reg (I := I) 2 cov hcov Ric)
  let R : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => metricScalarAt (I := I) g y,
      metricScalar_smooth (I := I) (M := M) g⟩
  let S : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => normSq0S (I := I) g y 2 (Ric y),
      normSq0S_smooth (I := I) g Ric⟩
  let duS := duSec (I := I) S S.contMDiff
  let W := gradFun (I := I) g R x
  obtain ⟨mu, basis, hinv, _, _, _⟩ :=
    exists_diagInv_of_equiv (I := I) g g x (C := 1) (by norm_num)
      (by intro v; simp)
  have hcontract :
      inner0S (I := I) g x 3 (nablaRic x)
          (Tensor0SSpace.product
            (differential1FormFun (I := I) R x) (Ric x)) =
        inner0S (I := I) g x 2
          ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 2 x
            (nablaRic x)) W) (Ric x) := by
    rw [inner0S_three_product_right (I := I) g x basis identityInvMetric hinv]
    rw [cotangentSharp_differential1FormFun_eq_gradientFun,
      Connection.gradient_eq_gradFun]
  have hmc : IsMetricCompatibleGen (I := I) cov g := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_isMetricCompatible (I := I) g)
  have hRic : TotalNabla0SRealizes (I := I) 2 cov Ric nablaRic :=
    totalNabla0S_realizes (I := I) 2 cov Ric _
  have hdu : DuFieldRealizes (I := I) S duS :=
    duSec_realizes (I := I) S S.contMDiff
  have hnorm := du_norm0S (I := I) cov g hmc Ric nablaRic hRic duS hdu W
  calc
    2 * inner0S (I := I) g x 3 (nablaRic x)
          (Tensor0SSpace.product
            (differential1FormFun (I := I) R x) (Ric x)) =
        2 * inner0S (I := I) g x 2
          ((tensor0SCurry (I := I) (𝕜 := Real) (M := M) 2 x
            (nablaRic x)) W) (Ric x) := by rw [hcontract]
    _ = duS x (fun _ : Fin 1 => W) := hnorm.symm
    _ = g.inner x (gradFun (I := I) g S x) W := by
      rw [duSec_apply]
      exact differential1FormFun_apply_eq_inner_gradientFun (I := I) g S x W
    _ = g.inner x (gradFun (I := I) g S x)
        (gradFun (I := I) g R x) := rfl

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem gradientRicciSoliton_ricci_norm_sq_scalar_ratio_identity
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    (hscalar : ∀ y : M, 0 < metricScalarAt (I := I) g y) (x : M) :
    let R : C^∞⟮I, M; Real⟯ :=
      ⟨fun y : M => metricScalarAt (I := I) g y,
        metricScalar_smooth (I := I) (M := M) g⟩
    weightedLaplacian (I := I) g f
          (ricciNormSqScalarRatio (I := I) g hscalar) x +
        2 * R x ^ (-1 : Real) *
          g.inner x (gradFun (I := I) g R x)
            (gradFun (I := I) g
              (ricciNormSqScalarRatio (I := I) g hscalar) x) =
      2 * R x ^ (-4 : Real) *
          normSq0S (I := I) g x 3 (ricciGradientCouplingAt (I := I) g x) +
        4 * R x ^ (-3 : Real) * ricciReactionDefectAt (I := I) g x := by
  let cov := LeviCivita (I := I) g
  let hcov : CovariantDerivative.ContMDiffCovariantDerivativeLocally cov ∞ := by
    simpa [cov, LeviCivita] using
      (leviCivitaConnectionOfMetric_contMDiffCovariantDerivativeLocally
        (I := I) (M := M) g)
  let Ric := metricRicci (I := I) (M := M) g
  let nablaRic := totalNabla0S (I := I) 2 cov Ric
    (totalNabla0S_reg (I := I) 2 cov hcov Ric)
  let R : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => metricScalarAt (I := I) g y,
      metricScalar_smooth (I := I) (M := M) g⟩
  let S : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => normSq0S (I := I) g y 2 (Ric y),
      normSq0S_smooth (I := I) g Ric⟩
  let RInvSq : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => R y ^ (-2 : Real),
      contMDiff_rpow_of_pos (I := I) hscalar⟩
  let Q : C^∞⟮I, M; Real⟯ := S * RInvSq
  have hRpos : 0 < R x := by
    simpa [R] using hscalar x
  have hSval : S x = normSq0S (I := I) g x 2 (Ric x) := rfl
  have hRInvSqVal : RInvSq x = R x ^ (-2 : Real) := rfl
  have hQ : Q = ricciNormSqScalarRatio (I := I) g hscalar := by
    ext y
    rfl
  rw [← hQ]
  change weightedLaplacian (I := I) g f Q x +
        2 * R x ^ (-1 : Real) *
          g.inner x (gradFun (I := I) g R x) (gradFun (I := I) g Q x) =
      2 * R x ^ (-4 : Real) *
          normSq0S (I := I) g x 3
            (R x • nablaRic x -
              Tensor0SSpace.product
                (differential1FormFun (I := I) R x) (Ric x)) +
        4 * R x ^ (-3 : Real) *
          (S x ^ 2 - R x *
            inner0S (I := I) g x 2
              (curvatureRicciContractionAt (I := I) (M := M) g x) (Ric x))
  have hquot := weightedLaplacian_mul_inv_sq
    (I := I) g f S R hscalar x
  change weightedLaplacian (I := I) g f Q x = _ at hquot
  have hS := gradientRicciSoliton_weightedLaplacian_ricci_norm_sq
    (I := I) (M := M) h x
  have hS' :
      weightedLaplacian (I := I) g f S x =
        2 * σ * S x -
          4 * inner0S (I := I) g x 2
            (curvatureRicciContractionAt (I := I) (M := M) g x) (Ric x) +
          2 * normSq0S (I := I) g x 3 (nablaRic x) := by
    simpa [cov, hcov, Ric, nablaRic, S] using hS
  have hR := gradientRicciSoliton_weightedLaplacian_scalar
    (I := I) h x
  have hR' :
      weightedLaplacian (I := I) g f R x =
        σ * R x - 2 * S x := by
    simpa [R, S, Ric] using hR
  rw [hS', hR'] at hquot
  have hRdiff : MDifferentiableAt I 𝓘(Real, Real) (R : M → Real) x :=
    (R.contMDiff x).mdifferentiableAt (by simp)
  have hSdiff : MDifferentiableAt I 𝓘(Real, Real) (S : M → Real) x :=
    (S.contMDiff x).mdifferentiableAt (by simp)
  have hRInvDiff :
      MDifferentiableAt I 𝓘(Real, Real) (RInvSq : M → Real) x :=
    (RInvSq.contMDiff x).mdifferentiableAt (by simp)
  have hgradInv :
      gradFun (I := I) g RInvSq x =
        (-2 * R x ^ (-3 : Real)) • gradFun (I := I) g R x := by
    change gradientFun (I := I) g (fun y : M => R y ^ (-2 : Real)) x = _
    have hp := gradientFun_rpow (I := I) g (-2 : Real) hRdiff (hscalar x)
    rw [show (-2 : Real) - 1 = -3 by ring] at hp
    simpa only [Connection.gradient_eq_gradFun] using hp
  have hgradQ :
      gradFun (I := I) g Q x =
        S x • gradFun (I := I) g RInvSq x +
          R x ^ (-2 : Real) • gradFun (I := I) g S x := by
    change gradientFun (I := I) g
      (fun y : M => S y * RInvSq y) x = _
    have hmul := gradientFun_mul (I := I) g hSdiff hRInvDiff
    simpa only [Connection.gradient_eq_gradFun, hRInvSqVal] using hmul
  have hinnerSymm :
      g.inner x (gradFun (I := I) g R x) (gradFun (I := I) g S x) =
        g.inner x (gradFun (I := I) g S x) (gradFun (I := I) g R x) :=
    g.symm x _ _
  have hm1m2 :
      R x ^ (-1 : Real) * R x ^ (-2 : Real) = R x ^ (-3 : Real) := by
    rw [← Real.rpow_add hRpos]
    norm_num
  have hm1m3 :
      R x ^ (-1 : Real) * R x ^ (-3 : Real) = R x ^ (-4 : Real) := by
    rw [← Real.rpow_add hRpos]
    norm_num
  have hdrift :
      2 * R x ^ (-1 : Real) *
          g.inner x (gradFun (I := I) g R x) (gradFun (I := I) g Q x) =
        -4 * S x * R x ^ (-4 : Real) *
            g.inner x (gradFun (I := I) g R x) (gradFun (I := I) g R x) +
          2 * R x ^ (-3 : Real) *
            g.inner x (gradFun (I := I) g S x) (gradFun (I := I) g R x) := by
    rw [hgradQ, hgradInv]
    simp only [map_add, map_smul, smul_eq_mul]
    rw [hinnerSymm]
    calc
      2 * R x ^ (-1 : Real) *
          (S x * (-2 * R x ^ (-3 : Real) *
              g.inner x (gradFun (I := I) g R x) (gradFun (I := I) g R x)) +
            R x ^ (-2 : Real) *
              g.inner x (gradFun (I := I) g S x) (gradFun (I := I) g R x)) =
        -4 * S x * (R x ^ (-1 : Real) * R x ^ (-3 : Real)) *
              g.inner x (gradFun (I := I) g R x) (gradFun (I := I) g R x) +
          2 * (R x ^ (-1 : Real) * R x ^ (-2 : Real)) *
              g.inner x (gradFun (I := I) g S x) (gradFun (I := I) g R x) := by
        ring
      _ = _ := by rw [hm1m3, hm1m2]
  obtain ⟨mu, basis, hinv, _, _, _⟩ :=
    exists_diagInv_of_equiv (I := I) g g x (C := 1) (by norm_num)
      (by intro v; simp)
  have hsquareExpansion := normSq0S_smul_sub_product_one_two
    (I := I) g x basis identityInvMetric hinv (R x) (nablaRic x)
      (differential1FormFun (I := I) R x) (Ric x)
  have hmixed := two_mul_inner_nablaRic_product_dscalar_eq_gradient_inner
    (I := I) (M := M) g x
  have hgradNorm :
      inner0S (I := I) g x 1
          (differential1FormFun (I := I) R x)
          (differential1FormFun (I := I) R x) =
        g.inner x (gradFun (I := I) g R x) (gradFun (I := I) g R x) := by
    rw [inner0S_differential1FormFun_pair_eq_grad_inner,
      Connection.gradient_eq_gradFun]
  have hsquare :
      normSq0S (I := I) g x 3
          (R x • nablaRic x -
            Tensor0SSpace.product
              (differential1FormFun (I := I) R x) (Ric x)) =
        R x ^ 2 * normSq0S (I := I) g x 3 (nablaRic x) -
          R x * g.inner x (gradFun (I := I) g S x) (gradFun (I := I) g R x) +
          g.inner x (gradFun (I := I) g R x) (gradFun (I := I) g R x) *
            S x := by
    rw [hsquareExpansion, hgradNorm, hSval]
    rw [show 2 * R x *
        inner0S (I := I) g x 3 (nablaRic x)
          (Tensor0SSpace.product
            (differential1FormFun (I := I) R x) (Ric x)) =
        R x * g.inner x (gradFun (I := I) g S x)
          (gradFun (I := I) g R x) by rw [← hmixed]; ring]
  have hm2 : R x ^ (-2 : Real) = (R x ^ 2)⁻¹ := by
    calc
      R x ^ (-2 : Real) = (R x ^ (2 : Real))⁻¹ :=
        Real.rpow_neg hRpos.le (2 : Real)
      _ = (R x ^ 2)⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast (R x) 2)
  have hm3 : R x ^ (-3 : Real) = (R x ^ 3)⁻¹ := by
    calc
      R x ^ (-3 : Real) = (R x ^ (3 : Real))⁻¹ :=
        Real.rpow_neg hRpos.le (3 : Real)
      _ = (R x ^ 3)⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast (R x) 3)
  have hm4 : R x ^ (-4 : Real) = (R x ^ 4)⁻¹ := by
    calc
      R x ^ (-4 : Real) = (R x ^ (4 : Real))⁻¹ :=
        Real.rpow_neg hRpos.le (4 : Real)
      _ = (R x ^ 4)⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast (R x) 4)
  rw [hquot, hdrift, hsquare, hm2, hm3, hm4]
  field_simp [ne_of_gt hRpos]
  ring

omit [NeZero (Module.finrank Real E)] [SigmaCompactSpace M] in
theorem gradientRicciSoliton_ricci_anisotropy_identity
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {σ : Real}
    (h : gradientRicciSoliton (I := I) g f σ)
    (hscalar : ∀ y : M, 0 < metricScalarAt (I := I) g y) (x : M) :
    let R : C^∞⟮I, M; Real⟯ :=
      ⟨fun y : M => metricScalarAt (I := I) g y,
        metricScalar_smooth (I := I) (M := M) g⟩
    weightedLaplacian (I := I) g f (ricciAnisotropy (I := I) g hscalar) x +
        2 * R x ^ (-1 : Real) *
          g.inner x (gradFun (I := I) g R x)
            (gradFun (I := I) g (ricciAnisotropy (I := I) g hscalar) x) =
      2 * R x ^ (-4 : Real) *
          normSq0S (I := I) g x 3 (ricciGradientCouplingAt (I := I) g x) +
        4 * R x ^ (-3 : Real) * ricciReactionDefectAt (I := I) g x := by
  let R : C^∞⟮I, M; Real⟯ :=
    ⟨fun y : M => metricScalarAt (I := I) g y,
      metricScalar_smooth (I := I) (M := M) g⟩
  let Q := ricciNormSqScalarRatio (I := I) g hscalar
  let A := ricciAnisotropy (I := I) g hscalar
  have hratio := gradientRicciSoliton_ricci_norm_sq_scalar_ratio_identity
    (I := I) (M := M) h hscalar x
  change weightedLaplacian (I := I) g f A x +
        2 * R x ^ (-1 : Real) *
          g.inner x (gradFun (I := I) g R x) (gradFun (I := I) g A x) = _
  have hA : A = Q - ContMDiffMap.const (Module.finrank Real E : Real)⁻¹ := rfl
  have hgrad :
      gradFun (I := I) g A x = gradFun (I := I) g Q x := by
    rw [hA]
    change gradientFun (I := I) g
      (fun y : M => Q y - (Module.finrank Real E : Real)⁻¹) x = _
    rw [gradientFun_sub (I := I) g
      ((Q.contMDiff x).mdifferentiableAt (by simp)) mdifferentiableAt_const,
      gradientFun_const, sub_zero, Connection.gradient_eq_gradFun]
  rw [hgrad, hA, weightedLaplacian_sub_const]
  simpa [R, Q] using hratio

end DifferentialGeometry.Geometry
