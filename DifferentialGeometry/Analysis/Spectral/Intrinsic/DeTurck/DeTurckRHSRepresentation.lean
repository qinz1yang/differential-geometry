import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearityExistence
import DifferentialGeometry.Analysis.Spectral.Tensor.Spectrum.SlotSwapEquivariance

noncomputable section

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
private theorem rawConnLap_symmS
    (g₀ : SmoothRiemannianMetric I M) (S : SmoothCcTensor g₀ 0 2) :
    rawTensorConnLapSmooth (I := I) g₀ 0 2 (symmS (I := I) (M := M) g₀ S) =
      symmS (I := I) (M := M) g₀ (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) := by
  have hhalf : ∀ W : SmoothCcTensor g₀ 0 2,
      (1 / 2 : ℝ) • W + (1 / 2 : ℝ) • W = W := fun W => by
    rw [← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]
  have hzero : rawTensorConnLapSmooth (I := I) g₀ 0 2
      (0 : SmoothCcTensor g₀ 0 2) = 0 := by
    have h := rawTensorConnLapSmooth_sub (I := I) (M := M) g₀ 0 2 S S
    rwa [sub_self, sub_self] at h
  have hadd : ∀ A B : SmoothCcTensor g₀ 0 2,
      rawTensorConnLapSmooth (I := I) g₀ 0 2 (A + B) =
        rawTensorConnLapSmooth (I := I) g₀ 0 2 A +
          rawTensorConnLapSmooth (I := I) g₀ 0 2 B := by
    intro A B
    have hAB : A + B = A - (0 - B) := by rw [zero_sub, sub_neg_eq_add]
    rw [hAB, rawTensorConnLapSmooth_sub (I := I) (M := M) g₀ 0 2 A (0 - B),
      rawTensorConnLapSmooth_sub (I := I) (M := M) g₀ 0 2 0 B, hzero,
      zero_sub, sub_neg_eq_add]
  have hLV : rawTensorConnLapSmooth (I := I) g₀ 0 2
        (symmS (I := I) (M := M) g₀ S) +
      rawTensorConnLapSmooth (I := I) g₀ 0 2
        (symmS (I := I) (M := M) g₀ S) =
      rawTensorConnLapSmooth (I := I) g₀ 0 2 S +
        domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) := by
    rw [← hadd]
    simp only [ccTensor02Symm]
    rw [hhalf, hadd,
      rawTensorConnLapSmooth_domDomCongrSection (I := I) (M := M) g₀
        (Equiv.swap (0 : Fin 2) 1) S]
  have hgoal : symmS (I := I) (M := M) g₀
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) =
      (1 / 2 : ℝ) •
        (rawTensorConnLapSmooth (I := I) g₀ 0 2
            (symmS (I := I) (M := M) g₀ S) +
          rawTensorConnLapSmooth (I := I) g₀ 0 2
            (symmS (I := I) (M := M) g₀ S)) := by
    change (1 / 2 : ℝ) •
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S +
          domDomCongrSection (I := I) g₀ (Equiv.swap (0 : Fin 2) 1)
            (rawTensorConnLapSmooth (I := I) g₀ 0 2 S)) = _
    rw [← hLV]
  rw [hgoal, smul_add, hhalf]

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem bilinSymm_add
    (g : SmoothRiemannianMetric I M)
    (S T : SmoothCcTensor g 0 2) (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g (S + T) x v w =
      ccTensorBilinSymm (I := I) g S x v w +
        ccTensorBilinSymm (I := I) g T x v w := by
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply,
    ccTensorBilinSymm_apply]
  have hbilin : ∀ (a b : TangentSpace I x),
      ccTensorBilin (I := I) g (S + T) x a b =
        ccTensorBilin (I := I) g S x a b +
          ccTensorBilin (I := I) g T x a b := by
    intro a b
    rw [ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply]
    show ccTensorModel (I := I) g (S + T) x ![a, b] =
      ccTensorModel (I := I) g S x ![a, b] +
        ccTensorModel (I := I) g T x ![a, b]
    have hmodel : ccTensorModel (I := I) g (S + T) x =
        ccTensorModel (I := I) g S x + ccTensorModel (I := I) g T x := by
      rw [ccTensorModel, ccTensorModel, ccTensorModel]
      have hmul : (ccTensorMultilinear (I := I) g (S + T) x :
            Tensor0SBundle.Tensor0SSpace 2 I x) =
          (ccTensorMultilinear (I := I) g S x :
              Tensor0SBundle.Tensor0SSpace 2 I x) +
            (ccTensorMultilinear (I := I) g T x :
              Tensor0SBundle.Tensor0SSpace 2 I x) := by
        rw [ccTensorMultilinear_apply, ccTensorMultilinear_apply,
          ccTensorMultilinear_apply, SmoothCcTensor.toSection_add]
        exact add_apply _ _ _
      rw [hmul, Tensor0SBundle.Tensor0SSpace.toModel_add]
    rw [hmodel, add_apply]
  rw [hbilin v w, hbilin w v]
  ring

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem bilinSymm_sec_congr
    {g₁ g₂ : SmoothRiemannianMetric I M}
    (S₁ : SmoothCcTensor g₁ 0 2) (S₂ : SmoothCcTensor g₂ 0 2)
    (hsec : S₁.toSection = S₂.toSection)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₁ S₁ x v w =
      ccTensorBilinSymm (I := I) g₂ S₂ x v w := by
  have hmodel : ∀ (a b : TangentSpace I x),
      ccTensorModel (I := I) g₁ S₁ x ![a, b] =
        ccTensorModel (I := I) g₂ S₂ x ![a, b] := by
    intro a b
    unfold ccTensorModel
    rw [ccTensorMultilinear_apply, ccTensorMultilinear_apply, hsec]
  rw [ccTensorBilinSymm_apply, ccTensorBilinSymm_apply,
    ccTensorBilin_apply, ccTensorBilin_apply, ccTensorBilin_apply,
    ccTensorBilin_apply, hmodel v w, hmodel w v]

omit [SigmaCompactSpace M] in
theorem deTurck_rem_repr
    (g₀ g_bg : SmoothRiemannianMetric I M)
    (S : SmoothCcTensor g₀ 0 2) {δ : ℝ}
    (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ S) δ)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) g₀
        (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
            (symmS (I := I) (M := M) g₀ S) hδ_lt
            (gFibreOpBound_symmS (I := I) (M := M) g₀ S hδ) +
          rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w =
      deTurckRicciRHS (I := I) g_bg
        (tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ) x v w := by
  have hlap : ccTensorBilinSymm (I := I) g₀
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w =
      ccTensorBilinSymm (I := I) g₀
        (rawTensorConnLapSmooth (I := I) g₀ 0 2
          (symmS (I := I) (M := M) g₀ S)) x v w := by
    rw [rawConnLap_symmS (I := I) (M := M) g₀ S,
      ccTensorBilinSymm_symmS_apply (I := I) (M := M) g₀
        (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w]
  rw [bilinSymm_add (I := I) (M := M) g₀
      (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
        (symmS (I := I) (M := M) g₀ S) hδ_lt
        (gFibreOpBound_symmS (I := I) (M := M) g₀ S hδ))
      (rawTensorConnLapSmooth (I := I) g₀ 0 2 S) x v w,
    hlap,
    ← bilinSymm_add (I := I) (M := M) g₀
      (deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
        (symmS (I := I) (M := M) g₀ S) hδ_lt
        (gFibreOpBound_symmS (I := I) (M := M) g₀ S hδ))
      (rawTensorConnLapSmooth (I := I) g₀ 0 2
        (symmS (I := I) (M := M) g₀ S)) x v w]
  set gDT := tensorSectionRealizeMetric (I := I) g₀
    (symmS (I := I) (M := M) g₀ S) hδ_lt
    (gFibreOpBound_symmS (I := I) (M := M) g₀ S hδ) with hgDT_def
  set R : SmoothCcTensor g₀ 0 2 :=
    { toSection := (deTurckRHSSection (I := I) g_bg gDT).toSection
      hasCompactSupport := (deTurckRHSSection (I := I) g_bg gDT).hasCompactSupport }
    with hR_def
  have hsum_eq : deTurckSmoothRemainder (I := I) (M := M) g₀ g_bg
      (symmS (I := I) (M := M) g₀ S) hδ_lt
      (gFibreOpBound_symmS (I := I) (M := M) g₀ S hδ) +
      rawTensorConnLapSmooth (I := I) g₀ 0 2
        (symmS (I := I) (M := M) g₀ S) = R := by
    rw [deTurckSmoothRemainder, sub_add_cancel]
  rw [hsum_eq,
    bilinSymm_sec_congr R (deTurckRHSSectionBackground (I := I) g_bg gDT)
      (by rw [hR_def, deTurckRHSSectionBackground_toSection]) x v w]
  have hreal : gDT = tensorSectionRealizeMetric (I := I) g₀ S hδ_lt hδ :=
    tensorSectionRealizeMetric_symmS_eq (I := I) g₀ S hδ_lt hδ hδ_lt
      (gFibreOpBound_symmS (I := I) (M := M) g₀ S hδ)
  rw [← hreal]
  exact deTurckRHSSection_ccTensorBilinSymm_eq_deTurckRicciRHS
    (I := I) g_bg gDT x v w

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
