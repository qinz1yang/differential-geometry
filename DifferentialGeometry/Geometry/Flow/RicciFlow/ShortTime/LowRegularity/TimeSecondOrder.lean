import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SecondOrderAction
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.SecondOrderCoefficientLipschitzBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.TimeDependentLowOrderOperators

noncomputable section

open Bundle Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem subtype_norm_lip
    {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
    {D : Set X} {C : ℝ} (hC : 0 ≤ C) (F : D → Y)
    (hF : ∀ x y : D, ‖F x - F y‖ ≤ C * ‖(x : X) - (y : X)‖) :
    LipschitzWith ⟨C, hC⟩ F := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hcoe : ((⟨C, hC⟩ : NNReal) : ℝ) = C := rfl
  calc
    dist (F x) (F y) = ‖F x - F y‖ := dist_eq_norm _ _
    _ ≤ C * ‖(x : X) - (y : X)‖ := hF x y
    _ = ((⟨C, hC⟩ : NNReal) : ℝ) * ‖(x : X) - (y : X)‖ :=
      congrArg (fun a : ℝ => a * ‖(x : X) - (y : X)‖) hcoe.symm
    _ = ((⟨C, hC⟩ : NNReal) : ℝ) * dist x y := by
      rw [Subtype.dist_eq, dist_eq_norm]

private theorem secondOrderActionFourthToSecondOrderCore_pairing
    (g : SmoothRiemannianMetric I M)
    {ρ δ C : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).secondOrderActionFourthToSecondOrder (I := I) (M := M) -
        (lowCoreActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal U).secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖)
    (x y : LowerScaleTimeInternal.LowCore (I := I) (M := M) g) :
    ‖LowerScaleTimeInternal.secondOrderActionFourthToSecondOrderCore (I := I) (M := M)
          g hρ hδ0 hδ_le hreal x -
        LowerScaleTimeInternal.secondOrderActionFourthToSecondOrderCore (I := I) (M := M)
          g hρ hδ0 hδ_le hreal y‖ ≤
      C * ‖(x : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) -
        (y : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))‖ := by
  obtain ⟨T, hT⟩ := x.property
  obtain ⟨U, hU⟩ := y.property
  have hx : x =
      ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ := by
    apply Subtype.ext
    exact hT.symm
  have hy : y =
      ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) U, ⟨U, rfl⟩⟩ := by
    apply Subtype.ext
    exact hU.symm
  rw [hx, hy]
  rw [LowerScaleTimeInternal.secondOrderActionFourthToSecondOrderCore_value,
    LowerScaleTimeInternal.secondOrderActionFourthToSecondOrderCore_value]
  rw [← map_sub]
  simpa only [ccToHsLin_apply] using hpair T U

private theorem secondOrderActionThirdToFirstOrderCore_pairing
    (g : SmoothRiemannianMetric I M)
    {ρ δ C : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).secondOrderActionThirdToFirstOrder (I := I) (M := M) -
        (lowCoreActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal U).secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖)
    (x y : LowerScaleTimeInternal.LowCore (I := I) (M := M) g) :
    ‖LowerScaleTimeInternal.secondOrderActionThirdToFirstOrderCore (I := I) (M := M)
          g hρ hδ0 hδ_le hreal x -
        LowerScaleTimeInternal.secondOrderActionThirdToFirstOrderCore (I := I) (M := M)
          g hρ hδ0 hδ_le hreal y‖ ≤
      C * ‖(x : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) -
        (y : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))‖ := by
  obtain ⟨T, hT⟩ := x.property
  obtain ⟨U, hU⟩ := y.property
  have hx : x =
      ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩ := by
    apply Subtype.ext
    exact hT.symm
  have hy : y =
      ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) U, ⟨U, rfl⟩⟩ := by
    apply Subtype.ext
    exact hU.symm
  rw [hx, hy]
  rw [LowerScaleTimeInternal.secondOrderActionThirdToFirstOrderCore_value,
    LowerScaleTimeInternal.secondOrderActionThirdToFirstOrderCore_value]
  rw [← map_sub]
  simpa only [ccToHsLin_apply] using hpair T U

private theorem secondOrderActionFourthToSecondOrder_extension_lipschitz
    (g : SmoothRiemannianMetric I M)
    {ρ δ C : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hC : 0 ≤ C)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).secondOrderActionFourthToSecondOrder (I := I) (M := M) -
        (lowCoreActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal U).secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) :
    LipschitzWith ⟨C, hC⟩
      (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal) := by
  change LipschitzWith ⟨C, hC⟩
    (Dense.extend
      (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
      (LowerScaleTimeInternal.secondOrderActionFourthToSecondOrderCore (I := I) (M := M)
        g hρ hδ0 hδ_le hreal))
  refine
    DifferentialGeometry.Analysis.Parabolic.QuasiLinear.dense_lipschitz
      (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
      (LowerScaleTimeInternal.secondOrderActionFourthToSecondOrderCore (I := I) (M := M)
        g hρ hδ0 hδ_le hreal) ?_
  exact subtype_norm_lip
    (X := TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
    (Y := TensorHs (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
    hC _ <|
    secondOrderActionFourthToSecondOrderCore_pairing (I := I) (M := M)
      g hρ hδ0 hδ_le hreal hpair

private theorem secondOrderActionThirdToFirstOrder_extension_lipschitz
    (g : SmoothRiemannianMetric I M)
    {ρ δ C : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hC : 0 ≤ C)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).secondOrderActionThirdToFirstOrder (I := I) (M := M) -
        (lowCoreActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal U).secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖) :
    LipschitzWith ⟨C, hC⟩
      (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal) := by
  change LipschitzWith ⟨C, hC⟩
    (Dense.extend
      (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
      (LowerScaleTimeInternal.secondOrderActionThirdToFirstOrderCore (I := I) (M := M)
        g hρ hδ0 hδ_le hreal))
  refine
    DifferentialGeometry.Analysis.Parabolic.QuasiLinear.dense_lipschitz
      (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
      (LowerScaleTimeInternal.secondOrderActionThirdToFirstOrderCore (I := I) (M := M)
        g hρ hδ0 hδ_le hreal) ?_
  exact subtype_norm_lip
    (X := TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
    (Y := TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
      TensorHs (I := I) (M := M) g 0 2 (1 : ℝ))
    hC _ <|
    secondOrderActionThirdToFirstOrderCore_pairing (I := I) (M := M)
      g hρ hδ0 hδ_le hreal hpair

private theorem secondOrderActionFourthToSecondOrder_extension_core
    (g : SmoothRiemannianMetric I M)
    {ρ δ C : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hC : 0 ≤ C)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).secondOrderActionFourthToSecondOrder (I := I) (M := M) -
        (lowCoreActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal U).secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖)
    (T : SmoothCcTensor g 0 2) :
    lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
      (lowCoreActionCoefficients (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T).secondOrderActionFourthToSecondOrder (I := I) (M := M) := by
  let D : Set (TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :=
    Set.range (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))
  let F : D →
      (TensorHs (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
        TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :=
    LowerScaleTimeInternal.secondOrderActionFourthToSecondOrderCore (I := I) (M := M)
      g hρ hδ0 hδ_le hreal
  have hF : LipschitzWith ⟨C, hC⟩ F :=
    subtype_norm_lip
      (X := TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (Y := TensorHs (I := I) (M := M) g 0 2 (4 : ℝ) →L[ℝ]
        TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      hC F <| secondOrderActionFourthToSecondOrderCore_pairing (I := I) (M := M)
        g hρ hδ0 hδ_le hreal hpair
  let x : D :=
    ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩
  have hext :=
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)).extend_eq
      hF.continuous x
  change Dense.extend
      (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
      F (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
    (lowCoreActionCoefficients (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T).secondOrderActionFourthToSecondOrder (I := I) (M := M)
  calc
    Dense.extend
        (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
        F (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
      F x := hext
    _ = _ := LowerScaleTimeInternal.secondOrderActionFourthToSecondOrderCore_value
      (I := I) (M := M) g hρ hδ0 hδ_le hreal T

private theorem secondOrderActionThirdToFirstOrder_extension_core
    (g : SmoothRiemannianMetric I M)
    {ρ δ C : ℝ} (hρ : 0 ≤ ρ) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ)
    (hC : 0 ≤ C)
    (hpair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal T).secondOrderActionThirdToFirstOrder (I := I) (M := M) -
        (lowCoreActionCoefficients (I := I) (M := M)
          g hρ hδ0 hδ_le hreal U).secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖)
    (T : SmoothCcTensor g 0 2) :
    lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M) g hρ hδ0 hδ_le hreal
        (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
      (lowCoreActionCoefficients (I := I) (M := M)
        g hρ hδ0 hδ_le hreal T).secondOrderActionThirdToFirstOrder (I := I) (M := M) := by
  let D : Set (TensorHs (I := I) (M := M) g 0 2 (2 : ℝ)) :=
    Set.range (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ))
  let F : D →
      (TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        TensorHs (I := I) (M := M) g 0 2 (1 : ℝ)) :=
    LowerScaleTimeInternal.secondOrderActionThirdToFirstOrderCore (I := I) (M := M)
      g hρ hδ0 hδ_le hreal
  have hF : LipschitzWith ⟨C, hC⟩ F :=
    subtype_norm_lip
      (X := TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (Y := TensorHs (I := I) (M := M) g 0 2 (3 : ℝ) →L[ℝ]
        TensorHs (I := I) (M := M) g 0 2 (1 : ℝ))
      hC F <| secondOrderActionThirdToFirstOrderCore_pairing (I := I) (M := M)
        g hρ hδ0 hδ_le hreal hpair
  let x : D :=
    ⟨ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T, ⟨T, rfl⟩⟩
  have hext :=
    (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)).extend_eq
      hF.continuous x
  change Dense.extend
      (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
      F (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
    (lowCoreActionCoefficients (I := I) (M := M)
      g hρ hδ0 hδ_le hreal T).secondOrderActionThirdToFirstOrder (I := I) (M := M)
  calc
    Dense.extend
        (ccToHsLin_dense (I := I) (M := M) g 2 (by positivity))
        F (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
      F x := hext
    _ = _ := LowerScaleTimeInternal.secondOrderActionThirdToFirstOrderCore_value
      (I := I) (M := M) g hρ hδ0 hδ_le hreal T

theorem radialSecondOrderAction_pairing_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {ρ₀ δ : ℝ} (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ 0 ≤ C ∧
      ∀ (T : SmoothCcTensor g 0 2) (hρ0 : 0 ≤ ρ) (hρ_le' : ρ ≤ ρ₀),
      let hreal' : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ :=
        fun S hS => hreal S (hS.trans hρ_le')
      let A := lowCoreActionCoefficients (I := I) (M := M)
        g hρ0 hδ0 hδ_le hreal' T
      ‖A.secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤ C * ρ ∧
        ‖A.secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤ C * ρ ∧
        (tensorHsInclusion (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (A.secondOrderActionFourthToSecondOrder (I := I) (M := M)) =
          (A.secondOrderActionThirdToFirstOrder (I := I) (M := M)).comp
            (tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)) := by
  obtain ⟨ρ₂, C₂, hρ₂, hC₂, hc₂⟩ :=
    exists_lowerScaleSecondOrderCoefficient_smallPerturbation_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cₐ, hCₐ, hpair⟩ :=
    secondOrderAction_sobolev_extension_bounds (I := I) (M := M) hDim g
  let ρ : ℝ := min ρ₀ ρ₂
  let C : ℝ := Cₐ * C₂
  have hρ : 0 < ρ := lt_min hρ₀ hρ₂
  have hρ_le : ρ ≤ ρ₀ := min_le_left _ _
  have hρ₂_le : ρ ≤ ρ₂ := min_le_right _ _
  have hC : 0 ≤ C := mul_nonneg hCₐ hC₂
  refine ⟨ρ, C, hρ, hρ_le, hC, ?_⟩
  intro T hρ0 hρ_le'
  dsimp only
  let S : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g ρ T
  have hSρ :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ :=
    lowRadial_norm (I := I) (M := M) g hρ0 T
  have hSδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g S) δ :=
    hreal S (hSρ.trans hρ_le)
  have hzeroHs :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ₀ := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hρ₀.le
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ :=
    hreal _ hzeroHs
  let A : LowerScaleActionCoefficients g :=
    lowCoreActionCoefficients (I := I) (M := M) g hρ0 hδ0 hδ_le
      (fun P hP => hreal P (hP.trans hρ_le')) T
  obtain ⟨hpoint, hjet⟩ :=
    hc₂ S
      (lowRadial_symm (I := I) (M := M) g ρ T)
      hδ_le hδ0 hSδ hZδ hρ.le hρ₂_le hSρ
  have hB : 0 ≤ C₂ * ρ := mul_nonneg hC₂ hρ.le
  obtain ⟨hHi, hLo, _, _, hcompat⟩ :=
    hpair A (C₂ * ρ) hB (by
      simpa only [A, lowCoreActionCoefficients, S] using hpoint) (by
      simpa only [A, lowCoreActionCoefficients, S] using hjet)
  refine ⟨hHi.trans_eq ?_, hLo.trans_eq ?_, hcompat⟩
  · simp only [C]
    ring
  · simp only [C]
    ring

theorem radialSecondOrderAction_pairing_bound_on_radius
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {ρ₀ δ : ℝ} (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ (ρ C : ℝ) (hρ_le : ρ ≤ ρ₀), 0 < ρ ∧ 0 ≤ C ∧
      ∀ {r : ℝ} (hr0 : 0 ≤ r) (hr_le : r ≤ ρ)
        (T : SmoothCcTensor g 0 2),
      let hreal' : ∀ S : SmoothCcTensor g 0 2,
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r →
            gFibreOpBound (I := I) (M := M) g
              (ccTensorBilinSymm (I := I) g S) δ :=
        fun S hS => hreal S (hS.trans (hr_le.trans hρ_le))
      let A := lowCoreActionCoefficients (I := I) (M := M)
        g hr0 hδ0 hδ_le hreal' T
      ‖A.secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤ C * r ∧
        ‖A.secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤ C * r ∧
        (tensorHsInclusion (I := I) (M := M) (g := g)
            (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
              (A.secondOrderActionFourthToSecondOrder (I := I) (M := M)) =
          (A.secondOrderActionThirdToFirstOrder (I := I) (M := M)).comp
            (tensorHsInclusion (I := I) (M := M) (g := g)
              (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)) := by
  obtain ⟨ρ₂, C₂, hρ₂, hC₂, hc₂⟩ :=
    exists_lowerScaleSecondOrderCoefficient_smallPerturbation_secondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cₐ, hCₐ, hpair⟩ :=
    secondOrderAction_sobolev_extension_bounds (I := I) (M := M) hDim g
  let ρ : ℝ := min ρ₀ ρ₂
  let C : ℝ := Cₐ * C₂
  have hρ : 0 < ρ := lt_min hρ₀ hρ₂
  have hρ_le : ρ ≤ ρ₀ := min_le_left _ _
  have hρ₂_le : ρ ≤ ρ₂ := min_le_right _ _
  have hC : 0 ≤ C := mul_nonneg hCₐ hC₂
  refine ⟨ρ, C, hρ_le, hρ, hC, ?_⟩
  intro r hr0 hr_le T
  dsimp only
  let S : SmoothCcTensor g 0 2 :=
    lowRadial (I := I) (M := M) g r T
  have hSr :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r :=
    lowRadial_norm (I := I) (M := M) g hr0 T
  have hSδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g S) δ :=
    hreal S (hSr.trans (hr_le.trans hρ_le))
  have hzeroHs :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (0 : SmoothCcTensor g 0 2)‖ ≤ ρ₀ := by
    rw [show (0 : SmoothCcTensor g 0 2) =
        (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
      ccTensorToHs_smul, zero_smul, norm_zero]
    exact hρ₀.le
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ :=
    hreal _ hzeroHs
  let A : LowerScaleActionCoefficients g :=
    lowCoreActionCoefficients (I := I) (M := M) g hr0 hδ0 hδ_le
      (fun P hP => hreal P (hP.trans (hr_le.trans hρ_le))) T
  obtain ⟨hpoint, hjet⟩ :=
    hc₂ S
      (lowRadial_symm (I := I) (M := M) g r T)
      hδ_le hδ0 hSδ hZδ hr0 (hr_le.trans hρ₂_le) hSr
  have hB : 0 ≤ C₂ * r := mul_nonneg hC₂ hr0
  obtain ⟨hHi, hLo, _, _, hcompat⟩ :=
    hpair A (C₂ * r) hB (by
      simpa only [A, lowCoreActionCoefficients, S] using hpoint) (by
      simpa only [A, lowCoreActionCoefficients, S] using hjet)
  refine ⟨hHi.trans_eq ?_, hLo.trans_eq ?_, hcompat⟩
  · simp only [C]
    ring
  · simp only [C]
    ring

theorem radialSecondOrderAction_lipschitz
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M)
    {ρ₀ δ : ℝ} (hρ₀ : 0 < ρ₀) (hδ0 : 0 ≤ δ) (hδ_le : δ ≤ 1 / 3)
    (hreal : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ ρ₀ →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ) :
    ∃ (ρ : ℝ) (C : NNReal) (_hρ : 0 < ρ) (hρ_le : ρ ≤ ρ₀),
      ∀ {r : ℝ} (hr0 : 0 ≤ r) (hr_le : r ≤ ρ),
        let hreal' : ∀ S : SmoothCcTensor g 0 2,
            ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r →
              gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g S) δ :=
          fun S hS => hreal S (hS.trans (hr_le.trans hρ_le))
        LipschitzWith C
            (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M)
              g hr0 hδ0 hδ_le hreal') ∧
          LipschitzWith C
            (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M)
              g hr0 hδ0 hδ_le hreal') ∧
          (∀ T : SmoothCcTensor g 0 2,
            lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M)
                g hr0 hδ0 hδ_le hreal'
                (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
              (lowCoreActionCoefficients (I := I) (M := M)
                g hr0 hδ0 hδ_le hreal' T).secondOrderActionFourthToSecondOrder (I := I) (M := M)) ∧
          (∀ T : SmoothCcTensor g 0 2,
            lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M)
                g hr0 hδ0 hδ_le hreal'
                (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ) T) =
              (lowCoreActionCoefficients (I := I) (M := M)
                g hr0 hδ0 hδ_le hreal' T).secondOrderActionThirdToFirstOrder (I := I) (M := M)) ∧
          ∀ v : TensorHs (I := I) (M := M) g 0 2 (2 : ℝ),
            (tensorHsInclusion (I := I) (M := M) (g := g)
                (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
                (lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M)
                  g hr0 hδ0 hδ_le hreal' v) =
              (lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M)
                  g hr0 hδ0 hδ_le hreal' v).comp
                (tensorHsInclusion (I := I) (M := M) (g := g)
                  (r := 0) (s := 2)
                  (show (3 : ℝ) ≤ 4 by norm_num)) := by
  obtain ⟨ρp, C, hρp, hC, hpair⟩ :=
    secondOrderAction_pairing_lipschitz_bound (I := I) (M := M) hDim g g
  let ρ : ℝ := min ρ₀ ρp
  have hρ : 0 < ρ := lt_min hρ₀ hρp
  have hρ_le : ρ ≤ ρ₀ := min_le_left _ _
  have hρp_le : ρ ≤ ρp := min_le_right _ _
  refine ⟨ρ, ⟨C, hC⟩, hρ, hρ_le, ?_⟩
  intro r hr0 hr_le
  dsimp only
  let hreal' : ∀ S : SmoothCcTensor g 0 2,
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r →
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
    fun S hS => hreal S (hS.trans (hr_le.trans hρ_le))
  have hδlt : δ < 1 :=
    lt_of_le_of_lt hδ_le (by norm_num)
  have hZδ :
      gFibreOpBound (I := I) (M := M) g
        (ccTensorBilinSymm (I := I) g
          (0 : SmoothCcTensor g 0 2)) δ :=
    hreal' (0 : SmoothCcTensor g 0 2) (by
      rw [show (0 : SmoothCcTensor g 0 2) =
          (0 : ℝ) • (0 : SmoothCcTensor g 0 2) by simp,
        ccTensorToHs_smul, zero_smul, norm_zero]
      exact hr0)
  have hHiPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M)
          g hr0 hδ0 hδ_le hreal' T).secondOrderActionFourthToSecondOrder (I := I) (M := M) -
        (lowCoreActionCoefficients (I := I) (M := M)
          g hr0 hδ0 hδ_le hreal' U).secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M)
          g 2 (2 : ℝ) (T - U)‖ := by
    intro T U
    let S := lowRadial (I := I) (M := M) g r T
    let V := lowRadial (I := I) (M := M) g r U
    have hSρ :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r :=
      lowRadial_norm (I := I) (M := M) g hr0 T
    have hVρ :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V‖ ≤ r :=
      lowRadial_norm (I := I) (M := M) g hr0 U
    have hSδ :
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
      hreal' S hSρ
    have hVδ :
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g V) δ :=
      hreal' V hVρ
    obtain ⟨hHi, _⟩ :=
      hpair S V hδlt hSδ hVδ hZδ
        (hSρ.trans (hr_le.trans hρp_le))
        (hVρ.trans (hr_le.trans hρp_le))
    have hSV :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ := by
      have hrad := lowRadial_lip (I := I) (M := M) g hr0 T U
      have hmapSV :
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V := by
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) S V
      have hmapTU :
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U := by
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) T U
      rw [hmapSV, hmapTU]
      simpa only [S, V] using hrad
    have hbound :
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ :=
      mul_le_mul_of_nonneg_left hSV hC
    have hHi' :
        ‖(lowCoreActionCoefficients (I := I) (M := M)
            g hr0 hδ0 hδ_le hreal' T).secondOrderActionFourthToSecondOrder (I := I) (M := M) -
          (lowCoreActionCoefficients (I := I) (M := M)
            g hr0 hδ0 hδ_le hreal' U).secondOrderActionFourthToSecondOrder (I := I) (M := M)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (S - V)‖ := by
      simpa only [lowCoreActionCoefficients, S, V] using hHi
    exact hHi'.trans hbound
  have hLoPair : ∀ T U : SmoothCcTensor g 0 2,
      ‖(lowCoreActionCoefficients (I := I) (M := M)
          g hr0 hδ0 hδ_le hreal' T).secondOrderActionThirdToFirstOrder (I := I) (M := M) -
        (lowCoreActionCoefficients (I := I) (M := M)
          g hr0 hδ0 hδ_le hreal' U).secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤
        C * ‖ccTensorToHs (I := I) (M := M)
          g 2 (2 : ℝ) (T - U)‖ := by
    intro T U
    let S := lowRadial (I := I) (M := M) g r T
    let V := lowRadial (I := I) (M := M) g r U
    have hSρ :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S‖ ≤ r :=
      lowRadial_norm (I := I) (M := M) g hr0 T
    have hVρ :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V‖ ≤ r :=
      lowRadial_norm (I := I) (M := M) g hr0 U
    have hSδ :
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g S) δ :=
      hreal' S hSρ
    have hVδ :
        gFibreOpBound (I := I) (M := M) g
          (ccTensorBilinSymm (I := I) g V) δ :=
      hreal' V hVρ
    obtain ⟨_, hLo⟩ :=
      hpair S V hδlt hSδ hVδ hZδ
        (hSρ.trans (hr_le.trans hρp_le))
        (hVρ.trans (hr_le.trans hρp_le))
    have hSV :
        ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤
          ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ := by
      have hrad := lowRadial_lip (I := I) (M := M) g hr0 T U
      have hmapSV :
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) S -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) V := by
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) S V
      have hmapTU :
          ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U) =
            ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T -
              ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) U := by
        simpa only [ccToHsLin_apply] using
          map_sub (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) T U
      rw [hmapSV, hmapTU]
      simpa only [S, V] using hrad
    have hbound :
        C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (S - V)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) (T - U)‖ :=
      mul_le_mul_of_nonneg_left hSV hC
    have hLo' :
        ‖(lowCoreActionCoefficients (I := I) (M := M)
            g hr0 hδ0 hδ_le hreal' T).secondOrderActionThirdToFirstOrder (I := I) (M := M) -
          (lowCoreActionCoefficients (I := I) (M := M)
            g hr0 hδ0 hδ_le hreal' U).secondOrderActionThirdToFirstOrder (I := I) (M := M)‖ ≤
          C * ‖ccTensorToHs (I := I) (M := M)
            g 2 (2 : ℝ) (S - V)‖ := by
      simpa only [lowCoreActionCoefficients, S, V] using hLo
    exact hLo'.trans hbound
  have hHiLip :=
    secondOrderActionFourthToSecondOrder_extension_lipschitz (I := I) (M := M)
      g hr0 hδ0 hδ_le hreal' hC hHiPair
  have hLoLip :=
    secondOrderActionThirdToFirstOrder_extension_lipschitz (I := I) (M := M)
      g hr0 hδ0 hδ_le hreal' hC hLoPair
  have hHiCore :=
    secondOrderActionFourthToSecondOrder_extension_core (I := I) (M := M)
      g hr0 hδ0 hδ_le hreal' hC hHiPair
  have hLoCore :=
    secondOrderActionThirdToFirstOrder_extension_core (I := I) (M := M)
      g hr0 hδ0 hδ_le hreal' hC hLoPair
  refine ⟨hHiLip, hLoLip, hHiCore, hLoCore, ?_⟩
  let J12 :=
    tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)
  let J34 :=
    tensorHsInclusion (I := I) (M := M) (g := g)
      (r := 0) (s := 2) (show (3 : ℝ) ≤ 4 by norm_num)
  let AHi :=
    lowerScaleSecondOrderActionFourthToSecondOrder (I := I) (M := M)
      g hr0 hδ0 hδ_le hreal'
  let ALo :=
    lowerScaleSecondOrderActionThirdToFirstOrder (I := I) (M := M)
      g hr0 hδ0 hδ_le hreal'
  have hleft : Continuous (fun v =>
      J12.comp (AHi v)) :=
    (ContinuousLinearMap.compL ℝ
      (TensorHs (I := I) (M := M) g 0 2 (4 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (2 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (continuous_const.prodMk hHiLip.continuous)
  have hright : Continuous (fun v =>
      (ALo v).comp J34) :=
    (ContinuousLinearMap.compL ℝ
      (TensorHs (I := I) (M := M) g 0 2 (4 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (3 : ℝ))
      (TensorHs (I := I) (M := M) g 0 2 (1 : ℝ))).continuous₂.comp
        (hLoLip.continuous.prodMk continuous_const)
  intro v
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by positivity)
  refine hdense.induction_on v (isClosed_eq hleft hright) ?_
  intro T
  rw [hHiCore T, hLoCore T]
  exact secondOrderAction_sobolev_extensions_commute (I := I) (M := M) hDim g
    (lowCoreActionCoefficients (I := I) (M := M)
      g hr0 hδ0 hδ_le hreal' T)

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
