import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.RemainderFirstOrderBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.TameEstimates

noncomputable section

open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open _root_.DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.HCGCompactness
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.PDE.DeTurck.RicciLinearization
open DifferentialGeometry.Analysis.Spectral.MetricRealization
open DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem smoothHs_eq_ccHs'
    (g : SmoothRiemannianMetric I M) (sigma : ℝ)
    (T : SmoothCcTensor g 0 2) :
    smoothCcToTensorHs (I := I) (M := M) g sigma T =
      ccTensorToHs (I := I) (M := M) g 2 sigma T := by
  ext i
  rw [smoothCcToTensorHs_coeff, ccTensorToHs_coeff]

theorem smoothN_h1_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ ρ Ctop : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ (T T' : SmoothCcTensor g 0 2)
          (_hTsymm : ∀ (x : M) (v w : TangentSpace I x),
            ccTensorBilin (I := I) g T x v w = ccTensorBilin (I := I) g T x w v)
          (_hT'symm : ∀ (x : M) (v w : TangentSpace I x),
            ccTensorBilin (I := I) g T' x v w = ccTensorBilin (I := I) g T' x w v)
          (hδ : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T) δ₀)
          (hδ' : gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T') δ₀)
          (R : ℝ), 0 ≤ R → R ≤ ρ →
          ‖smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
          ‖smoothCcToTensorHs (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 1) T'‖ ≤ R →
          ‖deTurckSmoothN (I := I) (M := M) g gBase 1 T hδ₀_lt hδ -
              deTurckSmoothN (I := I) (M := M) g gBase 1 T' hδ₀_lt hδ'‖ ≤
            Ctop * R *
                ‖smoothCcToTensorHs (I := I) (M := M) g
                  (((1 : ℕ) : ℝ) + 2) (T - T')‖ +
              B0 R *
                ‖smoothCcToTensorHs (I := I) (M := M) g
                  (((1 : ℕ) : ℝ) + 1) (T - T')‖ +
              B1 R *
                  (‖smoothCcToTensorHs (I := I) (M := M) g
                      (((1 : ℕ) : ℝ) + 2) T‖ +
                    ‖smoothCcToTensorHs (I := I) (M := M) g
                      (((1 : ℕ) : ℝ) + 2) T'‖) *
                ‖smoothCcToTensorHs (I := I) (M := M) g
                  (((1 : ℕ) : ℝ) + 1) (T - T')‖ := by
  obtain ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, hrem⟩ :=
    rem_h1_uniform (I := I) (M := M) hDim gBase hΛ hδ₀_nonneg hδ₀_lt
  refine ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, ?_⟩
  intro g hEq hjet T T' hTsymm hT'symm hδ hδ' R hR hRρ hT2 hT2'
  have hT2c :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R := by
    rw [← smoothHs_eq_ccHs']
    convert hT2 using 1
    rw [Nat.cast_one]
    rw [show (1 : ℝ) + 1 = 2 by norm_num]
  have hT2c' :
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R := by
    rw [← smoothHs_eq_ccHs']
    convert hT2' using 1
    rw [Nat.cast_one]
    rw [show (1 : ℝ) + 1 = 2 by norm_num]
  have hraw := hrem g hEq hjet T T' hTsymm hT'symm hδ hδ'
    R hR hRρ hT2c hT2c'
  rw [deTurckSmoothN_sub_eq_smoothCcToTensorHs_remainderSub
    (I := I) (M := M) g gBase 1 T T' hδ₀_lt hδ hδ₀_lt hδ']
  rw [deTurckSmoothRemainderDiff_eq_termDiff_sub_connLapDiff
    (I := I) g gBase T T' hδ₀_lt hδ hδ₀_lt hδ']
  simp only [smoothHs_eq_ccHs']
  convert hraw using 1
  rw [Nat.cast_one]
  rw [show (1 : ℝ) + 1 = 2 by norm_num,
    show (1 : ℝ) + 2 = 3 by norm_num]

theorem deTurckRemainderOnSmoothCore_tame_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ ρ Ctop : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B0 R) ∧
      (∀ R : ℝ, 0 ≤ R → 0 ≤ B1 R) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ {R : ℝ} (_hR : 0 ≤ R) (_hRρ : R ≤ ρ)
          (hreal : ∀ T : SmoothCcTensor g 0 2,
            ‖smoothCcToTensorHs (I := I) (M := M) g
              (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
              gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) δ₀)
          (x y : smoothCore (I := I) (M := M) g R),
          ‖deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ₀_lt hreal x -
              deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ₀_lt hreal y‖ ≤
            Ctop * R *
                ‖(x.1.1 : TensorHs (I := I) (M := M) g 0 2
                  (((1 : ℕ) : ℝ) + 2)) - y.1.1‖ +
              B0 R *
                ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                  (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                  ((x.1.1 : TensorHs (I := I) (M := M) g 0 2
                    (((1 : ℕ) : ℝ) + 2)) - y.1.1)‖ +
              B1 R *
                  (‖(x.1.1 : TensorHs (I := I) (M := M) g 0 2
                    (((1 : ℕ) : ℝ) + 2))‖ +
                    ‖(y.1.1 : TensorHs (I := I) (M := M) g 0 2
                      (((1 : ℕ) : ℝ) + 2))‖) *
                ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                  (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                  ((x.1.1 : TensorHs (I := I) (M := M) g 0 2
                    (((1 : ℕ) : ℝ) + 2)) - y.1.1)‖ := by
  obtain ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, hsmooth⟩ :=
    smoothN_h1_uniform (I := I) (M := M) hDim gBase hΛ hδ₀_nonneg hδ₀_lt
  refine ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, ?_⟩
  intro g hEq hjet R hR hRρ hreal x y
  let X : SmoothCcTensor g 0 2 := coreRep g x
  let Y : SmoothCcTensor g 0 2 := coreRep g y
  let S : SmoothCcTensor g 0 2 := ccTensor02Symm (I := I) (M := M) g X
  let S' : SmoothCcTensor g 0 2 := ccTensor02Symm (I := I) (M := M) g Y
  have hS2 :
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S‖ ≤ R := by
    simpa only [S, X] using coreSymm_h2 (I := I) (M := M) g x
  have hS2' :
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) S'‖ ≤ R := by
    simpa only [S', Y] using coreSymm_h2 (I := I) (M := M) g y
  have hδS := hreal S hS2
  have hδS' := hreal S' hS2'
  have hbase := hsmooth g hEq hjet S S'
    (fun z v w => smoothCcTensorBilinForm_ccTensor02Symm_symm
      (I := I) (M := M) g X z v w)
    (fun z v w => smoothCcTensorBilinForm_ccTensor02Symm_symm
      (I := I) (M := M) g Y z v w)
    hδS hδS' R hR hRρ hS2 hS2'
  have hS3 :
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2) S‖ ≤
        ‖(x.1.1 : TensorHs (I := I) (M := M) g 0 2
          (((1 : ℕ) : ℝ) + 2))‖ := by
    calc
      _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2) X‖ := by
        simpa only [S] using
          norm_smoothCcToTensorHs_ccTensor02Symm_le (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 2) X
      _ = _ := by
        simp only [X]
        rw [coreRep_spec]
  have hS3' :
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2) S'‖ ≤
        ‖(y.1.1 : TensorHs (I := I) (M := M) g 0 2
          (((1 : ℕ) : ℝ) + 2))‖ := by
    calc
      _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2) Y‖ := by
        simpa only [S'] using
          norm_smoothCcToTensorHs_ccTensor02Symm_le (I := I) (M := M) g
            (((1 : ℕ) : ℝ) + 2) Y
      _ = _ := by
        simp only [Y]
        rw [coreRep_spec]
  have hdiff3 :
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2) (S - S')‖ ≤
        ‖(x.1.1 : TensorHs (I := I) (M := M) g 0 2
          (((1 : ℕ) : ℝ) + 2)) - y.1.1‖ := by
    calc
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2)
          (ccTensor02Symm (I := I) (M := M) g (X - Y))‖ := by
        simp only [S, S']
        rw [← ccTensor02Symm_sub]
      _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2)
          (X - Y)‖ :=
        norm_smoothCcToTensorHs_ccTensor02Symm_le (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 2) (X - Y)
      _ = _ := by
        rw [smoothCcToTensorHs_sub]
        simp only [X, Y]
        rw [coreRep_spec, coreRep_spec]
  have hdiff2 :
      ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1) (S - S')‖ ≤
        ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
          ((x.1.1 : TensorHs (I := I) (M := M) g 0 2
            (((1 : ℕ) : ℝ) + 2)) - y.1.1)‖ := by
    calc
      _ = ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1)
          (ccTensor02Symm (I := I) (M := M) g (X - Y))‖ := by
        simp only [S, S']
        rw [← ccTensor02Symm_sub]
      _ ≤ ‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 1)
          (X - Y)‖ :=
        norm_smoothCcToTensorHs_ccTensor02Symm_le (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) (X - Y)
      _ = ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
          (smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2)
            (X - Y))‖ := by
        rw [tensorHsInclusion_smoothCcToTensorHs]
      _ = _ := by
        rw [smoothCcToTensorHs_sub]
        simp only [X, Y]
        rw [coreRep_spec, coreRep_spec]
  have hcoreX :
      deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ₀_lt hreal x =
        deTurckSmoothN (I := I) (M := M) g gBase 1 S hδ₀_lt hδS := by
    rfl
  have hcoreY :
      deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ₀_lt hreal y =
        deTurckSmoothN (I := I) (M := M) g gBase 1 S' hδ₀_lt hδS' := by
    rfl
  rw [hcoreX, hcoreY]
  refine hbase.trans ?_
  have htop := mul_le_mul_of_nonneg_left hdiff3 (mul_nonneg hCtop hR)
  have hlow := mul_le_mul_of_nonneg_left hdiff2 (hB0 R hR)
  have hhigh := add_le_add hS3 hS3'
  have hprod := mul_le_mul hhigh hdiff2 (norm_nonneg _)
    (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have hmixed :
      B1 R *
          (‖smoothCcToTensorHs (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2) S‖ +
            ‖smoothCcToTensorHs (I := I) (M := M) g
              (((1 : ℕ) : ℝ) + 2) S'‖) *
        ‖smoothCcToTensorHs (I := I) (M := M) g
          (((1 : ℕ) : ℝ) + 1) (S - S')‖ ≤
      B1 R *
          (‖(x.1.1 : TensorHs (I := I) (M := M) g 0 2
            (((1 : ℕ) : ℝ) + 2))‖ +
            ‖(y.1.1 : TensorHs (I := I) (M := M) g 0 2
              (((1 : ℕ) : ℝ) + 2))‖) *
        ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
          (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
          ((x.1.1 : TensorHs (I := I) (M := M) g 0 2
            (((1 : ℕ) : ℝ) + 2)) - y.1.1)‖ := by
    calc
      _ = B1 R *
          ((‖smoothCcToTensorHs (I := I) (M := M) g
                (((1 : ℕ) : ℝ) + 2) S‖ +
              ‖smoothCcToTensorHs (I := I) (M := M) g
                (((1 : ℕ) : ℝ) + 2) S'‖) *
            ‖smoothCcToTensorHs (I := I) (M := M) g
              (((1 : ℕ) : ℝ) + 1) (S - S')‖) := by ring
      _ ≤ B1 R *
          ((‖(x.1.1 : TensorHs (I := I) (M := M) g 0 2
                (((1 : ℕ) : ℝ) + 2))‖ +
              ‖(y.1.1 : TensorHs (I := I) (M := M) g 0 2
                (((1 : ℕ) : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
              (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
              ((x.1.1 : TensorHs (I := I) (M := M) g 0 2
                (((1 : ℕ) : ℝ) + 2)) - y.1.1)‖) :=
        mul_le_mul_of_nonneg_left hprod (hB1 R hR)
      _ = _ := by ring
  exact add_le_add (add_le_add htop hlow) hmixed

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
