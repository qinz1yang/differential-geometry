import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.DenseSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Uniform.TameEstimates

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

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
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear
open DifferentialGeometry.Analysis.Spectral.MetricRealization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

theorem coreN_outer_uniform
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ ρ Ctop : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧
      (∀ Q : ℝ, 0 ≤ Q → 0 ≤ B0 Q) ∧
      (∀ Q : ℝ, 0 ≤ Q → 0 ≤ B1 Q) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ {Q R : ℝ} (_hQ : 0 ≤ Q) (_hQρ : Q ≤ ρ)
          (_hR : 0 ≤ R) (hRQ : R ≤ Q)
          (hrealQ : ∀ T : SmoothCcTensor g 0 2,
            ‖smoothCcToTensorHs (I := I) (M := M) g
              (((1 : ℕ) : ℝ) + 1) T‖ ≤ Q →
              gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) δ₀)
          (x y : smoothCore (I := I) (M := M) g R),
          ‖deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ₀_lt
                (realizeOfLE (I := I) (M := M) g hRQ hrealQ) x -
              deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ₀_lt
                (realizeOfLE (I := I) (M := M) g hRQ hrealQ) y‖ ≤
            Ctop * Q *
                ‖(x.1.1 : TensorHs (I := I) (M := M) g 0 2
                  (((1 : ℕ) : ℝ) + 2)) - y.1.1‖ +
              B0 Q *
                ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                  (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                  ((x.1.1 : TensorHs (I := I) (M := M) g 0 2
                    (((1 : ℕ) : ℝ) + 2)) - y.1.1)‖ +
              B1 Q *
                  (‖(x.1.1 : TensorHs (I := I) (M := M) g 0 2
                    (((1 : ℕ) : ℝ) + 2))‖ +
                    ‖(y.1.1 : TensorHs (I := I) (M := M) g 0 2
                      (((1 : ℕ) : ℝ) + 2))‖) *
                ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                  (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                  ((x.1.1 : TensorHs (I := I) (M := M) g 0 2
                    (((1 : ℕ) : ℝ) + 2)) - y.1.1)‖ := by
  obtain ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, hcore⟩ :=
    deTurckRemainderOnSmoothCore_tame_uniform_bound (I := I) (M := M) hDim gBase hΛ
      hδ₀_nonneg hδ₀_lt
  refine ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, ?_⟩
  intro g hEq hjet Q R hQ hQρ hR hRQ hrealQ x y
  let xQ0 : lowerState (I := I) (M := M) g 1 Q :=
    ⟨x.1.1, x.1.2.trans hRQ⟩
  let yQ0 : lowerState (I := I) (M := M) g 1 Q :=
    ⟨y.1.1, y.1.2.trans hRQ⟩
  let xQ : smoothCore (I := I) (M := M) g Q := ⟨xQ0, x.2⟩
  let yQ : smoothCore (I := I) (M := M) g Q := ⟨yQ0, y.2⟩
  have hxrep : coreRep g xQ = coreRep g x := by
    apply smoothHs_inj (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2)
    rw [coreRep_spec, coreRep_spec]
  have hyrep : coreRep g yQ = coreRep g y := by
    apply smoothHs_inj (I := I) (M := M) g (((1 : ℕ) : ℝ) + 2)
    rw [coreRep_spec, coreRep_spec]
  have hxN :
      deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ₀_lt hrealQ xQ =
        deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ₀_lt
          (realizeOfLE (I := I) (M := M) g hRQ hrealQ) x := by
    unfold deTurckRemainderOnSmoothCore
    apply smoothN_wd (I := I) (M := M) g gBase 1
    rw [hxrep]
  have hyN :
      deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ₀_lt hrealQ yQ =
        deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ₀_lt
          (realizeOfLE (I := I) (M := M) g hRQ hrealQ) y := by
    unfold deTurckRemainderOnSmoothCore
    apply smoothN_wd (I := I) (M := M) g gBase 1
    rw [hyrep]
  have hbound := hcore g hEq hjet hQ hQρ hrealQ xQ yQ
  rw [hxN, hyN] at hbound
  simpa only [xQ, yQ, xQ0, yQ0] using hbound

theorem deTurckRemainderOnLowerState_outer_uniform_bound
    (hDim : Module.finrank ℝ E = 3)
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ ρ Ctop : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧
      (∀ Q : ℝ, 0 ≤ Q → 0 ≤ B0 Q) ∧
      (∀ Q : ℝ, 0 ≤ Q → 0 ≤ B1 Q) ∧
      ∀ g : SmoothRiemannianMetric I M,
        MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
        (∀ a : ℕ, a ≤ 3 →
          MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
        ∀ {Q R : ℝ} (_hQ : 0 ≤ Q) (_hQρ : Q ≤ ρ)
          (hR : 0 < R) (hRQ : R ≤ Q)
          (hrealQ : ∀ T : SmoothCcTensor g 0 2,
            ‖smoothCcToTensorHs (I := I) (M := M) g
              (((1 : ℕ) : ℝ) + 1) T‖ ≤ Q →
              gFibreOpBound (I := I) (M := M) g
                (ccTensorBilinSymm (I := I) g T) δ₀),
          Continuous (deTurckRemainderOnLowerState (I := I) (M := M) g gBase hR hδ₀_lt
            (realizeOfLE (I := I) (M := M) g hRQ hrealQ)) ∧
          Continuous (deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ₀_lt
            (realizeOfLE (I := I) (M := M) g hRQ hrealQ)) ∧
          ∀ u v : lowerState (I := I) (M := M) g 1 R,
            ‖deTurckRemainderOnLowerState (I := I) (M := M) g gBase hR hδ₀_lt
                  (realizeOfLE (I := I) (M := M) g hRQ hrealQ) u -
                deTurckRemainderOnLowerState (I := I) (M := M) g gBase hR hδ₀_lt
                  (realizeOfLE (I := I) (M := M) g hRQ hrealQ) v‖ ≤
              Ctop * Q *
                  ‖(u.1 : TensorHs (I := I) (M := M) g 0 2
                    (((1 : ℕ) : ℝ) + 2)) - v.1‖ +
                B0 Q *
                  ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                    (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                    ((u.1 : TensorHs (I := I) (M := M) g 0 2
                      (((1 : ℕ) : ℝ) + 2)) - v.1)‖ +
                B1 Q *
                    (‖(u.1 : TensorHs (I := I) (M := M) g 0 2
                      (((1 : ℕ) : ℝ) + 2))‖ +
                      ‖(v.1 : TensorHs (I := I) (M := M) g 0 2
                        (((1 : ℕ) : ℝ) + 2))‖) *
                  ‖tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
                    (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
                    ((u.1 : TensorHs (I := I) (M := M) g 0 2
                      (((1 : ℕ) : ℝ) + 2)) - v.1)‖ := by
  obtain ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, hcore⟩ :=
    coreN_outer_uniform (I := I) (M := M) hDim gBase hΛ
      hδ₀_nonneg hδ₀_lt
  refine ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, ?_⟩
  intro g hEq hjet Q R hQ hQρ hR hRQ hrealQ
  let hrealR := realizeOfLE (I := I) (M := M) g hRQ hrealQ
  let D : Set (lowerState (I := I) (M := M) g 1 R) :=
    smoothCore (I := I) (M := M) g R
  let F : D → TensorHs (I := I) (M := M) g 0 2 ((1 : ℕ) : ℝ) :=
    deTurckRemainderOnSmoothCore (I := I) (M := M) g gBase hδ₀_lt hrealR
  let e : lowerState (I := I) (M := M) g 1 R →
      TensorHs (I := I) (M := M) g 0 2
        (((1 : ℕ) : ℝ) + 2) := fun u => u.1
  let J := tensorHsInclusion (I := I) (M := M) (g := g) (r := 0) (s := 2)
    (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
  let z : lowerState (I := I) (M := M) g 1 R :=
    ⟨0, zero_mem_lowerState (I := I) (M := M) g 1 hR.le⟩
  have hD : Dense D := by
    simpa only [D] using smoothCore_dense (I := I) (M := M) g hR
  have htame : ∀ x y : D,
      ‖F x - F y‖ ≤
        Ctop * Q * ‖e x.1 - e y.1‖ +
          B0 Q * ‖J (e x.1 - e y.1)‖ +
          B1 Q * (‖e x.1‖ + ‖e y.1‖) * ‖J (e x.1 - e y.1)‖ := by
    intro x y
    simpa only [D, F, e, J, hrealR] using
      hcore g hEq hjet hQ hQρ hR.le hRQ hrealQ x y
  have he : Isometry e := by
    exact isometry_subtype_coe
  have he0 : e z = 0 := rfl
  have hball : ∀ r : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F
        {x : D | dist (x : lowerState (I := I) (M := M) g 1 R) z ≤ r} :=
    tame_lip_balls F z e he he0 J Ctop (B0 Q) (B1 Q) Q
      hCtop (hB0 Q hQ) (hB1 Q hQ) hQ htame
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro d
    let r : ℝ := dist (d : lowerState (I := I) (M := M) g 1 R) z + 1
    obtain ⟨K, hK⟩ := hball r
    have hdball : (d : lowerState (I := I) (M := M) g 1 R) ∈
        Metric.ball z r := by
      rw [Metric.mem_ball]
      dsimp only [r]
      linarith
    have hclosed : Metric.closedBall z r ∈
        𝓝 (d : lowerState (I := I) (M := M) g 1 R) :=
      Metric.closedBall_mem_nhds_of_mem hdball
    have hpre : ((↑) : D → lowerState (I := I) (M := M) g 1 R) ⁻¹'
        Metric.closedBall z r ∈ 𝓝 d :=
      continuousAt_subtype_val.preimage_mem_nhds hclosed
    have hd : d ∈ {x : D |
        dist (x : lowerState (I := I) (M := M) g 1 R) z ≤ r} := by
      change dist (d : lowerState (I := I) (M := M) g 1 R) z ≤
        dist (d : lowerState (I := I) (M := M) g 1 R) z + 1
      linarith
    apply (hK.continuousOn d hd).continuousAt
    change ((↑) : D → lowerState (I := I) (M := M) g 1 R) ⁻¹'
      Metric.closedBall z r ∈ 𝓝 d
    exact hpre
  have hcont := dense_cont_on_balls hD F z hball
  have hfull := dense_tame_extend hD F z hball e continuous_subtype_val J
    Ctop (B0 Q) (B1 Q) Q htame
  refine ⟨?_, ?_, ?_⟩
  · simpa only [deTurckRemainderOnLowerState, D, F, hrealR] using hcont
  · simpa only [D, F, hrealR] using hFcont
  · intro u v
    simpa only [deTurckRemainderOnLowerState, D, F, e, J, hrealR] using hfull u v

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
