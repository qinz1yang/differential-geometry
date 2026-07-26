import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegCoreTame
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegRealize
import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.TameForcingFixedPoint

/-!
# Dense low-regularity Ricci--DeTurck solver

This module extends the genuine smooth Ricci--DeTurck nonlinearity from the
dense smooth core to the complete lower `H2` state ball.  Coefficients are
frozen on an outer lower radius `Q`, while the actual solver state radius
`R <= Q` is chosen afterwards.  This separates the two contraction
requirements: `Ctop * Q` controls the top arm and `B1 Q * R` controls the
high-size times lower-difference arm.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

/-- The `H2` realization radius with its fibre bound fixed at the positive
DeTurck contraction threshold. -/
private theorem realize_at_thr
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) :
    ∃ R : ℝ, 0 < R ∧
      ∀ T : SmoothCcTensor g 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T‖ ≤ R →
          gFibreOpBound (I := I) (M := M) g
            (ccTensorBilinSymm (I := I) g T)
              (deTurckArmContractionThreshold'' (Module.finrank ℝ E)) := by
  obtain ⟨C, hC, hOp⟩ := hs2_op_bound (I := I) (M := M) hDim g
  let θ : ℝ := deTurckArmContractionThreshold'' (Module.finrank ℝ E)
  have hθ : 0 < θ := deTurckArmContractionThreshold''_pos (Module.finrank ℝ E)
  refine ⟨θ / C, div_pos hθ hC, ?_⟩
  intro T hT
  have htwo : ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T =
      smoothCcToTensorHs (I := I) (M := M) g (2 : ℝ) T :=
    tensorHs.ext (funext (fun _ ↦ rfl))
  have hT' : ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ θ / C := by
    simpa only [htwo] using hT
  have hdelta : C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ θ := by
    calc
      C * ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖
          ≤ C * (θ / C) := mul_le_mul_of_nonneg_left hT' hC.le
      _ = θ := by field_simp
  have hsmall := hOp T
  intro x v w
  refine (hsmall x v w).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hdelta (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

/-- A realization bound valid on an outer radius restricts to every smaller
lower-state radius. -/
def realizeOfLE
    (g₀ : SmoothRiemannianMetric I M) {δ R Q : ℝ} (hRQ : R ≤ Q)
    (hrealQ : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T‖ ≤ Q →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ :=
  fun T hT => hrealQ T (hT.trans hRQ)

/-- The genuine lower-state nonlinearity is the dense extension of `coreN`
from the smooth part of the same state ball. -/
def lowRegN
    (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ} (hR : 0 < R)
    (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T‖ ≤ R →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    lowerState (I := I) (M := M) g₀ 1 R →
      tensorHs (I := I) (M := M) g₀ 0 2 (1 : ℝ) :=
  Dense.extend (smoothCore_dense (I := I) (M := M) g₀ hR)
    (coreN (I := I) (M := M) g₀ g_bg hδ hreal)

/-- The core estimate may be frozen at an outer coefficient radius `Q` and
then restricted to a smaller state ball `R`. -/
theorem coreN_outer
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ ρ Ctop : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧
      (∀ Q : ℝ, 0 ≤ Q → 0 ≤ B0 Q) ∧
      (∀ Q : ℝ, 0 ≤ Q → 0 ≤ B1 Q) ∧
      ∀ {Q R : ℝ} (hQ : 0 ≤ Q) (hQρ : Q ≤ ρ)
        (hR : 0 ≤ R) (hRQ : R ≤ Q)
        (hrealQ : ∀ T : SmoothCcTensor g₀ 0 2,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T‖ ≤ Q →
            gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ T) δ₀)
        (x y : smoothCore (I := I) (M := M) g₀ R),
        ‖coreN (I := I) (M := M) g₀ g_bg hδ₀_lt
              (realizeOfLE (I := I) (M := M) g₀ hRQ hrealQ) x -
            coreN (I := I) (M := M) g₀ g_bg hδ₀_lt
              (realizeOfLE (I := I) (M := M) g₀ hRQ hrealQ) y‖ ≤
          Ctop * Q *
              ‖(x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - y.1.1‖ +
            B0 Q *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (2 : ℝ) ≤ 3 by norm_num)
                ((x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - y.1.1)‖ +
            B1 Q *
                (‖(x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖ +
                  ‖(y.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖) *
              ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                (show (2 : ℝ) ≤ 3 by norm_num)
                ((x.1.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - y.1.1)‖ := by
  obtain ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, hcore⟩ :=
    coreN_tame (I := I) (M := M) hDim g₀ g_bg hδ₀_nonneg hδ₀_lt
  refine ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, ?_⟩
  intro Q R hQ hQρ hR hRQ hrealQ x y
  let xQ0 : lowerState (I := I) (M := M) g₀ 1 Q :=
    ⟨x.1.1, x.1.2.trans hRQ⟩
  let yQ0 : lowerState (I := I) (M := M) g₀ 1 Q :=
    ⟨y.1.1, y.1.2.trans hRQ⟩
  let xQ : smoothCore (I := I) (M := M) g₀ Q := ⟨xQ0, x.2⟩
  let yQ : smoothCore (I := I) (M := M) g₀ Q := ⟨yQ0, y.2⟩
  have hxrep : coreRep g₀ xQ = coreRep g₀ x := by
    apply smoothHs_inj (I := I) (M := M) g₀ (3 : ℝ)
    rw [coreRep_spec, coreRep_spec]
    rfl
  have hyrep : coreRep g₀ yQ = coreRep g₀ y := by
    apply smoothHs_inj (I := I) (M := M) g₀ (3 : ℝ)
    rw [coreRep_spec, coreRep_spec]
    rfl
  have hxN :
      coreN (I := I) (M := M) g₀ g_bg hδ₀_lt hrealQ xQ =
        coreN (I := I) (M := M) g₀ g_bg hδ₀_lt
          (realizeOfLE (I := I) (M := M) g₀ hRQ hrealQ) x := by
    unfold coreN
    rw [hxrep]
  have hyN :
      coreN (I := I) (M := M) g₀ g_bg hδ₀_lt hrealQ yQ =
        coreN (I := I) (M := M) g₀ g_bg hδ₀_lt
          (realizeOfLE (I := I) (M := M) g₀ hRQ hrealQ) y := by
    unfold coreN
    rw [hyrep]
  have hbound := hcore hQ hQρ hrealQ xQ yQ
  rw [hxN, hyN] at hbound
  simpa only [xQ, yQ, xQ0, yQ0] using hbound

/-- The dense extension is continuous on the full lower-state ball and keeps
the outer-radius three-arm estimate. -/
theorem lowRegN_outer
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M)
    {δ₀ : ℝ} (hδ₀_nonneg : 0 ≤ δ₀) (hδ₀_lt : δ₀ < 1) :
    ∃ ρ Ctop : ℝ, ∃ B0 B1 : ℝ → ℝ,
      0 < ρ ∧ 0 ≤ Ctop ∧
      (∀ Q : ℝ, 0 ≤ Q → 0 ≤ B0 Q) ∧
      (∀ Q : ℝ, 0 ≤ Q → 0 ≤ B1 Q) ∧
      ∀ {Q R : ℝ} (hQ : 0 ≤ Q) (hQρ : Q ≤ ρ)
        (hR : 0 < R) (hRQ : R ≤ Q)
        (hrealQ : ∀ T : SmoothCcTensor g₀ 0 2,
          ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T‖ ≤ Q →
            gFibreOpBound (I := I) (M := M) g₀
              (ccTensorBilinSymm (I := I) g₀ T) δ₀),
        Continuous (lowRegN (I := I) (M := M) g₀ g_bg hR hδ₀_lt
          (realizeOfLE (I := I) (M := M) g₀ hRQ hrealQ)) ∧
        Continuous (coreN (I := I) (M := M) g₀ g_bg hδ₀_lt
          (realizeOfLE (I := I) (M := M) g₀ hRQ hrealQ)) ∧
        ∀ u v : lowerState (I := I) (M := M) g₀ 1 R,
          ‖lowRegN (I := I) (M := M) g₀ g_bg hR hδ₀_lt
                (realizeOfLE (I := I) (M := M) g₀ hRQ hrealQ) u -
              lowRegN (I := I) (M := M) g₀ g_bg hR hδ₀_lt
                (realizeOfLE (I := I) (M := M) g₀ hRQ hrealQ) v‖ ≤
            Ctop * Q * ‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - v.1‖ +
              B0 Q *
                ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show (2 : ℝ) ≤ 3 by norm_num)
                  ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - v.1)‖ +
              B1 Q *
                  (‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖ +
                    ‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖) *
                ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
                  (show (2 : ℝ) ≤ 3 by norm_num)
                  ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - v.1)‖ := by
  obtain ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, hcore⟩ :=
    coreN_outer (I := I) (M := M) hDim g₀ g_bg hδ₀_nonneg hδ₀_lt
  refine ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, ?_⟩
  intro Q R hQ hQρ hR hRQ hrealQ
  let hrealR := realizeOfLE (I := I) (M := M) g₀ hRQ hrealQ
  let D : Set (lowerState (I := I) (M := M) g₀ 1 R) :=
    smoothCore (I := I) (M := M) g₀ R
  let F : D → tensorHs (I := I) (M := M) g₀ 0 2 (1 : ℝ) :=
    coreN (I := I) (M := M) g₀ g_bg hδ₀_lt hrealR
  let e : lowerState (I := I) (M := M) g₀ 1 R →
      tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ) := fun u => u.1
  let J := tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
    (show (2 : ℝ) ≤ 3 by norm_num)
  let z : lowerState (I := I) (M := M) g₀ 1 R :=
    ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩
  have hD : Dense D := by
    simpa only [D] using smoothCore_dense (I := I) (M := M) g₀ hR
  have htame : ∀ x y : D,
      ‖F x - F y‖ ≤
        Ctop * Q * ‖e x.1 - e y.1‖ +
          B0 Q * ‖J (e x.1 - e y.1)‖ +
          B1 Q * (‖e x.1‖ + ‖e y.1‖) * ‖J (e x.1 - e y.1)‖ := by
    intro x y
    simpa only [D, F, e, J, hrealR] using
      hcore hQ hQρ hR.le hRQ hrealQ x y
  have he : Isometry e := by
    exact isometry_subtype_coe
  have he0 : e z = 0 := rfl
  have hball : ∀ r : ℝ, ∃ K : ℝ≥0,
      LipschitzOnWith K F {x : D | dist (x : lowerState (I := I) (M := M) g₀ 1 R) z ≤ r} :=
    tame_lip_balls F z e he he0 J Ctop (B0 Q) (B1 Q) Q
      hCtop (hB0 Q hQ) (hB1 Q hQ) hQ htame
  have hFcont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro d
    let r : ℝ := dist (d : lowerState (I := I) (M := M) g₀ 1 R) z + 1
    obtain ⟨K, hK⟩ := hball r
    have hdball : (d : lowerState (I := I) (M := M) g₀ 1 R) ∈
        Metric.ball z r := by
      rw [Metric.mem_ball]
      dsimp only [r]
      linarith
    have hclosed : Metric.closedBall z r ∈
        𝓝 (d : lowerState (I := I) (M := M) g₀ 1 R) :=
      Metric.closedBall_mem_nhds_of_mem hdball
    have hpre : ((↑) : D → lowerState (I := I) (M := M) g₀ 1 R) ⁻¹'
        Metric.closedBall z r ∈ 𝓝 d :=
      continuousAt_subtype_val.preimage_mem_nhds hclosed
    have hd : d ∈ {x : D |
        dist (x : lowerState (I := I) (M := M) g₀ 1 R) z ≤ r} := by
      change dist (d : lowerState (I := I) (M := M) g₀ 1 R) z ≤
        dist (d : lowerState (I := I) (M := M) g₀ 1 R) z + 1
      linarith
    apply (hK.continuousOn d hd).continuousAt
    simpa only [Metric.mem_closedBall, Set.mem_setOf_eq] using hpre
  have hcont := dense_cont_on_balls hD F z hball
  have hfull := dense_tame_extend hD F z hball e continuous_subtype_val J
    Ctop (B0 Q) (B1 Q) Q htame
  refine ⟨?_, ?_, ?_⟩
  · simpa only [lowRegN, D, F, hrealR] using hcont
  · simpa only [D, F, hrealR] using hFcont
  · intro u v
    simpa only [lowRegN, D, F, e, J, hrealR] using hfull u v

/-- In dimension three, the genuine lower-regularity Ricci--DeTurck
nonlinearity has a positive-radius fixed-background maximal-regularity
solution.  The outer radius controls the top arm, and the smaller state
radius controls the high-size times lower-difference arm. -/
theorem lowreg_partial_sol
    (hDim : Module.finrank ℝ E = 3)
    (g₀ g_bg : SmoothRiemannianMetric I M) :
    ∃ (R δ : ℝ) (hR : 0 < R) (hδ : δ < 1)
      (hrealR : ∀ S : SmoothCcTensor g₀ 0 2,
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) S‖ ≤ R →
          gFibreOpBound (I := I) (M := M) g₀
            (ccTensorBilinSymm (I := I) g₀ S) δ),
      let Nfun := lowRegN (I := I) (M := M) g₀ g_bg hR hδ hrealR
      Continuous Nfun ∧
        Continuous (coreN (I := I) (M := M) g₀ g_bg hδ hrealR) ∧
        ∃ T₀ : ℝ, 0 < T₀ ∧
          ∀ {T : ℝ} (hT : 0 < T) (hTT₀ : T ≤ T₀) (hT1 : T ≤ 1),
          ∃ (u : MaxRegSolutionSpace (I := I) (M := M) (1 : ℝ) T)
            (gforce : timeL2
              (tensorHs (I := I) (M := M) g₀ 0 2 (1 : ℝ)) T),
            let field := maxRegDuhamelSolField (I := I) (M := M) (1 : ℝ) hT hT1
              (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℝ) + 2)) gforce
            u = maxRegDuhamelMap (I := I) (M := M) (1 : ℝ) hT hT1
                (0 : tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℝ) + 2)) gforce ∧
              (∀ᵐ t ∂(timeMeasure T),
                field t ∈ lowerState (I := I) (M := M) g₀ 1 R) ∧
              gforce =ᵐ[timeMeasure T]
                (fun t => Nfun (aeSetLift
                  (zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le) field t)) ∧
              timeH1.trace0 _ T u = 0 ∧
              timeH1.timeDeriv _ T u =
                timeScaleLaplacian (I := I) (M := M) (1 : ℝ) field + gforce ∧
              ‖gforce‖ ≤ R / 4 := by
  let θ : ℝ := deTurckArmContractionThreshold'' (Module.finrank ℝ E)
  have hθ : 0 < θ := deTurckArmContractionThreshold''_pos (Module.finrank ℝ E)
  have hθlt : θ < 1 :=
    deTurckArmContractionThreshold''_lt_one' (Module.finrank ℝ E)
  obtain ⟨ρ, Ctop, B0, B1, hρ, hCtop, hB0, hB1, houter⟩ :=
    lowRegN_outer (I := I) (M := M) hDim g₀ g_bg hθ.le hθlt
  obtain ⟨P, hP, hprealθ⟩ := realize_at_thr (I := I) (M := M) hDim g₀
  let Q : ℝ := min (ρ / 2) (min (P / 2) (1 / (32 * (Ctop + 1))))
  have hQ : 0 < Q := by
    refine lt_min (div_pos hρ (by norm_num)) ?_
    refine lt_min (div_pos hP (by norm_num)) ?_
    exact one_div_pos.mpr (mul_pos (by norm_num) (by linarith))
  have hQρhalf : Q ≤ ρ / 2 := min_le_left _ _
  have hQρ : Q ≤ ρ := by linarith
  have hQPhalf : Q ≤ P / 2 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hQP : Q ≤ P := by linarith
  have hQcap : Q ≤ 1 / (32 * (Ctop + 1)) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hCtop1 : 0 < Ctop + 1 := by linarith
  have htopQ : Ctop * Q ≤ 1 / 16 := by
    calc
      Ctop * Q ≤ Ctop * (1 / (32 * (Ctop + 1))) :=
        mul_le_mul_of_nonneg_left hQcap hCtop
      _ ≤ (Ctop + 1) * (1 / (32 * (Ctop + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / 32 := by field_simp [ne_of_gt hCtop1]
      _ ≤ 1 / 16 := by norm_num
  have hrealQ : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (2 : ℝ) T‖ ≤ Q →
        gFibreOpBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) θ := by
    intro T hT
    exact hprealθ T (hT.trans hQP)
  have hB1Q : 0 ≤ B1 Q := hB1 Q hQ.le
  let R : ℝ := min (Q / 2) (1 / (32 * (B1 Q + 1)))
  have hR : 0 < R := by
    refine lt_min (div_pos hQ (by norm_num)) ?_
    exact one_div_pos.mpr (mul_pos (by norm_num) (by linarith))
  have hRQhalf : R ≤ Q / 2 := min_le_left _ _
  have hRQ : R ≤ Q := by linarith
  have hRcap : R ≤ 1 / (32 * (B1 Q + 1)) := min_le_right _ _
  have hB1Q1 : 0 < B1 Q + 1 := by linarith
  have hhighR : B1 Q * R ≤ 1 / 16 := by
    calc
      B1 Q * R ≤ B1 Q * (1 / (32 * (B1 Q + 1))) :=
        mul_le_mul_of_nonneg_left hRcap hB1Q
      _ ≤ (B1 Q + 1) * (1 / (32 * (B1 Q + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / 32 := by field_simp [ne_of_gt hB1Q1]
      _ ≤ 1 / 16 := by norm_num
  let hrealR := realizeOfLE (I := I) (M := M) g₀ hRQ hrealQ
  let Nfun : lowerState (I := I) (M := M) g₀ 1 R →
      tensorHs (I := I) (M := M) g₀ 0 2 (1 : ℝ) :=
    lowRegN (I := I) (M := M) g₀ g_bg hR hθlt hrealR
  obtain ⟨hcont0, hcorecont0, hbound0⟩ := houter hQ.le hQρ hR hRQ hrealQ
  have hcont : Continuous Nfun := by
    simpa only [Nfun, hrealR] using hcont0
  have hcorecont : Continuous
      (coreN (I := I) (M := M) g₀ g_bg hθlt hrealR) := by
    simpa only [hrealR] using hcorecont0
  have hbound : ∀ u v : lowerState (I := I) (M := M) g₀ 1 R,
      ‖Nfun u - Nfun v‖ ≤
        Ctop * Q * ‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - v.1‖ +
          B0 Q *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (2 : ℝ) ≤ 3 by norm_num)
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - v.1)‖ +
          B1 Q *
              (‖(u.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖ +
                ‖(v.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (2 : ℝ) ≤ 3 by norm_num)
              ((u.1 : tensorHs (I := I) (M := M) g₀ 0 2 (3 : ℝ)) - v.1)‖ := by
    simpa only [Nfun, hrealR] using hbound0
  let A : ℝ≥0 := Real.toNNReal (Ctop * Q / R)
  let B : ℝ≥0 := Real.toNNReal (B0 Q)
  let C : ℝ≥0 := Real.toNNReal (B1 Q)
  have hAarg : 0 ≤ Ctop * Q / R :=
    div_nonneg (mul_nonneg hCtop hQ.le) hR.le
  have hAcoe : (A : ℝ) = Ctop * Q / R :=
    Real.coe_toNNReal _ hAarg
  have hBcoe : (B : ℝ) = B0 Q :=
    Real.coe_toNNReal _ (hB0 Q hQ.le)
  have hCcoe : (C : ℝ) = B1 Q :=
    Real.coe_toNNReal _ hB1Q
  have hAR : (A : ℝ) * R = Ctop * Q := by
    rw [hAcoe]
    exact div_mul_cancel₀ _ hR.ne'
  have hsmallA : (A : ℝ) * R ≤ 1 / 16 := by
    rw [hAR]
    exact htopQ
  have hsmallC : (C : ℝ) * R ≤ 1 / 16 := by
    rw [hCcoe]
    exact hhighR
  have hsingle : ∀ u v : lowerState (I := I) (M := M) g₀ 1 R,
      ‖Nfun u - Nfun v‖ ≤
        (A : ℝ) * R *
            ‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℝ) + 2)) - (v : _)‖ +
          (B : ℝ) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith) ((u : _) - (v : _))‖ +
          (C : ℝ) *
              (‖(u : tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℝ) + 2))‖ +
                ‖(v : tensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℝ) + 2))‖) *
            ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
              (show (1 : ℝ) + 1 ≤ (1 : ℝ) + 2 by linarith) ((u : _) - (v : _))‖ := by
    intro u v
    rw [hAR, hBcoe, hCcoe]
    convert hbound u v using 1 <;> norm_num
  let D : ℝ :=
    ‖Nfun ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩‖
  have hD : 0 ≤ D := norm_nonneg _
  have hzero :
      ‖Nfun ⟨0, zero_mem_lowerState (I := I) (M := M) g₀ 1 hR.le⟩‖ ≤ D :=
    le_rfl
  obtain ⟨T₀, _hT₀eq, hT₀, hsol⟩ :=
    partial_sol_tame (I := I) (M := M) g₀ 1 hR Nfun hcont
      A B C D hD hzero hsmallA hsmallC hsingle
  refine ⟨R, θ, hR, hθlt, hrealR, ?_⟩
  change Continuous Nfun ∧ _
  refine ⟨hcont, hcorecont, T₀, hT₀, ?_⟩
  intro T hT hTT₀ hT1
  simpa only [Nat.cast_one] using hsol hT hTT₀ hT1

end DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral

end
