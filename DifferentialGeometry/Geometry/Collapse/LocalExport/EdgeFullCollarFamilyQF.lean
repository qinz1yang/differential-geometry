import DifferentialGeometry.Geometry.Collapse.EdgeFullCollarFamily
import DifferentialGeometry.Geometry.Collapse.EdgeScaledSmoothing
import DifferentialGeometry.Geometry.Collapse.EdgeRowSequence
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothDirections

/-!
# The edge full-collar family with LFR27's clauses of the shared smoothing exported (QF re-chain)

F7-EDGE's `exists_edge_full_collar_family` (`EdgeFullCollarFamily.lean`, frozen) builds ONE
smoothing `F` of the distance to the closed weak edge set with `exists_shared_low_collar_smoothing`
and keeps only its value clause. The LFR28 row (`exists_edgeDiskPacket_threshold`) needs, at every
centre `p` and in its normalization `(ρ(p)⁻¹ d, ρ(p)⁻² g)` with `F_p = F/ρ(p)`, `ρ_p = ρ/ρ(p)`, the
LFR27 clauses L1–L5 of lane LC87's list (`build-logs/resume/state-LC87.md`):

* `normalized_edge_lfr27_clauses_QF` (kernel): the physical low-collar output at one centre gives
  L1 `|F_p - d_A| < μΔ`, L2 an open `O ⊇ B̄(p, 20Δ) ∩ {3Δ/4 ≤ d_A ≤ 21Δ/2}` with `F_p` smooth on it,
  L3 the gradient clause against every minimizing direction (finite-order vocabulary, through
  `minimizingDirectionsTo_eq_setOf_expMap`), L4 the quotient clause `≤ 100ΔΛ` (from the Lipschitz
  bounds, `sqrt_gInner_gradFun_div_sub_le`), L5 the smooth core of `edgeRowHeight Δ F_p ρ_p`.
* `exists_edge_full_collar_family_QF`: `exists_edge_full_collar_family` (same binders, same proof)
  with L1–L5 added to the per-centre conclusion.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Topology
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Kernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [hM : CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **QF kernel.** The physical low-collar clauses of a smoothing `F` at one centre `p` give
LC87's normalized clauses L1–L5 for `F_p = F/ρ(p)`, `ρ_p = ρ/ρ(p)`. -/
theorem normalized_edge_lfr27_clauses_QF (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) g) {A O : Set M} {F ρ : M → ℝ} {p : M}
    {Δ ε μ : ℝ} {Λ : ℝ≥0} (hρpos : ∀ x, 0 < ρ x) (hΔ : 0 < Δ) (hε : 0 < ε) (hε1 : ε < 1 / 100)
    (hμ1 : μ ≤ 1 / 100) (hlam : 100 * Δ * Λ ≤ 1 / 100) (hO : IsOpen O)
    (hFO : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O) (hF0 : ∀ x, 0 ≤ F x)
    (hFL : LipschitzWith (Real.toNNReal (1 + ε)) F) (hρ : LipschitzWith Λ ρ)
    (hρs : ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ)
    (hval : ∀ x, |F x - infDist x A| < μ * (Δ * ρ p))
    (hCO : closedBall p (20 * (Δ * ρ p)) ∩ {x | Δ * ρ p / 25 ≤ infDist x A ∧
      infDist x A ≤ 21 / 2 * (Δ * ρ p)} ⊆ O)
    (hgrad : ∀ x ∈ closedBall p (20 * (Δ * ρ p)) ∩ {x | Δ * ρ p / 25 ≤ infDist x A ∧
        infDist x A ≤ 21 / 2 * (Δ * ρ p)}, ∀ v ∈ minimizingDirectionsTo g hEnorm A x,
      Real.sqrt (g.inner x (gradFun g F x + v) (gradFun g F x + v)) < ε)
    (hcore : ∀ x ∈ ball p (20 * (Δ * ρ p)), infDist x A < 41 / 4 * (Δ * ρ p) →
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞
        (fun y => Δ * DifferentialGeometry.Analysis.edgeSublevelProfile (F y / ρ y / Δ)) x) :
    (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
    letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
    letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
    letI : IsRiemannianManifold I M :=
      radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
    letI : CompleteSpace M :=
      (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hM
    let gR : SmoothRiemannianMetric I M :=
      scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
    (∀ x, |F x / ρ p - infDist x A| < μ * Δ) ∧
    (∃ OF : Set M, IsOpen OF ∧
      closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ} ⊆ OF ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => F x / ρ p) OF) ∧
    (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
      ∀ u ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo gR A y,
        Real.sqrt (gR.inner y (gradFun gR (fun x => F x / ρ p) y + u)
          (gradFun gR (fun x => F x / ρ p) y + u)) < ε) ∧
    (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
      Real.sqrt (gR.inner y
        (gradFun gR (fun z => F z / ρ p / (ρ z / ρ p)) y - gradFun gR (fun x => F x / ρ p) y)
        (gradFun gR (fun z => F z / ρ p / (ρ z / ρ p)) y - gradFun gR (fun x => F x / ρ p) y))
        ≤ 100 * Δ * Λ) ∧
    ∀ x ∈ ball p (20 * Δ), infDist x A < 41 / 4 * Δ →
      ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ (fun x => F x / ρ p) (fun x => ρ x / ρ p)) x) := by
  have hr : 0 < ρ p := hρpos p
  have hri : 0 < (ρ p)⁻¹ := inv_pos.mpr hr
  have hCOR := radialScaled_collar_subset hr hCO
  have hFLR := radialScaled_div_lipschitzWith hFL hr
  have hρR := lipschitzWith_normalized_scale hρ hr
  have hCC := radialScaled_collar_subset (A := A) (p := p) (Δ := Δ)
    (O := closedBall p (20 * (Δ * ρ p)) ∩ {x | Δ * ρ p / 25 ≤ infDist x A ∧
      infDist x A ≤ 21 / 2 * (Δ * ρ p)}) hr subset_rfl
  have hgradR (y : M) (hy : y ∈ closedBall p (20 * (Δ * ρ p)) ∩ {x | Δ * ρ p / 25 ≤
      infDist x A ∧ infDist x A ≤ 21 / 2 * (Δ * ρ p)}) :=
    radialScaled_low_collar_gradient g hEnorm hr
      ((hFO.contMDiffAt (hO.mem_nhds (hCO hy))).mdifferentiableAt (by simp)) (hgrad y hy)
  intro hmetric
  let mR : MetricSpace M := m.rescale (ρ p)⁻¹ hri
  let _ : CompleteSpace M := (m.rescale_completeSpace_iff (ρ p)⁻¹ hri).mpr hM
  let _ := radialScaledBundle g (ρ p)⁻¹ hri
  let _ := radialScaledContinuous g (ρ p)⁻¹ hri
  let _ := radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ hri
  intro gR
  have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
  have hinfR : ∀ x : M, infDist x A = (ρ p)⁻¹ * @infDist M m.toPseudoMetricSpace x A :=
    fun x => infDist_rescale m (ρ p)⁻¹ hri x A
  have hdR : ∀ x y : M, dist x y = (ρ p)⁻¹ * @dist M m.toDist x y := fun _ _ => rfl
  -- the normalized band lies in the normalized low collar
  have hband : ∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧
      infDist y A ≤ 21 / 2 * Δ}, y ∈ closedBall p (20 * Δ) ∩ {y | Δ / 25 ≤ infDist y A ∧
      infDist y A ≤ 21 / 2 * Δ} := fun y hy => ⟨hy.1, by linarith [hy.2.1], hy.2.2⟩
  refine ⟨fun x => ?_, ⟨O, hO, fun y hy => hCOR (hband y hy), hFO.div_const _⟩,
    fun y hy u hu => ?_, fun y hy => ?_, fun x hx hxA => ?_⟩
  · -- L1
    rw [hinfR, div_eq_inv_mul, ← mul_sub, abs_mul, abs_of_pos hri, ← div_eq_inv_mul,
      div_lt_iff₀ hr]
    have h := hval x
    linarith
  · -- L3
    have hu' : u ∈ minimizingDirectionsTo gR hnR A y := by
      rw [Bundle.ContMDiffRiemannianMetric.minimizingDirectionsTo_eq_setOf_expMap gR hnR A y]
      exact hu
    exact hgradR y (hCC (hband y hy)) u hu'
  · -- L4
    have hyO : y ∈ O := hCOR (hband y hy)
    have hFd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => F x / ρ p) y :=
      (((hFO.div_const (ρ p)) y hyO).contMDiffAt (hO.mem_nhds hyO)).mdifferentiableAt (by simp)
    have hρd : MDifferentiableAt I 𝓘(ℝ, ℝ) (fun x => ρ x / ρ p) y :=
      ((hρs.div_const (ρ p)) y).mdifferentiableAt (by simp)
    have hFg := sqrt_gInner_gradFun_le_of_lipschitzWith gR hnR hFLR hFd
    have hρg := sqrt_gInner_gradFun_le_of_lipschitzWith gR hnR hρR hρd
    have hε0 : (0 : ℝ) ≤ 1 + ε := by linarith
    rw [Real.coe_toNNReal _ hε0] at hFg
    have hyp : dist y p ≤ 20 * Δ := hy.1
    have hρy : |ρ y / ρ p - 1| ≤ 20 * Δ * Λ := by
      have h1 := hρR.dist_le_mul y p
      rw [Real.dist_eq, div_self hr.ne'] at h1
      have h2 : (Λ : ℝ) * dist y p ≤ Λ * (20 * Δ) := mul_le_mul_of_nonneg_left hyp Λ.coe_nonneg
      linarith
    have hFy : |F y / ρ p| ≤ 11 * Δ := by
      have h1 := hval y
      rw [abs_of_nonneg (div_nonneg (hF0 y) hr.le), div_le_iff₀ hr]
      have h2 : infDist y A ≤ 21 / 2 * Δ := hy.2.2
      rw [hinfR, inv_mul_le_iff₀ hr] at h2
      have h3 := (abs_lt.mp h1).2
      have h4 := mul_le_mul_of_nonneg_right hμ1 (le_of_lt (mul_pos hΔ hr))
      nlinarith
    have hq := sqrt_gInner_gradFun_div_sub_le gR hnR hFd hρd hFg hρg hρy (by linarith) hFy
    calc _ ≤ 2 * (20 * Δ * Λ) * (1 + ε) + 4 * (11 * Δ) * Λ := hq
      _ ≤ 100 * Δ * Λ := by
        have hΛ0 : (0 : ℝ) ≤ Λ := Λ.coe_nonneg
        have hk := mul_nonneg (mul_nonneg hΔ.le hΛ0) (by linarith : (0 : ℝ) ≤ 16 - 40 * ε)
        nlinarith
  · -- L5
    have hx' : x ∈ @ball M m.toPseudoMetricSpace p (20 * (Δ * ρ p)) := by
      have h : (ρ p)⁻¹ * @dist M m.toDist x p < 20 * Δ := hx
      change @dist M m.toDist x p < 20 * (Δ * ρ p)
      rw [← div_eq_inv_mul, div_lt_iff₀ hr] at h
      linarith
    have hxA' : @infDist M m.toPseudoMetricSpace x A < 41 / 4 * (Δ * ρ p) := by
      rw [hinfR, ← div_eq_inv_mul, div_lt_iff₀ hr] at hxA
      linarith
    have heq : edgeRowHeight Δ (fun x => F x / ρ p) (fun x => ρ x / ρ p) =
        fun y => Δ * DifferentialGeometry.Analysis.edgeSublevelProfile (F y / ρ y / Δ) := by
      funext y
      unfold edgeRowHeight
      rw [div_div_div_cancel_right₀ hr.ne']
    rw [heq]
    exact hcore x hx' hxA'

end Kernel

section Family

universe uE uH uM uY

/-- **LFR38, finite family, with LFR27's clauses (QF).** `exists_edge_full_collar_family` with LC87's
clauses L1–L5 of the shared smoothing at every centre (`normalized_edge_lfr27_clauses_QF`).
The original statement: With the ordered parameters of `exists_edge_full_collar_parameters`
(the strong tolerance `b₀` is fixed BEFORE the family), a finite family `P` of centres with
coarse-border charts for the SAME closed set at their physical scales `Δρ(p)` and the normalized
curvature bound gets ONE smoothing `F`: `0 ≤ F`, `(1+ε)`-Lipschitz, `μΔρ(p)`-close to `d_A`; and at
every centre, in its normalization `(ρ(p)⁻¹ d, ρ(p)⁻² g)`, for every actual `(1, b)`-splitting `α`
whose first coordinate is the chart's and every LFR19-type `f` for `α`, the original pair
`(f, (F/ρ(p))/(ρ/ρ(p))) = (f, F/ρ)` has the full adapted collar of quality `γ` on the whole band. -/
theorem exists_edge_full_collar_family_QF {β γ : ℝ} (hβ : 0 < β) (hβγ : β < γ / 1000)
    (hγ : 0 < γ) (hγ1 : γ < 1 / 100) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧ ∀ Δ : ℝ, Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ (σ ε μ τ κ b : ℝ) (Λ : ℝ≥0), 0 ≤ σ → σ ≤ σ₀ → 0 < ε → ε < 1 / 100 →
        0 < μ → μ ≤ 1 / 1000000 → 0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
        0 ≤ κ → κ ≤ κ₀ → 0 < b → b < b₀ → 100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γ / 1000 →
      ∀ (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E]
        [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
        (H : Type uH) [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
        (M : Type uM) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [SigmaCompactSpace M] [hM : CompleteSpace M]
        [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
        [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
        (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
        (A : Set M) (P : Finset M) (Q : M → M → WithLp 2 (ℝ × ℝ)) (ρ : M → ℝ)
        (hρpos : ∀ x, 0 < ρ x),
      P.Nonempty → IsClosed A → (∀ p ∈ P, Q p p = 0) →
      (∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), ∀ y ∈ ball p (200 * (Δ * ρ p)),
        |dist (Q p x) (Q p y) - dist x y| ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, ∀ x ∈ ball p (200 * (Δ * ρ p)), 0 ≤ (Q p x).snd) →
      (∀ p ∈ P, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * (Δ * ρ p) →
        z.snd ∈ Icc 0 (100 * (Δ * ρ p)) →
          ∃ x ∈ ball p (200 * (Δ * ρ p)), dist (Q p x) z ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, p ∈ A) →
      (∀ p ∈ P, ∀ a ∈ A ∩ ball p (190 * (Δ * ρ p)), (Q p a).snd ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, ∀ t : ℝ, |t| ≤ 100 * (Δ * ρ p) →
        ∃ a ∈ A ∩ ball p (190 * (Δ * ρ p)),
          dist (Q p a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * (Δ * ρ p)) →
      (∀ p ∈ P, ∀ z ∈ ball p (10000 * (Δ * ρ p)),
        SectionalBoundedBelowAt g z (-(κ / ρ p) ^ 2)) →
      LipschitzWith Λ ρ → ContMDiff I 𝓘(ℝ, ℝ) ∞ ρ →
      ∃ F : M → ℝ, (∀ x, 0 ≤ F x) ∧ LipschitzWith (Real.toNNReal (1 + ε)) F ∧
        ∀ p ∈ P, (∀ x, |F x - infDist x A| < μ * (Δ * ρ p)) ∧
        (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
        letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
          radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsRiemannianManifold I M :=
          radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : CompleteSpace M :=
          (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hM
        let gR : SmoothRiemannianMetric I M :=
          scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
        (∀ x, |F x / ρ p - infDist x A| < μ * Δ) ∧
        (∃ OF : Set M, IsOpen OF ∧
          closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ} ⊆ OF ∧
          ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => F x / ρ p) OF) ∧
        (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
          ∀ u ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo gR A y,
            Real.sqrt (gR.inner y (gradFun gR (fun x => F x / ρ p) y + u)
              (gradFun gR (fun x => F x / ρ p) y + u)) < ε) ∧
        (∀ y ∈ closedBall p (20 * Δ) ∩ {y | 3 / 4 * Δ ≤ infDist y A ∧ infDist y A ≤ 21 / 2 * Δ},
          Real.sqrt (gR.inner y
            (gradFun gR (fun z => F z / ρ p / (ρ z / ρ p)) y - gradFun gR (fun x => F x / ρ p) y)
            (gradFun gR (fun z => F z / ρ p / (ρ z / ρ p)) y - gradFun gR (fun x => F x / ρ p) y))
            ≤ 100 * Δ * Λ) ∧
        ∀ x ∈ ball p (20 * Δ), infDist x A < 41 / 4 * Δ →
          ContMDiffAt I 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ (fun x => F x / ρ p) (fun x => ρ x / ρ p)) x) ∧
        (have hmetric := riemannianEDistOf_eq_ofReal_dist g hEnorm
        letI := m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
          radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : IsRiemannianManifold I M :=
          radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr (hρpos p))
        letI : CompleteSpace M :=
          (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).mpr hM
        let gR : SmoothRiemannianMetric I M :=
          scaleMetric ((ρ p)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hρpos p)) 2) g
        have hnR : IsMetricNorm (I := I) (M := M) gR := isMetricNorm_of_riemannianBundle gR
        ∀ (Y : Type uY) [MetricSpace Y] (y₀ : Y)
          (α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) b),
        (∀ z ∈ ball p b⁻¹, SectionalBoundedBelowAt gR z (-b ^ 2)) →
        (∀ z ∈ ball p (200 * Δ), (Q p z).fst = ρ p * (α.toFun z).fst) →
        ∀ f : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f (ball p (100 * Δ)) →
        LipschitzWith (Real.toNNReal (1 + σ)) f →
        (∀ x ∈ ball p (100 * Δ), |f x - (α.toFun x).fst| ≤ μ * Δ) →
        (∀ x ∈ ball p (100 * Δ), ∀ x' ∈ ball p (1000 * Δ), 100 * Δ < dist x x' →
          ∀ w : TangentSpace I x, gR.inner x w w = 1 →
          intrinsicGeodesic gR hnR x w (dist x x') = x' →
          |mvfderiv (I := I) f x w - ((α.toFun x').fst - (α.toFun x).fst) / dist x x'| < σ) →
        ∀ x ∈ ball p (100 * Δ), |f x| ≤ 10 * Δ →
          Δ / 10 ≤ F x / ρ p / (ρ x / ρ p) → F x / ρ p / (ρ x / ρ p) ≤ 10 * Δ →
        ∃ hq : 99 / 100 ≤ ρ x / ρ p ∧ ρ x / ρ p ≤ 101 / 100,
          (letI := (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p))).rescale (ρ x / ρ p)⁻¹
            (inv_pos.mpr (lt_of_lt_of_le (by norm_num) hq.1));
            ∃ Φ : KleinerLottApprox x (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β,
              ∀ y, Φ.toFun y = @planeComparisonMap M (m.rescale (ρ p)⁻¹ (inv_pos.mpr (hρpos p)))
                (fun z => (ρ p)⁻¹ • Q p z) p x Δ (ρ x / ρ p) y) ∧
          let J := edgeReferenceCoordinates ![f, fun z => F z / ρ p / (ρ z / ρ p)]
          ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ J (ball x (300 * (ρ x / ρ p))) ∧
          (∀ y ∈ ball x (100 * (ρ x / ρ p)), Function.Surjective (mvfderiv (I := I) J y)) ∧
          (∀ y ∈ ball x (100 * (ρ x / ρ p)), ∀ z ∈ ball x (100 * (ρ x / ρ p)),
            ‖J y - J z‖ ≤ (1 + γ) * (dist y z / (ρ x / ρ p))) ∧
          (∀ y ∈ ball x (100 * (ρ x / ρ p)), infDist (J y) (ball (J x) 100) < 100 * γ) ∧
          (∀ v ∈ ball (J x) 100, ∃ y ∈ ball x (100 * (ρ x / ρ p)), ‖J y - v‖ < 100 * γ) ∧
          ∀ y ∈ ball x (100 * (ρ x / ρ p)), ∀ z ∈ ball x (100 * (ρ x / ρ p) / γ),
            ρ x / ρ p < dist y z →
            ∀ W : TangentSpace I y, gR.inner y W W = 1 →
            intrinsicGeodesic gR hnR y W (dist y z) = z →
            ‖(ρ x / ρ p) • mvfderiv (I := I) J y W - (dist y z / (ρ x / ρ p))⁻¹ •
              (planeReferenceIsometry (planeComparisonMap (fun z => (ρ p)⁻¹ • Q p z) p x Δ
                (ρ x / ρ p) z) -
                planeReferenceIsometry (planeComparisonMap (fun z => (ρ p)⁻¹ • Q p z) p x Δ
                  (ρ x / ρ p) y))‖ < γ) := by
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hcollar⟩ :=
    exists_edge_full_collar_parameters.{uE, uH, uM, uY} hβ hβγ hγ hγ1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun Δ hΔ => ?_⟩
  have hΔpos : 0 < Δ := hΔ₀.trans_le hΔ
  obtain ⟨τ₀, hτ₀, κ₀, hκ₀, b₀, hb₀, hΔcollar⟩ := hcollar Δ hΔ
  refine ⟨min τ₀ (1 / 20000), lt_min hτ₀ (by norm_num), min κ₀ (1 / (100 * Δ)),
    lt_min hκ₀ (by positivity), b₀, hb₀, ?_⟩
  intro σ ε μ τ κ b Λ hσ hσσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ hκ hκκ₀ hb hbb₀ hlam hbudget
    E _ _ _ _ H _ I _ M m _ _ _ hM _ _ _ g hEnorm A P Q ρ hρpos hP hA hQp hdist hheight hcover
    hpA hborder hbordercover hsec hρ hρs
  have hκΔ : κ * Δ ≤ 1 / 100 := by
    have h : κ ≤ 1 / (100 * Δ) := hκκ₀.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hτsmall : τ < 1 / 10000 :=
    (hττ₀.trans (min_le_right _ _)).trans_lt (by norm_num)
  obtain ⟨F, O, hO, hFO, hF0, hFL, -, hcent⟩ :=
    exists_shared_low_collar_smoothing g hEnorm hA hP hρpos hΔpos hτ hτsmall hQp hdist hheight
      hcover hpA hborder hbordercover hκ hκΔ
      (fun p hp z hz => hsec p hp z (ball_subset_ball (by nlinarith [hρpos p]) hz))
      hε hε1 hμ (by linarith) hθ hρ hρs (by linarith)
  refine ⟨F, hF0, hFL, fun p hp => ⟨(hcent p hp).1,
    normalized_edge_lfr27_clauses_QF g hEnorm hρpos hΔpos hε hε1 (by linarith) (by linarith) hO hFO
      hF0 hFL hρ hρs (hcent p hp).1 (hcent p hp).2.1 (hcent p hp).2.2.1 (hcent p hp).2.2.2.1, ?_⟩⟩
  obtain ⟨-, hCO, hgrad, -⟩ := hcent p hp
  have hr : 0 < ρ p := hρpos p
  have hchart := radialScaled_chart_clauses (A := A) hr (hQp p hp) (hdist p hp) (hheight p hp)
    (hcover p hp) (hborder p hp) (hbordercover p hp)
  have hsecR := radialScaled_sectional_bound g (r := 10000 * Δ) hr
    (fun z hz => hsec p hp z (by rwa [mul_assoc] at hz))
  have hvalR := radialScaled_value_clause (A := A) hr (hcent p hp).1
  have hCOR := radialScaled_collar_subset hr hCO
  have hFLR := radialScaled_div_lipschitzWith hFL hr
  have hρR := lipschitzWith_normalized_scale hρ hr
  have hgradR (y : M) (hy : y ∈ closedBall p (20 * (Δ * ρ p)) ∩ {x | Δ * ρ p / 25 ≤
      infDist x A ∧ infDist x A ≤ 21 / 2 * (Δ * ρ p)}) :=
    radialScaled_low_collar_gradient g hEnorm hr
      ((hFO.contMDiffAt (hO.mem_nhds (hCO hy))).mdifferentiableAt (by simp)) (hgrad y hy)
  have hCC := radialScaled_collar_subset (A := A) (p := p) (Δ := Δ)
    (O := closedBall p (20 * (Δ * ρ p)) ∩ {x | Δ * ρ p / 25 ≤ infDist x A ∧
      infDist x A ≤ 21 / 2 * (Δ * ρ p)}) hr subset_rfl
  intro hmetric gR hnR Y _ y₀ α hsecb hQα f hfs hfL hfval htest x hx hfx hη hη'
  let mR : MetricSpace M := m.rescale (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ : CompleteSpace M := (m.rescale_completeSpace_iff (ρ p)⁻¹ (inv_pos.mpr hr)).mpr hM
  let _ := radialScaledBundle g (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ := radialScaledContinuous g (ρ p)⁻¹ (inv_pos.mpr hr)
  let _ := radialScaledManifold (m := m) g hmetric (ρ p)⁻¹ (inv_pos.mpr hr)
  obtain ⟨hQp', hdist', hheight', hcover', hborder', hbordercover'⟩ := hchart
  have hQα' : ∀ z ∈ ball p (200 * Δ), ((fun z => (ρ p)⁻¹ • Q p z) z).fst = (α.toFun z).fst := by
    intro z hz
    change (ρ p)⁻¹ * (Q p z).fst = _
    rw [hQα z hz, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hfval' : ∀ x ∈ ball p (100 * Δ), |f x - ((fun z => (ρ p)⁻¹ • Q p z) x).fst| ≤ μ * Δ := by
    intro z hz
    rw [hQα' z (ball_subset_ball (by linarith) hz)]
    exact hfval z hz
  exact hΔcollar σ ε μ τ κ b Λ hσ hσσ₀ hε.le hε1 hμ1 (hττ₀.trans (min_le_left _ _)) hκ
    (hκκ₀.trans (min_le_left _ _)) hb hbb₀ hlam hbudget E H I M gR hnR Y p y₀ α
    (fun z => (ρ p)⁻¹ • Q p z) A (fun z => ρ z / ρ p) (fun z => F z / ρ p) f O hsecR hsecb hA
    hQp' hdist' hheight' hcover' (hpA p hp) hborder' hbordercover' hQα' hρR
    (div_self hr.ne') (hρs.div_const _) hO hCOR (hFO.div_const _) hFLR hvalR (fun y hy => hgradR y (hCC hy)) hfs hfL
    hfval' htest x hx hfx hη hη'

end Family

end DifferentialGeometry.Geometry.Collapse
