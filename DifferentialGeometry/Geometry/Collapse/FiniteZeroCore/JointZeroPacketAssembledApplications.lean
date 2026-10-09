import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.JointZeroPacketAssembled
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

/-!
# Consumers of the assembled LFR49 row (lane LFR49-FIN, group G2)

* `lfr49_eventually_balls_diffeomorphic`: on LFR49's subsequence, for every large scale `R`, on a
  tail, any two balls `B(p_{k j}, ρ₁ R)`, `B(p_{k j}, ρ₂ R)` with `ρ₁, ρ₂ ∈ [1/5, 2]` are
  diffeomorphic (through the common model `Ns` of T0′, both branches).
* The frozen form of T0 (build-logs/scratch/LFR49/Target.lean at sources in `Type`, with the
  instance `[∀ i, T2Space (TangentBundle I3 (X i))]`) is the `example` below.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Manifold
open DifferentialGeometry.Analysis.Calculus
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **Consumer of T0′.** On LFR49's subsequence, for every large scale `R`, on a tail, any two
balls `B(p_{k j}, ρ₁ R)`, `B(p_{k j}, ρ₂ R)`, `ρ₁, ρ₂ ∈ [1/5, 2]`, are diffeomorphic. -/
theorem lfr49_eventually_balls_diffeomorphic
    (K : ℕ) (hK : 10 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v) (A : ℝ → ℝ)
    {X : ℕ → Type} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
    [∀ i, IsManifold I3 ∞ (X i)] [∀ i, SigmaCompactSpace (X i)] [hXc : ∀ i, CompleteSpace (X i)]
    [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric I3 (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (hvol : ∀ᶠ i in atTop, ENNReal.ofReal v ≤
      riemannianVolumeMeasure I3 (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ᶠ i in atTop, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R → ∀ᶠ j in atTop,
      ∀ ρ₁ ∈ Icc (1 / 5 : ℝ) 2, ∀ ρ₂ ∈ Icc (1 / 5 : ℝ) 2,
        ∃ Φ : PartialDiffeomorph I3 I3 (X (k j)) (X (k j)) ∞,
          Φ.source = Metric.ball (p (k j)) (ρ₁ * R) ∧
            Φ.target = Metric.ball (p (k j)) (ρ₂ * R) := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, h1, h2, h3, h4, h5, C, mC, o, h6, h7, Ns, tNs, cNs, hNs, h8,
      R₃, hball⟩ := lfr49_finite_model_ball_type_all_scales K hK hr hv A g hmetric p hvol hcurv hη hL
      hsec
  refine ⟨φ, hφ, R₃, fun R hR => ?_⟩
  filter_upwards [hball R hR] with j hj ρ₁ hρ₁ ρ₂ hρ₂
  obtain ⟨Ψ₁, hΨ₁s, hΨ₁t⟩ := hj ρ₁ hρ₁
  obtain ⟨Ψ₂, hΨ₂s, hΨ₂t⟩ := hj ρ₂ hρ₂
  refine ⟨Ψ₁.trans Ψ₂.symm, ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source, PartialDiffeomorph.symm_source, hΨ₂t, preimage_univ,
      inter_univ, hΨ₁s]
  · change (Ψ₁.toPartialEquiv.trans Ψ₂.symm.toPartialEquiv).target = _
    rw [PartialEquiv.trans_target]
    change Ψ₂.source ∩ Ψ₂ ⁻¹' Ψ₁.target = _
    rw [hΨ₁t, preimage_univ, inter_univ, hΨ₂s]

-- The frozen form of T0 (sources in `Type`, with the instance on the tangent bundles).
example
    (K : ℕ) (hK : 10 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v) (A : ℝ → ℝ)
    {X : ℕ → Type} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
    [∀ i, IsManifold I3 ∞ (X i)] [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle I3 (X i))] [∀ i, CompleteSpace (X i)]
    [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric I3 (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (hvol : ∀ᶠ i in atTop, ENNReal.ofReal v ≤
      riemannianVolumeMeasure I3 (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ᶠ i in atTop, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {δ ε e T : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε < 1) (he : 0 < e)
    (he1 : e < 1 / 40) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ R : ℝ, T ≤ R ∧ ∃ hR : 0 < R,
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace E3 N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold I3 ∞ N)
        (G : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : N → Type _))
        (q : N),
        ProperSpace N ∧ ConnectedSpace N ∧
        (letI : RiemannianBundle (fun x : N => TangentSpace I3 x) := ⟨G.toRiemannianMetric⟩
         IsRiemannianManifold I3 N) ∧
        (∀ (x : N) (v w : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x v w) ∧
        PointedGHConverges (fun j => p (k j)) q ∧
        ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
          (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R' : ℝ, ∀ hR' : 0 < R', R₀ ≤ R' →
            Nonempty (@KleinerLottApprox N C (mN.rescale R'⁻¹ (inv_pos.mpr hR')) mC q o τ)) ∧
        ∃ (Ns : Type) (_ : TopologicalSpace Ns) (_ : ChartedSpace E3 Ns)
          (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N),
        ∀ᶠ j in atTop,
          Nonempty (@KleinerLottApprox (X (k j)) C
            ((mX (k j)).rescale R⁻¹ (inv_pos.mpr hR)) mC (p (k j)) o δ) ∧
          (letI := (mX (k j)).rescale R⁻¹ (inv_pos.mpr hR)
          let gR := scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) (g (k j))
          ∃ F : X (k j) → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
            (∃ O : Set (X (k j)), IsOpen O ∧
              {x : X (k j) | 1 / 10 ≤ dist x (p (k j)) ∧ dist x (p (k j)) ≤ 10} ⊆ O ∧
              ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O) ∧
            (∀ x, |F x - Metric.infDist x {p (k j)}| < e) ∧
            (∀ x, x ∉ {x : X (k j) | 1 / 20 < dist x (p (k j)) ∧ dist x (p (k j)) < 20} →
              F x = Metric.infDist x {p (k j)}) ∧
            (∀ x y, |(F x - Metric.infDist x {p (k j)}) - (F y - Metric.infDist y {p (k j)})| ≤
              ε * dist x y) ∧
            (∀ x, 0 ≤ F x) ∧ F (p (k j)) = 0 ∧
            (∀ q' ∈ {x : X (k j) | 1 / 10 ≤ dist x (p (k j)) ∧ dist x (p (k j)) ≤ 10},
              1 - ε ≤ Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ∧
                Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ≤ 1 + ε) ∧
            (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x (p (k j)) ∧
              dist x (p (k j)) < 2 + e) ∧
            F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆
              {x : X (k j) | 1 / 10 ≤ dist x (p (k j)) ∧ dist x (p (k j)) ≤ 10} ∧
            (∃ O' : Set (X (k j)), IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
              ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q' ∈ O', gradFun gR F q' ≠ 0) ∧
            ∃ L' : ℝ, 0 ≤ L' ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L') ∧
              ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
              (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
              (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
              tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
                {x : X (k j) | 1 / 5 - e < dist x (p (k j)) ∧ dist x (p (k j)) < 9 / 10 + e} ∧
              ∀ q', Real.sqrt (gR.inner q'
                (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')
                (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')) ≤ L' * (1 + ε)) ∧
          ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I3 I3 (X (k j)) Ns ∞,
            Ψ.source = Metric.ball (p (k j)) (ρ' * R) ∧ Ψ.target = univ :=
  lfr49_finite_joint_zero_packet K hK hr hv A g hmetric p hvol hcurv hη hL hsec hδ hδ1 hε hε1 he he1

end DifferentialGeometry.Geometry.Collapse
