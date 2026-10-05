import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LFR49InputsApplications
import DifferentialGeometry.Geometry.Collapse.SublevelCore.JointWitnessConeRadial
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.EventualBounds
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.CurvatureScaleBinding

/-!
# LFR49: the joint zero packet for an ARBITRARY sequence (unconditional tier)

Frozen blueprint master207A, LFR49 (A:29096), in the finite form that LPA02 consumes
(state-F8-LPA2.md, "LPA02"): LFR14's hypotheses for ANY sequence of complete connected smooth
Riemannian three-manifolds (`10 ≤ K`, volume, curvature derivatives, `sec ≥ -η_i` on `L_i`-balls
with `η_i → 0`, `L_i → ∞`, the bounds holding eventually), and LC57's ranges `δ, ε, e, T` fixed
FIRST. On one subsequence there are ONE scale `R ≥ T`, one complete nonnegative `C^{K-1}` model
`(N, G, q)` (LFR14 / L-CONS), its cone `(C, o)` (LFR59 for the finite model,
`exists_finite_cone_package_of_limit`) and, on one tail at the scale `R`:
1. an actual pointed Kleiner–Lott `δ`-map to `(C, o)` (LC57 (1));
2. an LC30 radial function with LC31's cutoff (LC57 (2));
3. if the model is COMPACT: every open ball `B(p, ρ' R)`, `ρ' ∈ [1/5, 2]`, is diffeomorphic to `N`
   (LFR48 + T2, `exists_scale_eventually_compact_model_type_of_finite_limit`).

The source curvature input of LC57 is LFR49's step 1 (`exists_curvature_scale_of_signed_ball_lower_bounds`,
after replacing `L_i` by `0` on the finitely many indices before the eventual bound).

Not covered here: item 3 for a NONCOMPACT model. Its kernel is
`exists_scale_eventually_open_ball_bundle_type_finite` (T4 + T5, model in carrier coordinates);
the carrier comparison maps and the carrier form of LFR46.2's margin are open (state-LFR49.md).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
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

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **LFR49 step 1 along a subsequence, eventual form.** Eventual bounds `sec_{g_i} ≥ -η_i` on
`B(p_i, L_i)` with `L_i → ∞`, `η_i → 0` give, along any strictly increasing `φ`, scales
`H_k → ∞` with `sec ≥ -H_k⁻²` on the metric balls `B(p_{φ k}, H_k)` for EVERY `k`. -/
theorem exists_curvature_scale_along_of_eventual {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace E3 (X i)] [∀ i, IsManifold I3 ∞ (X i)]
    (g : ∀ i, SmoothRiemannianMetric I3 (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i) {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ᶠ i in atTop, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ∃ Hb : ℕ → ℝ, Tendsto Hb atTop atTop ∧ ∀ k, ∀ y ∈ Metric.ball (p (φ k)) (Hb k),
      SectionalBoundedBelowAt (g (φ k)) y (-((Hb k)⁻¹ ^ 2)) := by
  classical
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hsec
  set L' : ℕ → ℝ := fun i => if N₀ ≤ i then L i else 0 with hL'def
  have hL' : Tendsto L' atTop atTop :=
    hL.congr' (eventually_atTop.mpr ⟨N₀, fun i hi => by simp [hL'def, hi]⟩)
  have hsec' : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L' i),
      SectionalBoundedBelowAt (g i) y (-η i) := by
    intro i y hy
    by_cases hi : N₀ ≤ i
    · have hy' : y ∈ riemannianBallOf (g i) (p i) (L i) := by
        have h : L' i = L i := by simp [hL'def, hi]
        rw [← h]
        exact hy
      exact hN₀ i hi y hy'
    · exfalso
      have h : L' i = 0 := by simp [hL'def, hi]
      have hy' : riemannianEDistOf (g i) (p i) y < ENNReal.ofReal (L' i) := hy
      rw [h, ENNReal.ofReal_zero] at hy'
      exact ENNReal.not_lt_zero hy'
  obtain ⟨Hs, hHs, -, hHsec⟩ := exists_curvature_scale_of_signed_ball_lower_bounds g p hL' hη hsec'
  refine ⟨fun k => Hs (φ k), hHs.comp hφ.tendsto_atTop, fun k y hy => ?_⟩
  have hy' : y ∈ riemannianBallOf (g (φ k)) (p (φ k)) (Hs (φ k)) := by
    change riemannianEDistOf (g (φ k)) (p (φ k)) y < ENNReal.ofReal (Hs (φ k))
    rw [hmetric]
    have hd : dist (p (φ k)) y < Hs (φ k) := by rw [dist_comm]; exact mem_ball.mp hy
    exact (ENNReal.ofReal_lt_ofReal_iff (dist_nonneg.trans_lt hd)).mpr hd
  have h := hHsec (φ k) y hy'
  rwa [← inv_pow] at h

/-- **LFR49 (row), unconditional tier: every branch's items (1)–(2), the compact branch's item (3).**
For ANY sequence with LFR14's eventual hypotheses (`10 ≤ K`) and LC57's ranges fixed first, there
are a subsequence `k`, ONE scale `R ≥ T`, one complete nonnegative `C^{K-1}` model `(N, G, q)` with
pointed convergence, its cone `(C, o)`, and one tail on which, at the scale `R`: (1) a KL `δ`-map to
`(C, o)`; (2) an LC30 radial function with LC31's cutoff; (3) if `N` is compact, every open ball
`B(p_{k j}, ρ' R)`, `ρ' ∈ [1/5, 2]`, is diffeomorphic to `N`. -/
theorem lfr49_finite_joint_zero_packet_compact_tier
    (K : ℕ) (hK : 10 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v) (A : ℝ → ℝ)
    {X : ℕ → Type u} [mX : ∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
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
          (CompactSpace N → ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
            ∃ Ψ : PartialDiffeomorph I3 I3 (X (k j)) N ∞,
              Ψ.source = Metric.ball (p (k j)) (ρ' * R) ∧ Ψ.target = univ) := by
  have instNZ_LFR49 : NeZero (Module.finrank ℝ E3) := ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  -- LFR14 for the sequence (L-CONS, eventual bounds), with the curvature sign
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      -, hsecG⟩ :=
    exists_finite_cheeger_gromov_limit_with_nonneg_sectional_of_eventual_bounds 3 K
      (by norm_num) (by omega) hr hv A g hmetric p hvol hcurv hη hL hsec
  -- LFR59 for the finite model
  obtain ⟨C, mC, o, ⟨Hc⟩, -, -, -, hcone⟩ :=
    exists_finite_cone_package_of_limit (by omega : 3 ≤ K) G hRiem hsecG q
  -- LFR49 step 1 along `φ`
  obtain ⟨Hb, hHb, hsecM⟩ := exists_curvature_scale_along_of_eventual g hmetric p hη hL hsec hφ
  -- LC57 (1)–(2)
  obtain ⟨R₁, hR₁, h12⟩ := exists_scale_eventually_cone_radial_witnesses
    (M := fun i => X (φ i)) (fun i => g (φ i)) (fun i => hmetric (φ i)) hGH Hc hcone Hb hHb
    hsecM hδ hδ1 hε hε1 he he1
  by_cases hc : CompactSpace N
  · -- LC57 (3), compact branch: LFR48 + T2
    obtain ⟨R₂, -, h3⟩ := exists_scale_eventually_compact_model_type_of_finite_limit
      (X := fun i => X (φ i)) (by omega : 1 ≤ K) (fun i => g (φ i)) (fun i => hmetric (φ i))
      (fun i => p (φ i)) G q j hpt hexh hconv hdist
    set R : ℝ := max (max R₁ R₂) T with hRdef
    have hR1 : R₁ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
    have hR2 : R₂ ≤ R := (le_max_right _ _).trans (le_max_left _ _)
    have hR : 0 < R := hR₁.trans_le hR1
    refine ⟨φ, hφ, R, le_max_right _ _, hR, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG,
      hGH, C, mC, o, ⟨Hc⟩, hcone, ?_⟩
    filter_upwards [h12 R hR hR1, h3 R hR2] with i h12i h3i
    exact ⟨h12i.1, h12i.2, fun _ => h3i⟩
  · set R : ℝ := max R₁ T with hRdef
    have hR1 : R₁ ≤ R := le_max_left _ _
    have hR : 0 < R := hR₁.trans_le hR1
    refine ⟨φ, hφ, R, le_max_right _ _, hR, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG,
      hGH, C, mC, o, ⟨Hc⟩, hcone, ?_⟩
    filter_upwards [h12 R hR hR1] with i h12i
    exact ⟨h12i.1, h12i.2, fun h => absurd h hc⟩

end DifferentialGeometry.Geometry.Collapse
