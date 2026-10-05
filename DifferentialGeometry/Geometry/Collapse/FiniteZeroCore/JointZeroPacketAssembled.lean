import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.JointZeroPacketApplications
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LFR49InputsApplications
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.SoulTubeBundleData
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalFlowMarginTransportApplications
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.IsometryTransport
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CarrierPackage

/-!
# LFR49 (row): the joint zero packet for an ARBITRARY sequence, both branches

Frozen blueprint master207A, LFR49 (A:29096), in the finite form that LPA02 consumes
(state-F8-LPA2.md, "LPA02"). Assembled from the delivered interfaces (no stub):
* (a) `lfr49A_carrier_package` (`CarrierPackage.lean`): the soul carrier re-charted over `E3` with
  the transported metric, generator and SMOOTH comparison maps;
* (b) `cms3flow2_finiteMinimizingDirectionsTo_map` (CMS3-FLOW2): finite minimizing directions move
  along the `C¹` isometry `κ`;
* (c) `exists_finite_soul_tube_bundle_data_dim_three` (`SoulTubeBundleData.lean`): soul, tube and
  normal bundle data for every soul dimension;
* (d) `hcone_of_isometryEquiv`, `pointedGHConverges_of_isometryEquiv` (`IsometryTransport.lean`).

* `lfr49_finite_model_ball_type_all_scales` (T0′): extraction (L-CONS), the cone (LFR59 for the
  finite model) and LFR49's item (3) at EVERY scale `R ≥ R₀` (compact branch: LFR48 + T2;
  noncompact branch: LFR46 tube form + LFR47 + (a)–(d) + T4 + T5);
* `lfr49_finite_joint_zero_packet` (T0, the row): T0′ + LFR49 step 1 + LC57 (1)–(2) at one scale
  `R ≥ T`.

Deviations from the frozen T0 (build-logs/scratch/LFR49/Target.lean): sources in `Type` (LC60 and
GAP C live in `Type`); the unused instance `[∀ i, T2Space (TangentBundle I3 (X i))]` is dropped (it
is a global instance, `FiberBundle.instT2SpaceTotalSpace`).
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
open DifferentialGeometry.Geometry.FiniteSoul
open DifferentialGeometry.Topology (TransportedCarrier)
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- A smooth source metric aligned with the distance makes the source a Riemannian manifold for
the bundle structure `⟨g.toRiemannianMetric⟩`. -/
theorem isRiemannianManifold_of_aligned {Y : Type} [MetricSpace Y] [ChartedSpace E3 Y]
    [IsManifold I3 ∞ Y] (g : SmoothRiemannianMetric I3 Y)
    (hmetric : ∀ a b, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) :
    letI : RiemannianBundle (fun x : Y => TangentSpace I3 x) := ⟨g.toRiemannianMetric⟩
    IsRiemannianManifold I3 Y := by
  let instRB_LFR49FIN : RiemannianBundle (fun x : Y => TangentSpace I3 x) :=
    ⟨g.toRiemannianMetric⟩
  constructor
  intro a b
  change edist a b = riemannianEDistOf g a b
  rw [edist_dist, hmetric]

/-- **T0' (LFR49, item (3) at every large scale).** For ANY sequence with LFR14's eventual
hypotheses (`10 ≤ K`): a subsequence `k`, one complete nonnegative `C^{K-1}` model `(N, G, q)` with
pointed convergence, its cone `(C, o)` (Kleiner–Lott maps for every blow-down), a smooth `Ns ≃ₜ N`
and `R₀` such that for EVERY `R ≥ R₀`, on a tail, every open ball `B(p_{k j}, ρ' R)`,
`ρ' ∈ [1/5, 2]`, is diffeomorphic to `Ns` (compact model: `Ns = N`, LFR48 + T2; noncompact model:
`Ns = N'` the re-charted soul carrier, (a) + (b) + (c) + (d) + T4 + T5). The source metric instance
`mX` and its completeness `hXc` are named so that rescaled sources can be passed (LPA02). -/
theorem lfr49_finite_model_ball_type_all_scales
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
    ∃ k : ℕ → ℕ, StrictMono k ∧
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
          (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N), ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
          ∀ᶠ j in atTop, ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
            ∃ Ψ : PartialDiffeomorph I3 I3 (X (k j)) Ns ∞,
              Ψ.source = Metric.ball (p (k j)) (ρ' * R) ∧ Ψ.target = univ := by
  have instNZ_LFR49FIN : NeZero (Module.finrank ℝ E3) :=
    ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, hsecG⟩ :=
    exists_finite_cheeger_gromov_limit_with_nonneg_sectional_of_eventual_bounds 3 K
      (by norm_num) (by omega) hr hv A g hmetric p hvol hcurv hη hL hsec
  obtain ⟨C, mC, o, ⟨Hc⟩, -, -, -, hcone⟩ :=
    exists_finite_cone_package_of_limit (by omega : 3 ≤ K) G hRiem hsecG q
  obtain ⟨Hb, hHb, hsecM⟩ := exists_curvature_scale_along_of_eventual g hmetric p hη hL hsec hφ
  -- item (3), both branches
  have h3 : ∃ (Ns : Type) (tNs : TopologicalSpace Ns) (cNs : ChartedSpace E3 Ns)
      (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N), ∃ R₃ : ℝ, ∀ R : ℝ, R₃ ≤ R →
      ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∃ Ψ : PartialDiffeomorph I3 I3 (X (φ i)) Ns ∞,
        Ψ.source = Metric.ball (p (φ i)) (ρ * R) ∧ Ψ.target = univ := by
    by_cases hc : CompactSpace N
    · obtain ⟨R₃, -, h3⟩ := exists_scale_eventually_compact_model_type_of_finite_limit
        (X := fun i => X (φ i)) (by omega : 1 ≤ K) (fun i => g (φ i)) (fun i => hmetric (φ i))
        (fun i => p (φ i)) G q j hpt hexh hconv hdist
      exact ⟨N, inferInstance, cN, hMN, Homeomorph.refl N, R₃, h3⟩
    · have hnc : NoncompactSpace N := not_compactSpace_iff.mp hc
      let rbN : RiemannianBundle (fun x : N => TangentSpace I3 x) := ⟨G.toRiemannianMetric⟩
      have hRM : IsRiemannianManifold I3 N := hRiem
      have hGnorm : ∀ (z : N) (u : TangentSpace I3 z),
          ‖u‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner z u u)) := by
        intro z u
        rw [← ofReal_norm, norm_eq_sqrt_real_inner]
        rfl
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 10 := ⟨K - 10, by omega⟩
      have hr8 : (3 : ℕ∞) ≤ ((m + 8 : ℕ) : ℕ∞) := by exact_mod_cast (show 3 ≤ m + 8 by omega)
      let G8 : ContMDiffRiemannianMetric I3 ((((m + 8 : ℕ) : ℕ∞) : ℕ∞ω) + 1) E3
          (TangentSpace I3 : N → Type _) := G
      have hGnorm8 : ∀ (z : N) (u : TangentSpace I3 z),
          ‖u‖ₑ = ENNReal.ofReal (Real.sqrt (G8.inner z u u)) := hGnorm
      have hsec8 : ∀ (x : N) (v w : TangentSpace I3 x), 0 ≤ G8.sectionalCurvature x v w := hsecG
      -- LFR48 on the limit
      obtain ⟨jN, hjNpt, -, -, hjNexh, hjNconv, hjNdist, -⟩ :=
        exists_smooth_comparison_maps_of_finite_limit (X := fun i => X (φ i)) (by omega)
          (fun i => g (φ i)) (fun i => hmetric (φ i)) (fun i => p (φ i)) G q j hpt hexh hconv
          hdist
      -- (c)
      obtain ⟨S, ε₀, ψ, EB, i1, i2, i3, B, i4, i5, i6, i7, F, i8, i9, i10, V, i11, i12, i13, i14,
          i15, i16, i17, b, ι, hdimP, hSc, hSne, hout, hε₀, hψs, hψ, hψexp, hdS, hbinj, hbS,
          hbinv, hι, hιb, hιlin, hιnorm, hιν, hιonto⟩ :=
        exists_finite_soul_tube_bundle_data_dim_three (finrank_euclideanSpace_fin) hr8 G8 hGnorm8
          hsec8
      -- LFR46 (tube form) + LFR47 flow + T5
      obtain ⟨X0, ℓ, A₂, eN, hℓ, -, hXB, hmargin, -, W, hW, hWX, -, hdu, -, -, -, -⟩ :=
        lfr49_noncompact_carrier_data G8 hr8 hGnorm8 hsec8 hSc hSne hout hε₀ ψ hψs hψ hψexp hdS b
          hbinj hbS hbinv ι hι hιb hιlin hιnorm hιν hιonto q
      -- (a)
      obtain ⟨N', mN', cN', hMN', rbN', hRM', r', hr', G', κ, D', W', jt, hpN', hG'norm, hκ, hκG,
          -, hW', hW'X, hdu', hjtpt, hjtexh, hjtconv, hjtdist, hjtcov⟩ :=
        lfr49A_carrier_package (X := fun i => X (φ i))
          (show (6 : ℕ∞) ≤ ((m + 8 : ℕ) : ℕ∞) by exact_mod_cast (show 6 ≤ m + 8 by omega))
          G8 hGnorm8 (fun i => g (φ i))
          (fun i => hmetric (φ i)) q jN hjNexh
          (fun x L hL hLt => (hjNconv x L hL hLt).mono_order (by omega)) hjNdist hdimP eN W hW hdu
      -- (b): the margin of `W'` for the finite minimizing directions of `G'`
      have hW'dir : ∀ y : N', A₂ ≤ dist (κ.symm q) y →
          ∀ w ∈ G'.finiteMinimizingDirectionsTo {κ.symm q} y,
            G'.inner y (W' y) w ≤ -(1 / 4) := by
        intro y hy w hw
        have hw' := cms3flow2_finiteMinimizingDirectionsTo_map (le_trans (by norm_num) hr')
          (show (2 : ℕ∞) ≤ ((m + 8 : ℕ) : ℕ∞) by exact_mod_cast (show 2 ≤ m + 8 by omega))
          G' hG'norm G8 hGnorm8 (κ : N' → N) hκ (fun a b => κ.dist_eq a b) hκG {κ.symm q} y w hw
        rw [image_singleton, κ.apply_symm_apply] at hw'
        rw [hκG, hW'X, hWX]
        refine hmargin (κ y) ?_ _ hw'
        rw [← κ.apply_symm_apply q, κ.dist_eq]
        exact hy
      have hW'B : ∀ y : N', G'.inner y (W' y) (W' y) ≤ 4 := by
        intro y
        rw [hκG, hW'X, hWX]
        exact hXB (κ y)
      -- (d): cone and pointed convergence of `N'`
      have hcone' := hcone_of_isometryEquiv κ hcone
      have hGH' : PointedGHConverges (fun i => jt i (κ.symm q)) (κ.symm q) := by
        have h := pointedGHConverges_of_isometryEquiv κ hGH
        have hfun : (fun i => jt i (κ.symm q)) = fun i => p (φ i) :=
          funext fun i => ((hjtpt i).2.trans (hjNpt i).2)
        rw [hfun]
        exact h
      have hsecM' : ∀ i, ∀ y ∈ Metric.ball (jt i (κ.symm q)) (Hb i),
          SectionalBoundedBelowAt (g (φ i)) y (-((Hb i)⁻¹ ^ 2)) := by
        intro i y hy
        rw [(hjtpt i).2, (hjNpt i).2] at hy
        exact hsecM i y hy
      -- T4 + T5 on `N'`
      obtain ⟨R₃, -, hball⟩ := exists_scale_eventually_open_ball_bundle_type_finite
        (M := fun i => X (φ i))
        (rbM := fun i => ⟨(g (φ i)).toRiemannianMetric⟩)
        (rmM := fun i => isRiemannianManifold_of_aligned (g (φ i)) (hmetric (φ i)))
        (crM := fun i => isContinuousRiemannianBundle_of_smoothRiemannianMetric (g (φ i)))
        (finrank_euclideanSpace_fin) (le_trans (by norm_num) hr') G' hG'norm (κ.symm q) Hc
        hcone' (fun i => g (φ i)) (fun i => isMetricNorm_of_riemannianBundle (g (φ i))) jt
        hjtexh hjtconv hjtdist hjtcov hGH' Hb hHb hsecM' D' W' hW' hℓ.le hW'B hW'dir hdu'
      refine ⟨N', mN'.toUniformSpace.toTopologicalSpace, cN', hMN', κ.toHomeomorph, R₃,
        fun R hR => ?_⟩
      filter_upwards [hball R hR] with i hi ρ hρ
      obtain ⟨Ψ, hΨs, hΨt⟩ := hi ρ hρ
      refine ⟨Ψ.trans D'.toPartialDiffeomorph, ?_, ?_⟩
      · rw [PartialDiffeomorph.trans_source, hΨs, (hjtpt i).2, (hjNpt i).2]
        exact inter_eq_left.mpr fun x _ => mem_univ _
      · apply eq_univ_of_forall
        intro z
        refine ⟨mem_univ z, ?_⟩
        change D'.symm z ∈ Ψ.target
        rw [hΨt]
        exact mem_univ _
  refine ⟨φ, hφ, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hGH, C, mC, o, ⟨Hc⟩, hcone, h3⟩

/-- **T0 = LFR49 (row, LPA02's shape).** For ANY sequence with LFR14's eventual hypotheses
(`10 ≤ K`) and LC57's ranges `δ, ε, e, T` fixed first: a subsequence `k`, ONE scale `R ≥ T`, one
complete nonnegative `C^{K-1}` model `(N, G, q)` with pointed convergence, its cone `(C, o)`, a
smooth `Ns ≃ₜ N`, and one tail on which, at the scale `R`: (1) a Kleiner–Lott `δ`-map to `(C, o)`;
(2) an LC30 radial function with LC31's cutoff; (3) every open ball `B(p_{k j}, ρ' R)`,
`ρ' ∈ [1/5, 2]`, is diffeomorphic to `Ns` (both branches). -/
theorem lfr49_finite_joint_zero_packet
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
            Ψ.source = Metric.ball (p (k j)) (ρ' * R) ∧ Ψ.target = univ := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hGH, C, mC, o, ⟨Hc⟩, hcone,
      Ns, tNs, cNs, hNs, hhom, R₃, h3'⟩ :=
    lfr49_finite_model_ball_type_all_scales K hK hr hv A g hmetric p hvol hcurv hη hL hsec
  obtain ⟨Hb, hHb, hsecM⟩ := exists_curvature_scale_along_of_eventual g hmetric p hη hL hsec hφ
  obtain ⟨R₁, hR₁, h12⟩ := exists_scale_eventually_cone_radial_witnesses
    (M := fun i => X (φ i)) (fun i => g (φ i)) (fun i => hmetric (φ i)) hGH Hc hcone Hb hHb
    hsecM hδ hδ1 hε hε1 he he1
  set R : ℝ := max (max R₁ R₃) T with hRdef
  have hR1 : R₁ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hR3 : R₃ ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  have hR : 0 < R := hR₁.trans_le hR1
  refine ⟨φ, hφ, R, le_max_right _ _, hR, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG,
    hGH, C, mC, o, ⟨Hc⟩, hcone, Ns, tNs, cNs, hNs, hhom, ?_⟩
  filter_upwards [h12 R hR hR1, h3' R hR3] with i h12i h3i
  exact ⟨h12i.1, h12i.2, h3i⟩

end DifferentialGeometry.Geometry.Collapse
