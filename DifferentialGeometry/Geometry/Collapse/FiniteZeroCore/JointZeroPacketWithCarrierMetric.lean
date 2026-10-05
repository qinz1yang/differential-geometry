import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.JointZeroPacketWithCarrier

/-!
# T0′ with its carrier and, on a compact model, the model metric on the smooth model

`lfr49_finite_model_ball_type_all_scales_withCarrier` exports, in its compact branch, only
`CompactSpace Ns`. LFR53 (`isCompactNonnegativeType_of_finite_metric`, used by LFR54's compact clause)
needs the compact model as a closed manifold WITH its `C^{K-1}` metric of `sec ≥ 0`. In the compact
branch the smooth model is the limit `N` itself (`Ns := N`, `Homeomorph.refl`), so the limit metric `G`
is a metric on `Ns`. `lfr49_finite_model_ball_type_all_scales_withCarrierMetric` is the same theorem with
that metric added to the compact branch (proof: the same, the compact branch exports `G`).
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
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **T0′ with its carrier and the compact metric.** `lfr49_finite_model_ball_type_all_scales_withCarrier`
with, in the compact branch, also the `C^{K-1}` limit metric of `sec ≥ 0` on the smooth model `Ns`
ITSELF (there `Ns` is the limit `N` with its own atlas): either `Ns` is compact, eventually the
sources lie in `B(p, R₀)` and `Ns` carries that metric, or a core coordinate `u` of `Ns` carries, for every `R ≥ R₀` on one tail, the actual
sublevels of every admissible radial function of `(X, R⁻¹ d)` onto cores `{u ≤ T}`, and `u` is the
fibre radius of a smooth Riemannian soul bundle `D : TotalSpace F V ≃ Ns` with base `Fin 0 → ℝ`
(rank 3), `AddCircle 1` (rank 2), or a compact connected surface on `𝓡 2` (rank 1) carrying a
metric with `sec ≥ 0`. -/
theorem lfr49_finite_model_ball_type_all_scales_withCarrierMetric
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
        (∀ (x : N) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x u₁ u₂) ∧
        PointedGHConverges (fun j => p (k j)) q ∧
        ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧ ProperSpace C ∧
          (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R' : ℝ, ∀ hR' : 0 < R', R₀ ≤ R' →
            Nonempty (@KleinerLottApprox N C (mN.rescale R'⁻¹ (inv_pos.mpr hR')) mC q o τ)) ∧
        ∃ (Ns : Type) (_ : TopologicalSpace Ns) (_ : ChartedSpace E3 Ns)
          (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N), ∃ R₀ : ℝ, 0 < R₀ ∧
          (∀ R : ℝ, R₀ ≤ R → ∀ᶠ j in atTop, ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
            ∃ Ψ : PartialDiffeomorph I3 I3 (X (k j)) Ns ∞,
              Ψ.source = Metric.ball (p (k j)) (ρ' * R) ∧ Ψ.target = univ) ∧
          ((CompactSpace Ns ∧ (∀ᶠ j in atTop, ∀ x : X (k j), dist (p (k j)) x < R₀) ∧
            ∃ G' : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : Ns → Type _),
              ∀ (x : Ns) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G'.sectionalCurvature x u₁ u₂) ∨
           ∃ u : Ns → ℝ,
            (∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R → ∀ᶠ j in atTop,
              ∀ (ηs : X (k j) → ℝ) (eη : ℝ), eη < 1 / 40 →
              (letI := (mX (k j)).rescale R⁻¹ (inv_pos.mpr hR)
              (∀ x, |ηs x - dist (p (k j)) x| < eη) ∧
                LipschitzWith (1 / 64 : ℝ≥0) (fun x => ηs x - dist (p (k j)) x) ∧
                ∃ Wi : Set (X (k j)), IsOpen Wi ∧
                  (∀ x, 1 / 10 ≤ dist (p (k j)) x → dist (p (k j)) x ≤ 10 → x ∈ Wi) ∧
                  ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ηs Wi) →
              ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∃ T : ℝ, 0 < T ∧
                ∃ Ψ : PartialDiffeomorph I3 I3 (X (k j)) Ns ∞,
                  {y | ηs y ≤ ρ} ⊆ Ψ.source ∧ Ψ '' {y | ηs y ≤ ρ} = {x | u x ≤ T}) ∧
            ((∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
                (_ : FiniteDimensional ℝ F) (V : (Fin 0 → ℝ) → Type)
                (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
                (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
                (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, Fin 0 → ℝ))
                (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, Fin 0 → ℝ) ∞ F V)
                (D : Diffeomorph (𝓘(ℝ, Fin 0 → ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
                Module.finrank ℝ F = 3 ∧ ∀ x, u x = ‖(D.symm x).2‖) ∨
             (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
                (_ : FiniteDimensional ℝ F) (V : AddCircle (1 : ℝ) → Type)
                (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
                (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
                (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ))
                (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V)
                (D : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
                Module.finrank ℝ F = 2 ∧ ∀ x, u x = ‖(D.symm x).2‖) ∨
             ∃ (B : Type) (_ : TopologicalSpace B) (_ : ChartedSpace E2 B)
                (_ : IsManifold (𝓡 2) ∞ B) (_ : CompactSpace B) (_ : T2Space B)
                (_ : ConnectedSpace B)
                (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
                (_ : FiniteDimensional ℝ F) (V : B → Type)
                (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
                (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
                (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V (𝓡 2))
                (_ : IsContMDiffRiemannianBundle (𝓡 2) ∞ F V)
                (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Ns ∞),
                Module.finrank ℝ F = 1 ∧ (∀ x, u x = ‖(D.symm x).2‖) ∧
                ∃ nB : ℕ∞ω, 2 ≤ nB ∧
                  ∃ kB : ContMDiffRiemannianMetric (𝓡 2) nB E2 (TangentSpace (𝓡 2) : B → Type _),
                    ∀ (x : B) (u₁ u₂ : TangentSpace (𝓡 2) x),
                      0 ≤ kB.sectionalCurvature x u₁ u₂)) := by
  have instNZ_LPA02 : NeZero (Module.finrank ℝ E3) :=
    ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, hsecG⟩ :=
    exists_finite_cheeger_gromov_limit_with_nonneg_sectional_of_eventual_bounds 3 K
      (by norm_num) (by omega) hr hv A g hmetric p hvol hcurv hη hL hsec
  obtain ⟨C, mC, o, ⟨Hc⟩, hCp, -, -, hcone⟩ :=
    exists_finite_cone_package_of_limit (by omega : 3 ≤ K) G hRiem hsecG q
  obtain ⟨Hb, hHb, hsecM⟩ := exists_curvature_scale_along_of_eventual g hmetric p hη hL hsec hφ
  refine ⟨φ, hφ, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hGH, C, mC, o, ⟨Hc⟩, hCp,
    hcone, ?_⟩
  by_cases hc : CompactSpace N
  · obtain ⟨R₃, hR₃, h3⟩ := exists_scale_eventually_compact_model_type_of_finite_limit
      (X := fun i => X (φ i)) (by omega : 1 ≤ K) (fun i => g (φ i)) (fun i => hmetric (φ i))
      (fun i => p (φ i)) G q j hpt hexh hconv hdist
    refine ⟨N, inferInstance, cN, hMN, Homeomorph.refl N, R₃, hR₃, h3, Or.inl ⟨hc, ?_, G, hsecG⟩⟩
    filter_upwards [h3 R₃ le_rfl] with i hi x
    obtain ⟨Ψ, hΨs, hΨt⟩ := hi (1 / 5) ⟨le_rfl, by norm_num⟩
    have hsrc : Ψ.toPartialEquiv.symm '' Ψ.target = Ψ.source :=
      Ψ.toPartialEquiv.symm_image_target_eq_source
    have hcpt : IsCompact Ψ.source := by
      rw [← hsrc, hΨt]
      refine isCompact_univ.image_of_continuousOn ?_
      have h := Ψ.symm.contMDiffOn.continuousOn
      rw [PartialDiffeomorph.symm_source, hΨt] at h
      exact h
    have hne : Ψ.source.Nonempty := ⟨p (φ i), by
      rw [hΨs]; exact mem_ball_self (by positivity)⟩
    have huniv := (IsClopen.eq_univ ⟨hcpt.isClosed, Ψ.open_source⟩ hne)
    have hx : x ∈ Ψ.source := huniv ▸ mem_univ x
    rw [hΨs, mem_ball, dist_comm] at hx
    linarith
  · have hnc : NoncompactSpace N := not_compactSpace_iff.mp hc
    let rbN_LPA02 : RiemannianBundle (fun x : N => TangentSpace I3 x) := ⟨G.toRiemannianMetric⟩
    have instRM_LPA02 : IsRiemannianManifold I3 N := hRiem
    have hGnorm : ∀ (z : N) (w : TangentSpace I3 z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner z w w)) := by
      intro z w
      rw [← ofReal_norm, norm_eq_sqrt_real_inner]
      rfl
    obtain ⟨m, rfl⟩ : ∃ m, K = m + 10 := ⟨K - 10, by omega⟩
    have hr8 : (3 : ℕ∞) ≤ ((m + 8 : ℕ) : ℕ∞) := by exact_mod_cast (show 3 ≤ m + 8 by omega)
    have hr2 : (2 : ℕ∞) ≤ ((m + 8 : ℕ) : ℕ∞) := by exact_mod_cast (show 2 ≤ m + 8 by omega)
    let G8 : ContMDiffRiemannianMetric I3 ((((m + 8 : ℕ) : ℕ∞) : ℕ∞ω) + 1) E3
        (TangentSpace I3 : N → Type _) := G
    have hGnorm8 : ∀ (z : N) (w : TangentSpace I3 z),
        ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G8.inner z w w)) := hGnorm
    have hsec8 : ∀ (x : N) (v w : TangentSpace I3 x), 0 ≤ G8.sectionalCurvature x v w := hsecG
    -- LFR48 on the limit
    obtain ⟨jN, hjNpt, -, -, hjNexh, hjNconv, hjNdist, -⟩ :=
      exists_smooth_comparison_maps_of_finite_limit (X := fun i => X (φ i)) (by omega)
        (fun i => g (φ i)) (fun i => hmetric (φ i)) (fun i => p (φ i)) G q j hpt hexh hconv
        hdist
    -- LFR45: the soul and its tube
    obtain ⟨S, hSne, hSc, hSconn, -, hslice, -, hd3, htg, hout, ε₀, hε₀, ψ, hψs, hψ, hψexp, -,
        hdS, -, -⟩ := exists_finite_soul_strict_outward_tube_data G8 hr8 hGnorm8 hsec8
    -- the common finishing step over a soul base
    have finish : ∀ {d : ℕ} (_ : IsEmbeddedSliceOfOrder I3 ((((m + 8 : ℕ) : ℕ∞)) : ℕ∞ω) d S)
        (_ : d ≤ 3)
        {EB : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
        (_ : Module.finrank ℝ EB = d)
        {B : Type} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
        [CompactSpace B] [T2Space B]
        (b : B → N) (_ : ContMDiff 𝓘(ℝ, EB) I3 ((((m + 8 : ℕ) : ℕ∞) - 1 : ℕ∞) : ℕ∞ω) b)
        (_ : Injective b) (_ : range b = S)
        (_ : ∃ R : N → B, (∀ s, R (b s) = s) ∧
          ∀ x ∈ S, ContMDiffAt I3 𝓘(ℝ, EB) ((((m + 8 : ℕ) : ℕ∞) - 1 : ℕ∞) : ℕ∞ω) R x),
        ∃ (N' : Type) (mN' : MetricSpace N') (cN' : ChartedSpace E3 N')
          (_ : IsManifold I3 ∞ N') (_ : N' ≃ᵢ N)
          (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
          (_ : FiniteDimensional ℝ F) (V : B → Type)
          (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
          (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
          (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB))
          (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V)
          (D : Diffeomorph (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) N' ∞),
          Module.finrank ℝ EB + Module.finrank ℝ F = 3 ∧
          ∃ R₃ : ℝ, 0 < R₃ ∧
            (∀ R : ℝ, R₃ ≤ R → ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2,
              ∃ Ψ : PartialDiffeomorph I3 I3 (X (φ i)) N' ∞,
                Ψ.source = Metric.ball (p (φ i)) (ρ * R) ∧ Ψ.target = univ) ∧
            (∀ R : ℝ, ∀ hR : 0 < R, R₃ ≤ R → ∀ᶠ i in atTop,
              ∀ (ηs : X (φ i) → ℝ) (eη : ℝ), eη < 1 / 40 →
              (letI := (mX (φ i)).rescale R⁻¹ (inv_pos.mpr hR)
              (∀ x, |ηs x - dist (p (φ i)) x| < eη) ∧
                LipschitzWith (1 / 64 : ℝ≥0) (fun x => ηs x - dist (p (φ i)) x) ∧
                ∃ Wi : Set (X (φ i)), IsOpen Wi ∧
                  (∀ x, 1 / 10 ≤ dist (p (φ i)) x → dist (p (φ i)) x ≤ 10 → x ∈ Wi) ∧
                  ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ηs Wi) →
              ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∃ T : ℝ, 0 < T ∧
                ∃ Ψ : PartialDiffeomorph I3 I3 (X (φ i)) N' ∞,
                  {y | ηs y ≤ ρ} ⊆ Ψ.source ∧
                    Ψ '' {y | ηs y ≤ ρ} = {x | ‖(D.symm x).2‖ ≤ T}) := by
      intro d hS hd3' EB instEB1_LPA02 instEB2_LPA02 instEB3_LPA02 hEB B instB1_LPA02
        instB2_LPA02 instB3_LPA02 instB4_LPA02 instB5_LPA02 b hb hbinj hbS hbinv
      obtain ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, ι, hdimP, hι, hιb, hιlin, hιnorm,
          hιν, hιonto⟩ := exists_soul_bundle_data_of_base hr2 G8 hS
            (by rw [finrank_euclideanSpace_fin]; exact hd3') hEB b hb hbS hbinv
      have hdimP' : Module.finrank ℝ EB + Module.finrank ℝ F = 3 := by
        rw [hdimP, finrank_euclideanSpace_fin]
      -- LFR46 (tube form) + LFR47 flow + T5
      obtain ⟨X0, ℓ, A₂, eN, hℓ, -, hXB, hmargin, -, W, hW, hWX, -, hdu, -, -, -, -⟩ :=
        lfr49_noncompact_carrier_data G8 hr8 hGnorm8 hsec8 hSc hSne hout hε₀ ψ hψs hψ hψexp
          hdS b hbinj hbS hbinv ι hι hιb hιlin hιnorm hιν hιonto q
      -- (a)
      obtain ⟨N', mN', cN', hMN', rbN', hRM', r', hr', G', κ, D', W', jt, hpN', hG'norm, hκ, hκG,
          -, hW', hW'X, hdu', hjtpt, hjtexh, hjtconv, hjtdist, hjtcov⟩ :=
        lfr49A_carrier_package (X := fun i => X (φ i))
          (show (6 : ℕ∞) ≤ ((m + 8 : ℕ) : ℕ∞) by exact_mod_cast (show 6 ≤ m + 8 by omega))
          G8 hGnorm8 (fun i => g (φ i))
          (fun i => hmetric (φ i)) q jN hjNexh
          (fun x L hL hLt => (hjNconv x L hL hLt).mono_order (by omega)) hjNdist hdimP' eN W hW
          hdu
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
      have hjtp : ∀ i, jt i (κ.symm q) = p (φ i) := fun i => (hjtpt i).2.trans (hjNpt i).2
      have hGH' : PointedGHConverges (fun i => jt i (κ.symm q)) (κ.symm q) := by
        have h := pointedGHConverges_of_isometryEquiv κ hGH
        have hfun : (fun i => jt i (κ.symm q)) = fun i => p (φ i) := funext hjtp
        rw [hfun]
        exact h
      have hsecM' : ∀ i, ∀ y ∈ Metric.ball (jt i (κ.symm q)) (Hb i),
          SectionalBoundedBelowAt (g (φ i)) y (-((Hb i)⁻¹ ^ 2)) := by
        intro i y hy
        rw [hjtp i] at hy
        exact hsecM i y hy
      -- T4 + T5 on `N'`: open balls
      obtain ⟨R₃, hR₃, hball⟩ := exists_scale_eventually_open_ball_bundle_type_finite
        (M := fun i => X (φ i))
        (rbM := fun i => ⟨(g (φ i)).toRiemannianMetric⟩)
        (rmM := fun i => isRiemannianManifold_of_aligned (g (φ i)) (hmetric (φ i)))
        (crM := fun i => isContinuousRiemannianBundle_of_smoothRiemannianMetric (g (φ i)))
        (finrank_euclideanSpace_fin) (le_trans (by norm_num) hr') G' hG'norm (κ.symm q) Hc
        hcone' (fun i => g (φ i)) (fun i => isMetricNorm_of_riemannianBundle (g (φ i))) jt
        hjtexh hjtconv hjtdist hjtcov hGH' Hb hHb hsecM' D' W' hW' hℓ.le hW'B hW'dir hdu'
      -- T4 + T5 closed on `N'`: the actual sublevels
      obtain ⟨R₄, hR₄, hclosed⟩ := exists_scale_eventually_sublevel_onto_disc_core
        (M := fun i => X (φ i))
        (rbM := fun i => ⟨(g (φ i)).toRiemannianMetric⟩)
        (rmM := fun i => isRiemannianManifold_of_aligned (g (φ i)) (hmetric (φ i)))
        (crM := fun i => isContinuousRiemannianBundle_of_smoothRiemannianMetric (g (φ i)))
        (le_trans (by norm_num) hr') G' hG'norm (κ.symm q) (fun i => g (φ i))
        (fun i => isMetricNorm_of_riemannianBundle (g (φ i))) jt
        hjtexh hjtconv hjtdist hjtcov D' W' hW' hℓ.le hW'B hW'dir hdu'
      refine ⟨N', mN', cN', hMN', κ, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D', hdimP',
        max R₃ R₄, lt_of_lt_of_le hR₃ (le_max_left _ _), fun R hR => ?_, fun R hRpos hR => ?_⟩
      · filter_upwards [hball R ((le_max_left _ _).trans hR)] with i hi ρ hρ
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
      · filter_upwards [hclosed R hRpos ((le_max_right _ _).trans hR)] with i hi ηs eη heη hηs
          ρ hρ
        obtain ⟨h1, h2, Wi, h3, h4, h5⟩ := hηs
        rw [← hjtp i] at h1 h2 h4
        obtain ⟨T, hT, Ψ, hΨs, hΨi, -⟩ := hi ηs eη heη ⟨h1, h2, Wi, h3, h4, h5⟩ ρ hρ
        exact ⟨T, hT, Ψ, hΨs, hΨi⟩
    -- the case split on the soul dimension
    set d := maxSliceDimOfOrder I3 ((((m + 8 : ℕ) : ℕ∞)) : ℕ∞ω) S with hddef
    have hd : d < 3 := by rw [finrank_euclideanSpace_fin] at hd3; exact hd3
    rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with h0 | h1 | h2
    · -- point soul
      rw [h0] at hslice
      obtain ⟨x, hx⟩ := hSne
      have hSx : S = {x} := eq_singleton_of_isEmbeddedSliceOfOrder_zero hslice
        hSconn.isPreconnected hx
      obtain ⟨b, hb, hbinj, hbS, R, hRb, hR⟩ := soulBase_point_finite (I := I3) x
        ((((m + 8 : ℕ) : ℕ∞) - 1 : ℕ∞) : ℕ∞ω)
      obtain ⟨N', mN', cN', hMN', κ, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D', hdimFD,
          R₃, hR₃, hballs, hclosed⟩ := finish hslice (by norm_num) (EB := Fin 0 → ℝ)
        (Module.finrank_fin_fun ℝ) b hb hbinj (hbS.trans hSx.symm) ⟨R, hRb, hSx ▸ hR⟩
      refine ⟨N', mN'.toUniformSpace.toTopologicalSpace, cN', hMN', κ.toHomeomorph, R₃, hR₃,
        hballs, Or.inr ⟨fun x => ‖(D'.symm x).2‖, hclosed, Or.inl ⟨F, i1, i2, i3, V, j1, j2, j3,
        j4, j5, j6, j7, D', ?_, fun _ => rfl⟩⟩⟩
      rw [Module.finrank_fin_fun] at hdimFD
      omega
    · -- closed geodesic soul
      rw [h1] at hslice
      obtain ⟨p0, ℓ0, hℓ0, hunit, hper, hinj, hSrange⟩ :=
        exists_closedGeodesic_of_slice_dim_one G8 hr2 hGnorm8 hSc hSconn hslice htg
      obtain ⟨b, -, hb, hbinj, hbS, R, hRb, hR⟩ :=
        soulBase_closedGeodesic G8 hr2 hGnorm8 p0 hℓ0 hunit hper hinj
      obtain ⟨N', mN', cN', hMN', κ, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D', hdimFD,
          R₃, hR₃, hballs, hclosed⟩ := finish hslice (by norm_num) (EB := ℝ)
        (Module.finrank_self ℝ) b hb hbinj (hbS.trans hSrange.symm)
        ⟨R, hRb, fun x hx => hR x (hSrange ▸ hx)⟩
      refine ⟨N', mN'.toUniformSpace.toTopologicalSpace, cN', hMN', κ.toHomeomorph, R₃, hR₃,
        hballs, Or.inr ⟨fun x => ‖(D'.symm x).2‖, hclosed, Or.inr (Or.inl ⟨F, i1, i2, i3, V, j1,
        j2, j3, j4, j5, j6, j7, D', ?_, fun _ => rfl⟩)⟩⟩
      rw [Module.finrank_self] at hdimFD
      omega
    · -- surface soul
      rw [h2] at hslice
      obtain ⟨Shat, hShat, hrest⟩ := soulBase_surface_carrier G8 hr2 hGnorm8
        (finrank_euclideanSpace_fin) hSc ⟨hSne.some, hSne.some_mem⟩ hslice
      let csOld_LPA02 := DifferentialGeometry.Geometry.Topology.embeddedSliceChartedSpace hShat
      obtain ⟨hcS, htS, hmS, b, hb, hbinj, hbS, R, hRb, hR⟩ := hrest
      have instC_LPA02 : CompactSpace Shat := hcS
      have instT_LPA02 : T2Space Shat := htS
      have instM_LPA02 : IsManifold 𝓘(ℝ, Fin 2 → ℝ) ∞ Shat := hmS
      -- (b): the base model `𝓡 2`
      obtain ⟨csNew_LPA02, instMNew_LPA02, hb', hR'⟩ :=
        exists_euclidean_plane_base_of_fin_two (IM := I3) b hb R S hR
      -- the base is connected: it is the image of the connected soul under `R`
      have instConn_LPA02 : ConnectedSpace Shat := by
        have himg : R '' S = univ := by
          apply eq_univ_of_forall
          intro s
          exact ⟨b s, hbS ▸ mem_range_self s, hRb s⟩
        have hRc : ContinuousOn R S := fun x hx => (hR x hx).continuousAt.continuousWithinAt
        have hcon := hSconn.image R hRc
        rw [himg] at hcon
        exact connectedSpace_iff_univ.mpr hcon
      -- EXIT-51: the induced metric on the base has `sec ≥ 0`
      obtain ⟨gS, -, hgS⟩ := exists_inducedMetric_sectional_eq (B := Shat) G8
        (show (4 : ℕ∞) ≤ ((m + 8 : ℕ) : ℕ∞) by exact_mod_cast (show 4 ≤ m + 8 by omega))
        hGnorm8 hslice htg b hb' hbS ⟨R, hRb, hR'⟩
      obtain ⟨N', mN', cN', hMN', κ, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D', hdimFD,
          R₃, hR₃, hballs, hclosed⟩ := finish hslice (by norm_num) (EB := E2)
        (finrank_euclideanSpace_fin) b hb' hbinj hbS ⟨R, hRb, hR'⟩
      refine ⟨N', mN'.toUniformSpace.toTopologicalSpace, cN', hMN', κ.toHomeomorph, R₃, hR₃,
        hballs, Or.inr ⟨fun x => ‖(D'.symm x).2‖, hclosed, Or.inr (Or.inr ⟨Shat, inferInstance,
        csNew_LPA02, instMNew_LPA02, instC_LPA02, instT_LPA02, instConn_LPA02, F, i1, i2, i3, V,
        j1, j2, j3, j4, j5, j6, j7, D', ?_, fun _ => rfl, _, ?_, gS, fun s u₁ u₂ => ?_⟩)⟩⟩
      · rw [finrank_euclideanSpace_fin] at hdimFD
        omega
      · have h46 : ((m + 8 : ℕ) : ℕ∞) - 2 = ((m + 6 : ℕ) : ℕ∞) := by
          rw [show (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) from rfl, ← ENat.natCast_sub]
          exact congrArg _ (by omega)
        rw [h46]
        exact WithTop.coe_le_coe.mpr (by exact_mod_cast (show 2 ≤ m + 6 by omega))
      · rw [hgS s u₁ u₂]
        exact hsec8 _ _ _

end DifferentialGeometry.Geometry.Collapse
