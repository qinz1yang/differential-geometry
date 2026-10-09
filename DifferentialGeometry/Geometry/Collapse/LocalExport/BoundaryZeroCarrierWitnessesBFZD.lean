import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroFamilyIdx
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA02WithCarrierMetric

/-!
# LPA02's witnesses WITH the carrier on the completed interiors (lane BFAM-ZD)

External review 53 §4.1 (A-Z, binding dispositions): the type witness of the actual zero sublevels
must be KEPT along the regional LPA02 / LPA05 path of the boundary producer, never taken from a
second existence statement. The regional LPA02 (`lpa02_uniform_joint_zero_witnesses_boundary_BDRY2_IDX`,
lane BDRY-IDX, sequences at `δ_{n+1}`) runs LFR49 on the complete σ-compact connected completions
`((W n)°, d_ĝ)`; the carrier form of that kernel,
`lfr49_finite_model_ball_type_all_scales_withCarrierMetric`, has the SAME hypotheses (no compactness
of the sources). Running it instead, with the closed carrier step of
`lpa02_uniform_joint_zero_witnesses_withCarrierMetric` (the core coordinate `u` and the closed cores
of every admissible radial function at every large scale), gives:

* `lpa02_uniform_joint_zero_witnesses_boundary_withCarrier_BFZD`: the regional LPA02 statement with,
  for the SAME witnesses, a core coordinate `u : Ns → ℝ`, for the SAME selected radial function `F`
  and every `t ∈ [1/5, 2]` a level `T₀ > 0` and an ambient partial diffeomorphism `Ψ` with
  `{F ≤ t} ⊆ dom Ψ`, `Ψ '' {F ≤ t} = {u ≤ T₀}`, and the type of `u` (compact model with its
  `C^{K-1}` metric of `sec ≥ 0` and `u = 0`, or the fibre radius of a point / circle / surface soul
  bundle). The Lipschitz tolerance of `F` is `ε ≤ 1/64` (the closed LC38 margin).
* `lpa02_total_witnesses_boundary_withCarrier_BFZD`: the same made total (BDRY-3's helper).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function Manifold
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry GC.Endpoint
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **The regional LPA02 with the carrier** (lane BFAM-ZD): the statement of
`lpa02_uniform_joint_zero_witnesses_boundary_BDRY2_IDX` (sequences at `δ_{n+1}`, eligible pairs
`D(p) > 5`, `0 < r ≤ 2 r_p^g(w')`) with `ε ≤ 1/64` and, for the SAME witnesses: a core coordinate
`u` of the smooth model `Ns`; for the SAME radial function `F` and every `t ∈ [1/5, 2]`, an ambient
partial diffeomorphism carrying the actual sublevel `{F ≤ t}` onto a core `{u ≤ T₀}`; the type of
`u` (compact model with a `C^{K-1}` metric of `sec ≥ 0`, or a soul-bundle fibre radius). -/
theorem lpa02_uniform_joint_zero_witnesses_boundary_withCarrier_BFZD :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {ε δ' e T : ℝ}, 0 < ε → ε ≤ 1 / 64 → 0 < δ' → 0 < e → e < 1 / 40 →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
        (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤)),
        (∀ n, RiemannianMetricComplete (I := 𝓡 3) (ĝ n)) →
        (∀ n (x : (W n).pieceInterior ⊤), ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
          (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        letI := inducedMetricSpace (ĝ n)
        ∀ (p : (W n).pieceInterior ⊤), ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) p →
        ∀ (r : ℝ) (hr : 0 < r),
        r ≤ 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) →
        ∃ s ∈ Icc T V, ∃ hs : 0 < s,
        ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace E3 N),
          letI := mN
          letI := cN
          ∃ (_ : IsManifold I3 ∞ N)
            (G : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3
              (TangentSpace I3 : N → Type _))
            (q : N),
            ProperSpace N ∧ ConnectedSpace N ∧
            (letI : RiemannianBundle (fun x : N => TangentSpace I3 x) := ⟨G.toRiemannianMetric⟩
             IsRiemannianManifold I3 N) ∧
            (∀ (x : N) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x u₁ u₂) ∧
            fourPointComparison 0 (univ : Set N) ∧
            (∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
              f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂) ∧
            ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
              ProperSpace C ∧
              (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R' : ℝ, ∀ hR' : 0 < R', R₀ ≤ R' →
                Nonempty (@KleinerLottApprox N C (mN.rescale R'⁻¹ (inv_pos.mpr hR')) mC q o τ)) ∧
            ∃ (Ns : Type) (_ : TopologicalSpace Ns) (_ : ChartedSpace E3 Ns)
              (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N) (u : Ns → ℝ),
              (∀ y ∈ Metric.ball p (400 * (s * r)),
                SectionalBoundedBelowAt (ĝ n) y (-((1 / 60) ^ 2 * (s * r)⁻¹ ^ 2))) ∧
              Nonempty (@KleinerLottApprox ((W n).pieceInterior ⊤) C
                ((inducedMetricSpace (ĝ n)).rescale (s * r)⁻¹ (inv_pos.mpr (mul_pos hs hr))) mC
                p o δ) ∧
              (letI := (inducedMetricSpace (ĝ n)).rescale (s * r)⁻¹
                (inv_pos.mpr (mul_pos hs hr))
              let gR := scaleMetric ((s * r)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (mul_pos hs hr)) 2)
                (ĝ n)
              ∃ F : (W n).pieceInterior ⊤ → ℝ,
                (∀ t ∈ Icc (1 / 5 : ℝ) 2, ∃ T₀ : ℝ, 0 < T₀ ∧
                  ∃ Ψ : PartialDiffeomorph I3 I3 ((W n).pieceInterior ⊤) Ns ∞,
                    {x | F x ≤ t} ⊆ Ψ.source ∧ Ψ '' {x | F x ≤ t} = {y | u y ≤ T₀}) ∧
                LipschitzWith (Real.toNNReal (1 + ε)) F ∧
                (∃ O : Set ((W n).pieceInterior ⊤), IsOpen O ∧
                  {x : (W n).pieceInterior ⊤ | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
                  ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O) ∧
                (∀ x, |F x - Metric.infDist x {p}| < e) ∧
                (∀ x, x ∉ {x : (W n).pieceInterior ⊤ | 1 / 20 < dist x p ∧ dist x p < 20} →
                  F x = Metric.infDist x {p}) ∧
                (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤
                  ε * dist x y) ∧
                (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
                (∀ q' ∈ {x : (W n).pieceInterior ⊤ | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
                  1 - ε ≤ Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ∧
                    Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ≤ 1 + ε) ∧
                (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
                F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆
                  {x : (W n).pieceInterior ⊤ | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
                (∃ O' : Set ((W n).pieceInterior ⊤), IsOpen O' ∧ F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
                  ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q' ∈ O', gradFun gR F q' ≠ 0) ∧
                ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
                  ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
                  (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
                  (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) → annularCutoff cutoffProfile (F x) = 1) ∧
                  tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
                    {x : (W n).pieceInterior ⊤ | 1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
                  ∀ q', Real.sqrt (gR.inner q'
                    (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')
                    (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')) ≤
                      L * (1 + ε)) ∧
              (∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
                ∃ Ψ : PartialDiffeomorph I3 I3 ((W n).pieceInterior ⊤) Ns ∞,
                  Ψ.source = Metric.ball p (ρ' * (s * r)) ∧ Ψ.target = univ) ∧
              ((CompactSpace Ns ∧ (∀ y, u y = 0) ∧
                ∃ G' : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : Ns → Type _),
                  ∀ (x : Ns) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G'.sectionalCurvature x u₁ u₂) ∨
               (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
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
                      ∀ (x : B) (u₁ u₂ : TangentSpace (𝓡 2) x), 0 ≤ kB.sectionalCurvature x u₁ u₂) := by
  obtain ⟨δ1, hδ1, hseqH⟩ := lpa02_normalized_sequence_hypotheses_boundary_BDRY2_IDX.{0}
  obtain ⟨δ2, hδ2, hbuf⟩ := completion_original_buffer_BDRY3
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro K hK A hA Λ w hΛ hw hwc ε δ' e T hε hε64 hδ' he he1 δ₀ hδ₀ hδ₀S W _ g B hcoll hder ĝ
    hcomp heq
  have hε1 : ε < 1 := by linarith
  have instNZ_BDRY3 : NeZero (Module.finrank ℝ E3) :=
    ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  let instM_BDRY3 : ∀ n, MetricSpace ((W n).pieceInterior ⊤) := fun n => inducedMetricSpace (ĝ n)
  have instC_BDRY3 : ∀ n, CompleteSpace ((W n).pieceInterior ⊤) := fun n =>
    completeSpace_completion_BDRY2 (W n) (ĝ n) (hcomp n)
  have hw'0 : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := by positivity
  have hw'c : w / (2 * (1 + 2 * Λ⁻¹) ^ 3) < euclideanThreeUnitBallVolume := by
    have h1 : 1 ≤ 1 + 2 * Λ⁻¹ := by have := inv_pos.mpr hΛ; linarith
    have h2 : 1 ≤ 2 * (1 + 2 * Λ⁻¹) ^ 3 := by nlinarith [one_le_pow₀ (n := 3) h1]
    calc w / (2 * (1 + 2 * Λ⁻¹) ^ 3) ≤ w := div_le_self hw.le h2
      _ < euclideanThreeUnitBallVolume := hwc
  obtain ⟨δ, hδ0, hδ1', hδδ', hδr⟩ := exists_coneError_below_thresholds hε hδ'
  -- the LC58 kernel on the eligible pairs `(p, r)`
  obtain ⟨V, hTV, α₀, hGC⟩ := exists_uniform_scale_interval_of_eventual_witnesses
    (X := fun n => {pr : (W n).pieceInterior ⊤ × ℝ //
      ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) pr.1 ∧ 0 < pr.2 ∧
        pr.2 ≤ 2 * firstVolumeScale (g n) pr.1 (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))})
    (fun n y s => ∃ hs : 0 < s,
      ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace E3 N),
        letI := mN
        letI := cN
        ∃ (_ : IsManifold I3 ∞ N)
          (G : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3
            (TangentSpace I3 : N → Type _))
          (q : N),
          ProperSpace N ∧ ConnectedSpace N ∧
          (letI : RiemannianBundle (fun x : N => TangentSpace I3 x) := ⟨G.toRiemannianMetric⟩
           IsRiemannianManifold I3 N) ∧
          (∀ (x : N) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G.sectionalCurvature x u₁ u₂) ∧
          fourPointComparison 0 (univ : Set N) ∧
          (∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
            f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂) ∧
          ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
            ProperSpace C ∧
            (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R' : ℝ, ∀ hR' : 0 < R', R₀ ≤ R' →
              Nonempty (@KleinerLottApprox N C (mN.rescale R'⁻¹ (inv_pos.mpr hR')) mC q o τ)) ∧
          ∃ (Ns : Type) (_ : TopologicalSpace Ns) (_ : ChartedSpace E3 Ns)
            (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N) (u : Ns → ℝ),
            Nonempty (@KleinerLottApprox ((W n).pieceInterior ⊤) C
              ((instM_BDRY3 n).rescale (s * y.1.2)⁻¹ (inv_pos.mpr (mul_pos hs y.2.2.1))) mC
              y.1.1 o δ) ∧
            (∀ (ηs : (W n).pieceInterior ⊤ → ℝ) (eη : ℝ), eη < 1 / 40 →
              (letI := (instM_BDRY3 n).rescale (s * y.1.2)⁻¹ (inv_pos.mpr (mul_pos hs y.2.2.1))
              (∀ x, |ηs x - dist y.1.1 x| < eη) ∧
                LipschitzWith (1 / 64 : ℝ≥0) (fun x => ηs x - dist y.1.1 x) ∧
                ∃ Wi : Set ((W n).pieceInterior ⊤), IsOpen Wi ∧
                  (∀ x, 1 / 10 ≤ dist y.1.1 x → dist y.1.1 x ≤ 10 → x ∈ Wi) ∧
                  ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ηs Wi) →
              ∀ t ∈ Icc (1 / 5 : ℝ) 2, ∃ T₀ : ℝ, 0 < T₀ ∧
                ∃ Ψ : PartialDiffeomorph I3 I3 ((W n).pieceInterior ⊤) Ns ∞,
                  {x | ηs x ≤ t} ⊆ Ψ.source ∧ Ψ '' {x | ηs x ≤ t} = {y | u y ≤ T₀}) ∧
            (∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
              ∃ Ψ : PartialDiffeomorph I3 I3 ((W n).pieceInterior ⊤) Ns ∞,
                Ψ.source = Metric.ball y.1.1 (ρ' * (s * y.1.2)) ∧ Ψ.target = univ) ∧
            ((CompactSpace Ns ∧ (∀ y, u y = 0) ∧
              ∃ G' : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : Ns → Type _),
                ∀ (x : Ns) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G'.sectionalCurvature x u₁ u₂) ∨
             (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
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
                    ∀ (x : B) (u₁ u₂ : TangentSpace (𝓡 2) x), 0 ≤ kB.sectionalCurvature x u₁ u₂)) T
    (by
      intro a ha z
      -- LPA02, first paragraph, on the completed interiors (G11)
      -- `obtain` would re-check the (large) goal in every `cases` motive: `Exists.elim` and
      -- projections instead
      have hsq := hseqH K (by omega) A hA hw'0 hw'c hδ₀ (hδ₀S.trans (min_le_left _ _)) W g B hcoll
        hder ĝ heq a ha (fun j => (z j).1.1) (fun j => (z j).2.1) (fun j => (z j).1.2)
        (fun j => (z j).2.2.1) (fun j => (z j).2.2.2)
      have hmetric' := hsq.1
      have hv0 := hsq.2.1
      have hvol' := hsq.2.2.1
      have hcurv' := hsq.2.2.2.1
      have hη := hsq.2.2.2.2.1
      have hL := hsq.2.2.2.2.2.1
      have hsec' := hsq.2.2.2.2.2.2
      -- LFR49 (T0′) on the rescaled complete σ-compact sources
      have h49 :=
        @lfr49_finite_model_ball_type_all_scales_withCarrierMetric K hK 1 _ one_pos hv0
          (fun R => (2 : ℝ) ^ (K + 2) *
            boundaryDerivativeConstant A K (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)))
          (fun j => (W (a j)).pieceInterior ⊤)
          (fun j => (instM_BDRY3 (a j)).rescale ((z j).1.2)⁻¹ (inv_pos.mpr (z j).2.2.1))
          (fun j => inferInstance) (fun j => inferInstance) (fun j => inferInstance)
          (fun j => ((instM_BDRY3 (a j)).rescale_completeSpace_iff _ _).mpr (instC_BDRY3 (a j)))
          (fun j => connectedSpace_pieceInterior_top_BDRY1 (W (a j)))
          (fun j => normalizedCenterMetric (ĝ (a j)) ((z j).1.2) (z j).2.2.1) hmetric'
          (fun j => (z j).1.1) hvol' hcurv' _ _ hη hL hsec'
      refine h49.elim fun k e1 => ?_
      have hk := e1.1
      refine e1.2.elim fun N e2 => ?_
      refine e2.elim fun mN e3 => ?_
      refine e3.elim fun cN e4 => ?_
      refine e4.elim fun hMN e5 => ?_
      refine e5.elim fun G e6 => ?_
      refine e6.elim fun q e7 => ?_
      have hprop := e7.1
      have hconn := e7.2.1
      have hRiem := e7.2.2.1
      have hsecG := e7.2.2.2.1
      have hGH := e7.2.2.2.2.1
      refine e7.2.2.2.2.2.elim fun C e8 => ?_
      refine e8.elim fun mC e9 => ?_
      refine e9.elim fun o e10 => ?_
      have hCp := e10.2.1
      have hcone := e10.2.2.1
      refine e10.2.2.2.elim fun Ns e11 => ?_
      refine e11.elim fun tNs e12 => ?_
      refine e12.elim fun cNs e13 => ?_
      refine e13.elim fun hNs e14 => ?_
      refine e14.elim fun hhom e15 => ?_
      refine e15.elim fun R₃ e16 => ?_
      have hR₃ := e16.1
      have h3 := e16.2.1
      have hcar := e16.2.2
      -- the model clauses: four-point comparison and segments
      let instRB_BDRY3 : RiemannianBundle (fun x : N => TangentSpace I3 x) :=
        ⟨G.toRiemannianMetric⟩
      have instRM_BDRY3 : IsRiemannianManifold I3 N := hRiem
      have hGnorm : ∀ (x : N) (u : TangentSpace I3 x),
          ‖u‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x u u)) := by
        intro x u
        rw [← ofReal_norm, norm_eq_sqrt_real_inner]
        rfl
      have hn : (2 : ℕ∞ω) ≤ ((K - 1 : ℕ) : ℕ∞ω) := by exact_mod_cast (show 2 ≤ K - 1 by omega)
      have hfour : fourPointComparison 0 (univ : Set N) :=
        DifferentialGeometry.Geometry.FiniteComparison.fourPointComparison_zero_univ_finite G hn
          hGnorm hsecG
      have hseg : ∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
          f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂ :=
        fun x y => Metric.exists_metric_segment_of_approximate_midpoints
          (DifferentialGeometry.Geometry.FiniteComparison.approximate_midpoints_finite G hn
            hGnorm) x y
      -- LFR49 step 1 along `k`, in the `scaleMetric` form of LC57
      refine (@exists_curvature_scale_along_of_eventual
        (fun j => (W (a j)).pieceInterior ⊤)
        (fun j => (instM_BDRY3 (a j)).rescale ((z j).1.2)⁻¹ (inv_pos.mpr (z j).2.2.1))
        (fun j => inferInstance) (fun j => inferInstance)
        (fun j => normalizedCenterMetric (ĝ (a j)) ((z j).1.2) (z j).2.2.1) hmetric'
        (fun j => (z j).1.1) _ _ hη hL hsec' k hk).elim fun Hb e17 => ?_
      have hHb := e17.1
      have hsecM := e17.2
      have hsecS : ∀ j, ∀ y ∈ @Metric.ball ((W (a (k j))).pieceInterior ⊤)
          ((instM_BDRY3 (a (k j))).rescale ((z (k j)).1.2)⁻¹
            (inv_pos.mpr (z (k j)).2.2.1)).toPseudoMetricSpace ((z (k j)).1.1) (Hb j),
          SectionalBoundedBelowAt (scaleMetric (((z (k j)).1.2)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (z (k j)).2.2.1) 2) (ĝ (a (k j)))) y (-((Hb j)⁻¹ ^ 2)) := by
        intro j y hy
        rw [← normalizedCenterMetric_eq_scaleMetric]
        exact hsecM j y hy
      -- LC57 (1): Kleiner–Lott maps at every large scale
      refine (exists_scale_eventually_normalized_cone_radial_witnesses
        (M := fun j => (W (a (k j))).pieceInterior ⊤) (fun j => ĝ (a (k j)))
        (fun j => inducedMetricSpace_hmetric (ĝ (a (k j))))
        (fun j => (z (k j)).1.2) (fun j => (z (k j)).2.2.1) hGH e10.1.some hcone Hb hHb hsecS
        hδ0 hδ1' hε hε1 he he1).elim fun R₀ e18 => ?_
      have hR₀ := e18.1
      have hall := e18.2
      -- the core coordinate and the closed cores at every large scale, in the `(R r)⁻¹` form
      have key : ∃ u : Ns → ℝ, ∃ R₄ : ℝ, 0 < R₄ ∧
          (∀ R : ℝ, ∀ hR : 0 < R, R₄ ≤ R → ∀ᶠ j in atTop,
            ∀ (ηs : (W (a (k j))).pieceInterior ⊤ → ℝ) (eη : ℝ), eη < 1 / 40 →
              (letI := (instM_BDRY3 (a (k j))).rescale (R * (z (k j)).1.2)⁻¹
                (inv_pos.mpr (mul_pos hR (z (k j)).2.2.1))
              (∀ x, |ηs x - dist (z (k j)).1.1 x| < eη) ∧
                LipschitzWith (1 / 64 : ℝ≥0) (fun x => ηs x - dist (z (k j)).1.1 x) ∧
                ∃ Wi : Set (((W (a (k j))).pieceInterior ⊤)), IsOpen Wi ∧
                  (∀ x, 1 / 10 ≤ dist (z (k j)).1.1 x → dist (z (k j)).1.1 x ≤ 10 → x ∈ Wi) ∧
                  ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ ηs Wi) →
              ∀ ρ ∈ Icc (1 / 5 : ℝ) 2, ∃ T₀ : ℝ, 0 < T₀ ∧
                ∃ Ψ : PartialDiffeomorph I3 I3 (((W (a (k j))).pieceInterior ⊤)) Ns ∞,
                  {x | ηs x ≤ ρ} ⊆ Ψ.source ∧ Ψ '' {x | ηs x ≤ ρ} = {y | u y ≤ T₀}) ∧
          ((CompactSpace Ns ∧ (∀ y, u y = 0) ∧
            ∃ G' : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : Ns → Type _),
              ∀ (x : Ns) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G'.sectionalCurvature x u₁ u₂) ∨
           (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
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
                  ∀ (x : B) (u₁ u₂ : TangentSpace (𝓡 2) x), 0 ≤ kB.sectionalCurvature x u₁ u₂) := by
        rcases hcar with ⟨hcNs, hdiam, hGc⟩ | ⟨u, hclosed, hcases⟩
        · refine ⟨fun _ => 0, 10 * R₃, by positivity, fun R hR hRR => ?_, Or.inl ⟨hcNs, fun _ => rfl, hGc⟩⟩
          filter_upwards [hdiam, h3 R (by linarith)] with j hj h3j ηs eη heη hηs ρ hρ
          obtain ⟨Ψ, hΨs, hΨt⟩ := h3j (1 / 5) ⟨le_rfl, by norm_num⟩
          have hsrc : Ψ.source = univ := by
            rw [hΨs]
            apply eq_univ_of_forall
            intro x
            have h1 : ((z (k j)).1.2)⁻¹ * dist (z (k j)).1.1 x < R₃ := hj x
            change ((z (k j)).1.2)⁻¹ * dist x (z (k j)).1.1 < 1 / 5 * R
            rw [dist_comm]
            linarith
          have hsub : {x | ηs x ≤ ρ} = univ := by
            apply eq_univ_of_forall
            intro x
            have h1 : ((z (k j)).1.2)⁻¹ * dist (z (k j)).1.1 x < R₃ := hj x
            have h2 : |ηs x - (R * (z (k j)).1.2)⁻¹ * dist (z (k j)).1.1 x| < eη := hηs.1 x
            have h3' : (R * (z (k j)).1.2)⁻¹ * dist (z (k j)).1.1 x < 1 / 10 := by
              rw [mul_inv, mul_assoc]
              calc R⁻¹ * (((z (k j)).1.2)⁻¹ * dist (z (k j)).1.1 x) < R⁻¹ * R₃ :=
                    mul_lt_mul_of_pos_left h1 (inv_pos.mpr hR)
                _ ≤ 1 / 10 := by
                  rw [inv_mul_le_iff₀ hR]
                  linarith
            have h4 := (abs_lt.mp h2).2
            change ηs x ≤ ρ
            linarith [hρ.1]
          refine ⟨1, one_pos, Ψ, by rw [hsub, hsrc], ?_⟩
          rw [hsub, ← hsrc, Ψ.toPartialEquiv.image_source_eq_target, hΨt]
          exact (eq_univ_of_forall fun y => show (0 : ℝ) ≤ 1 by norm_num).symm
        · refine ⟨u, R₃, hR₃, fun R hR hRR => ?_, Or.inr hcases⟩
          filter_upwards [hclosed R hR hRR] with j hj ηs eη heη hηs ρ hρ
          exact hj ηs eη heη (closedCore_admissible_rescale_mul (inv_pos.mpr (z (k j)).2.2.1)
            (inv_pos.mpr hR) (inv_pos.mpr (mul_pos hR (z (k j)).2.2.1)) (mul_inv R _) hηs) ρ hρ
      refine key.elim fun u e19 => ?_
      refine e19.elim fun R₄ e20 => ?_
      have hR₄ := e20.1
      have hcore := e20.2.1
      have hcases := e20.2.2
      have hR0 : R₀ ≤ max (max R₀ R₄) (max R₃ T) := (le_max_left _ _).trans (le_max_left _ _)
      have hR4 : R₄ ≤ max (max R₀ R₄) (max R₃ T) := (le_max_right _ _).trans (le_max_left _ _)
      have hR3 : R₃ ≤ max (max R₀ R₄) (max R₃ T) := (le_max_left _ _).trans (le_max_right _ _)
      have hRT : T ≤ max (max R₀ R₄) (max R₃ T) := (le_max_right _ _).trans (le_max_right _ _)
      have hR : 0 < max (max R₀ R₄) (max R₃ T) := hR₀.trans_le hR0
      refine ⟨k, hk, max (max R₀ R₄) (max R₃ T), hRT, ?_⟩
      refine ((hall _ hR hR0).and ((hcore _ hR hR4).and (h3 _ hR3))).mono fun j hj => ?_
      refine ⟨hR, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o, e10.1,
        hCp, hcone, Ns, tNs, cNs, hNs, hhom, u, hj.1.1, hj.2.1, fun ρ' hρ' => ?_, hcases⟩
      have hj3 := hj.2.2
      obtain ⟨Ψ, hΨs, hΨt⟩ := hj3 ρ' hρ'
      refine ⟨Ψ, ?_, hΨt⟩
      rw [hΨs]
      ext x
      change ((z (k j)).1.2)⁻¹ * dist x (z (k j)).1.1 < ρ' * max (max R₀ R₄) (max R₃ T) ↔
        dist x (z (k j)).1.1 < ρ' * (max (max R₀ R₄) (max R₃ T) * (z (k j)).1.2)
      rw [inv_mul_lt_iff₀ (z (k j)).2.2.1]
      have hcomm : (z (k j)).1.2 * (ρ' * max (max R₀ R₄) (max R₃ T)) =
          ρ' * (max (max R₀ R₄) (max R₃ T) * (z (k j)).1.2) := by ring
      rw [hcomm])
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop α₀, hnR.eventually_ge_atTop 3,
    hnR.eventually_ge_atTop (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))⁻¹,
    hnR.eventually_gt_atTop (3200 * V)] with n hnα hn3 hnw hnV
  intro p hp r hr hrv
  obtain ⟨s, hsI, hs, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o,
      ⟨Hc⟩, hCp, hcone, Ns, tNs, cNs, hNs, hhom, u, ⟨φ⟩, hcore, h3, hcases⟩ :=
    hGC n hnα ⟨(p, r), hp, hr, hrv⟩
  have hn0 : (0 : ℝ) < n := by linarith
  have hbuf' := hbuf (W n) (g n) K _ (by omega) (boundaryCounterexampleRatio_pos hδ₀
      (Nat.le_add_left 1 n)).le
    ((boundaryCounterexampleRatio_le δ₀ (n + 1)).trans (hδ₀S.trans (min_le_right _ _))) (B n)
    (hcoll n) (hder n) hA (ĝ n) (heq n) hn3 (boundaryCounterexampleRatio_succ_mul_le_IDX δ₀ n)
    ((inv_le_comm₀ hn0 hw'0).mpr hnw) hw'c p hp hr hrv hs (by linarith [hsI.2])
  obtain ⟨F, hFlip, hFO, hclose, hout, hdiff, hnn, hp0, hgrad, hrng, hsub, hO', L, hL0, hL, hc1,
      hc2, hc3, hc4, hc5⟩ :=
    exists_buffered_radial_cutoff_at_scale (ĝ n) (inducedMetricSpace_hmetric (ĝ n))
      (mul_pos hs hr) φ Hc hbuf' hε hε1 hδr he he1
  have hadm := radial_admissible_of_buffered_clauses (I := I3)
    (m := (inducedMetricSpace (ĝ n)).rescale (s * r)⁻¹ (inv_pos.mpr (mul_pos hs hr))) hε64 hFO
    hclose hdiff
  exact ⟨s, hsI, hs, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o,
    ⟨Hc⟩, hCp, hcone, Ns, tNs, cNs, hNs, hhom, u, hbuf', ⟨φ⟩,
    ⟨F, fun t ht => hcore F e he1 hadm t ht, hFlip, hFO, hclose, hout, hdiff, hnn, hp0, hgrad,
      hrng, hsub, hO', L, hL0, hL, hc1, hc2, hc3, hc4, hc5⟩, h3, hcases⟩


/-- **The regional LPA02 witnesses with the carrier, made total** (lane BFAM-ZD): BDRY-3's helper
`lpa02_total_witnesses_boundary_BDRY3_IDX` on `lpa02_uniform_joint_zero_witnesses_boundary_withCarrier_BFZD`
(`εr ≤ 1/64`): at every eligible centre also the core coordinate `u`, the closed cores of the SAME
radial function and the type of `u`. -/
theorem lpa02_total_witnesses_boundary_withCarrier_BFZD :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {εr δ' e T : ℝ}, 0 < εr → εr ≤ 1 / 64 → 0 < δ' → 0 < e → e < 1 / 40 →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
        (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤)),
        (∀ n, RiemannianMetricComplete (I := 𝓡 3) (ĝ n)) →
        (∀ n (x : (W n).pieceInterior ⊤), ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
          (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        letI := inducedMetricSpace (ĝ n)
        ∀ (ρ : (W n).Carrier → ℝ) (hρ : ∀ p, 0 < ρ p),
        (∀ p, ρ p ≤ 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
        (∃ p₀ : (W n).pieceInterior ⊤, ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) p₀) →
        ∀ p : (W n).pieceInterior ⊤, ∃ s ∈ Icc T V, ∃ hs : 0 < s,
          ∃ (N : Type) (mN : MetricSpace N) (q : N),
            letI := mN
            ProperSpace N ∧ fourPointComparison 0 (univ : Set N) ∧
            (∀ x y : N, ∃ f : Icc (0 : ℝ) 1 → N, Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧
              f ⟨1, by norm_num⟩ = y ∧ ∀ t₁ t₂, dist (f t₁) (f t₂) = dist x y * dist t₁ t₂) ∧
            ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
              ProperSpace C ∧
              (∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R' : ℝ, ∀ hR' : 0 < R', R₀ ≤ R' →
                Nonempty (@KleinerLottApprox N C (mN.rescale R'⁻¹ (inv_pos.mpr hR')) mC q o τ)) ∧
              ∃ (Ns : Type) (_ : TopologicalSpace Ns) (_ : ChartedSpace E3 Ns)
                (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N) (u : Ns → ℝ),
                (ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) p →
                  (∀ y ∈ Metric.ball p (400 * (s * ρ p)),
                    SectionalBoundedBelowAt (ĝ n) y (-((1 / 60) ^ 2 * (s * ρ p)⁻¹ ^ 2))) ∧
                  Nonempty (@KleinerLottApprox ((W n).pieceInterior ⊤) C
                    ((inducedMetricSpace (ĝ n)).rescale (s * ρ p)⁻¹
                      (inv_pos.mpr (mul_pos hs (hρ p)))) mC p o δ) ∧
                  (letI := (inducedMetricSpace (ĝ n)).rescale (s * ρ p)⁻¹
                    (inv_pos.mpr (mul_pos hs (hρ p)))
                  let gR := scaleMetric ((s * ρ p)⁻¹ ^ 2)
                    (pow_pos (inv_pos.mpr (mul_pos hs (hρ p))) 2) (ĝ n)
                  ∃ F : (W n).pieceInterior ⊤ → ℝ,
                    (∀ t ∈ Icc (1 / 5 : ℝ) 2, ∃ T₀ : ℝ, 0 < T₀ ∧
                      ∃ Ψ : PartialDiffeomorph I3 I3 ((W n).pieceInterior ⊤) Ns ∞,
                        {x | F x ≤ t} ⊆ Ψ.source ∧ Ψ '' {x | F x ≤ t} = {y | u y ≤ T₀}) ∧
                    LipschitzWith (Real.toNNReal (1 + εr)) F ∧
                    (∃ O : Set ((W n).pieceInterior ⊤), IsOpen O ∧
                      {x : (W n).pieceInterior ⊤ | 3 / 40 ≤ dist x p ∧ dist x p ≤ 11} ⊆ O ∧
                      ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O) ∧
                    (∀ x, |F x - Metric.infDist x {p}| < e) ∧
                    (∀ x, x ∉ {x : (W n).pieceInterior ⊤ | 1 / 20 < dist x p ∧ dist x p < 20} →
                      F x = Metric.infDist x {p}) ∧
                    (∀ x y, |(F x - Metric.infDist x {p}) - (F y - Metric.infDist y {p})| ≤
                      εr * dist x y) ∧
                    (∀ x, 0 ≤ F x) ∧ F p = 0 ∧
                    (∀ q' ∈ {x : (W n).pieceInterior ⊤ | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10},
                      1 - εr ≤ Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ∧
                        Real.sqrt (gR.inner q' (gradFun gR F q') (gradFun gR F q')) ≤ 1 + εr) ∧
                    (∀ x, F x ∈ Icc (1 / 5 : ℝ) 2 → 1 / 5 - e < dist x p ∧ dist x p < 2 + e) ∧
                    F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆
                      {x : (W n).pieceInterior ⊤ | 1 / 10 ≤ dist x p ∧ dist x p ≤ 10} ∧
                    (∃ O' : Set ((W n).pieceInterior ⊤), IsOpen O' ∧
                      F ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
                      ContMDiffOn I3 𝓘(ℝ, ℝ) ∞ F O' ∧ ∀ q' ∈ O', gradFun gR F q' ≠ 0) ∧
                    ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
                      ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (F x)) ∧
                      (∀ x, annularCutoff cutoffProfile (F x) ∈ Icc (0 : ℝ) 1) ∧
                      (∀ x, F x ∈ Icc (3 / 10 : ℝ) (4 / 5) →
                        annularCutoff cutoffProfile (F x) = 1) ∧
                      tsupport (fun x => annularCutoff cutoffProfile (F x)) ⊆
                        {x : (W n).pieceInterior ⊤ |
                          1 / 5 - e < dist x p ∧ dist x p < 9 / 10 + e} ∧
                      ∀ q', Real.sqrt (gR.inner q'
                        (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')
                        (gradFun gR (fun x => annularCutoff cutoffProfile (F x)) q')) ≤
                          L * (1 + εr)) ∧
                  (∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
                    ∃ Ψ : PartialDiffeomorph I3 I3 ((W n).pieceInterior ⊤) Ns ∞,
                      Ψ.source = Metric.ball p (ρ' * (s * ρ p)) ∧ Ψ.target = univ) ∧
                  ((CompactSpace Ns ∧ (∀ y, u y = 0) ∧
                    ∃ G' : ContMDiffRiemannianMetric I3 ((K - 1 : ℕ) : ℕ∞ω) E3 (TangentSpace I3 : Ns → Type _),
                      ∀ (x : Ns) (u₁ u₂ : TangentSpace I3 x), 0 ≤ G'.sectionalCurvature x u₁ u₂) ∨
                   (∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
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
                          ∀ (x : B) (u₁ u₂ : TangentSpace (𝓡 2) x), 0 ≤ kB.sectionalCurvature x u₁ u₂)) := by
  obtain ⟨δ1, hδ1, hP3b⟩ := lpa02_uniform_joint_zero_witnesses_boundary_withCarrier_BFZD
  refine ⟨δ1, hδ1, ?_⟩
  intro K hK A hA Λ w hΛ hw hwc εr δ' e T hεr hεr1 hδ' he he1 δ₀ hδ₀ hδ₀S W _ g B hcoll hder ĝ
    hcomp heq
  obtain ⟨V, hTV, δ, hδ0, hδδ', hev⟩ := hP3b K hK A hA hΛ hw hwc (ε := εr) (δ' := δ') (e := e)
    (T := T) hεr hεr1 hδ' he he1 hδ₀ hδ₀S W g B hcoll hder ĝ hcomp heq
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [hev] with n hn
  intro ρ hρ hρw ⟨p₀, hp₀⟩ p
  have hT : T ≤ V := hTV
  by_cases hp : ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) p
  · obtain ⟨s, hsI, hs, N, mN, cN, hMN, G, q, hprop, -, -, -, hfour, hseg, C, mC, o, hRCD,
      hCp, hcone, Ns, tNs, cNs, hNs, hhom, u, hbuf, hKL, hrad, hball, hcases⟩ :=
      hn p hp (ρ p) (hρ p) (hρw p)
    exact ⟨s, hsI, hs, N, mN, q, hprop, hfour, hseg, C, mC, o, hRCD, hCp, hcone, Ns, tNs, cNs,
      hNs, hhom, u, fun _ => ⟨hbuf, hKL, hrad, hball, hcases⟩⟩
  · obtain ⟨s, hsI, hs, N, mN, cN, hMN, G, q, hprop, -, -, -, hfour, hseg, C, mC, o, hRCD,
      hCp, hcone, Ns, tNs, cNs, hNs, hhom, u, -⟩ := hn p₀ hp₀ (ρ p₀) (hρ p₀) (hρw p₀)
    exact ⟨s, hsI, hs, N, mN, q, hprop, hfour, hseg, C, mC, o, hRCD, hCp, hcone, Ns, tNs, cNs,
      hNs, hhom, u, fun h => (hp h).elim⟩

end DifferentialGeometry.Geometry.Collapse
