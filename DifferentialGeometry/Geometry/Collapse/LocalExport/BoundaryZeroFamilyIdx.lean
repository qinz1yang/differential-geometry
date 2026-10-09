import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroFamily
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryModifiedScaleStrictIdx

/-!
# LPA02 witnesses and the regional zero family on the index-shifted sequence (lane BDRY-IDX)

The accepted sequence theorems of packets P3a–P3c
(`lpa02_normalized_sequence_hypotheses_boundary_BDRY2`,
`lpa02_uniform_joint_zero_witnesses_boundary_BDRY2`, `lpa02_total_witnesses_boundary_BDRY3`,
`eventually_zeroModelFamilyOn_boundary_BDRY3`, `eventually_zeroModelFamilyOn_gBalls_boundary_BDRY3`)
take a boundary sequence at `δ_n` for ALL `n`, which is uninhabited at `n = 0` (`δ_0 = 0`, lane
FC39-BQ). This module restates them on sequences at `δ_{n+1}` (BBR03's form), proofs re-run from
the accepted sources: the per-member lemmas (`bsa06_pair_BDRY2`, `completion_original_buffer_BDRY3`,
`ofReal_ten_lt_of_near_zero_stratum_BDRY3`) are applied at the real parameter `n` (resp. `a j`) with
the ratio `δ_{n+1}`, using `δ_{n+1}·16n⁴ ≤ 1` (`boundaryCounterexampleRatio_succ_mul_le_IDX`).
Statements are otherwise verbatim.
-/

set_option autoImplicit false

noncomputable section

universe u

section PairData

open Set Filter Manifold Real Bundle
open scoped ENNReal Manifold Topology ContDiff
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **LPA02, first paragraph, on the completed interiors (consumer).** For a boundary counterexample
sequence, completions `ĝ_n` at cut height `4`, and ANY sequence of eligible pairs `(z_j, r_j)` at
indices `a j → ∞` (`D(z_j) > 5`, `0 < r_j ≤ 2 r_{z_j}(w')` for the ORIGINAL metric), the normalized
sources `((W_{a j})°, r_j⁻² ĝ, z_j)` satisfy LFR14's eventual hypotheses: aligned distances, volume
`≥ v_*` of the unit ball, the derivative profile `2^{K+2} A'(2R+2, w')` on every fixed ball
eventually, and `sec ≥ -(a_j/4)⁻²` on the ball of radius `a_j/8 → ∞`. -/
theorem lpa02_normalized_sequence_hypotheses_boundary_BDRY2_IDX :
    ∃ δStar > 0, ∀ (K : ℕ), 2 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {w' : ℝ}, 0 < w' → w' < euclideanThreeUnitBallVolume →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
        (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤)),
        (∀ n (x : (W n).pieceInterior ⊤), ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
          (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) →
      ∀ (a : ℕ → ℕ), Tendsto a atTop atTop →
      ∀ (z : ∀ j, (W (a j)).pieceInterior ⊤),
        (∀ j, ENNReal.ofReal 5 < distanceToBoundary (W (a j)) (g (a j)) (z j)) →
      ∀ (r : ℕ → ℝ) (hr : ∀ j, 0 < r j),
        (∀ j, r j ≤ 2 * firstVolumeScale (g (a j)) (z j) w') →
      (∀ j a' b', riemannianEDistOf (normalizedCenterMetric (ĝ (a j)) (r j) (hr j)) a' b' =
        ENNReal.ofReal (@dist _ ((inducedMetricSpace (ĝ (a j))).rescale (r j)⁻¹
          (inv_pos.mpr (hr j))).toDist a' b')) ∧
      0 < w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) ∧
      (∀ᶠ j in atTop, ENNReal.ofReal (w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2)) ≤
        riemannianVolumeMeasure (𝓡 3) ((W (a j)).pieceInterior ⊤)
          (normalizedCenterMetric (ĝ (a j)) (r j) (hr j))
          (riemannianBallOf (normalizedCenterMetric (ĝ (a j)) (r j) (hr j)) (z j) 1)) ∧
      (∀ R > 0, ∀ᶠ j in atTop, ∀ k ≤ K,
        ∀ y ∈ riemannianBallOf (normalizedCenterMetric (ĝ (a j)) (r j) (hr j)) (z j) R,
          curvDerivNorm k (normalizedCenterMetric (ĝ (a j)) (r j) (hr j)) y ≤
            (2 : ℝ) ^ (K + 2) * boundaryDerivativeConstant A K (2 * R + 2) w') ∧
      Tendsto (fun j => (((a j : ℝ) / 4) ^ 2)⁻¹) atTop (𝓝 0) ∧
      Tendsto (fun j => (a j : ℝ) / 8) atTop atTop ∧
      (∀ᶠ j in atTop, ∀ y ∈ riemannianBallOf (normalizedCenterMetric (ĝ (a j)) (r j) (hr j))
          (z j) ((a j : ℝ) / 8),
        SectionalBoundedBelowAt (normalizedCenterMetric (ĝ (a j)) (r j) (hr j)) y
          (-(((a j : ℝ) / 4) ^ 2)⁻¹)) := by
  obtain ⟨δS, hδS, hpair⟩ := bsa06_pair_BDRY2.{u}
  refine ⟨δS, hδS, ?_⟩
  intro K hK A hA w' hw' hwc δ₀ hδ₀ hδ₀S W _ g B hcoll hder ĝ heq a ha z hz r hr hrz
  have haR : Tendsto (fun j => (a j : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp ha
  have hev : ∀ᶠ j in atTop, 3 ≤ (a j : ℝ) ∧ ((a j : ℝ))⁻¹ ≤ w' := by
    filter_upwards [haR.eventually_ge_atTop 3, haR.eventually_ge_atTop w'⁻¹] with j h3 hw
    have h0 : 0 < (a j : ℝ) := by linarith
    exact (inv_le_comm₀ h0 hw').mpr hw |> fun h => ⟨h3, h⟩
  have hdat : ∀ j, 3 ≤ (a j : ℝ) → ((a j : ℝ))⁻¹ ≤ w' → _ := fun j h3 hw => by
    exact hpair (W (a j)) (g (a j)) K _ hK (boundaryCounterexampleRatio_pos hδ₀ (Nat.le_add_left 1
        (a j))).le
      ((boundaryCounterexampleRatio_le δ₀ (a j + 1)).trans hδ₀S) (B (a j)) (hcoll (a j)) (hder
          (a j))
      hA h3 (boundaryCounterexampleRatio_succ_mul_le_IDX δ₀ (a j)) hw hwc (z j).val (hr j) (hrz j)
  have hpd : ∀ j, 3 ≤ (a j : ℝ) → ((a j : ℝ))⁻¹ ≤ w' → ∀ {R : ℝ}, 0 ≤ R → 8 * R ≤ (a j : ℝ) →
      _ := fun j h3 hw R hR hRn =>
    completion_pair_data_BDRY2 (W (a j)) (g (a j)) (ĝ (a j)) (heq (a j)) (z j) (hz j) (hr j)
      ((hdat j h3 hw).2.2.2 (lt_of_le_of_lt zero_le (hz j))) hR hRn
  have hv0 : 0 < w' / (24 * ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2) :=
    (volume_lower_at_modified_scale_of_pos (g (a 0)) (z 0).val hw' (hr 0) (hrz 0)).1
  refine ⟨fun j a' b' => ?_, hv0, ?_, fun R hR => ?_, ?_, haR.atTop_div_const (by norm_num), ?_⟩
  · let := inducedMetricSpace (ĝ (a j))
    exact riemannianEDistOf_normalizedCenterMetric (ĝ (a j)) (inducedMetricSpace_hmetric (ĝ (a j)))
      (hr j) a' b'
  · filter_upwards [hev, haR.eventually_ge_atTop 8] with j ⟨h3, hw⟩ h8
    have hvol := (hdat j h3 hw).1
    have heqv := (hpd j h3 hw zero_le_one (by linarith)).2.2.2
    have hid := ballVolume_normalizedCenterMetric_one_BDRY2 finrank_euclideanSpace_fin (g (a j))
      (hr j) (z j).val
    change ENNReal.ofReal _ ≤ ballVolume (normalizedCenterMetric (ĝ (a j)) (r j) (hr j)) (z j) 1
    rw [heqv]
    refine (ENNReal.ofReal_le_ofReal (hid ▸ hvol)).trans ENNReal.ofReal_toReal_le
  · filter_upwards [hev, haR.eventually_gt_atTop (8 * R + 2)] with j ⟨h3, hw⟩ hR8 k hk y hy
    have hder' := (hdat j h3 hw).2.2.1 R hR (by linarith)
    have h := (hpd j h3 hw hR.le (by linarith)).2.2.1 K _ hder' k hk y hy
    rwa [curvatureDerivativeNorm_eq_curvDerivNorm] at h
  · have hsq : Tendsto (fun j => ((a j : ℝ) / 4) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp (haR.atTop_div_const (by norm_num))
    exact tendsto_inv_atTop_zero.comp hsq
  · filter_upwards [hev] with j ⟨h3, hw⟩ y hy
    have hsec := (hdat j h3 hw).2.1
    refine (hpd j h3 hw (by positivity) (by linarith)).2.1 _ (fun y' hy' => hsec y' ?_) y hy
    exact riemannianBallOf_mono _ _ (by linarith) hy'

end DifferentialGeometry.Geometry.Collapse

end PairData

section Witnesses

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

/-- **LPA02 (row) on the completed interiors (P3b, frozen in sheet-BDRY-2 §P3).** The closed
`lpa02_uniform_joint_zero_witnesses` with the sources `((W n)°, d_ĝ, ĝ)` of a boundary
counterexample sequence (completions `ĝ = g°` on `{D ≥ 4}`, complete) and the ELIGIBLE pairs
`D(p) > 5`, `0 < r ≤ 2 r_p^g(w')`: there are `V ≥ T`, `0 < δ < δ'` and a tail on which every
eligible pair has a scale `s ∈ [T, V]` with the closed witness clauses read on
`((W n)°, d_ĝ, ĝ)`. -/
theorem lpa02_uniform_joint_zero_witnesses_boundary_BDRY2_IDX :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {ε δ' e T : ℝ}, 0 < ε → ε < 1 → 0 < δ' → 0 < e → e < 1 / 40 →
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
              (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N),
              (∀ y ∈ Metric.ball p (400 * (s * r)),
                SectionalBoundedBelowAt (ĝ n) y (-((1 / 60) ^ 2 * (s * r)⁻¹ ^ 2))) ∧
              Nonempty (@KleinerLottApprox ((W n).pieceInterior ⊤) C
                ((inducedMetricSpace (ĝ n)).rescale (s * r)⁻¹ (inv_pos.mpr (mul_pos hs hr))) mC
                p o δ) ∧
              (letI := (inducedMetricSpace (ĝ n)).rescale (s * r)⁻¹
                (inv_pos.mpr (mul_pos hs hr))
              let gR := scaleMetric ((s * r)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (mul_pos hs hr)) 2)
                (ĝ n)
              ∃ F : (W n).pieceInterior ⊤ → ℝ, LipschitzWith (Real.toNNReal (1 + ε)) F ∧
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
              ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
                ∃ Ψ : PartialDiffeomorph I3 I3 ((W n).pieceInterior ⊤) Ns ∞,
                  Ψ.source = Metric.ball p (ρ' * (s * r)) ∧ Ψ.target = univ := by
  obtain ⟨δ1, hδ1, hseqH⟩ := lpa02_normalized_sequence_hypotheses_boundary_BDRY2_IDX.{0}
  obtain ⟨δ2, hδ2, hbuf⟩ := completion_original_buffer_BDRY3
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro K hK A hA Λ w hΛ hw hwc ε δ' e T hε hε1 hδ' he he1 δ₀ hδ₀ hδ₀S W _ g B hcoll hder ĝ
    hcomp heq
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
            (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N),
            Nonempty (@KleinerLottApprox ((W n).pieceInterior ⊤) C
              ((instM_BDRY3 n).rescale (s * y.1.2)⁻¹ (inv_pos.mpr (mul_pos hs y.2.2.1))) mC
              y.1.1 o δ) ∧
            ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
              ∃ Ψ : PartialDiffeomorph I3 I3 ((W n).pieceInterior ⊤) Ns ∞,
                Ψ.source = Metric.ball y.1.1 (ρ' * (s * y.1.2)) ∧ Ψ.target = univ) T
    (by
      intro a ha z
      -- LPA02, first paragraph, on the completed interiors (G11)
      obtain ⟨hmetric', hv0, hvol', hcurv', hη, hL, hsec'⟩ :=
        hseqH K (by omega) A hA hw'0 hw'c hδ₀ (hδ₀S.trans (min_le_left _ _)) W g B hcoll hder ĝ
          heq a ha (fun j => (z j).1.1) (fun j => (z j).2.1) (fun j => (z j).1.2)
          (fun j => (z j).2.2.1) (fun j => (z j).2.2.2)
      -- LFR49 (T0′) on the rescaled complete σ-compact sources
      obtain ⟨k, hk, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hGH, _, _, _, -, -, Ns,
          tNs, cNs, hNs, hhom, R₃, h3⟩ :=
        @lfr49_finite_model_ball_type_all_scales K hK 1 _ one_pos hv0
          (fun R => (2 : ℝ) ^ (K + 2) *
            boundaryDerivativeConstant A K (2 * R + 2) (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)))
          (fun j => (W (a j)).pieceInterior ⊤)
          (fun j => (instM_BDRY3 (a j)).rescale ((z j).1.2)⁻¹ (inv_pos.mpr (z j).2.2.1))
          (fun j => inferInstance) (fun j => inferInstance) (fun j => inferInstance)
          (fun j => ((instM_BDRY3 (a j)).rescale_completeSpace_iff _ _).mpr (instC_BDRY3 (a j)))
          (fun j => connectedSpace_pieceInterior_top_BDRY1 (W (a j)))
          (fun j => normalizedCenterMetric (ĝ (a j)) ((z j).1.2) (z j).2.2.1) hmetric'
          (fun j => (z j).1.1) hvol' hcurv' _ _ hη hL hsec'
      -- LFR59: the cone of the SAME model, with its properness
      obtain ⟨C, mC, o, ⟨Hc⟩, hCp, -, -, hcone⟩ :=
        exists_finite_cone_package_of_limit (by omega : 3 ≤ K) G hRiem hsecG q
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
      obtain ⟨Hb, hHb, hsecM⟩ := @exists_curvature_scale_along_of_eventual
        (fun j => (W (a j)).pieceInterior ⊤)
        (fun j => (instM_BDRY3 (a j)).rescale ((z j).1.2)⁻¹ (inv_pos.mpr (z j).2.2.1))
        (fun j => inferInstance) (fun j => inferInstance)
        (fun j => normalizedCenterMetric (ĝ (a j)) ((z j).1.2) (z j).2.2.1) hmetric'
        (fun j => (z j).1.1) _ _ hη hL hsec' k hk
      have hsecS : ∀ j, ∀ y ∈ @Metric.ball ((W (a (k j))).pieceInterior ⊤)
          ((instM_BDRY3 (a (k j))).rescale ((z (k j)).1.2)⁻¹
            (inv_pos.mpr (z (k j)).2.2.1)).toPseudoMetricSpace ((z (k j)).1.1) (Hb j),
          SectionalBoundedBelowAt (scaleMetric (((z (k j)).1.2)⁻¹ ^ 2)
            (pow_pos (inv_pos.mpr (z (k j)).2.2.1) 2) (ĝ (a (k j)))) y (-((Hb j)⁻¹ ^ 2)) := by
        intro j y hy
        rw [← normalizedCenterMetric_eq_scaleMetric]
        exact hsecM j y hy
      -- LC57 (1): Kleiner–Lott maps at every large scale
      obtain ⟨R₀, hR₀, hall⟩ := exists_scale_eventually_normalized_cone_radial_witnesses
        (M := fun j => (W (a (k j))).pieceInterior ⊤) (fun j => ĝ (a (k j)))
        (fun j => inducedMetricSpace_hmetric (ĝ (a (k j))))
        (fun j => (z (k j)).1.2) (fun j => (z (k j)).2.2.1) hGH Hc hcone Hb hHb hsecS
        hδ0 hδ1' hε hε1 he he1
      have hR0 : R₀ ≤ max (max R₀ R₃) T := (le_max_left _ _).trans (le_max_left _ _)
      have hR3 : R₃ ≤ max (max R₀ R₃) T := (le_max_right _ _).trans (le_max_left _ _)
      have hR : 0 < max (max R₀ R₃) T := hR₀.trans_le hR0
      refine ⟨k, hk, max (max R₀ R₃) T, le_max_right _ _, ?_⟩
      filter_upwards [hall _ hR hR0, h3 _ hR3] with j hj1 hj3
      refine ⟨hR, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o, ⟨Hc⟩,
        hCp, hcone, Ns, tNs, cNs, hNs, hhom, hj1.1, fun ρ' hρ' => ?_⟩
      obtain ⟨Ψ, hΨs, hΨt⟩ := hj3 ρ' hρ'
      refine ⟨Ψ, ?_, hΨt⟩
      rw [hΨs]
      ext x
      change ((z (k j)).1.2)⁻¹ * dist x (z (k j)).1.1 < ρ' * max (max R₀ R₃) T ↔
        dist x (z (k j)).1.1 < ρ' * (max (max R₀ R₃) T * (z (k j)).1.2)
      rw [inv_mul_lt_iff₀ (z (k j)).2.2.1]
      have hcomm : (z (k j)).1.2 * (ρ' * max (max R₀ R₃) T) =
          ρ' * (max (max R₀ R₃) T * (z (k j)).1.2) := by ring
      rw [hcomm])
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop α₀, hnR.eventually_ge_atTop 3,
    hnR.eventually_ge_atTop (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))⁻¹,
    hnR.eventually_gt_atTop (3200 * V)] with n hnα hn3 hnw hnV
  intro p hp r hr hrv
  obtain ⟨s, hsI, hs, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o,
      ⟨Hc⟩, hCp, hcone, Ns, tNs, cNs, hNs, hhom, ⟨φ⟩, h3⟩ := hGC n hnα ⟨(p, r), hp, hr, hrv⟩
  have hn0 : (0 : ℝ) < n := by linarith
  have hbuf' := hbuf (W n) (g n) K _ (by omega) (boundaryCounterexampleRatio_pos hδ₀
      (Nat.le_add_left 1 n)).le
    ((boundaryCounterexampleRatio_le δ₀ (n + 1)).trans (hδ₀S.trans (min_le_right _ _))) (B n)
    (hcoll n) (hder n) hA (ĝ n) (heq n) hn3 (boundaryCounterexampleRatio_succ_mul_le_IDX δ₀ n)
    ((inv_le_comm₀ hn0 hw'0).mpr hnw) hw'c p hp hr hrv hs (by linarith [hsI.2])
  exact ⟨s, hsI, hs, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o,
    ⟨Hc⟩, hCp, hcone, Ns, tNs, cNs, hNs, hhom, hbuf', ⟨φ⟩,
    exists_buffered_radial_cutoff_at_scale (ĝ n) (inducedMetricSpace_hmetric (ĝ n))
      (mul_pos hs hr) φ Hc hbuf' hε hε1 hδr he he1, h3⟩

end DifferentialGeometry.Geometry.Collapse

end Witnesses

section ZeroFamily

open Set Filter Bundle Metric Function Manifold
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry GC.Endpoint
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Hyperbolic
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

/-- **One LPA02 witness at EVERY point (helper).** P3b's tail, made total: for every scale
`ρ ≤ 2 r_p(w')` on `W_n` and every centre `p` of `W°` (once some point is eligible), one scale
`s ∈ [T, V]`, one model and cone (the data of an eligible point), and — when `p` itself is eligible
(`D(p) > 5`) — P3b's buffer, Kleiner–Lott map, radial function and ball identifications at the
scale `s ρ(p)`. -/
theorem lpa02_total_witnesses_boundary_BDRY3_IDX :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {εr δ' e T : ℝ}, 0 < εr → εr < 1 → 0 < δ' → 0 < e → e < 1 / 40 →
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
                (_ : IsManifold I3 ∞ Ns) (_ : Ns ≃ₜ N),
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
                  ∃ F : (W n).pieceInterior ⊤ → ℝ, LipschitzWith (Real.toNNReal (1 + εr)) F ∧
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
                  ∀ ρ' ∈ Icc (1 / 5 : ℝ) 2,
                    ∃ Ψ : PartialDiffeomorph I3 I3 ((W n).pieceInterior ⊤) Ns ∞,
                      Ψ.source = Metric.ball p (ρ' * (s * ρ p)) ∧ Ψ.target = univ) := by
  obtain ⟨δ1, hδ1, hP3b⟩ := lpa02_uniform_joint_zero_witnesses_boundary_BDRY2_IDX
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
      hCp, hcone, Ns, tNs, cNs, hNs, hhom, hbuf, hKL, hrad, hball⟩ :=
      hn p hp (ρ p) (hρ p) (hρw p)
    exact ⟨s, hsI, hs, N, mN, q, hprop, hfour, hseg, C, mC, o, hRCD, hCp, hcone, Ns, tNs, cNs,
      hNs, hhom, fun _ => ⟨hbuf, hKL, hrad, hball⟩⟩
  · obtain ⟨s, hsI, hs, N, mN, cN, hMN, G, q, hprop, -, -, -, hfour, hseg, C, mC, o, hRCD,
      hCp, hcone, Ns, tNs, cNs, hNs, hhom, -⟩ := hn p₀ hp₀ (ρ p₀) (hρ p₀) (hρw p₀)
    exact ⟨s, hsI, hs, N, mN, q, hprop, hfour, hseg, C, mC, o, hRCD, hCp, hcone, Ns, tNs, cNs,
      hNs, hhom, fun h => (hp h).elim⟩

/-- **The regional zero family on the completion (P3c, frozen in sheet-BDRY-3 §P3c).** After
`0 < β₁ < 1`: constants `δ', Λ'`; then for `εr`, `T ≥ 20 Λ'`, `e`, `Λ, w`, a boundary
counterexample sequence and complete completions `ĝ ≥ g°` with `ĝ = g°` on `{D ≥ 4}`, there are
`V ≥ T`, `0 < δ < δ'` and a tail on which every continuous scale `ρ < 2 r_p(w')` with the collar
smallness `ρ ≤ β₁³/2000` on the collar heights `≤ 96` carries a regional zero-model family on
`((W n)°, d_ĝ, ρ ∘ val)` with centres in `U₁ = {D > 10}`. -/
theorem eventually_zeroModelFamilyOn_boundary_BDRY3_IDX :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {β : ℕ → ℝ}, 0 < β 1 → β 1 < 1 →
      ∃ δ' Λ' : ℝ, 0 < δ' ∧ 0 < Λ' ∧
      ∀ {εr : ℝ}, 0 < εr → εr < 1 → ∀ {T : ℝ}, 0 < T → 20 * Λ' ≤ T →
      ∀ {e : ℝ}, 0 < e → e < 1 / 40 →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤)),
        (∀ n, RiemannianMetricComplete (I := 𝓡 3) (ĝ n)) →
        (∀ n (x : (W n).pieceInterior ⊤), ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
          (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) →
        (∀ n (x : (W n).pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
          (pieceInteriorMetric (W n) (g n) ⊤).inner x v v ≤ (ĝ n).inner x v v) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        letI := inducedMetricSpace (ĝ n)
        ∀ (ρ : (W n).Carrier → ℝ) (hρ : ∀ p, 0 < ρ p), Continuous ρ →
        (∀ p, ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
        (∀ (i : Fin (B n).count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
          ρ (((B n).collar i).toFun q) ≤ β 1 ^ 3 / 2000) →
        ∃ (N C : (W n).pieceInterior ⊤ → Type) (_ : ∀ a, MetricSpace (N a))
          (_ : ∀ a, ChartedSpace E3 (N a)) (_ : ∀ a, MetricSpace (C a)) (o : ∀ a, C a),
          Nonempty (ZeroModelFamilyOn I3 ((W n).pieceInterior ⊤) (ĝ n) (fun x => ρ x)
            (fun x => hρ x) β N C o δ εr e T V
            {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
            {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x}) := by
  obtain ⟨δ1, hδ1, htot⟩ := lpa02_total_witnesses_boundary_BDRY3_IDX
  obtain ⟨δ2, hδ2, hcand0⟩ := ofReal_ten_lt_of_near_zero_stratum_BDRY3
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro K hK A hA β hβ hβ1
  have instNZ_BDRY3 : NeZero (Module.finrank ℝ E3) :=
    ⟨by rw [finrank_euclideanSpace_fin]; norm_num⟩
  obtain ⟨δs, Λs, hδs, hΛs, hsel⟩ := exists_selected_zero_family_envelope_BDRY3 (E := E3)
    (H := E3) (I := I3) finrank_euclideanSpace_fin hβ hβ1
  refine ⟨δs, Λs, hδs, hΛs, ?_⟩
  intro εr hεr hεr1 T hT hTΛ e he he1 Λ w hΛ hw hwc δ₀ hδ₀ hδ₀S W _ g B hcoll hder ĝ hcomp heq
    hle
  obtain ⟨V, hTV, δ, hδ0, hδδ', hev⟩ := htot K hK A hA hΛ hw hwc (εr := εr) (δ' := δs) (e := e)
    (T := T) hεr hεr1 hδs he he1 hδ₀ (hδ₀S.trans (min_le_left _ _)) W g B hcoll hder ĝ hcomp heq
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  have hw'0 : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := by positivity
  have hw'c : w / (2 * (1 + 2 * Λ⁻¹) ^ 3) < euclideanThreeUnitBallVolume := by
    have h1 : 1 ≤ 1 + 2 * Λ⁻¹ := by have := inv_pos.mpr hΛ; linarith
    have h2 : 1 ≤ 2 * (1 + 2 * Λ⁻¹) ^ 3 := by nlinarith [one_le_pow₀ (n := 3) h1]
    calc w / (2 * (1 + 2 * Λ⁻¹) ^ 3) ≤ w := div_le_self hw.le h2
      _ < euclideanThreeUnitBallVolume := hwc
  set Rβ : ℝ := 1 + |(β 0)⁻¹| + |(β 1)⁻¹| + |(β 2)⁻¹| + |(β 3)⁻¹| with hRβ
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hev, hnR.eventually_ge_atTop 3,
    hnR.eventually_ge_atTop (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))⁻¹,
    hnR.eventually_ge_atTop (6408 + 1000 / β 1 ^ 2), hnR.eventually_gt_atTop (13 * V / 75),
    hnR.eventually_ge_atTop (32 * Rβ)] with n hn hn3 hnw hnM hnV hn32
  let instM_BDRY3 : MetricSpace ((W n).pieceInterior ⊤) := inducedMetricSpace (ĝ n)
  intro ρ hρ hρc hρw hsmall
  -- the boundary ratio on the tail
  have hn0 : (0 : ℝ) < n := by linarith
  have hδn0 : 0 ≤ boundaryCounterexampleRatio δ₀ (n + 1) :=
    (boundaryCounterexampleRatio_pos hδ₀ (Nat.le_add_left 1 n)).le
  have hδn16 := boundaryCounterexampleRatio_succ_mul_le_IDX δ₀ n
  have hδnle : boundaryCounterexampleRatio δ₀ (n + 1) ≤ 1 / n := by
    have hn4 : (n : ℝ) ≤ 16 * (n : ℝ) ^ 4 := by
      have : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by linarith)
      nlinarith
    rw [le_div_iff₀ hn0]
    nlinarith
  have hβ2 : 0 < β 1 ^ 2 := by positivity
  have hpos1000 : 0 < 1000 / β 1 ^ 2 := by positivity
  have hM : 1000 / β 1 ^ 2 ≤ n := by linarith
  have hδ6408 : boundaryCounterexampleRatio δ₀ (n + 1) ≤ 1 / 6408 :=
    hδnle.trans (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hδβ : boundaryCounterexampleRatio δ₀ (n + 1) ≤ β 1 ^ 2 / 1000 := by
    refine hδnle.trans ?_
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    have := (div_le_iff₀ hβ2).mp hM
    linarith
  have hnw' : (n : ℝ)⁻¹ ≤ w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := (inv_le_comm₀ hn0 hw'0).mpr hnw
  set Z : Set ((W n).pieceInterior ⊤) :=
    {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x} ∩
      scaledSplittingStratum.{0, 0} (fun x => ρ x) (fun x => hρ x) β 0 with hZdef
  have h510 : ENNReal.ofReal 5 < ENNReal.ofReal 10 :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have hU1 : ∀ v z, z ∈ Z → dist v z < V * ρ v →
      ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) v := fun v z hz hvz =>
    hcand0 (W n) (g n) K _ (by omega) hδn0 ((boundaryCounterexampleRatio_le δ₀ (n + 1)).trans
      (hδ₀S.trans (min_le_right _ _))) (B n) (hcoll n) (hder n) hA (ĝ n) (heq n) (hle n) hβ hβ1
      hδβ hδ6408 hn3 hδn16 hnw' hw'c (by linarith) (by linarith) hn32 ρ hρ (fun p => (hρw p).le)
      hsmall v z hz.1 hz.2 hvz
  by_cases hE : ∃ p₀ : (W n).pieceInterior ⊤, ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) p₀
  swap
  · -- no eligible point: the empty family
    refine ⟨fun _ => E3, fun _ => E3, fun _ => inferInstance, fun _ => inferInstance,
      fun _ => inferInstance, fun _ => 0, ⟨{
        centres := ∅
        finite_centres := finite_empty
        centres_subset := empty_subset _
        zero := fun i hi => (notMem_empty i hi).elim
        zero_center := fun i hi => (notMem_empty i hi).elim
        radius_mem := fun i hi => (notMem_empty i hi).elim
        disjoint := fun i hi => (notMem_empty i hi).elim
        meets_stratum := fun i hi => (notMem_empty i hi).elim
        covers_stratum := fun x hx => (hE ⟨x, h510.trans hx.1⟩).elim
        one_end := fun i hi => (notMem_empty i hi).elim }⟩⟩
  obtain ⟨p₀, hp₀⟩ := hE
  choose s hsI hs N mN q hprop hfour hseg C mC o hRCD hCp hcone Ns tNs cNs hNs hhom hloc
    using hn ρ hρ (fun p => (hρw p).le) ⟨p₀, hp₀⟩
  -- the models: the smooth `Ns` with the pulled-back limit metric
  let mNs : ∀ p, MetricSpace (Ns p) := fun p => @homeomorphComapMetric _ _ (tNs p) (mN p) (hhom p)
  have hmod := fun p => @homeomorphComapMetric_model_clauses (Ns p) (N p) (C p) (tNs p) (mN p)
    (hprop p) (mC p) (hhom p) (q p) (o p) (hfour p) (hseg p) (hcone p)
  have instNsP_BDRY3 : ∀ p, @ProperSpace (Ns p) (mNs p).toPseudoMetricSpace :=
    fun p => (hmod p).2.1
  have instCP_BDRY3 : ∀ p, @ProperSpace (C p) (mC p).toPseudoMetricSpace := hCp
  -- the radii `s(p) ρ(p)` and their global bounds (`W_n` compact)
  let r : (W n).pieceInterior ⊤ → ℝ := fun p => s p * ρ p
  have hlower : ∀ p : (W n).pieceInterior ⊤, T * ρ p ≤ r p := fun p =>
    mul_le_mul_of_nonneg_right (hsI p).1 (hρ p).le
  have instNE_BDRY3 : Nonempty (W n).Carrier := ⟨p₀.val⟩
  obtain ⟨pmin, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hρc.continuousOn
  obtain ⟨pmax, -, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hρc.continuousOn
  have hrlow : ∀ p, T * ρ pmin ≤ r p := fun p =>
    (mul_le_mul_of_nonneg_left (hmin (mem_univ p.val)) hT.le).trans (hlower p)
  have hrV : ∀ p, r p ≤ V * ρ p := fun p => mul_le_mul_of_nonneg_right (hsI p).2 (hρ p).le
  have hrup : ∀ p, r p ≤ V * ρ pmax := fun p =>
    (hrV p).trans (mul_le_mul_of_nonneg_left (hmax (mem_univ p.val)) (by linarith))
  -- the compact candidate envelope: the `V ρ_max`-thickening of `{D ≥ 10}`
  have instP_BDRY3 : ProperSpace ((W n).pieceInterior ⊤) :=
    inducedMetricSpace_properSpace_of_riemannianMetricComplete (hcomp n)
  have hKc := isCompact_le_distanceToBoundary_BDRY1 (W n) (g n) (by norm_num : (0 : ℝ) < 10)
  have hS : TotallyBounded (cthickening (V * ρ pmax)
      {x : (W n).pieceInterior ⊤ | ENNReal.ofReal 10 ≤ distanceToBoundary (W n) (g n) x}) :=
    hKc.cthickening.totallyBounded
  have hSZ : ∀ v, (ball v (r v) ∩ Z).Nonempty → v ∈ cthickening (V * ρ pmax)
      {x : (W n).pieceInterior ⊤ | ENNReal.ofReal 10 ≤ distanceToBoundary (W n) (g n) x} := by
    rintro v ⟨z, hz1, hz2⟩
    have hz10 : ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) z := hz2.1
    refine mem_cthickening_of_dist_le v z _ _ (show ENNReal.ofReal 10 ≤
      distanceToBoundary (W n) (g n) z from hz10.le) ?_
    have := mem_ball.mp hz1
    rw [dist_comm]
    linarith [hrup v]
  have hcand : ∀ v, (ball v (r v) ∩ Z).Nonempty →
      ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) v := by
    rintro v ⟨z, hz1, hz2⟩
    refine hU1 v z hz2 ?_
    have := mem_ball.mp hz1
    rw [dist_comm]
    linarith [hrV v]
  -- ONE selection on the envelope (LC66 + LC77 on the complete carrier)
  obtain ⟨J, hfin, hdisj, hmeet, himp⟩ := hsel ((W n).pieceInterior ⊤) (ĝ n) (hcomp n) Ns C
    (mN := mNs) (mC := mC) (fun p => (hhom p).symm (q p)) o (fun p => (hRCD p).some)
    (fun _ => δ) r (fun x => ρ x) (fun x => hρ x) hT hTΛ hlower (mul_pos hT (hρ pmin)) hrlow
    hrup Z _ hS (fun x hx => hx.2) hSZ
  have hJU : ∀ i ∈ J, ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) i :=
    fun i hi => hcand i (hmeet i hi)
  have hJ5 : ∀ i ∈ J, ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) i :=
    fun i hi => h510.trans (hJU i hi)
  obtain ⟨hcover, hend⟩ := himp fun i hi => ⟨fun y hy => (hloc i (hJ5 i hi)).1 y (by
    rw [inducedMetricSpace_ball (ĝ n)]; exact hy), (hmod i).2.2.1, (hmod i).2.2.2.1,
    (hmod i).2.2.2.2, hδδ', (hloc i (hJ5 i hi)).2.1⟩
  exact ⟨Ns, C, mNs, cNs, mC, o, ⟨{
    centres := J
    finite_centres := hfin
    centres_subset := fun i hi => hJU i hi
    zero := fun c hc =>
      { center := c
        radius := r c
        radius_pos := mul_pos (hs c) (hρ c)
        model := c
        coneMap := ((hloc c (hJ5 c hc)).2.1).some
        radial := ((hloc c (hJ5 c hc)).2.2.1).choose
        radial_spec := ((hloc c (hJ5 c hc)).2.2.1).choose_spec
        modelChart := fun ρ' h => ((hloc c (hJ5 c hc)).2.2.2 ρ' h).choose
        modelChart_source := fun ρ' h => ((hloc c (hJ5 c hc)).2.2.2 ρ' h).choose_spec.1
        modelChart_target := fun ρ' h => ((hloc c (hJ5 c hc)).2.2.2 ρ' h).choose_spec.2 }
    zero_center := fun _ _ => rfl
    radius_mem := fun c _ => ⟨hlower c, hrV c⟩
    disjoint := fun _ hi _ hj hij => hdisj hi hj hij
    meets_stratum := fun c hc => (hmeet c hc).mono (inter_subset_inter_right _ inter_subset_right)
    covers_stratum := fun _ hx => hcover hx
    one_end := fun c hc => hend c hc }⟩⟩

/-- **Consumer: the zero balls are actual `g`-balls (T2, clause (iv)).** On the tail of
`eventually_zeroModelFamilyOn_boundary_BDRY3_IDX` with the late condition `8 V ≤ n`, the regional
zero
family has every zero ball `B_ĝ(z, R_z)` equal, under the inclusion `W° → W`, to the `g`-ball
`B_g(z, R_z)` of `W_n` (the radius `R_z ≤ V ρ(z)` is budgeted by BCP04.a). -/
theorem eventually_zeroModelFamilyOn_gBalls_boundary_BDRY3_IDX :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {β : ℕ → ℝ}, 0 < β 1 → β 1 < 1 →
      ∃ δ' Λ' : ℝ, 0 < δ' ∧ 0 < Λ' ∧
      ∀ {εr : ℝ}, 0 < εr → εr < 1 → ∀ {T : ℝ}, 0 < T → 20 * Λ' ≤ T →
      ∀ {e : ℝ}, 0 < e → e < 1 / 40 →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ (n + 1))),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ (n + 1))) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ (n + 1))) →
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤)),
        (∀ n, RiemannianMetricComplete (I := 𝓡 3) (ĝ n)) →
        (∀ n (x : (W n).pieceInterior ⊤), ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
          (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) →
        (∀ n (x : (W n).pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
          (pieceInteriorMetric (W n) (g n) ⊤).inner x v v ≤ (ĝ n).inner x v v) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        letI := inducedMetricSpace (ĝ n)
        ∀ (ρ : (W n).Carrier → ℝ) (hρ : ∀ p, 0 < ρ p), Continuous ρ →
        (∀ p, ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
        (∀ (i : Fin (B n).count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
          ρ (((B n).collar i).toFun q) ≤ β 1 ^ 3 / 2000) →
        ∃ (N C : (W n).pieceInterior ⊤ → Type) (_ : ∀ a, MetricSpace (N a))
          (_ : ∀ a, ChartedSpace E3 (N a)) (_ : ∀ a, MetricSpace (C a)) (o : ∀ a, C a),
          ∃ F : ZeroModelFamilyOn I3 ((W n).pieceInterior ⊤) (ĝ n) (fun x => ρ x)
            (fun x => hρ x) β N C o δ εr e T V
            {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
            {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x},
          ∀ z (hz : z ∈ F.centres),
            Subtype.val '' Metric.ball z (F.zero z hz).radius =
              riemannianBallOf (g n) z.val (F.zero z hz).radius := by
  obtain ⟨δ1, hδ1, hfam⟩ := eventually_zeroModelFamilyOn_boundary_BDRY3_IDX
  obtain ⟨δ2, hδ2, hpair⟩ := bsa06_pair_BDRY2.{0}
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro K hK A hA β hβ hβ1
  obtain ⟨δ', Λ', hδ', hΛ', h⟩ := hfam K hK A hA hβ hβ1
  refine ⟨δ', Λ', hδ', hΛ', ?_⟩
  intro εr hεr hεr1 T hT hTΛ e he he1 Λ w hΛ hw hwc δ₀ hδ₀ hδ₀S W _ g B hcoll hder ĝ hcomp heq
    hle
  obtain ⟨V, hTV, δ, hδ0, hδδ', hev⟩ := h hεr hεr1 hT hTΛ he he1 hΛ hw hwc hδ₀
    (hδ₀S.trans (min_le_left _ _)) W g B hcoll hder ĝ hcomp heq hle
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  have hw'0 : 0 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) := by positivity
  have hw'c : w / (2 * (1 + 2 * Λ⁻¹) ^ 3) < euclideanThreeUnitBallVolume := by
    have h1 : 1 ≤ 1 + 2 * Λ⁻¹ := by have := inv_pos.mpr hΛ; linarith
    have h2 : 1 ≤ 2 * (1 + 2 * Λ⁻¹) ^ 3 := by nlinarith [one_le_pow₀ (n := 3) h1]
    calc w / (2 * (1 + 2 * Λ⁻¹) ^ 3) ≤ w := div_le_self hw.le h2
      _ < euclideanThreeUnitBallVolume := hwc
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hev, hnR.eventually_ge_atTop 3,
    hnR.eventually_ge_atTop (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))⁻¹,
    hnR.eventually_ge_atTop (8 * V)] with n hn hn3 hnw hn8
  let instM_BDRY3 : MetricSpace ((W n).pieceInterior ⊤) := inducedMetricSpace (ĝ n)
  intro ρ hρ hρc hρw hsmall
  obtain ⟨N, C, mN, cN, mC, o, ⟨F⟩⟩ := hn ρ hρ hρc hρw hsmall
  refine ⟨N, C, mN, cN, mC, o, F, fun z hz => ?_⟩
  have hn0 : (0 : ℝ) < n := by linarith
  have hbcp : ∀ p : (W n).Carrier, 0 < distanceToBoundary (W n) (g n) p →
      n * (distanceToBoundary (W n) (g n) p).toReal /
          ((distanceToBoundary (W n) (g n) p).toReal + 3) <
        (distanceToBoundary (W n) (g n) p).toReal / ρ p := fun p hp =>
    (hpair (W n) (g n) K _ (by omega) (boundaryCounterexampleRatio_pos hδ₀ (Nat.le_add_left 1 n)).le
      ((boundaryCounterexampleRatio_le δ₀ (n + 1)).trans (hδ₀S.trans (min_le_right _ _))) (B n)
      (hcoll n) (hder n) hA hn3 (boundaryCounterexampleRatio_succ_mul_le_IDX δ₀ n)
      ((inv_le_comm₀ hn0 hw'0).mpr hnw) hw'c p (hρ p) (hρw p).le).2.2.2 hp
  have h510 : ENNReal.ofReal 5 < ENNReal.ofReal 10 :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have hz5 : ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) z :=
    h510.trans (F.centres_subset hz)
  have hV0 : 0 ≤ V := by linarith
  have hbud := ofReal_buffer_lt_distanceToBoundary_BDRY1 (W n) (g n) ρ hρ hbcp (C := V / 3)
    (by positivity) (by linarith) z.val hz5
  have hR := (F.radius_mem z hz).2
  have hR0 := (F.zero z hz).radius_pos
  have hq : ENNReal.ofReal ((F.zero z hz).radius + 4) ≤ distanceToBoundary (W n) (g n) z := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hbud.le
    have he : 3 * (V / 3) * ρ z = V * ρ z := by ring
    linarith
  rw [inducedMetricSpace_ball (ĝ n)]
  exact image_val_riemannianBallOf_cut_BDRY1 (W n) (g n) (ĝ n) (by norm_num) (heq n) z hR0.le hq

end DifferentialGeometry.Geometry.Collapse

end ZeroFamily
