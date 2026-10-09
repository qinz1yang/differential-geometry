import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPairData
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA02UniformWitnesses

/-!
# LC88 / BCP04, packet P3b: LPA02's uniform joint zero witnesses on the completion (BDRY-3, G12)

Review 45 §4.2 (LPA02 row, "keep the SAME joint witness"): the closed row
`lpa02_uniform_joint_zero_witnesses` read on the completed interiors `((W n)°, d_ĝ, ĝ)` (cut height
`4`) of a boundary counterexample sequence, at ELIGIBLE pairs only: centres `p` with `D(p) > 5`
and radii `0 < r ≤ 2 r_p^g(w')` of the ORIGINAL first volume scale (`w' = w / (2(1 + 2Λ⁻¹)³)`).
For fixed `ε, δ', e, T` there are `V ≥ T`, one cone error `δ < δ'` and a tail on which every
eligible pair has a scale `s ∈ [T, V]` with ONE model, cone and smooth `Ns`, the original buffer
`sec_ĝ ≥ -(1/60)²(sr)⁻²` on `B(p, 400 s r)`, a Kleiner–Lott `δ`-map at the scale `s r`, LC67's
radial function with LC31's cutoff, and `B(p, ρ' s r) ≃ Ns` for `ρ' ∈ [1/5, 2]`.

Proof: the LC58 kernel on the eligible pairs; its sequential hypothesis is the closed proof with
the boundary first paragraph `lpa02_normalized_sequence_hypotheses_boundary_BDRY2` (G11) and the
complete σ-compact LFR49 core on `X j := (W (a j))°`; the buffer comes from BSA06 at the pair
(`bsa06_pair_BDRY2`) through `completion_pair_data_BDRY2` once `n > 3200 V` (late `n` after `V`).
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

/-- **The original buffer at an eligible pair of the completion.** On the tail `3 ≤ n`,
`n⁻¹ ≤ w'`, at `p` with `D(p) > 5` and `0 < r ≤ 2 r_p(w')`, every scale `0 < s` with `3200 s < n`
has `sec_ĝ ≥ -(1/60)²(sr)⁻²` on the `d_ĝ`-ball `B(p, 400 s r)`. -/
theorem completion_original_buffer_BDRY3 :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ),
      2 ≤ K → 0 ≤ δ → δ ≤ δStar → NearlyCuspidalBoundary W g K δ →
      boundaryVolumeCollapsed W g δ → ∀ {A : ℝ → ℝ}, curvatureDerivativesControlled g K A δ →
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤)),
        (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
          ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) →
      ∀ {n w' : ℝ}, 3 ≤ n → δ * (16 * n ^ 4) ≤ 1 → n⁻¹ ≤ w' →
        w' < euclideanThreeUnitBallVolume →
      ∀ (p : W.pieceInterior ⊤), ENNReal.ofReal 5 < distanceToBoundary W g p →
      ∀ {r : ℝ}, 0 < r → r ≤ 2 * firstVolumeScale g p w' →
      ∀ {s : ℝ}, 0 < s → 3200 * s < n →
        ∀ y ∈ @Metric.ball _ (inducedMetricSpace ĝ).toPseudoMetricSpace p (400 * (s * r)),
          SectionalBoundedBelowAt ĝ y (-((1 / 60) ^ 2 * (s * r)⁻¹ ^ 2)) := by
  obtain ⟨δS, hδS, hpair⟩ := bsa06_pair_BDRY2.{0}
  refine ⟨δS, hδS, ?_⟩
  intro W _ g K δ hK hδ0 hδ B hcoll A hder hA ĝ heq n w' hn hδn hwn hwc p hp r hr hrp s hs hsn
    y hy
  have hnpos : 0 < n := by linarith
  have hdat := hpair W g K δ hK hδ0 hδ B hcoll hder hA hn hδn hwn hwc p.val hr hrp
  have hpd := completion_pair_data_BDRY2 W g ĝ heq p hp hr
    (hdat.2.2.2 (lt_of_le_of_lt zero_le hp)) (R := n / 8) (by positivity) (by linarith)
  have hsec := hpd.2.1 (-((n / 4) ^ 2)⁻¹) (fun y' hy' => hdat.2.1 y'
    (riemannianBallOf_mono _ _ (by linarith) hy'))
  let := inducedMetricSpace ĝ
  have hy' : y ∈ riemannianBallOf (normalizedCenterMetric ĝ r hr) p (n / 8) := by
    change riemannianEDistOf (normalizedCenterMetric ĝ r hr) p y < ENNReal.ofReal (n / 8)
    rw [riemannianEDistOf_normalizedCenterMetric ĝ (inducedMetricSpace_hmetric ĝ) hr,
      MetricSpace.rescale_dist]
    have hd : dist p y < 400 * (s * r) := by rw [dist_comm]; exact Metric.mem_ball.mp hy
    have hlt : r⁻¹ * dist p y < n / 8 := by
      rw [inv_mul_lt_iff₀ hr]
      nlinarith
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr hlt
  have h := hsec y hy'
  rw [normalizedCenterMetric_eq_scaleMetric, sectionalBoundedBelowAt_scaleMetric_iff] at h
  refine h.mono ?_
  have h60 : 60 * s ≤ n / 4 := by linarith
  have hsq : ((n / 4) ^ 2)⁻¹ ≤ ((60 * s) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) h60 2)
  have hid : (1 / 60) ^ 2 * (s * r)⁻¹ ^ 2 = ((60 * s) ^ 2)⁻¹ * r⁻¹ ^ 2 := by
    ring
  rw [hid, neg_mul, neg_le_neg_iff]
  exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)

/-- **LPA02 (row) on the completed interiors (P3b, frozen in sheet-BDRY-2 §P3).** The closed
`lpa02_uniform_joint_zero_witnesses` with the sources `((W n)°, d_ĝ, ĝ)` of a boundary
counterexample sequence (completions `ĝ = g°` on `{D ≥ 4}`, complete) and the ELIGIBLE pairs
`D(p) > 5`, `0 < r ≤ 2 r_p^g(w')`: there are `V ≥ T`, `0 < δ < δ'` and a tail on which every
eligible pair has a scale `s ∈ [T, V]` with the closed witness clauses read on
`((W n)°, d_ĝ, ĝ)`. -/
theorem lpa02_uniform_joint_zero_witnesses_boundary_BDRY2 :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {ε δ' e T : ℝ}, 0 < ε → ε < 1 → 0 < δ' → 0 < e → e < 1 / 40 →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
        (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
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
  obtain ⟨δ1, hδ1, hseqH⟩ := lpa02_normalized_sequence_hypotheses_boundary_BDRY2.{0}
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
  have h1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  have hn0 : (0 : ℝ) < n := by linarith
  have hbuf' := hbuf (W n) (g n) K _ (by omega) (boundaryCounterexampleRatio_pos hδ₀ h1).le
    ((boundaryCounterexampleRatio_le δ₀ n).trans (hδ₀S.trans (min_le_right _ _))) (B n)
    (hcoll n) (hder n) hA (ĝ n) (heq n) hn3 (boundaryCounterexampleRatio_mul_le δ₀ h1)
    ((inv_le_comm₀ hn0 hw'0).mpr hnw) hw'c p hp hr hrv hs (by linarith [hsI.2])
  exact ⟨s, hsI, hs, N, mN, cN, hMN, G, q, hprop, hconn, hRiem, hsecG, hfour, hseg, C, mC, o,
    ⟨Hc⟩, hCp, hcone, Ns, tNs, cNs, hNs, hhom, hbuf', ⟨φ⟩,
    exists_buffered_radial_cutoff_at_scale (ĝ n) (inducedMetricSpace_hmetric (ĝ n))
      (mul_pos hs hr) φ Hc hbuf' hε hε1 hδr he he1, h3⟩

/-- **Consumer: the witnesses at an original scale function.** On the tail of P3b, for EVERY scale
`ρ` on `W_n` below `2 r_p(w')` (the LC02 upper bound of T2's scale), every centre `p ∈ U₀ = {D > 5}`
has a scale `s ∈ [T, V]` with the original buffer on `B_ĝ(p, 400 s ρ(p))` and a Kleiner–Lott
`δ`-map of `((W n)°, (s ρ(p))⁻¹ d_ĝ, p)` to a radial cone. -/
theorem lpa02_witnesses_at_scale_boundary_BDRY3 :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {δ' T : ℝ}, 0 < δ' →
      ∀ {δ₀ : ℝ}, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier),
        (∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
      ∀ (ĝ : ∀ n, SmoothRiemannianMetric (𝓡 3) ((W n).pieceInterior ⊤)),
        (∀ n, RiemannianMetricComplete (I := 𝓡 3) (ĝ n)) →
        (∀ n (x : (W n).pieceInterior ⊤), ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
          (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        letI := inducedMetricSpace (ĝ n)
        ∀ (ρ : (W n).Carrier → ℝ) (hρ : ∀ p, 0 < ρ p),
        (∀ p, ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) →
        ∀ (p : (W n).pieceInterior ⊤), ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) p →
        ∃ s ∈ Icc T V, ∃ hs : 0 < s,
          (∀ y ∈ Metric.ball p (400 * (s * ρ p)),
            SectionalBoundedBelowAt (ĝ n) y (-((1 / 60) ^ 2 * (s * ρ p)⁻¹ ^ 2))) ∧
          ∃ (C : Type) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
            Nonempty (@KleinerLottApprox ((W n).pieceInterior ⊤) C
              ((inducedMetricSpace (ĝ n)).rescale (s * ρ p)⁻¹ (inv_pos.mpr (mul_pos hs (hρ p))))
              mC p o δ) := by
  obtain ⟨δS, hδS, hmain⟩ := lpa02_uniform_joint_zero_witnesses_boundary_BDRY2
  refine ⟨δS, hδS, ?_⟩
  intro K hK A hA Λ w hΛ hw hwc δ' T hδ' δ₀ hδ₀ hδ₀S W _ g B hcoll hder ĝ hcomp heq
  obtain ⟨V, hTV, δ, hδ0, hδδ', hev⟩ := hmain K hK A hA hΛ hw hwc (ε := 1 / 2) (e := 1 / 80)
    (T := T) (by norm_num) (by norm_num) hδ' (by norm_num) (by norm_num) hδ₀ hδ₀S W g B hcoll
    hder ĝ hcomp heq
  refine ⟨V, hTV, δ, hδ0, hδδ', ?_⟩
  filter_upwards [hev] with n hn ρ hρ hρw p hp
  obtain ⟨s, hsI, hs, N, mN, cN, hMN, G, q, -, -, -, -, -, -, C, mC, o, hC, -, -, Ns, tNs, cNs,
    hNs, hhom, hbuf, hφ, -⟩ := hn p hp (ρ p) (hρ p) (hρw p).le
  exact ⟨s, hsI, hs, hbuf, C, mC, o, hC, hφ⟩

end DifferentialGeometry.Geometry.Collapse
