import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryUniformWitnesses
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroRank
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroSelection
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryLocalPacketsOn
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05ModelMetric

/-!
# LC88 / BCP04, packet P3c: the regional zero family on the completion (BDRY-3)

Review 45 §2.2 (T2 zero family) and §4 (zero-ball selection is a real risk): on the completed
interiors `((W n)°, d_ĝ)` of a boundary counterexample sequence, on one tail after `V`, for EVERY
continuous scale `ρ < 2 r_p(w')` on `W_n` with T2's collar smallness, ONE regional zero-model
family `ZeroModelFamilyOn … U₁ U₂` (`U₁ = {D > 10}`): finitely many LC80 zero-model balls centred
in `U₁` (radii `s(p) ρ(p) ∈ [Tρ, Vρ]` from ONE LPA02 witness per point, P3b), pairwise disjoint,
each meeting the zero stratum of `(W°, d_ĝ, ρ ∘ val)`, whose tenth-radius balls cover
`U₁ ∩ Z₀`, with the ORIGINAL radial functions and LC61's ball identifications, and every model
with at most one end.

Proof: the zero stratum of `U₁` stays at `D > 85` (L-Z through the export packet with `P.cusp = B n`
and the rank equality on `U₀`); every candidate centre is in `U₁` (centre margin, BCP04.a,
`13 V < 75 n`); the candidates lie in the compact `d_ĝ`-thickening of `{D ≥ 10}`; the selection
is `exists_selected_zero_family_envelope_BDRY3` with the smooth LPA02 models carrying the
pulled-back limit metric (`homeomorphComapMetric`). No `V·Λ` smallness is used.
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
theorem lpa02_total_witnesses_boundary_BDRY3 :
    ∃ δStar > 0, ∀ (K : ℕ), 10 ≤ K → ∀ (A : ℝ → ℝ),
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ {Λ w : ℝ}, 0 < Λ → 0 < w → w < 4 * Real.pi / 3 →
      ∀ {εr δ' e T : ℝ}, 0 < εr → εr < 1 → 0 < δ' → 0 < e → e < 1 / 40 →
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
  obtain ⟨δ1, hδ1, hP3b⟩ := lpa02_uniform_joint_zero_witnesses_boundary_BDRY2
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

/-- **Zero candidates lie in `U₁` (consumer of L-Z).** On a boundary carrier with BCP04's
standing data, a completion `ĝ ≥ g°` (`= g°` on `{D ≥ 4}`), a scale `ρ ≤ 2 r_p(w')` with the
collar smallness, and the late-index conditions (`13 V < 75 n`, `32 R_β ≤ n`): every point `v`
within `d_ĝ`-distance `V ρ(v)` of a rank-zero point `z` (rank of `(W°, d_ĝ, ρ ∘ val)`) with
`D(z) > 10` has `D(v) > 10`. -/
theorem ofReal_ten_lt_of_near_zero_stratum_BDRY3 :
    ∃ δStar > 0, ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ) {A : ℝ → ℝ},
      2 ≤ K → 0 ≤ δ → δ ≤ δStar → ∀ (B : NearlyCuspidalBoundary W g K δ),
      boundaryVolumeCollapsed W g δ → curvatureDerivativesControlled g K A δ →
      (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) →
      ∀ (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤)),
        (∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
          ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) →
        (∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
          (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v) →
      ∀ {β : ℕ → ℝ}, 0 < β 1 → β 1 < 1 → δ ≤ β 1 ^ 2 / 1000 → δ ≤ 1 / 6408 →
      ∀ {n w' V : ℝ}, 3 ≤ n → δ * (16 * n ^ 4) ≤ 1 → n⁻¹ ≤ w' →
        w' < euclideanThreeUnitBallVolume → 0 ≤ V → 13 * V < 75 * n →
        32 * (1 + |(β 0)⁻¹| + |(β 1)⁻¹| + |(β 2)⁻¹| + |(β 3)⁻¹|) ≤ n →
      ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p), (∀ p, ρ p ≤ 2 * firstVolumeScale g p w') →
        (∀ (i : Fin B.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
          ρ ((B.collar i).toFun q) ≤ β 1 ^ 3 / 2000) →
      letI := inducedMetricSpace ĝ
      ∀ v z : W.pieceInterior ⊤, ENNReal.ofReal 10 < distanceToBoundary W g z →
        z ∈ scaledSplittingStratum.{0, 0} (fun x : W.pieceInterior ⊤ => ρ x) (fun x => hρ x) β 0 →
        dist v z < V * ρ v → ENNReal.ofReal 10 < distanceToBoundary W g v := by
  obtain ⟨δ2, hδ2, hpair⟩ := bsa06_pair_BDRY2.{0}
  refine ⟨δ2, hδ2, ?_⟩
  intro W _ g K δ A hK hδ0 hδS B hcoll hder hA ĝ heq hle β hβ hβ1 hδβ hδ6408 n w' V hn3 hδn16
    hnw hwc hV0 hnV hn32 ρ hρ hρw hsmall
  let instM_BDRY3 : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  -- the rank budget `R_β ≥ (β k)⁻¹`, `k ≤ 3`
  set Rβ : ℝ := 1 + |(β 0)⁻¹| + |(β 1)⁻¹| + |(β 2)⁻¹| + |(β 3)⁻¹| with hRβ
  have hRβ0 : 0 < Rβ := by positivity
  have hβR : ∀ k ≤ 3, (β k)⁻¹ ≤ Rβ := by
    intro k hk
    have h0 := abs_nonneg (β 0)⁻¹
    have h1 := abs_nonneg (β 1)⁻¹
    have h2 := abs_nonneg (β 2)⁻¹
    have h3 := abs_nonneg (β 3)⁻¹
    interval_cases k
    · linarith [le_abs_self (β 0)⁻¹]
    · linarith [le_abs_self (β 1)⁻¹]
    · linarith [le_abs_self (β 2)⁻¹]
    · linarith [le_abs_self (β 3)⁻¹]
  -- the export packet over the given cusp structure
  have hεB0 : 0 < min (1 / 1000 : ℝ) (β 1 ^ 2 / 1000) := lt_min (by norm_num) (by positivity)
  obtain ⟨P, hPc⟩ := exists_boundaryExportPacket_cusp_eq_BDRY3
    (ε := min (1 / 1000) (β 1 ^ 2 / 1000)) B hcoll hder hK hδ6408 hεB0 (min_le_left _ _)
  have hsmall' : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000 := by
    rw [hPc]
    exact hsmall
  -- BCP04.a at every point of `W` for the scale `ρ`
  have hbcp : ∀ p : W.Carrier, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p := fun p hp =>
    (hpair W g K δ hK hδ0 hδS B hcoll hder hA hn3 hδn16 hnw hwc p (hρ p) (hρw p)).2.2.2 hp
  -- the zero stratum of `U₁` is at boundary distance `> 85` (rank equality on `U₀` + L-Z)
  have h510 : ENNReal.ofReal 5 < ENNReal.ofReal 10 :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  have hfar : ∀ z : W.pieceInterior ⊤, ENNReal.ofReal 10 < distanceToBoundary W g z →
      z ∈ scaledSplittingStratum.{0, 0} (fun x : W.pieceInterior ⊤ => ρ x) (fun x => hρ x) β 0 →
      ENNReal.ofReal 85 < distanceToBoundary W g z := by
    intro z hz10 hz0
    have hbud := ofReal_buffer_lt_distanceToBoundary_BDRY1 W g ρ hρ hbcp
      (C := 4 * Rβ / 3) (by positivity) (by linarith) z.val (h510.trans hz10)
    have hq : ENNReal.ofReal (4 * (Rβ * ρ z) + 4) ≤ distanceToBoundary W g z := by
      have he : 3 * (4 * Rβ / 3) * ρ z + 4 = 4 * (Rβ * ρ z) + 4 := by ring
      rw [← he]
      exact hbud.le
    have heqr := scaledSplittingRank_cut_eq_BDRY1 W g ĝ (by norm_num) heq ρ hρ β hRβ0 hβR z hq
    have h0 : @scaledSplittingRank.{0, 0} W.Carrier (inducedMetricSpace g) ρ hρ β z.val = 0 := by
      rw [← heqr]
      exact hz0
    exact ofReal_eightyFive_lt_of_rank_eq_zero_BDRY3 P ρ hρ β hβ hβ1 hδβ (min_le_right _ _)
      hsmall' z.val hz10 h0
  -- the centre margin
  intro v z hz10 hz0 hvz
  obtain ⟨s0, hs0, hs0D⟩ := exists_pos_ofReal_le_distanceToBoundary_BDRY1 W g v
  have hvpos : 0 < distanceToBoundary W g v := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hs0) hs0D
  have hVρ : 0 ≤ V * ρ v := mul_nonneg hV0 (hρ v).le
  refine ofReal_ten_lt_of_near_far_zero_BDRY3 W g ĝ hle v z (hρ v) (V := V) (n := n) hV0 hnV
    (hbcp v hvpos) (hfar z hz10 hz0) ?_
  rw [inducedMetricSpace_hmetric ĝ v z]
  exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt dist_nonneg hvz)).mpr hvz

/-- **The regional zero family on the completion (P3c, frozen in sheet-BDRY-3 §P3c).** After
`0 < β₁ < 1`: constants `δ', Λ'`; then for `εr`, `T ≥ 20 Λ'`, `e`, `Λ, w`, a boundary
counterexample sequence and complete completions `ĝ ≥ g°` with `ĝ = g°` on `{D ≥ 4}`, there are
`V ≥ T`, `0 < δ < δ'` and a tail on which every continuous scale `ρ < 2 r_p(w')` with the collar
smallness `ρ ≤ β₁³/2000` on the collar heights `≤ 96` carries a regional zero-model family on
`((W n)°, d_ĝ, ρ ∘ val)` with centres in `U₁ = {D > 10}`. -/
theorem eventually_zeroModelFamilyOn_boundary_BDRY3 :
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
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
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
  obtain ⟨δ1, hδ1, htot⟩ := lpa02_total_witnesses_boundary_BDRY3
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
  have h1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  have hn0 : (0 : ℝ) < n := by linarith
  have hδn0 : 0 ≤ boundaryCounterexampleRatio δ₀ n :=
    (boundaryCounterexampleRatio_pos hδ₀ h1).le
  have hδn16 := boundaryCounterexampleRatio_mul_le δ₀ h1
  have hδnle : boundaryCounterexampleRatio δ₀ n ≤ 1 / n := by
    have hn4 : (n : ℝ) ≤ 16 * (n : ℝ) ^ 4 := by
      have : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ (by linarith)
      nlinarith
    rw [le_div_iff₀ hn0]
    nlinarith
  have hβ2 : 0 < β 1 ^ 2 := by positivity
  have hpos1000 : 0 < 1000 / β 1 ^ 2 := by positivity
  have hM : 1000 / β 1 ^ 2 ≤ n := by linarith
  have hδ6408 : boundaryCounterexampleRatio δ₀ n ≤ 1 / 6408 :=
    hδnle.trans (one_div_le_one_div_of_le (by norm_num) (by linarith))
  have hδβ : boundaryCounterexampleRatio δ₀ n ≤ β 1 ^ 2 / 1000 := by
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
    hcand0 (W n) (g n) K _ (by omega) hδn0 ((boundaryCounterexampleRatio_le δ₀ n).trans
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
`eventually_zeroModelFamilyOn_boundary_BDRY3` with the late condition `8 V ≤ n`, the regional zero
family has every zero ball `B_ĝ(z, R_z)` equal, under the inclusion `W° → W`, to the `g`-ball
`B_g(z, R_z)` of `W_n` (the radius `R_z ≤ V ρ(z)` is budgeted by BCP04.a). -/
theorem eventually_zeroModelFamilyOn_gBalls_boundary_BDRY3 :
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
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
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
  obtain ⟨δ1, hδ1, hfam⟩ := eventually_zeroModelFamilyOn_boundary_BDRY3
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
  have h1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  have hn0 : (0 : ℝ) < n := by linarith
  have hbcp : ∀ p : (W n).Carrier, 0 < distanceToBoundary (W n) (g n) p →
      n * (distanceToBoundary (W n) (g n) p).toReal /
          ((distanceToBoundary (W n) (g n) p).toReal + 3) <
        (distanceToBoundary (W n) (g n) p).toReal / ρ p := fun p hp =>
    (hpair (W n) (g n) K _ (by omega) (boundaryCounterexampleRatio_pos hδ₀ h1).le
      ((boundaryCounterexampleRatio_le δ₀ n).trans (hδ₀S.trans (min_le_right _ _))) (B n)
      (hcoll n) (hder n) hA hn3 (boundaryCounterexampleRatio_mul_le δ₀ h1)
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
