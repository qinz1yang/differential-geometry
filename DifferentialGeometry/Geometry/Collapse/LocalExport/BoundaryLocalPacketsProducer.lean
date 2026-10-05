import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryTransport
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroFamily
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.BoundaryModifiedScaleStrict

/-!
# LC88 / BCP04: T2 — the boundary local packets on the interior completion (lane BDRY-5, G20)

The frozen T2 of `build-logs/scratch/BDRY-1/Targets.lean` v2 (review 45 §2.6, binding dispositions
2026-10-05), proved as written. On one tail of a boundary counterexample sequence:

* the ORIGINAL scale `ρ` on `W_n` — strict BSA05/BSA06 (`bsa06_row_eventually_strict_BDRY4`, G16);
* ONE completion `ĝ` at cut height `a = 4` (T1′ `exists_interior_completion_cut_BDRY1`), chosen for
  all `n` before `V`;
* the packets `F : LocalPacketsOn` on `(W°, d_ĝ, ρ ∘ val)`: the family of the shared regionalised
  kernel bound to `(W°, ĝ)` (`exists_interior_chartFamilyEA_BDRY5`, G18) and the zero family of
  `eventually_zeroModelFamilyOn_gBalls_boundary_BDRY3` (G13), on the SAME data;
* the transport clauses (G19): ranks on `U₀`, consumer domains and zero balls as actual `g`-balls,
  weak-edge distance locality on the active edge domains.

Parameter order (review 45 §2.6): local parameters, `Λ`, `w`, `β`, `T`, `e` → `V` → late `n`
(`n ≥ 32 C_b(V)`); no `V·Λ` smallness, no re-choice of `Λ` or `w` after `V`.

* `interiorChartedT_BDRY1`, `interiorManifoldT_BDRY1`: the frozen helper names of the targets file
  (the interior atlas of `BoundaryInteriorCompletion`, `= interiorCharted_BDRY1`);
* `EdgeFamilyOn.mem_closure_weakEdge_BDRY5`: every edge centre lies in the closure of the weak-edge
  set (the input of the weak-edge locality);
* **T2** `eventually_nonempty_boundaryLocalPackets_BDRY1` (statement verbatim from the targets file;
  the interior-atlas instances are local instances of this module, the statement's own `letI`s and
  `∃ _ : ConnectedSpace` binders take precedence).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Interior

variable (W : CompactCarrier.{u})

/-- The interior atlas (model `𝓡 3`) on `W° = W.pieceInterior ⊤` (as in the delivered G2 module). -/
@[reducible] def interiorChartedT_BDRY1 : ChartedSpace E3 (W.pieceInterior ⊤) :=
  Manifold.interiorChartedSpace W.model ∞

theorem interiorManifoldT_BDRY1 :
    letI := interiorChartedT_BDRY1 W
    IsManifold 𝓘(ℝ, E3) ∞ (W.pieceInterior ⊤) :=
  Manifold.interiorIsManifold W.model ∞

end Interior

section EdgeCentre

variable {X : Type u} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X]

/-- **Edge centres lie in the closure of the weak-edge set** (the field `center_mem` of the edge
chart at `j`, read through `chart_center`). -/
theorem EdgeFamilyOn.mem_closure_weakEdge_BDRY5 {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {β : ℕ → ℝ} {Δ σc μ b s b' s' ε γc βc : ℝ} {U₁ U₂ : Set X}
    (F : EdgeFamilyOn X g hmetric ρ hρ β Δ σc μ b s b' s' ε γc βc U₁ U₂) {j : X}
    (hj : j ∈ F.centres) :
    j ∈ closure
      {y | @isEdgePoint.{u, 0} X (mX.rescale (ρ y)⁻¹ (inv_pos.mpr (hρ y))) y Δ b' s'} := by
  let c := F.chart j hj
  have hcc := F.chart_center j hj
  let hMc : CompleteSpace X := ‹CompleteSpace X›
  let _ := mX.rescale (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ := radialScaledBundle g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric (ρ j)⁻¹ (inv_pos.mpr (hρ j))
  let _ : CompleteSpace X :=
    (mX.rescale_completeSpace_iff (ρ j)⁻¹ (inv_pos.mpr (hρ j))).mpr hMc
  have h1 : c.center = j := hcc
  have h2 := c.center_mem
  rw [h1] at h2
  exact h2

end EdgeCentre

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

/-- **T2 (frozen v2).** Closed prefix verbatim (blueprint order), standing data `K ≥ 10`, `A > 0`,
numerical `δStar`, boundary sequence at `boundaryCounterexampleRatio δ₀ n`. On one tail:
(i) ONE original scale `ρ` on `W_n` (smooth, `Λ`-Lipschitz for `g_n`, LC02 bounds with `g_n`'s first
volume scales, collar smallness `ρ ≤ β₁³/2000` on `z ≤ 96`); (ii) ONE completion `ĝ` (complete,
`= g°` on an open `O ⊇ {D ≥ 4}`, `≥ g°`); (iii) ONE packet assignment `F : LocalPacketsOn` on
`(W°, d_ĝ)` with the scale `ρ ∘ ι`, centres in `U₁ = {D > 10}`, covers of `U₁`/`U₂ = {D ≥ 20}`;
(iv) original-metric transport: ranks agree on `U₀ = {D > 5}`; every per-centre consumer domain
`B(j, Cb ρ(j))`, `Cb = 4(201·10⁴ + 2·10⁶Δ + 400V + β₁⁻¹ + b⁻¹)`, at a centre `j ∈ U₁` is an actual
`g`-ball with the distances of `W`; the zero balls are actual `g`-balls; the weak-edge distance of
`ĝ` equals that of `g` on every active edge domain `B(j, 200Δρ(j))`. -/
theorem eventually_nonempty_boundaryLocalPackets_BDRY1
    {σs : ℝ} (hσs : 0 < σs) (hσs1 : σs ≤ 1 / 100) (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) :
    ∃ δStar : ℝ, 0 < δStar ∧
    ∃ a₂ : ℝ, 0 < a₂ ∧ ∀ γ : ℝ, 0 < γ → γ < 1 / 10 → ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ a₂ ∧
      ∀ βc γc : ℝ, 0 < βc → βc < γc / 1000 → 0 < γc → γc < 1 / 100 →
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∃ Δ₀ : ℝ, 0 < Δ₀ ∧
      ∀ β₂ Δ : ℝ, 0 < β₂ → β₂ ≤ β₀ → β₂ < 1 / 100 → 100 / β₂ < Δ → Δ₀ ≤ Δ →
      ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ bc₀ : ℝ, 0 < bc₀ ∧
      ∀ σc ε μ τ : ℝ, 0 < σc → σc ≤ σ₀ → σc < 1 → 0 < ε → ε < 1 / 100 → 0 < μ → μ ≤ 1 / 1000000 →
        0 < τ → τ ≤ τ₀ → 140 * Real.sqrt τ < ε ^ 2 / 20 →
      ∀ s b' s' : ℝ, 0 < s → s < 1 / 100 → s < b' / 100000 → s < s' / 100000 →
        b' < 1 / (1000000 * Δ) → s' < 1 / (1000000 * Δ) →
        b' < τ * Δ / 1000000000 → s' < τ * Δ / 1000000000 → ∃ a₀ b₁ : ℝ, 0 < a₀ ∧ 0 < b₁ ∧
      ∀ σ : ℝ, 0 < σ → σ ≤ a₂ → σ ≤ threeSplittingExclusionThreshold.{0, 0} → σ ≤ a₀ →
      ∀ Λ : ℝ, 0 < Λ → Δ * Λ * 2000000 ≤ 1 / 100 → Λ < 1 / (1000000 * Δ) →
        100 * Δ * Λ ≤ 1 / 1000000 →
        2 * ε + 300 * Δ * Λ + Real.sqrt (504000 / Δ + 3780 * τ) < γc / 1000 →
        Λ < s' / (100000000 * Δ ^ 2) →
      ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ b : ℝ, 0 < b → b < s / 100000 → b < bc₀ → b < b₁ → 100 * Δ < b⁻¹ → ∃ b₀ : ℝ, 0 < b₀ ∧
      ∀ β : ℕ → ℝ, β 2 = β₂ → 0 < β 1 → β 1 < b₀ → β 1 < 1 →
        β 3 ≤ threeSplittingExclusionThreshold.{0, 0} →
      ∀ ζ : ℝ, β 1 < ζ → ζ < 1 →
      ∃ εr δ' Λ' : ℝ, 0 < εr ∧ εr < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ T : ℝ, 0 < T → 20 * Λ' ≤ T → ∀ e : ℝ, 0 < e → e < 1 / 40 →
      ∀ Lmax : ℝ, 0 < Lmax →
      ∀ δ₀ : ℝ, 0 < δ₀ → δ₀ ≤ δStar →
      ∀ (W : ℕ → CompactCarrier.{0}) [∀ n, ConnectedSpace (W n).Carrier]
        (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
        (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δ₀ n)),
        (∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δ₀ n)) →
        (∀ n, curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δ₀ n)) →
      ∃ V : ℝ, T ≤ V ∧ ∃ δ : ℝ, 0 < δ ∧ δ < δ' ∧ ∀ᶠ n in atTop,
        ∃ ρ : (W n).Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
          ContMDiff (W n).model 𝓘(ℝ, ℝ) ∞ ρ ∧
          (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf (g n) x y) ∧
          (∀ p, firstVolumeScale (g n) p w / 2 < ρ p ∧
            ρ p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
          (∀ (i : Fin (B n).count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
            ρ (((B n).collar i).toFun q) ≤ β 1 ^ 3 / 2000) ∧
          letI := interiorChartedT_BDRY1 (W n)
          haveI := interiorManifoldT_BDRY1 (W n)
          ∃ _ : ConnectedSpace ((W n).pieceInterior ⊤),
          ∃ ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) ((W n).pieceInterior ⊤),
          ∃ O : Set ((W n).pieceInterior ⊤), IsOpen O ∧
            {x : (W n).pieceInterior ⊤ | ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x} ⊆ O ∧
            (∀ x ∈ O, ĝ.inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x) ∧
            (∀ (x : (W n).pieceInterior ⊤) (v : TangentSpace 𝓘(ℝ, E3) x),
              (pieceInteriorMetric (W n) (g n) ⊤).inner x v v ≤ ĝ.inner x v v) ∧
            letI := inducedMetricSpace ĝ
            ∃ _ : CompleteSpace ((W n).pieceInterior ⊤),
            ∃ F : LocalPacketsOn ((W n).pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
                (fun x => ρ x) (fun x => hρpos x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
                T V {x | ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x}
                {x | ENNReal.ofReal 20 ≤ distanceToBoundary (W n) (g n) x},
              -- ranks on U₀ = {D > 5}
              (∀ x : (W n).pieceInterior ⊤,
                ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) x →
                scaledSplittingRank.{0, 0} (fun y : (W n).pieceInterior ⊤ => ρ y)
                    (fun y => hρpos y) β x =
                  @scaledSplittingRank.{0, 0} (W n).Carrier (inducedMetricSpace (g n)) ρ hρpos β
                    x) ∧
              -- every per-centre consumer domain is an actual g-ball with the distances of W
              (∀ j : (W n).pieceInterior ⊤,
                ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) j →
                Subtype.val '' Metric.ball j
                    (4 * (2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j) =
                  riemannianBallOf (g n) j.val
                    (4 * (2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j) ∧
                ∀ y ∈ Metric.ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j),
                  ∀ z ∈ Metric.ball j ((2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹) * ρ j),
                    riemannianEDistOf (g n) y.val z.val = edist y z) ∧
              -- the zero balls are actual g-balls of W
              (letI := F.instMetricN
              letI := F.instChartedN
              letI := F.instMetricC
              ∀ z (hz : z ∈ F.zero.centres),
                Subtype.val '' Metric.ball z (F.zero.zero z hz).radius =
                  riemannianBallOf (g n) z.val (F.zero.zero z hz).radius) ∧
              -- weak-edge distance locality on the active edge domains
              (∀ j ∈ F.edge.centres, ∀ x ∈ Metric.ball j (200 * Δ * ρ j),
                Metric.infDist x (closure {y : (W n).pieceInterior ⊤ |
                    @isEdgePoint.{0, 0} _ ((inducedMetricSpace ĝ).rescale (ρ y)⁻¹
                      (inv_pos.mpr (hρpos y))) y Δ b' s'}) =
                  @Metric.infDist (W n).Carrier (inducedMetricSpace (g n)).toPseudoMetricSpace
                    x.val (@closure (W n).Carrier _ {y : (W n).Carrier |
                      @isEdgePoint.{0, 0} _ ((inducedMetricSpace (g n)).rescale (ρ y)⁻¹
                        (inv_pos.mpr (hρpos y))) y Δ b' s'})) := by
  obtain ⟨δZ, hδZ, hZ⟩ := eventually_zeroModelFamilyOn_gBalls_boundary_BDRY3
  obtain ⟨δR, hδR, hR⟩ := bsa06_row_eventually_strict_BDRY4.{0}
  obtain ⟨a₂, ha₂, hbind⟩ := exists_interior_chartFamilyEA_BDRY5 hσs hσs1 K (by omega) A
  refine ⟨min δZ δR, lt_min hδZ hδR, a₂, ha₂, fun γ hγ hγ1 => ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀a, hbind⟩ := hbind γ hγ hγ1
  refine ⟨β₀, hβ₀, hβ₀a, fun βc γc hβc hβγ hγc hγc1 => ?_⟩
  obtain ⟨σ₀, hσ₀, Δ₀, hΔ₀, hbind⟩ := hbind βc γc hβc hβγ hγc hγc1
  refine ⟨σ₀, hσ₀, Δ₀, hΔ₀, fun β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ => ?_⟩
  have hΔpos : 0 < Δ := lt_trans (div_pos (by norm_num) hβ₂) hΔ
  obtain ⟨τ₀, hτ₀, bc₀, hbc₀, hbind⟩ := hbind β₂ Δ hβ₂ hβ₂β₀ hβ₂small hΔ hΔ₀Δ
  refine ⟨τ₀, hτ₀, bc₀, hbc₀, fun σc ε μ τ hσc hσcσ₀ _ hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e => ?_⟩
  have hb'pos : 0 < b' := by have := hs.trans hsb'; linarith
  obtain ⟨a₀, b₁, ha₀, hb₁, hbind⟩ := hbind σc ε μ τ hσc hσcσ₀ hε hε1 hμ hμ1 hτ hττ₀ hθ s b' s' hs
    hssmall hsb' hss' hb'd hs'd hb'e hs'e
  refine ⟨a₀, b₁, ha₀, hb₁, fun σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend => ?_⟩
  have hΔΛ : 600 * Δ * Λ ≤ 1 := by nlinarith
  obtain ⟨w₀, hw₀, hbind⟩ := hbind σ hσ hσa hση hσa₀ Λ hΛ hΛΔ hΛ44 hlam hbudget hend
  have hvol4 : 0 < euclideanThreeUnitBallVolume / 4 := by
    unfold euclideanThreeUnitBallVolume; positivity
  refine ⟨min w₀ (euclideanThreeUnitBallVolume / 4), lt_min hw₀ hvol4,
    fun w hw hww hwc b hb hbs hbc hbb₁ hsource => ?_⟩
  obtain ⟨b₀, hb₀, hbind⟩ := hbind w hw (hww.trans_le (min_le_left _ _)) b hb hbs hbc hbb₁
    hsource
  refine ⟨b₀, hb₀, fun β hβ2 hβ1 hβ1b hβ11 hβ3 ζ _ _ => ?_⟩
  obtain ⟨δ', Λ', hδ', hΛ', hZ⟩ := hZ K hK A hA hβ1 hβ11
  refine ⟨1 / 8, δ', Λ', by norm_num, by norm_num, hδ', hΛ', fun T hT hTΛ e he he1 Lmax _ δ₀
    hδ₀ hδ₀S W _ g B hcoll hder => ?_⟩
  obtain ⟨L₀, hL₀, hbind⟩ := hbind β hβ2 hβ1 hβ1b hβ3 Lmax
  -- ONE completion at cut height `4` for every `n`, before `V`
  have hT1 := fun n => exists_interior_completion_cut_BDRY1 (W n) (g n) (a := 4) (by norm_num)
  choose ĝ O hcomp hO hKO heqO hle using hT1
  have heq4 : ∀ n (x : (W n).pieceInterior ⊤),
      ENNReal.ofReal 4 ≤ distanceToBoundary (W n) (g n) x →
        (ĝ n).inner x = (pieceInteriorMetric (W n) (g n) ⊤).inner x :=
    fun n x hx => heqO n x (hKO n hx)
  -- the ORIGINAL scale (strict BSA05 / BSA06)
  obtain ⟨ρ, hρev, hρcol⟩ := hR hδ₀ (hδ₀S.trans (min_le_right _ _)) K (by omega) A hA W g B
    hcoll hder hΛ hw (hww.trans_le (min_le_right _ _))
  -- the zero family on the completion
  obtain ⟨V, hTV, δ, hδ, hδδ', hzero⟩ := hZ (εr := 1 / 8) (by norm_num) (by norm_num) hT hTΛ he
    he1 hΛ hw hwc hδ₀ (hδ₀S.trans (min_le_left _ _)) W g B hcoll hder ĝ hcomp heq4 hle
  refine ⟨V, hTV, δ, hδ, hδδ', ?_⟩
  have hV0 : 0 ≤ V := (hT.le.trans hTV)
  have hβi1 : 0 < (β 1)⁻¹ := inv_pos.mpr hβ1
  have hbi : 0 < b⁻¹ := inv_pos.mpr hb
  have hb'i : 0 < b'⁻¹ := inv_pos.mpr hb'pos
  set Lbig : ℝ := max L₀ Lmax with hLbig
  set Cb : ℝ := 2010000 + 2000000 * Δ + 400 * V + (β 1)⁻¹ + b⁻¹ with hCb
  set Rβ : ℝ := 1 + |(β 0)⁻¹| + |(β 1)⁻¹| + |(β 2)⁻¹| + |(β 3)⁻¹| with hRβ
  have hCb0 : 0 ≤ Cb := by rw [hCb]; positivity
  have hnR : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hρev, hρcol (β 1 ^ 3 / 2000) (by positivity), hzero,
    hnR.eventually_ge_atTop (8 * Lbig), hnR.eventually_ge_atTop (13 * Δ / 10),
    hnR.eventually_ge_atTop 16, hnR.eventually_ge_atTop (32 * Cb),
    hnR.eventually_ge_atTop (32 * Rβ), hnR.eventually_ge_atTop (32 * (600 * Δ + 2 * b'⁻¹))]
    with n hρn hcn hzn h8 h13 h16 hnC hnRβ hnE
  obtain ⟨hρpos, hsm, hlc, hlip, hdata⟩ := hρn
  have hcn' : ∀ (i : Fin (B n).count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ n (((B n).collar i).toFun q) ≤ β 1 ^ 3 / 2000 := fun i q hq => (hcn i q hq).le
  have h2Λ : (2 : ℝ) / Λ = 2 * Λ⁻¹ := div_eq_mul_inv 2 Λ
  have hlc' : ∀ p, firstVolumeScale (g n) p w / 2 < ρ n p ∧
      ρ n p < 2 * firstVolumeScale (g n) p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3)) := by
    intro p
    have h := hlc p
    rw [h2Λ] at h
    exact h
  have hbcp : ∀ p, 0 < distanceToBoundary (W n) (g n) p →
      (n : ℝ) * (distanceToBoundary (W n) (g n) p).toReal /
          ((distanceToBoundary (W n) (g n) p).toReal + 3) <
        (distanceToBoundary (W n) (g n) p).toReal / ρ n p := fun p => (hdata p).2.2.2.1
  have hpos5 : ∀ x : (W n).pieceInterior ⊤,
      ENNReal.ofReal 10 < distanceToBoundary (W n) (g n) x →
        ENNReal.ofReal 5 < distanceToBoundary (W n) (g n) x := fun x hx =>
    lt_trans ((ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 10)).mpr
      (by norm_num : (5 : ℝ) < 10)) hx
  -- the family of the regionalised kernel on `(W°, ĝ)`
  obtain ⟨hcN, L, ⟨hAd⟩⟩ := hbind Lbig (le_max_left _ _) (le_max_right _ _) (W n) (g n) (ĝ n)
    (hcomp n) (heq4 n) (hle n) (ρ n) hρpos hsm hlip (fun p => (hlc p).1) (n : ℝ)
    (by linarith only [h8]) (by linarith only [h13]) h16
    (fun p => ⟨(hdata p).1, (hdata p).2.1, (hdata p).2.2.1, (hdata p).2.2.2.1⟩)
  -- the zero family for THIS scale
  obtain ⟨N, C, mN, cN, mC, o, Fz, hFz⟩ := hzn (ρ n) hρpos hsm.continuous (fun p => (hlc' p).2)
    hcn'
  let instM_BDRY5 : MetricSpace ((W n).pieceInterior ⊤) := inducedMetricSpace (ĝ n)
  refine ⟨ρ n, hρpos, hsm, hlip, hlc', hcn', connectedSpace_pieceInterior_top_BDRY1 (W n), ĝ n, O n,
    hO n, hKO n, heqO n, hle n, hcN,
    { toChartFamilyEOn := L
      circleAdapted := hAd
      N := N
      C := C
      instMetricN := mN
      instChartedN := cN
      instMetricC := mC
      o := o
      zero := Fz }, ?_, ?_, hFz, ?_⟩
  · exact scaledSplittingRank_completion_eq_BDRY5 (W n) (g n) (ĝ n) (heq4 n) (ρ n) hρpos β hbcp
      hnRβ
  · intro j hj
    exact consumer_domain_completion_BDRY5 (W n) (g n) (ĝ n) (heq4 n) (ρ n) hρpos hCb0 hbcp hnC j
      (hpos5 j hj)
  · intro j hj x hx
    have hm := L.edge.mem_closure_weakEdge_BDRY5 hj
    exact infDist_weakEdge_completion_eq_BDRY5 (W n) (g n) (ĝ n) (heq4 n) (hle n) (ρ n) hρpos
      hΔpos hb'pos hΛ.le hΔΛ hlip hbcp hnE j (hpos5 j (L.edge.centres_subset hj)) hm x hx

end DifferentialGeometry.Geometry.Collapse
