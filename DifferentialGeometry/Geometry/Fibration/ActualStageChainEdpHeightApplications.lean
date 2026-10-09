import DifferentialGeometry.Geometry.Fibration.ActualStageChainEdpHeight
import DifferentialGeometry.Geometry.Fibration.ActualEdgeBuffer
import DifferentialGeometry.Geometry.Fibration.ActualEdgeCollarCircleApplications
import DifferentialGeometry.Geometry.Collapse.LocalExport.LocalChartPacketsC14ZeroTypes


/-!
# EDP04–EDP06's final-map clauses: the compact time trace, EDP06's rim step, the final family

Lane C14-EDP-E. Blueprint `master207B.tex`, EDP04 (B:6974–6986: "the ENTIRE time-dependent inverse
image lies in the interior of the SAME compact `Q_i` from EDP03. It is closed in `Q_i × [0,1]`, and
hence compact") and EDP06 (B:7103–7108: a point of (EV) is in EDP06's band, two-stratum and in a
circle chart), for a chain `C : Gaf02Chain L.toLocalChartPackets …` on `L : LocalChartPacketsC14`.

* `edp04_trace_compact_C14_EDPE`: with EDP03's own `Q_j` (`edp03_buffer`), for every `|a| < 4Δ`
  the whole trace of `X_a` in `Y_j × [0, 1]` lies in `int Q_j × [0, 1]` and is compact.
* `edge_vertical_rank_C14Z_EDPE`: `D(g, T)` onto along the rim inside `Y_j`, on the final closed
  family `LocalChartPacketsC14Z` (projection).
* `eventually_edp06_final_rim_circle_EDPE` (consumer of `Gaf02Chain.edge_trace_EDPE` and of
  C14-EDP6's binding `eventually_edp06_collar_circle_EDP6`, reused): on LC20's tail every point of
  the actual rim `T = 4Δ` in `Y_j` with `|g_j| < 4Δ` is two-stratum and lies in a circle chart.

The witnessing index and `x ∈ Y_j` are inputs here; that every point of `∂X₂` has one is EDP02's
(ELoc) (needs GAF05/GAF06, sheet `state-C14-EDP-E.md`). FC34's transport, `f₂⁻¹(w) ∩ X₂`, X₁/B₁
(GAF07) are not here.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Family

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

/-- The model metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricN_EDPEb
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalChartPackets`, as a named local instance. -/
local instance instChartedN_EDPEb
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalChartPackets`, as a named local instance. -/
local instance instMetricC_EDPEb
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)
    (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **EDP04's whole time trace is compact, inside the SAME compact buffer `Q_j`** (B:6974–6986):
with EDP03's `Q_j` (`edp03_buffer`), for every `|a| < 4Δ` every trace point
`p ∈ Y_j`, `τ ∈ [0, 1]`, `(1 − τ)η + τg = a`, `(1 − τ)H₀ + τT ≤ 4Δ` lies in `int Q_j`, and the
trace `{(p, τ) : p ∈ Y_j, τ ∈ [0, 1], …}` is compact (closed in `Q_j × [0, 1]`). -/
theorem edp04_trace_compact_C14_EDPE
    {L : LocalChartPacketsC14 X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz}
    (C : Gaf02Chain L.toLocalChartPackets Kj Ξ Γ S eg c cw) (hcw : 0 ≤ cw 0)
    (hSΞ : S 0 ≤ Ξ 0 / 10000) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8)
    (hσc : σc ≤ 1 / 1000) (hb : b * (1000 * Δ) ≤ 1) {j : X} (hj : j ∈ L.edge.centres) :
    let jF : L.edge.finite_centres.toFinset := ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩
    let η := L.edge.coord j
    let t : X → ℝ := fun z => L.edge.smoothing z / ρ z
    let H₀ := edgeRowHeight Δ L.edge.smoothing ρ
    let A : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector L.toLocalChartFamily L.zero (C.E z))
    let Tq : X → ℝ := fun z => A z / C.scale z
    let gq : X → ℝ := fun z => EuclideanSpace.proj (0 : Fin 2)
      (gafEdgeVector L.toLocalChartFamily L.zero jF (C.E z)) / ρ j
    let Y : Set X := {p | p ∈ ball j (100 * Δ * ρ j) ∧ |η p| < 5 * Δ ∧ t p < 5 * Δ}
    ∃ Q : Set X, IsCompact Q ∧ Q ⊆ Y ∧ ∀ a : ℝ, |a| < 4 * Δ →
      (∀ θ ∈ Icc (0 : ℝ) 1, ∀ p ∈ Y, (1 - θ) * η p + θ * gq p = a →
        (1 - θ) * H₀ p + θ * Tq p ≤ 4 * Δ → p ∈ interior Q) ∧
      IsCompact {q : X × ℝ | q.1 ∈ Y ∧ q.2 ∈ Icc (0 : ℝ) 1 ∧
        (1 - q.2) * η q.1 + q.2 * gq q.1 = a ∧ (1 - q.2) * H₀ q.1 + q.2 * Tq q.1 ≤ 4 * Δ} := by
  intro jF η t H₀ A Tq gq Y
  obtain ⟨hΛ, hΔ, -, -, hLΛ, -⟩ := C.std
  have hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Δ) hΛ]
  obtain ⟨-, hηs, hHs, -, Q, hQc, hQY, hQi⟩ :=
    edp03_buffer L.toLocalChartFamilyE hΔ hμ hτ hlam hσc hb hj
  have htr := C.edge_trace_EDPE hcw hSΞ hc hϑ hε0 hε hj
  obtain ⟨-, -, hT, hg⟩ := (C.final_smooth_EDPE).2
  have hint : ∀ a : ℝ, |a| < 4 * Δ → ∀ θ ∈ Icc (0 : ℝ) 1, ∀ p ∈ Y,
      (1 - θ) * η p + θ * gq p = a → (1 - θ) * H₀ p + θ * Tq p ≤ 4 * Δ → p ∈ interior Q := by
    intro a ha θ hθ p hp hfib hH
    obtain ⟨h1, h2, -⟩ := htr θ hθ p hp.1 hp.2.1 hp.2.2 a ha hfib hH
    exact hQi ⟨hp.1, by linarith, by linarith⟩
  refine ⟨Q, hQc, hQY, fun a ha => ⟨hint a ha, ?_⟩⟩
  have hQI : IsCompact (Q ×ˢ Icc (0 : ℝ) 1) := hQc.prod isCompact_Icc
  have hfst : ∀ (f : X → ℝ), ContinuousOn f Y →
      ContinuousOn (fun q : X × ℝ => f q.1) (Q ×ˢ Icc (0 : ℝ) 1) := fun f hf =>
    (hf.mono hQY).comp continuous_fst.continuousOn (fun q hq => hq.1)
  have hF : ContinuousOn (fun q : X × ℝ => (1 - q.2) * η q.1 + q.2 * gq q.1)
      (Q ×ˢ Icc (0 : ℝ) 1) :=
    ((continuous_const.sub continuous_snd).continuousOn.mul (hfst η hηs.continuousOn)).add
      (continuous_snd.continuousOn.mul (hfst gq (hg jF).continuous.continuousOn))
  have hG : ContinuousOn (fun q : X × ℝ => (1 - q.2) * H₀ q.1 + q.2 * Tq q.1)
      (Q ×ˢ Icc (0 : ℝ) 1) :=
    ((continuous_const.sub continuous_snd).continuousOn.mul (hfst H₀ hHs.continuousOn)).add
      (continuous_snd.continuousOn.mul (hfst Tq hT.continuous.continuousOn))
  have hcl1 := hF.preimage_isClosed_of_isClosed (hQc.isClosed.prod isClosed_Icc)
    (isClosed_singleton (x := a))
  have hcl2 := (hG.mono inter_subset_left).preimage_isClosed_of_isClosed hcl1
    (isClosed_Iic (a := 4 * Δ))
  refine hQI.of_isClosed_subset ?_ (fun q hq =>
    ⟨interior_subset (hint a ha q.2 hq.2.1 q.1 hq.1 hq.2.2.1 hq.2.2.2), hq.2.1⟩)
  convert hcl2 using 1
  ext q
  simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_singleton_iff, mem_Iic, mem_prod]
  constructor
  · rintro ⟨hqY, hqI, hfib, hH⟩
    exact ⟨⟨⟨interior_subset (hint a ha q.2 hqI q.1 hqY hfib hH), hqI⟩, hfib⟩, hH⟩
  · rintro ⟨⟨⟨hqQ, hqI⟩, hfib⟩, hH⟩
    exact ⟨hQY hqQ, hqI, hfib, hH⟩

/-- **EDP04–EDP06's rim rank on the final closed family** (projection of
`Gaf02Chain.edge_vertical_rank_EDPE`): at a point of `Y_j` with `|g| < 4Δ` and `T = 4Δ`, `D(g, T)`
is onto. -/
theorem edge_vertical_rank_C14Z_EDPE {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3}
    {L : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
      T V vs ζ Λz oM}
    (C : Gaf02Chain L.toLocalChartPackets Kj Ξ Γ S eg c cw) (hcw : 0 ≤ cw 0)
    (hSΞ : S 0 ≤ Ξ 0 / 10000) (hc : c 2 < 1 / 100000)
    (hϑ : 100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
      1 / 1000000) (hε0 : 0 ≤ ε) (hε : ε < 1) (hγc : 0 < γc) (hγc1 : γc ≤ 1 / 100)
    (hβc1 : βc ≤ 1 / 100000) {j : X} (hj : j ∈ L.edge.centres) {p : X}
    (hp : p ∈ ball j (100 * Δ * ρ j)) (hη : |L.edge.coord j p| < 5 * Δ)
    (ht : L.edge.smoothing p / ρ p < 5 * Δ)
    (hg : |EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero
      ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ (C.E p)) / ρ j| < 4 * Δ)
    (hT4 : EuclideanSpace.proj (0 : Fin 2)
      (gafHeightVector L.toLocalChartFamily L.zero (C.E p)) / C.scale p = 4 * Δ) :
    Function.Surjective (mvfderiv 𝓘(ℝ, E3) (edgeReferenceCoordinates
      ![fun z => EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero
          ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ (C.E z)) / ρ j,
        fun z => EuclideanSpace.proj (0 : Fin 2)
          (gafHeightVector L.toLocalChartFamily L.zero (C.E z)) / C.scale z]) p) :=
  (Gaf02Chain.edge_vertical_rank_EDPE (L := L.toLocalChartPacketsC14D.toLocalChartPacketsC14) C
    hcw hSΞ hc hϑ hε0 hε hγc hγc1 hβc1 hj p hp hη ht hg hT4).2.2.2.1

end Family


/-- **EDP06's first step on the chain object, on LC20's tail** (B:7103–7108; consumer of
`Gaf02Chain.edge_trace_EDPE` and of lane C14-EDP6's binding `eventually_edp06_collar_circle_EDP6`,
reused, no no-three hypothesis): on one tail, for every family `LocalChartPacketsC14` on a scale in
LC02's window (`β 3` below LC18's threshold, `3βc ≤ β 2 < 1`, `0 ≤ γ`) and every chain `C` on it
with EDP01's and (SE)'s numbers, every point `x ∈ Y_j` of the actual rim `T = 4Δ` with
`|g_j| < 4Δ` is two-stratum and lies at distance `< 2ρ(a)` from a circle centre `a` with
`‖η_a(x)‖ < 2(1 + γ)`. -/
theorem eventually_edp06_final_rim_circle_EDPE {Λ₀ : ℝ} (hΛ₀ : 0 < Λ₀) :
    ∃ w₀ : ℝ, 0 < w₀ ∧ ∀ w : ℝ, 0 < w → w < w₀ → w < 4 * Real.pi / 3 →
      ∀ (Y : ℕ → Type) [mY : ∀ i, MetricSpace (Y i)] [∀ i, ChartedSpace E3 (Y i)]
        [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (Y i)] [∀ i, CompactSpace (Y i)]
        (gY : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (Y i))
        (hmY : ∀ i a b, riemannianEDistOf (gY i) a b = ENNReal.ofReal (dist a b)),
      ∀ α : ℕ → ℝ, Tendsto α atTop atTop →
      (∀ i (p : Y i), ENNReal.ofReal (α i * firstVolumeScale (gY i) p (α i)⁻¹) ≤
        curvatureRadius (gY i) p) →
      ∀ᶠ i in atTop, ∀ (ρY : Y i → ℝ) (hρY : ∀ y, 0 < ρY y),
        (∀ p, firstVolumeScale (gY i) p w / 2 ≤ ρY p ∧
          ρY p ≤ 2 * firstVolumeScale (gY i) p (w / (2 * (1 + 2 * Λ₀⁻¹) ^ 3))) →
        ∀ (Λ : ℝ) (βY : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
          (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ),
        βY 3 ≤ threeSplittingExclusionThreshold.{0, 0} → 3 * βc ≤ βY 2 → βY 2 < 1 → 0 ≤ γ →
        ∀ L : LocalChartPacketsC14 (Y i) (gY i) (hmY i) ρY hρY Λ βY Δ σs K σc μ b s b' s' ε γc
          βc Lmax τ γ δ εr e T V vs ζ Λz,
        ∀ (Kj : ℕ) (Ξ Γ S eg cA cw : Fin 3 → ℝ)
          (C : Gaf02Chain L.toLocalChartPackets Kj Ξ Γ S eg cA cw),
        0 ≤ cw 0 → S 0 ≤ Ξ 0 / 10000 → cA 2 < 1 / 100000 →
        100 * (gafDerivativeBound + 1) * (1 + gafCutoffConstant + 1 * cw 0 / S 0) * Λ * Δ <
          1 / 1000000 → 0 ≤ ε → ε < 1 →
        ∀ j (hj : j ∈ L.edge.centres) (x : Y i), x ∈ ball j (100 * Δ * ρY j) →
        |L.edge.coord j x| < 5 * Δ → L.edge.smoothing x / ρY x < 5 * Δ →
        |EuclideanSpace.proj (0 : Fin 2) (gafEdgeVector L.toLocalChartFamily L.zero
          ⟨j, (Set.Finite.mem_toFinset _).mpr hj⟩ (C.E x)) / ρY j| < 4 * Δ →
        EuclideanSpace.proj (0 : Fin 2) (gafHeightVector L.toLocalChartFamily L.zero (C.E x)) /
          C.scale x = 4 * Δ →
        x ∈ scaledSplittingStratum.{0, 0} ρY hρY βY 2 ∧
          ∃ a, ∃ ha : a ∈ L.circle.centres, dist x a < 2 * ρY a ∧
            (let c := L.circle.chart a ha
             letI := (mY i).rescale (ρY a)⁻¹ (inv_pos.mpr (hρY a))
             ‖c.coord x‖ < 2 * (1 + γ)) := by
  obtain ⟨w₀, hw₀, hbind⟩ := eventually_edp06_collar_circle_EDP6 hΛ₀
  refine ⟨w₀, hw₀, ?_⟩
  intro w hw hww hwc Y mY _ _ _ gY hmY α hα hstand
  filter_upwards [hbind w hw hww hwc Y gY hmY α hα hstand] with i hi
  intro ρY hρY hwin Λ βY Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz hβ3 h3βc
    hβ2 hγ L Kj Ξ Γ S eg cA cw C hcw hSΞ hc hϑ hε0 hε j hj x hx hη ht hg hT4
  obtain ⟨-, hΔ, -⟩ := C.std
  obtain ⟨hhs, -, -⟩ := C.edge_height_EH_EDPE hcw hSΞ hc hϑ hε0 hε hj
  have htr := C.edge_trace_EDPE hcw hSΞ hc hϑ hε0 hε hj 1 ⟨zero_le_one, le_rfl⟩ x hx hη ht _ hg
    (by ring) (by rw [sub_self, zero_mul, zero_add, one_mul]; exact le_of_eq hT4)
  obtain ⟨hη401, -, hrim⟩ := htr
  obtain ⟨hband, -, -⟩ := hrim (by rw [sub_self, zero_mul, zero_add, one_mul]; exact hT4)
  have hηc := hη401
  unfold EdgeFamily.coord at hηc
  rw [dite_eq_left hj] at hηc
  exact hi ρY hρY hwin Λ βY Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz hβ3 h3βc
    hβ2 hγ hΔ L _ hhs.le j hj x (mem_ball.mp hx) hηc hband

end DifferentialGeometry.Geometry.Collapse
