import DifferentialGeometry.Geometry.Collapse.StaticRegisterValidity
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollapsePacket

/-!
# The boundary threshold validity (lane FC39-VAL; external review 49, B.1, T49-4)

Design `build-logs/resume/design-FC39-VAL.md` §3, §5. Replaces the `opaque` placeholder
`BoundaryThresholdValidity` of the FC39-P0 targets (`evidence/fc39-p0/Targets.lean.txt:50–51`). The
boundary register (`BoundaryRegister.lean:70–166`) is independent of the member: ONE register for
every later `(W, g, B)` (wrappers (4), (6), (7)). Its interior is the closed register on the
augmented constants (`BoundaryRegister.toClosedRegister`), so the closed parameter adapter
(`StaticRegisterFamilyAdapter`) is reused; the boundary export tolerance is
`εB := min (1/1000) (β₁²/1000)`.

* `BoundaryPacketRest … P …` / `BoundaryPacketsOut W g K A δn B εB …`: the per-member conclusion
  (after / with the export packet `P`) of LC88's T3 `lc88_boundary_collapse_packet_BDRY1`
  (`LocalExport/BoundaryCollapsePacket.lean:167–219`, verbatim; the export packet with `P.cusp = B`,
  the original scale, ONE completion `ĝ`, the packets `LocalPacketsOn` on `(W°, d_ĝ)`, the transport
  clauses and the labelled product alternative) at the given prefix values.
* `BoundaryModel W g B`: a universe-`0` copy of a boundary member with the pulled-back metric and
  the transported nearly cuspidal boundary (T3 and `LocalPacketsOn` are stated on `Type`,
  `BoundaryLocalPacketsOn.lean:367`; its existence for `W : CompactCarrier.{u}` is an open adapter,
  design §4).
* `BoundaryFamilyAt K A R m W g B`: on some such model, T3's per-member conclusion at the register's
  interior values (with `V = R.later.split.V`, `T = T₀`, `Lmax = famLmax`).
* `BoundaryThresholdValidity K A D T`: the early sources on `D.toClosedEarlyData`, the constant
  interior slots (`lc18`, `I₁`) for every boundary request, and the per-member package for EVERY
  register, EVERY `m ≥ max 2 R.tail` and EVERY member at `boundaryCounterexampleRatio δ* m`.

QUANTIFIER GATE (dispositions 49): T2/T3 return `V` and the tail AFTER a standing sequence; the
`family` field needs them for all later members at once. It cannot be produced by rewriting
`∀ sequence ∃ V, N` as `∃ V, N ∀ sequence`; the uniformisation (two-step counterexample-sequence
argument, design §5) is open, and so is the universe-`0` boundary model. Rows-level `Out`s of the
boundary slots (BCG02–03, short comparisons, BCG05–06, BCP02/BCP03/BCP05 on the T3 packet) come in
later files.
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

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

universe u

/-- The closed register retained by a boundary register for the interior blocks (BR04–BR23). -/
def BoundaryRegister.toClosedRegister {D : BoundaryEarlyData} {T : BoundaryThresholds D}
    (R : BoundaryRegister D T) :
    ClosedRegister D.toClosedEarlyData (T.toClosed R.ϑ R.shortErr R.bcgErr) :=
  ⟨R.stage, R.later⟩

/-- The boundary export tolerance `εB := min (1/1000) (β₁²/1000)` (T3's `εB ≤ 1/1000`,
`εB ≤ β₁²/1000`). -/
def BoundaryRegister.famεB {D : BoundaryEarlyData} {T : BoundaryThresholds D}
    (R : BoundaryRegister D T) : ℝ :=
  min (1 / 1000) (R.later.split.β₁ ^ 2 / 1000)

/-- **The rest of T3's per-member conclusion** (`lc88_boundary_collapse_packet_BDRY1`, verbatim,
after `P.cusp = B`) for a given export packet `P`. -/
def BoundaryPacketRest (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (A : ℝ → ℝ) (δn εB : ℝ)
    (P : BoundaryExportPacket W g K A δn εB) (Λ w : ℝ) (β : ℕ → ℝ)
    (Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ) : Prop :=
  ∃ ρ : W.Carrier → ℝ, ∃ hρpos : ∀ p, 0 < ρ p,
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ ρ ∧
    (∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y) ∧
    (∀ p, firstVolumeScale g p w / 2 < ρ p ∧
      ρ p < 2 * firstVolumeScale g p (w / (2 * (1 + 2 * Λ⁻¹) ^ 3))) ∧
    (∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) ≤ β 1 ^ 3 / 2000) ∧
    letI := interiorChartedT_BDRY1 W
    haveI := interiorManifoldT_BDRY1 W
    ∃ _ : ConnectedSpace (W.pieceInterior ⊤),
    ∃ ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤),
    ∃ O : Set (W.pieceInterior ⊤), IsOpen O ∧
      {x : W.pieceInterior ⊤ | ENNReal.ofReal 4 ≤ distanceToBoundary W g x} ⊆ O ∧
      (∀ x ∈ O, ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x) ∧
      (∀ (x : W.pieceInterior ⊤) (v : TangentSpace 𝓘(ℝ, E3) x),
        (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v) ∧
      letI := inducedMetricSpace ĝ
      ∃ _ : CompleteSpace (W.pieceInterior ⊤),
      ∃ F : LocalPacketsOn (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
          (fun x => ρ x) (fun x => hρpos x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
          T V {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
          {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x},
        (∀ x : W.pieceInterior ⊤,
          ENNReal.ofReal 5 < distanceToBoundary W g x →
          scaledSplittingRank.{0, 0} (fun y : W.pieceInterior ⊤ => ρ y)
              (fun y => hρpos y) β x =
            @scaledSplittingRank.{0, 0} W.Carrier (inducedMetricSpace g) ρ hρpos β
              x) ∧
        (letI := F.instMetricN
        letI := F.instChartedN
        letI := F.instMetricC
        (∀ z (hz : z ∈ F.zero.centres),
          Subtype.val '' Metric.ball z (F.zero.zero z hz).radius =
            riemannianBallOf g z.val (F.zero.zero z hz).radius) ∧
        ((∃ (i j : Fin P.cusp.count), i ≠ j ∧
          ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1)
            W.Carrier ∞,
            (∀ p, D p ∈ P.cusp.component i ↔ p.2.1 = 0) ∧
              ∀ p, D p ∈ P.cusp.component j ↔ p.2.1 = 1) ∨
        ((∀ i j : Fin P.cusp.count, i ≠ j →
          Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
            ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) ∧
          Disjoint {x | P.level i x ≤ 90} {y | P.level j y ≤ 90} ∧
          ∀ x y, P.level i x ≤ 90 → P.level j y ≤ 90 →
            ENNReal.ofReal 1 ≤ riemannianEDistOf g x y) ∧
        (∀ z (hz : z ∈ F.zero.centres) (i : Fin P.cusp.count),
          Disjoint (riemannianBallOf g z.val (F.zero.zero z hz).radius)
            ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) ∧
        Disjoint (⋃ z, ⋃ hz : z ∈ F.zero.centres,
            riemannianBallOf g z.val (F.zero.zero z hz).radius)
          (⋃ i, tsupport (P.toBoundaryCollarPacket.block i)))))

/-- **T3's per-member conclusion** (`lc88_boundary_collapse_packet_BDRY1`, verbatim) at the given
prefix values, for one member `(W, g, B)` at the ratio `δn`: an export packet with `P.cusp = B` and
the rest of the conclusion. -/
def BoundaryPacketsOut (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (A : ℝ → ℝ) (δn : ℝ)
    (B : NearlyCuspidalBoundary W g K δn) (εB Λ w : ℝ) (β : ℕ → ℝ)
    (Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ) : Prop :=
  ∃ P : BoundaryExportPacket W g K A δn εB, P.cusp = B ∧
    BoundaryPacketRest W g K A δn εB P Λ w β Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V

/-- **A universe-`0` copy of a boundary member**: a carrier, a diffeomorphism onto the member, the
pulled-back metric and the transported nearly cuspidal boundary (component by component). -/
structure BoundaryModel (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
    {K : ℕ} {δ : ℝ} (B : NearlyCuspidalBoundary W g K δ) where
  /-- The small carrier. -/
  W₀ : CompactCarrier.{0}
  connected₀ : ConnectedSpace W₀.Carrier
  /-- The identification with the member. -/
  ψ : W₀.Carrier ≃ₘ⟮W₀.model, W.model⟯ W.Carrier
  /-- The pulled-back metric. -/
  g₀ : SmoothRiemannianMetric W₀.model W₀.Carrier
  metric_eq : g₀ = Diffeomorph.pullbackMetricCross g ψ
  /-- The transported nearly cuspidal boundary. -/
  B₀ : NearlyCuspidalBoundary W₀ g₀ K δ
  count_eq : B₀.count = B.count
  component_eq : ∀ i, ψ '' B₀.component i = B.component (Fin.cast count_eq i)

/-- **The per-member package at a boundary register**: on a universe-`0` model of the member, T3's
conclusion at the register's interior values. -/
def BoundaryFamilyAt (K : ℕ) (A : ℝ → ℝ) {D : BoundaryEarlyData} {T : BoundaryThresholds D}
    (R : BoundaryRegister D T) (m : ℕ) (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio D.δStar m)) : Prop :=
  ∃ M : BoundaryModel W g B, ∃ δ εr : ℝ, 0 < δ ∧ 0 < εr ∧ εr < 1 / 4 ∧
    letI := M.connected₀
    BoundaryPacketsOut M.W₀ M.g₀ K A (boundaryCounterexampleRatio D.δStar m) M.B₀ R.famεB
      R.later.scale.Λ R.later.scale.w R.toClosedRegister.famβ R.later.excl.Δ
      R.toClosedRegister.famσs R.toClosedRegister.famσc R.later.err.μ R.later.split.b
      R.toClosedRegister.fams R.toClosedRegister.famb' R.toClosedRegister.fams'
      R.toClosedRegister.famε R.toClosedRegister.famγc R.toClosedRegister.famβc
      R.toClosedRegister.famLmax R.later.err.τ R.later.circle.γ δ εr R.later.err.e₀
      R.later.split.T₀ R.later.split.V

/-- **The boundary threshold validity** (review 49, B.1): the early sources, the constant interior
slots, and the per-member package for EVERY register and EVERY later member (the QUANTIFIER GATE is
the open uniformisation that produces this field, design §5). -/
structure BoundaryThresholdValidity (K : ℕ) (A : ℝ → ℝ) (D : BoundaryEarlyData)
    (T : BoundaryThresholds D) : Prop where
  /-- PR01 `N` on the augmented constants. -/
  N_ge : gafMultiplicity ≤ D.N
  /-- PR01 `P`. -/
  P_ge : cgpProfileBound ≤ D.P
  /-- PR02 `L₀`. -/
  L₀_ge : gafDerivativeBound ≤ D.L₀
  /-- PR03 `Ξ_j`: CFS15's conclusion. -/
  Ξ_cfs15 : ∀ j, Cfs15ModulusOut (gafStageDim j) K (5 / 3) (D.Ξ j)
  /-- BR04–BR23, PR12: LC18's obstruction for every boundary request. -/
  lc18_le : ∀ ϑ sh bc, (T.interior ϑ sh bc).lc18 ≤ threeSplittingExclusionThreshold.{0, 0}
  /-- BR04–BR23, PR20: the comparison constant `I(1)`. -/
  I₁_eq : ∀ ϑ sh bc, (T.interior ϑ sh bc).I₁ = ∫ t in (0 : ℝ)..1, Real.sinh t ^ 2
  /-- BR04–BR25: the per-member package for every register and every later member. -/
  family : ∀ (R : BoundaryRegister D T) (m : ℕ), max 2 R.tail ≤ m →
    ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier)
      (B : NearlyCuspidalBoundary W g K (boundaryCounterexampleRatio D.δStar m)),
      boundaryVolumeCollapsed W g (boundaryCounterexampleRatio D.δStar m) →
      curvatureDerivativesControlled g K A (boundaryCounterexampleRatio D.δStar m) →
      BoundaryFamilyAt K A R m W g B

namespace BoundaryThresholdValidity

variable {K : ℕ} {A : ℝ → ℝ} {D : BoundaryEarlyData} {T : BoundaryThresholds D}

/-- **Consumer**: the splitting coordinate `β 3 = β₃` of the interior family is below LC18's
obstruction. -/
theorem famβ_three_le_VAL (hv : BoundaryThresholdValidity.{u} K A D T)
    (R : BoundaryRegister D T) :
    R.toClosedRegister.famβ 3 ≤ threeSplittingExclusionThreshold.{0, 0} := by
  rw [ClosedRegister.famβ_three_VAL]
  exact (R.later.β₃_lt.trans_le (hv.lc18_le R.ϑ R.shortErr R.bcgErr)).le

end BoundaryThresholdValidity

/-- **Consumer (the register's `εB` meets T3's request)**. -/
theorem BoundaryRegister.famεB_spec_VAL {D : BoundaryEarlyData} {T : BoundaryThresholds D}
    (R : BoundaryRegister D T) :
    0 < R.famεB ∧ R.famεB ≤ 1 / 1000 ∧ R.famεB ≤ R.later.split.β₁ ^ 2 / 1000 := by
  have := R.later.β₁_pos
  exact ⟨lt_min (by norm_num) (by positivity), min_le_left _ _, min_le_right _ _⟩


/-- **Consumer (verbatim check)**: T3 with its per-member conclusion written as
`BoundaryPacketsOut`. -/
theorem lc88_boundaryPacketsOut_VAL
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
      ∀ εB : ℝ, 0 < εB → εB ≤ 1 / 1000 → εB ≤ β 1 ^ 2 / 1000 →
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
        BoundaryPacketsOut (W n) (g n) K A (boundaryCounterexampleRatio δ₀ n) (B n) εB Λ w β Δ σs σc
          μ b s b' s' ε γc βc Lmax τ γ δ εr e T V :=
  lc88_boundary_collapse_packet_BDRY1 hσs hσs1 K hK A hA

end DifferentialGeometry.Geometry.Collapse
