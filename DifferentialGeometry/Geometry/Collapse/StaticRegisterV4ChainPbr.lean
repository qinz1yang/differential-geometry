import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainComplete
import DifferentialGeometry.Geometry.Collapse.StaticCounterexamples

/-!
# PBR02 and PBR03 on register V4: the static data on the tail, and the counterexample reduction

Lane C14-REG-CHAIN, G3. Blueprint `master207B.tex`, PBR02
(`thm:fibration-closed-standing-static-certificates`, B:10257–10275) and PBR03
(`thm:fibration-closed-static-collapse-threshold`, B:10277–10333).

PBR02 reads: every sufficiently late member of the closed standing construction has an actual FC39
decomposition and finite KL graph presentation on its SAME smooth carrier; the parameter assignment
is independent of the centre and of the member on that tail. Its proof: PBR01 gives one assignment
and tail; LPA supplies local packets; SGP/EGP/TCP their images; GAF the sequential adjustments; ZSP,
EDP, FDC the compact restrictions and faces; FDC04 and FC42 (with FC41) the graph presentation.

What is proved here (unconditional):

* `exists_gafSelection_RGC`: selections of original preimages over the enlarged stage clouds exist
  on every nonempty carrier (the clouds are images).
* `pbr02_static_RGC` — PBR02's STATIC-DATA part: on every closed standing sequence, ONE strategy
  `T` with the validity record and an inhabited register; for EVERY register `R` (one assignment,
  fixed before the members) prefix witnesses `ε_r, δ, Λ_z` and, on every member `m ≥ R.tail`, a
  normalized model `M` of the SAME carrier (`M.ψ` a diffeomorphism onto `(W_m).Carrier`,
  `M.gX = ψ^*g_m`), ONE instance `F` of the final family at exactly the register's values (LPA02's
  joint witness and the zero selection inside `F`), a selection `sel`, and the chain
  `C : Gaf02Chain F.family.toLocalChartPackets K (Ξ_j(Γ_j)) Γ Σ e c (stageCwAt_V4C R.stage)` on the
  register's own stage data (GAF02 CORE: `E = Ψ₃Ψ₂Ψ₁𝓔⁰`), with EDP01's (SD) at the register's
  `C_ρ`. The parameters `R` do not depend on `m` or on a centre.
* `pbr03_reduction_RGC` — PBR03's proof up to its last line: for every certificate `Good`, EITHER
  the closed threshold `w₀` exists, OR there is a closed standing sequence of counterexamples at the
  ratios `w_{m+2}` without `Good`, on whose tail register V4 yields the static data above.

NOT proved (obstruction, recorded in `state-C14-REG-CHAIN.md`): PBR02's certificate part "static
data ⇒ FC39 decomposition / KL graph presentation" needs GAF02 BASES on the enhanced chain
(lanes C14-GAF8 ChainE, C14-BASES), ZSP/EDP/FDC on that chain, FC39's certificate producer and FC42;
PBR03's last line "PBR02 makes every late counterexample a graph manifold" is exactly that step.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- **Selections exist**: on a nonempty carrier, every packet has a selection of original
preimages over its three enlarged stage clouds (each cloud is the image `π_j𝓔⁰(Ã_j)`). -/
theorem exists_gafSelection_RGC {X : Type} [MetricSpace X] [ChartedSpace E3 X]
    [IsManifold 𝓘(ℝ, E3) ∞ X] [CompactSpace X] [Nonempty X]
    {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
    {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
    {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
    {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ}
    (P : LocalChartPackets X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V) :
    ∃ sel : Fin 3 → BlockSpace (fun _ : CGPTag P.toLocalChartFamily P.zero => ℝ²) → X,
      ∀ st, ∀ x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st,
        cgpProjMap P.toLocalChartFamily P.zero (gafStageTags P.toLocalChartFamily P.zero st)
          (sel st x) = x := by
  classical
  refine ⟨fun st x => if h : x ∈ gafCloudEnlarged P.toLocalChartFamily P.zero st then
    Classical.choose h else Classical.arbitrary X, fun st x hx => ?_⟩
  simp only [hx, ↓reduceDIte]
  exact (Classical.choose_spec hx).2

/-- **PBR02, static-data part, on register V4** (see the module header). -/
theorem pbr02_static_RGC (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
      Nonempty (ClosedRegisterV4 (earlyDataSharedV4 K) T) ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
        ∃ M : ClosedModel (Wseq m) (gseq m),
          M.gX = Diffeomorph.pullbackMetricCross (gseq m) M.ψ ∧
          ∃ F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz,
            ∃ sel : Fin 3 → BlockSpace (fun _ : CGPTag F.family.toLocalChartFamily F.family.zero =>
                ℝ²) → M.X,
              (∀ st, ∀ x ∈ gafCloudEnlarged F.family.toLocalChartFamily F.family.zero st,
                cgpProjMap F.family.toLocalChartFamily F.family.zero
                  (gafStageTags F.family.toLocalChartFamily F.family.zero st) (sel st x) = x) ∧
              ∃ C : Gaf02Chain F.family.toLocalChartPackets K
                  (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig
                  R.stage.e R.stage.c (stageCwAt_V4C R.stage),
                C.sel = sel ∧ ∀ p : M.X,
                  |C.scale p - F.ρ p| ≤
                    closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage * R.later.scale.Λ *
                      F.ρ p ∧
                  (∀ v : TangentSpace 𝓘(ℝ, E3) p, |mvfderiv 𝓘(ℝ, E3) C.scale p v| ≤
                    closedScaleConstantV4 (earlyDataSharedV4 K) T R.stage * R.later.scale.Λ *
                      Real.sqrt (M.gX.inner p v v)) ∧
                  0 < C.scale p := by
  obtain ⟨T, hv, -, -, -, -, hR⟩ := register_yields_chain_RGC K hK A hA Wseq gseq hf hg
  refine ⟨T, hv, exists_closedRegisterV4 _ T, fun R => ?_⟩
  obtain ⟨-, εr, -, Λz, δc, -, -, ht⟩ := hR R
  refine ⟨εr, δc, Λz, fun m hm => ?_⟩
  obtain ⟨M, F, -, -, -, -, -, -, hchain⟩ := ht m hm
  have : ConnectedSpace (Wseq m).Carrier := (hf m).connected
  have : Nonempty M.X := ⟨M.ψ.symm (Classical.arbitrary (Wseq m).Carrier)⟩
  obtain ⟨sel, hsel⟩ := exists_gafSelection_RGC F.family.toLocalChartPackets
  obtain ⟨C, hC, hp⟩ := hchain sel hsel
  exact ⟨M, M.metric_eq, F, sel, hsel, C, hC, fun p => ⟨(hp p).2.1, (hp p).2.2.1, (hp p).2.2.2⟩⟩

/-- **PBR03's reduction on register V4** (B:10293–10333, up to the last line; see the module
header): for every certificate `Good`, either the closed finite-scale threshold exists, or there is
a closed standing sequence of counterexamples without `Good` (closed connected members, finite
curvature scales, the standing hypotheses at `w_{m+2}`), on whose tail register V4 yields ONE
assignment, the final family at its values and the chain on its own stage data. -/
theorem pbr03_reduction_RGC (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ) (hA : ∀ x, 0 < x → 0 < A x)
    (Good : CompactCarrier.{u} → Prop) :
    (∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ → Good W) ∨
    ∃ (Wseq : ℕ → CompactCarrier.{u})
      (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier),
      (∀ m, ClosedMemberFacts (Wseq m) ∧ (∀ p, curvatureRadius (gseq m) p ≠ ⊤) ∧
        closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2)) ∧
        ¬ Good (Wseq m)) ∧
      ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
        PartialClosedThresholdValidityV4Rows K A Wseq gseq (earlyDataSharedV4 K) T ∧
        Nonempty (ClosedRegisterV4 (earlyDataSharedV4 K) T) ∧
        ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, ∀ m, R.later.tail ≤ m →
          ∃ M : ClosedModel (Wseq m) (gseq m),
            ∃ F : ClosedFamilyInstanceC14DV4 K R M δ εr Λz,
              ∃ sel : Fin 3 → BlockSpace (fun _ : CGPTag F.family.toLocalChartFamily
                  F.family.zero => ℝ²) → M.X,
                (∀ st, ∀ x ∈ gafCloudEnlarged F.family.toLocalChartFamily F.family.zero st,
                  cgpProjMap F.family.toLocalChartFamily F.family.zero
                    (gafStageTags F.family.toLocalChartFamily F.family.zero st) (sel st x) = x) ∧
                Nonempty (Gaf02Chain F.family.toLocalChartPackets K
                  (fun j => (earlyDataSharedV4 K).Ξ j (R.stage.Γ j)) R.stage.Γ R.stage.Sig
                  R.stage.e R.stage.c (stageCwAt_V4C R.stage)) := by
  by_cases h : ∃ w₀ : ℝ, 0 < w₀ ∧ w₀ < euclideanThreeUnitBallVolume ∧
      ∀ (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
        (g : SmoothRiemannianMetric W.model W.Carrier),
        (∀ p, curvatureRadius g p ≠ ⊤) → closedCollapseHypotheses W g K A w₀ → Good W
  · exact Or.inl h
  right
  obtain ⟨W, hW, g, hseq⟩ := exists_closed_standing_sequence_of_no_threshold K A Good h
  have hf : ∀ m, ClosedMemberFacts (W m) := fun m => ⟨(hseq m).2.1.1, hW m⟩
  obtain ⟨T, hv, hreg, hR⟩ := pbr02_static_RGC K hK A hA W g hf (fun m => (hseq m).2.1)
  refine ⟨W, g, fun m => ⟨hf m, (hseq m).1, (hseq m).2.1, (hseq m).2.2.1⟩, T, hv, hreg,
    fun R => ?_⟩
  obtain ⟨εr, δ, Λz, ht⟩ := hR R
  refine ⟨εr, δ, Λz, fun m hm => ?_⟩
  obtain ⟨M, -, F, sel, hsel, C, -, -⟩ := ht m hm
  exact ⟨M, F, sel, hsel, ⟨C⟩⟩

end DifferentialGeometry.Geometry.Collapse
