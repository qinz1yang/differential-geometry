import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainLinkValues74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainEZComplete

/-!
# The cut choice at the register: numerics discharged by the ONE strategy (D74-18 order)

Lane C14-REG-CHAIN (by C14-REG-CHAINc), G17. Draft 74 §6.3 / D74-18: "one early choice → one
strategy → `R` → same FAMZ parameters → current tail member → `P_Z` → `Ĉ_R` → `B_R` → `D_R`". The
cut-choice producer (G12) and the link values (G14) take the numeric premises `ε_r < 1/2`,
`σ_c = q_e ≤ 1/2`, `0 ≤ γ ≤ 3/4`; here they are discharged in that order:

* `ClosedLaterV4.qe_le_half_R74`: `q_e < θ_e²/10⁸ < 1/2` (PR14, a field of every register);
* `register_yields_cutChoice_R74`: the strategy of `register_yields_chainEJAZ_RGC` (the chain
  strategy `exists_chainEStrategy_RGC` refined by the C14Z realization), at which every register
  has `0 < ε_r < 1/4` (FAMZ's own choice), `0 < γ < 1/100` (the Gram cap), and on every tail member,
  for every base point, a C14Z source `S` with that base point (`B_R = S.bases74`) and a cut choice
  `D_R` with the D74-5 value rows on `W` (`closed_link_values_R74`) — no fixed `S` is claimed to lie
  in a good tail after the fact; every number is read before the member.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

/-- PR14: the edge quality of every register is at most `1/2` (`q_e < θ_e²/10⁸`, `θ_e < 1/100`). -/
theorem ClosedLaterV4.qe_le_half_R74 {D : ClosedEarlyData} {T : ClosedThresholdsV4 D}
    {st : ClosedStage D} (la : ClosedLaterV4 D T st) : la.err.co.qe ≤ 1 / 2 := by
  have h1 : la.err.co.qe < la.circle.θe ^ 2 / 10 ^ 8 :=
    la.qe_lt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h2 := la.θe_lt_hundredth_VAL6
  have h3 := la.θe_pos
  have h4 : la.circle.θe ^ 2 / 10 ^ 8 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- **The register yields the cut choice and the D74-5 value rows** (D74-18's order): at the
strategy of `register_yields_chainEJAZ_RGC`, every register has `0 < ε_r < 1/4` and, on every tail
member (a nonempty model), for every base point, a C14Z source with that base point and a cut
choice on its own bases object with the edge row on `W`, the circle region inside GAF07's `X₁`,
the decomposition `W = ψ(Z) ∪ ψ(slimSet) ∪ ψ(M₂)` and `q_j ∘ ψ⁻¹ = Θ_j ∘ f_j ∘ ψ⁻¹`. -/
theorem register_yields_cutChoice_R74 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{u})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ClosedStrategyRefinesV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) ∧
      T.Nb = maxNb_V4C ∧ T.cw = maxCw_V4C ∧
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, 0 < εr ∧ εr < 1 / 4 ∧
        ∀ m, R.later.tail ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧
          ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ D : ClosedCutChoice74 S S.bases74,
              M.ψ '' D.edgeSet = M.ψ '' D.M₂ ∩ (S.stageProjW_R74 1 ⁻¹'
                (S.chain.toChain.finalBase_BAS 1 ∩
                  edgeRatio_R74 S.F.family.toLocalChartPacketsC14) ∩
                {x | S.edgeHeightW_R74 x ≤ R.edgeLevel_R74}) ∧
              M.ψ '' D.M₃ ⊆ S.stageProjW_R74 0 ⁻¹' (S.chain.toChain.finalBase_BAS 0 ∩
                gaf07CircleRatio_G47 S.F.family.toLocalChartPacketsC14.toLocalChartPackets) ∧
              M.ψ '' S.chain.zeroUnion_ZSP35 ∪ M.ψ '' D.slimSet ∪ M.ψ '' D.M₂ = univ ∧
              ∀ j x, S.stageProjW_R74 j x =
                S.chain.toChain.Θ_BAS j (S.chain.toChain.stageMap_BAS j (M.ψ.symm x)) := by
  obtain ⟨U', hU'U, hchain⟩ :=
    exists_chainEStrategy_RGC K (closedStrategyCompleteV4C (earlyDataSharedV4 K))
  obtain ⟨T, hTU', -, -, hfam⟩ :=
    exists_closed_realization_C14Z_RGC K hK A hA Wseq gseq hf hg U'
  have hTU := hTU'.trans_RGC hU'U
  have hbU' : ClosedStrategyBelowV4 T U' := hTU'.below_VAL6
  have hb : ClosedStrategyBelowV4 T (closedStrategyCompleteV4C (earlyDataSharedV4 K)) :=
    hTU.below_VAL6
  obtain ⟨-, -, hgram, -⟩ := hb.complete_caps_V4C
  refine ⟨T, hTU, hTU.Nb_eq, hTU.cw_eq, fun R => ?_⟩
  obtain ⟨hγ0, hγ1, -⟩ := R.gram_request_of_below_V4C hgram
  obtain ⟨εrF, δ'F, ΛzF, hF⟩ := hfam
  obtain ⟨hεr0, hεr14, hεrε₀, -, -, hΛz, δc, -, -, ht⟩ := hF R
  refine ⟨εrF R.stage R.later.circle R.later.excl R.later.err R.later.scale R.later.split.b
      R.later.split.β₁, δc, ΛzF R.stage R.later.circle R.later.excl R.later.err R.later.scale
      R.later.split.b R.later.split.β₁, hεr0, hεr14, fun m hm => ?_⟩
  obtain ⟨M, ⟨F⟩, -, -⟩ := ht m hm
  have : ConnectedSpace (Wseq m).Carrier := (hf m).connected
  refine ⟨M, ⟨M.ψ.symm (Classical.arbitrary (Wseq m).Carrier)⟩, fun x₀ => ?_⟩
  obtain ⟨C, hCx⟩ := hchain T hbU' R F.family.toLocalChartPacketsC14 hεr0.le hεrε₀ hΛz x₀
  obtain ⟨D, hD⟩ := closed_link_values_R74 ⟨F, C⟩ (ClosedChainEZRowsSource_RGC.bases74 ⟨F, C⟩)
    (by linarith) R.later.qe_le_half_R74 hγ0.le (by linarith)
  exact ⟨⟨F, C⟩, hCx, D, hD⟩

end DifferentialGeometry.Geometry.Collapse
