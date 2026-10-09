import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFdcFacts74
import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainFdc04AtOCLFD4

/-!
# FDC04 on the register: the consumer of `fdc04_row_at_OCL_FD4` (G6)

Lane S-FDC04b (`_FD4`), group G6. `register_yields_fdc04_FD4`: on the sources of
`register_yields_fdcFacts_RNUM` (the numerics record `N : ClosedRowsNumericsAt74 S` and the member
facts `Hm`), for every bases object `B` and every stage-bases object `Ab`, `fdc04_row_at_OCL_FD4`
holds at the produced cut choice `D_R` with `hT hNb hcw εr` from `N`, `Htail := (Hm B).facts _` and
`5 ≤ K` from `10 ≤ K`: FDC04's row on the production chain (zero pieces, slim pieces, four-piece
cover, edge pieces, FDC02 / EDP05 row, horizontal disks) and the FC39 cover field `CutCoverFacts74`
with the zero exit produced. Technique (the failure of G4's consumer): the register tail is peeled
by `Exists.imp` combinators and the final conjunct is supplied by `exact`; no `obtain` on the goal
that carries the `type_of%` term (that `obtain` ran into the 200000 heartbeat limit).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry GC.Endpoint GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Analysis
open DifferentialGeometry.Topology
open GC.GraphManifold GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

open DifferentialGeometry.Topology.Handle in
attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

/-- **Consumer: the register yields FDC04's row and cover field at `D_R`** (see the module
docstring). -/
theorem register_yields_fdc04_FD4 (K : ℕ) (hK : 10 ≤ K) (A : ℝ → ℝ)
    (hA : ∀ x, 0 < x → 0 < A x) (Wseq : ℕ → CompactCarrier.{0})
    (gseq : ∀ m, SmoothRiemannianMetric (Wseq m).model (Wseq m).Carrier)
    (hf : ∀ m, ClosedMemberFacts (Wseq m))
    (hg : ∀ m, closedCollapseHypotheses (Wseq m) (gseq m) K A (closedCounterexampleRatio (m + 2))) :
    ∃ T : ClosedThresholdsV4 (earlyDataSharedV4 K),
      ∀ R : ClosedRegisterV4 (earlyDataSharedV4 K) T, ∃ εr δ Λz : ℝ, 0 < εr ∧ εr < 1 / 4 ∧
        ∃ n : ℕ, ∀ m, n ≤ m → ∃ M : ClosedModel (Wseq m) (gseq m), Nonempty M.X ∧
          ∀ x₀ : M.X, ∃ S : ClosedChainEZRowsSource_RGC K R M δ εr Λz, S.chain.x₀ = x₀ ∧
            ∃ N : ClosedRowsNumericsAt74 S, ∃ Hm : ∀ B : ClosedBases74 S,
              ClosedFdcMemberFacts74 S B, ∀ (B : ClosedBases74 S) (Ab : SmoothStageBases74 S),
              type_of% (S.fdc04_row_at_OCL_FD4 B N.strategy_below N.nb_eq N.cw_eq N.eps_lt
                (le_trans (by norm_num) hK) Ab ((Hm B).facts _)) :=
  (register_yields_fdcFacts_RNUM K hK A hA Wseq gseq hf hg).imp fun T hT R =>
    (hT.2.2.2 R).imp fun εr h1 => h1.imp fun δ h2 => h2.imp fun Λz h3 =>
      ⟨h3.1, h3.2.1, h3.2.2.imp fun n hn m hm => (hn m hm).imp fun M h4 =>
        ⟨h4.1, fun x₀ => (h4.2 x₀).imp fun S h5 =>
          ⟨h5.1, h5.2.1.elim fun N => ⟨N, h5.2.2, fun B Ab =>
            S.fdc04_row_at_OCL_FD4 B N.strategy_below N.nb_eq N.cw_eq N.eps_lt
              (le_trans (by norm_num) hK) Ab ((h5.2.2 B).facts _)⟩⟩⟩⟩

end DifferentialGeometry.Geometry.Collapse
