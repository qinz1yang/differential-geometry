import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreFlowW
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreApplications

/-!
# BCG06, G3: consumers of the relative supported flow on `W` (lane BCG6-Kb)

* `original_cuspCore_relative_flow_BCG6K`: for every collar packet with `ε ≤ 1/1000` and every
  component, the ORIGINAL boundary pair `(u_b, v_b) = P.block b` (the map `E = F_∂`, zero actual
  error, POSITIVE tolerances `ε∂ = 10⁻⁷`, `c₃ = 10⁻⁶`) carries the relative supported flow on `W`:
  `Φ : ℝ → W ≃ₘ W`, identity off a compact subset of `band ∩ {38 < η_b < 42}`, `Φ 0 = id`,
  `G_{s(t)} ∘ Φ t = level_b` everywhere, `Φ 1 {level_b ≤ 40} = C_b`, `Φ 1 {level_b = 40} = H_b`;
* `doubleCusp_cuspCore_relative_flow_BCG6K`: both ends of the double cusp `T² × [0, 240]`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Topology.Manifold
open GC.Seifert

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ}

namespace BoundaryCollarPacket

/-- **Consumer: the relative supported flow of the original core on `W`** (every collar packet
with `ε ≤ 1/1000`, every component; `E = F_∂`, `ε∂ = 10⁻⁷`, `c₃ = 10⁻⁶`). -/
theorem original_cuspCore_relative_flow_BCG6K (P : BoundaryCollarPacket W g K A w₀ ε)
    (hε : ε ≤ 1 / 1000) (b : Fin P.cusp.count) :
    ∃ (K' : Set W.Carrier) (Φ : ℝ → Diffeomorph W.model W.model W.Carrier W.Carrier ∞),
      IsCompact K' ∧
      (∀ x ∈ K', x ∈ P.collarBand_BAUGA b ∧ 38 < P.height b x ∧ P.height b x < 42) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod W.model) W.model ∞ (fun q : ℝ × W.Carrier => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧ (∀ t x, x ∉ K' → Φ t x = x) ∧
      (∀ t x, P.coreLevelT_BCG6K b (P.originalBoundaryU_BCG6K b) (Real.smoothTransition t)
        (Φ t x) = P.level b x) ∧
      Φ 1 '' {x | P.level b x ≤ 40} =
        P.cuspCore_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K ∧
      Φ 1 '' {x | P.level b x = 40} =
        P.cuspFront_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K := by
  obtain ⟨K', Φ, hK', hK'N, hjoint, h0, hoff, -, hlev, -, -, hcore, hfront⟩ :=
    cuspCore_relative_flow_BCG6K hε (P.contMDiff_originalBoundaryU_BCG6K b)
      (εd := 1 / 10000000) (c₃ := 1 / 1000000) (by norm_num) (by norm_num) (by norm_num)
      (P.original_BI_BCG6K (by norm_num) b) (P.original_BFM_BCG6K b)
      (P.original_BD_BCG6K (by norm_num) b)
  exact ⟨K', Φ, hK', hK'N, hjoint, h0, hoff, hlev, hcore, hfront⟩

end BoundaryCollarPacket

/-- The double cusp carrier is connected (as in `SmallBoundaryPackets`). -/
local instance connectedSpace_annulusCircleCarrier_flow_BCG6K :
    ConnectedSpace annulusCircleCarrier.{u}.Carrier :=
  connectedSpace_productSet (Or.inl rfl)

/-- **Consumer on the double cusp `T² × [0, 240]`**: both ends carry the relative supported flow
of the original core on the whole carrier. -/
theorem doubleCusp_cuspCore_relative_flow_BCG6K (K : ℕ) (hK : 2 ≤ K) :
    ∃ a : ℝ, ∃ ha : 0 < a, ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧
      ∃ P : BoundaryExportPacket annulusCircleCarrier.{u} (doubleCuspMetric.{u} a ha) K A
          (1 / 6408) (1 / 1000),
        P.cusp.count = 2 ∧ ∀ b,
          ∃ (K' : Set annulusCircleCarrier.{u}.Carrier)
            (Φ : ℝ → Diffeomorph annulusCircleCarrier.{u}.model annulusCircleCarrier.{u}.model
              annulusCircleCarrier.{u}.Carrier annulusCircleCarrier.{u}.Carrier ∞),
            IsCompact K' ∧ (∀ x, Φ 0 x = x) ∧ (∀ t x, x ∉ K' → Φ t x = x) ∧
            Φ 1 '' {x | P.level b x ≤ 40} =
              P.cuspCore_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K ∧
            Φ 1 '' {x | P.level b x = 40} =
              P.cuspFront_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K := by
  obtain ⟨a, ha, A, hA, P, hc⟩ := exists_doubleCuspBoundaryExport.{u} K hK (1 / 6408) (1 / 1000)
    (by norm_num) le_rfl (by norm_num) le_rfl
  refine ⟨a, ha, A, hA, P, hc, fun b => ?_⟩
  obtain ⟨K', Φ, hK', -, -, h0, hoff, -, hcore, hfront⟩ :=
    P.toBoundaryCollarPacket.original_cuspCore_relative_flow_BCG6K le_rfl b
  exact ⟨K', Φ, hK', h0, hoff, hcore, hfront⟩

end DifferentialGeometry.Geometry.Collapse
