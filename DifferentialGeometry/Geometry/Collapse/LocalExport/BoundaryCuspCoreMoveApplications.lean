import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreMove
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreApplications

/-!
# BCG06, G4b: the spec with the relative move, and its consumers (lane BCG6-K)

* `BoundaryCuspCoreSpecM_BCG6K` extends `BoundaryCuspCoreSpec_BCG6K` by the relative supported
  move of every core (review 65 M3): an ambient diffeomorphism of `W°` (interior atlas), the
  identity off a compact set inside `band ∩ {38 < η_b < 42}`, carrying `{level_b ≤ 40}` onto `C_b`
  and `{level_b = 40}` onto `H_b`; `boundaryCuspCoreSpecM_BCG6K` proves it under the kernel premises.
* Consumers: `original_cuspCore_relative_move_BCG6K` (every collar packet with `ε ≤ 1/1000`, the
  original map `E = F_∂` with positive tolerances) and `doubleCusp_cuspCore_relative_move_BCG6K`
  (both ends of the double cusp `T² × [0, 240]`).
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

/-- **BCG06 output with the relative supported move** (separated branch, review 65 M3). -/
structure BoundaryCuspCoreSpecM_BCG6K (P : BoundaryCollarPacket W g K A w₀ ε)
    (u v : Fin P.cusp.count → W.Carrier → ℝ) {ζ : Type*} (Zb : ζ → Set W.Carrier) : Prop
    extends BoundaryCuspCoreSpec_BCG6K P u v Zb where
  relative_move : ∀ b,
    letI := interiorCharted_BDRY1 W
    ∃ (K' : Set (W.pieceInterior ⊤))
      (Φ : Diffeomorph (𝓡 3) (𝓡 3) (W.pieceInterior ⊤) (W.pieceInterior ⊤) ∞),
      IsCompact K' ∧
      (∀ x ∈ K', (x : W.Carrier) ∈ P.collarBand_BAUGA b ∧ 38 < P.height b x ∧
        P.height b x < 42) ∧
      (∀ x, x ∉ K' → Φ x = x) ∧
      (fun x => (Φ x : W.Carrier)) '' {x : W.pieceInterior ⊤ | P.level b x ≤ 40} =
        P.cuspCore_BCG6K b u v ∩
          ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier) ∧
      (fun x => (Φ x : W.Carrier)) '' {x : W.pieceInterior ⊤ | P.level b x = 40} =
        P.cuspFront_BCG6K b u v

/-- **BCG06 (kernel, separated branch) with the relative move.** -/
theorem boundaryCuspCoreSpecM_BCG6K (P : BoundaryCollarPacket W g K A w₀ ε) (hε : ε ≤ 1 / 1000)
    {u v : Fin P.cusp.count → W.Carrier → ℝ} (hu : ∀ b, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u b))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃0 : 0 ≤ c₃) (hc₃ : c₃ < 1 / 100000)
    (hBI : ∀ b x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ b, ∀ x ∈ P.safeBand_BAUGA b, v b x = 1)
    (hBD : ∀ b, ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u b y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w))
    (hsep : ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    {ζ : Type*} (Zb : ζ → Set W.Carrier)
    (hZ : ∀ j (i : Fin P.cusp.count),
      Disjoint (Zb j) ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) :
    BoundaryCuspCoreSpecM_BCG6K P u v Zb :=
  { toBoundaryCuspCoreSpec_BCG6K :=
      boundaryCuspCoreSpec_BCG6K P hε hu hεd hc₃0 hc₃ hBI hBFM hBD hsep Zb hZ
    relative_move := fun b =>
      cuspCore_relative_move_BCG6K hε (hu b) hεd hc₃0 (register_R_BCG6K hεd hc₃) (hBI b)
        (hBFM b) (hBD b) }

/-- **Consumer: the relative move of the original core** for every collar packet with
`ε ≤ 1/1000` and every component (`E = F_∂`, `ε∂ = 10⁻⁷`, `c₃ = 10⁻⁶`). -/
theorem original_cuspCore_relative_move_BCG6K (P : BoundaryCollarPacket W g K A w₀ ε)
    (hε : ε ≤ 1 / 1000) (b : Fin P.cusp.count) :
    letI := interiorCharted_BDRY1 W
    ∃ (K' : Set (W.pieceInterior ⊤))
      (Φ : Diffeomorph (𝓡 3) (𝓡 3) (W.pieceInterior ⊤) (W.pieceInterior ⊤) ∞),
      IsCompact K' ∧
      (∀ x ∈ K', (x : W.Carrier) ∈ P.collarBand_BAUGA b ∧ 38 < P.height b x ∧
        P.height b x < 42) ∧
      (∀ x, x ∉ K' → Φ x = x) ∧
      (fun x => (Φ x : W.Carrier)) '' {x : W.pieceInterior ⊤ | P.level b x ≤ 40} =
        P.cuspCore_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K ∩
          ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier) ∧
      (fun x => (Φ x : W.Carrier)) '' {x : W.pieceInterior ⊤ | P.level b x = 40} =
        P.cuspFront_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K :=
  cuspCore_relative_move_BCG6K hε (P.contMDiff_originalBoundaryU_BCG6K b)
    (εd := 1 / 10000000) (c₃ := 1 / 1000000) (by norm_num) (by norm_num) (by norm_num)
    (P.original_BI_BCG6K (by norm_num) b) (P.original_BFM_BCG6K b)
    (P.original_BD_BCG6K (by norm_num) b)

end BoundaryCollarPacket

/-- The double cusp carrier is connected (as in `SmallBoundaryPackets`). -/
local instance connectedSpace_annulusCircleCarrier_move_BCG6K :
    ConnectedSpace annulusCircleCarrier.{u}.Carrier :=
  connectedSpace_productSet (Or.inl rfl)

/-- **Consumer on the double cusp `T² × [0, 240]`**: both ends of the two-ended double cusp carry
the relative supported move of the original core. -/
theorem doubleCusp_cuspCore_relative_move_BCG6K (K : ℕ) (hK : 2 ≤ K) :
    ∃ a : ℝ, ∃ ha : 0 < a, ∃ A : ℝ → ℝ, (∀ w, 0 < A w) ∧
      ∃ P : BoundaryExportPacket annulusCircleCarrier.{u} (doubleCuspMetric.{u} a ha) K A
          (1 / 6408) (1 / 1000),
        P.cusp.count = 2 ∧ ∀ b,
          letI := interiorCharted_BDRY1 annulusCircleCarrier.{u}
          ∃ (K' : Set (annulusCircleCarrier.{u}.pieceInterior ⊤))
            (Φ : Diffeomorph (𝓡 3) (𝓡 3) (annulusCircleCarrier.{u}.pieceInterior ⊤)
              (annulusCircleCarrier.{u}.pieceInterior ⊤) ∞),
            IsCompact K' ∧ (∀ x, x ∉ K' → Φ x = x) ∧
            (fun x => (Φ x : annulusCircleCarrier.{u}.Carrier)) ''
                {x : annulusCircleCarrier.{u}.pieceInterior ⊤ | P.level b x = 40} =
              P.cuspFront_BCG6K b P.originalBoundaryU_BCG6K P.originalBoundaryV_BCG6K := by
  obtain ⟨a, ha, A, hA, P, hc⟩ := exists_doubleCuspBoundaryExport.{u} K hK (1 / 6408) (1 / 1000)
    (by norm_num) le_rfl (by norm_num) le_rfl
  refine ⟨a, ha, A, hA, P, hc, fun b => ?_⟩
  obtain ⟨K', Φ, hK', -, hid, -, hfront⟩ :=
    P.toBoundaryCollarPacket.original_cuspCore_relative_move_BCG6K le_rfl b
  exact ⟨K', Φ, hK', hid, hfront⟩

end DifferentialGeometry.Geometry.Collapse
