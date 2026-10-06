import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Junctions

/-!
# D74-5 (draft 74 §2.1): the link table, plain-data form

Lane S-LANDING (`_LND74`), G1 kernel. The frozen link specification `ClosedRowsLinkAt74` (and the
boundary `BoundaryRowsLink`) is an equality table between the rows `Rw : FC39RowsV2 W E` and the
ACTUAL objects of the chain, carried to `W` by ONE identification `ψ : X ≃ W.Carrier` (the closed
route: `M.ψ`). The five tables below are stated on PLAIN data (sets, functions, index types of the
actual side), so that

* the closed binding (`StaticRegisterV4ChainRowsLink74`) instantiates them on the actual chain,
  height, cut choice, and
* each table has a compiled inhabitant (`RowsLinkKernel74Applications`: the `S³` and
  `S² × S¹` singleton rows).

Tables (every function is PULLED BACK along `ψ.symm`, every set is PUSHED FORWARD along `ψ`):

* `ZeroLink_LND74`: `zeroEquiv` an EQUIVALENCE of indices (every actual zero domain is listed,
  D74-5), the piece range `= ψ '' Z_k`, the model boundary `= ψ '' frontier Z_k`, the two (ZB)
  inclusions through `ψ`, the buffer equality `ratio = u/v − 2/5` on `near`, and the global ratio
  `ratio = F ∘ ψ.symm` for an `F` equal to `u/v − 2/5` on an open set around the whole face;
* `SlimLink_LND74`: an equivalence with the actual components, each piece the `ψ`-image of the
  WHOLE `f₃`-preimage, the union the `ψ`-image of the slim set;
* `EdgeLink_LND74` / `CircleLink_LND74`: a topological embedding of the rows' base onto the open
  base neighbourhood, the final projection `q_j`, the height, the level, the compact base, WHOLE
  disks / rims / fibres, the piece;
* `RegionsLink_LND74`: `M₁ / M₂ / M₃` of the rows are the `ψ`-images of the actual regions.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u v w

namespace GC.GraphManifold.Assembly.FC39P0

variable {X : Type v} [TopologicalSpace X] {W : CompactCarrier.{u}}

/-- **Zero table.** `dom k` is the actual zero domain `Z_k`; `inner k`, `outer k` the (ZB) balls
(`B̄(c_k, .38R_k)`, `B(c_k, .42R_k)`); `uv k` the function `u_k(E)/v_k(E) − 2/5` on `X`. -/
def ZeroLink_LND74 (ψ : X ≃ W.Carrier) (Zr : ZeroDomains W) {ι : Type w}
    (dom inner outer : ι → Set X) (uv : ι → X → ℝ) : Prop :=
  ∃ σ : Fin Zr.count ≃ ι, ∀ i,
    range (Zr.piece i).map = ψ '' dom (σ i) ∧
    pieceBoundary (Zr.piece i) = ψ '' frontier (dom (σ i)) ∧
    ψ '' inner (σ i) ⊆ interior (range (Zr.piece i).map) ∧
    range (Zr.piece i).map ⊆ ψ '' outer (σ i) ∧
    (∀ x ∈ (Zr.near i : Set W.Carrier), Zr.ratio i x = uv (σ i) (ψ.symm x)) ∧
    ∃ (F : X → ℝ) (N : Set X), IsOpen N ∧ frontier (dom (σ i)) ⊆ N ∧
      (∀ z ∈ N, F z = uv (σ i) z) ∧ ∀ x, Zr.ratio i x = F (ψ.symm x)

/-- **Slim table.** `comp c` is the WHOLE `f₃`-preimage of the base component `c`, `slimSet` the
`f₃`-preimage of the compact one-domain. -/
def SlimLink_LND74 {n : ℕ} {E : BoundaryTori W n} {Z : ZeroDomains W} {C : CuspCores W E}
    (ψ : X ≃ W.Carrier) (Sl : SlimPiecesV2 W Z C) {κ : Type w} (comp : κ → Set X)
    (slimSet : Set X) : Prop :=
  Sl.union = ψ '' slimSet ∧
    ∃ σ : Fin Sl.count ≃ κ, ∀ j, range (Sl.piece j).map = ψ '' comp (σ j)

/-- **Edge table.** `q` is the FINAL stage projection `q₁ = π₁ ∘ E`, `Hs` the height `A/s`,
`lvl` the level `4Δ`, `baseOpen` the open good base neighbourhood, `cb` the compact base `C₂`,
`src` its whole `q`-preimage, `edgeSet` the edge piece. -/
def EdgeLink_LND74 {B : Type w} [TopologicalSpace B] (ψ : X ≃ W.Carrier) (P : EdgeBundle W)
    (q : X → B) (Hs : X → ℝ) (lvl : ℝ) (baseOpen cb : Set B) (src edgeSet : Set X) : Prop :=
  ∃ ι : P.Base → B, Topology.IsEmbedding ι ∧ range ι = baseOpen ∧ ι '' P.cbase = cb ∧
    (P.source : Set W.Carrier) = ψ '' src ∧
    (∀ x : P.source, ι (P.proj x) = q (ψ.symm x) ∧ P.height x = Hs (ψ.symm x)) ∧
    P.level = lvl ∧
    (∀ c, P.disk c = ψ '' {p | q p = ι c ∧ Hs p ≤ lvl}) ∧
    (∀ c, P.rim c = ψ '' {p | q p = ι c ∧ Hs p = lvl}) ∧
    P.edgePiece = ψ '' edgeSet

/-- **Circle table.** `q` is the FINAL stage projection `q₀ = π₀ ∘ E`, `baseOpen` the open good
base neighbourhood, `cb` the compact base `C₁`, `dom` its whole `q`-preimage, `reg` the region
`M₃`. -/
def CircleLink_LND74 {B : Type w} [TopologicalSpace B] (ψ : X ≃ W.Carrier) (R : CircleBundle W)
    (q : X → B) (baseOpen cb : Set B) (dom reg : Set X) : Prop :=
  ∃ ι : R.Base → B, Topology.IsEmbedding ι ∧ range ι = baseOpen ∧ ι '' R.cbase = cb ∧
    (R.domain : Set W.Carrier) = ψ '' dom ∧
    (∀ x : R.domain, ι (R.proj x) = q (ψ.symm x)) ∧
    (∀ c, R.fibre c = ψ '' (q ⁻¹' {ι c})) ∧
    R.region = ψ '' reg

/-- **Regions table.** `M₁ / M₂ / M₃` of the rows are the `ψ`-images of the actual regions. -/
def RegionsLink_LND74 {n : ℕ} {E : BoundaryTori W n} (ψ : X ≃ W.Carrier) (Rw : FC39RowsV2 W E)
    (M₁ M₂ M₃ : Set X) : Prop :=
  regionM1 Rw.zero Rw.cusp = ψ '' M₁ ∧ regionM2 Rw.slim = ψ '' M₂ ∧
    regionM3 Rw.slim Rw.edge = ψ '' M₃

end GC.GraphManifold.Assembly.FC39P0
