import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollarAlternative

/-!
# FC43, the nearly cuspidal boundary block, in its E-free form

Blueprint `master207B.tex`, FC43 (`found:fibration-boundary-assembly`, B:7549–7575): on LC88's
KL16.1 input (the SAME metric), "the smoothed inward collar coordinate has support between levels
`20, 90` and plateau between `30, 80`. Its block is `(η_iζ_i, ζ_i)`, with physical collar units,
not a local `ρ(p_i)` factor."

`fc43_collar_block_FCF` states these clauses, in LEVELS of the smoothed collar coordinate `η_i`
(`P.height i`, physical depth), for the collar blocks `P.block i` of a `BoundaryExportPacket` — the
export packet `P` (with `P.cusp = B n`, the same metric `g n`) that T3B on the final boundary family
(`lc88_boundary_packets_BFRZ_BFZD`) outputs together with its `LocalPacketsOnBFRZ`:

* the block is smooth on the whole carrier and is `(η_i ζ_i, ζ_i)` everywhere (first component
  `= η_i ·` second; extended by zero off the collar band);
* on the collar band `2 < z < 98` the cutoff is the profile of the collar coordinate,
  `ζ_i = χ_∂(η_i)`; it takes values in `[0, 1]`;
* support between levels `20, 90`: the block is nonzero only where `20 < η_i < 90`;
* plateau between levels `30, 80`: on the collar band, `30 ≤ η_i ≤ 80` forces `ζ_i = 1`;
* the closed support lies in the collar between depths `20 − ε` and `90 + ε`.

The exceptional whole carrier `I × T²` of FC43 ("handle it first") is the export packet's field
`P.alternative` (KL 16.5). Not in this file: adjoining the block to EVERY `Q_j` (the boundary
augmented map, lane BAUG-A), repeating the adjustments with the block kept (BCG04) and the torus
collar core of the ADJUSTED map (BCG06) — all on the boundary chain object.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}}
  {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- The collar block is `(η_i ζ_i, ζ_i)` at every point of the carrier (zero off the band). -/
theorem BoundaryCollarPacket.block_fst_eq_FCF (P : BoundaryCollarPacket W g K A w₀ ε)
    (i : Fin P.cusp.count) (x : W.Carrier) :
    (P.block i x).1 = P.height i x * (P.block i x).2 := by
  by_cases hx : x ∈ (P.cusp.collar i).toFun '' {p : CuspHalfSpace | 2 < p.2.val 0 ∧ p.2.val 0 < 98}
  · rw [BoundaryCollarPacket.block, indicator_of_mem hx, boundaryBlock_fst, boundaryBlock_snd]
  · rw [BoundaryCollarPacket.block, indicator_of_notMem hx]
    simp

/-- On the collar band the cutoff is the boundary profile of the collar coordinate. -/
theorem BoundaryCollarPacket.cutoff_eq_profile_FCF (P : BoundaryCollarPacket W g K A w₀ ε)
    (i : Fin P.cusp.count) {p : CuspHalfSpace} (h2 : 2 < p.2.val 0) (h98 : p.2.val 0 < 98) :
    P.cutoff i ((P.cusp.collar i).toFun p) =
      boundaryProfile (P.height i ((P.cusp.collar i).toFun p)) := by
  change (P.block i ((P.cusp.collar i).toFun p)).2 = _
  have hmem : (P.cusp.collar i).toFun p ∈
      (P.cusp.collar i).toFun '' {q : CuspHalfSpace | 2 < q.2.val 0 ∧ q.2.val 0 < 98} :=
    mem_image_of_mem _ (show 2 < p.2.val 0 ∧ p.2.val 0 < 98 from ⟨h2, h98⟩)
  rw [BoundaryCollarPacket.block, indicator_of_mem hmem, boundaryBlock_snd]

/-- **FC43, the boundary block** (E-free form) for the export packet of the final boundary family:
the block `(η_i ζ_i, ζ_i)` in physical collar units, smooth on the carrier, `ζ_i = χ_∂(η_i)` on the
collar band with values in `[0, 1]`, support between the levels `20, 90`, plateau between the
levels `30, 80`, closed support in the collar between depths `20 − ε` and `90 + ε`. -/
theorem fc43_collar_block_FCF [ConnectedSpace W.Carrier] (P : BoundaryExportPacket W g K A w₀ ε)
    (i : Fin P.cusp.count) :
    ContMDiff W.model 𝓘(ℝ, ℝ × ℝ) ∞ (P.block i) ∧
      (∀ x, (P.block i x).1 = P.height i x * (P.block i x).2 ∧ (P.block i x).2 = P.cutoff i x) ∧
      (∀ p : CuspHalfSpace, 2 < p.2.val 0 → p.2.val 0 < 98 →
        P.cutoff i ((P.cusp.collar i).toFun p) =
          boundaryProfile (P.height i ((P.cusp.collar i).toFun p))) ∧
      (∀ x, P.cutoff i x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, P.block i x ≠ 0 → 20 < P.height i x ∧ P.height i x < 90) ∧
      (∀ p : CuspHalfSpace, 2 < p.2.val 0 → p.2.val 0 < 98 →
        P.height i ((P.cusp.collar i).toFun p) ∈ Icc (30 : ℝ) 80 →
          P.cutoff i ((P.cusp.collar i).toFun p) = 1) ∧
      tsupport (P.block i) ⊆
        (P.cusp.collar i).toFun '' {p : CuspHalfSpace | 20 - ε ≤ p.2.val 0 ∧ p.2.val 0 ≤ 90 + ε} :=
  ⟨P.contMDiff_block i, fun x => ⟨P.block_fst_eq_FCF i x, rfl⟩,
    fun _ h2 h98 => P.cutoff_eq_profile_FCF i h2 h98, P.cutoff_mem_Icc i,
    fun _ hx => P.height_mem_of_block_ne_zero i hx,
    fun _ h2 h98 hη => by rw [P.cutoff_eq_profile_FCF i h2 h98]; exact boundaryProfile_eq_one hη,
    P.tsupport_block_subset i⟩

end DifferentialGeometry.Geometry.Collapse
