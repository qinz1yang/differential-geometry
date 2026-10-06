import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySublevelPieces
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySublevelPiecesApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCertificateParts

/-!
# Draft 74, package S2 (loops), part 1: the piece of a clopen connected region of the interior

Lane S-JUNCTIONS (suffix `_JN74`, group G4b). The loop components of the slim cut are the open
compact (hence clopen) connected sets `O_j = f₃⁻¹(range loop_j)` of the interior of `W` (S-ZSP04
G18 / G19). A clopen `O` is the sublevel `{f ≤ 0}` of the locally constant function
`f = -1` on `O`, `+1` off `O`, which is smooth with no zero; the tree's `carrierSublevelPiece`
(`AssemblySublevelPieces.lean`) of the component of a point of `O` is then a `PieceEmbedding` with
image exactly `O` when `O` is connected, and empty model boundary when `O ⊆ int W`.

* `clopenFn74 O`, `clopenFn74_smooth`;
* `clopenPiece74 O hO hint x₀ hx₀ : PieceEmbedding W`, `range_clopenPiece74` (`= O`),
  `clopenPiece74_boundary_empty` (`∂ = ∅`), `clopenPiece74_localDiffeo` (the piece map is a local
  diffeomorphism at every point);
* `contMDiff_of_comp_localDiffeo74`: a continuous map into a piece whose composite with the piece
  map is smooth is smooth (the piece map is a local diffeomorphism).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

variable {W : CompactCarrier.{0}} (O : Set W.Carrier)

open Classical in
/-- The locally constant function `-1` on `O`, `+1` off `O`. -/
def clopenFn74 (x : W.Carrier) : ℝ :=
  if x ∈ O then -1 else 1

theorem clopenFn74_of_mem {x : W.Carrier} (hx : x ∈ O) : clopenFn74 O x = -1 :=
  by simp [clopenFn74, hx]

theorem clopenFn74_of_not_mem {x : W.Carrier} (hx : x ∉ O) : clopenFn74 O x = 1 :=
  by simp [clopenFn74, hx]

theorem clopenFn74_le_zero_iff {O : Set W.Carrier} {x : W.Carrier} :
    clopenFn74 O x ≤ 0 ↔ x ∈ O := by
  by_cases hx : x ∈ O
  · rw [clopenFn74_of_mem O hx]
    exact iff_of_true (by norm_num) hx
  · rw [clopenFn74_of_not_mem O hx]
    exact iff_of_false (by norm_num) hx

variable {O}

theorem clopenFn74_smooth (hO : IsClopen O) : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (clopenFn74 O) := by
  intro x
  by_cases hx : x ∈ O
  · refine (contMDiffAt_const (c := (-1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hO.isOpen.mem_nhds hx] with y hy
    exact clopenFn74_of_mem O hy
  · refine (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hO.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact clopenFn74_of_not_mem O hy

theorem clopenFn74_ne_zero (x : W.Carrier) : clopenFn74 O x ≠ 0 := by
  by_cases hx : x ∈ O
  · rw [clopenFn74_of_mem O hx]
    norm_num
  · rw [clopenFn74_of_not_mem O hx]
    norm_num

theorem clopenFn74_reg (x : W.Carrier) (hx : clopenFn74 O x = 0) :
    mfderiv W.model 𝓘(ℝ, ℝ) (clopenFn74 O) x ≠ 0 :=
  (clopenFn74_ne_zero x hx).elim

theorem clopenFn74_int (x : W.Carrier) (hx : clopenFn74 O x = 0) : x ∈ W.interior :=
  (clopenFn74_ne_zero x hx).elim

/-- The component index of a point of the clopen region. -/
def clopenIdx74 {x₀ : W.Carrier} (hx₀ : x₀ ∈ O) :
    ConnectedComponents {x : W.Carrier // clopenFn74 O x ≤ 0} :=
  ConnectedComponents.mk ⟨x₀, (clopenFn74_le_zero_iff).2 hx₀⟩

/-- **The piece of a clopen region**: the piece of the component of `x₀` of the sublevel
`{clopenFn74 O ≤ 0} = O`. -/
def clopenPiece74 (hO : IsClopen O) {x₀ : W.Carrier} (hx₀ : x₀ ∈ O) : PieceEmbedding W :=
  carrierSublevelPiece W (clopenFn74 O) 0 (clopenFn74_smooth hO) clopenFn74_reg clopenFn74_int
    (clopenIdx74 hx₀)

/-- The piece of a CONNECTED clopen region has image exactly `O`. -/
theorem range_clopenPiece74 (hO : IsClopen O) (hc : IsPreconnected O) {x₀ : W.Carrier}
    (hx₀ : x₀ ∈ O) : range (clopenPiece74 hO hx₀).map = O := by
  rw [clopenPiece74, range_carrierSublevelPiece]
  have hmem : x₀ ∈ {x : W.Carrier | clopenFn74 O x ≤ 0} := (clopenFn74_le_zero_iff).2 hx₀
  have h1 := connectedComponentIn_eq_image hmem
  have h2 : connectedComponentIn {x : W.Carrier | clopenFn74 O x ≤ 0} x₀ = O := by
    have hset : {x : W.Carrier | clopenFn74 O x ≤ 0} = O :=
      Set.ext fun x => clopenFn74_le_zero_iff
    have key : ∀ S : Set W.Carrier, S = O → x₀ ∈ S → connectedComponentIn S x₀ = O := by
      rintro S rfl hxS
      exact hc.connectedComponentIn hxS
    exact key _ hset hmem
  have h3 : ConnectedComponents.mk ⁻¹' {clopenIdx74 hx₀} =
      connectedComponent (⟨x₀, hmem⟩ : {x : W.Carrier // clopenFn74 O x ≤ 0}) :=
    connectedComponents_preimage_singleton
  rw [h3]
  exact h1.symm.trans h2

theorem map_mem_clopenPiece74 (hO : IsClopen O) {x₀ : W.Carrier} (hx₀ : x₀ ∈ O)
    (q : (clopenPiece74 hO hx₀).Piece) : (clopenPiece74 hO hx₀).map q ∈ O :=
  (clopenFn74_le_zero_iff).1 q.1.2

/-- The map of the piece of a clopen region is a local diffeomorphism at every point. -/
theorem clopenPiece74_localDiffeo (hO : IsClopen O) {x₀ : W.Carrier} (hx₀ : x₀ ∈ O)
    (q : (clopenPiece74 hO hx₀).Piece) :
    IsLocalDiffeomorphAt (𝓡∂ 3) W.model ∞ (clopenPiece74 hO hx₀).map q :=
  carrierSublevelPiece_isLocalDiffeomorphAt W (clopenFn74 O) 0 (clopenFn74_smooth hO)
    clopenFn74_reg clopenFn74_int (clopenIdx74 hx₀) q (by
      have h := clopenFn74_of_mem O (map_mem_clopenPiece74 hO hx₀ q)
      change clopenFn74 O ((clopenPiece74 hO hx₀).map q) < 0
      rw [h]
      norm_num)

/-- A piece of a clopen region inside the interior has empty model boundary. -/
theorem clopenPiece74_boundary_empty (hO : IsClopen O) (hint : O ⊆ W.interior)
    {x₀ : W.Carrier} (hx₀ : x₀ ∈ O) :
    (𝓡∂ 3).boundary (clopenPiece74 hO hx₀).Piece = ∅ := by
  refine eq_empty_of_forall_notMem fun q hq => ?_
  rcases (carrierSublevelPiece_isBoundaryPoint_iff (i := clopenIdx74 hx₀)).1 hq with hb | hz
  · exact ((W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp
      (hint (map_mem_clopenPiece74 hO hx₀ q))) hb
  · exact clopenFn74_ne_zero _ hz

/-- A continuous map into a piece whose composite with the piece map is smooth is smooth, when
the piece map is a local diffeomorphism at every point. -/
theorem contMDiff_of_comp_localDiffeo74 {E' H' N : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] (P : PieceEmbedding W) {g : N → P.Piece} (hg : Continuous g)
    (hP : ∀ q, IsLocalDiffeomorphAt (𝓡∂ 3) W.model ∞ P.map q)
    (hgs : ContMDiff J W.model ∞ (P.map ∘ g)) : ContMDiff J (𝓡∂ 3) ∞ g := by
  intro z
  have hl := hP (g z)
  have h1 : ContMDiffAt J (𝓡∂ 3) ∞ (hl.localInverse ∘ (P.map ∘ g)) z :=
    ContMDiffAt.comp z (hl.contMDiffAt_localInverse) (hgs z)
  refine h1.congr_of_eventuallyEq ?_
  have h2 := hl.localInverse_eventuallyEq_left
  filter_upwards [hg.continuousAt.eventually h2] with y hy
  exact hy.symm

end GC.GraphManifold.Assembly
