import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SelectedSmoothCore74

/-!
# Draft 74, D74-7 / D74-8 / package Z2: `ZeroDomains` from the actual zero exits (abstract kernel)

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G28 (kernel). The closed-route zero row assembled from the
three exits of the zero stratum on the original source `X` (model `𝓡 3`), carried to the member
`W` by the ONE identification `e` (`M.ψ`), draft 74 §3.1:

* Z1 (G27): the selected solid cores `Q i : SelectedSmoothCore74 (A i)` with ZSP02's ambient
  diffeomorphisms `Ψ i`, `Ψ i (A i) = Z i` (`piece`, `model`, `range_eq`, `boundary_eq`);
* Z0 (C14-ZSP35 G9): the global ratio-compatible definer `F i` with open buffer `N i`
  (`ratio = F i ∘ e⁻¹`, `ratio_smooth`, `ratio_regular`, `near = e (N i)`, `zero_subset_near`):
  `{F i ≤ 0} = Z i`, `{F i = 0} = frontier (Z i)`; the exact normalization on the buffer
  (`F i = u/v − 2/5`, not `rfl`) is a provenance fact of Z0 and stays with its binding;
* ZSP02: pairwise disjointness of the `Z i`.

`zeroDomainsOfExits74` is the assembler (finite family indexed by a `Fintype`, reindexed by
`Fintype.equivFin`); `…_range`, `…_ratio`, `…_near`, `…_model`, `…_boundary`, `…_union` read the
fields back. The closed-chain binding is `Gaf02ChainE.zeroDomains_of_actual_zero_exit74`
(`Collapse/StaticRegisterV4ChainZeroDomains74.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u v

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Regular

variable {X : Type v} [TopologicalSpace X] [ChartedSpace E3 X]
  {EN' HN' : Type*} [NormedAddCommGroup EN'] [NormedSpace ℝ EN'] [TopologicalSpace HN']
  {I' : ModelWithCorners ℝ EN' HN'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace HN' N']

/-- A pulled-back function along a diffeomorphism from `X` is regular where the original is. -/
theorem mfderiv_comp_symm_ne_zero_gen_R74 (e : X ≃ₘ⟮𝓡 3, I'⟯ N') {f : X → ℝ}
    (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f) {y : N'}
    (hy : mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f (e.symm y) ≠ 0) :
    mfderiv I' 𝓘(ℝ, ℝ) (f ∘ e.symm) y ≠ 0 := by
  have hd : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) f (e.symm y) := hf.mdifferentiableAt (by simp)
  have he : MDifferentiableAt I' (𝓡 3) e.symm y := e.symm.mdifferentiable (by simp) _
  rw [mfderiv_comp y hd he]
  intro h0
  apply hy
  ext v
  obtain ⟨u, rfl⟩ := (mfderiv_diffeo_bijective_R74 e.symm y).2 v
  exact congrArg (fun L => L u) h0

end Regular

namespace SelectedSmoothCore74

variable {X : Type v} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold (𝓡 3) ∞ X]
  [T2Space X] {A : Set X} {W : CompactCarrier.{u}}

omit [T2Space X] in
/-- The row piece of a selected core has range `e (Ψ A)`. -/
theorem range_piece_R74 (Q : SelectedSmoothCore74.{u, v} A) (Ψ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X)
    (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) :
    range (Q.piece Ψ e).map = e '' (Ψ '' A) :=
  Q.solid.range_toPiece Ψ e

/-- The model boundary image of the row piece of a selected core is `e` of the frontier of
`Ψ A`. -/
theorem pieceBoundary_piece_R74 (Q : SelectedSmoothCore74.{u, v} A) (Ψ : X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X)
    (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) :
    FC39P0.pieceBoundary (Q.piece Ψ e) = e '' frontier (Ψ '' A) :=
  Q.solid.pieceBoundary_toPiece_frontier Ψ e

end SelectedSmoothCore74

/-- The index equivalence `Fin (card ι) ≃ ι` of a finite family. -/
def idx74 (ι : Type) [Fintype ι] : Fin (Fintype.card ι) ≃ ι :=
  (Fintype.equivFin ι).symm

namespace FC39P0

variable {X : Type v} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold (𝓡 3) ∞ X]
  [T2Space X]

/-- **Z2 assembler** (draft 74 §3.1): the closed-route `ZeroDomains W` of a finite family of
selected solid cores `Q i` with ZSP02's ambient diffeomorphisms `Ψ i` (`Ψ i (A i) = Z i`,
disjoint), Z0's definers `F i` (`{F i ≤ 0} = Z i`, `{F i = 0} = frontier (Z i)`, smooth, regular
on the zero level, buffer `N i` open ⊇ zero level), carried to `W` by `e`; the model is the
selected core's branch (`SelectedSmoothCore74.model`), the closed branch keeping the metric of the
selected model. `W` has empty boundary (the closed route: the `near` sets lie in `W.interior`). -/
def zeroDomainsOfExits74 {W : CompactCarrier.{u}} {ι : Type} [Fintype ι]
    (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) (hW : W.model.boundary W.Carrier = ∅)
    {A : ι → Set X} (Q : ∀ i, SelectedSmoothCore74.{u, v} (A i))
    (Ψ : ι → X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X) (Z N : ι → Set X) (F : ι → X → ℝ)
    (hΨ : ∀ i, Ψ i '' A i = Z i) (hdisj : ∀ i j, i ≠ j → Disjoint (Z i) (Z j))
    (hN : ∀ i, IsOpen (N i)) (hFs : ∀ i, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (F i))
    (hFr : ∀ i x, F i x = 0 → mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (F i) x ≠ 0)
    (hle : ∀ i, {x | F i x ≤ 0} = Z i) (hfr : ∀ i, {x | F i x = 0} = frontier (Z i))
    (hzn : ∀ i, {x | F i x = 0} ⊆ N i) : ZeroDomains W where
  count := Fintype.card ι
  piece j := (Q (idx74 ι j)).piece (Ψ (idx74 ι j)) e
  disjoint j j' hjj' := by
    beta_reduce
    rw [(Q (idx74 ι j)).range_piece_R74 (Ψ (idx74 ι j)) e,
      (Q (idx74 ι j')).range_piece_R74 (Ψ (idx74 ι j')) e, hΨ, hΨ]
    exact (disjoint_image_iff e.injective).mpr
      (hdisj _ _ fun h => hjj' ((idx74 ι).injective h))
  ratio j := F (idx74 ι j) ∘ e.symm
  near j := ⟨e '' N (idx74 ι j), e.toHomeomorph.isOpenMap _ (hN _)⟩
  near_interior j y _ := by
    have : BoundarylessManifold W.model W.Carrier :=
      ModelWithCorners.Boundaryless.of_boundary_eq_empty hW
    exact BoundarylessManifold.isInteriorPoint
  ratio_smooth j := (hFs _).comp e.symm.contMDiff
  ratio_regular j y hy :=
    mfderiv_comp_symm_ne_zero_gen_R74 e (hFs _) (hFr _ _ hy)
  zero_subset_near j y hy := ⟨e.symm y, hzn _ hy, e.apply_symm_apply y⟩
  boundary_eq j := by
    refine ((Q (idx74 ι j)).pieceBoundary_piece_R74 (Ψ (idx74 ι j)) e).trans ?_
    rw [hΨ, ← hfr]
    exact (preimage_symm_R74 e (F (idx74 ι j)) {0}).symm
  range_eq j := by
    refine ((Q (idx74 ι j)).range_piece_R74 (Ψ (idx74 ι j)) e).trans ?_
    rw [hΨ, ← hle]
    exact (preimage_symm_R74 e (F (idx74 ι j)) (Iic 0)).symm
  model j := (Q (idx74 ι j)).model (Ψ (idx74 ι j)) e

section Readback

variable {W : CompactCarrier.{u}} {ι : Type} [Fintype ι]
  (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) (hW : W.model.boundary W.Carrier = ∅)
  {A : ι → Set X} (Q : ∀ i, SelectedSmoothCore74.{u, v} (A i))
  (Ψ : ι → X ≃ₘ⟮𝓡 3, 𝓡 3⟯ X) (Z N : ι → Set X) (F : ι → X → ℝ)
  (hΨ : ∀ i, Ψ i '' A i = Z i) (hdisj : ∀ i j, i ≠ j → Disjoint (Z i) (Z j))
  (hN : ∀ i, IsOpen (N i)) (hFs : ∀ i, ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (F i))
  (hFr : ∀ i x, F i x = 0 → mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (F i) x ≠ 0)
  (hle : ∀ i, {x | F i x ≤ 0} = Z i) (hfr : ∀ i, {x | F i x = 0} = frontier (Z i))
  (hzn : ∀ i, {x | F i x = 0} ⊆ N i)

/-- The assembled pieces have the transported ranges `e (Z i)`. -/
theorem zeroDomainsOfExits74_range (j : Fin (Fintype.card ι)) :
    range ((zeroDomainsOfExits74 e hW Q Ψ Z N F hΨ hdisj hN hFs hFr hle hfr hzn).piece j).map =
      e '' Z (idx74 ι j) :=
  ((Q (idx74 ι j)).range_piece_R74 (Ψ (idx74 ι j)) e).trans (by rw [hΨ])

/-- The assembled ratio is Z0's definer pulled back by `e⁻¹`. -/
theorem zeroDomainsOfExits74_ratio (j : Fin (Fintype.card ι)) :
    (zeroDomainsOfExits74 e hW Q Ψ Z N F hΨ hdisj hN hFs hFr hle hfr hzn).ratio j =
      F (idx74 ι j) ∘ e.symm :=
  rfl

/-- The assembled buffer is the image `e (N i)`. -/
theorem zeroDomainsOfExits74_near (j : Fin (Fintype.card ι)) :
    ((zeroDomainsOfExits74 e hW Q Ψ Z N F hΨ hdisj hN hFs hFr hle hfr hzn).near j :
      Set W.Carrier) = e '' N (idx74 ι j) :=
  rfl

/-- The assembled model is the selected core's model (same branch). -/
theorem zeroDomainsOfExits74_model (j : Fin (Fintype.card ι)) :
    (zeroDomainsOfExits74 e hW Q Ψ Z N F hΨ hdisj hN hFs hFr hle hfr hzn).model j =
      (Q (idx74 ι j)).model (Ψ (idx74 ι j)) e :=
  rfl

/-- The union of the assembled pieces is `e (⋃ Z i)`. -/
theorem zeroDomainsOfExits74_union :
    ⋃ j, range
        ((zeroDomainsOfExits74 e hW Q Ψ Z N F hΨ hdisj hN hFs hFr hle hfr hzn).piece j).map =
      e '' ⋃ i, Z i := by
  rw [image_iUnion]
  exact (iUnion_congr
    (zeroDomainsOfExits74_range e hW Q Ψ Z N F hΨ hdisj hN hFs hFr hle hfr hzn)).trans
    (Equiv.iSup_comp (g := fun i => e '' Z i) (idx74 ι))

end Readback

end FC39P0

end GC.GraphManifold.Assembly
