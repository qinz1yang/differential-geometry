import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryBoundary_S39
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryLiftProps_S34
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryMetricTransfer_S34
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryAssemble
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutMetricPullback_S25

/-!
# CH12-S39 G2a: `NearlyCuspidalBoundary` of a block of the real cut from collar data in `M`

For the cut presentation of a collared torus family `F` in `M`, a block `j` owning no left torus,
and for every `i` a collar `φ i : CuspHalfSpace → M.Carrier` (agreeing with `F.collar i` below height 1,
avoiding all closed slabs above, an embedding/immersion with `g`-error `≤ δ` against a cusp `H i` of
torus diameter `≤ D₀`): the block has a `NearlyCuspidalBoundary` of size `max δ (√(1+δ) D₀)` for the
induced cut metric.  Slice-specific producer facts are in the next group.
-/

set_option autoImplicit false

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry.Hyperbolic
  DifferentialGeometry.Geometry.Collapse GC.Endpoint GC.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem sideTorus_val_S39 {M : ConnectedClosedOrientedManifold.{u} 3}
    (F : CollaredTorusFamily_C2a M.Carrier) (i : Fin F.count) (t : Torus) :
    (sideTorus_C2a F i hR_C2a t).1 = F.collar i (t, 1 / 2) := by
  simp [sideTorus_C2a, sideParam_C2a]

section Lift

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)
  (j : Fin (cutPresentation_S12 M F).toTorusDecomposition.components.count)

/-- The lift of a collar `φ i` to the block `j` which owns the torus `σ_i(·, 1/2)`. -/
theorem exists_blockLift_S39 (i : Fin F.count) (φ : CuspHalfSpace → M.Carrier)
    (hcol : ∀ p : CuspHalfSpace, p.2.val 0 < 1 → φ p = F.collar i (p.1, p.2.val 0))
    (hout : ∀ p ∈ cuspDomain, 1 ≤ p.2.val 0 →
      ∀ k, φ p ∉ F.collar k '' (univ ×ˢ Icc (-7 / 8 : ℝ) (7 / 8)))
    (hsm : ContMDiffOn halfCollarModel (𝓡 3) ∞ φ cuspDomain)
    (hφe : _root_.Topology.IsEmbedding (fun p : cuspDomain => φ p))
    (hφi : ∀ p ∈ cuspDomain, Function.Injective (mfderiv halfCollarModel (𝓡 3) φ p))
    (hown : ∃ t, (sideTorus_C2a F i hR_C2a t :
        (cutPresentation_S12 M F).toTorusDecomposition.carrier.Carrier) ∈
      ((cutPresentation_S12 M F).toTorusDecomposition.components.piece j :
        Set (cutPresentation_S12 M F).toTorusDecomposition.carrier.Carrier)) :
    ∃ L' : CuspHalfSpace → ((cutPresentation_S12 M F).toTorusDecomposition.component j).Carrier,
      ContMDiffOn halfCollarModel
        ((cutPresentation_S12 M F).toTorusDecomposition.component j).model ∞ L' cuspDomain ∧
      (∀ p ∈ cuspDomain, cutPieceMap (cutPresentation_S12 M F).toTorusDecomposition j (L' p) = φ p) ∧
      (∀ t, (L' (t, halfZero)).val = sideTorus_C2a F i hR_C2a t) ∧
      _root_.Topology.IsEmbedding (fun p : cuspDomain => L' p) ∧
      (∀ p ∈ cuspDomain, Function.Injective (mfderiv halfCollarModel
        ((cutPresentation_S12 M F).toTorusDecomposition.component j).model L' p)) := by
  obtain ⟨L, hL, hb, hside, -⟩ := exists_rightLift_S34 F i φ hcol hout hsm
  obtain ⟨t₀, ht₀⟩ := hown
  have hzd (t : Torus) : ((t, halfZero) : CuspHalfSpace) ∈ cuspDomain := by
    change (0 : ℝ) < 100; norm_num
  have hq₀ := hzd t₀
  obtain ⟨L', hL'v, hL'⟩ := exists_pieceLift_S34
    (cutPresentation_S12 M F).toTorusDecomposition.components j L hL _ hq₀
    (by rw [hside]; exact ht₀)
  have hb' : ∀ p ∈ cuspDomain,
      cutPieceMap (cutPresentation_S12 M F).toTorusDecomposition j (L' p) = φ p := fun p hp => by
    rw [← hb p hp, ← hL'v p hp]; rfl
  refine ⟨L', hL', hb', fun t => ?_, ?_, ?_⟩
  · exact (hL'v _ (hzd t)).trans (hside t)
  · exact isEmbedding_lift_S34 (W₀ := NoCuts.carrier M)
      (cutPieceMap (cutPresentation_S12 M F).toTorusDecomposition j) L' φ
      (contMDiff_cutPieceMap _ j) hL' hb' hφe
  · exact immersion_lift_S34 (W₀ := NoCuts.carrier M)
      (cutPieceMap (cutPresentation_S12 M F).toTorusDecomposition j) L' φ
      (contMDiff_cutPieceMap _ j) hL' hb' hφi

end Lift

section Generic

/-- **Generic assembly over an index type.** Collars `L' i` with disjoint height-zero slices covering
`∂W` give a `NearlyCuspidalBoundary`. -/
theorem ncb_of_lifts_S39 {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
    {K : ℕ} {δ : ℝ} (D₀ : ℝ) (hD₀ : 0 ≤ D₀) {ι : Type} [Finite ι] [Nonempty ι]
    (H : ι → HyperbolicCusp) (L' : ι → CuspHalfSpace → W.Carrier)
    (hsm : ∀ i, ContMDiffOn halfCollarModel W.model ∞ (L' i) cuspDomain)
    (hemb : ∀ i, _root_.Topology.IsEmbedding (fun p : cuspDomain => L' i p))
    (himm : ∀ i, ∀ p ∈ cuspDomain, Function.Injective (mfderiv halfCollarModel W.model (L' i) p))
    (herr : ∀ i, cuspMetricErrorBound g K δ (H i) (L' i))
    (hdiam : ∀ i (x y : Torus), riemannianEDistOf (H i).torusMetric x y ≤ ENNReal.ofReal D₀)
    (hbd : ∀ i t, L' i (t, halfZero) ∈ W.model.boundary W.Carrier)
    (hdisj : ∀ i k, i ≠ k → ∀ t t', L' i (t, halfZero) ≠ L' k (t', halfZero))
    (hcover : ∀ x ∈ W.model.boundary W.Carrier, ∃ i t, x = L' i (t, halfZero)) :
    Nonempty (NearlyCuspidalBoundary W g K (max δ (Real.sqrt (1 + δ) * D₀))) := by
  classical
  have := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  refine ⟨NearlyCuspidalBoundary.ofCollars_C4 (Fintype.card ι) Fintype.card_pos
    (fun k => range (fun t : Torus => L' (e.symm k) (t, halfZero)))
    (fun k => CuspEmbedding.ofSlice_C4 (H (e.symm k)) (L' (e.symm k))
      ((hsm _).of_le (by exact_mod_cast le_top)) (hemb _) (himm _) rfl
      (by rintro _ ⟨t, rfl⟩; exact hbd _ t) (herr _))
    (fun a b hab => Set.disjoint_left.mpr (by
      rintro _ ⟨t, rfl⟩ ⟨t', ht'⟩
      exact hdisj _ _ (fun h => hab (e.symm.injective h)) t t' ht'.symm))
    ?_ D₀ hD₀ (fun k x y => hdiam _ x y)⟩
  refine Set.Subset.antisymm (Set.iUnion_subset fun k => ?_) fun x hx => ?_
  · rintro _ ⟨t, rfl⟩; exact hbd _ t
  · obtain ⟨i, t, rfl⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨e i, t, by simp⟩

end Generic

section Main

variable {M : ConnectedClosedOrientedManifold.{u} 3} (F : CollaredTorusFamily_C2a M.Carrier)
  (j : Fin (cutPresentation_S12 M F).toTorusDecomposition.components.count)

/-- Right tori `σ_i(·, 1/2)` owned by the block `j`. -/
abbrev ownedIdx_S39 : Type :=
  {i : Fin F.count // ∃ t, (sideTorus_C2a F i hR_C2a t :
        (cutPresentation_S12 M F).toTorusDecomposition.carrier.Carrier) ∈
      ((cutPresentation_S12 M F).toTorusDecomposition.components.piece j :
        Set (cutPresentation_S12 M F).toTorusDecomposition.carrier.Carrier)}

/-- **G2a (generic assembly).** See the module docstring. -/
theorem nearlyCuspidal_of_collars_S39
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) (K : ℕ) (δ D₀ : ℝ) (hD₀ : 0 ≤ D₀)
    (hnoleft : ∀ x : ((cutPresentation_S12 M F).toTorusDecomposition.component j).Carrier,
      ∀ (i : Fin F.count) (t : Torus), x.val.1 ≠ F.collar i (t, -1 / 2))
    (hne : ((cutPresentation_S12 M F).toTorusDecomposition.component j).model.boundary
        ((cutPresentation_S12 M F).toTorusDecomposition.component j).Carrier ≠ ∅)
    (H : Fin F.count → HyperbolicCusp) (φ : Fin F.count → CuspHalfSpace → M.Carrier)
    (hcol : ∀ i (p : CuspHalfSpace), p.2.val 0 < 1 → φ i p = F.collar i (p.1, p.2.val 0))
    (hout : ∀ i, ∀ p ∈ cuspDomain, 1 ≤ p.2.val 0 →
      ∀ k, φ i p ∉ F.collar k '' (univ ×ˢ Icc (-7 / 8 : ℝ) (7 / 8)))
    (hsm : ∀ i, ContMDiffOn halfCollarModel (𝓡 3) ∞ (φ i) cuspDomain)
    (hemb : ∀ i, _root_.Topology.IsEmbedding (fun p : cuspDomain => φ i p))
    (himm : ∀ i, ∀ p ∈ cuspDomain, Function.Injective (mfderiv halfCollarModel (𝓡 3) (φ i) p))
    (herr : ∀ i, cuspMetricErrorBound (W := NoCuts.carrier M) g K δ (H i) (φ i))
    (hdiam : ∀ i (x y : Torus), riemannianEDistOf (H i).torusMetric x y ≤ ENNReal.ofReal D₀) :
    Nonempty (NearlyCuspidalBoundary ((cutPresentation_S12 M F).toTorusDecomposition.component j)
      (cutMetric_S25 g (cutPresentation_S12 M F).toTorusDecomposition j) K
      (max δ (Real.sqrt (1 + δ) * D₀))) := by
  classical
  have hlift : ∀ i : ownedIdx_S39 F j, ∃ L' : CuspHalfSpace →
      ((cutPresentation_S12 M F).toTorusDecomposition.component j).Carrier,
      ContMDiffOn halfCollarModel
        ((cutPresentation_S12 M F).toTorusDecomposition.component j).model ∞ L' cuspDomain ∧
      (∀ p ∈ cuspDomain, cutPieceMap (cutPresentation_S12 M F).toTorusDecomposition j (L' p) =
        φ i.1 p) ∧
      (∀ t, (L' (t, halfZero)).val = sideTorus_C2a F i.1 hR_C2a t) ∧
      _root_.Topology.IsEmbedding (fun p : cuspDomain => L' p) ∧
      (∀ p ∈ cuspDomain, Function.Injective (mfderiv halfCollarModel
        ((cutPresentation_S12 M F).toTorusDecomposition.component j).model L' p)) :=
    fun i => exists_blockLift_S39 F j i.1 (φ i.1) (hcol i.1) (hout i.1) (hsm i.1) (hemb i.1)
      (himm i.1) i.2
  choose L' hsm' hb' hside hemb' himm' using hlift
  have hbdy := fun x => mem_boundary_block_iff_S39 (F := F) (j := j) (x := x) hnoleft
  have hbd : ∀ (i : ownedIdx_S39 F j) (t : Torus), L' i (t, halfZero) ∈
      ((cutPresentation_S12 M F).toTorusDecomposition.component j).model.boundary
        ((cutPresentation_S12 M F).toTorusDecomposition.component j).Carrier := fun i t =>
    (hbdy _).mpr ⟨i.1, t, by rw [hside i t]; exact sideTorus_val_S39 F i.1 t⟩
  have hcover : ∀ x ∈ ((cutPresentation_S12 M F).toTorusDecomposition.component j).model.boundary
      ((cutPresentation_S12 M F).toTorusDecomposition.component j).Carrier,
      ∃ (i : ownedIdx_S39 F j) (t : Torus), x = L' i (t, halfZero) := by
    intro x hx
    obtain ⟨i, t, hxt⟩ := (hbdy x).mp hx
    have hxv : x.val = sideTorus_C2a F i hR_C2a t :=
      Subtype.ext (hxt.trans (sideTorus_val_S39 F i t).symm)
    have hmem : ∃ t', (sideTorus_C2a F i hR_C2a t' :
        (cutPresentation_S12 M F).toTorusDecomposition.carrier.Carrier) ∈
      ((cutPresentation_S12 M F).toTorusDecomposition.components.piece j :
        Set (cutPresentation_S12 M F).toTorusDecomposition.carrier.Carrier) :=
      ⟨t, hxv ▸ x.2⟩
    exact ⟨⟨i, hmem⟩, t, Subtype.ext ((hxv.trans (hside ⟨i, hmem⟩ t).symm))⟩
  have hI : Nonempty (ownedIdx_S39 F j) := by
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨i, -⟩ := hcover x hx
    exact ⟨i⟩
  exact ncb_of_lifts_S39 D₀ hD₀ (fun i : ownedIdx_S39 F j => H i.1) L' hsm' hemb' himm'
    (fun i => cuspMetricErrorBound_transfer_S34 (W₀ := NoCuts.carrier M) g
      (cutPieceMap (cutPresentation_S12 M F).toTorusDecomposition j) (contMDiff_cutPieceMap _ j)
      (cutMetric_S25 g (cutPresentation_S12 M F).toTorusDecomposition j)
      (isInducedCutMetric_cutMetric_S25 g _ j) K δ (H i.1) (L' i) (φ i.1) (hsm' i) (hb' i)
      (herr i.1))
    (fun i => hdiam i.1) hbd
    (fun a b hab t t' h => by
      have h1 := congrArg Subtype.val h
      rw [hside a t, hside b t'] at h1
      have h2 := congrArg Subtype.val h1
      rw [sideTorus_val_S39, sideTorus_val_S39] at h2
      exact hab (Subtype.ext (right_torus_injective_S39 F h2)))
    hcover

end Main

end GC.LongTime.Ch12
