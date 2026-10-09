import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Elementary
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem.Basic
import DifferentialGeometry.Topology.Manifold.InteriorChart
import DifferentialGeometry.Topology.Manifold.Sigma
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Sigma
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans
import DifferentialGeometry.Topology.Manifold.SmoothMapDifferentialCoordinates
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.RegularSublevelAtlas
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordReversal
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingDisc
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CollarGermAdapter
import DifferentialGeometry.Topology.Embedding.Diffeomorph

/-!
# Embedded piece systems

Lane MD6 of `20261003-survey-p1-morse-decomposition.md`: the constructor of a torus presentation
of a given compact carrier `W` from embedded pieces, layered as asked by review 8.

`EmbeddedCutSystem W k` is the general input: finitely many compact connected smooth 3-manifolds
`Piece j` modelled on `k.model`, smooth maps `map j : Piece j → W` with bijective differential
whose images cover `W`, half collars of finitely many boundary tori of each piece exhausting its
boundary, and a bijection from all these tori to the sides of seams and the external tori. Seam
`c` is a signed collar of `W` in the interior of `W` reading the half collar of its left side for
`s ≤ 0` and, through `matching c`, the half collar of its right side for `s ≥ 0`. The two sides of
a seam may lie on the same piece: an old self-seam has two distinct ports. Near the external tori
the maps are local diffeomorphisms (`external_local`). Two points of `Cut = Σ j, Piece j` with the
same image are equal or lie over a seam torus (`overlap`, a comparison of `Σ`-points).

From this weak overlap the exact fibres of the fold `Cut → W` follow (`fold_eq_fold`): a fibre is
a point or the two sides of one seam over one torus point, so there are no triple overlaps. The
proof runs the inverse function theorem at interior points
(`isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective`) and uses that the seam tori have empty
interior. `toTorusPresentation` is the torus presentation: the cut carrier is the `Σ` with the
orientation pulled back along the fold, the gluing identifies the two side tori of every seam,
the reconstruction is the fold on the quotient, the interior diffeomorphism is the bijective
local diffeomorphism induced by the fold, the external collars of `W` are the fold of the
external side collars, and `reversing` is proved from the tangent-space equality, the left side
reading `seam ∘ reflection ∘ height` and the right side `seam ∘ height`. Disjointness of all seams
and external collars comes from `fold_sideCollar_eq`.

A `ProductCertificate` exhibits every piece as `Pₖ × S¹` with the piece collars equal to the base
collars, and gives `toElementaryPresentation`. `EmbeddedPieceSystem W` is the product form of the
plan (pieces `Pₖ × S¹` over planar bases mapped into `W`); `toCutSystem` replaces each product by
the model `cutModelPiece k`, a regular sublevel set in `PlaneLift × S¹`, through the embedding of
the base. It differs from the frozen text in three fields: in `overlap` the ill-typed alternative
`j = j' ∧ q = q'` is replaced by the equality of `Σ`-points; `injective` is dropped, since it
excludes self-seams and follows from `overlap` away from them; `external_boundary` is replaced by
`external_local`, from which it follows, because the tree has no inverse function theorem at
boundary points.

Every torus presentation is a cut system (`TorusPresentation.cutSystem`, pieces the components),
and the constructor gives it back: the external collars agree on the whole collar
(`cutSystem_toTorusPresentation_external_collar`) and seams, matchings and owning pieces agree by
definition. `productPieceSystem k` rebuilds `productPresentation k` as a one-piece system.
-/

set_option autoImplicit false

noncomputable section
open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section InteriorInverse

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem fderiv_writtenInExtChartAt_of_isInteriorPoint {f : M → N} {x : M}
    (hf : ContMDiffAt I J ∞ f x) (hx : I.IsInteriorPoint x) :
    fderiv ℝ (writtenInExtChartAt I J x f) (extChartAt I x x) = mfderiv I J f x := by
  rw [(hf.mdifferentiableAt (by simp)).mfderiv]
  exact (fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hx)).symm

omit [FiniteDimensional ℝ F] in
private theorem eventually_isInvertible_fderiv' {G : E → F} {V : Set E} {a : E}
    (hV : IsOpen V) (ha : a ∈ V) (hG : ContDiffOn ℝ ∞ G V)
    (hinv : (fderiv ℝ G a).IsInvertible) : ∀ᶠ y in 𝓝 a, (fderiv ℝ G y).IsInvertible := by
  obtain ⟨e, he⟩ := hinv
  have hn : {L : E →L[ℝ] F | L.IsInvertible} ∈ 𝓝 (fderiv ℝ G a) := by
    rw [← he]
    exact e.nhds
  exact ((hG.contDiffAt (hV.mem_nhds ha)).continuousAt_fderiv (by simp)).preimage_mem_nhds hn

omit [FiniteDimensional ℝ F] in
theorem isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective {f : M → N} {x : M}
    (hf : ContMDiff I J ∞ f) (hx : I.IsInteriorPoint x)
    (hb : Function.Bijective (mfderiv I J f x)) : IsLocalDiffeomorphAt I J ∞ f x := by
  have hy : J.IsInteriorPoint (f x) :=
    (hf.mdifferentiableAt (by simp)).isInteriorPoint_of_surjective_mfderiv hb.2 hx
  let c := DifferentialGeometry.Manifold.interiorChart I ∞ x
  let d := DifferentialGeometry.Manifold.interiorChart J ∞ (f x)
  have hxc : x ∈ c.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hx
  have hyd : f x ∈ d.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff J ∞ (f x)).mpr hy
  let V : Set E := c.target ∩ (c.symm : E → M) ⁻¹' (f ⁻¹' d.source)
  let K : E → F := fun w => d (f (c.symm w))
  have hV : IsOpen V :=
    c.symm.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage c.open_target
      (d.open_source.preimage hf.continuous)
  have hcxV : c x ∈ V := by
    refine ⟨c.map_source hxc, ?_⟩
    change f ((extChartAt I x).symm (extChartAt I x x)) ∈ d.source
    rw [(extChartAt I x).left_inv (mem_extChartAt_source x)]
    exact hyd
  have hinner : ContMDiffOn 𝓘(ℝ, E) J ∞ (fun w => f (c.symm w)) V :=
    hf.comp_contMDiffOn (c.contMDiffOn_invFun.mono inter_subset_left)
  have hK : ContDiffOn ℝ ∞ K V :=
    (d.contMDiffOn_toFun.comp hinner (fun w hw => hw.2)).contDiffOn
  have hinvK : (fderiv ℝ K (c x)).IsInvertible := by
    have hKdef : K = writtenInExtChartAt I J x f := rfl
    have hcz : c x = extChartAt I x x := rfl
    rw [hKdef, hcz, fderiv_writtenInExtChartAt_of_isInteriorPoint hf.contMDiffAt hx]
    exact ⟨(LinearEquiv.ofBijective (mfderiv I J f x).toLinearMap hb).toContinuousLinearEquiv,
      rfl⟩
  have hevent := eventually_isInvertible_fderiv' hV hcxV hK hinvK
  obtain ⟨W, hWsub, hW, hcxW⟩ := mem_nhds_iff.mp (inter_mem hevent (hV.mem_nhds hcxV))
  exact DifferentialGeometry.Coordinates.isLocalDiffeomorphAt_of_coordinates c d hW hxc hcxW
    (fun w hw => (hWsub hw).2.2) (hK.mono fun w hw => (hWsub hw).2)
    (fun w hw => (hWsub hw).1)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [IsManifold J ∞ N] in
theorem isOpen_image_of_isLocalDiffeomorphAt {f : M → N} {U : Set M} (hU : IsOpen U)
    (hf : ∀ x ∈ U, IsLocalDiffeomorphAt I J ∞ f x) : IsOpen (f '' U) := by
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨Φ, hxΦ, hΦ⟩ := hf x hx
  have himg : Φ '' (Φ.source ∩ U) ⊆ f '' U := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨z, hz.2, hΦ hz.1⟩
  refine Filter.mem_of_superset ?_ himg
  rw [hΦ hxΦ]
  exact (Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source (Φ.open_source.inter hU)
    inter_subset_left).mem_nhds ⟨x, ⟨hxΦ, hx⟩, rfl⟩

end InteriorInverse

section SigmaSmooth

variable {ι : Type*} {H : Type*} [TopologicalSpace H] [Nonempty H]
  {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, ChartedSpace H (X i)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {I : ModelWithCorners ℝ E H}
  [∀ i, IsManifold I ∞ (X i)]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]

theorem contMDiffAt_sigma {f : (Σ j, X j) → N} {i : ι} {x : X i}
    (hf : ContMDiffAt I J ∞ (fun y : X i => f ⟨i, y⟩) x) :
    ContMDiffAt I J ∞ f ⟨i, x⟩ := by
  obtain ⟨Φ, hx, hΦ⟩ := isLocalDiffeomorph_sigmaMk (I := I) (n := ∞) (M := X) i x
  have hΦx : Φ x = ⟨i, x⟩ := (hΦ hx).symm
  have hxt : (⟨i, x⟩ : Σ j, X j) ∈ Φ.target := by
    rw [← hΦx]
    exact Φ.map_source hx
  have hsym : Φ.symm ⟨i, x⟩ = x := by
    rw [← hΦx]
    exact Φ.left_inv hx
  have hinv : ContMDiffAt I I ∞ Φ.symm ⟨i, x⟩ :=
    Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hxt)
  have hcomp : ContMDiffAt I J ∞ ((fun y : X i => f ⟨i, y⟩) ∘ Φ.symm) ⟨i, x⟩ := by
    refine ContMDiffAt.comp _ ?_ hinv
    rw [hsym]
    exact hf
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [Φ.open_target.mem_nhds hxt] with y hy
  have h1 : Φ (Φ.symm y) = y := Φ.right_inv hy
  have h2 : Φ (Φ.symm y) = ⟨i, Φ.symm y⟩ := (hΦ (Φ.map_target hy)).symm
  exact congrArg f (h1.symm.trans h2)

theorem contMDiff_sigma {f : (Σ j, X j) → N}
    (hf : ∀ i, ContMDiff I J ∞ (fun y : X i => f ⟨i, y⟩)) : ContMDiff I J ∞ f := by
  rintro ⟨i, x⟩
  exact contMDiffAt_sigma (hf i x)

theorem mfderiv_sigma_bijective {f : (Σ j, X j) → N} {i : ι} {x : X i}
    (hf : MDifferentiableAt I J f ⟨i, x⟩)
    (hb : Function.Bijective (mfderiv I J (fun y : X i => f ⟨i, y⟩) x)) :
    Function.Bijective (mfderiv I J f ⟨i, x⟩) := by
  have hl := isLocalDiffeomorph_sigmaMk (I := I) (n := ∞) (M := X) i x
  have hmk : MDifferentiableAt I I (Sigma.mk i : X i → Σ j, X j) x :=
    hl.mdifferentiableAt (by simp)
  have hc := mfderiv_comp x hf hmk
  have hcb : Function.Bijective (mfderiv I I (Sigma.mk i : X i → Σ j, X j) x) :=
    (hl.mfderivToContinuousLinearEquiv (by simp)).bijective
  change Function.Bijective (mfderiv I J (f ∘ Sigma.mk i) x) at hb
  rw [hc] at hb
  have hsurj : Function.Surjective (mfderiv I J f ⟨i, x⟩) := by
    intro w
    obtain ⟨v, hv⟩ := hb.2 w
    exact ⟨_, hv⟩
  refine ⟨fun a b hab => ?_, hsurj⟩
  obtain ⟨a', rfl⟩ := hcb.2 a
  obtain ⟨b', rfl⟩ := hcb.2 b
  exact congrArg _ (hb.1 hab)

theorem isInteriorPoint_sigmaMk_iff {i : ι} (x : X i) :
    I.IsInteriorPoint (⟨i, x⟩ : Σ j, X j) ↔ I.IsInteriorPoint x :=
  ((isLocalDiffeomorph_sigmaMk (I := I) (n := ∞) (M := X) i x).isInteriorPoint_iff
    (by simp)).symm

theorem exists_sigmaMkPD [Nonempty ι] [∀ i, Nonempty (X i)] (i : ι) :
    ∃ Φ : PartialDiffeomorph I I (X i) (Σ j, X j) ∞, Φ.toPartialEquiv.source = univ ∧
      Φ.toPartialEquiv.target = range (Sigma.mk i) ∧ Φ.toFun = Sigma.mk i := by
  obtain ⟨Φ, h1, h2, h3⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    ((isLocalDiffeomorph_sigmaMk (I := I) (n := ∞) (M := X) i).isLocalDiffeomorphOn univ)
    isOpen_univ univ_nonempty sigma_mk_injective.injOn
  exact ⟨Φ, h1, by rw [h2, image_univ], h3⟩

end SigmaSmooth

theorem halfCollarModel_isInteriorPoint' {p : Torus × EuclideanHalfSpace 1}
    (hp : 0 < p.2.val 0) : halfCollarModel.IsInteriorPoint p := by
  have h1 : (𝓡∂ 1).IsInteriorPoint p.2 := by
    rw [ModelWithCorners.IsInteriorPoint, interior_range_modelWithCornersEuclideanHalfSpace]
    change 0 < ((𝓡∂ 1) p.2) 0
    exact hp
  have h2 : torusModel.IsInteriorPoint p.1 := BoundarylessManifold.isInteriorPoint
  have h3 : p ∈ halfCollarModel.interior (Torus × EuclideanHalfSpace 1) := by
    rw [ModelWithCorners.interior_prod]
    exact ⟨h2, h1⟩
  exact h3

def clampHalf (s : ℝ) : EuclideanHalfSpace 1 := halfPoint (max s 0) (le_max_right s 0)

theorem continuous_clampHalf : Continuous clampHalf :=
  Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun _ => continuous_id.max continuous_const)) _

theorem clampHalf_of_nonneg {s : ℝ} (hs : 0 ≤ s) : clampHalf s = halfPoint s hs :=
  (halfPoint_eq_self (clampHalf s) hs (max_eq_left hs).symm).symm

theorem clampHalf_zero : clampHalf 0 = halfZero := clampHalf_of_nonneg le_rfl

theorem isOpen_halfCollarSource' : IsOpen halfCollarSource :=
  isOpen_lt ((EuclideanSpace.proj 0).continuous.comp (continuous_subtype_val.comp continuous_snd))
    continuous_const

theorem isOpen_signedCollarSource' : IsOpen signedCollarSource :=
  (isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const)

instance (k : CarrierModel) : Nonempty k.Space := by
  cases k
  · exact inferInstanceAs (Nonempty (EuclideanSpace ℝ (Fin 3)))
  · exact ⟨⟨0, le_rfl⟩⟩

structure EmbeddedCutSystem (W : CompactCarrier.{u}) (kind : CarrierModel) where
  count : ℕ
  count_pos : 0 < count
  Piece : Fin count → Type u
  [topology : ∀ j, TopologicalSpace (Piece j)]
  [charts : ∀ j, ChartedSpace kind.Space (Piece j)]
  [manifold : ∀ j, IsManifold kind.model ∞ (Piece j)]
  [compact : ∀ j, CompactSpace (Piece j)]
  [hausdorff : ∀ j, T2Space (Piece j)]
  [secondCountable : ∀ j, SecondCountableTopology (Piece j)]
  [connected : ∀ j, ConnectedSpace (Piece j)]
  map : ∀ j, Piece j → W.Carrier
  smooth : ∀ j, ContMDiff kind.model W.model ∞ (map j)
  mfderiv_bijective : ∀ j q, Function.Bijective (mfderiv kind.model W.model (map j) q)
  covers : ⋃ j, range (map j) = univ
  torusCount : Fin count → ℕ
  collar : ∀ j, Fin (torusCount j) →
    PartialDiffeomorph halfCollarModel kind.model (Torus × EuclideanHalfSpace 1) (Piece j) ∞
  collar_source : ∀ j l, (collar j l).source = halfCollarSource
  collar_disjoint : ∀ j, Pairwise fun l l' => Disjoint (collar j l).target (collar j l').target
  boundary_exhausted : ∀ j, kind.model.boundary (Piece j) =
    ⋃ l, range fun t => collar j l (t, halfZero)
  seamCount : ℕ
  side : Fin seamCount → Bool → Σ j, Fin (torusCount j)
  externalCount : ℕ
  externalSide : Fin externalCount → Σ j, Fin (torusCount j)
  sides_bijective : Function.Bijective (Sum.elim (Function.uncurry side) externalSide)
  matching : Fin seamCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  seam : Fin seamCount → PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞
  seam_source : ∀ c, (seam c).source = signedCollarSource
  seam_neg : ∀ c (t : Torus) s (hs : s ≤ 0), -1 < s → seam c (t, s) =
    map (side c true).1 (collar _ (side c true).2 (t, halfPoint (-s) (neg_nonneg.2 hs)))
  seam_pos : ∀ c (t : Torus) s (hs : 0 ≤ s), s < 1 → seam c (t, s) =
    map (side c false).1 (collar _ (side c false).2 (matching c t, halfPoint s hs))
  seam_interior : ∀ c, (seam c).target ⊆ W.interior
  external_local : ∀ i (t : Torus), IsLocalDiffeomorphAt kind.model W.model ∞
    (map (externalSide i).1) (collar _ (externalSide i).2 (t, halfZero))
  overlap : ∀ j j' q q', map j q = map j' q' →
    (⟨j, q⟩ : Σ j, Piece j) = ⟨j', q'⟩ ∨ ∃ c t, map j q = seam c (t, 0)

attribute [instance] EmbeddedCutSystem.topology EmbeddedCutSystem.charts
  EmbeddedCutSystem.manifold EmbeddedCutSystem.compact EmbeddedCutSystem.hausdorff
  EmbeddedCutSystem.secondCountable EmbeddedCutSystem.connected

namespace EmbeddedCutSystem

variable {W : CompactCarrier.{u}} {k : CarrierModel} (S : EmbeddedCutSystem W k)

abbrev Cut : Type u := Σ j, S.Piece j

abbrev Side : Type := Σ j, Fin (S.torusCount j)

instance : Nonempty (Fin S.count) := ⟨⟨0, S.count_pos⟩⟩

def fold (x : S.Cut) : W.Carrier := S.map x.1 x.2

theorem fold_mk (j : Fin S.count) (q : S.Piece j) : S.fold ⟨j, q⟩ = S.map j q := rfl

theorem contMDiff_fold : ContMDiff k.model W.model ∞ S.fold :=
  contMDiff_sigma fun j => S.smooth j

theorem mfderiv_fold_bijective (x : S.Cut) :
    Function.Bijective (mfderiv k.model W.model S.fold x) := by
  obtain ⟨j, q⟩ := x
  exact mfderiv_sigma_bijective (S.contMDiff_fold.mdifferentiableAt (by simp))
    (S.mfderiv_bijective j q)

def cutOrientation : ManifoldOrientation k.model S.Cut 3 :=
  Manifold.manifoldOrientationPullback k.model W.model finrank_euclideanSpace_fin S.fold
    S.contMDiff_fold S.mfderiv_fold_bijective W.orientation

abbrev cutCarrier : CompactCarrier.{u} where
  kind := k
  Carrier := S.Cut
  charts := (inferInstance : ChartedSpace k.Space S.Cut)
  smooth := (inferInstance : IsManifold k.model ∞ S.Cut)
  orientation := S.cutOrientation

theorem isInteriorPoint_mk_iff (j : Fin S.count) (q : S.Piece j) :
    k.model.IsInteriorPoint (⟨j, q⟩ : S.Cut) ↔ k.model.IsInteriorPoint q :=
  isInteriorPoint_sigmaMk_iff q

def pieceOpen (j : Fin S.count) : TopologicalSpace.Opens S.Cut :=
  ⟨range (Sigma.mk j), isOpen_range_sigmaMk⟩

theorem pieceInterior_eq (j : Fin S.count) :
    (S.cutCarrier.pieceInterior (S.pieceOpen j) : Set S.Cut) =
      Sigma.mk j '' k.model.interior (S.Piece j) := by
  ext x
  constructor
  · rintro ⟨⟨q, rfl⟩, hx⟩
    exact ⟨q, (S.isInteriorPoint_mk_iff j q).mp hx, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, rfl⟩, (S.isInteriorPoint_mk_iff j q).mpr hq⟩

def components : S.cutCarrier.Components where
  count := S.count
  count_pos := S.count_pos
  piece := S.pieceOpen
  closed _ := isClosed_range_sigmaMk
  connected _ := isConnected_iff_connectedSpace.mp (isConnected_range continuous_sigmaMk)
  disjoint i j hij := by
    change Disjoint (range (Sigma.mk i)) (range (Sigma.mk j))
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    exact hij (congrArg Sigma.fst hb).symm
  covers := eq_univ_of_forall fun x => mem_iUnion.2 ⟨x.1, x.2, rfl⟩
  interior_connected j := by
    refine isConnected_iff_connectedSpace.mp ?_
    rw [S.pieceInterior_eq j]
    have hne : (k.model.interior (S.Piece j)).Nonempty :=
      DifferentialGeometry.Topology.Manifold.dense_manifold_interior.nonempty
    exact ⟨hne.image _,
      DifferentialGeometry.Topology.Manifold.isPreconnected_manifold_interior.image _
        continuous_sigmaMk.continuousOn⟩

def mkPD (j : Fin S.count) : PartialDiffeomorph k.model k.model (S.Piece j) S.Cut ∞ :=
  Classical.choose (exists_sigmaMkPD (I := k.model) (X := S.Piece) j)

theorem mkPD_source (j : Fin S.count) : (S.mkPD j).source = univ :=
  (Classical.choose_spec (exists_sigmaMkPD (I := k.model) (X := S.Piece) j)).1

theorem mkPD_apply (j : Fin S.count) (q : S.Piece j) : S.mkPD j q = ⟨j, q⟩ :=
  congrFun (Classical.choose_spec (exists_sigmaMkPD (I := k.model) (X := S.Piece) j)).2.2 q

def sideCollar (σ : S.Side) :
    PartialDiffeomorph halfCollarModel k.model (Torus × EuclideanHalfSpace 1) S.Cut ∞ :=
  (S.collar σ.1 σ.2).trans (S.mkPD σ.1)

theorem sideCollar_apply (σ : S.Side) (p : Torus × EuclideanHalfSpace 1) :
    S.sideCollar σ p = ⟨σ.1, S.collar σ.1 σ.2 p⟩ :=
  S.mkPD_apply σ.1 _

theorem sideCollar_source (σ : S.Side) : (S.sideCollar σ).source = halfCollarSource := by
  change ((S.collar σ.1 σ.2).trans (S.mkPD σ.1)).source = _
  rw [PartialDiffeomorph.trans_source, S.mkPD_source, preimage_univ, inter_univ,
    S.collar_source]

theorem fold_sideCollar (σ : S.Side) (p : Torus × EuclideanHalfSpace 1) :
    S.fold (S.sideCollar σ p) = S.map σ.1 (S.collar σ.1 σ.2 p) := by
  rw [S.sideCollar_apply]
  rfl

theorem collar_mem_target {j : Fin S.count} (l : Fin (S.torusCount j))
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    S.collar j l p ∈ (S.collar j l).target :=
  (S.collar j l).map_source ((S.collar_source j l).symm ▸ hp)

theorem sideCollar_inj {σ σ' : S.Side} {p p' : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) (hp' : p' ∈ halfCollarSource)
    (h : S.sideCollar σ p = S.sideCollar σ' p') : σ = σ' ∧ p = p' := by
  obtain ⟨j, l⟩ := σ
  obtain ⟨j', l'⟩ := σ'
  rw [S.sideCollar_apply, S.sideCollar_apply] at h
  obtain ⟨rfl, hq⟩ := Sigma.mk.inj_iff.mp h
  have hq' : S.collar j l p = S.collar j l' p' := eq_of_heq hq
  have hll : l = l' := by
    by_contra hne
    exact (S.collar_disjoint j hne).le_bot
      ⟨S.collar_mem_target l hp, hq' ▸ S.collar_mem_target l' hp'⟩
  subst hll
  refine ⟨rfl, ?_⟩
  exact (S.collar j l).toOpenPartialHomeomorph.injOn ((S.collar_source j l).symm ▸ hp)
    ((S.collar_source j l).symm ▸ hp') hq'

theorem zero_mem_halfCollarSource' (t : Torus) : (t, halfZero) ∈ halfCollarSource := by
  change (0 : ℝ) < 1
  norm_num

def sideTorus (σ : S.Side) (t : Torus) : S.Cut := S.sideCollar σ (t, halfZero)

theorem continuous_sideTorus (σ : S.Side) : Continuous (S.sideTorus σ) :=
  (S.sideCollar σ).contMDiffOn.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
    fun t => (S.sideCollar_source σ).symm ▸ zero_mem_halfCollarSource' t

theorem injective_sideTorus (σ : S.Side) : Injective (S.sideTorus σ) := fun t t' h =>
  congrArg Prod.fst (S.sideCollar_inj (zero_mem_halfCollarSource' t)
    (zero_mem_halfCollarSource' t') h).2

theorem sideTorus_eq_sideTorus {σ σ' : S.Side} {t t' : Torus}
    (h : S.sideTorus σ t = S.sideTorus σ' t') : σ = σ' ∧ t = t' := by
  obtain ⟨h1, h2⟩ := S.sideCollar_inj (zero_mem_halfCollarSource' t)
    (zero_mem_halfCollarSource' t') h
  exact ⟨h1, congrArg Prod.fst h2⟩

theorem side_injective : Injective (Function.uncurry S.side) :=
  S.sides_bijective.1.comp Sum.inl_injective

theorem side_ne_externalSide (c : Fin S.seamCount) (b : Bool) (i : Fin S.externalCount) :
    S.side c b ≠ S.externalSide i := fun h =>
  Sum.inl_ne_inr (S.sides_bijective.1 (a₁ := .inl (c, b)) (a₂ := .inr i) h)

theorem externalSide_injective : Injective S.externalSide :=
  S.sides_bijective.1.comp Sum.inr_injective

theorem side_ne (c : Fin S.seamCount) : S.side c true ≠ S.side c false := fun h =>
  Bool.true_eq_false.mp (congrArg Prod.snd (S.side_injective
    (a₁ := (c, true)) (a₂ := (c, false)) h))

theorem side_eq_side_iff {c d : Fin S.seamCount} {b b' : Bool} :
    S.side c b = S.side d b' ↔ c = d ∧ b = b' := by
  constructor
  · intro h
    have := S.side_injective (a₁ := (c, b)) (a₂ := (d, b')) h
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  · rintro ⟨rfl, rfl⟩
    rfl

def leftPt (c : Fin S.seamCount) (t : Torus) : S.Cut := S.sideTorus (S.side c true) t

def rightPt (c : Fin S.seamCount) (t : Torus) : S.Cut :=
  S.sideTorus (S.side c false) (S.matching c t)

theorem fold_leftCollar (c : Fin S.seamCount) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    S.fold (S.sideCollar (S.side c true) p) = S.seam c (p.1, -(p.2.val 0)) := by
  have h0 : -(p.2.val 0) ≤ 0 := neg_nonpos.mpr p.2.property
  have h1 : -1 < -(p.2.val 0) := neg_lt_neg hp
  rw [S.seam_neg c p.1 _ h0 h1, S.fold_sideCollar, halfPoint_eq_self p.2 _ (neg_neg _)]

theorem fold_rightCollar (c : Fin S.seamCount) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    S.fold (S.sideCollar (S.side c false) (S.matching c p.1, p.2)) =
      S.seam c (p.1, p.2.val 0) := by
  rw [S.seam_pos c p.1 _ p.2.property hp, S.fold_sideCollar, halfPoint_eq_self p.2 _ rfl]

theorem fold_leftPt (c : Fin S.seamCount) (t : Torus) :
    S.fold (S.leftPt c t) = S.seam c (t, 0) := by
  have h := S.fold_leftCollar c (zero_mem_halfCollarSource' t)
  rw [show -(halfZero.val 0) = (0 : ℝ) from neg_zero] at h
  exact h

theorem fold_rightPt (c : Fin S.seamCount) (t : Torus) :
    S.fold (S.rightPt c t) = S.seam c (t, 0) :=
  S.fold_rightCollar c (zero_mem_halfCollarSource' t)

def leftSweep (c : Fin S.seamCount) (p : Torus × ℝ) : S.Cut :=
  S.sideCollar (S.side c true) (p.1, clampHalf (-p.2))

def rightSweep (c : Fin S.seamCount) (p : Torus × ℝ) : S.Cut :=
  S.sideCollar (S.side c false) (S.matching c p.1, clampHalf p.2)

theorem continuousAt_leftSweep (c : Fin S.seamCount) (t : Torus) :
    ContinuousAt (S.leftSweep c) (t, 0) := by
  have hin : Continuous fun p : Torus × ℝ => (p.1, clampHalf (-p.2)) :=
    continuous_fst.prodMk (continuous_clampHalf.comp continuous_snd.neg)
  have hpt : (fun p : Torus × ℝ => (p.1, clampHalf (-p.2))) (t, 0) = (t, halfZero) := by
    simp only [neg_zero, clampHalf_zero]
  refine ContinuousAt.comp_of_eq ?_ hin.continuousAt hpt
  exact (S.sideCollar _).contMDiffOn.continuousOn.continuousAt
    ((S.sideCollar _).open_source.mem_nhds
      ((S.sideCollar_source _).symm ▸ zero_mem_halfCollarSource' t))

theorem continuousAt_rightSweep (c : Fin S.seamCount) (t : Torus) :
    ContinuousAt (S.rightSweep c) (t, 0) := by
  have hin : Continuous fun p : Torus × ℝ => (S.matching c p.1, clampHalf p.2) :=
    ((S.matching c).continuous.comp continuous_fst).prodMk
      (continuous_clampHalf.comp continuous_snd)
  have hpt : (fun p : Torus × ℝ => (S.matching c p.1, clampHalf p.2)) (t, 0) =
      (S.matching c t, halfZero) := by
    simp only [clampHalf_zero]
  refine ContinuousAt.comp_of_eq ?_ hin.continuousAt hpt
  exact (S.sideCollar _).contMDiffOn.continuousOn.continuousAt
    ((S.sideCollar _).open_source.mem_nhds
      ((S.sideCollar_source _).symm ▸ zero_mem_halfCollarSource' _))

theorem leftSweep_zero (c : Fin S.seamCount) (t : Torus) : S.leftSweep c (t, 0) = S.leftPt c t := by
  change S.sideCollar _ (t, clampHalf (-0)) = S.sideCollar _ (t, halfZero)
  rw [neg_zero, clampHalf_zero]

theorem rightSweep_zero (c : Fin S.seamCount) (t : Torus) :
    S.rightSweep c (t, 0) = S.rightPt c t := by
  change S.sideCollar _ (S.matching c t, clampHalf 0) = S.sideCollar _ (S.matching c t, halfZero)
  rw [clampHalf_zero]

theorem fold_leftSweep (c : Fin S.seamCount) {p : Torus × ℝ} (hp : p ∈ signedCollarSource)
    (h0 : p.2 ≤ 0) : S.fold (S.leftSweep c p) = S.seam c p := by
  have hn : 0 ≤ -p.2 := neg_nonneg.mpr h0
  have hmem : (p.1, clampHalf (-p.2)) ∈ halfCollarSource := by
    change (clampHalf (-p.2)).val 0 < 1
    rw [clampHalf_of_nonneg hn]
    change -p.2 < 1
    linarith [hp.1]
  have h := S.fold_leftCollar c hmem
  rw [clampHalf_of_nonneg hn] at h
  change S.fold (S.sideCollar _ (p.1, clampHalf (-p.2))) = _
  rw [clampHalf_of_nonneg hn, h]
  change S.seam c (p.1, -(-p.2)) = S.seam c p
  rw [neg_neg]

theorem fold_rightSweep (c : Fin S.seamCount) {p : Torus × ℝ} (hp : p ∈ signedCollarSource)
    (h0 : 0 ≤ p.2) : S.fold (S.rightSweep c p) = S.seam c p := by
  have hmem : (p.1, clampHalf p.2) ∈ halfCollarSource := by
    change (clampHalf p.2).val 0 < 1
    rw [clampHalf_of_nonneg h0]
    exact hp.2
  have h := S.fold_rightCollar c hmem
  change S.fold (S.sideCollar _ (S.matching c p.1, clampHalf p.2)) = _
  rw [h, clampHalf_of_nonneg h0]
  rfl

def seamTorusSet : Set W.Carrier := ⋃ c, range fun t : Torus => S.seam c (t, 0)

theorem continuous_seam_zero (c : Fin S.seamCount) :
    Continuous fun t : Torus => S.seam c (t, 0) :=
  (S.seam c).contMDiffOn.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
    fun t => (S.seam_source c).symm ▸ ⟨by norm_num, by norm_num⟩

theorem isClosed_seamTorusSet : IsClosed S.seamTorusSet :=
  isClosed_iUnion_of_finite fun c => (isCompact_range (S.continuous_seam_zero c)).isClosed

theorem interior_seamTorus (c : Fin S.seamCount) :
    interior (range fun t : Torus => S.seam c (t, 0)) = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨t, rfl⟩ := (interior_subset hx : x ∈ range fun t : Torus => S.seam c (t, 0))
  have h0 : ((t, 0) : Torus × ℝ) ∈ (S.seam c).source :=
    (S.seam_source c).symm ▸ ⟨by norm_num, by norm_num⟩
  have hnhds : (fun p : Torus × ℝ => S.seam c p) ⁻¹'
      interior (range fun t : Torus => S.seam c (t, 0)) ∩ (S.seam c).source ∈ 𝓝 (t, 0) :=
    inter_mem ((S.seam c).contMDiffOn.continuousOn.continuousAt ((S.seam c).open_source.mem_nhds h0)
      |>.preimage_mem_nhds (isOpen_interior.mem_nhds hx))
      ((S.seam c).open_source.mem_nhds h0)
  have hseq : Tendsto (fun ε : ℝ => ((t, ε) : Torus × ℝ)) (𝓝[>] 0) (𝓝 (t, 0)) :=
    ((continuous_const.prodMk continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨ε, hε, hεpos⟩ := ((hseq.eventually hnhds).and self_mem_nhdsWithin).exists
  obtain ⟨t', ht'⟩ := interior_subset hε.1
  have hsrc : ((t', 0) : Torus × ℝ) ∈ (S.seam c).source :=
    (S.seam_source c).symm ▸ ⟨by norm_num, by norm_num⟩
  have := congrArg Prod.snd ((S.seam c).toOpenPartialHomeomorph.injOn hsrc hε.2 ht')
  simp only at this
  exact (ne_of_gt hεpos) this.symm

theorem interior_seamTorusSet : interior S.seamTorusSet = ∅ := by
  have h : IsNowhereDense S.seamTorusSet := by
    refine IsNowhereDense.iUnion fun c => ?_
    rw [(isCompact_range (S.continuous_seam_zero c)).isClosed.isNowhereDense_iff]
    exact S.interior_seamTorus c
  rwa [S.isClosed_seamTorusSet.isNowhereDense_iff] at h

theorem fold_eq_or_mem {x y : S.Cut} (h : S.fold x = S.fold y) :
    x = y ∨ S.fold x ∈ S.seamTorusSet := by
  obtain ⟨j, q⟩ := x
  obtain ⟨j', q'⟩ := y
  rcases S.overlap j j' q q' h with h | ⟨c, t, h⟩
  · exact Or.inl h
  · exact Or.inr (mem_iUnion.2 ⟨c, t, h.symm⟩)

theorem isLocalDiffeomorphAt_fold {x : S.Cut} (hx : k.model.IsInteriorPoint x) :
    IsLocalDiffeomorphAt k.model W.model ∞ S.fold x :=
  isLocalDiffeomorphAt_of_isInteriorPoint_of_bijective S.contMDiff_fold hx
    (S.mfderiv_fold_bijective x)

theorem eq_leftPt_or_eq_rightPt {x : S.Cut} {c : Fin S.seamCount} {t : Torus}
    (h : S.fold x = S.seam c (t, 0)) : x = S.leftPt c t ∨ x = S.rightPt c t := by
  by_contra hne
  push Not at hne
  obtain ⟨hL, hR⟩ := hne
  obtain ⟨U₁, V₁, hU₁, hV₁, hxU₁, hLV₁, hUV₁⟩ := t2_separation hL
  obtain ⟨U₂, V₂, hU₂, hV₂, hxU₂, hRV₂, hUV₂⟩ := t2_separation hR
  have h0 : ((t, 0) : Torus × ℝ) ∈ signedCollarSource := ⟨by norm_num, by norm_num⟩
  have hn1 : S.leftSweep c ⁻¹' V₁ ∈ 𝓝 ((t, 0) : Torus × ℝ) :=
    (S.continuousAt_leftSweep c t).preimage_mem_nhds
      (hV₁.mem_nhds ((S.leftSweep_zero c t).symm ▸ hLV₁))
  have hn2 : S.rightSweep c ⁻¹' V₂ ∈ 𝓝 ((t, 0) : Torus × ℝ) :=
    (S.continuousAt_rightSweep c t).preimage_mem_nhds
      (hV₂.mem_nhds ((S.rightSweep_zero c t).symm ▸ hRV₂))
  obtain ⟨V, hVsub, hVo, htV⟩ := mem_nhds_iff.mp
    (inter_mem (inter_mem hn1 hn2) (isOpen_signedCollarSource'.mem_nhds h0))
  have hVsrc : V ⊆ (S.seam c).source := fun p hp => (S.seam_source c).symm ▸ (hVsub hp).2
  have hO : IsOpen (S.seam c '' V) :=
    (S.seam c).toOpenPartialHomeomorph.isOpen_image_of_subset_source hVo hVsrc
  let N : Set S.Cut := ((U₁ ∩ U₂) ∩ S.fold ⁻¹' (S.seam c '' V)) ∩ k.model.interior S.Cut
  have hN0 : IsOpen ((U₁ ∩ U₂) ∩ S.fold ⁻¹' (S.seam c '' V)) :=
    (hU₁.inter hU₂).inter (hO.preimage S.contMDiff_fold.continuous)
  have hxN0 : x ∈ (U₁ ∩ U₂) ∩ S.fold ⁻¹' (S.seam c '' V) :=
    ⟨⟨hxU₁, hxU₂⟩, ⟨(t, 0), htV, h.symm⟩⟩
  have hNo : IsOpen N :=
    hN0.inter (ModelWithCorners.isOpen_interior (I := k.model) (M := S.Cut) (n := ∞) (by simp))
  have hNne : N.Nonempty :=
    DifferentialGeometry.Topology.Manifold.dense_manifold_interior.inter_open_nonempty _ hN0
      ⟨x, hxN0⟩
  have himg : IsOpen (S.fold '' N) :=
    isOpen_image_of_isLocalDiffeomorphAt hNo fun z hz => S.isLocalDiffeomorphAt_fold hz.2
  have hnot : ¬ S.fold '' N ⊆ S.seamTorusSet := by
    intro hsub
    have := interior_maximal hsub himg
    rw [S.interior_seamTorusSet] at this
    exact (hNne.image _).ne_empty (subset_empty_iff.mp this)
  obtain ⟨_, ⟨y, hyN, rfl⟩, hyZ⟩ := not_subset.mp hnot
  obtain ⟨p, hpV, hp⟩ := hyN.1.2
  have hps : p.2 ≠ 0 := by
    intro hp0
    apply hyZ
    refine mem_iUnion.2 ⟨c, p.1, ?_⟩
    change S.seam c (p.1, 0) = S.fold y
    rw [← hp0, ← hp]
  rcases lt_or_gt_of_ne hps with hneg | hpos
  · have hfy : S.fold (S.leftSweep c p) = S.fold y := by
      rw [S.fold_leftSweep c (hVsub hpV).2 hneg.le, hp]
    rcases S.fold_eq_or_mem hfy with heq | hz
    · exact hUV₁.le_bot ⟨hyN.1.1.1, heq ▸ (hVsub hpV).1.1⟩
    · exact hyZ (hfy ▸ hz)
  · have hfy : S.fold (S.rightSweep c p) = S.fold y := by
      rw [S.fold_rightSweep c (hVsub hpV).2 hpos.le, hp]
    rcases S.fold_eq_or_mem hfy with heq | hz
    · exact hUV₂.le_bot ⟨hyN.1.1.2, heq ▸ (hVsub hpV).1.2⟩
    · exact hyZ (hfy ▸ hz)

theorem fold_eq_fold {x y : S.Cut} (h : S.fold x = S.fold y) :
    x = y ∨ ∃ c t, (x = S.leftPt c t ∧ y = S.rightPt c t) ∨
      (x = S.rightPt c t ∧ y = S.leftPt c t) := by
  rcases S.fold_eq_or_mem h with hxy | hz
  · exact Or.inl hxy
  obtain ⟨c, t, ht⟩ := mem_iUnion.1 hz
  have hx := S.eq_leftPt_or_eq_rightPt ht.symm
  have hy := S.eq_leftPt_or_eq_rightPt (h ▸ ht.symm)
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨c, t, Or.inl ⟨rfl, rfl⟩⟩
  · exact Or.inr ⟨c, t, Or.inr ⟨rfl, rfl⟩⟩
  · exact Or.inl rfl

end EmbeddedCutSystem

namespace EmbeddedCutSystem

variable {W : CompactCarrier.{u}} {k : CarrierModel} (S : EmbeddedCutSystem W k)

theorem isBoundaryPoint_mk_iff (j : Fin S.count) (q : S.Piece j) :
    k.model.IsBoundaryPoint (⟨j, q⟩ : S.Cut) ↔ k.model.IsBoundaryPoint q := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
    ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, S.isInteriorPoint_mk_iff]

theorem sideTorus_isBoundaryPoint (σ : S.Side) (t : Torus) :
    k.model.IsBoundaryPoint (S.sideTorus σ t) := by
  rw [sideTorus, sideCollar_apply, isBoundaryPoint_mk_iff]
  change S.collar σ.1 σ.2 (t, halfZero) ∈ k.model.boundary (S.Piece σ.1)
  rw [S.boundary_exhausted]
  exact mem_iUnion.2 ⟨σ.2, t, rfl⟩

theorem exists_sideTorus_of_isBoundaryPoint {x : S.Cut} (hx : k.model.IsBoundaryPoint x) :
    ∃ σ t, S.sideTorus σ t = x := by
  obtain ⟨j, q⟩ := x
  have hq : q ∈ k.model.boundary (S.Piece j) := (S.isBoundaryPoint_mk_iff j q).mp hx
  rw [S.boundary_exhausted] at hq
  obtain ⟨l, t, ht⟩ := mem_iUnion.1 hq
  refine ⟨⟨j, l⟩, t, ?_⟩
  rw [sideTorus, sideCollar_apply]
  exact Sigma.ext rfl (heq_of_eq ht)

theorem sideCollar_isInteriorPoint (σ : S.Side) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) (h0 : 0 < p.2.val 0) :
    k.model.IsInteriorPoint (S.sideCollar σ p) := by
  have hloc := (S.sideCollar σ).isLocalDiffeomorphAt halfCollarModel k.model ∞
    ((S.sideCollar_source σ).symm ▸ hp)
  exact (hloc.isInteriorPoint_iff (by simp)).mp (halfCollarModel_isInteriorPoint' h0)

theorem eq_halfZero_of_isBoundaryPoint (σ : S.Side) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) (hb : k.model.IsBoundaryPoint (S.sideCollar σ p)) :
    p = (p.1, halfZero) := by
  rcases eq_or_lt_of_le p.2.property with h0 | h0
  · exact Prod.ext rfl (halfPoint_eq_self p.2 le_rfl h0).symm
  · exact absurd (S.sideCollar_isInteriorPoint σ hp h0)
      ((ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint _).mp hb)

theorem side_or_external (σ : S.Side) :
    (∃ c b, S.side c b = σ) ∨ ∃ i, S.externalSide i = σ := by
  obtain ⟨a, ha⟩ := S.sides_bijective.2 σ
  rcases a with ⟨c, b⟩ | i
  · exact Or.inl ⟨c, b, ha⟩
  · exact Or.inr ⟨i, ha⟩

theorem fold_sideCollar_eq {σ σ' : S.Side} {p p' : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) (hp' : p' ∈ halfCollarSource)
    (h : S.fold (S.sideCollar σ p) = S.fold (S.sideCollar σ' p')) :
    (σ = σ' ∧ p = p') ∨ ∃ c b, σ = S.side c b ∧ σ' = S.side c (!b) := by
  rcases S.fold_eq_fold h with he | ⟨c, t, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · exact Or.inl (S.sideCollar_inj hp hp' he)
  · have hb : k.model.IsBoundaryPoint (S.sideCollar σ p) := by
      rw [h1]
      exact S.sideTorus_isBoundaryPoint _ t
    have hb' : k.model.IsBoundaryPoint (S.sideCollar σ' p') := by
      rw [h2]
      exact S.sideTorus_isBoundaryPoint _ _
    have e1 : S.sideTorus σ p.1 = S.sideTorus (S.side c true) t := by
      rw [sideTorus, ← S.eq_halfZero_of_isBoundaryPoint σ hp hb]
      exact h1
    have e2 : S.sideTorus σ' p'.1 = S.sideTorus (S.side c false) (S.matching c t) := by
      rw [sideTorus, ← S.eq_halfZero_of_isBoundaryPoint σ' hp' hb']
      exact h2
    exact Or.inr ⟨c, true, (S.sideTorus_eq_sideTorus e1).1, (S.sideTorus_eq_sideTorus e2).1⟩
  · have hb : k.model.IsBoundaryPoint (S.sideCollar σ p) := by
      rw [h1]
      exact S.sideTorus_isBoundaryPoint _ _
    have hb' : k.model.IsBoundaryPoint (S.sideCollar σ' p') := by
      rw [h2]
      exact S.sideTorus_isBoundaryPoint _ t
    have e1 : S.sideTorus σ p.1 = S.sideTorus (S.side c false) (S.matching c t) := by
      rw [sideTorus, ← S.eq_halfZero_of_isBoundaryPoint σ hp hb]
      exact h1
    have e2 : S.sideTorus σ' p'.1 = S.sideTorus (S.side c true) t := by
      rw [sideTorus, ← S.eq_halfZero_of_isBoundaryPoint σ' hp' hb']
      exact h2
    exact Or.inr ⟨c, false, (S.sideTorus_eq_sideTorus e1).1, (S.sideTorus_eq_sideTorus e2).1⟩

theorem surjective_fold : Surjective S.fold := fun w => by
  have hw : w ∈ ⋃ j, range (S.map j) := S.covers ▸ mem_univ w
  obtain ⟨j, q, hq⟩ := mem_iUnion.1 hw
  exact ⟨⟨j, q⟩, hq⟩

def sideParam (σ : S.Side) : Torus ≃ₜ range (S.sideTorus σ) :=
  ((S.continuous_sideTorus σ).isClosedEmbedding (S.injective_sideTorus σ)).isEmbedding.toHomeomorph

theorem sideParam_apply (σ : S.Side) (t : Torus) : (S.sideParam σ t : S.Cut) = S.sideTorus σ t :=
  rfl

def attaching (c : Fin S.seamCount) :
    range (S.sideTorus (S.side c true)) ≃ₜ range (S.sideTorus (S.side c false)) :=
  (S.sideParam _).symm.trans ((S.matching c).toHomeomorph.trans (S.sideParam _))

theorem attaching_sideParam (c : Fin S.seamCount) (t : Torus) :
    S.attaching c (S.sideParam _ t) = S.sideParam _ (S.matching c t) := by
  simp [attaching]

def gluing : BoundaryGluing S.Cut (Fin S.seamCount) where
  left c := range (S.sideTorus (S.side c true))
  right c := range (S.sideTorus (S.side c false))
  attaching c := S.attaching c
  isClosed_left _ := isClosed_range_of_continuous_of_compactSpace (S.continuous_sideTorus _)
  isClosed_right _ := isClosed_range_of_continuous_of_compactSpace (S.continuous_sideTorus _)
  disjoint_left_right c := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, rfl⟩ ⟨s, hs⟩
    exact S.side_ne c (S.sideTorus_eq_sideTorus hs).1.symm
  disjoint_blocks c d hcd := by
    rw [Set.disjoint_left]
    rintro _ (⟨t, rfl⟩ | ⟨t, rfl⟩) (⟨s, hs⟩ | ⟨s, hs⟩) <;>
      exact hcd (S.side_eq_side_iff.mp (S.sideTorus_eq_sideTorus hs).1).1.symm

theorem fold_eq_of_rel {x y : S.Cut} (h : S.gluing.rel x y) : S.fold x = S.fold y := by
  rcases h with rfl | ⟨c, hx, rfl⟩
  · rfl
  · rcases hx with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [S.gluing.flip_of_mem_left ⟨t, rfl⟩]
      change S.fold (S.sideTorus _ t) = S.fold (S.attaching c (S.sideParam _ t) : S.Cut)
      rw [S.attaching_sideParam, sideParam_apply]
      exact (S.fold_leftPt c t).trans (S.fold_rightPt c t).symm
    · rw [S.gluing.flip_of_mem_right ⟨t, rfl⟩]
      have he : (⟨S.sideTorus (S.side c false) t, ⟨t, rfl⟩⟩ :
          range (S.sideTorus (S.side c false))) =
          S.attaching c (S.sideParam _ ((S.matching c).symm t)) := by
        rw [S.attaching_sideParam, Diffeomorph.apply_symm_apply]
        rfl
      change S.fold (S.sideTorus _ t) = S.fold ((S.attaching c).symm ⟨_, ⟨t, rfl⟩⟩ : S.Cut)
      rw [he, Homeomorph.symm_apply_apply, sideParam_apply]
      have h1 := S.fold_leftPt c ((S.matching c).symm t)
      have h2 := S.fold_rightPt c ((S.matching c).symm t)
      rw [rightPt, Diffeomorph.apply_symm_apply] at h2
      exact h2.trans h1.symm

theorem rel_of_fold_eq {x y : S.Cut} (h : S.fold x = S.fold y) : S.gluing.rel x y := by
  rcases S.fold_eq_fold h with rfl | ⟨c, t, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  · exact Or.inl rfl
  · refine Or.inr ⟨c, Or.inl ⟨t, rfl⟩, ?_⟩
    change S.rightPt c t = S.gluing.flip c (S.sideTorus (S.side c true) t)
    rw [S.gluing.flip_of_mem_left ⟨t, rfl⟩]
    change S.rightPt c t = (S.attaching c (S.sideParam _ t) : S.Cut)
    rw [S.attaching_sideParam]
    rfl
  · refine Or.inr ⟨c, Or.inr ⟨S.matching c t, rfl⟩, ?_⟩
    change S.leftPt c t = S.gluing.flip c (S.sideTorus (S.side c false) (S.matching c t))
    rw [S.gluing.flip_of_mem_right ⟨S.matching c t, rfl⟩]
    change S.leftPt c t = ((S.attaching c).symm (S.sideParam _ (S.matching c t)) : S.Cut)
    rw [← S.attaching_sideParam, Homeomorph.symm_apply_apply]
    rfl

theorem orientation_map_cutOrientation (x : S.Cut) :
    Orientation.map (Fin 3) (Manifold.differentialEquivOfBijective k.model W.model S.fold
      S.mfderiv_fold_bijective x).toLinearEquiv (S.cutOrientation.orientation x) =
      W.orientation.orientation (S.fold x) :=
  Manifold.orientation_map_manifoldOrientationPullback k.model W.model
    finrank_euclideanSpace_fin
    S.fold S.contMDiff_fold S.mfderiv_fold_bijective W.orientation x

def rightMatched (c : Fin S.seamCount) :
    PartialDiffeomorph halfCollarModel k.model (Torus × EuclideanHalfSpace 1) S.Cut ∞ :=
  ((S.matching c).prodCongr
    (Diffeomorph.refl (𝓡∂ 1) (EuclideanHalfSpace 1) ∞)).toPartialDiffeomorph.trans
      (S.sideCollar (S.side c false))

theorem halfCollarHeight_mem_seam_source (c : Fin S.seamCount) (t : Torus) :
    halfCollarHeight (t, halfZero) ∈ (S.seam c).source := by
  rw [S.seam_source]
  change -1 < halfZero.val 0 ∧ halfZero.val 0 < 1
  rw [show halfZero.val 0 = 0 from rfl]
  norm_num

theorem fold_leftCollar_eventuallyEq (c : Fin S.seamCount) (t : Torus) :
    S.fold ∘ S.sideCollar (S.side c true) =ᶠ[𝓝 (t, halfZero)]
      S.seam c ∘ seamReflection ∘ halfCollarHeight := by
  filter_upwards [isOpen_halfCollarSource'.mem_nhds (zero_mem_halfCollarSource' t)] with q hq
  exact S.fold_leftCollar c hq

theorem fold_rightMatched_eventuallyEq (c : Fin S.seamCount) (t : Torus) :
    S.fold ∘ S.rightMatched c =ᶠ[𝓝 (t, halfZero)] S.seam c ∘ halfCollarHeight := by
  filter_upwards [isOpen_halfCollarSource'.mem_nhds (zero_mem_halfCollarSource' t)] with q hq
  exact S.fold_rightCollar c hq

theorem mfderiv_seam_congr (c : Fin S.seamCount) (y₁ y₂ : Torus × ℝ) (h : y₁ = y₂)
    (w : TangentSpace signedCollarModel y₁) :
    mfderiv signedCollarModel W.model (S.seam c) y₁ w =
      mfderiv signedCollarModel W.model (S.seam c) y₂ w := by
  subst h
  rfl

theorem mfderiv_fold_leftCollar_apply (c : Fin S.seamCount) (t : Torus)
    (v : TangentSpace halfCollarModel ((t, halfZero) : Torus × EuclideanHalfSpace 1)) :
    mfderiv k.model W.model S.fold (S.sideCollar (S.side c true) (t, halfZero))
      (mfderiv halfCollarModel k.model (S.sideCollar (S.side c true)) (t, halfZero) v) =
      mfderiv signedCollarModel W.model (S.seam c) (halfCollarHeight (t, halfZero))
        (mfderiv signedCollarModel signedCollarModel seamReflection
          (halfCollarHeight (t, halfZero))
          (mfderiv halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) v)) := by
  have hq0 : ((t, halfZero) : Torus × EuclideanHalfSpace 1) ∈
      (S.sideCollar (S.side c true)).source := by
    rw [S.sideCollar_source]
    exact zero_mem_halfCollarSource' t
  have hy0 := S.halfCollarHeight_mem_seam_source c t
  have hfold : MDifferentiableAt k.model W.model S.fold
      (S.sideCollar (S.side c true) (t, halfZero)) :=
    S.contMDiff_fold.mdifferentiableAt (by simp)
  have hl : MDifferentiableAt halfCollarModel k.model (S.sideCollar (S.side c true))
      (t, halfZero) :=
    (S.sideCollar _).mdifferentiableAt (by simp) hq0
  have hj : MDifferentiableAt halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) :=
    contMDiff_halfCollarHeight.mdifferentiableAt (by simp)
  have hρ : MDifferentiableAt signedCollarModel signedCollarModel seamReflection
      (halfCollarHeight (t, halfZero)) :=
    contMDiff_seamReflection.mdifferentiableAt (by simp)
  have hS : MDifferentiableAt signedCollarModel W.model (S.seam c)
      (seamReflection (halfCollarHeight (t, halfZero))) := by
    rw [seamReflection_halfCollarHeight_zero]
    exact (S.seam c).mdifferentiableAt (by simp) hy0
  have e1 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hfold hl) v
  have e2 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hS (hρ.comp (t, halfZero) hj)) v
  have e3 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hρ hj) v
  have e4 := DFunLike.congr_fun (Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel)
    (I' := W.model) (S.fold_leftCollar_eventuallyEq c t)) v
  exact ((e1.symm.trans e4).trans e2).trans ((congrArg (mfderiv signedCollarModel W.model
    (S.seam c) (seamReflection (halfCollarHeight (t, halfZero)))) e3).trans
      (S.mfderiv_seam_congr c _ _ (seamReflection_halfCollarHeight_zero t) _))

theorem mfderiv_fold_rightMatched_apply (c : Fin S.seamCount) (t : Torus)
    (v : TangentSpace halfCollarModel ((t, halfZero) : Torus × EuclideanHalfSpace 1)) :
    mfderiv k.model W.model S.fold (S.rightMatched c (t, halfZero))
      (mfderiv halfCollarModel k.model (S.rightMatched c) (t, halfZero) v) =
      mfderiv signedCollarModel W.model (S.seam c) (halfCollarHeight (t, halfZero))
        (mfderiv halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) v) := by
  have hq0 : ((t, halfZero) : Torus × EuclideanHalfSpace 1) ∈ (S.rightMatched c).source := by
    refine ⟨mem_univ _, ?_⟩
    change (S.matching c t, halfZero) ∈ (S.sideCollar (S.side c false)).source
    rw [S.sideCollar_source]
    exact zero_mem_halfCollarSource' _
  have hy0 := S.halfCollarHeight_mem_seam_source c t
  have hfold : MDifferentiableAt k.model W.model S.fold (S.rightMatched c (t, halfZero)) :=
    S.contMDiff_fold.mdifferentiableAt (by simp)
  have hr : MDifferentiableAt halfCollarModel k.model (S.rightMatched c) (t, halfZero) :=
    (S.rightMatched c).mdifferentiableAt (by simp) hq0
  have hj : MDifferentiableAt halfCollarModel signedCollarModel halfCollarHeight (t, halfZero) :=
    contMDiff_halfCollarHeight.mdifferentiableAt (by simp)
  have hS : MDifferentiableAt signedCollarModel W.model (S.seam c)
      (halfCollarHeight (t, halfZero)) :=
    (S.seam c).mdifferentiableAt (by simp) hy0
  have e1 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hfold hr) v
  have e2 := DFunLike.congr_fun (mfderiv_comp (t, halfZero) hS hj) v
  have e4 := DFunLike.congr_fun (Filter.EventuallyEq.mfderiv_eq (I := halfCollarModel)
    (I' := W.model) (S.fold_rightMatched_eventuallyEq c t)) v
  exact (e1.symm.trans e4).trans e2

theorem reversing (c : Fin S.seamCount) :
    ReversesBoundaryOrientation S.cutCarrier (S.sideCollar (S.side c true))
      (fun p => S.sideCollar (S.side c false) (S.matching c p.1, p.2)) := by
  intro t
  let q0 : Torus × EuclideanHalfSpace 1 := (t, halfZero)
  have hq0l : q0 ∈ (S.sideCollar (S.side c true)).source := by
    rw [S.sideCollar_source]
    exact zero_mem_halfCollarSource' t
  have hq0r : q0 ∈ (S.rightMatched c).source := by
    refine ⟨mem_univ _, ?_⟩
    change (S.matching c t, halfZero) ∈ (S.sideCollar (S.side c false)).source
    rw [S.sideCollar_source]
    exact zero_mem_halfCollarSource' _
  have hl := (S.sideCollar (S.side c true)).isLocalDiffeomorphAt halfCollarModel k.model ∞ hq0l
  have hr := (S.rightMatched c).isLocalDiffeomorphAt halfCollarModel k.model ∞ hq0r
  let L := (hl.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let R := (hr.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  refine ⟨L, R, fun v => rfl, fun v => rfl, ?_⟩
  let D : (x : S.Cut) → EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    fun x => (Manifold.differentialEquivOfBijective k.model W.model S.fold
      S.mfderiv_fold_bijective x).toLinearEquiv
  have hO : ∀ x : S.Cut, S.cutOrientation.orientation x =
      Orientation.map (Fin 3) (D x).symm (W.orientation.orientation (S.fold x)) := by
    intro x
    rw [← S.orientation_map_cutOrientation x]
    exact (Equiv.symm_apply_apply (Orientation.map (Fin 3) (D x)) _).symm
  let y0 : Torus × ℝ := halfCollarHeight q0
  have hS := (S.seam c).isLocalDiffeomorphAt signedCollarModel W.model ∞
    (S.halfCollarHeight_mem_seam_source c t)
  let dS := (hS.mfderivToContinuousLinearEquiv (by simp)).toLinearEquiv
  let A := L.trans (D (S.sideCollar (S.side c true) q0))
  let B := R.trans (D (S.rightMatched c q0))
  let J := B.trans dS.symm
  let P : (TangentSpace signedCollarModel y0) →ₗ[ℝ] (TangentSpace signedCollarModel y0) :=
    (LinearMap.id : (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) →ₗ[ℝ] _).prodMap
      (-LinearMap.id : ℝ →ₗ[ℝ] ℝ)
  have hJ : ∀ v, J v = mfderiv halfCollarModel signedCollarModel halfCollarHeight q0 v := by
    intro v
    apply dS.injective
    exact (dS.apply_symm_apply (B v)).trans (S.mfderiv_fold_rightMatched_apply c t v)
  have hdet : LinearMap.det ((A.trans B.symm : _ ≃ₗ[ℝ] _) :
      TangentSpace halfCollarModel q0 →ₗ[ℝ] TangentSpace halfCollarModel q0) < 0 := by
    let Sₗ : TangentSpace signedCollarModel y0 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) := dS.toLinearMap
    rw [det_trans_symm_eq_det A B J P Sₗ]
    · rw [show LinearMap.det P = -1 from
        det_prodMap_id_neg (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))]
      norm_num
    · intro v
      change D (S.sideCollar (S.side c true) q0) (L v) = Sₗ (P (J v))
      rw [hJ]
      exact (S.mfderiv_fold_leftCollar_apply c t v).trans
        (congrArg Sₗ (mfderiv_seamReflection_apply _ _))
    · intro v
      change D (S.rightMatched c q0) (R v) = Sₗ (J v)
      rw [hJ]
      exact S.mfderiv_fold_rightMatched_apply c t v
  have hpt : S.fold (S.rightMatched c q0) = S.fold (S.sideCollar (S.side c true) q0) :=
    (S.fold_rightPt c t).trans (S.fold_leftPt c t).symm
  have hOS : ∀ p₁ p₂ : W.Carrier, p₁ = p₂ →
      W.orientation.orientation p₁ = W.orientation.orientation p₂ := by
    rintro _ _ rfl
    rfl
  change Orientation.map (Fin 3) L.symm
      (S.cutOrientation.orientation (S.sideCollar (S.side c true) q0)) =
    -Orientation.map (Fin 3) R.symm
      (S.cutOrientation.orientation (S.rightMatched c q0))
  rw [hO, hO, hOS _ _ hpt]
  let o := W.orientation.orientation (S.fold (S.sideCollar (S.side c true) q0))
  have key := orientation_map_symm_eq_neg_of_det_neg (finrank_halfCollarTangent q0) A B o hdet
  have hA' : A.symm = (D (S.sideCollar (S.side c true) q0)).symm.trans L.symm :=
    LinearEquiv.ext fun _ => rfl
  have hB' : B.symm = (D (S.rightMatched c q0)).symm.trans R.symm :=
    LinearEquiv.ext fun _ => rfl
  rw [hA', hB'] at key
  exact (DifferentialGeometry.orientation_map_trans (D (S.sideCollar (S.side c true) q0)).symm
    L.symm o).symm.trans (key.trans (congrArg Neg.neg (DifferentialGeometry.orientation_map_trans
      (D (S.rightMatched c q0)).symm R.symm o)))

def pairing : TorusPairing S.cutCarrier where
  count := S.seamCount
  gluing := S.gluing
  leftParam c := S.sideParam (S.side c true)
  rightParam c := S.sideParam (S.side c false)
  matching := S.matching
  matching_eq c t := S.attaching_sideParam c t
  leftCollar c := S.sideCollar (S.side c true)
  rightCollar c := S.sideCollar (S.side c false)
  left_source _ := S.sideCollar_source _
  right_source _ := S.sideCollar_source _
  left_zero _ _ := rfl
  right_zero _ _ := rfl
  reversing c := S.reversing c

end EmbeddedCutSystem


namespace EmbeddedCutSystem

variable {W : CompactCarrier.{u}} {k : CarrierModel} (S : EmbeddedCutSystem W k)

theorem sideCollar_target_disjoint {σ σ' : S.Side} (h : σ ≠ σ') :
    Disjoint (S.sideCollar σ).target (S.sideCollar σ').target := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨p, hp, rfl⟩ := exists_eq_of_mem_target_of_source_eq (C := S.cutCarrier)
    (S.sideCollar σ)
    (S.sideCollar_source σ) hx
  obtain ⟨p', hp', hpp⟩ := exists_eq_of_mem_target_of_source_eq (C := S.cutCarrier)
    (S.sideCollar σ')
    (S.sideCollar_source σ') hx'
  exact h (S.sideCollar_inj hp hp' hpp.symm).1

theorem isLocalDiffeomorphAt_fold_external (i : Fin S.externalCount) (t : Torus) :
    IsLocalDiffeomorphAt k.model W.model ∞ S.fold (S.sideTorus (S.externalSide i) t) := by
  have hmk := isLocalDiffeomorph_sigmaMk (I := k.model) (n := ∞) (M := S.Piece)
    (S.externalSide i).1 (S.collar _ (S.externalSide i).2 (t, halfZero))
  have h := DifferentialGeometry.isLocalDiffeomorphAt_of_comp (g := S.fold)
    (S.external_local i t) hmk
  rw [sideTorus, sideCollar_apply]
  exact h

theorem isLocalDiffeomorphAt_externalMap (i : Fin S.externalCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    IsLocalDiffeomorphAt halfCollarModel W.model ∞
      (S.fold ∘ S.sideCollar (S.externalSide i)) p := by
  have hc := (S.sideCollar (S.externalSide i)).isLocalDiffeomorphAt halfCollarModel k.model ∞
    ((S.sideCollar_source _).symm ▸ hp)
  rcases eq_or_lt_of_le p.2.property with h0 | h0
  · have hpz : p = (p.1, halfZero) := Prod.ext rfl (halfPoint_eq_self p.2 le_rfl h0).symm
    have hf : IsLocalDiffeomorphAt k.model W.model ∞ S.fold
        (S.sideCollar (S.externalSide i) p) := by
      rw [hpz]
      exact S.isLocalDiffeomorphAt_fold_external i p.1
    exact hc.comp W.model W.Carrier hf
  · exact hc.comp W.model W.Carrier
      (S.isLocalDiffeomorphAt_fold (S.sideCollar_isInteriorPoint _ hp h0))

theorem injOn_externalMap (i : Fin S.externalCount) :
    InjOn (S.fold ∘ S.sideCollar (S.externalSide i)) halfCollarSource := by
  intro p hp p' hp' h
  rcases S.fold_sideCollar_eq hp hp' h with ⟨-, h2⟩ | ⟨c, b, h1, -⟩
  · exact h2
  · exact absurd h1.symm (S.side_ne_externalSide c b i)

theorem exists_externalCollar (i : Fin S.externalCount) :
    ∃ Φ : PartialDiffeomorph halfCollarModel W.model (Torus × EuclideanHalfSpace 1) W.Carrier ∞,
      Φ.toPartialEquiv.source = halfCollarSource ∧
        Φ.toPartialEquiv.target = (S.fold ∘ S.sideCollar (S.externalSide i)) '' halfCollarSource ∧
          Φ.toFun = S.fold ∘ S.sideCollar (S.externalSide i) :=
  IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
    (fun p => S.isLocalDiffeomorphAt_externalMap i p.property) isOpen_halfCollarSource'
    ⟨_, zero_mem_halfCollarSource' 1⟩ (S.injOn_externalMap i)

def externalCollar (i : Fin S.externalCount) :
    PartialDiffeomorph halfCollarModel W.model (Torus × EuclideanHalfSpace 1) W.Carrier ∞ :=
  Classical.choose (S.exists_externalCollar i)

theorem externalCollar_source (i : Fin S.externalCount) :
    (S.externalCollar i).source = halfCollarSource :=
  (Classical.choose_spec (S.exists_externalCollar i)).1

theorem externalCollar_target (i : Fin S.externalCount) :
    (S.externalCollar i).target =
      (S.fold ∘ S.sideCollar (S.externalSide i)) '' halfCollarSource :=
  (Classical.choose_spec (S.exists_externalCollar i)).2.1

theorem externalCollar_apply (i : Fin S.externalCount) (p : Torus × EuclideanHalfSpace 1) :
    S.externalCollar i p = S.fold (S.sideCollar (S.externalSide i) p) :=
  congrFun (Classical.choose_spec (S.exists_externalCollar i)).2.2 p

theorem fold_isInteriorPoint {x : S.Cut} (hx : k.model.IsInteriorPoint x) :
    W.model.IsInteriorPoint (S.fold x) :=
  ((S.isLocalDiffeomorphAt_fold hx).isInteriorPoint_iff (by simp)).mp hx

theorem fold_external_isBoundaryPoint (i : Fin S.externalCount) (t : Torus) :
    W.model.IsBoundaryPoint (S.fold (S.sideTorus (S.externalSide i) t)) := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint]
  intro h
  exact (ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint _).mp
    (S.sideTorus_isBoundaryPoint _ t)
    (((S.isLocalDiffeomorphAt_fold_external i t).isInteriorPoint_iff (by simp)).mpr h)

theorem externalCollar_disjoint :
    Pairwise fun i j => Disjoint (S.externalCollar i).target (S.externalCollar j).target := by
  intro i j hij
  rw [Set.disjoint_left, S.externalCollar_target, S.externalCollar_target]
  rintro _ ⟨p, hp, rfl⟩ ⟨p', hp', h⟩
  rcases S.fold_sideCollar_eq hp hp' h.symm with ⟨h1, -⟩ | ⟨c, b, h1, -⟩
  · exact hij (S.externalSide_injective h1)
  · exact S.side_ne_externalSide c b i h1.symm

def externalTori : BoundaryTori W S.externalCount where
  collar := S.externalCollar
  source_eq := S.externalCollar_source
  boundary_zero i t := by
    rw [S.externalCollar_apply]
    exact S.fold_external_isBoundaryPoint i t
  disjoint := S.externalCollar_disjoint

def cutExternal : BoundaryTori S.cutCarrier S.externalCount where
  collar i := S.sideCollar (S.externalSide i)
  source_eq _ := S.sideCollar_source _
  boundary_zero _ t := S.sideTorus_isBoundaryPoint _ t
  disjoint _ _ hij := S.sideCollar_target_disjoint fun h => hij (S.externalSide_injective h)

theorem fold_seamSide_mem_interior (c : Fin S.seamCount) (b : Bool) (t : Torus) :
    S.fold (S.sideTorus (S.side c b) t) ∈ W.interior := by
  cases b
  · have h := S.fold_rightPt c ((S.matching c).symm t)
    rw [rightPt, Diffeomorph.apply_symm_apply] at h
    rw [h]
    exact S.seam_interior c ((S.seam c).map_source
      ((S.seam_source c).symm ▸ ⟨by norm_num, by norm_num⟩))
  · rw [show S.sideTorus (S.side c true) t = S.leftPt c t from rfl, S.fold_leftPt]
    exact S.seam_interior c ((S.seam c).map_source
      ((S.seam_source c).symm ▸ ⟨by norm_num, by norm_num⟩))

theorem boundary_eq_externalImage :
    W.model.boundary W.Carrier = S.externalTori.image := by
  ext w
  constructor
  · intro hw
    obtain ⟨x, rfl⟩ := S.surjective_fold w
    have hx : k.model.IsBoundaryPoint x := by
      rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint]
      intro hint
      exact (W.model.isBoundaryPoint_iff_not_isInteriorPoint _).mp hw (S.fold_isInteriorPoint hint)
    obtain ⟨σ, t, rfl⟩ := S.exists_sideTorus_of_isBoundaryPoint hx
    rcases S.side_or_external σ with ⟨c, b, rfl⟩ | ⟨i, rfl⟩
    · exact absurd (S.fold_seamSide_mem_interior c b t)
        ((W.model.isBoundaryPoint_iff_not_isInteriorPoint _).mp hw)
    · exact mem_iUnion.2 ⟨i, t, S.externalCollar_apply i _⟩
  · intro hw
    obtain ⟨i, t, rfl⟩ := mem_iUnion.1 hw
    exact S.externalTori.boundary_zero i t

theorem cut_boundary_eq : k.model.boundary S.Cut =
    (⋃ c, S.gluing.block c) ∪ S.cutExternal.image := by
  ext x
  constructor
  · intro hx
    obtain ⟨σ, t, rfl⟩ := S.exists_sideTorus_of_isBoundaryPoint hx
    rcases S.side_or_external σ with ⟨c, b, rfl⟩ | ⟨i, rfl⟩
    · refine Or.inl (mem_iUnion.2 ⟨c, ?_⟩)
      cases b
      · exact Or.inr ⟨t, rfl⟩
      · exact Or.inl ⟨t, rfl⟩
    · exact Or.inr (mem_iUnion.2 ⟨i, t, rfl⟩)
  · rintro (hx | hx)
    · obtain ⟨c, (⟨t, rfl⟩ | ⟨t, rfl⟩)⟩ := mem_iUnion.1 hx <;>
        exact S.sideTorus_isBoundaryPoint _ t
    · obtain ⟨i, t, rfl⟩ := mem_iUnion.1 hx
      exact S.sideTorus_isBoundaryPoint _ t

theorem external_disjoint_blocks :
    Disjoint (⋃ c, S.gluing.block c) S.cutExternal.image := by
  rw [Set.disjoint_left]
  intro x hx hx'
  obtain ⟨i, t', rfl⟩ := mem_iUnion.1 hx'
  obtain ⟨c, (⟨t, ht⟩ | ⟨t, ht⟩)⟩ := mem_iUnion.1 hx
  · exact S.side_ne_externalSide c true i (S.sideTorus_eq_sideTorus ht).1
  · exact S.side_ne_externalSide c false i (S.sideTorus_eq_sideTorus ht).1

def quotientFold : S.pairing.QuotientSpace → W.Carrier :=
  Quotient.lift S.fold fun _ _ h => S.fold_eq_of_rel h

theorem bijective_quotientFold : Bijective S.quotientFold := by
  constructor
  · intro q q' h
    induction q using Quotient.inductionOn with
    | h x =>
      induction q' using Quotient.inductionOn with
      | h y => exact Quotient.sound (S.rel_of_fold_eq h)
  · intro w
    obtain ⟨x, hx⟩ := S.surjective_fold w
    exact ⟨Quotient.mk _ x, hx⟩

def reconstruction : S.pairing.QuotientSpace ≃ₜ W.Carrier :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ S.bijective_quotientFold)
    (continuous_quot_lift _ S.contMDiff_fold.continuous)

theorem reconstruction_quotientMap (x : S.Cut) :
    S.reconstruction (S.pairing.quotientMap x) = S.fold x := rfl

def interiorImage : TopologicalSpace.Opens W.Carrier :=
  ⟨S.fold '' S.cutCarrier.interior,
    isOpen_image_of_isLocalDiffeomorphAt S.cutCarrier.interior.isOpen
      fun _ hx => S.isLocalDiffeomorphAt_fold hx⟩

def interiorMap (x : S.cutCarrier.interior) : S.interiorImage :=
  ⟨S.fold x.val, x.val, x.property, rfl⟩

theorem isLocalDiffeomorph_interiorMap :
    IsLocalDiffeomorph k.model W.model ∞ S.interiorMap := by
  intro x
  have hval := DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := k.model)
    S.cutCarrier.interior x
  have h : IsLocalDiffeomorphAt k.model W.model ∞
      (S.fold ∘ (Subtype.val : S.cutCarrier.interior → S.Cut)) x :=
    hval.comp W.model W.Carrier (S.isLocalDiffeomorphAt_fold x.property)
  exact DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict
    (V := S.interiorImage)
    (f := S.fold ∘ (Subtype.val : S.cutCarrier.interior → S.Cut))
    (fun y => ⟨y.val, y.property, rfl⟩) h

theorem bijective_interiorMap : Bijective S.interiorMap := by
  constructor
  · intro x y h
    have h' : S.fold x.val = S.fold y.val := congrArg Subtype.val h
    rcases S.fold_eq_fold h' with hxy | ⟨c, t, ⟨hx, -⟩ | ⟨hx, -⟩⟩
    · exact Subtype.ext hxy
    · exact absurd x.property ((ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint _).mp
        (hx ▸ S.sideTorus_isBoundaryPoint _ t))
    · exact absurd x.property ((ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint _).mp
        (hx ▸ S.sideTorus_isBoundaryPoint _ _))
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

def interiorDiffeomorph :
    S.cutCarrier.interior ≃ₘ⟮k.model, W.model⟯ S.interiorImage :=
  S.isLocalDiffeomorph_interiorMap.diffeomorphOfBijective S.bijective_interiorMap

theorem exists_seamSide {c : Fin S.seamCount} {w : W.Carrier} (hw : w ∈ (S.seam c).target) :
    ∃ b p, p ∈ halfCollarSource ∧ w = S.fold (S.sideCollar (S.side c b) p) := by
  set y := (S.seam c).symm w with hydef
  have hy : y ∈ signedCollarSource := by
    rw [← S.seam_source c]
    exact (S.seam c).map_target hw
  have hw' : S.seam c y = w := (S.seam c).right_inv hw
  rcases le_total y.2 0 with h0 | h0
  · refine ⟨true, (y.1, halfPoint (-y.2) (neg_nonneg.2 h0)), ?_, ?_⟩
    · change -y.2 < 1
      linarith [hy.1]
    · rw [S.fold_sideCollar, ← S.seam_neg c y.1 y.2 h0 hy.1]
      exact hw'.symm
  · refine ⟨false, (S.matching c y.1, halfPoint y.2 h0), hy.2, ?_⟩
    rw [S.fold_sideCollar, ← S.seam_pos c y.1 y.2 h0 hy.2]
    exact hw'.symm

theorem seam_disjoint : Pairwise fun c d => Disjoint (S.seam c).target (S.seam d).target := by
  intro c d hcd
  rw [Set.disjoint_left]
  intro w hc hd
  obtain ⟨b, p, hp, rfl⟩ := S.exists_seamSide hc
  obtain ⟨b', p', hp', h⟩ := S.exists_seamSide hd
  rcases S.fold_sideCollar_eq hp hp' h with ⟨h1, -⟩ | ⟨e, a, h1, h2⟩
  · exact hcd (S.side_eq_side_iff.mp h1).1
  · exact hcd ((S.side_eq_side_iff.mp h1).1.trans (S.side_eq_side_iff.mp h2).1.symm)

theorem external_seam_disjoint (i : Fin S.externalCount) (c : Fin S.seamCount) :
    Disjoint (S.externalCollar i).target (S.seam c).target := by
  rw [Set.disjoint_left, S.externalCollar_target]
  rintro _ ⟨p, hp, rfl⟩ hc
  obtain ⟨b', p', hp', h⟩ := S.exists_seamSide hc
  rcases S.fold_sideCollar_eq hp hp' h with ⟨h1, -⟩ | ⟨e, a, h1, -⟩
  · exact S.side_ne_externalSide c b' i h1.symm
  · exact S.side_ne_externalSide e a i h1.symm

def toTorusPresentation : TorusPresentation W where
  cutCarrier := S.cutCarrier
  components := S.components
  pairing := S.pairing
  externalCount := S.externalCount
  external := S.externalTori
  cutExternal := S.cutExternal
  external_exhausted := S.boundary_eq_externalImage
  cut_boundary_exhausted := S.cut_boundary_eq
  external_disjoint := S.external_disjoint_blocks
  reconstruction := S.reconstruction
  quotient_smooth := S.contMDiff_fold
  quotient_oriented x := ⟨(Manifold.differentialEquivOfBijective k.model W.model S.fold
      S.mfderiv_fold_bijective x).toLinearEquiv, fun _ => rfl, S.orientation_map_cutOrientation x⟩
  interiorImage := S.interiorImage
  interiorDiffeomorph := S.interiorDiffeomorph
  interior_map _ := rfl
  seam := S.seam
  seam_source := S.seam_source
  seam_zero c t := (S.fold_leftPt c t).symm
  seam_positive c t s hs h1 := by
    rw [S.seam_pos c t s hs h1]
    exact (S.fold_sideCollar _ _).symm
  seam_negative c t s hs h1 := by
    rw [S.seam_neg c t s hs h1]
    exact (S.fold_sideCollar _ _).symm
  seam_interior := S.seam_interior
  seam_disjoint := S.seam_disjoint
  marked_collar i p _ := (S.externalCollar_apply i p).symm
  external_seam_disjoint := S.external_seam_disjoint
  leftPiece c := (S.side c true).1
  rightPiece c := (S.side c false).1
  left_owned _ := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, (S.sideCollar_apply _ _).symm⟩
  right_owned _ := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, (S.sideCollar_apply _ _).symm⟩
  externalPiece i := (S.externalSide i).1
  external_owned _ := by
    rintro _ ⟨t, rfl⟩
    exact ⟨_, (S.sideCollar_apply _ _).symm⟩

end EmbeddedCutSystem


namespace EmbeddedCutSystem

variable {W : CompactCarrier.{u}} {k : CarrierModel} (S : EmbeddedCutSystem W k)

@[simp]
theorem toTorusPresentation_externalCount : S.toTorusPresentation.externalCount = S.externalCount :=
  rfl

@[simp]
theorem toTorusPresentation_pairing_count : S.toTorusPresentation.pairing.count = S.seamCount :=
  rfl

@[simp]
theorem toTorusPresentation_components_count :
    S.toTorusPresentation.components.count = S.count :=
  rfl

theorem toTorusPresentation_seam (c : Fin S.seamCount) : S.toTorusPresentation.seam c = S.seam c :=
  rfl

theorem toTorusPresentation_matching (c : Fin S.seamCount) :
    S.toTorusPresentation.pairing.matching c = S.matching c :=
  rfl

theorem toTorusPresentation_cutMap (x : S.Cut) :
    S.toTorusPresentation.reconstruction (S.toTorusPresentation.pairing.quotientMap x) =
      S.fold x :=
  rfl

theorem toTorusPresentation_external_collar (i : Fin S.externalCount)
    (p : Torus × EuclideanHalfSpace 1) :
    S.toTorusPresentation.external.collar i p = S.fold (S.sideCollar (S.externalSide i) p) :=
  S.externalCollar_apply i p

theorem toTorusPresentation_external_zero (i : Fin S.externalCount) (t : Torus) :
    S.toTorusPresentation.external.collar i (t, halfZero) =
      S.map (S.externalSide i).1 (S.collar _ (S.externalSide i).2 (t, halfZero)) :=
  (S.externalCollar_apply i _).trans (S.fold_sideCollar _ _)

def sideOf : S.toTorusPresentation.Side → S.Side
  | .inl c => S.side c true
  | .inr (.inl c) => S.side c false
  | .inr (.inr i) => S.externalSide i

theorem sidePiece_eq (s : S.toTorusPresentation.Side) :
    S.toTorusPresentation.sidePiece s = (S.sideOf s).1 := by
  rcases s with c | c | i <;> rfl

theorem sideCollar_eq (s : S.toTorusPresentation.Side) :
    S.toTorusPresentation.sideCollar s = S.sideCollar (S.sideOf s) := by
  rcases s with c | c | i <;> rfl

theorem bijective_sideOf : Bijective S.sideOf := by
  constructor
  · rintro (c | c | i) (d | d | k) h <;>
      simp only [sideOf] at h
    · rw [(S.side_eq_side_iff.mp h).1]
    · exact absurd (S.side_eq_side_iff.mp h).2 Bool.noConfusion
    · exact absurd h (S.side_ne_externalSide c true k)
    · exact absurd (S.side_eq_side_iff.mp h).2 Bool.noConfusion
    · rw [(S.side_eq_side_iff.mp h).1]
    · exact absurd h (S.side_ne_externalSide c false k)
    · exact absurd h.symm (S.side_ne_externalSide d true i)
    · exact absurd h.symm (S.side_ne_externalSide d false i)
    · rw [S.externalSide_injective h]
  · intro σ
    rcases S.side_or_external σ with ⟨c, b, rfl⟩ | ⟨i, rfl⟩
    · cases b
      · exact ⟨.inr (.inl c), rfl⟩
      · exact ⟨.inl c, rfl⟩
    · exact ⟨.inr (.inr i), rfl⟩

def ownedEquiv (j : Fin S.count) :
    S.toTorusPresentation.OwnedSide j ≃ {σ : S.Side // σ.1 = j} :=
  (Equiv.ofBijective S.sideOf S.bijective_sideOf).subtypeEquiv fun s => by
    rw [S.sidePiece_eq]
    rfl

def port (j : Fin S.count) : Fin (S.torusCount j) ≃ S.toTorusPresentation.OwnedSide j :=
  ((S.ownedEquiv j).trans (Equiv.sigmaSubtype j)).symm

theorem sideOf_port (j : Fin S.count) (l : Fin (S.torusCount j)) :
    S.sideOf (S.port j l).val = ⟨j, l⟩ :=
  congrArg Subtype.val ((S.ownedEquiv j).apply_symm_apply ((Equiv.sigmaSubtype j).symm l))

def pieceMap (j : Fin S.count) (q : S.Piece j) : S.components.piece j := ⟨⟨j, q⟩, q, rfl⟩

theorem isLocalDiffeomorph_pieceMap (j : Fin S.count) :
    IsLocalDiffeomorph k.model k.model ∞ (S.pieceMap j) := fun q =>
  DifferentialGeometry.isLocalDiffeomorphAt_subtypeCodRestrict (V := S.components.piece j)
    (f := Sigma.mk j) (fun q => ⟨q, rfl⟩)
    (isLocalDiffeomorph_sigmaMk (I := k.model) (n := ∞) (M := S.Piece) j q)

theorem bijective_pieceMap (j : Fin S.count) : Bijective (S.pieceMap j) := by
  constructor
  · intro q q' h
    exact sigma_mk_injective (congrArg Subtype.val h)
  · rintro ⟨_, q, rfl⟩
    exact ⟨q, rfl⟩

def pieceDiffeomorph (j : Fin S.count) :
    S.Piece j ≃ₘ⟮k.model, k.model⟯ S.components.piece j :=
  (S.isLocalDiffeomorph_pieceMap j).diffeomorphOfBijective (S.bijective_pieceMap j)

theorem pieceDiffeomorph_apply (j : Fin S.count) (q : S.Piece j) :
    (S.pieceDiffeomorph j q : S.Cut) = ⟨j, q⟩ :=
  rfl

structure ProductCertificate where
  kind_mem : ∀ j, S.torusCount j ∈ ({1, 2, 3} : Finset ℕ)
  base : ∀ j, PlanarBase.{u} (S.torusCount j)
  trivialization : ∀ j, ((base j).surface.Carrier × Circle) ≃ₘ⟮
    (SurfaceModel.model (base j).surface.kind).prod (𝓡 1), k.model⟯ S.Piece j
  collar_eq : ∀ j l p, p ∈ halfCollarSource →
    S.collar j l p = trivialization j ((base j).collar l (p.1.1, p.2), p.1.2)

variable {S}

def ProductCertificate.piece (C : S.ProductCertificate) (j : Fin S.count) :
    ProductFibredPiece S.toTorusPresentation j (S.torusCount j) where
  base := C.base j
  port := S.port j
  trivialization := (C.trivialization j).trans (S.pieceDiffeomorph j)
  collar_eq l p hp := by
    apply Subtype.ext
    refine (TorusPresentation.pieceCollar_apply S.toTorusPresentation j (S.port j l) hp).trans ?_
    rw [S.sideCollar_eq, S.sideOf_port, S.sideCollar_apply, C.collar_eq j l p hp]
    rfl

def toElementaryPresentation (C : S.ProductCertificate) : ElementaryPresentation W where
  toTorus := S.toTorusPresentation
  kind := S.torusCount
  kind_mem := C.kind_mem
  piece := C.piece

@[simp]
theorem toElementaryPresentation_toTorus (C : S.ProductCertificate) :
    (S.toElementaryPresentation C).toTorus = S.toTorusPresentation :=
  rfl

end EmbeddedCutSystem


structure EmbeddedPieceSystem (W : CompactCarrier.{u}) where
  count : ℕ
  count_pos : 0 < count
  kind : Fin count → ℕ
  kind_mem : ∀ j, kind j ∈ ({1, 2, 3} : Finset ℕ)
  base : ∀ j, PlanarBase.{u} (kind j)
  map : ∀ j, (base j).surface.Carrier × Circle → W.Carrier
  smooth : ∀ j, ContMDiff ((SurfaceModel.model (base j).surface.kind).prod (𝓡 1)) W.model ∞
    (map j)
  mfderiv_bijective : ∀ j q, Function.Bijective
    (mfderiv ((SurfaceModel.model (base j).surface.kind).prod (𝓡 1)) W.model (map j) q)
  covers : ⋃ j, range (map j) = univ
  seamCount : ℕ
  side : Fin seamCount → Bool → Σ j, Fin (kind j)
  externalCount : ℕ
  externalSide : Fin externalCount → Σ j, Fin (kind j)
  sides_bijective : Function.Bijective (Sum.elim (Function.uncurry side) externalSide)
  matching : Fin seamCount → (Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
  seam : Fin seamCount → PartialDiffeomorph signedCollarModel W.model (Torus × ℝ) W.Carrier ∞
  seam_source : ∀ c, (seam c).source = signedCollarSource
  seam_neg : ∀ c t s (hs : s ≤ 0), -1 < s → seam c (t, s) =
    map (side c true).1 ((base _).collar (side c true).2
      (t.1, halfPoint (-s) (neg_nonneg.2 hs)), t.2)
  seam_pos : ∀ c t s (hs : 0 ≤ s), s < 1 → seam c (t, s) =
    map (side c false).1 ((base _).collar (side c false).2
      ((matching c t).1, halfPoint s hs), (matching c t).2)
  seam_interior : ∀ c, (seam c).target ⊆ W.interior
  external_local : ∀ i (t : Torus), IsLocalDiffeomorphAt
    ((SurfaceModel.model (base (externalSide i).1).surface.kind).prod (𝓡 1)) W.model ∞
    (map (externalSide i).1) ((base _).collar (externalSide i).2 (t.1, halfZero), t.2)
  overlap : ∀ j j' q q', map j q = map j' q' →
    (⟨j, q⟩ : Σ j, (base j).surface.Carrier × Circle) = ⟨j', q'⟩ ∨
      ∃ c t, map j q = seam c (t, 0)

def cutModelFunction (k : ℕ) (z : ℂ) : ℝ := if k = 1 then sqDist 0 3 z else planarFunction k z

theorem cutModelFunction_eq_of_eq_one {k : ℕ} (hk : k = 1) :
    cutModelFunction k = sqDist 0 3 :=
  funext fun _ => by simp [cutModelFunction, hk]

theorem cutModelFunction_eq_of_ne_one {k : ℕ} (hk : k ≠ 1) :
    cutModelFunction k = planarFunction k :=
  funext fun _ => by simp [cutModelFunction, hk]

theorem contDiff_cutModelFunction (k : ℕ) : ContDiff ℝ ∞ (cutModelFunction k) := by
  by_cases hk : k = 1
  · rw [cutModelFunction_eq_of_eq_one hk]
    exact contDiff_sqDist 0 3
  · rw [cutModelFunction_eq_of_ne_one hk]
    exact contDiff_planarFunction k

theorem cutModelFunction_regular (k : ℕ) {z : ℂ} (hz : cutModelFunction k z = 0) :
    fderiv ℝ (cutModelFunction k) z ≠ 0 := by
  by_cases hk : k = 1
  · rw [cutModelFunction_eq_of_eq_one hk] at hz ⊢
    exact fderiv_sqDist_ne_zero (by norm_num) hz
  · rw [cutModelFunction_eq_of_ne_one hk] at hz ⊢
    exact planarFunction_regular k hz

theorem cutModelFunction_nonpos_iff {k : ℕ} (hk : k ∈ ({1, 2, 3} : Finset ℕ)) (z : ℂ) :
    cutModelFunction k z ≤ 0 ↔ z ∈ planarModel k := by
  by_cases h1 : k = 1
  · subst h1
    rw [cutModelFunction_eq_of_eq_one rfl, sqDist_nonpos_iff 0 (by norm_num), sub_zero,
      planarModel_one, mem_closedBall_zero_iff]
  · rw [cutModelFunction_eq_of_ne_one h1]
    refine planarFunction_nonpos_iff ?_ z
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    omega

theorem contMDiff_cutModelFunction_down (k : ℕ) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ (fun w : PlaneLift.{u} => cutModelFunction k w.down) :=
  (contDiff_cutModelFunction k).contMDiff.comp contMDiff_planeLift_down

theorem cutModelFunction_down_regular (k : ℕ) (w : PlaneLift.{u})
    (hw : cutModelFunction k w.down = 0) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun w : PlaneLift.{u} => cutModelFunction k w.down) w ≠ 0 := by
  refine mfderiv_ne_zero_of_comp (J := 𝓘(ℝ, ℂ)) (s := ULift.up) (y := w.down)
    ((contMDiff_cutModelFunction_down k).mdifferentiableAt (by simp))
    (contMDiff_planeLift_up.mdifferentiableAt (by simp)) ?_
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (cutModelFunction k) w.down ≠ 0
  rw [mfderiv_eq_fderiv]
  exact cutModelFunction_regular k hw

def cutModelSurface (k : ℕ) : Set PlaneLift.{u} := {w | cutModelFunction k w.down ≤ 0}

def cutModelSurfaceAtlas (k : ℕ) : SmoothBoundaryAtlas 𝓘(ℝ, ℂ) 2 (cutModelSurface.{u} k) :=
  SmoothBoundaryAtlas.regularSublevel 𝓘(ℝ, ℂ) (n := 1) Complex.finrank_real_complex
    (contMDiff_cutModelFunction_down.{u} k) 0 (cutModelFunction_down_regular k)

instance (k : ℕ) : ChartedSpace (EuclideanHalfSpace 2) (cutModelSurface.{u} k) :=
  (cutModelSurfaceAtlas k).toChartedSpace

instance (k : ℕ) : IsManifold (𝓡∂ 2) ∞ (cutModelSurface.{u} k) :=
  (cutModelSurfaceAtlas k).isManifold

theorem contMDiff_cutModelPieceFunction (k : ℕ) :
    ContMDiff (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : PlaneLift.{u} × Circle => cutModelFunction k p.1.down) :=
  (contMDiff_cutModelFunction_down k).comp contMDiff_fst

theorem cutModelPieceFunction_regular (k : ℕ) (p : PlaneLift.{u} × Circle)
    (hp : cutModelFunction k p.1.down = 0) :
    mfderiv (𝓘(ℝ, ℂ).prod (𝓡 1)) 𝓘(ℝ, ℝ)
      (fun p : PlaneLift.{u} × Circle => cutModelFunction k p.1.down) p ≠ 0 := by
  refine mfderiv_ne_zero_of_comp (J := 𝓘(ℝ, ℂ))
    (s := fun w : ℂ => ((ULift.up w : PlaneLift.{u}), p.2)) (y := p.1.down)
    ((contMDiff_cutModelPieceFunction k).mdifferentiableAt (by simp))
    ((contMDiff_planeLift_up.prodMk contMDiff_const).mdifferentiableAt (by simp)) ?_
  change mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (cutModelFunction k) p.1.down ≠ 0
  rw [mfderiv_eq_fderiv]
  exact cutModelFunction_regular k hp

def cutModelPiece (k : ℕ) : Set (PlaneLift.{u} × Circle) := {p | cutModelFunction k p.1.down ≤ 0}

def cutModelPieceAtlas (k : ℕ) :
    SmoothBoundaryAtlas (𝓘(ℝ, ℂ).prod (𝓡 1)) 3 (cutModelPiece.{u} k) :=
  SmoothBoundaryAtlas.regularSublevel (𝓘(ℝ, ℂ).prod (𝓡 1)) (n := 2) finrank_planeCircleModel
    (contMDiff_cutModelPieceFunction.{u} k) 0 (cutModelPieceFunction_regular k)

instance (k : ℕ) : ChartedSpace (EuclideanHalfSpace 3) (cutModelPiece.{u} k) :=
  (cutModelPieceAtlas k).toChartedSpace

instance (k : ℕ) : IsManifold (𝓡∂ 3) ∞ (cutModelPiece.{u} k) := (cutModelPieceAtlas k).isManifold

def cutModelProduct (k : ℕ) :
    (cutModelSurface.{u} k × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯ cutModelPiece.{u} k where
  toFun q := ⟨(q.1.val, q.2), q.1.2⟩
  invFun p := (⟨p.val.1, p.2⟩, p.val.2)
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := ((cutModelPieceAtlas k).contMDiff_iff_subtype_val _).mpr
    (((cutModelSurfaceAtlas k).contMDiff_subtype_val.comp contMDiff_fst).prodMk contMDiff_snd)
  contMDiff_invFun :=
    (((cutModelSurfaceAtlas k).contMDiff_iff_subtype_val _).mpr
      (contMDiff_fst.comp (cutModelPieceAtlas k).contMDiff_subtype_val)).prodMk
      (contMDiff_snd.comp (cutModelPieceAtlas k).contMDiff_subtype_val)

theorem isSmoothEmbedding_cutModelSurface (k : ℕ) :
    Manifold.IsSmoothEmbedding (𝓡∂ 2) 𝓘(ℝ, ℂ) ∞
      (fun x : cutModelSurface.{u} k => x.val.down) :=
  ⟨((cutModelSurfaceAtlas.{u} k).isSmoothEmbedding_subtype_val.isImmersion.comp_diffeomorph
    (uliftDiffeomorph 𝓘(ℝ, ℂ) ℂ).symm),
  (Homeomorph.ulift : PlaneLift.{u} ≃ₜ ℂ).isEmbedding.comp
    _root_.Topology.IsEmbedding.subtypeVal⟩

theorem range_cutModelSurface {k : ℕ} (hk : k ∈ ({1, 2, 3} : Finset ℕ)) :
    range (fun x : cutModelSurface.{u} k => x.val.down) = planarModel k := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact (cutModelFunction_nonpos_iff hk _).mp x.2
  · intro hz
    exact ⟨⟨ULift.up z, (cutModelFunction_nonpos_iff hk z).mpr hz⟩, rfl⟩

def PlanarBase.cutModelDiffeomorph {k : ℕ} (B : PlanarBase.{u} k)
    (hk : k ∈ ({1, 2, 3} : Finset ℕ)) :
    B.surface.Carrier ≃ₘ⟮SurfaceModel.model B.surface.kind, 𝓡∂ 2⟯ cutModelSurface.{u} k :=
  B.isSmoothEmbedding.diffeomorphOfRangeEq (isSmoothEmbedding_cutModelSurface k)
    (B.range_embedding.trans (range_cutModelSurface hk).symm)

def PlanarBase.cutModelTrivialization {k : ℕ} (B : PlanarBase.{u} k)
    (hk : k ∈ ({1, 2, 3} : Finset ℕ)) :
    (B.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1), 𝓡∂ 3⟯
      cutModelPiece.{u} k :=
  ((B.cutModelDiffeomorph hk).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).trans
    (cutModelProduct k)

section DiffeoComp

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {E' H'' P : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H'']
  {K : ModelWithCorners ℝ E' H''} [TopologicalSpace P] [ChartedSpace H'' P]

theorem mfderiv_comp_diffeomorph_symm_bijective {f : M → N} (Φ : P ≃ₘ⟮K, I⟯ M)
    (hf : ContMDiff I J ∞ f) (q : P) (hb : Bijective (mfderiv I J f (Φ q))) :
    Bijective (mfderiv K J (f ∘ Φ) q) := by
  obtain ⟨e, he⟩ := Φ.isInvertible_mfderiv (x := q) (by simp)
  have hΦ : Bijective (mfderiv K I Φ q) := by
    rw [← he, ContinuousLinearEquiv.coe_coe]
    exact e.bijective
  rw [mfderiv_comp q (hf.mdifferentiableAt (by simp)) (Φ.contMDiff.mdifferentiableAt (by simp)),
    ContinuousLinearMap.coe_comp]
  exact hb.comp hΦ

end DiffeoComp

namespace EmbeddedPieceSystem

variable {W : CompactCarrier.{u}} (P : EmbeddedPieceSystem W)

def theta (j : Fin P.count) :
    ((P.base j).surface.Carrier × Circle) ≃ₘ⟮
      (SurfaceModel.model (P.base j).surface.kind).prod (𝓡 1), 𝓡∂ 3⟯
      cutModelPiece.{u} (P.kind j) :=
  (P.base j).cutModelTrivialization (P.kind_mem j)

def toCutSystem : EmbeddedCutSystem W .withBoundary where
  count := P.count
  count_pos := P.count_pos
  Piece j := cutModelPiece.{u} (P.kind j)
  charts j := (inferInstance : ChartedSpace (EuclideanHalfSpace 3) (cutModelPiece.{u} (P.kind j)))
  manifold j := (inferInstance : IsManifold (𝓡∂ 3) ∞ (cutModelPiece.{u} (P.kind j)))
  compact j := (P.theta j).toHomeomorph.compactSpace
  connected j := (P.theta j).toHomeomorph.surjective.connectedSpace (P.theta j).continuous
  map j q := P.map j ((P.theta j).symm q)
  smooth j := (P.smooth j).comp (P.theta j).symm.contMDiff
  mfderiv_bijective j q := mfderiv_comp_diffeomorph_symm_bijective (P.theta j).symm (P.smooth j) q
    (P.mfderiv_bijective j _)
  covers := by
    refine eq_univ_of_forall fun w => ?_
    have hw : w ∈ ⋃ j, range (P.map j) := P.covers ▸ mem_univ w
    obtain ⟨j, q, hq⟩ := mem_iUnion.1 hw
    exact mem_iUnion.2 ⟨j, P.theta j q, by
      change P.map j ((P.theta j).symm (P.theta j q)) = w
      rw [Diffeomorph.symm_apply_apply]
      exact hq⟩
  torusCount := P.kind
  collar j l := trivCollar ((P.base j).collar l) (P.theta j)
  collar_source j l := trivCollar_source ((P.base j).source_eq l) _
  collar_disjoint j l l' hll' := by
    refine Disjoint.mono (trivCollar_target_subset _ _) (trivCollar_target_subset _ _) ?_
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have h := (P.theta j).injective hab
    subst h
    exact (P.base j).disjoint hll' |>.le_bot ⟨ha.1, hb.1⟩
  boundary_exhausted j := by
    ext x
    have hx : (𝓡∂ 3).IsBoundaryPoint x ↔ ((SurfaceModel.model (P.base j).surface.kind).prod
        (𝓡 1)).IsBoundaryPoint ((P.theta j).symm x) := by
      rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint,
        ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, not_iff_not]
      have h := ((P.theta j).symm.isLocalDiffeomorph x).isInteriorPoint_iff (by simp)
      exact h
    change (𝓡∂ 3).IsBoundaryPoint x ↔ _
    rw [hx]
    change (P.theta j).symm x ∈ ((SurfaceModel.model (P.base j).surface.kind).prod
      (𝓡 1)).boundary _ ↔ _
    rw [ModelWithCorners.boundary_of_boundaryless_right, (P.base j).boundary_exhausted]
    constructor
    · rintro ⟨hb, -⟩
      obtain ⟨l, t, ht⟩ := mem_iUnion.1 hb
      refine mem_iUnion.2 ⟨l, (t, ((P.theta j).symm x).2), ?_⟩
      change P.theta j ((P.base j).collar l (t, halfZero), ((P.theta j).symm x).2) = x
      rw [show (P.base j).collar l (t, halfZero) = ((P.theta j).symm x).1 from ht,
        Diffeomorph.apply_symm_apply]
    · rintro hx'
      obtain ⟨l, p, rfl⟩ := mem_iUnion.1 hx'
      refine ⟨mem_iUnion.2 ⟨l, p.1, ?_⟩, mem_univ _⟩
      change (P.base j).collar l (p.1, halfZero) =
        ((P.theta j).symm (P.theta j ((P.base j).collar l (p.1, halfZero), p.2))).1
      rw [Diffeomorph.symm_apply_apply]
  seamCount := P.seamCount
  side := P.side
  externalCount := P.externalCount
  externalSide := P.externalSide
  sides_bijective := P.sides_bijective
  matching := P.matching
  seam := P.seam
  seam_source := P.seam_source
  seam_neg c t s hs h1 := by
    rw [P.seam_neg c t s hs h1, trivCollar_apply, Diffeomorph.symm_apply_apply]
  seam_pos c t s hs h1 := by
    rw [P.seam_pos c t s hs h1, trivCollar_apply, Diffeomorph.symm_apply_apply]
  seam_interior := P.seam_interior
  external_local i t := by
    have hθ := (P.theta (P.externalSide i).1).symm.isLocalDiffeomorph
      (P.theta (P.externalSide i).1
        ((P.base _).collar (P.externalSide i).2 (t.1, halfZero), t.2))
    have hm : IsLocalDiffeomorphAt
        ((SurfaceModel.model (P.base (P.externalSide i).1).surface.kind).prod (𝓡 1)) W.model ∞
        (P.map (P.externalSide i).1) ((P.theta (P.externalSide i).1).symm
          (P.theta (P.externalSide i).1
            ((P.base _).collar (P.externalSide i).2 (t.1, halfZero), t.2))) := by
      rw [Diffeomorph.symm_apply_apply]
      exact P.external_local i t
    exact hθ.comp W.model W.Carrier hm
  overlap j j' q q' h := by
    rcases P.overlap j j' _ _ h with he | hs
    · left
      obtain ⟨rfl, he'⟩ := Sigma.mk.inj_iff.mp he
      rw [(P.theta j).symm.injective (eq_of_heq he')]
    · exact Or.inr hs

theorem toCutSystem_map_collar (j : Fin P.count) (l : Fin (P.kind j))
    (p : Torus × EuclideanHalfSpace 1) :
    P.toCutSystem.map j (P.toCutSystem.collar j l p) =
      P.map j ((P.base j).collar l (p.1.1, p.2), p.1.2) := by
  exact congrArg (P.map j) ((P.theta j).symm_apply_apply ((P.base j).collar l (p.1.1, p.2), p.1.2))

def certificate : P.toCutSystem.ProductCertificate where
  kind_mem := P.kind_mem
  base := P.base
  trivialization := P.theta
  collar_eq _ _ _ _ := rfl

def toElementaryPresentation : ElementaryPresentation W :=
  P.toCutSystem.toElementaryPresentation P.certificate

theorem toElementaryPresentation_externalCount :
    P.toElementaryPresentation.toTorus.externalCount = P.externalCount :=
  rfl

theorem toElementaryPresentation_external_zero (i : Fin P.externalCount) (t : Torus) :
    P.toElementaryPresentation.toTorus.external.collar i (t, halfZero) =
      P.map (P.externalSide i).1 ((P.base _).collar (P.externalSide i).2 (t.1, halfZero), t.2) := by
  exact (P.toCutSystem.toTorusPresentation_external_zero i t).trans
    (P.toCutSystem_map_collar _ _ _)

theorem toElementaryPresentation_external_collar (i : Fin P.externalCount)
    (p : Torus × EuclideanHalfSpace 1) :
    P.toElementaryPresentation.toTorus.external.collar i p =
      P.map (P.externalSide i).1 ((P.base _).collar (P.externalSide i).2 (p.1.1, p.2), p.1.2) := by
  exact ((P.toCutSystem.toTorusPresentation_external_collar i p).trans
    (P.toCutSystem.fold_sideCollar _ _)).trans (P.toCutSystem_map_collar _ _ _)

theorem toElementaryPresentation_seam (c : Fin P.seamCount) :
    P.toElementaryPresentation.toTorus.seam c = P.seam c :=
  rfl

theorem toElementaryPresentation_pairing_count :
    P.toElementaryPresentation.toTorus.pairing.count = P.seamCount :=
  rfl

theorem toElementaryPresentation_components_count :
    P.toElementaryPresentation.toTorus.components.count = P.count :=
  rfl

end EmbeddedPieceSystem

section DiffeoBijective

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]

theorem bijective_mfderiv_of_isLocalDiffeomorphAt {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J ∞ f x) : Bijective (mfderiv I J f x) := by
  obtain ⟨e, he⟩ := hf.isInvertible_mfderiv (by simp)
  rw [← he, ContinuousLinearEquiv.coe_coe]
  exact e.bijective

end DiffeoBijective

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)

def sideEquiv : T.Side ≃ Σ j, Fin (Fintype.card (T.OwnedSide j)) :=
  (Equiv.sigmaFiberEquiv T.sidePiece).symm.trans
    (Equiv.sigmaCongrRight fun j => Fintype.equivFin (T.OwnedSide j))

theorem sideEquiv_apply (s : T.Side) :
    T.sideEquiv s = ⟨T.sidePiece s, Fintype.equivFin _ ⟨s, rfl⟩⟩ :=
  rfl

def sideSum : Fin T.pairing.count × Bool ⊕ Fin T.externalCount → T.Side
  | .inl (c, true) => .inl c
  | .inl (c, false) => .inr (.inl c)
  | .inr i => .inr (.inr i)

theorem bijective_sideSum : Bijective T.sideSum := by
  constructor
  · rintro (⟨c, _ | _⟩ | i) (⟨d, _ | _⟩ | k) h <;> simp_all [sideSum]
  · rintro (c | c | i)
    · exact ⟨.inl (c, true), rfl⟩
    · exact ⟨.inl (c, false), rfl⟩
    · exact ⟨.inr i, rfl⟩

theorem bijective_mfderiv_cutMap (x : T.cutCarrier.Carrier) :
    Bijective (mfderiv T.cutCarrier.model W.model T.cutMap x) := by
  obtain ⟨L, hL, -⟩ := T.quotient_oriented x
  have h : (mfderiv T.cutCarrier.model W.model T.cutMap x : _ → _) = L :=
    funext fun v => (hL v).symm
  rw [h]
  exact L.bijective

theorem bijective_mfderiv_cutMap_val (j : Fin T.components.count) (q : T.components.piece j) :
    Bijective (mfderiv T.cutCarrier.model W.model
      (fun x : T.components.piece j => T.cutMap x.val) q) := by
  have hval := DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := T.cutCarrier.model)
    (T.components.piece j) q
  have hc : MDifferentiableAt T.cutCarrier.model W.model T.cutMap q.val :=
    T.quotient_smooth.mdifferentiableAt (by simp)
  rw [show (fun x : T.components.piece j => T.cutMap x.val) = T.cutMap ∘ Subtype.val from rfl,
    mfderiv_comp q hc (hval.mdifferentiableAt (by simp)), ContinuousLinearMap.coe_comp]
  exact (T.bijective_mfderiv_cutMap q.val).comp (bijective_mfderiv_of_isLocalDiffeomorphAt hval)

theorem covers_cutMap :
    ⋃ j, range (fun x : T.components.piece j => T.cutMap x.val) = univ := by
  refine eq_univ_of_forall fun w => ?_
  obtain ⟨q, rfl⟩ := T.reconstruction.surjective w
  induction q using Quotient.inductionOn with
  | h x =>
    have hx : x ∈ ⋃ j, (T.components.piece j : Set T.cutCarrier.Carrier) :=
      T.components.covers ▸ mem_univ x
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨j, ⟨x, hj⟩, rfl⟩

theorem pieceCollar_sideEquiv (s : T.Side) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    Subtype.val ((T.pieceBoundaryTori (T.sideEquiv s).1).collar (T.sideEquiv s).2 p) =
      T.sideCollar s p := by
  change (T.pieceCollar (T.sidePiece s)
    ((Fintype.equivFin _).symm (Fintype.equivFin _ ⟨s, rfl⟩)) p : T.cutCarrier.Carrier) = _
  rw [Equiv.symm_apply_apply, T.pieceCollar_apply _ _ hp]

theorem bijective_cutSides : Bijective (Sum.elim
    (Function.uncurry fun c b => T.sideEquiv (T.sideSum (.inl (c, b))))
    (fun i => T.sideEquiv (T.sideSum (.inr i)))) := by
  have h : Sum.elim (Function.uncurry fun c b => T.sideEquiv (T.sideSum (.inl (c, b))))
      (fun i => T.sideEquiv (T.sideSum (.inr i))) = T.sideEquiv ∘ T.sideSum := by
    funext a
    rcases a with ⟨c, b⟩ | i <;> rfl
  rw [h]
  exact T.sideEquiv.bijective.comp T.bijective_sideSum

theorem quotientMap_leftParam_eq_rightParam_matching (c : Fin T.pairing.count) (t : Torus) :
    T.pairing.quotientMap (T.pairing.leftParam c t) =
      T.pairing.quotientMap (T.pairing.rightParam c (T.pairing.matching c t)) := by
  rw [← T.pairing.matching_eq]
  exact Quotient.sound (T.pairing.gluing.rel_of_mem_left (T.pairing.leftParam c t).property)

theorem isLocalDiffeomorphAt_cutMap_external (i : Fin T.externalCount) (t : Torus) :
    IsLocalDiffeomorphAt T.cutCarrier.model W.model ∞ T.cutMap
      (T.cutExternal.collar i (t, halfZero)) := by
  have h0 : ((t, halfZero) : Torus × EuclideanHalfSpace 1) ∈ (T.cutExternal.collar i).source := by
    rw [T.cutExternal.source_eq]
    exact zero_mem_halfCollarSource t
  have h0' : ((t, halfZero) : Torus × EuclideanHalfSpace 1) ∈ (T.external.collar i).source := by
    rw [T.external.source_eq]
    exact zero_mem_halfCollarSource t
  have hx : T.cutExternal.collar i (t, halfZero) ∈ (T.cutExternal.collar i).target :=
    (T.cutExternal.collar i).map_source h0
  have hinv := (T.cutExternal.collar i).symm.isLocalDiffeomorphAt T.cutCarrier.model
    halfCollarModel ∞ hx
  have hext : IsLocalDiffeomorphAt halfCollarModel W.model ∞ (T.external.collar i)
      ((T.cutExternal.collar i).symm (T.cutExternal.collar i (t, halfZero))) := by
    convert (T.external.collar i).isLocalDiffeomorphAt halfCollarModel W.model ∞ h0' using 1
    exact (T.cutExternal.collar i).left_inv h0
  refine DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq ?_
    (hinv.comp W.model W.Carrier hext)
  filter_upwards [(T.cutExternal.collar i).open_target.mem_nhds hx] with y hy
  have hs := (T.cutExternal.collar i).map_target hy
  rw [T.cutExternal.source_eq] at hs
  have h := T.marked_collar i _ hs
  rw [(T.cutExternal.collar i).right_inv hy] at h
  exact h

def cutSystem : EmbeddedCutSystem W T.cutCarrier.kind where
  count := T.components.count
  count_pos := T.components.count_pos
  Piece j := T.components.piece j
  compact j := isCompact_iff_compactSpace.mp (T.components.piece_compact j)
  connected j := T.components.connected j
  map _ x := T.cutMap x.val
  smooth _ := T.quotient_smooth.comp contMDiff_subtype_val
  mfderiv_bijective j q := T.bijective_mfderiv_cutMap_val j q
  covers := T.covers_cutMap
  torusCount j := Fintype.card (T.OwnedSide j)
  collar j := (T.pieceBoundaryTori j).collar
  collar_source j := (T.pieceBoundaryTori j).source_eq
  collar_disjoint j := (T.pieceBoundaryTori j).disjoint
  boundary_exhausted j := T.pieceBoundaryTori_image j
  seamCount := T.pairing.count
  side c b := T.sideEquiv (T.sideSum (.inl (c, b)))
  externalCount := T.externalCount
  externalSide i := T.sideEquiv (T.sideSum (.inr i))
  sides_bijective := T.bijective_cutSides
  matching := T.pairing.matching
  seam := T.seam
  seam_source := T.seam_source
  seam_neg c t s hs h1 := (T.seam_negative c t s hs h1).trans (congrArg T.cutMap
    (T.pieceCollar_sideEquiv (.inl c) (p := (t, halfPoint (-s) (neg_nonneg.2 hs)))
      (show -s < 1 by linarith)).symm)
  seam_pos c t s hs h1 := (T.seam_positive c t s hs h1).trans (congrArg T.cutMap
    (T.pieceCollar_sideEquiv (.inr (.inl c)) (p := (T.pairing.matching c t, halfPoint s hs))
      h1).symm)
  seam_interior := T.seam_interior
  external_local i t := by
    have hv := DifferentialGeometry.isLocalDiffeomorph_subtype_val (I := T.cutCarrier.model)
      (T.components.piece (T.externalPiece i))
      ((T.pieceBoundaryTori _).collar (T.sideEquiv (.inr (.inr i))).2 (t, halfZero))
    have hc : IsLocalDiffeomorphAt T.cutCarrier.model W.model ∞ T.cutMap
        (Subtype.val ((T.pieceBoundaryTori (T.sideEquiv (.inr (.inr i))).1).collar
          (T.sideEquiv (.inr (.inr i))).2 (t, halfZero))) := by
      rw [T.pieceCollar_sideEquiv (.inr (.inr i)) (zero_mem_halfCollarSource t)]
      exact T.isLocalDiffeomorphAt_cutMap_external i t
    exact hv.comp W.model W.Carrier hc
  overlap j j' q q' h := by
    have hq : T.pairing.quotientMap q.val = T.pairing.quotientMap q'.val :=
      T.reconstruction.injective h
    rcases (Quotient.exact hq : T.pairing.gluing.rel q.val q'.val) with he | ⟨c, hc, -⟩
    · left
      have hjj : j = j' := by
        by_contra hne
        exact (T.components.disjoint hne).le_bot ⟨q.property, he ▸ q'.property⟩
      subst hjj
      rw [Subtype.ext he]
    · right
      rcases hc with hl | hr
      · refine ⟨c, (T.pairing.leftParam c).symm ⟨q.val, hl⟩, ?_⟩
        rw [T.seam_zero, Homeomorph.apply_symm_apply]
        rfl
      · refine ⟨c, (T.pairing.matching c).symm ((T.pairing.rightParam c).symm ⟨q.val, hr⟩), ?_⟩
        rw [T.seam_zero]
        change T.reconstruction (T.pairing.quotientMap q.val) = _
        rw [T.quotientMap_leftParam_eq_rightParam_matching, Diffeomorph.apply_symm_apply,
          Homeomorph.apply_symm_apply]

theorem cutSystem_toTorusPresentation_external_collar (i : Fin T.externalCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    T.cutSystem.toTorusPresentation.external.collar i p = T.external.collar i p :=
  ((T.cutSystem.toTorusPresentation_external_collar i p).trans
    (T.cutSystem.fold_sideCollar _ _)).trans
    ((congrArg T.cutMap (T.pieceCollar_sideEquiv (.inr (.inr i)) hp)).trans
      (T.marked_collar i p hp))

theorem cutSystem_toTorusPresentation_seam (c : Fin T.pairing.count) :
    T.cutSystem.toTorusPresentation.seam c = T.seam c :=
  rfl

theorem cutSystem_toTorusPresentation_matching (c : Fin T.pairing.count) :
    T.cutSystem.toTorusPresentation.pairing.matching c = T.pairing.matching c :=
  rfl

theorem cutSystem_toTorusPresentation_leftPiece (c : Fin T.pairing.count) :
    T.cutSystem.toTorusPresentation.leftPiece c = T.leftPiece c :=
  rfl

theorem cutSystem_toTorusPresentation_rightPiece (c : Fin T.pairing.count) :
    T.cutSystem.toTorusPresentation.rightPiece c = T.rightPiece c :=
  rfl

theorem cutSystem_toTorusPresentation_externalPiece (i : Fin T.externalCount) :
    T.cutSystem.toTorusPresentation.externalPiece i = T.externalPiece i :=
  rfl

theorem cutSystem_toTorusPresentation_cutMap (x : T.cutSystem.Cut) :
    T.cutSystem.toTorusPresentation.reconstruction
        (T.cutSystem.toTorusPresentation.pairing.quotientMap x) = T.cutMap x.2.val :=
  rfl

theorem cutSystem_side_ne (c : Fin T.pairing.count) :
    T.cutSystem.side c true ≠ T.cutSystem.side c false :=
  T.cutSystem.side_ne c

end TorusPresentation

namespace ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)

def portSide (s : E.toTorus.Side) : Σ j, Fin (E.kind j) :=
  ⟨E.toTorus.sidePiece s, (E.piece _).port.symm ⟨s, rfl⟩⟩

def portEquiv : E.toTorus.Side ≃ Σ j, Fin (E.kind j) :=
  (Equiv.sigmaFiberEquiv E.toTorus.sidePiece).symm.trans
    (Equiv.sigmaCongrRight fun j => (E.piece j).port.symm)

theorem portEquiv_apply (s : E.toTorus.Side) : E.portEquiv s = E.portSide s :=
  rfl

def pieceMap (j : Fin E.toTorus.components.count) (q : (E.piece j).base.surface.Carrier × Circle) :
    W.Carrier :=
  E.toTorus.cutMap ((E.piece j).trivialization q).val

theorem trivialization_collar_val (j : Fin E.toTorus.components.count) (l : Fin (E.kind j))
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    ((E.piece j).trivialization ((E.piece j).base.collar l (p.1.1, p.2), p.1.2)).val =
      E.toTorus.sideCollar ((E.piece j).port l).val p := by
  rw [← (E.piece j).collar_eq l p hp, TorusPresentation.pieceCollar_apply _ _ _ hp]

theorem trivialization_collar_side (s : E.toTorus.Side) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    ((E.piece (E.toTorus.sidePiece s)).trivialization
      ((E.piece _).base.collar ((E.piece _).port.symm ⟨s, rfl⟩) (p.1.1, p.2), p.1.2)).val =
      E.toTorus.sideCollar s p := by
  rw [E.trivialization_collar_val _ _ hp, Equiv.apply_symm_apply]

theorem pieceMap_collar (s : E.toTorus.Side) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    E.pieceMap (E.portSide s).1 ((E.piece _).base.collar (E.portSide s).2 (p.1.1, p.2), p.1.2) =
      E.toTorus.cutMap (E.toTorus.sideCollar s p) :=
  congrArg E.toTorus.cutMap (E.trivialization_collar_side s hp)

theorem bijective_mfderiv_pieceMap (j : Fin E.toTorus.components.count)
    (q : (E.piece j).base.surface.Carrier × Circle) :
    Bijective (mfderiv ((SurfaceModel.model (E.piece j).base.surface.kind).prod (𝓡 1)) W.model
      (E.pieceMap j) q) := by
  let g : E.toTorus.components.piece j → W.Carrier := fun x => E.toTorus.cutMap x.val
  have hg : ContMDiff E.toTorus.cutCarrier.model W.model ∞ g :=
    E.toTorus.quotient_smooth.comp contMDiff_subtype_val
  have hgb : Bijective (mfderiv E.toTorus.cutCarrier.model W.model g
      ((E.piece j).trivialization q)) :=
    E.toTorus.bijective_mfderiv_cutMap_val j _
  change Bijective (mfderiv _ W.model (g ∘ (E.piece j).trivialization) q)
  rw [mfderiv_comp q (hg.mdifferentiableAt (by simp))
    ((E.piece j).trivialization.contMDiff.mdifferentiableAt (by simp)),
    ContinuousLinearMap.coe_comp]
  exact hgb.comp (bijective_mfderiv_of_isLocalDiffeomorphAt
    ((E.piece j).trivialization.isLocalDiffeomorph q))

theorem covers_pieceMap : ⋃ j, range (E.pieceMap j) = univ := by
  refine eq_univ_of_forall fun w => ?_
  have hw : w ∈ ⋃ j, range fun x : E.toTorus.components.piece j => E.toTorus.cutMap x.val :=
    E.toTorus.covers_cutMap ▸ mem_univ w
  obtain ⟨j, x, rfl⟩ := mem_iUnion.1 hw
  obtain ⟨q, rfl⟩ := (E.piece j).trivialization.surjective x
  exact mem_iUnion.2 ⟨j, q, rfl⟩

theorem bijective_portSides : Bijective (Sum.elim
    (Function.uncurry fun c b => E.portSide (E.toTorus.sideSum (.inl (c, b))))
    fun m => E.portSide (E.toTorus.sideSum (.inr m))) := by
  have h : Sum.elim (Function.uncurry fun c b => E.portSide (E.toTorus.sideSum (.inl (c, b))))
      (fun m => E.portSide (E.toTorus.sideSum (.inr m))) = E.portEquiv ∘ E.toTorus.sideSum := by
    funext a
    rcases a with ⟨c, b⟩ | m <;> rfl
  rw [h]
  exact E.portEquiv.bijective.comp E.toTorus.bijective_sideSum

theorem isLocalDiffeomorphAt_pieceMap_external (m : Fin E.toTorus.externalCount) (t : Torus) :
    IsLocalDiffeomorphAt
      ((SurfaceModel.model (E.piece (E.portSide (.inr (.inr m))).1).base.surface.kind).prod
        (𝓡 1)) W.model ∞ (E.pieceMap (E.portSide (.inr (.inr m))).1)
      ((E.piece _).base.collar (E.portSide (.inr (.inr m))).2 (t.1, halfZero), t.2) := by
  have hθ := (E.piece (E.portSide (.inr (.inr m))).1).trivialization.isLocalDiffeomorph
    ((E.piece _).base.collar (E.portSide (.inr (.inr m))).2 (t.1, halfZero), t.2)
  have hv := DifferentialGeometry.isLocalDiffeomorph_subtype_val
    (I := E.toTorus.cutCarrier.model) (E.toTorus.components.piece (E.portSide (.inr (.inr m))).1)
    ((E.piece _).trivialization
      ((E.piece _).base.collar (E.portSide (.inr (.inr m))).2 (t.1, halfZero), t.2))
  have e : ((E.piece (E.portSide (.inr (.inr m))).1).trivialization
      ((E.piece _).base.collar (E.portSide (.inr (.inr m))).2 (t.1, halfZero), t.2)).val =
      E.toTorus.cutExternal.collar m (t, halfZero) :=
    E.trivialization_collar_side (.inr (.inr m)) (p := (t, halfZero))
      (zero_mem_halfCollarSource t)
  have hc := E.toTorus.isLocalDiffeomorphAt_cutMap_external m t
  rw [← e] at hc
  exact hθ.comp W.model W.Carrier (hv.comp W.model W.Carrier hc)

def toPieceSystem : EmbeddedPieceSystem W where
  count := E.toTorus.components.count
  count_pos := E.toTorus.components.count_pos
  kind := E.kind
  kind_mem := E.kind_mem
  base j := (E.piece j).base
  map := E.pieceMap
  smooth j := E.toTorus.quotient_smooth.comp
    (contMDiff_subtype_val.comp (E.piece j).trivialization.contMDiff)
  mfderiv_bijective := E.bijective_mfderiv_pieceMap
  covers := E.covers_pieceMap
  seamCount := E.toTorus.pairing.count
  side c b := E.portSide (E.toTorus.sideSum (.inl (c, b)))
  externalCount := E.toTorus.externalCount
  externalSide m := E.portSide (E.toTorus.sideSum (.inr m))
  sides_bijective := E.bijective_portSides
  matching := E.toTorus.pairing.matching
  seam := E.toTorus.seam
  seam_source := E.toTorus.seam_source
  seam_neg c t s hs h1 := (E.toTorus.seam_negative c t s hs h1).trans
    (E.pieceMap_collar (.inl c) (p := (t, halfPoint (-s) (neg_nonneg.2 hs)))
      (show -s < 1 by linarith)).symm
  seam_pos c t s hs h1 := (E.toTorus.seam_positive c t s hs h1).trans
    (E.pieceMap_collar (.inr (.inl c))
      (p := (E.toTorus.pairing.matching c t, halfPoint s hs)) h1).symm
  seam_interior := E.toTorus.seam_interior
  external_local m t := E.isLocalDiffeomorphAt_pieceMap_external m t
  overlap j j' q q' h := by
    have hq : E.toTorus.pairing.quotientMap ((E.piece j).trivialization q).val =
        E.toTorus.pairing.quotientMap ((E.piece j').trivialization q').val :=
      E.toTorus.reconstruction.injective h
    rcases (Quotient.exact hq : E.toTorus.pairing.gluing.rel _ _) with he | ⟨d, hd, -⟩
    · left
      have hjj : j = j' := by
        by_contra hne
        exact (E.toTorus.components.disjoint hne).le_bot
          ⟨((E.piece j).trivialization q).property, he ▸ ((E.piece j').trivialization q').property⟩
      subst hjj
      rw [(E.piece j).trivialization.injective (Subtype.ext he)]
    · right
      rcases hd with hl | hr
      · refine ⟨d, (E.toTorus.pairing.leftParam d).symm ⟨_, hl⟩, ?_⟩
        rw [E.toTorus.seam_zero, Homeomorph.apply_symm_apply]
        rfl
      · refine ⟨d, (E.toTorus.pairing.matching d).symm
          ((E.toTorus.pairing.rightParam d).symm ⟨_, hr⟩), ?_⟩
        rw [E.toTorus.seam_zero]
        change E.toTorus.reconstruction (E.toTorus.pairing.quotientMap _) = _
        rw [E.toTorus.quotientMap_leftParam_eq_rightParam_matching, Diffeomorph.apply_symm_apply,
          Homeomorph.apply_symm_apply]

theorem toPieceSystem_external_collar (m : Fin E.toTorus.externalCount)
    {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    E.toPieceSystem.toElementaryPresentation.toTorus.external.collar m p =
      E.toTorus.external.collar m p :=
  (E.toPieceSystem.toElementaryPresentation_external_collar m p).trans
    ((E.pieceMap_collar (.inr (.inr m)) hp).trans (E.toTorus.marked_collar m p hp))

theorem toPieceSystem_seam (c : Fin E.toTorus.pairing.count) :
    E.toPieceSystem.toElementaryPresentation.toTorus.seam c = E.toTorus.seam c :=
  rfl

end ElementaryPresentation

def productPieceSystem (k : ℕ) (hk : k = 2 ∨ k = 3) :
    EmbeddedPieceSystem (productCarrier.{u} k hk) where
  count := 1
  count_pos := Nat.one_pos
  kind _ := k
  kind_mem _ := by rcases hk with rfl | rfl <;> decide
  base _ := planarBase k hk
  map _ := productDiffeomorph k
  smooth _ := (productDiffeomorph k).contMDiff
  mfderiv_bijective _ q :=
    bijective_mfderiv_of_isLocalDiffeomorphAt ((productDiffeomorph k).isLocalDiffeomorph q)
  covers := eq_univ_of_forall fun w =>
    mem_iUnion.2 ⟨⟨0, Nat.one_pos⟩, (productDiffeomorph k).surjective w⟩
  seamCount := 0
  side c := c.elim0
  externalCount := k
  externalSide l := ⟨⟨0, Nat.one_pos⟩, l⟩
  sides_bijective := by
    constructor
    · rintro (⟨c, -⟩ | l) (⟨c', -⟩ | l') h
      · exact c.elim0
      · exact c.elim0
      · exact c'.elim0
      · simp only [Sum.elim_inr, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
        rw [h]
    · rintro ⟨j, l⟩
      exact ⟨.inr l, by rw [Subsingleton.elim j ⟨0, Nat.one_pos⟩]; rfl⟩
  matching c := c.elim0
  seam c := c.elim0
  seam_source c := c.elim0
  seam_neg c := c.elim0
  seam_pos c := c.elim0
  seam_interior c := c.elim0
  external_local _ _ := (productDiffeomorph k).isLocalDiffeomorph _
  overlap j j' q q' h := by
    left
    obtain rfl : j = j' := Subsingleton.elim j j'
    rw [(productDiffeomorph k).injective h]

theorem productPieceSystem_external_collar (k : ℕ) (hk : k = 2 ∨ k = 3) (l : Fin k)
    (p : Torus × EuclideanHalfSpace 1) :
    (productPieceSystem.{u} k hk).toElementaryPresentation.toTorus.external.collar l p =
      (productPresentation.{u} k hk).external.collar l p :=
  (productPieceSystem.{u} k hk).toElementaryPresentation_external_collar l p

theorem productPieceSystem_externalCount (k : ℕ) (hk : k = 2 ∨ k = 3) :
    (productPieceSystem.{u} k hk).toElementaryPresentation.toTorus.externalCount =
      (productPresentation.{u} k hk).externalCount :=
  rfl

theorem productPieceSystem_components_count (k : ℕ) (hk : k = 2 ∨ k = 3) :
    (productPieceSystem.{u} k hk).toElementaryPresentation.toTorus.components.count = 1 :=
  rfl

end GC.Seifert
