import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarBundle
import DifferentialGeometry.Topology.Manifold.FiniteCollarBoundaryAtlas
import DifferentialGeometry.Topology.Manifold.InteriorChart
import DifferentialGeometry.Topology.Manifold.ImmersionInterior
import DifferentialGeometry.Topology.Manifold.OpenSubtype

/-!
# Circle bundles over the planar pieces of a decomposition

Chapter 6, lane MD5, tier T2 of the P1 Morse-decomposition plan
(`docs/geometrization/handoffs/20261003-survey-p1-morse-decomposition.md`, §3 and errata after
review 8): synchronised trivialisations of a circle fibration over an embedded planar piece.

Data of a piece: a `PlanarBase k` `Q`, a smooth embedding `ι : Q → B` into the interior of the
base, bicollars `c l : S¹ × (-1, 1) → B` of the boundary circles with
`ι (Q.collar l (t, s)) = c l (σ l t, ±s)`, and a lifted bicollar `L l` of each (a flow of the total
space covering the flow along the `ℝ`-lines of `c l`, `SF/FibreCoordinate.lean`).

(1) The image `K = range ι` is a closed sub-surface: `K` is the closure of its interior (interior
points of `Q` go to interior points of `K` by the inverse function theorem through an interior
chart, `mem_interior_range_of_isInteriorPoint`), its frontier lies on the zero sections of the
`c l`, and `exists_smoothBoundaryAtlas_of_collars` (the collar construction of
`FiniteCollarBoundaryAtlas` for a base with boundary) gives a `SmoothBoundaryAtlas` of `K`
(`nonempty_pieceAtlas`).

(2) Restriction. `pieceDiffeo` identifies `Q` with the restricted base: maps into `K` are smooth iff
their composition with the inclusion is, and the inverse is smooth because `ι` is an immersion
(`ContMDiff.iff_comp_isImmersion`). The planar clause `circleBundlesOverPlanarBases_planar` for
the restricted fibration gives a product `Ψ` (`exists_restrictProduct`), hence a smooth injective
`pieceMap : Q × S¹ → U` over `ι` onto `π⁻¹ K` with bijective differential.

(3) Synchronisation, as the collar normalisation FN of the plan on the inner half collars: on the
collar of side `l` with coordinate `s`, `pieceSyncMap (q, v) = L.flow (±s χ(s)) (pieceMap (pull q,
v))` with `pull` the collar point at `s (1 - χ(s))` and `χ = pieceBump w` equal to `1` for
`s ≤ w/4` and `0` for `s ≥ w/2`; off the collars it is `pieceMap`. It differs from `pieceMap` by
the fibrewise diffeomorphism `pieceSyncH` (inverse through the flow at `-s χ(s)`), so it keeps all
the properties, and for `s < w/4` it satisfies the synchronisation identity
`Φ (Q.collar l (t, s), v) = L.flow (±s) (Φ (Q.collar l (t, 0), v))` (`exists_syncedPiece`).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section CollarAtlas

variable {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin 2)) H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def collarChart
    (e : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) I (Circle × ℝ) M ∞) (q : Circle)
    (positive : Bool) : PartialDiffeomorph I (𝓡 2) M (EuclideanSpace ℝ (Fin 2)) ∞ :=
  (e.symm.trans (PartialDiffeomorph.prod (PartialDiffeomorph.extendedChart (I := 𝓡 1) q)
    (Diffeomorph.refl 𝓘(ℝ) ℝ ∞).toPartialDiffeomorph)).trans
      (signedNormalFirstDiffeomorph 1 positive).toPartialDiffeomorph

omit [IsManifold I ∞ M] in
private theorem collarChart_zero
    (e : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) I (Circle × ℝ) M ∞) (q : Circle)
    (positive : Bool) (y : M) :
    collarChart e q positive y 0 = if positive then (e.symm y).2 else -(e.symm y).2 := by
  change signedNormalFirstEquiv 1 positive (_, (e.symm y).2) 0 = _
  exact signedNormalFirstEquiv_zero 1 positive _

omit [IsManifold I ∞ M] in
private theorem collarChart_mem_source
    (e : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) I (Circle × ℝ) M ∞) (q : Circle)
    (positive : Bool) (hq : (q, (0 : ℝ)) ∈ e.source) :
    e (q, 0) ∈ (collarChart e q positive).source := by
  change ((e (q, 0) ∈ e.target ∧
    (e.symm (e (q, 0))).1 ∈ (extChartAt (𝓡 1) q).source ∧ True) ∧ True)
  refine ⟨⟨e.map_source hq, ?_, trivial⟩, trivial⟩
  exact (congrArg Prod.fst (e.left_inv hq)).symm ▸ mem_extChartAt_source q

omit [IsManifold I ∞ M] in
private theorem exists_collarChart_side
    (e : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) I (Circle × ℝ) M ∞)
    {r : ℝ} (hr : 0 < r) (hsource : univ ×ˢ Ioo (-r) r ⊆ e.source)
    {K : Set M} (positive : Bool)
    (hside : ∀ q t, t ∈ Ioo (-r) r → (e (q, t) ∈ K ↔ 0 ≤ if positive then t else -t))
    (q : Circle) :
    ∃ φ : PartialDiffeomorph I (𝓡 2) M (EuclideanSpace ℝ (Fin 2)) ∞,
      e (q, 0) ∈ φ.source ∧ ∀ y ∈ φ.source, y ∈ K ↔ 0 ≤ φ y 0 := by
  let V := e '' (univ ×ˢ Ioo (-r) r)
  have hVo : IsOpen V := e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
    (isOpen_univ.prod isOpen_Ioo) hsource
  let φ := PartialDiffeomorph.restrict (collarChart e q positive) V hVo
  have hqsource : (q, (0 : ℝ)) ∈ e.source := hsource ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩
  refine ⟨φ, ⟨collarChart_mem_source e q positive hqsource,
    (q, 0), ⟨mem_univ _, neg_lt_zero.mpr hr, hr⟩, rfl⟩, ?_⟩
  intro y hy
  obtain ⟨⟨z, t⟩, ⟨_, ht⟩, hzt⟩ := hy.2
  have hinv : e.symm y = (z, t) := hzt ▸ e.left_inv (hsource ⟨mem_univ _, ht⟩)
  have hcoord : φ y 0 = if positive then t else -t := by
    change collarChart e q positive y 0 = _
    rw [collarChart_zero]
    exact congrArg (fun p : Circle × ℝ => if positive then p.2 else -p.2) hinv
  rw [hcoord, ← hzt]
  exact hside z t ht

private theorem exists_positiveChart_of_isInteriorPoint {V : Set M} (hV : IsOpen V) {x : M}
    (hx : x ∈ V) (hxi : I.IsInteriorPoint x) :
    ∃ φ : PartialDiffeomorph I (𝓡 2) M (EuclideanSpace ℝ (Fin 2)) ∞,
      x ∈ φ.source ∧ φ.source ⊆ V ∧ ∀ y ∈ φ.source, 0 < φ y 0 := by
  let c := DifferentialGeometry.Manifold.interiorChart I ∞ x
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun _ ↦ 1) - c x
  let d := c.trans (translateDiffeomorph v).toPartialDiffeomorph
  have hxc : x ∈ c.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff I ∞ x).mpr hxi
  have hxsource : x ∈ d.source := ⟨hxc, mem_univ _⟩
  have hxpos : 0 < d x 0 := by
    change 0 < (c x + v) 0
    simp [v]
  let W := (d.source ∩ d ⁻¹' {z | 0 < z 0}) ∩ V
  have hW : IsOpen W :=
    (d.toOpenPartialHomeomorph.isOpen_inter_preimage
      (isOpen_lt continuous_const (by fun_prop))).inter hV
  refine ⟨PartialDiffeomorph.restrict d W hW, ⟨hxsource, ⟨hxsource, hxpos⟩, hx⟩, ?_, ?_⟩
  · exact fun _ hy ↦ hy.2.2
  · exact fun _ hy ↦ hy.2.1.2

theorem exists_smoothBoundaryAtlas_of_collars [T2Space M] {ι : Type*} [Finite ι]
    (e : ι → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) I (Circle × ℝ) M ∞)
    (hzero : ∀ i q, (q, (0 : ℝ)) ∈ (e i).source)
    (hdisjoint : Pairwise (fun i j => Disjoint
      (range (fun q : Circle => e i (q, 0))) (range (fun q : Circle => e j (q, 0)))))
    {K : Set M} (hregular : closure (interior K) = K)
    (hfrontier : frontier K ⊆ ⋃ i, range (fun q : Circle => e i (q, 0)))
    (hint : ∀ x ∈ interior K, I.IsInteriorPoint x) :
    Nonempty (SmoothBoundaryAtlas I 2 K) := by
  classical
  have hcharts : ∀ x : K, ∃ φ : PartialDiffeomorph I (𝓡 2) M (EuclideanSpace ℝ (Fin 2)) ∞,
      x.val ∈ φ.source ∧ ∀ y ∈ φ.source, y ∈ K ↔ 0 ≤ φ y 0 := by
    intro x
    by_cases hx : x.val ∈ interior K
    · obtain ⟨φ, hxφ, hφK, hpos⟩ :=
        exists_positiveChart_of_isInteriorPoint isOpen_interior hx (hint _ hx)
      exact ⟨φ, hxφ, fun y hy => iff_of_true (interior_subset (hφK hy)) (hpos y hy).le⟩
    · have hxf : x.val ∈ frontier K := ⟨subset_closure x.property, hx⟩
      obtain ⟨i, q, hq⟩ := mem_iUnion.mp (hfrontier hxf)
      obtain ⟨r, σ, hr, hσ, hsource, hside, _⟩ :=
        (frontier_eq_iUnion_of_finite_disjoint_collars
          (fun i => (e i).toOpenPartialHomeomorph) hzero hdisjoint hregular hfrontier).2
          i ⟨x.val, ⟨q, hq⟩, hxf⟩
      have hex : ∃ φ : PartialDiffeomorph I (𝓡 2) M (EuclideanSpace ℝ (Fin 2)) ∞,
          e i (q, 0) ∈ φ.source ∧ ∀ y ∈ φ.source, y ∈ K ↔ 0 ≤ φ y 0 := by
        rcases hσ with rfl | rfl
        · refine exists_collarChart_side (e i) hr hsource false ?_ q
          intro z t ht
          have h := hside z t ht
          change e i (z, t) ∈ K ↔ 1 * t ≤ 0 at h
          simpa only [one_mul, Bool.false_eq_true, ↓reduceIte, neg_nonneg] using h
        · refine exists_collarChart_side (e i) hr hsource true ?_ q
          intro z t ht
          have h := hside z t ht
          change e i (z, t) ∈ K ↔ -1 * t ≤ 0 at h
          simpa only [neg_one_mul, ↓reduceIte, neg_nonpos] using h
      obtain ⟨φ, hxφ, hφ⟩ := hex
      exact ⟨φ, hq ▸ hxφ, hφ⟩
  choose φ hmem hiff using hcharts
  exact ⟨⟨φ, hmem, hiff⟩⟩

end CollarAtlas

section PieceTopology

open DifferentialGeometry.Topology.Manifold

variable {X H H' M : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E H'}
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]

theorem mem_interior_range_of_isInteriorPoint {ι : X → M}
    (hι : Manifold.IsSmoothEmbedding I J ∞ ι) {q : X} (hq : I.IsInteriorPoint q)
    (hqi : J.IsInteriorPoint (ι q)) : ι q ∈ interior (range ι) := by
  let c := DifferentialGeometry.Manifold.interiorChart J ∞ (ι q)
  have hxc : ι q ∈ c.source :=
    (DifferentialGeometry.Manifold.mem_interiorChart_source_iff J ∞ (ι q)).mpr hqi
  let O : TopologicalSpace.Opens X :=
    ⟨ι ⁻¹' c.source, c.open_source.preimage hι.contMDiff.continuous⟩
  let q' : O := ⟨q, hxc⟩
  let f : O → E := fun y => c (ι y.val)
  have hf : ContMDiff I 𝓘(ℝ, E) ∞ f := by
    intro y
    have h1 : ContMDiffAt J 𝓘(ℝ, E) ∞ c (ι y.val) :=
      c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds y.2)
    exact h1.comp y (hι.contMDiff.contMDiffAt.comp y contMDiff_subtype_val.contMDiffAt)
  have hq' : I.IsInteriorPoint q' := ModelWithCorners.isInteriorPoint_iff_isInteriorPoint_val.mpr hq
  have hinj : Function.Injective (mfderiv I 𝓘(ℝ, E) f q') := by
    have hcd : MDifferentiableAt J 𝓘(ℝ, E) c (ι q) :=
      (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hxc)).mdifferentiableAt (by simp)
    have hιd : MDifferentiableAt I J ι q := hι.contMDiff.mdifferentiableAt (by simp)
    have hvd : MDifferentiableAt I I (Subtype.val : O → X) q' :=
      (contMDiff_subtype_val (I := I) (n := ∞)).mdifferentiableAt (by simp)
    have h1 : mfderiv I 𝓘(ℝ, E) f q' = (mfderiv J 𝓘(ℝ, E) c (ι q)).comp
        ((mfderiv I J ι q).comp (mfderiv I I (Subtype.val : O → X) q')) := by
      rw [← mfderiv_comp q' hιd hvd]
      exact mfderiv_comp q' hcd (hιd.comp q' hvd)
    have hloc : IsLocalDiffeomorphAt J 𝓘(ℝ, E) ∞ c (ι q) := c.isLocalDiffeomorphAt J 𝓘(ℝ, E) ∞ hxc
    have hc : Function.Injective (mfderiv J 𝓘(ℝ, E) c (ι q)) :=
      (hloc.mfderivToContinuousLinearEquiv (by simp)).injective
    have hv : mfderiv I I (Subtype.val : O → X) q' = ContinuousLinearMap.id ℝ _ :=
      mfderiv_subtype_val (I := I) O q'
    rw [h1, hv]
    exact hc.comp ((hι.isImmersion.mfderiv_injective (by simp) q).comp fun _ _ h => h)
  obtain ⟨Φ, hqΦ, hfΦ⟩ :=
    isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv hf hq' rfl hinj
  let W : Set M := c.source ∩ c ⁻¹' Φ.target
  have hW : IsOpen W :=
    c.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage c.open_source Φ.open_target
  have hxW : ι q ∈ W := by
    refine ⟨hxc, ?_⟩
    change f q' ∈ Φ.target
    rw [hfΦ hqΦ]
    exact Φ.map_source hqΦ
  refine mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hW.mem_nhds hxW) ?_)
  rintro y ⟨hyc, hyΦ⟩
  let z := Φ.symm (c y)
  have hz : z ∈ Φ.source := Φ.map_target hyΦ
  have h1 : f z = c y := by
    rw [hfΦ hz]
    exact Φ.right_inv hyΦ
  exact ⟨z.val, c.toOpenPartialHomeomorph.injOn z.2 hyc h1⟩

end PieceTopology

section PieceAtlas

theorem PlanarBase.collar_mem_source {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k) (t : Circle)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) : (t, halfPoint s hs) ∈ (Q.collar l).source := by
  rw [Q.source_eq]
  exact hs1

theorem PlanarBase.isInteriorPoint_collar {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k) (t : Circle)
    {s : ℝ} (hs : 0 < s) (hs1 : s < 1) :
    (SurfaceModel.model Q.surface.kind).IsInteriorPoint (Q.collar l (t, halfPoint s hs.le)) := by
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
  intro hb
  have hb' : Q.collar l (t, halfPoint s hs.le) ∈
      (SurfaceModel.model Q.surface.kind).boundary Q.surface.Carrier := hb
  rw [Q.boundary_exhausted] at hb'
  obtain ⟨j, t', hj⟩ := mem_iUnion.mp hb'
  have hsrc := Q.collar_mem_source l t hs.le hs1
  have hsrc' : (t', halfZero) ∈ (Q.collar j).source := Q.collar_mem_source j t' le_rfl one_pos
  by_cases hjl : j = l
  · subst hjl
    have h := (Q.collar j).toOpenPartialHomeomorph.injOn hsrc' hsrc hj
    have h2 := congrArg (fun p : Circle × EuclideanHalfSpace 1 => p.2.val 0) h
    change (0 : ℝ) = s at h2
    linarith
  · have hd := Q.disjoint hjl
    have h1 : Q.collar j (t', halfZero) ∈ (Q.collar l).target := by
      have h2 : Q.collar j (t', halfZero) = Q.collar l (t, halfPoint s hs.le) := hj
      rw [h2]
      exact (Q.collar l).map_source hsrc
    exact Set.disjoint_left.mp hd ((Q.collar j).map_source hsrc') h1

variable {B : CompactSurface.{u}} {k : ℕ} (Q : PlanarBase.{u} k)
  {ι : Q.surface.Carrier → B.Carrier}
  (hι : Manifold.IsSmoothEmbedding (SurfaceModel.model Q.surface.kind)
    (SurfaceModel.model B.kind) ∞ ι)
  (c : Fin k → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
    (Circle × ℝ) B.Carrier ∞)
  (hc : ∀ l, (c l).source = {p | -1 < p.2 ∧ p.2 < 1}) (b : Fin k → Bool)
  (σ : Fin k → (Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle))
  (hcol : ∀ l t s (hs : 0 ≤ s), s < 1 →
    ι (Q.collar l (t, halfPoint s hs)) = c l (σ l t, if b l then s else -s))
  (hint : ∀ q, (SurfaceModel.model B.kind).IsInteriorPoint (ι q))

include hcol in
theorem piece_zero_eq (l : Fin k) (t : Circle) :
    ι (Q.collar l (t, halfZero)) = c l (σ l t, 0) := by
  have h := hcol l t 0 le_rfl one_pos
  have h0 : (if b l then (0 : ℝ) else -0) = 0 := by cases b l <;> simp
  rw [h0] at h
  exact h

include hι in
theorem isClosed_range_piece : IsClosed (range ι) :=
  (isCompact_range hι.contMDiff.continuous).isClosed

include hι hint in
theorem interior_range_piece_of_isInteriorPoint {q : Q.surface.Carrier}
    (hq : (SurfaceModel.model Q.surface.kind).IsInteriorPoint q) : ι q ∈ interior (range ι) :=
  mem_interior_range_of_isInteriorPoint hι hq (hint q)

include hι hc hcol hint in
theorem closure_interior_range_piece : closure (interior (range ι)) = range ι := by
  refine subset_antisymm (closure_minimal interior_subset (isClosed_range_piece Q hι)) ?_
  rintro _ ⟨q, rfl⟩
  rcases (SurfaceModel.model Q.surface.kind).isInteriorPoint_or_isBoundaryPoint q with hq | hq
  · exact subset_closure (interior_range_piece_of_isInteriorPoint Q hι hint hq)
  have hq' : q ∈ (SurfaceModel.model Q.surface.kind).boundary Q.surface.Carrier := hq
  rw [Q.boundary_exhausted] at hq'
  obtain ⟨l, t, rfl⟩ := mem_iUnion.mp hq'
  let g : ℝ → B.Carrier := fun s => c l (σ l t, if b l then s else -s)
  have hg : ContinuousAt g 0 := by
    have hpath : Continuous (fun s : ℝ => ((σ l t, if b l then s else -s) : Circle × ℝ)) := by
      cases b l
      · exact continuous_const.prodMk continuous_neg
      · exact continuous_const.prodMk continuous_id
    have h0 : ((σ l t, if b l then (0 : ℝ) else -0) : Circle × ℝ) ∈ (c l).source := by
      rw [hc]
      cases b l <;> norm_num
    have hcont : ContinuousAt (c l) ((σ l t, if b l then (0 : ℝ) else -0) : Circle × ℝ) :=
      (c l).toOpenPartialHomeomorph.continuousOn.continuousAt ((c l).open_source.mem_nhds h0)
    exact ContinuousAt.comp (g := c l)
      (f := fun s : ℝ => ((σ l t, if b l then s else -s) : Circle × ℝ)) (x := 0) hcont
      hpath.continuousAt
  have hg0 : g 0 = ι (Q.collar l (t, halfZero)) := by
    rw [piece_zero_eq Q c b σ hcol]
    change c l (σ l t, if b l then (0 : ℝ) else -0) = _
    cases b l <;> simp
  change ι (Q.collar l (t, halfZero)) ∈ _
  rw [← hg0]
  refine mem_closure_of_tendsto (f := g) (b := 𝓝[>] (0 : ℝ))
    (hg.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  have h := hcol l t s hs.1.le hs.2
  change c l (σ l t, if b l then s else -s) ∈ interior (range ι)
  rw [← h]
  exact interior_range_piece_of_isInteriorPoint Q hι hint (Q.isInteriorPoint_collar l t hs.1 hs.2)

include hι hcol hint in
theorem frontier_range_piece_subset :
    frontier (range ι) ⊆ ⋃ l, range (fun θ : Circle => c l (θ, 0)) := by
  intro x hx
  have hxK : x ∈ range ι := (isClosed_range_piece Q hι).frontier_subset hx
  obtain ⟨q, rfl⟩ := hxK
  rcases (SurfaceModel.model Q.surface.kind).isInteriorPoint_or_isBoundaryPoint q with hq | hq
  · exact absurd (interior_range_piece_of_isInteriorPoint Q hι hint hq) hx.2
  have hq' : q ∈ (SurfaceModel.model Q.surface.kind).boundary Q.surface.Carrier := hq
  rw [Q.boundary_exhausted] at hq'
  obtain ⟨l, t, rfl⟩ := mem_iUnion.mp hq'
  exact mem_iUnion.mpr ⟨l, σ l t, (piece_zero_eq Q c b σ hcol l t).symm⟩

include hι hcol in
theorem disjoint_zero_piece : Pairwise (fun i j => Disjoint
    (range (fun θ : Circle => c i (θ, 0))) (range (fun θ : Circle => c j (θ, 0)))) := by
  intro i j hij
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨θ, rfl⟩ ⟨θ', hθ'⟩
  have h1 := piece_zero_eq Q c b σ hcol i ((σ i).symm θ)
  have h2 := piece_zero_eq Q c b σ hcol j ((σ j).symm θ')
  rw [Diffeomorph.apply_symm_apply] at h1 h2
  have hθ'' : c j (θ', 0) = c i (θ, 0) := hθ'
  have h3 : Q.collar i ((σ i).symm θ, halfZero) = Q.collar j ((σ j).symm θ', halfZero) :=
    hι.isEmbedding.injective (by rw [h1, h2, hθ''])
  exact Set.disjoint_left.mp (Q.disjoint hij)
    ((Q.collar i).map_source (Q.collar_mem_source i _ le_rfl one_pos))
    (h3 ▸ (Q.collar j).map_source (Q.collar_mem_source j _ le_rfl one_pos))

include hι hc hcol hint in
theorem nonempty_pieceAtlas :
    Nonempty (SmoothBoundaryAtlas (SurfaceModel.model B.kind) 2 (range ι)) :=
  exists_smoothBoundaryAtlas_of_collars c (fun l q => by rw [hc]; norm_num)
    (disjoint_zero_piece Q hι c b σ hcol) (closure_interior_range_piece Q hι c hc b σ hcol hint)
    (frontier_range_piece_subset Q hι c b σ hcol hint)
    (fun x hx => by
      obtain ⟨q, rfl⟩ := interior_subset hx
      exact hint q)

end PieceAtlas

section PieceDiffeo

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  {k : ℕ} (Q : PlanarBase.{u} k) {ι : Q.surface.Carrier → F.base.Carrier}
  (hι : Manifold.IsSmoothEmbedding (SurfaceModel.model Q.surface.kind)
    (SurfaceModel.model F.base.kind) ∞ ι)
  (A : SmoothBoundaryAtlas (SurfaceModel.model F.base.kind) 2 (range ι)) (hK : IsClosed (range ι))

include hι in
theorem connectedSpace_range_piece : ConnectedSpace (range ι) :=
  Subtype.connectedSpace (isConnected_range hι.contMDiff.continuous)

def pieceDiffeo :
    letI := connectedSpace_range_piece F Q hι
    Q.surface.Carrier ≃ₘ⟮SurfaceModel.model Q.surface.kind,
      SurfaceModel.model (CircleFibration.restrictBase F A hK).kind⟯
      (CircleFibration.restrictBase F A hK).Carrier :=
  letI := connectedSpace_range_piece F Q hι
  { toEquiv := hι.isEmbedding.toHomeomorph.toEquiv
    contMDiff_toFun := by
      let _ := A.toChartedSpace
      exact (A.contMDiff_iff_subtype_val (fun q => hι.isEmbedding.toHomeomorph q)).mpr
        hι.contMDiff
    contMDiff_invFun := by
      let _ := A.toChartedSpace
      have h : ContMDiff (𝓡∂ 2) (SurfaceModel.model Q.surface.kind) ∞
          (fun y : range ι => hι.isEmbedding.toHomeomorph.symm y) := by
        apply (ContMDiff.iff_comp_isImmersion hι.isImmersion).mpr
        refine ⟨hι.isEmbedding.toHomeomorph.symm.continuous, ?_⟩
        refine A.contMDiff_subtype_val.congr fun y => ?_
        exact congrArg Subtype.val (hι.isEmbedding.toHomeomorph.apply_symm_apply y)
      exact h }

theorem pieceDiffeo_apply_val (q : Q.surface.Carrier) :
    letI := connectedSpace_range_piece F Q hι
    Subtype.val (p := fun x => x ∈ range ι) (pieceDiffeo F Q hι A hK q) = ι q := rfl

end PieceDiffeo

section PieceProduct

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  {k : ℕ} (hk : k ∈ ({1, 2, 3} : Finset ℕ)) (Q : PlanarBase.{u} k)
  {ι : Q.surface.Carrier → F.base.Carrier}
  (hι : Manifold.IsSmoothEmbedding (SurfaceModel.model Q.surface.kind)
    (SurfaceModel.model F.base.kind) ∞ ι)
  (A : SmoothBoundaryAtlas (SurfaceModel.model F.base.kind) 2 (range ι)) (hK : IsClosed (range ι))

include hk hι in
theorem exists_restrictProduct :
    letI := connectedSpace_range_piece F Q hι
    ∃ Ψ : (⊤ : TopologicalSpace.Opens (CircleFibration.restrictTotal F A hK).Carrier) ≃ₘ⟮
        (CircleFibration.restrictTotal F A hK).model,
        (SurfaceModel.model Q.surface.kind).prod (𝓡 1)⟯ Q.surface.Carrier × Circle,
      ∀ y, ι (Ψ y).1 = F.projection y.val.val := by
  let _ := connectedSpace_range_piece F Q hι
  obtain ⟨Ψ, hΨ⟩ := circleBundlesOverPlanarBases_planar (CircleFibration.restrictTotal F A hK) ⊤
    (CircleFibration.restrict F A hK) k hk Q (pieceDiffeo F Q hι A hK).symm
  refine ⟨Ψ, fun y => ?_⟩
  rw [hΨ y, ← pieceDiffeo_apply_val F Q hι A hK]
  let z : (CircleFibration.restrictBase F A hK).Carrier :=
    (CircleFibration.restrict F A hK).projection y
  have h2 : (pieceDiffeo F Q hι A hK) ((pieceDiffeo F Q hι A hK).symm z) = z :=
    Diffeomorph.apply_symm_apply _ z
  exact congrArg (Subtype.val (p := fun x => x ∈ range ι)) h2

end PieceProduct

section PieceMap

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  {k : ℕ} (Q : PlanarBase.{u} k) {ι : Q.surface.Carrier → F.base.Carrier}
  (A : SmoothBoundaryAtlas (SurfaceModel.model F.base.kind) 2 (range ι)) (hK : IsClosed (range ι))
  (Ψ : (⊤ : TopologicalSpace.Opens (CircleFibration.restrictTotal F A hK).Carrier)
    ≃ₘ⟮(CircleFibration.restrictTotal F A hK).model,
      (SurfaceModel.model Q.surface.kind).prod (𝓡 1)⟯ Q.surface.Carrier × Circle)

def pieceMap (p : Q.surface.Carrier × Circle) : U := ((Ψ.symm p).val).val

theorem pieceMap_mem (p : Q.surface.Carrier × Circle) :
    F.projection (pieceMap F Q A hK Ψ p) ∈ range ι := ((Ψ.symm p).val).2

def pieceLift (x : U) (hx : F.projection x ∈ range ι) :
    (⊤ : TopologicalSpace.Opens (CircleFibration.restrictTotal F A hK).Carrier) :=
  ⟨⟨x, hx⟩, trivial⟩

theorem pieceMap_pieceLift (x : U) (hx : F.projection x ∈ range ι) :
    pieceMap F Q A hK Ψ (Ψ (pieceLift F Q A hK x hx)) = x := by
  change ((Ψ.symm (Ψ (pieceLift F Q A hK x hx))).val).val = x
  rw [Diffeomorph.symm_apply_apply]
  rfl

theorem injective_pieceMap : Function.Injective (pieceMap F Q A hK Ψ) := by
  intro p p' h
  have h1 : Ψ.symm p = Ψ.symm p' := Subtype.ext (Subtype.ext h)
  exact Ψ.symm.injective h1

theorem range_pieceMap : range (pieceMap F Q A hK Ψ) = F.projection ⁻¹' range ι := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact pieceMap_mem F Q A hK Ψ p
  · intro hx
    exact ⟨_, pieceMap_pieceLift F Q A hK Ψ x hx⟩

theorem contMDiff_pieceMap : ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) C.model ∞
    (fun p => (pieceMap F Q A hK Ψ p).val) := by
  have h1 : ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1))
      (CircleFibration.restrictTotal F A hK).model ∞ (fun p => (Ψ.symm p).val) :=
    contMDiff_subtype_val.comp Ψ.symm.contMDiff
  exact contMDiff_subtype_val.comp ((CircleFibration.contMDiff_restrictTotal_val F A hK).comp h1)

theorem bijective_mfderiv_pieceMap (p : Q.surface.Carrier × Circle) :
    Function.Bijective (mfderiv ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) C.model
      (fun p => (pieceMap F Q A hK Ψ p).val) p) := by
  let T := (CircleFibration.restrictTotal F A hK)
  let y := Ψ.symm p
  have hΨd : MDifferentiableAt ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) T.model
      Ψ.symm p :=
    Ψ.symm.contMDiff.mdifferentiableAt (by simp)
  have hv1 : MDifferentiableAt T.model T.model
      (Subtype.val : (⊤ : TopologicalSpace.Opens T.Carrier) → T.Carrier) y :=
    (contMDiff_subtype_val (I := T.model) (n := ∞)).mdifferentiableAt (by simp)
  have hv2 : MDifferentiableAt T.model C.model (fun z : T.Carrier => (z.val : U)) y.val :=
    (CircleFibration.contMDiff_restrictTotal_val F A hK).mdifferentiableAt (by simp)
  have hv3 : MDifferentiableAt C.model C.model (Subtype.val : U → C.Carrier) y.val.val :=
    (contMDiff_subtype_val (I := C.model) (n := ∞)).mdifferentiableAt (by simp)
  have H := hv3.hasMFDerivAt.comp p (hv2.hasMFDerivAt.comp p (hv1.hasMFDerivAt.comp p
    hΨd.hasMFDerivAt))
  have hc : mfderiv ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) C.model
      (fun p => (pieceMap F Q A hK Ψ p).val) p =
      (mfderiv C.model C.model (Subtype.val : U → C.Carrier) y.val.val).comp
        ((mfderiv T.model C.model (fun z : T.Carrier => (z.val : U)) y.val).comp
          ((mfderiv T.model T.model
            (Subtype.val : (⊤ : TopologicalSpace.Opens T.Carrier) → T.Carrier) y).comp
            (mfderiv ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) T.model Ψ.symm p))) :=
    H.mfderiv
  rw [hc]
  have b1 : Function.Bijective
      (mfderiv C.model C.model (Subtype.val : U → C.Carrier) y.val.val) := by
    rw [mfderiv_subtype_val (I := C.model) U y.val.val]
    exact Function.bijective_id
  have b2 : Function.Bijective
      (mfderiv T.model C.model (fun z : T.Carrier => (z.val : U)) y.val) :=
    (CircleFibration.totalAtlas F A).mfderiv_subtypeVal_bijective y.val
  have b3 : Function.Bijective (mfderiv T.model T.model
      (Subtype.val : (⊤ : TopologicalSpace.Opens T.Carrier) → T.Carrier) y) := by
    rw [mfderiv_subtype_val (I := T.model) ⊤ y]
    exact Function.bijective_id
  have b4 : Function.Bijective
      (mfderiv ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) T.model Ψ.symm p) :=
    (Ψ.symm.mfderivToContinuousLinearEquiv (by simp) p).bijective
  exact b1.comp (b2.comp (b3.comp b4))

end PieceMap

section CollarShift

def pieceBump (w s : ℝ) : ℝ := Real.smoothTransition ((w ^ 2 / 4 - s ^ 2) * (16 / (3 * w ^ 2)))

theorem contDiff_pieceBump (w : ℝ) : ContDiff ℝ ∞ (pieceBump w) := by
  unfold pieceBump
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem pieceBump_nonneg (w s : ℝ) : 0 ≤ pieceBump w s := Real.smoothTransition.nonneg _

theorem pieceBump_le_one (w s : ℝ) : pieceBump w s ≤ 1 := Real.smoothTransition.le_one _

theorem pieceBump_eq_one {w s : ℝ} (hw : 0 < w) (hs : |s| ≤ w / 4) : pieceBump w s = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have h1 : s ^ 2 ≤ w ^ 2 / 16 := by
    have h2 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    rw [h2]
    have h3 : |s| ^ 2 ≤ (w / 4) ^ 2 := pow_le_pow_left₀ (abs_nonneg s) hs 2
    linarith
  have hw2 : 0 < w ^ 2 := by positivity
  have h4 : 1 * (3 * w ^ 2) ≤ (w ^ 2 / 4 - s ^ 2) * 16 := by nlinarith
  calc (1 : ℝ) = 1 * (3 * w ^ 2) / (3 * w ^ 2) := by field_simp
    _ ≤ (w ^ 2 / 4 - s ^ 2) * 16 / (3 * w ^ 2) := by gcongr
    _ = (w ^ 2 / 4 - s ^ 2) * (16 / (3 * w ^ 2)) := by ring

theorem pieceBump_eq_zero {w s : ℝ} (hw : 0 < w) (hs : w / 2 ≤ |s|) : pieceBump w s = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : w ^ 2 / 4 ≤ s ^ 2 := by
    have h2 : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    rw [h2]
    have h3 : (w / 2) ^ 2 ≤ |s| ^ 2 := pow_le_pow_left₀ (by positivity) hs 2
    linarith
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

variable {k : ℕ} (Q : PlanarBase.{u} k) (l : Fin k)

def collarS (q : Q.surface.Carrier) : ℝ := ((Q.collar l).symm q).2.val 0

def collarT (q : Q.surface.Carrier) : Circle := ((Q.collar l).symm q).1

theorem collarS_nonneg (q : Q.surface.Carrier) : 0 ≤ collarS Q l q := ((Q.collar l).symm q).2.2

theorem collarS_lt_one {q : Q.surface.Carrier} (hq : q ∈ (Q.collar l).target) :
    collarS Q l q < 1 := by
  have h := (Q.collar l).map_target hq
  rw [Q.source_eq] at h
  exact h

theorem collar_collarT {q : Q.surface.Carrier} (hq : q ∈ (Q.collar l).target) :
    Q.collar l (collarT Q l q, halfPoint (collarS Q l q) (collarS_nonneg Q l q)) = q := by
  have h : ((collarT Q l q, halfPoint (collarS Q l q) (collarS_nonneg Q l q)) :
      Circle × EuclideanHalfSpace 1) = (Q.collar l).symm q :=
    Prod.ext rfl (GC.GraphManifold.halfPoint_coord_eq _)
  rw [h]
  exact (Q.collar l).right_inv hq

theorem collarS_collar (t : Circle) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    collarS Q l (Q.collar l (t, halfPoint s hs)) = s := by
  have h : (Q.collar l).symm (Q.collar l (t, halfPoint s hs)) = (t, halfPoint s hs) :=
    (Q.collar l).left_inv (Q.collar_mem_source l t hs hs1)
  unfold collarS
  rw [h]
  rfl

theorem collarT_collar (t : Circle) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    collarT Q l (Q.collar l (t, halfPoint s hs)) = t := by
  have h : (Q.collar l).symm (Q.collar l (t, halfPoint s hs)) = (t, halfPoint s hs) :=
    (Q.collar l).left_inv (Q.collar_mem_source l t hs hs1)
  unfold collarT
  rw [h]

theorem contMDiffOn_collarS :
    ContMDiffOn (SurfaceModel.model Q.surface.kind) 𝓘(ℝ, ℝ) ∞ (collarS Q l)
      (Q.collar l).target := by
  have h1 : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (fun h : EuclideanHalfSpace 1 => h.val 0) :=
    (EuclideanSpace.proj (0 : Fin 1)).contDiff.contMDiff.comp (𝓡∂ 1).contMDiff
  exact h1.comp_contMDiffOn (contMDiff_snd.comp_contMDiffOn (Q.collar l).contMDiffOn_invFun)

theorem contMDiffOn_collarT :
    ContMDiffOn (SurfaceModel.model Q.surface.kind) (𝓡 1) ∞ (collarT Q l) (Q.collar l).target :=
  contMDiff_fst.comp_contMDiffOn (Q.collar l).contMDiffOn_invFun

end CollarShift

section SyncMap

variable {k : ℕ} (Q : PlanarBase.{u} k)

theorem collarShrink_nonneg (w : ℝ) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ s * (1 - pieceBump w s) :=
  mul_nonneg hs (sub_nonneg.mpr (pieceBump_le_one w s))

theorem collarShrink_le (w : ℝ) {s : ℝ} (hs : 0 ≤ s) : s * (1 - pieceBump w s) ≤ s := by
  have h := pieceBump_nonneg w s
  nlinarith

def pieceCollarPull (w : ℝ) (l : Fin k) (q : Q.surface.Carrier) : Q.surface.Carrier :=
  Q.collar l (collarT Q l q, halfPoint (collarS Q l q * (1 - pieceBump w (collarS Q l q)))
    (collarShrink_nonneg w (collarS_nonneg Q l q)))

theorem exists_collar_eq_of_mem_target {q : Q.surface.Carrier} {l l' : Fin k}
    (hl : q ∈ (Q.collar l).target) (hl' : q ∈ (Q.collar l').target) : l = l' := by
  by_contra hne
  exact Set.disjoint_left.mp (Q.disjoint hne) hl hl'

theorem pieceCollarPull_of_le {w : ℝ} (hw : 0 < w) (l : Fin k) {q : Q.surface.Carrier}
    (hq : q ∈ (Q.collar l).target) (hs : w / 2 ≤ collarS Q l q) : pieceCollarPull Q w l q = q := by
  have h0 : pieceBump w (collarS Q l q) = 0 :=
    pieceBump_eq_zero hw (by rw [abs_of_nonneg (collarS_nonneg Q l q)]; exact hs)
  unfold pieceCollarPull
  have h1 : halfPoint (collarS Q l q * (1 - pieceBump w (collarS Q l q)))
      (collarShrink_nonneg w (collarS_nonneg Q l q)) =
      halfPoint (collarS Q l q) (collarS_nonneg Q l q) := by
    apply Subtype.ext
    simp only [h0, sub_zero, mul_one]
  rw [h1]
  exact collar_collarT Q l hq

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  {ι : Q.surface.Carrier → F.base.Carrier}
  (c : Fin k → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞) (b : Fin k → Bool) (L : ∀ l, LiftedBicollar F (c l))
  (w : ℝ) (Φ₀ : Q.surface.Carrier × Circle → U)

def pieceSyncTime (l : Fin k) (q : Q.surface.Carrier) : ℝ :=
  (if b l then 1 else -1) * (collarS Q l q * pieceBump w (collarS Q l q))

open Classical in
def pieceSyncMap (p : Q.surface.Carrier × Circle) : U :=
  if h : ∃ l, p.1 ∈ (Q.collar l).target then
    (L (Classical.choose h)).flow (pieceSyncTime Q b w (Classical.choose h) p.1)
      (Φ₀ (pieceCollarPull Q w (Classical.choose h) p.1, p.2))
  else Φ₀ p

theorem syncMap_of_mem {l : Fin k} {q : Q.surface.Carrier} (hq : q ∈ (Q.collar l).target)
    (v : Circle) : pieceSyncMap Q F c b L w Φ₀ (q, v) =
      (L l).flow (pieceSyncTime Q b w l q) (Φ₀ (pieceCollarPull Q w l q, v)) := by
  have h : ∃ l, q ∈ (Q.collar l).target := ⟨l, hq⟩
  have hl : Classical.choose h = l :=
    exists_collar_eq_of_mem_target Q (Classical.choose_spec h) hq
  unfold pieceSyncMap
  rw [dite_eq_left_of_eq_true (eq_true h)]
  generalize Classical.choose h = l' at hl
  subst hl
  rfl

theorem syncMap_of_not_mem {q : Q.surface.Carrier} (hq : ∀ l, q ∉ (Q.collar l).target)
    (v : Circle) : pieceSyncMap Q F c b L w Φ₀ (q, v) = Φ₀ (q, v) := by
  unfold pieceSyncMap
  rw [dite_eq_right_of_eq_false (eq_false fun ⟨l, hl⟩ => hq l hl)]

theorem syncMap_of_le {l : Fin k} {q : Q.surface.Carrier} (hw : 0 < w)
    (hq : q ∈ (Q.collar l).target) (hs : w / 2 ≤ collarS Q l q) (v : Circle) :
    pieceSyncMap Q F c b L w Φ₀ (q, v) = Φ₀ (q, v) := by
  rw [syncMap_of_mem Q F c b L w Φ₀ hq, pieceCollarPull_of_le Q hw l hq hs]
  have h0 : pieceSyncTime Q b w l q = 0 := by
    unfold pieceSyncTime
    rw [pieceBump_eq_zero hw (by rw [abs_of_nonneg (collarS_nonneg Q l q)]; exact hs)]
    ring
  rw [h0, (L l).flow_zero]

theorem syncMap_collar_small {l : Fin k} (hw : 0 < w) (t : Circle) {s : ℝ} (hs : 0 ≤ s)
    (hsw : s ≤ w / 4) (hs1 : s < 1) (v : Circle) :
    pieceSyncMap Q F c b L w Φ₀ (Q.collar l (t, halfPoint s hs), v) =
      (L l).flow (if b l then s else -s) (Φ₀ (Q.collar l (t, halfZero), v)) := by
  have hmem : Q.collar l (t, halfPoint s hs) ∈ (Q.collar l).target :=
    (Q.collar l).map_source (Q.collar_mem_source l t hs hs1)
  rw [syncMap_of_mem Q F c b L w Φ₀ hmem]
  have hS : collarS Q l (Q.collar l (t, halfPoint s hs)) = s := collarS_collar Q l t hs hs1
  have hT : collarT Q l (Q.collar l (t, halfPoint s hs)) = t := collarT_collar Q l t hs hs1
  have h1 : pieceBump w s = 1 := pieceBump_eq_one hw (by rw [abs_of_nonneg hs]; exact hsw)
  have hpull : pieceCollarPull Q w l (Q.collar l (t, halfPoint s hs)) =
      Q.collar l (t, halfZero) := by
    unfold pieceCollarPull
    congr 1
    refine Prod.ext hT (Subtype.ext ?_)
    simp only [hS, h1, sub_self, mul_zero]
    rfl
  have htime : pieceSyncTime Q b w l (Q.collar l (t, halfPoint s hs)) = if b l then s else -s := by
    unfold pieceSyncTime
    rw [hS, h1]
    cases b l <;> simp
  rw [hpull, htime]

theorem projection_pieceSyncMap (hι0 : ∀ p, F.projection (Φ₀ p) = ι p.1)
    (σ : Fin k → (Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle))
    (hcol : ∀ l t s (hs : 0 ≤ s), s < 1 →
      ι (Q.collar l (t, halfPoint s hs)) = c l (σ l t, if b l then s else -s))
    (hw : 0 < w) (hwL : ∀ l, w ≤ (L l).width) (p : Q.surface.Carrier × Circle) :
    F.projection (pieceSyncMap Q F c b L w Φ₀ p) = ι p.1 := by
  obtain ⟨q, v⟩ := p
  by_cases hq : ∃ l, q ∈ (Q.collar l).target
  · obtain ⟨l, hl⟩ := hq
    set s := collarS Q l q with hsdef
    have hs0 : 0 ≤ s := collarS_nonneg Q l q
    have hs1 : s < 1 := collarS_lt_one Q l hl
    by_cases hsw : w / 2 ≤ s
    · rw [syncMap_of_le Q F c b L w Φ₀ hw hl hsw]
      exact hι0 _
    push Not at hsw
    have hqeq := collar_collarT Q l hl
    rw [syncMap_of_mem Q F c b L w Φ₀ hl, (L l).projection_flow, hι0]
    have hpull : ι (pieceCollarPull Q w l q) = c l (σ l (collarT Q l q),
        if b l then s * (1 - pieceBump w s) else -(s * (1 - pieceBump w s))) :=
      hcol l _ _ _ (lt_of_le_of_lt (collarShrink_le w hs0) hs1)
    change (L l).baseFlow (pieceSyncTime Q b w l q) (ι (pieceCollarPull Q w l q)) = ι q
    rw [hpull]
    have hW := hwL l
    have hb0 := pieceBump_nonneg w s
    have hb1 := pieceBump_le_one w s
    have hq' : ι q = c l (σ l (collarT Q l q), if b l then s else -s) := by
      conv_lhs => rw [← hqeq]
      exact hcol l _ _ _ hs1
    rw [hq']
    unfold pieceSyncTime
    rw [← hsdef]
    cases hbl : b l
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [(L l).baseFlow_apply]
      · congr 2
        ring
      · rw [abs_neg, abs_of_nonneg (collarShrink_nonneg w hs0)]
        nlinarith
      · rw [show -(s * (1 - pieceBump w s)) + -1 * (s * pieceBump w s) = -s by ring, abs_neg,
          abs_of_nonneg hs0]
        linarith
    · simp only [↓reduceIte]
      rw [(L l).baseFlow_apply]
      · congr 2
        ring
      · rw [abs_of_nonneg (collarShrink_nonneg w hs0)]
        nlinarith
      · rw [show s * (1 - pieceBump w s) + 1 * (s * pieceBump w s) = s by ring,
          abs_of_nonneg hs0]
        linarith
  · push Not at hq
    rw [syncMap_of_not_mem Q F c b L w Φ₀ hq]
    exact hι0 _

theorem contMDiffOn_pieceCollarPull (l : Fin k) :
    ContMDiffOn (SurfaceModel.model Q.surface.kind) (SurfaceModel.model Q.surface.kind) ∞
      (pieceCollarPull Q w l) (Q.collar l).target := by
  let g : Q.surface.Carrier → ℝ := fun q => collarS Q l q * (1 - pieceBump w (collarS Q l q))
  have hg : ContMDiffOn (SurfaceModel.model Q.surface.kind) 𝓘(ℝ, ℝ) ∞ g (Q.collar l).target := by
    have h1 := contMDiffOn_collarS Q l
    have h2 : ContMDiffOn (SurfaceModel.model Q.surface.kind) 𝓘(ℝ, ℝ) ∞
        (fun q => pieceBump w (collarS Q l q)) (Q.collar l).target :=
      (contDiff_pieceBump w).contMDiff.comp_contMDiffOn h1
    exact h1.mul (contMDiffOn_const.sub h2)
  have hφ : ContMDiffOn (SurfaceModel.model Q.surface.kind) circleCollarModel ∞
      (fun q => (collarT Q l q, Manifold.halfSpaceOneLift (g q))) (Q.collar l).target :=
    (contMDiffOn_collarT Q l).prodMk (Manifold.contMDiffOn_halfSpaceOneLift.comp hg
      fun q _ => collarShrink_nonneg w (collarS_nonneg Q l q))
  have heq : ∀ q ∈ (Q.collar l).target, pieceCollarPull Q w l q =
      Q.collar l (collarT Q l q, Manifold.halfSpaceOneLift (g q)) := by
    intro q _
    unfold pieceCollarPull
    rw [GC.GraphManifold.halfPoint_eq_halfSpaceOneLift]
  refine ((Q.collar l).contMDiffOn.comp hφ ?_).congr heq
  intro q hq
  change (collarT Q l q, Manifold.halfSpaceOneLift (g q)) ∈ (Q.collar l).source
  rw [← GC.GraphManifold.halfPoint_eq_halfSpaceOneLift _
    (collarShrink_nonneg w (collarS_nonneg Q l q))]
  exact Q.collar_mem_source l _ _
    (lt_of_le_of_lt (collarShrink_le w (collarS_nonneg Q l q)) (collarS_lt_one Q l hq))

theorem contMDiffOn_pieceSyncTime (l : Fin k) :
    ContMDiffOn (SurfaceModel.model Q.surface.kind) 𝓘(ℝ, ℝ) ∞ (pieceSyncTime Q b w l)
      (Q.collar l).target := by
  have h1 := contMDiffOn_collarS Q l
  have h2 : ContMDiffOn (SurfaceModel.model Q.surface.kind) 𝓘(ℝ, ℝ) ∞
      (fun q => pieceBump w (collarS Q l q)) (Q.collar l).target :=
    (contDiff_pieceBump w).contMDiff.comp_contMDiffOn h1
  exact contMDiffOn_const.mul (h1.mul h2)

theorem isCompact_collarStrip (l : Fin k) (hw1 : w / 2 < 1) :
    IsCompact (range fun p : Circle × Icc (0 : ℝ) (w / 2) =>
      Q.collar l (p.1, halfPoint p.2.1 p.2.2.1)) := by
  apply isCompact_range
  have hcont : Continuous fun p : Circle × Icc (0 : ℝ) (w / 2) =>
      ((p.1, halfPoint p.2.1 p.2.2.1) : Circle × EuclideanHalfSpace 1) := by
    refine continuous_fst.prodMk (Continuous.subtype_mk ?_ _)
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ =>
      continuous_subtype_val.comp continuous_snd)
  refine ContinuousOn.comp_continuous (Q.collar l).toOpenPartialHomeomorph.continuousOn hcont
    fun p => ?_
  exact Q.collar_mem_source l _ _ (lt_of_le_of_lt p.2.2.2 hw1)

theorem contMDiff_pieceSyncMap (hΦ₀ : ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1))
    C.model ∞ Φ₀) (hw : 0 < w) (hw1 : w / 2 < 1) :
    ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) C.model ∞
      (pieceSyncMap Q F c b L w Φ₀) := by
  intro p
  by_cases hq : ∃ l, p.1 ∈ (Q.collar l).target
  · obtain ⟨l, hl⟩ := hq
    have hO : (Q.collar l).target ×ˢ (univ : Set Circle) ∈ 𝓝 p :=
      ((Q.collar l).open_target.prod isOpen_univ).mem_nhds ⟨hl, mem_univ _⟩
    have hform : ContMDiffOn ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) C.model ∞
        (fun p : Q.surface.Carrier × Circle =>
          (L l).flow (pieceSyncTime Q b w l p.1) (Φ₀ (pieceCollarPull Q w l p.1, p.2)))
        ((Q.collar l).target ×ˢ univ) := by
      have hfst : ContMDiffOn ((SurfaceModel.model Q.surface.kind).prod (𝓡 1))
          (SurfaceModel.model Q.surface.kind) ∞ (Prod.fst : Q.surface.Carrier × Circle → _)
          ((Q.collar l).target ×ˢ univ) := contMDiffOn_fst
      have hsnd : ContMDiffOn ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) (𝓡 1) ∞
          (Prod.snd : Q.surface.Carrier × Circle → Circle) ((Q.collar l).target ×ˢ univ) :=
        contMDiffOn_snd
      have ht := (contMDiffOn_pieceSyncTime Q b w l).comp hfst (fun p hp => hp.1)
      have hpull := ((contMDiffOn_pieceCollarPull Q w l).comp hfst (fun p hp => hp.1)).prodMk hsnd
      have hΦ := hΦ₀.comp_contMDiffOn hpull
      exact (L l).smooth.comp_contMDiffOn (ht.prodMk hΦ)
    refine (hform.contMDiffAt hO).congr_of_eventuallyEq ?_
    filter_upwards [hO] with p' hp'
    exact syncMap_of_mem Q F c b L w Φ₀ hp'.1 p'.2
  · push Not at hq
    let Kc : Set Q.surface.Carrier := ⋃ l, range fun p : Circle × Icc (0 : ℝ) (w / 2) =>
      Q.collar l (p.1, halfPoint p.2.1 p.2.2.1)
    have hKc : IsClosed Kc :=
      (isCompact_iUnion fun l => isCompact_collarStrip Q w l hw1).isClosed
    have hpK : p.1 ∉ Kc := by
      intro h
      obtain ⟨l, ⟨t, s⟩, hts⟩ := mem_iUnion.mp h
      apply hq l
      rw [← hts]
      exact (Q.collar l).map_source (Q.collar_mem_source l _ _ (lt_of_le_of_lt s.2.2 hw1))
    have hO : Kcᶜ ×ˢ (univ : Set Circle) ∈ 𝓝 p :=
      (hKc.isOpen_compl.prod isOpen_univ).mem_nhds ⟨hpK, mem_univ _⟩
    refine hΦ₀.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hO] with p' hp'
    obtain ⟨q', v'⟩ := p'
    by_cases hq' : ∃ l, q' ∈ (Q.collar l).target
    · obtain ⟨l, hl⟩ := hq'
      refine syncMap_of_le Q F c b L w Φ₀ hw hl ?_ v'
      by_contra hlt
      push Not at hlt
      apply hp'.1
      refine mem_iUnion.mpr ⟨l, ⟨collarT Q l q', ⟨collarS Q l q', collarS_nonneg Q l q',
        hlt.le⟩⟩, ?_⟩
      exact collar_collarT Q l hl
    · push Not at hq'
      exact syncMap_of_not_mem Q F c b L w Φ₀ hq' v'

end SyncMap

section PieceAngle

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  {k : ℕ} (Q : PlanarBase.{u} k) {ι : Q.surface.Carrier → F.base.Carrier}
  (A : SmoothBoundaryAtlas (SurfaceModel.model F.base.kind) 2 (range ι)) (hK : IsClosed (range ι))
  (Ψ : (⊤ : TopologicalSpace.Opens (CircleFibration.restrictTotal F A hK).Carrier)
    ≃ₘ⟮(CircleFibration.restrictTotal F A hK).model,
      (SurfaceModel.model Q.surface.kind).prod (𝓡 1)⟯ Q.surface.Carrier × Circle)

open Classical in
def pieceAngle (x : U) : Circle :=
  if hx : F.projection x ∈ range ι then (Ψ (pieceLift F Q A hK x hx)).2 else 1

theorem pieceAngle_of_mem (x : U) (hx : F.projection x ∈ range ι) :
    pieceAngle F Q A hK Ψ x = (Ψ (pieceLift F Q A hK x hx)).2 := by
  unfold pieceAngle
  rw [dite_eq_left_of_eq_true (eq_true hx)]

theorem pieceAngle_pieceMap (p : Q.surface.Carrier × Circle) :
    pieceAngle F Q A hK Ψ (pieceMap F Q A hK Ψ p) = p.2 := by
  rw [pieceAngle_of_mem F Q A hK Ψ _ (pieceMap_mem F Q A hK Ψ p)]
  have h : pieceLift F Q A hK (pieceMap F Q A hK Ψ p) (pieceMap_mem F Q A hK Ψ p) = Ψ.symm p :=
    rfl
  rw [h, Diffeomorph.apply_symm_apply]

theorem pieceMap_pieceAngle (hΨ : ∀ y, ι (Ψ y).1 = F.projection y.val.val)
    (hι : Function.Injective ι) {x : U} {q : Q.surface.Carrier} (hx : F.projection x = ι q) :
    pieceMap F Q A hK Ψ (q, pieceAngle F Q A hK Ψ x) = x := by
  have hxK : F.projection x ∈ range ι := ⟨q, hx.symm⟩
  rw [pieceAngle_of_mem F Q A hK Ψ x hxK]
  have h1 : (Ψ (pieceLift F Q A hK x hxK)).1 = q := hι ((hΨ _).trans hx)
  have h2 : ((q, (Ψ (pieceLift F Q A hK x hxK)).2) : Q.surface.Carrier × Circle) =
      Ψ (pieceLift F Q A hK x hxK) := Prod.ext h1.symm rfl
  rw [h2]
  exact pieceMap_pieceLift F Q A hK Ψ x hxK

theorem contMDiff_pieceAngle_comp {X : Type*} [TopologicalSpace X]
    [ChartedSpace (ModelProd (SurfaceModel.Space Q.surface.kind) (EuclideanSpace ℝ (Fin 1))) X]
    {f : X → U}
    (hf : ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) C.model ∞ f)
    (hfK : ∀ x, F.projection (f x) ∈ range ι) :
    ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) (𝓡 1) ∞
      (fun x => pieceAngle F Q A hK Ψ (f x)) := by
  let T := CircleFibration.restrictTotal F A hK
  let g : X → T.Carrier := fun x => ⟨f x, hfK x⟩
  have hg : ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) T.model ∞ g :=
    (CircleFibration.contMDiff_restrictTotal_iff F A hK g).mpr hf
  let g' : X → (⊤ : TopologicalSpace.Opens T.Carrier) := fun x => ⟨g x, trivial⟩
  have hg' : ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) T.model ∞ g' :=
    (ContMDiff.subtypeVal_comp_iff ⊤ g').mp hg
  have h := contMDiff_snd.comp (Ψ.contMDiff.comp hg')
  refine h.congr fun x => ?_
  exact pieceAngle_of_mem F Q A hK Ψ (f x) (hfK x)

end PieceAngle

section SyncInv

variable {k : ℕ} (Q : PlanarBase.{u} k)
  {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  {ι : Q.surface.Carrier → F.base.Carrier}
  (c : Fin k → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞) (b : Fin k → Bool) (L : ∀ l, LiftedBicollar F (c l))
  (w : ℝ) (Φ₀ : Q.surface.Carrier × Circle → U)

open Classical in
def pieceSyncInv (p : Q.surface.Carrier × Circle) : U :=
  if h : ∃ l, p.1 ∈ (Q.collar l).target then
    (L (Classical.choose h)).flow (-pieceSyncTime Q b w (Classical.choose h) p.1) (Φ₀ p)
  else Φ₀ p

theorem syncInv_of_mem {l : Fin k} {q : Q.surface.Carrier} (hq : q ∈ (Q.collar l).target)
    (u : Circle) : pieceSyncInv Q F c b L w Φ₀ (q, u) =
      (L l).flow (-pieceSyncTime Q b w l q) (Φ₀ (q, u)) := by
  have h : ∃ l, q ∈ (Q.collar l).target := ⟨l, hq⟩
  have hl : Classical.choose h = l :=
    exists_collar_eq_of_mem_target Q (Classical.choose_spec h) hq
  unfold pieceSyncInv
  rw [dite_eq_left_of_eq_true (eq_true h)]
  generalize Classical.choose h = l' at hl
  subst hl
  rfl

theorem syncInv_of_not_mem {q : Q.surface.Carrier} (hq : ∀ l, q ∉ (Q.collar l).target)
    (u : Circle) : pieceSyncInv Q F c b L w Φ₀ (q, u) = Φ₀ (q, u) := by
  unfold pieceSyncInv
  rw [dite_eq_right_of_eq_false (eq_false fun ⟨l, hl⟩ => hq l hl)]

theorem syncInv_of_le {l : Fin k} {q : Q.surface.Carrier} (hw : 0 < w)
    (hq : q ∈ (Q.collar l).target) (hs : w / 2 ≤ collarS Q l q) (u : Circle) :
    pieceSyncInv Q F c b L w Φ₀ (q, u) = Φ₀ (q, u) := by
  rw [syncInv_of_mem Q F c b L w Φ₀ hq]
  have h0 : pieceSyncTime Q b w l q = 0 := by
    unfold pieceSyncTime
    rw [pieceBump_eq_zero hw (by rw [abs_of_nonneg (collarS_nonneg Q l q)]; exact hs)]
    ring
  rw [h0, neg_zero, (L l).flow_zero]

theorem projection_pieceSyncInv (hι0 : ∀ p, F.projection (Φ₀ p) = ι p.1)
    (σ : Fin k → (Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle))
    (hcol : ∀ l t s (hs : 0 ≤ s), s < 1 →
      ι (Q.collar l (t, halfPoint s hs)) = c l (σ l t, if b l then s else -s))
    (hw : 0 < w) (hwL : ∀ l, w ≤ (L l).width) {l : Fin k} {q : Q.surface.Carrier}
    (hl : q ∈ (Q.collar l).target) (u : Circle) :
    F.projection (pieceSyncInv Q F c b L w Φ₀ (q, u)) = ι (pieceCollarPull Q w l q) := by
  set s := collarS Q l q with hsdef
  have hs0 : 0 ≤ s := collarS_nonneg Q l q
  have hs1 : s < 1 := collarS_lt_one Q l hl
  by_cases hsw : w / 2 ≤ s
  · rw [syncInv_of_le Q F c b L w Φ₀ hw hl hsw, hι0, pieceCollarPull_of_le Q hw l hl hsw]
  push Not at hsw
  have hqeq := collar_collarT Q l hl
  rw [syncInv_of_mem Q F c b L w Φ₀ hl, (L l).projection_flow, hι0]
  have hpull : ι (pieceCollarPull Q w l q) = c l (σ l (collarT Q l q),
      if b l then s * (1 - pieceBump w s) else -(s * (1 - pieceBump w s))) :=
    hcol l _ _ _ (lt_of_le_of_lt (collarShrink_le w hs0) hs1)
  have hq' : ι q = c l (σ l (collarT Q l q), if b l then s else -s) := by
    conv_lhs => rw [← hqeq]
    exact hcol l _ _ _ hs1
  change (L l).baseFlow (-pieceSyncTime Q b w l q) (ι q) = ι (pieceCollarPull Q w l q)
  rw [hpull, hq']
  have hW := hwL l
  have hb0 := pieceBump_nonneg w s
  have hb1 := pieceBump_le_one w s
  unfold pieceSyncTime
  rw [← hsdef]
  cases hbl : b l
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [(L l).baseFlow_apply]
    · congr 2
      ring
    · rw [abs_neg, abs_of_nonneg hs0]
      linarith
    · rw [show -s + -(-1 * (s * pieceBump w s)) = -(s * (1 - pieceBump w s)) by ring, abs_neg,
        abs_of_nonneg (collarShrink_nonneg w hs0)]
      nlinarith
  · simp only [↓reduceIte]
    rw [(L l).baseFlow_apply]
    · congr 2
      ring
    · rw [abs_of_nonneg hs0]
      linarith
    · rw [show s + -(1 * (s * pieceBump w s)) = s * (1 - pieceBump w s) by ring,
        abs_of_nonneg (collarShrink_nonneg w hs0)]
      nlinarith

theorem contMDiff_pieceSyncInv (hΦ₀ : ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1))
    C.model ∞ Φ₀) (hw : 0 < w) (hw1 : w / 2 < 1) :
    ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) C.model ∞
      (pieceSyncInv Q F c b L w Φ₀) := by
  intro p
  by_cases hq : ∃ l, p.1 ∈ (Q.collar l).target
  · obtain ⟨l, hl⟩ := hq
    have hO : (Q.collar l).target ×ˢ (univ : Set Circle) ∈ 𝓝 p :=
      ((Q.collar l).open_target.prod isOpen_univ).mem_nhds ⟨hl, mem_univ _⟩
    have hform : ContMDiffOn ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) C.model ∞
        (fun p : Q.surface.Carrier × Circle =>
          (L l).flow (-pieceSyncTime Q b w l p.1) (Φ₀ p))
        ((Q.collar l).target ×ˢ univ) := by
      have hfst : ContMDiffOn ((SurfaceModel.model Q.surface.kind).prod (𝓡 1))
          (SurfaceModel.model Q.surface.kind) ∞ (Prod.fst : Q.surface.Carrier × Circle → _)
          ((Q.collar l).target ×ˢ univ) := contMDiffOn_fst
      have ht := ((contMDiffOn_pieceSyncTime Q b w l).comp hfst (fun p hp => hp.1)).neg
      exact (L l).smooth.comp_contMDiffOn (ht.prodMk hΦ₀.contMDiffOn)
    refine (hform.contMDiffAt hO).congr_of_eventuallyEq ?_
    filter_upwards [hO] with p' hp'
    exact syncInv_of_mem Q F c b L w Φ₀ hp'.1 p'.2
  · push Not at hq
    let Kc : Set Q.surface.Carrier := ⋃ l, range fun p : Circle × Icc (0 : ℝ) (w / 2) =>
      Q.collar l (p.1, halfPoint p.2.1 p.2.2.1)
    have hKc : IsClosed Kc :=
      (isCompact_iUnion fun l => isCompact_collarStrip Q w l hw1).isClosed
    have hpK : p.1 ∉ Kc := by
      intro h
      obtain ⟨l, ⟨t, s⟩, hts⟩ := mem_iUnion.mp h
      apply hq l
      rw [← hts]
      exact (Q.collar l).map_source (Q.collar_mem_source l _ _ (lt_of_le_of_lt s.2.2 hw1))
    have hO : Kcᶜ ×ˢ (univ : Set Circle) ∈ 𝓝 p :=
      (hKc.isOpen_compl.prod isOpen_univ).mem_nhds ⟨hpK, mem_univ _⟩
    refine hΦ₀.contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [hO] with p' hp'
    obtain ⟨q', u'⟩ := p'
    by_cases hq' : ∃ l, q' ∈ (Q.collar l).target
    · obtain ⟨l, hl⟩ := hq'
      refine syncInv_of_le Q F c b L w Φ₀ hw hl ?_ u'
      by_contra hlt
      push Not at hlt
      apply hp'.1
      refine mem_iUnion.mpr ⟨l, ⟨collarT Q l q', ⟨collarS Q l q', collarS_nonneg Q l q',
        hlt.le⟩⟩, ?_⟩
      exact collar_collarT Q l hl
    · push Not at hq'
      exact syncInv_of_not_mem Q F c b L w Φ₀ hq' u'

end SyncInv

section Synced

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  {k : ℕ} (Q : PlanarBase.{u} k) {ι : Q.surface.Carrier → F.base.Carrier}
  (A : SmoothBoundaryAtlas (SurfaceModel.model F.base.kind) 2 (range ι)) (hK : IsClosed (range ι))
  (Ψ : (⊤ : TopologicalSpace.Opens (CircleFibration.restrictTotal F A hK).Carrier)
    ≃ₘ⟮(CircleFibration.restrictTotal F A hK).model,
      (SurfaceModel.model Q.surface.kind).prod (𝓡 1)⟯ Q.surface.Carrier × Circle)
  (hΨ : ∀ y, ι (Ψ y).1 = F.projection y.val.val) (hιi : Function.Injective ι)
  (c : Fin k → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
    (Circle × ℝ) F.base.Carrier ∞) (b : Fin k → Bool) (L : ∀ l, LiftedBicollar F (c l))
  (w : ℝ) (σ : Fin k → (Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle))
  (hcol : ∀ l t s (hs : 0 ≤ s), s < 1 →
    ι (Q.collar l (t, halfPoint s hs)) = c l (σ l t, if b l then s else -s))
  (hw : 0 < w) (hw1 : w / 2 < 1) (hwL : ∀ l, w ≤ (L l).width)

include hΨ in
theorem projection_pieceMap (p : Q.surface.Carrier × Circle) :
    F.projection (pieceMap F Q A hK Ψ p) = ι p.1 := by
  have h := hΨ (Ψ.symm p)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm

theorem contMDiff_pieceMap_opens : ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1))
    C.model ∞ (pieceMap F Q A hK Ψ) :=
  (ContMDiff.subtypeVal_comp_iff U _).mp (contMDiff_pieceMap F Q A hK Ψ)

include hΨ hιi hcol hw hwL in
theorem pieceSyncInv_pieceSyncMap (p : Q.surface.Carrier × Circle) :
    pieceAngle F Q A hK Ψ (pieceSyncInv Q F c b L w (pieceMap F Q A hK Ψ)
      (p.1, pieceAngle F Q A hK Ψ (pieceSyncMap Q F c b L w (pieceMap F Q A hK Ψ) p))) = p.2 := by
  obtain ⟨q, v⟩ := p
  have hπ0 := projection_pieceMap F Q A hK Ψ hΨ
  have hπG := projection_pieceSyncMap Q F c b L w (pieceMap F Q A hK Ψ) hπ0 σ hcol hw hwL (q, v)
  have hrec := pieceMap_pieceAngle F Q A hK Ψ hΨ hιi hπG
  by_cases hq : ∃ l, q ∈ (Q.collar l).target
  · obtain ⟨l, hl⟩ := hq
    rw [syncInv_of_mem Q F c b L w _ hl, hrec, syncMap_of_mem Q F c b L w _ hl,
      LiftedBicollar.flow_neg_flow, pieceAngle_pieceMap]
  · push Not at hq
    rw [syncInv_of_not_mem Q F c b L w _ hq, hrec, syncMap_of_not_mem Q F c b L w _ hq,
      pieceAngle_pieceMap]

include hΨ hιi hcol hw hwL in
theorem pieceSyncMap_pieceSyncInv (p : Q.surface.Carrier × Circle) :
    pieceAngle F Q A hK Ψ (pieceSyncMap Q F c b L w (pieceMap F Q A hK Ψ)
      (p.1, pieceAngle F Q A hK Ψ (pieceSyncInv Q F c b L w (pieceMap F Q A hK Ψ) p))) = p.2 := by
  obtain ⟨q, u⟩ := p
  have hπ0 := projection_pieceMap F Q A hK Ψ hΨ
  by_cases hq : ∃ l, q ∈ (Q.collar l).target
  · obtain ⟨l, hl⟩ := hq
    have hπG' := projection_pieceSyncInv Q F c b L w (pieceMap F Q A hK Ψ) hπ0 σ hcol hw hwL hl u
    have hrec := pieceMap_pieceAngle F Q A hK Ψ hΨ hιi hπG'
    rw [syncMap_of_mem Q F c b L w _ hl, hrec, syncInv_of_mem Q F c b L w _ hl,
      LiftedBicollar.flow_flow_neg, pieceAngle_pieceMap]
  · push Not at hq
    have hπ := hπ0 (q, u)
    rw [syncMap_of_not_mem Q F c b L w _ hq, syncInv_of_not_mem Q F c b L w _ hq,
      pieceMap_pieceAngle F Q A hK Ψ hΨ hιi hπ, pieceAngle_pieceMap]

def pieceSyncH : (Q.surface.Carrier × Circle) ≃ₘ⟮(SurfaceModel.model Q.surface.kind).prod (𝓡 1),
    (SurfaceModel.model Q.surface.kind).prod (𝓡 1)⟯ (Q.surface.Carrier × Circle) where
  toFun p := (p.1, pieceAngle F Q A hK Ψ (pieceSyncMap Q F c b L w (pieceMap F Q A hK Ψ) p))
  invFun p := (p.1, pieceAngle F Q A hK Ψ (pieceSyncInv Q F c b L w (pieceMap F Q A hK Ψ) p))
  left_inv p := Prod.ext rfl (pieceSyncInv_pieceSyncMap F Q A hK Ψ hΨ hιi c b L w σ hcol hw hwL p)
  right_inv p := Prod.ext rfl (pieceSyncMap_pieceSyncInv F Q A hK Ψ hΨ hιi c b L w σ hcol hw hwL p)
  contMDiff_toFun := contMDiff_fst.prodMk (contMDiff_pieceAngle_comp F Q A hK Ψ
    (contMDiff_pieceSyncMap Q F c b L w _ (contMDiff_pieceMap_opens F Q A hK Ψ) hw hw1)
    fun p => ⟨p.1, (projection_pieceSyncMap Q F c b L w _ (projection_pieceMap F Q A hK Ψ hΨ)
      σ hcol hw hwL p).symm⟩)
  contMDiff_invFun := contMDiff_fst.prodMk (contMDiff_pieceAngle_comp F Q A hK Ψ
    (contMDiff_pieceSyncInv Q F c b L w _ (contMDiff_pieceMap_opens F Q A hK Ψ) hw hw1)
    fun p => by
      by_cases hq : ∃ l, p.1 ∈ (Q.collar l).target
      · obtain ⟨l, hl⟩ := hq
        exact ⟨_, (projection_pieceSyncInv Q F c b L w _ (projection_pieceMap F Q A hK Ψ hΨ)
          σ hcol hw hwL hl p.2).symm⟩
      · push Not at hq
        refine ⟨p.1, ?_⟩
        rw [syncInv_of_not_mem Q F c b L w _ hq, projection_pieceMap F Q A hK Ψ hΨ])

theorem pieceSyncMap_eq_comp (p : Q.surface.Carrier × Circle) :
    pieceSyncMap Q F c b L w (pieceMap F Q A hK Ψ) p =
      pieceMap F Q A hK Ψ (pieceSyncH F Q A hK Ψ hΨ hιi c b L w σ hcol hw hw1 hwL p) :=
  (pieceMap_pieceAngle F Q A hK Ψ hΨ hιi (projection_pieceSyncMap Q F c b L w _
    (projection_pieceMap F Q A hK Ψ hΨ) σ hcol hw hwL p)).symm

end Synced

section Main

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

theorem exists_syncedPiece (F : CircleFibration C U) {k : ℕ} (hk : k ∈ ({1, 2, 3} : Finset ℕ))
    (Q : PlanarBase.{u} k) {ι : Q.surface.Carrier → F.base.Carrier}
    (hι : Manifold.IsSmoothEmbedding (SurfaceModel.model Q.surface.kind)
      (SurfaceModel.model F.base.kind) ∞ ι)
    (c : Fin k → PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model F.base.kind)
      (Circle × ℝ) F.base.Carrier ∞)
    (hc : ∀ l, (c l).source = {p | -1 < p.2 ∧ p.2 < 1}) (b : Fin k → Bool)
    (σ : Fin k → (Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle))
    (hcol : ∀ l t s (hs : 0 ≤ s), s < 1 →
      ι (Q.collar l (t, halfPoint s hs)) = c l (σ l t, if b l then s else -s))
    (hint : ∀ q, (SurfaceModel.model F.base.kind).IsInteriorPoint (ι q))
    (L : ∀ l, LiftedBicollar F (c l)) :
    ∃ Φ : Q.surface.Carrier × Circle → U,
      ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) C.model ∞
        (fun q => (Φ q).val) ∧
      Topology.IsClosedEmbedding Φ ∧
      (∀ q, Function.Bijective (mfderiv ((SurfaceModel.model Q.surface.kind).prod (𝓡 1))
        C.model (fun q => (Φ q).val) q)) ∧
      (∀ q, F.projection (Φ q) = ι q.1) ∧ range Φ = F.projection ⁻¹' range ι ∧
      ∃ δ > 0, ∀ l t v s (hs : 0 ≤ s), s < δ →
        Φ (Q.collar l (t, halfPoint s hs), v) =
          (L l).flow (if b l then s else -s) (Φ (Q.collar l (t, halfZero), v)) := by
  have hk0 : 0 < k := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    omega
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk0⟩, Finset.mem_univ _⟩
  let w : ℝ := min (1 / 2) (Finset.univ.inf' hne fun l => (L l).width)
  have hw : 0 < w := lt_min (by norm_num)
    ((Finset.lt_inf'_iff hne).mpr fun l _ => (L l).width_pos)
  have hw1 : w / 2 < 1 := by
    have : w ≤ 1 / 2 := min_le_left _ _
    linarith
  have hwL : ∀ l, w ≤ (L l).width := fun l =>
    (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ l))
  have hK := isClosed_range_piece Q hι
  let A := (nonempty_pieceAtlas Q hι c hc b σ hcol hint).some
  obtain ⟨Ψ, hΨ⟩ := exists_restrictProduct F hk Q hι A hK
  have hιi : Function.Injective ι := hι.isEmbedding.injective
  let Φ₀ := pieceMap F Q A hK Ψ
  let H := pieceSyncH F Q A hK Ψ hΨ hιi c b L w σ hcol hw hw1 hwL
  let G := pieceSyncMap Q F c b L w Φ₀
  have hGH : ∀ p, G p = Φ₀ (H p) := pieceSyncMap_eq_comp F Q A hK Ψ hΨ hιi c b L w σ hcol hw hw1 hwL
  have hGsm : ContMDiff ((SurfaceModel.model Q.surface.kind).prod (𝓡 1)) C.model ∞ G :=
    contMDiff_pieceSyncMap Q F c b L w Φ₀ (contMDiff_pieceMap_opens F Q A hK Ψ) hw hw1
  have hGinj : Function.Injective G := by
    intro p p' h
    rw [hGH, hGH] at h
    exact H.injective (injective_pieceMap F Q A hK Ψ h)
  refine ⟨G, contMDiff_subtype_val.comp hGsm, ?_, ?_, ?_, ?_, ?_⟩
  · exact hGsm.continuous.isClosedEmbedding hGinj
  · intro p
    have hcomp : (fun q => (G q).val) = (fun q => (Φ₀ q).val) ∘ H := funext fun q => by
      simp only [Function.comp_apply, hGH]
    rw [hcomp, mfderiv_comp p ((contMDiff_pieceMap F Q A hK Ψ).mdifferentiableAt (by simp))
      (H.contMDiff.mdifferentiableAt (by simp))]
    exact (bijective_mfderiv_pieceMap F Q A hK Ψ (H p)).comp
      (H.mfderivToContinuousLinearEquiv (by simp) p).bijective
  · exact projection_pieceSyncMap Q F c b L w Φ₀ (projection_pieceMap F Q A hK Ψ hΨ) σ hcol hw hwL
  · rw [← range_pieceMap F Q A hK Ψ]
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨H p, (hGH p).symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨H.symm p, by rw [hGH, H.apply_symm_apply]⟩
  · refine ⟨w / 4, by positivity, fun l t v s hs hsδ => ?_⟩
    have hs1 : s < 1 := by linarith
    have h1 : G (Q.collar l (t, halfPoint s hs), v) =
        (L l).flow (if b l then s else -s) (Φ₀ (Q.collar l (t, halfZero), v)) :=
      syncMap_collar_small Q F c b L w Φ₀ hw t hs hsδ.le hs1 v
    have h0 : G (Q.collar l (t, halfPoint 0 le_rfl), v) =
        (L l).flow (if b l then 0 else -0) (Φ₀ (Q.collar l (t, halfZero), v)) :=
      syncMap_collar_small Q F c b L w Φ₀ hw t le_rfl (by positivity) one_pos v
    have h00 : (if b l then (0 : ℝ) else -0) = 0 := by cases b l <;> simp
    rw [h00, (L l).flow_zero] at h0
    change G (Q.collar l (t, halfPoint s hs), v) =
      (L l).flow (if b l then s else -s) (G (Q.collar l (t, halfPoint 0 le_rfl), v))
    rw [h0, h1]

end Main

end GC.Seifert
