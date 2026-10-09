/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.WallSystemBlocks
import DifferentialGeometry.Topology.PiecewiseLinear.DoubleHalfSpaceChart
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChart
import DifferentialGeometry.Topology.PiecewiseLinear.SingularNormalForm
import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldConnectivity
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldFaces
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryFacets
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryTraceTransport
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryOfBall
import DifferentialGeometry.Topology.PiecewiseLinear.GeneratedSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.DualCells

open Set Topology Metric
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem isPiecewiseAffineOn_val_of_mem_maximalAtlas {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (X : Geometry.SimplicialComplex ℝ F)
    [Finite X.faces] {n : ℕ} (hX : IsCombinatorialManifold (n + 1) X)
    {ec : OpenPartialHomeomorph X.space (EuclideanSpace ℝ (Fin (n + 1)))}
    (hec : letI := combinatorialChartedSpace X hX
      ec ∈ (plGroupoid (n + 1)).maximalAtlas X.space) :
    IsPiecewiseAffineOn (fun q => if h : q ∈ X.space then ec ⟨q, h⟩ else 0)
      (Subtype.val '' ec.source) := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) X.space := combinatorialChartedSpace X hX
  have : HasGroupoid X.space (plGroupoid (n + 1)) := combinatorialChartedSpace_hasGroupoid X hX
  rintro _ ⟨x₀, hx₀, rfl⟩
  set e := chartAt (EuclideanSpace ℝ (Fin (n + 1))) x₀ with he
  obtain ⟨p, hp, hep⟩ := mem_combinatorialChartedSpace_atlas X hX (chart_mem_atlas _ x₀)
  have hT : e.symm ≫ₕ ec ∈ plGroupoid (n + 1) :=
    StructureGroupoid.compatible_of_mem_maximalAtlas
      (StructureGroupoid.chart_mem_maximalAtlas _ x₀) hec
  have hTpl : IsPiecewiseAffineOn (e.symm ≫ₕ ec) (e.symm ≫ₕ ec).source :=
    (mem_plGroupoid_iff.mp hT).1
  have hepl : IsPiecewiseAffineOn (fun q => if h : q ∈ X.space then e ⟨q, h⟩ else 0)
      (Subtype.val '' e.source) := by
    rw [he, hep]
    exact isPiecewiseAffineOn_vertexChart X hp (hX.isPLSphere_link hp)
  have hcomp := hTpl.comp hepl
  obtain ⟨U, hUo, hUe⟩ := isOpen_induced_iff.mp e.open_source
  have hx₀e : x₀ ∈ e.source := mem_chart_source _ x₀
  have hD : Subtype.val '' e.source ∩
      (fun q => if h : q ∈ X.space then e ⟨q, h⟩ else 0) ⁻¹' (e.symm ≫ₕ ec).source =
      Subtype.val '' ec.source ∩ U := by
    ext q
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxT⟩
      simp only [mem_preimage, dite_eq_left x.2, Subtype.coe_eta] at hxT
      rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, OpenPartialHomeomorph.symm_source,
        mem_preimage, e.left_inv hx] at hxT
      refine ⟨⟨x, hxT.2, rfl⟩, ?_⟩
      rw [← hUe] at hx
      exact hx
    · rintro ⟨⟨x, hx, rfl⟩, hxU⟩
      have hxe : x ∈ e.source := by
        rw [← hUe]
        exact hxU
      refine ⟨⟨x, hxe, rfl⟩, ?_⟩
      simp only [mem_preimage, dite_eq_left x.2, Subtype.coe_eta]
      rw [OpenPartialHomeomorph.trans_source, mem_inter_iff, OpenPartialHomeomorph.symm_source,
        mem_preimage, e.left_inv hxe]
      exact ⟨e.map_source hxe, hx⟩
  have hx₀U : (x₀ : F) ∈ U := by
    have : x₀ ∈ Subtype.val ⁻¹' U := by rw [hUe]; exact hx₀e
    exact this
  have h1 := hcomp x₀ (hD ▸ ⟨⟨x₀, hx₀, rfl⟩, hx₀U⟩)
  rw [hD] at h1
  refine (h1.congr ?_).of_inter_of_mem_nhds (hUo.mem_nhds hx₀U)
  rintro _ ⟨⟨x, hx, rfl⟩, hxU⟩
  have hxe : x ∈ e.source := by
    rw [← hUe]
    exact hxU
  simp only [Function.comp_apply, dite_eq_left x.2, Subtype.coe_eta, OpenPartialHomeomorph.coe_trans,
    e.left_inv hxe]

theorem exists_wallSides_of_isCombinatorialManifold {Ea : Type*} [NormedAddCommGroup Ea]
    [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea] (Q : Geometry.SimplicialComplex ℝ Ea)
    [Finite Q.faces] (hQ : IsCombinatorialManifold 3 Q) {w : Finset Ea}
    (hw : w ∈ Q.faces) (hw3 : w.card = 3) :
    ∃ cm ∈ Q.faces, ∃ cp ∈ Q.faces, cm.card = 4 ∧ cp.card = 4 ∧ cm ≠ cp ∧ w ⊆ cm ∧ w ⊆ cp ∧
      ∀ c ∈ Q.faces, c.card = 4 → w ⊆ c → c = cm ∨ c = cp := by
  classical
  obtain ⟨a, b, hab, hset⟩ := IsCombinatorialManifold.codimension_one_cofaces Q hQ hw hw3
  have ha : a ∉ w ∧ insert a w ∈ Q.faces := by
    have : a ∈ {v | v ∉ w ∧ insert v w ∈ Q.faces} := by rw [hset]; exact Or.inl rfl
    exact this
  have hb : b ∉ w ∧ insert b w ∈ Q.faces := by
    have : b ∈ {v | v ∉ w ∧ insert v w ∈ Q.faces} := by rw [hset]; exact Or.inr rfl
    exact this
  refine ⟨insert a w, ha.2, insert b w, hb.2, by rw [Finset.card_insert_of_notMem ha.1, hw3],
    by rw [Finset.card_insert_of_notMem hb.1, hw3], ?_, Finset.subset_insert a w,
    Finset.subset_insert b w, ?_⟩
  · intro hEq
    have : a ∈ insert b w := by rw [← hEq]; exact Finset.mem_insert_self a w
    rcases Finset.mem_insert.mp this with h | h
    · exact hab h
    · exact ha.1 h
  · intro c hc hc4 hwc
    have hcw : (c \ w).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hwc, hc4, hw3]
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcw
    have hvc : v ∈ c \ w := by rw [hv]; exact Finset.mem_singleton_self v
    have hcv : c = insert v w := by
      have h1 : w ∪ c \ w = c := Finset.union_sdiff_of_subset hwc
      rw [hv] at h1
      rw [← h1]
      ext u
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
      tauto
    have hvset : v ∈ {v | v ∉ w ∧ insert v w ∈ Q.faces} :=
      ⟨(Finset.mem_sdiff.mp hvc).2, hcv ▸ hc⟩
    rw [hset] at hvset
    rcases hvset with h | h
    · left
      rw [hcv, h]
    · right
      rw [hcv, mem_singleton_iff.mp h]

open Classical in
theorem exists_commonWallComplex {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (n : ℕ) :
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K hK)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
    ∀ (V : Fin n → Set (double 3 K).space)
      (ec : Fin n → OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)))
      (ℓ : Fin n → (EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)),
      (∀ i, ec i ∈ (plGroupoid 3).maximalAtlas (double 3 K).space) → (∀ i, ℓ i ≠ 0) →
        (∀ i, ∀ x ∈ (ec i).source, x ∈ C ↔ 0 ≤ ℓ i (ec i x)) →
        (∀ i, ∀ x ∈ (ec i).source, x ∈ Bd ↔ ℓ i (ec i x) = 0) →
        (∀ i, closure (V i) ⊆ (ec i).source) →
        ∃ (Q : Geometry.SimplicialComplex ℝ (E × E × ℝ))
          (Cf Bf : Set (Finset (E × E × ℝ))) (Eb Eb' : Fin n → Set (double 3 K).space),
          IsSubdivision Q (double 3 K) ∧ (∀ i, closure (V i) ⊆ interior (Eb i)) ∧
            IsCommonWallSystem Q ((↑) : (double 3 K).space → E × E × ℝ) Cf Bf Bd C
              ec ℓ Eb Eb' := by
  intro ι C Bd V ec ℓ hec hℓ hCc hBdc hV
  let _ : DecidableEq (E × E × ℝ) := fun a b => Classical.propDecidable (a = b)
  have hL : IsCombinatorialManifold 3 (double 3 K) := isCombinatorialManifold_double_succ_succ K hK
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (double 3 K).space :=
    combinatorialChartedSpace (double 3 K) hL
  let X := double 3 K
  have hXc : IsCompact X.space := (isPolyhedron_space X).isCompact
  have : CompactSpace X.space := isCompact_iff_compactSpace.mp hXc
  let A : Fin n → Set (E × E × ℝ) := fun i => Subtype.val '' closure (V i)
  have hAc : ∀ i, IsCompact (A i) := fun i =>
    isClosed_closure.isCompact.image continuous_subtype_val
  have hOex : ∀ i, ∃ O : Set (E × E × ℝ), IsOpen O ∧ Subtype.val ⁻¹' O = (ec i).source :=
    fun i => isOpen_induced_iff.mp (ec i).open_source
  choose O hOo hOe using hOex
  have hAO : ∀ i, A i ⊆ O i := by
    rintro i _ ⟨x, hx, rfl⟩
    have h1 : x ∈ (ec i).source := hV i hx
    rw [← hOe i] at h1
    exact h1
  have hdex : ∀ i, ∃ d : ℝ, 0 < d ∧ thickening d (A i) ⊆ O i :=
    fun i => (hAc i).exists_thickening_subset_open (hOo i) (hAO i)
  choose d hdpos hdsub using hdex
  obtain ⟨μ₀, hμ₀, hμ₀le⟩ : ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ i, μ₀ ≤ d i := by
    rcases isEmpty_or_nonempty (Fin n) with hn | hn
    · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
    · exact ⟨Finset.univ.inf' Finset.univ_nonempty d,
        (Finset.lt_inf'_iff _).mpr fun i _ => hdpos i,
        fun i => Finset.inf'_le _ (Finset.mem_univ i)⟩
  set μ : ℝ := μ₀ / 4 with hμdef
  have hμ : 0 < μ := by positivity
  obtain ⟨X₀, hX₀, hX₀fin, -, hX₀diam⟩ := exists_isSubdivision_diam_lt X
    (fun s hs => card_le_finrank_succ_of_mem_faces X hs) hμ
  have : Finite X₀.faces := hX₀fin.to_subtype
  have hX₀sp : X₀.space = X.space := hX₀.space_eq
  let L : Fin n → Geometry.SimplicialComplex ℝ (E × E × ℝ) := fun i =>
    subcomplexGeneratedBy X₀
      {s | (convexHull ℝ (s : Set (E × E × ℝ)) ∩ thickening (3 * μ) (A i)).Nonempty}
  have hLX₀ : ∀ i, (L i).faces ⊆ X₀.faces := fun i => subcomplexGeneratedBy_faces_subset X₀ _
  have hLfin : ∀ i, (L i).faces.Finite := fun i => subcomplexGeneratedBy_faces_finite X₀ _
  have hLK : ∀ i, (L i).space ⊆ X₀.space := fun i => space_mono_of_faces_subset (hLX₀ i)
  have hLO : ∀ i, (L i).space ⊆ O i := by
    intro i z hz
    rw [subcomplexGeneratedBy_space] at hz
    obtain ⟨t, ⟨htX, w, hwt, hwA⟩, hzt⟩ := mem_iUnion₂.mp hz
    obtain ⟨a, haA, hwa⟩ := mem_thickening_iff.mp hwA
    have hzw : dist z w < μ :=
      (dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isBounded hzt
        hwt).trans_lt (hX₀diam t htX)
    have h4 : 4 * μ = μ₀ := by rw [hμdef]; ring
    apply hdsub i
    exact mem_thickening_iff.mpr ⟨a, haA, by linarith [dist_triangle z w a, hμ₀le i]⟩
  have hLcov : ∀ i, cthickening (2 * μ) (A i) ∩ X.space ⊆ (L i).space := by
    rintro i z ⟨hzc, hzX⟩
    rw [← hX₀sp] at hzX
    obtain ⟨t, ht, hzt⟩ := X₀.mem_space_iff.mp hzX
    rw [subcomplexGeneratedBy_space]
    exact mem_iUnion₂.mpr ⟨t, ⟨ht, z, hzt,
      cthickening_subset_thickening' (by positivity) (by linarith) _ hzc⟩, hzt⟩
  have hLsrc : ∀ i, (L i).space ⊆ Subtype.val '' (ec i).source := by
    intro i z hz
    have hzX : z ∈ X.space := hX₀sp ▸ hLK i hz
    refine ⟨⟨z, hzX⟩, ?_, rfl⟩
    have h1 : (⟨z, hzX⟩ : X.space) ∈ Subtype.val ⁻¹' O i := hLO i hz
    rwa [hOe i] at h1
  let F : Fin n → E × E × ℝ → EuclideanSpace ℝ (Fin 3) := fun i q =>
    if h : q ∈ X.space then ec i ⟨q, h⟩ else 0
  have hF : ∀ i, IsPiecewiseAffineOn (F i) (Subtype.val '' (ec i).source) := fun i =>
    isPiecewiseAffineOn_val_of_mem_maximalAtlas X hL (hec i)
  have hFL : ∀ i, IsPiecewiseAffineOn (F i) (L i).space := by
    intro i
    have : Finite (L i).faces := (hLfin i).to_subtype
    exact (hF i).mono_of_isPolyhedron (isPolyhedron_space (L i)) (hLsrc i)
  obtain ⟨K', hK', hK'fin, hK'aff⟩ :=
    exists_isSubdivision_affineOn_subcomplexes_finite X₀ L hLfin hLK F hFL
  have : Finite K'.faces := hK'fin.to_subtype
  obtain ⟨Q, hQ, hQfin, -, hQdiam⟩ := exists_isSubdivision_diam_lt K'
    (fun s hs => card_le_finrank_succ_of_mem_faces K' hs) hμ
  have : Finite Q.faces := hQfin.to_subtype
  have hQX : IsSubdivision Q X := hQ.trans (hK'.trans hX₀)
  have hQman : IsCombinatorialManifold 3 Q := hL.of_isSubdivision hQX
  set G₂ := glued₂ K (PiecewiseLinear.boundaryComplex 3 K) id with hG₂def
  have : Finite G₂.faces :=
    (glued₂_faces_finite K (PiecewiseLinear.boundaryComplex 3 K) id).to_subtype
  have hG₂X : G₂.faces ⊆ X.faces := fun t ht => Or.inr ht
  have hG₂sp : G₂.space = ι '' K.space := glued₂_space K (PiecewiseLinear.boundaryComplex 3 K) id
  have hiso : @IsGlueIso E (E × E × ℝ) _ _ _ _ K G₂
      (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id) (glueSnd E E)
      (fun a b => Classical.propDecidable (a = b))
      (fun a b => Classical.propDecidable (a = b)) := by
    convert isGlueIso_glued₂_id K (PiecewiseLinear.boundaryComplex 3 K)
  have hG₂man : IsCombinatorialManifoldWithBoundary 3 G₂ :=
    hiso.isCombinatorialManifoldWithBoundary hK
  have hB₂ : (PiecewiseLinear.boundaryComplex 3 G₂).space =
      ι '' (PiecewiseLinear.boundaryComplex 3 K).space :=
    boundaryComplex_space_of_isPLHomeomorphOn K G₂ hK hiso.isPLHomeomorphOn
  set Q' := restrict Q G₂.space with hQ'def
  have hQ'sub : IsSubdivision Q' G₂ := hQX.restrict G₂ hG₂X
  have : Finite Q'.faces := (hQfin.subset (restrict_faces_subset Q _)).to_subtype
  have hQ'man : IsCombinatorialManifoldWithBoundary 3 Q' := hG₂man.of_isSubdivision hQ'sub
  have hQ'B : (PiecewiseLinear.boundaryComplex 3 Q').space =
      ι '' (PiecewiseLinear.boundaryComplex 3 K).space :=
    (boundaryComplex_space_of_isSubdivision G₂ Q' hG₂man hQ'sub).trans hB₂
  have : Finite (PiecewiseLinear.boundaryComplex 3 G₂).faces :=
    (boundaryComplex_faces_finite 3 G₂).to_subtype
  have hBG₂man : IsCombinatorialManifold 2 (PiecewiseLinear.boundaryComplex 3 G₂) :=
    isCombinatorialManifold_boundaryComplex G₂ hG₂man
  set Q'' := restrict Q (PiecewiseLinear.boundaryComplex 3 G₂).space with hQ''def
  have hQ''sub : IsSubdivision Q'' (PiecewiseLinear.boundaryComplex 3 G₂) :=
    hQX.restrict _ (fun t ht => hG₂X ht.1)
  have : Finite Q''.faces := (hQfin.subset (restrict_faces_subset Q _)).to_subtype
  have hQ''man : IsCombinatorialManifold 2 Q'' := hBG₂man.of_isSubdivision hQ''sub
  let Cf : Set (Finset (E × E × ℝ)) :=
    {c | c ∈ wallSystemCells Q ∧ convexHull ℝ (c : Set (E × E × ℝ)) ⊆ ι '' K.space}
  let Bf : Set (Finset (E × E × ℝ)) :=
    {w | w ∈ wallSystemWalls Q ∧ convexHull ℝ (w : Set (E × E × ℝ)) ⊆
      ι '' (PiecewiseLinear.boundaryComplex 3 K).space}
  let Eb : Fin n → Set X.space := fun i => Subtype.val ⁻¹' cthickening μ (A i)
  let Eb' : Fin n → Set X.space := fun i => Subtype.val ⁻¹' cthickening (2 * μ) (A i)
  have hVEb : ∀ i, closure (V i) ⊆ interior (Eb i) := by
    intro i x hx
    have hsub : Subtype.val ⁻¹' thickening μ (A i) ⊆ Eb i :=
      fun y hy => thickening_subset_cthickening μ (A i) hy
    exact interior_maximal hsub (isOpen_thickening.preimage continuous_subtype_val)
      (self_subset_thickening hμ (A i) ⟨x, hx, rfl⟩)
  refine ⟨Q, Cf, Bf, Eb, Eb', hQX, hVEb, ?_⟩
  exact {
    finiteFaces := hQfin
    dimLe := fun s hs => by
      obtain ⟨t, -, hst, htc⟩ := IsCombinatorialManifold.exists_face_superset_card_eq Q hQman hs
      exact (Finset.card_le_card hst).trans htc.le
    memCell := fun s hs => by
      obtain ⟨t, ht, hst, htc⟩ := IsCombinatorialManifold.exists_face_superset_card_eq Q hQman hs
      exact ⟨t, ⟨ht, htc⟩, hst⟩
    continuous := continuous_subtype_val
    injective := Subtype.val_injective
    rangeEq := by rw [Subtype.range_coe, hQX.space_eq]
    facesC := fun c hc => hc.1
    facesBd := fun w hw => hw.1
    eqC := by
      ext x
      constructor
      · intro hx
        have hxG : (x : E × E × ℝ) ∈ Q'.space := by
          rw [hQ'sub.space_eq, hG₂sp]
          exact hx
        obtain ⟨s, hs, hxs⟩ := Q'.mem_space_iff.mp hxG
        obtain ⟨t, ht, hst, htc⟩ := hQ'man.exists_face_superset_card_eq hs
        exact mem_iUnion₂.mpr ⟨t, ⟨⟨ht.1, htc⟩, hG₂sp ▸ ht.2⟩,
          convexHull_mono (Finset.coe_subset.mpr hst) hxs⟩
      · intro hx
        obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp hx
        exact hc.2 hxc
    eqBd := by
      ext x
      constructor
      · intro hx
        have hxB : (x : E × E × ℝ) ∈ Q''.space := by
          rw [hQ''sub.space_eq, hB₂]
          exact hx
        obtain ⟨s, hs, hxs⟩ := Q''.mem_space_iff.mp hxB
        obtain ⟨t, ht, hst, htc⟩ := IsCombinatorialManifold.exists_face_superset_card_eq Q''
          hQ''man hs
        exact mem_iUnion₂.mpr ⟨t, ⟨⟨ht.1, htc⟩, hB₂ ▸ ht.2⟩,
          convexHull_mono (Finset.coe_subset.mpr hst) hxs⟩
      · intro hx
        obtain ⟨w, hw, hxw⟩ := mem_iUnion₂.mp hx
        exact hw.2 hxw
    wallSides := fun w hw => by
      obtain ⟨cm, hcm, cp, hcp, hcm4, hcp4, hne, hwm, hwp, huniq⟩ :=
        exists_wallSides_of_isCombinatorialManifold Q hQman hw.1 hw.2
      exact ⟨cm, ⟨hcm, hcm4⟩, cp, ⟨hcp, hcp4⟩, hne, hwm, hwp,
        fun c hc hwc => huniq c hc.1 hc.2 hwc⟩
    boundarySides := fun w hw => by
      have hwK : convexHull ℝ (w : Set (E × E × ℝ)) ⊆ G₂.space := by
        rw [hG₂sp]
        exact hw.2.trans (image_mono (boundaryComplex_space_subset 3 K))
      have hwQ' : w ∈ Q'.faces := ⟨hw.1.1, hwK⟩
      have hne : w.Nonempty := Finset.card_pos.mp (by rw [hw.1.2]; norm_num)
      have hc₀ := centroid_mem_openSimplex hne
      have hc₀B : w.centroid ℝ id ∈ (PiecewiseLinear.boundaryComplex 3 Q').space := by
        rw [hQ'B]
        exact hw.2 (openSimplex_subset_convexHull w hc₀)
      have hwB : w ∈ (PiecewiseLinear.boundaryComplex 3 Q').faces :=
        mem_faces_of_mem_openSimplex_of_mem_space
          (fun t ht => ((mem_boundaryComplex_faces_iff 3 Q').mp ht).1) hwQ' hc₀ hc₀B
      obtain ⟨a, ha⟩ := (IsCombinatorialManifoldWithBoundary.mem_boundaryComplex_iff_unique_coface
        Q' hQ'man hw.1.2).mp hwB
      have haw : a ∉ w ∧ insert a w ∈ Q'.faces := by
        have : a ∈ {v | v ∉ w ∧ insert v w ∈ Q'.faces} := by rw [ha]; exact rfl
        exact this
      refine ⟨insert a w, ⟨⟨haw.2.1, by rw [Finset.card_insert_of_notMem haw.1, hw.1.2]⟩,
        hG₂sp ▸ haw.2.2⟩, Finset.subset_insert a w, ?_⟩
      intro c' hc' hwc'
      have hc'Q' : c' ∈ Q'.faces := ⟨hc'.1.1, hG₂sp ▸ hc'.2⟩
      have hcw : (c' \ w).card = 1 := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hwc', hc'.1.2, hw.1.2]
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcw
      have hvc : v ∈ c' \ w := by rw [hv]; exact Finset.mem_singleton_self v
      have hcv : c' = insert v w := by
        have h1 : w ∪ c' \ w = c' := Finset.union_sdiff_of_subset hwc'
        rw [hv] at h1
        rw [← h1]
        ext u
        simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
        tauto
      have hvset : v ∈ {v | v ∉ w ∧ insert v w ∈ Q'.faces} :=
        ⟨(Finset.mem_sdiff.mp hvc).2, hcv ▸ hc'Q'⟩
      rw [ha] at hvset
      rw [hcv, mem_singleton_iff.mp hvset]
    starLayer := fun i c hc hmeet => by
      obtain ⟨x₀, hx₀c, hx₀E⟩ := hmeet
      intro x hxc
      have hd : dist (x : E × E × ℝ) x₀ ≤ μ :=
        (dist_le_diam_of_mem (c.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isBounded hxc
          hx₀c).trans (hQdiam c hc.1).le
      have h1 : (x : E × E × ℝ) ∈ cthickening μ (cthickening μ (A i)) :=
        mem_cthickening_of_dist_le _ _ _ _ hx₀E hd
      have h2 := cthickening_cthickening_subset hμ.le hμ.le (A i) h1
      change (x : E × E × ℝ) ∈ cthickening (2 * μ) (A i)
      rwa [two_mul]
    layerSubset := fun i x hx => cthickening_mono (by linarith) _ hx
    layerCompact := fun i => (isClosed_cthickening.preimage continuous_subtype_val).isCompact
    layerSource := fun i x hx => by
      have h1 : (x : E × E × ℝ) ∈ thickening (d i) (A i) :=
        cthickening_subset_thickening' (hdpos i) (by linarith [hμ₀le i]) _ hx
      have h2 : x ∈ Subtype.val ⁻¹' O i := hdsub i h1
      rwa [hOe i] at h2
    chartAtlas := hec
    normalNe := hℓ
    chartC := hCc
    chartBd := hBdc
    chartAffine := fun i s hs hsE => by
      have hsX : convexHull ℝ (s : Set (E × E × ℝ)) ⊆ X.space :=
        hQX.space_eq ▸ Q.convexHull_subset_space hs
      have hsL : convexHull ℝ (s : Set (E × E × ℝ)) ⊆ (L i).space := by
        intro p hp
        have hpE : (⟨p, hsX hp⟩ : X.space) ∈ Eb' i := hsE hp
        exact hLcov i ⟨hpE, hsX hp⟩
      have hc₀ := centroid_mem_openSimplex (Q.nonempty_of_mem_faces hs)
      have hc₀L : s.centroid ℝ id ∈ (restrict K' (L i).space).space := by
        rw [(hK'aff i).1]
        exact hsL (openSimplex_subset_convexHull s hc₀)
      obtain ⟨t, ht, hc₀t⟩ := (restrict K' (L i).space).mem_space_iff.mp hc₀L
      have hst : convexHull ℝ (s : Set (E × E × ℝ)) ⊆ convexHull ℝ (t : Set (E × E × ℝ)) :=
        hQ.convexHull_subset_of_mem_openSimplex ht.1 hs hc₀ hc₀t
      obtain ⟨Aff, hAff⟩ := (hK'aff i).2 t ht
      refine ⟨Aff, fun x hx => ?_⟩
      have h1 := hAff (hst hx)
      simp only [F, dite_eq_left (show (x : E × E × ℝ) ∈ X.space from x.2)] at h1
      exact h1 }

end DifferentialGeometry.Topology.PiecewiseLinear
