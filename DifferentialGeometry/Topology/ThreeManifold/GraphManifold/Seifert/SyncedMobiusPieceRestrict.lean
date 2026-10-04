import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarBundlePieces

/-!
# A circle fibration over an embedded Möbius piece

Lane MD5b, step (2) of `exists_syncedMobiusPiece`: the Möbius analogue of the piece atlas and the
piece diffeomorphism of `SF/PlanarBundlePieces.lean`.

Data: a `MobiusBase` `M`, a smooth embedding `ι : M → B` into the interior of the base, a bicollar
`c : S¹ × (-1, 1) → B` of the boundary circle with `ι (M.collar (t, s)) = c (σ t, ±s)`.
The image `K = range ι` is the closure of its interior, its frontier lies on the zero section of
`c`, so it carries a `SmoothBoundaryAtlas` (`nonempty_mobiusAtlas`), and `mobiusDiffeo`
identifies `M.surface` with the restricted base. Near the zero section, `K` lies on the side of
`c` prescribed by the collar formula (`exists_side_mobius`), and a point `ι q` lies on the zero
section of `c` exactly when `q` is on the boundary collar of `M` (`mem_zero_mobius_iff`).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

section MobiusAtlas

private theorem mobius_collar_mem_source (M : MobiusBase.{u}) (t : Circle) {s : ℝ} (hs : 0 ≤ s)
    (hs1 : s < 1) : (t, halfPoint s hs) ∈ M.collar.source := by
  rw [M.source_eq]
  exact hs1

private theorem mobius_isInteriorPoint_collar (M : MobiusBase.{u}) (t : Circle) {s : ℝ}
    (hs : 0 < s) (hs1 : s < 1) :
    (SurfaceModel.model M.surface.kind).IsInteriorPoint (M.collar (t, halfPoint s hs.le)) := by
  rw [ModelWithCorners.isInteriorPoint_iff_not_isBoundaryPoint]
  intro hb
  have hb' : M.collar (t, halfPoint s hs.le) ∈
      (SurfaceModel.model M.surface.kind).boundary M.surface.Carrier := hb
  rw [M.boundary_exhausted] at hb'
  obtain ⟨t', hj⟩ := hb'
  have h := M.collar.toOpenPartialHomeomorph.injOn
    (mobius_collar_mem_source M t' le_rfl one_pos) (mobius_collar_mem_source M t hs.le hs1) hj
  have h2 := congrArg (fun p : Circle × EuclideanHalfSpace 1 => p.2.val 0) h
  change (0 : ℝ) = s at h2
  linarith

variable {B : CompactSurface.{u}} (M : MobiusBase.{u})
  {ι : M.surface.Carrier → B.Carrier}
  (hι : Manifold.IsSmoothEmbedding (SurfaceModel.model M.surface.kind)
    (SurfaceModel.model B.kind) ∞ ι)
  (c : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ)) (SurfaceModel.model B.kind)
    (Circle × ℝ) B.Carrier ∞)
  (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) (b : Bool)
  (σ : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle)
  (hcol : ∀ t s (hs : 0 ≤ s), s < 1 →
    ι (M.collar (t, halfPoint s hs)) = c (σ t, if b then s else -s))
  (hint : ∀ q, (SurfaceModel.model B.kind).IsInteriorPoint (ι q))

include hcol in
theorem mobius_zero_eq (t : Circle) : ι (M.collar (t, halfZero)) = c (σ t, 0) := by
  have h := hcol t 0 le_rfl one_pos
  have h0 : (if b then (0 : ℝ) else -0) = 0 := by cases b <;> simp
  rw [h0] at h
  exact h

include hι in
private theorem isClosed_range_mobius : IsClosed (range ι) :=
  (isCompact_range hι.contMDiff.continuous).isClosed

include hι hint in
private theorem interior_range_mobius_of_isInteriorPoint {q : M.surface.Carrier}
    (hq : (SurfaceModel.model M.surface.kind).IsInteriorPoint q) : ι q ∈ interior (range ι) :=
  mem_interior_range_of_isInteriorPoint hι hq (hint q)

include hι hc hcol hint in
private theorem closure_interior_range_mobius : closure (interior (range ι)) = range ι := by
  refine subset_antisymm (closure_minimal interior_subset (isClosed_range_mobius M hι)) ?_
  rintro _ ⟨q, rfl⟩
  rcases (SurfaceModel.model M.surface.kind).isInteriorPoint_or_isBoundaryPoint q with hq | hq
  · exact subset_closure (interior_range_mobius_of_isInteriorPoint M hι hint hq)
  have hq' : q ∈ (SurfaceModel.model M.surface.kind).boundary M.surface.Carrier := hq
  rw [M.boundary_exhausted] at hq'
  obtain ⟨t, rfl⟩ := hq'
  let g : ℝ → B.Carrier := fun s => c (σ t, if b then s else -s)
  have hg : ContinuousAt g 0 := by
    have hpath : Continuous (fun s : ℝ => ((σ t, if b then s else -s) : Circle × ℝ)) := by
      cases b
      · exact continuous_const.prodMk continuous_neg
      · exact continuous_const.prodMk continuous_id
    have h0 : ((σ t, if b then (0 : ℝ) else -0) : Circle × ℝ) ∈ c.source := by
      rw [hc]
      cases b <;> norm_num
    have hcont : ContinuousAt c ((σ t, if b then (0 : ℝ) else -0) : Circle × ℝ) :=
      c.toOpenPartialHomeomorph.continuousOn.continuousAt (c.open_source.mem_nhds h0)
    exact ContinuousAt.comp (g := c)
      (f := fun s : ℝ => ((σ t, if b then s else -s) : Circle × ℝ)) (x := 0) hcont
      hpath.continuousAt
  have hg0 : g 0 = ι (M.collar (t, halfZero)) := by
    rw [mobius_zero_eq M c b σ hcol]
    change c (σ t, if b then (0 : ℝ) else -0) = _
    cases b <;> simp
  change ι (M.collar (t, halfZero)) ∈ _
  rw [← hg0]
  refine mem_closure_of_tendsto (f := g) (b := 𝓝[>] (0 : ℝ))
    (hg.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
  have h := hcol t s hs.1.le hs.2
  change c (σ t, if b then s else -s) ∈ interior (range ι)
  rw [← h]
  exact interior_range_mobius_of_isInteriorPoint M hι hint
    (mobius_isInteriorPoint_collar M t hs.1 hs.2)

include hι hcol hint in
private theorem frontier_range_mobius_subset :
    frontier (range ι) ⊆ range (fun θ : Circle => c (θ, 0)) := by
  intro x hx
  have hxK : x ∈ range ι := (isClosed_range_mobius M hι).frontier_subset hx
  obtain ⟨q, rfl⟩ := hxK
  rcases (SurfaceModel.model M.surface.kind).isInteriorPoint_or_isBoundaryPoint q with hq | hq
  · exact absurd (interior_range_mobius_of_isInteriorPoint M hι hint hq) hx.2
  have hq' : q ∈ (SurfaceModel.model M.surface.kind).boundary M.surface.Carrier := hq
  rw [M.boundary_exhausted] at hq'
  obtain ⟨t, rfl⟩ := hq'
  exact ⟨σ t, (mobius_zero_eq M c b σ hcol t).symm⟩

include hι hc hcol hint in
theorem nonempty_mobiusAtlas :
    Nonempty (SmoothBoundaryAtlas (SurfaceModel.model B.kind) 2 (range ι)) :=
  exists_smoothBoundaryAtlas_of_collars (fun _ : Unit => c) (fun _ q => by rw [hc]; norm_num)
    (fun i j hij => absurd (Subsingleton.elim i j) hij)
    (closure_interior_range_mobius M hι c hc b σ hcol hint)
    (fun x hx => mem_iUnion.mpr ⟨(), frontier_range_mobius_subset M hι c b σ hcol hint hx⟩)
    (fun x hx => by
      obtain ⟨q, rfl⟩ := interior_subset hx
      exact hint q)

include hι hc hcol in
theorem exists_side_mobius :
    ∃ r > (0 : ℝ), ∀ θ s, |s| < r → c (θ, s) ∈ range ι → 0 ≤ (if b then s else -s) := by
  obtain ⟨V, hVo, hV⟩ := hι.isEmbedding.isOpen_iff.mp M.collar.open_target
  have hzero : (univ : Set Circle) ×ˢ ({0} : Set ℝ) ⊆ c.source ∩ c ⁻¹' V := by
    rintro ⟨θ, s⟩ ⟨-, hs⟩
    rw [mem_singleton_iff] at hs
    subst hs
    refine ⟨by rw [hc]; norm_num, ?_⟩
    have h := mobius_zero_eq M c b σ hcol (σ.symm θ)
    rw [Diffeomorph.apply_symm_apply] at h
    change c (θ, 0) ∈ V
    rw [← h]
    change M.collar _ ∈ ι ⁻¹' V
    rw [hV]
    exact M.collar.map_source (mobius_collar_mem_source M _ le_rfl one_pos)
  obtain ⟨u, v, -, hvo, hu, h0v, huv⟩ := generalized_tube_lemma isCompact_univ
    isCompact_singleton
    (c.toOpenPartialHomeomorph.continuousOn.isOpen_inter_preimage c.open_source hVo) hzero
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hvo 0 (h0v rfl)
  refine ⟨min ε 1, lt_min hε one_pos, ?_⟩
  rintro θ s hs ⟨q, hq⟩
  have hsv : s ∈ v := hball (by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hs.trans_le (min_le_left _ _))
  have hθs : (θ, s) ∈ c.source ∩ c ⁻¹' V := huv ⟨hu (mem_univ θ), hsv⟩
  have hqV : q ∈ M.collar.target := by
    rw [← hV]
    change ι q ∈ V
    rw [hq]
    exact hθs.2
  obtain ⟨⟨t', h⟩, hp, hpq⟩ : ∃ p ∈ M.collar.source, M.collar p = q :=
    ⟨_, M.collar.toOpenPartialHomeomorph.map_target hqV,
      M.collar.toOpenPartialHomeomorph.right_inv hqV⟩
  have hp1 : h.val 0 < 1 := by
    rw [M.source_eq] at hp
    exact hp
  have h1 := hcol t' (h.val 0) h.2 hp1
  rw [halfPoint_coord_eq, hpq, hq] at h1
  have hsrc : (σ t', if b then h.val 0 else -h.val 0) ∈ c.source := by
    rw [hc]
    have h0 : 0 ≤ h.val 0 := h.2
    cases b
    · exact ⟨by simp; linarith, by simp; linarith⟩
    · exact ⟨by simp; linarith, by simp; linarith⟩
  have h2 := congrArg Prod.snd (c.toOpenPartialHomeomorph.injOn hθs.1 hsrc h1)
  change s = if b then h.val 0 else -h.val 0 at h2
  have h0 : 0 ≤ h.val 0 := h.2
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h2 ⊢
    linarith
  · simp only [↓reduceIte] at h2 ⊢
    linarith

include hι hcol in
theorem mem_zero_mobius_iff (q : M.surface.Carrier) :
    ι q ∈ range (fun θ : Circle => c (θ, 0)) ↔ q ∈ range (fun t => M.collar (t, halfZero)) := by
  constructor
  · rintro ⟨θ, hθ⟩
    have h := mobius_zero_eq M c b σ hcol (σ.symm θ)
    rw [Diffeomorph.apply_symm_apply] at h
    exact ⟨σ.symm θ, hι.isEmbedding.injective (h.trans hθ)⟩
  · rintro ⟨t, rfl⟩
    exact ⟨σ t, (mobius_zero_eq M c b σ hcol t).symm⟩

end MobiusAtlas

section MobiusDiffeo

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier} (F : CircleFibration C U)
  (M : MobiusBase.{u}) {ι : M.surface.Carrier → F.base.Carrier}
  (hι : Manifold.IsSmoothEmbedding (SurfaceModel.model M.surface.kind)
    (SurfaceModel.model F.base.kind) ∞ ι)
  (A : SmoothBoundaryAtlas (SurfaceModel.model F.base.kind) 2 (range ι)) (hK : IsClosed (range ι))

include hι in
theorem connectedSpace_range_mobius : ConnectedSpace (range ι) :=
  Subtype.connectedSpace (isConnected_range hι.contMDiff.continuous)

def mobiusDiffeo :
    letI := connectedSpace_range_mobius F M hι
    M.surface.Carrier ≃ₘ⟮SurfaceModel.model M.surface.kind,
      SurfaceModel.model (CircleFibration.restrictBase F A hK).kind⟯
      (CircleFibration.restrictBase F A hK).Carrier :=
  letI := connectedSpace_range_mobius F M hι
  { toEquiv := hι.isEmbedding.toHomeomorph.toEquiv
    contMDiff_toFun := by
      let _ := A.toChartedSpace
      exact (A.contMDiff_iff_subtype_val (fun q => hι.isEmbedding.toHomeomorph q)).mpr
        hι.contMDiff
    contMDiff_invFun := by
      let _ := A.toChartedSpace
      have h : ContMDiff (𝓡∂ 2) (SurfaceModel.model M.surface.kind) ∞
          (fun y : range ι => hι.isEmbedding.toHomeomorph.symm y) := by
        apply (ContMDiff.iff_comp_isImmersion hι.isImmersion).mpr
        refine ⟨hι.isEmbedding.toHomeomorph.symm.continuous, ?_⟩
        refine A.contMDiff_subtype_val.congr fun y => ?_
        exact congrArg Subtype.val (hι.isEmbedding.toHomeomorph.apply_symm_apply y)
      exact h }

theorem mobiusDiffeo_apply_val (q : M.surface.Carrier) :
    letI := connectedSpace_range_mobius F M hι
    Subtype.val (p := fun x => x ∈ range ι) (mobiusDiffeo F M hι A hK q) = ι q := rfl

end MobiusDiffeo

end GC.Seifert
