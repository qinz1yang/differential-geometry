import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarBundleMobius

/-!
# Twisted charts with smooth local left inverses

Lane MD5b, input of step (2) of `exists_syncedMobiusPiece`. The twisted chart of MD5's tier T4
(`MobiusCover.chartMap`) has, near every point, a smooth left inverse defined on an open subset
of the ambient carrier: the sheet inverse of the covering `pullProj`, followed by the base
projection and the angle of the glued fibre coordinate (as in the proof of
`MobiusCover.injective_mfderiv_pullSndU_assembled`), followed by the inverse of `unwrapA`,
`w ↦ (w / ‖w‖, (2 ‖w‖ - 1) / 5)`. This strengthens `circleBundlesOverPlanarBases_mobius`
(`circleBundlesOverPlanarBases_mobius_localInv`).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace MobiusCover

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

section LocalInverse

variable {F : CircleFibration C U} {E : F.base.Carrier → EuclideanSpace ℝ (Fin 3)}
  {hE : Manifold.IsSmoothEmbedding (SurfaceModel.model F.base.kind)
    𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ E} {hrange : range E = mobiusModel}

private def unwrapInv (w : annulusSurface.{u}.Carrier) : Circle × unitInterval :=
  (unitOf (annEmb w), ⟨(2 * ‖annEmb w‖ - 1) / 5, by linarith [(annEmb_mem w).1],
    by linarith [(annEmb_mem w).2]⟩)

private theorem unwrapInv_unwrapA (p : Circle × unitInterval) :
    unwrapInv.{u} (unwrapA.{u} p) = p := by
  have hpos : 0 < 1 / 2 + 5 / 2 * (p.2 : ℝ) := by linarith [p.2.2.1]
  refine Prod.ext (unitOf_smul hpos p.1) (Subtype.ext ?_)
  change (2 * ‖unwrap p.1 p.2‖ - 1) / 5 = (p.2 : ℝ)
  rw [norm_unwrap]
  ring

private theorem contMDiff_unwrapInv :
    ContMDiff (SurfaceModel.model annulusSurface.{u}.kind) ((𝓡 1).prod (𝓡∂ 1)) ∞
      unwrapInv.{u} := by
  have hemb : ContMDiff (SurfaceModel.model annulusSurface.{u}.kind) 𝓘(ℝ, ℂ) ∞ annEmb.{u} :=
    isSmoothEmbedding_annEmb.isImmersion.contMDiff
  have hne : ∀ w : annulusSurface.{u}.Carrier, annEmb w ≠ 0 := fun w =>
    norm_pos_iff.mp (norm_pos_of_mem_annulus (annEmb_mem w))
  have h1 : ContMDiff (SurfaceModel.model annulusSurface.{u}.kind) (𝓡 1) ∞
      (fun w : annulusSurface.{u}.Carrier => unitOf (annEmb w)) :=
    contMDiffOn_unitOf.comp_contMDiff hemb hne
  have h2 : ContMDiff (SurfaceModel.model annulusSurface.{u}.kind) 𝓘(ℝ, ℝ) ∞
      (fun w : annulusSurface.{u}.Carrier => (2 * ‖annEmb w‖ - 1) / 5) := fun w =>
    (((contDiffAt_const.mul (contDiffAt_norm ℝ (hne w))).sub contDiffAt_const).div_const
      _).contMDiffAt.comp w (hemb w)
  exact h1.prodMk (contMDiff_iff_comp_subtypeVal_Icc.mpr ⟨h2.continuous.subtype_mk _, h2⟩)

private theorem exists_sheet_localInv {X : Type*} [TopologicalSpace X] {EY HY Y : Type*}
    [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
    {J : ModelWithCorners ℝ EY HY} [TopologicalSpace Y] [ChartedSpace HY Y]
    (a : X → (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier)) {x₀ : X}
    (ha : ContinuousAt a x₀)
    {O : Set (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier)}
    (hO : IsOpen O) (h0 : a x₀ ∈ O)
    {g : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier) → Y}
    (hg : ContMDiffOn (pullCarrier F hE hrange).model J ∞ g O) :
    ∃ W : Set C.Carrier, IsOpen W ∧ (pullSndU (a x₀) : C.Carrier) ∈ W ∧
      ∃ G : C.Carrier → Y, ContMDiffOn C.model J ∞ G W ∧
        ∀ᶠ x in 𝓝 x₀, G (pullSndU (a x) : C.Carrier) = g (a x) := by
  set hl := isLocalHomeomorph_pullProj F hE hrange
  let := Manifold.coveringChartedSpace (H := C.kind.Space) hl
  let := Manifold.covering_isManifold hl C.model
  set e := hl.localInverseAt (a x₀).val
  have he : (e.symm : (pullCarrier F hE hrange).Carrier → C.Carrier) = pullProj F hrange :=
    hl.localInverseAt_symm (a x₀).val
  have hes := Manifold.covering_sheetInverse_contMDiff hl C.model e.symm (fun y _ => by
    rw [he])
  have hmem : (pullSndU (a x₀) : C.Carrier) ∈ e.source := hl.apply_self_mem_localInverseAt_source
  let sec : C.Carrier → (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier) :=
    fun x => ⟨e x, trivial⟩
  have hsec : ∀ x ∈ e.source, ContMDiffAt C.model (pullCarrier F hE hrange).model ∞ sec x := by
    intro x hx
    have h1 : ContMDiffAt C.model (pullCarrier F hE hrange).model ∞ (Subtype.val ∘ sec) x :=
      hes.contMDiffAt (e.symm.open_target.mem_nhds hx)
    exact (ContMDiffAt.subtypeVal_comp_iff ⊤ sec x).mp h1
  have hsec0 : sec (pullSndU (a x₀) : C.Carrier) = a x₀ := by
    apply Subtype.ext
    change e (pullProj F hrange (a x₀).val) = (a x₀).val
    rw [← he]
    exact e.right_inv hl.self_mem_localInverseAt_target
  refine ⟨e.source ∩ sec ⁻¹' O, ?_, ⟨hmem, ?_⟩, g ∘ sec, ?_, ?_⟩
  · exact ContinuousOn.isOpen_inter_preimage
      (fun x hx => (hsec x hx).continuousAt.continuousWithinAt) e.open_source hO
  · rw [mem_preimage, hsec0]
    exact h0
  · intro x hx
    exact ((hg.contMDiffAt (hO.mem_nhds hx.2)).comp x (hsec x hx.1)).contMDiffWithinAt
  · have hc : ContinuousAt (fun x => ((a x).val : (pullCarrier F hE hrange).Carrier)) x₀ :=
      continuous_subtype_val.continuousAt.comp ha
    filter_upwards [hc (e.open_target.mem_nhds hl.self_mem_localInverseAt_target)] with x hx
    change g (sec (pullProj F hrange (a x).val)) = g (a x)
    congr 1
    apply Subtype.ext
    change e (pullProj F hrange (a x).val) = (a x).val
    rw [← he]
    exact e.right_inv hx

private theorem exists_branch_localInv {τ : FibreCoordinate (pullFibration F hE hrange) ⊤}
    {τu : FibreCoordinate (pullFibration F hE hrange) (rightOpen ⊔ leftOpen)}
    (hU0 : ∀ w v, seamCutoff w = 0 → w ∈ rightOpen → τu.symmFn w v = τ.symmFn w v)
    (hU1 : ∀ w v, seamCutoff w = 1 → w ∈ leftOpen → τu.symmFn w v = (twistCoord τ).symmFn w v)
    (q₀ : annulusSurface.{u}.Carrier × Circle) :
    ∃ O : Set (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier), IsOpen O ∧
      assembled τu q₀ ∈ O ∧
      ∃ g : (⊤ : TopologicalSpace.Opens (pullCarrier F hE hrange).Carrier) →
          annulusSurface.{u}.Carrier × Circle,
        ContMDiffOn (pullCarrier F hE hrange).model
          ((SurfaceModel.model annulusSurface.{u}.kind).prod (𝓡 1)) ∞ g O ∧
        ∀ᶠ q in 𝓝 q₀, g (assembled τu q) = q := by
  by_cases h : 0 ≤ (annEmb q₀.1).im
  · refine ⟨(pullFibration F hE hrange).projection ⁻¹'
        ((rightOpen.{u} ⊔ leftOpen.{u} : TopologicalSpace.Opens _) :
          Set annulusSurface.{u}.Carrier),
      FibreCoordinate.isOpen_preimage _, ?_,
      fun y => ((pullFibration F hE hrange).projection y, τu.angle y),
      (pullFibration F hE hrange).smooth.contMDiffOn.prodMk τu.contMDiffOn_angle, ?_⟩
    · rw [mem_preimage, projection_assembled]
      exact mem_sup_of_im_nonneg h
    · filter_upwards [eventually_assembled_A hU0 hU1 h] with q hq
      change ((pullFibration F hE hrange).projection (assembled τu q),
        τu.angle (assembled τu q)) = q
      rw [projection_assembled, hq.1, τu.angle_symmFn hq.2]
  · have h' := not_le.mp h
    refine ⟨deckT F hE hrange ⁻¹' ((pullFibration F hE hrange).projection ⁻¹'
        ((rightOpen.{u} ⊔ leftOpen.{u} : TopologicalSpace.Opens _) :
          Set annulusSurface.{u}.Carrier)),
      (FibreCoordinate.isOpen_preimage _).preimage (contMDiff_deckT F hE hrange).continuous, ?_,
      fun y => ((pullFibration F hE hrange).projection y, (τu.angle (deckT F hE hrange y))⁻¹),
      (pullFibration F hE hrange).smooth.contMDiffOn.prodMk
        ((contMDiff_inv (𝓡 1) ∞).comp_contMDiffOn (τu.contMDiffOn_angle.comp
          (contMDiff_deckT F hE hrange).contMDiffOn fun y hy => hy)), ?_⟩
    · rw [mem_preimage, mem_preimage, projection_deckT, projection_assembled]
      exact annDeck_mem_sup_of_neg h'
    · filter_upwards [eventually_assembled_B (τu := τu) h'] with q hq
      change ((pullFibration F hE hrange).projection (assembled τu q),
        (τu.angle (deckT F hE hrange (assembled τu q)))⁻¹) = q
      rw [projection_assembled, hq.1, deckT_deckT, τu.angle_symmFn hq.2, inv_inv]

end LocalInverse

theorem exists_isTwistedChart_localInv (F : CircleFibration C U)
    {E : F.base.Carrier → EuclideanSpace ℝ (Fin 3)}
    (hE : Manifold.IsSmoothEmbedding (SurfaceModel.model F.base.kind)
      𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ E) (hrange : range E = mobiusModel) :
    ∃ Ψ : (Circle × unitInterval) × Circle → U, IsTwistedChart F E Ψ ∧
      ∀ p₀, ∃ W : Set C.Carrier, IsOpen W ∧ (Ψ p₀ : C.Carrier) ∈ W ∧
        ∃ G : C.Carrier → (Circle × unitInterval) × Circle,
          ContMDiffOn C.model (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) ∞ G W ∧
          ∀ᶠ p in 𝓝 p₀, G (Ψ p : C.Carrier) = p := by
  obtain ⟨τ, hτ⟩ := exists_positive_pullCoord F hE hrange
  obtain ⟨τu, hU0, hU1⟩ := exists_upperCoord F hE hrange τ hτ
  refine ⟨chartMap τu, isTwistedChart_chartMap hU0 hU1, fun p₀ => ?_⟩
  let φ : (Circle × unitInterval) × Circle → annulusSurface.{u}.Carrier × Circle :=
    fun p => (unwrapA p.1, p.2)
  have hφ : Continuous φ :=
    (contMDiff_unwrapA.continuous.comp continuous_fst).prodMk continuous_snd
  obtain ⟨O, hO, h0, g, hg, hev⟩ := exists_branch_localInv hU0 hU1 (φ p₀)
  have hr : ContMDiffOn (pullCarrier F hE hrange).model (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) ∞
      (fun y => (unwrapInv (g y).1, (g y).2)) O :=
    ((contMDiff_unwrapInv.comp contMDiff_fst).prodMk contMDiff_snd).comp_contMDiffOn hg
  obtain ⟨W, hW, hW0, G, hG, hGev⟩ := exists_sheet_localInv (fun p => assembled τu (φ p))
    ((contMDiff_assembled hU0 hU1).continuous.comp hφ).continuousAt hO h0 hr
  refine ⟨W, hW, hW0, G, hG, ?_⟩
  filter_upwards [hGev, (hφ.tendsto p₀).eventually hev] with p h1 h2
  change G (pullSndU (assembled τu (φ p)) : C.Carrier) = p
  rw [h1, h2]
  exact Prod.ext (unwrapInv_unwrapA p.1) rfl

end MobiusCover

theorem circleBundlesOverPlanarBases_mobius_localInv (C : CompactCarrier.{u})
    (U : TopologicalSpace.Opens C.Carrier) (F : CircleFibration C U) (M : MobiusBase.{u})
    (e : F.base.Carrier ≃ₘ⟮SurfaceModel.model F.base.kind,
      SurfaceModel.model M.surface.kind⟯ M.surface.Carrier) :
    ∃ Ψ : (Circle × unitInterval) × Circle → U, IsTwistedChart F (M.embedding ∘ e) Ψ ∧
      ∀ p₀, ∃ W : Set C.Carrier, IsOpen W ∧ (Ψ p₀ : C.Carrier) ∈ W ∧
        ∃ G : C.Carrier → (Circle × unitInterval) × Circle,
          ContMDiffOn C.model (((𝓡 1).prod (𝓡∂ 1)).prod (𝓡 1)) ∞ G W ∧
          ∀ᶠ p in 𝓝 p₀, G (Ψ p : C.Carrier) = p :=
  MobiusCover.exists_isTwistedChart_localInv (CircleFibration.relabelBase F M.surface e)
    M.isSmoothEmbedding M.range_embedding

end GC.Seifert
