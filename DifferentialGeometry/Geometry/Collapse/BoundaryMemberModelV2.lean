import DifferentialGeometry.Geometry.Collapse.BoundaryRegisterValidity
import DifferentialGeometry.Geometry.Collapse.LocalExport.ClosedMemberModel
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFinitePatch
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspVolumeTransfer

/-!
# The universe-`0` boundary model with both transport groups (lane FC39-BQ3, review 54 §7)

External review 54, §7 (dispositions row 7, work item 2): the boundary analogue of the closed
route's `ClosedModel` (`LocalExport/ClosedMemberModel.lean`) must carry the WHOLE carrier with
boundary (never the interior with a closed atlas) and two transport groups — analytic (curvature
scale, ball volumes, derivative control, distance to the boundary, original-metric balls, scale
function) through the EXACT pulled-back metric, and boundary (all component labels, cusp maps with
their torus metrics, height / level, actual collar subsets); the small models are chosen for the
WHOLE sequence first.

* Generic transport along any diffeomorphism `ψ : W₀ ≃ₘ W` of carriers:
  `mfderiv_apply_symm_comp_BQ3`, `localPullInner_pullbackMetricCross_symm_comp_BQ3`,
  `cuspMetricError_pullback_BQ3`, `CuspEmbedding.pullback_BQ3` (`ψ⁻¹ ∘ e`, same cusp, preimage
  component), `NearlyCuspidalBoundary.pullback_BQ3` (same count, same `K, δ`).
* Volume transport for carriers WITH boundary (the tree's `riemannianVolumeMeasure_pullback_cross`
  needs a boundaryless source model): `paramDensity_pullbackMetricCross_BQ3`,
  `riemannianVolumeMeasure_preimage_patch_BQ3` (area formula on interior chart patches),
  `map_riemannianVolumeMeasure_pullbackMetricCross_BQ3` (+ null boundaries).
* `BoundaryModelV2_BQ3 W g B` extends `BoundaryModel` (`BoundaryRegisterValidity.lean:144`) by
  `collar_toFun` (`ψ ∘ B₀.collar i = B.collar (cast i)`) and `collar_cusp` (same cusp).
* Analytic transport on every `BoundaryModel` (`edist_eq_BQ3`, `inner_eq_BQ3`,
  `ball_eq_preimage_BQ3`, `ballVolume_eq_BQ3`, `firstVolumeScale_eq_BQ3`, `curvatureRadius_eq_BQ3`,
  `curvatureDerivativeNorm_eq_BQ3`, `distanceToBoundary_eq_BQ3`,
  `volumeCollapsedAtCurvatureScale_iff_BQ3`, `boundaryVolumeCollapsed_iff_BQ3`,
  `curvatureDerivativesControlled_iff_BQ3`) and labels (`preimage_boundary_BQ3`,
  `component_eq_preimage_BQ3`, `image_sublevel_BQ3`); cusp data on the V2 model
  (`collar_apply_BQ3`, `collar_toFun_eq_BQ3`, `image_collar_image_BQ3`, `torusMetric_eq_BQ3`,
  `invFunOn_collar_eq_BQ3`).
* `nonempty_boundaryModelV2_BQ3`: existence on the whole carrier (`smallManifoldModel` for
  `W.model` itself). Consumers: `exists_boundaryModelsV2_standing_BQ3` (models of the whole
  sequence first, standing hypotheses transported) and `exists_boundaryModels_standing_BQ3` (the
  frozen target (h1) of the V2 targets file, verbatim).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Manifold Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Integral.Measure GC.Endpoint
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u v

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  {X : Type*} [TopologicalSpace X] [ChartedSpace H' X]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold I ∞ M] [T2Space M]
  [IsManifold J ∞ N] in
/-- The differential of `ψ ∘ (ψ⁻¹ ∘ f)` is that of `f`, at EVERY point (both sides vanish where `f`
is not differentiable). -/
theorem mfderiv_apply_symm_comp_BQ3 (ψ : M ≃ₘ⟮I, J⟯ N) (f : X → N) (x : X)
    (a : TangentSpace I' x) :
    mfderiv I J ψ ((ψ.symm ∘ f) x) (mfderiv I' I (ψ.symm ∘ f) x a) = mfderiv I' J f x a := by
  by_cases hd : MDifferentiableAt I' I (ψ.symm ∘ f) x
  · have hc := mfderiv_comp x (ψ.contMDiff.mdifferentiableAt (by simp)) hd
    have hfun : (ψ : M → N) ∘ (ψ.symm ∘ f) = f := by
      funext y
      simp
    rw [hfun] at hc
    rw [hc]
    rfl
  · have hf : ¬ MDifferentiableAt I' J f x := fun h =>
      hd ((ψ.symm.contMDiff.mdifferentiableAt (by simp)).comp x h)
    rw [mfderiv_zero_of_not_mdifferentiableAt hd, mfderiv_zero_of_not_mdifferentiableAt hf]
    simp only [zero_apply, map_zero]
    rfl

omit [FiniteDimensional ℝ F] in
/-- The local pull-back of the pulled-back metric along `ψ⁻¹ ∘ f` is that of `g` along `f`. -/
theorem localPullInner_pullbackMetricCross_symm_comp_BQ3 (g : SmoothRiemannianMetric J N)
    (ψ : M ≃ₘ⟮I, J⟯ N) (f : X → N) (x : X) :
    localPullInner (I := I') (J := I) (Diffeomorph.pullbackMetricCross g ψ) (ψ.symm ∘ f) x =
      localPullInner (I := I') (J := J) g f x := by
  ext a b
  rw [localPullInner_apply, localPullInner_apply, Diffeomorph.pullbackMetricCross_inner,
    mfderiv_apply_symm_comp_BQ3, mfderiv_apply_symm_comp_BQ3]
  have hx : ψ ((ψ.symm ∘ f) x) = f x := by simp
  rw [hx]

end Generic

section Volume

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H₀ : Type*} [TopologicalSpace H₀] {I₀ : ModelWithCorners ℝ E H₀}
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H₀ M₀] [IsManifold I₀ ∞ M₀] [T2Space M₀]
  [SigmaCompactSpace M₀]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [SigmaCompactSpace M]

private local instance measurableModelSpaceBQ3 : MeasurableSpace E := borel E
private local instance borelModelSpaceBQ3 : BorelSpace E := ⟨rfl⟩
private local instance measurableSourceBQ3 : MeasurableSpace M₀ := borel M₀
private local instance borelSourceBQ3 : BorelSpace M₀ := ⟨rfl⟩
private local instance measurableTargetBQ3 : MeasurableSpace M := borel M
private local instance borelTargetBQ3 : BorelSpace M := ⟨rfl⟩

omit [SigmaCompactSpace M₀] [T2Space M] [SigmaCompactSpace M] in
/-- The parametrized density of `ψ⁻¹ ∘ f` for the pulled-back metric is that of `f`. -/
theorem paramDensity_pullbackMetricCross_BQ3 (g : SmoothRiemannianMetric I M)
    (ψ : M₀ ≃ₘ⟮I₀, I⟯ M) (f : E → M) :
    paramDensity (I := I₀) (Diffeomorph.pullbackMetricCross g ψ) (ψ.symm ∘ f) =
      paramDensity (I := I) g f := by
  funext w
  have hG : paramGramMatrix (I := I₀) (Diffeomorph.pullbackMetricCross g ψ) (ψ.symm ∘ f) w =
      paramGramMatrix (I := I) g f w := by
    ext i j
    have h := congrArg (fun L : TangentSpace 𝓘(ℝ, E) w →L[ℝ] TangentSpace 𝓘(ℝ, E) w →L[ℝ] ℝ =>
      L (Tensor.Coordinates.chartModelBasis E i) (Tensor.Coordinates.chartModelBasis E j))
      (localPullInner_pullbackMetricCross_symm_comp_BQ3 (I' := 𝓘(ℝ, E)) g ψ f w)
    rw [paramGramMatrix_apply, paramGramMatrix_apply]
    exact h
  rw [paramDensity_apply, paramDensity_apply, hG]

/-- **Volume transport on an interior chart patch**: for a measurable set inside the interior part
of a chart domain, the volume of its preimage for the pulled-back metric is its volume. (Area
formula on both sides with the parametrization `(extChartAt I α)⁻¹` and `ψ⁻¹ ∘ (extChartAt I α)⁻¹`
over the interior of the chart target.) -/
theorem riemannianVolumeMeasure_preimage_patch_BQ3 (g : SmoothRiemannianMetric I M)
    (ψ : M₀ ≃ₘ⟮I₀, I⟯ M) (α : M) {B : Set M} (hB : MeasurableSet B)
    (hBs : B ⊆ (chartAt H α).source ∩ I.interior M) :
    riemannianVolumeMeasure I₀ M₀ (Diffeomorph.pullbackMetricCross g ψ) (ψ ⁻¹' B) =
      riemannianVolumeMeasure I M g B := by
  have hUo : IsOpen (interior (extChartAt I α).target) := isOpen_interior
  have hUt : interior (extChartAt I α).target ⊆ (extChartAt I α).target := interior_subset
  have hf : ContMDiffOn 𝓘(ℝ, E) I 1 (extChartAt I α).symm (interior (extChartAt I α).target) :=
    ((contMDiffOn_extChartAt_symm (n := ∞) α).mono hUt).of_le (by exact_mod_cast le_top)
  obtain ⟨K, hKdef⟩ : ∃ K : Set E, K = interior (extChartAt I α).target ∩
      (extChartAt I α).symm ⁻¹' B := ⟨_, rfl⟩
  have hK : MeasurableSet K := by
    rw [hKdef, ← Subtype.image_preimage_coe]
    exact hUo.measurableSet.subtype_image (hf.continuousOn.domRestrict.measurable hB)
  have hKU : K ⊆ interior (extChartAt I α).target := hKdef ▸ inter_subset_left
  have hinj : InjOn (extChartAt I α).symm K := (extChartAt I α).symm.injOn.mono (hKU.trans hUt)
  have himg : (extChartAt I α).symm '' K = B := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hKdef] at hz
      exact hz.2
    · intro hx
      obtain ⟨hxs, hxi⟩ := hBs hx
      have hxs' : x ∈ (extChartAt I α).source := by rwa [extChartAt_source]
      refine ⟨extChartAt I α x, ?_, (extChartAt I α).left_inv hxs'⟩
      rw [hKdef]
      refine ⟨(I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) (chart_mem_atlas H α)
        hxs).mp hxi, ?_⟩
      change (extChartAt I α).symm (extChartAt I α x) ∈ B
      rw [(extChartAt I α).left_inv hxs']
      exact hx
  have hf₀ : ContMDiffOn 𝓘(ℝ, E) I₀ 1 (ψ.symm ∘ (extChartAt I α).symm)
      (interior (extChartAt I α).target) :=
    (ψ.symm.contMDiff.of_le (by exact_mod_cast le_top)).comp_contMDiffOn hf
  have hinj₀ : InjOn (ψ.symm ∘ (extChartAt I α).symm) K := ψ.symm.injective.comp_injOn hinj
  have himg₀ : (ψ.symm ∘ (extChartAt I α).symm) '' K = ψ ⁻¹' B := by
    rw [image_comp, himg]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [mem_preimage, Diffeomorph.apply_symm_apply] using hy
    · intro hx
      exact ⟨ψ x, hx, ψ.symm_apply_apply x⟩
  have h1 := riemannianVolumeMeasure_image_eq g hUo hK hKU hf hinj
  have h2 := riemannianVolumeMeasure_image_eq (Diffeomorph.pullbackMetricCross g ψ) hUo hK hKU
    hf₀ hinj₀
  rw [himg] at h1
  rw [himg₀, paramDensity_pullbackMetricCross_BQ3] at h2
  rw [h1, h2]

end Volume

/-! ## The transported nearly cuspidal boundary -/

variable {W₀ : CompactCarrier.{v}} {W : CompactCarrier.{u}}

/-- The cusp error tensor of the transported cusp map for the pulled-back metric is that of the
original cusp map. -/
theorem cuspMetricError_pullback_BQ3 (g : SmoothRiemannianMetric W.model W.Carrier)
    (ψ : W₀.Carrier ≃ₘ⟮W₀.model, W.model⟯ W.Carrier) (Hc : HyperbolicCusp)
    (f : CuspHalfSpace → W.Carrier) :
    cuspMetricError (Diffeomorph.pullbackMetricCross g ψ) Hc (ψ.symm ∘ f) =
      cuspMetricError g Hc f := by
  funext p
  unfold cuspMetricError
  rw [localPullInner_pullbackMetricCross_symm_comp_BQ3]

/-- **The transported cusp embedding**: `ψ⁻¹ ∘ e` on the diffeomorphic carrier, the same cusp, for
the pulled-back metric, with the preimage of the boundary component. -/
def CuspEmbedding.pullback_BQ3 {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
    {X : Set W.Carrier} (ψ : W₀.Carrier ≃ₘ⟮W₀.model, W.model⟯ W.Carrier)
    (e : CuspEmbedding W g K δ X) :
    CuspEmbedding W₀ (Diffeomorph.pullbackMetricCross g ψ) K δ (ψ ⁻¹' X) where
  cusp := e.cusp
  toFun := ψ.symm ∘ e.toFun
  contMDiffOn := (ψ.symm.contMDiff.of_le (by exact_mod_cast le_top)).comp_contMDiffOn e.contMDiffOn
  isEmbedding := ψ.symm.toHomeomorph.isEmbedding.comp e.isEmbedding
  immersion p hp := by
    have hd : MDifferentiableAt halfCollarModel W.model e.toFun p :=
      ((e.contMDiffOn p hp).contMDiffAt (isOpen_cuspDomain.mem_nhds hp)).mdifferentiableAt
        (by simp)
    rw [mfderiv_comp p (ψ.symm.contMDiff.mdifferentiableAt (by simp)) hd]
    rw [ContinuousLinearMap.coe_comp]
    exact (ψ.symm.mfderivToContinuousLinearEquiv (by simp) (e.toFun p)).injective.comp
      (e.immersion p hp)
  boundary_image := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      change ψ (ψ.symm (e.toFun (t, halfZero))) ∈ X
      rw [Diffeomorph.apply_symm_apply]
      exact e.boundary_image.subset ⟨t, rfl⟩
    · intro hx
      obtain ⟨t, ht⟩ := e.boundary_image.symm.subset (show ψ x ∈ X from hx)
      exact ⟨t, by simp only [Function.comp_apply, ht, Diffeomorph.symm_apply_apply]⟩
  boundary_preimage {p} hp := by
    rw [← e.boundary_preimage hp, ← ψ.symm.preimage_boundary (by simp)]
    rfl
  metric_error := by
    unfold cuspMetricErrorBound
    rw [cuspMetricError_pullback_BQ3]
    exact e.metric_error

/-- **The transported nearly cuspidal boundary**: the same count, the preimages of the components,
the transported cusp embeddings, for the pulled-back metric, at the same `K, δ`. -/
def NearlyCuspidalBoundary.pullback_BQ3 {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
    {δ : ℝ} (ψ : W₀.Carrier ≃ₘ⟮W₀.model, W.model⟯ W.Carrier) (B : NearlyCuspidalBoundary W g K δ) :
    NearlyCuspidalBoundary W₀ (Diffeomorph.pullbackMetricCross g ψ) K δ where
  count := B.count
  count_pos := B.count_pos
  component i := ψ ⁻¹' B.component i
  connected i := ψ.toHomeomorph.isConnected_preimage.mpr (B.connected i)
  closed i := (B.closed i).preimage ψ.continuous
  disjoint i j hij := (B.disjoint hij).preimage ψ
  covers := by rw [← preimage_iUnion, B.covers, ψ.preimage_boundary (by simp)]
  diameter i x hx y hy := by
    rw [riemannianEDistOf_pullbackMetricCross]
    exact B.diameter i _ hx _ hy
  collar i := (B.collar i).pullback_BQ3 ψ

section CarrierVolume

private local instance measurableCarrierBQ3 : MeasurableSpace W.Carrier := borel W.Carrier
private local instance borelCarrierBQ3 : BorelSpace W.Carrier := ⟨rfl⟩
private local instance measurableSmallCarrierBQ3 : MeasurableSpace W₀.Carrier :=
  borel W₀.Carrier
private local instance borelSmallCarrierBQ3 : BorelSpace W₀.Carrier := ⟨rfl⟩

/-- **Volume transport on carriers WITH boundary**: the push-forward by `ψ` of the volume of the
pulled-back metric is the volume of the member (interior chart patches + null boundaries; the
tree's `riemannianVolumeMeasure_pullback_cross` needs a boundaryless source model). -/
theorem map_riemannianVolumeMeasure_pullbackMetricCross_BQ3
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (ψ : W₀.Carrier ≃ₘ⟮W₀.model, W.model⟯ W.Carrier) :
    Measure.map ψ (riemannianVolumeMeasure W₀.model W₀.Carrier
      (Diffeomorph.pullbackMetricCross g ψ)) = riemannianVolumeMeasure W.model W.Carrier g := by
  obtain ⟨S, hSc, hS⟩ : ∃ S : Set W.Carrier, S.Countable ∧
      ⋃ x ∈ S, (chartAt W.kind.Space x).source = univ :=
    countable_cover_nhds_of_sigmaCompact (fun x => chart_source_mem_nhds W.kind.Space x)
  have : Countable S := hSc.to_subtype
  refine Measure.ext_of_iUnion_eq_univ (s := fun o : Option S =>
    o.elim (W.model.boundary W.Carrier)
      (fun α => (chartAt W.kind.Space α.1).source ∩ W.model.interior W.Carrier)) ?_ ?_
  · refine eq_univ_of_forall fun x => ?_
    rcases W.model.isInteriorPoint_or_isBoundaryPoint x with hx | hx
    · have hxS : x ∈ ⋃ α ∈ S, (chartAt W.kind.Space α).source := hS ▸ mem_univ x
      obtain ⟨α, hα, hxα⟩ : ∃ α ∈ S, x ∈ (chartAt W.kind.Space α).source := by
        simpa only [mem_iUnion, exists_prop] using hxS
      exact mem_iUnion.mpr ⟨some ⟨α, hα⟩, hxα, hx⟩
    · exact mem_iUnion.mpr ⟨none, hx⟩
  · rintro (_ | α)
    · have hb : MeasurableSet (W.model.boundary W.Carrier) :=
        (W.model.isClosed_boundary (by simp : (∞ : WithTop ℕ∞) ≠ 0)).measurableSet
      change (Measure.map ψ _).restrict (W.model.boundary W.Carrier) =
        (riemannianVolumeMeasure W.model W.Carrier g).restrict (W.model.boundary W.Carrier)
      rw [Measure.restrict_eq_zero.mpr, Measure.restrict_eq_zero.mpr
        (CompactCarrier.riemannianVolumeMeasure_boundary_eq_zero W g)]
      rw [Measure.map_apply ψ.continuous.measurable hb, ψ.preimage_boundary (by simp)]
      exact CompactCarrier.riemannianVolumeMeasure_boundary_eq_zero W₀ _
    · ext B hB
      have hs : MeasurableSet ((chartAt W.kind.Space α.1).source ∩ W.model.interior W.Carrier) :=
        ((chartAt W.kind.Space α.1).open_source.inter
          (W.model.isOpen_interior (by simp : (∞ : WithTop ℕ∞) ≠ 0))).measurableSet
      change (Measure.map ψ _).restrict ((chartAt W.kind.Space α.1).source ∩
          W.model.interior W.Carrier) B =
        (riemannianVolumeMeasure W.model W.Carrier g).restrict
          ((chartAt W.kind.Space α.1).source ∩ W.model.interior W.Carrier) B
      rw [Measure.restrict_apply hB, Measure.restrict_apply hB,
        Measure.map_apply ψ.continuous.measurable (hB.inter hs)]
      exact riemannianVolumeMeasure_preimage_patch_BQ3 g ψ α.1 (hB.inter hs) inter_subset_right

end CarrierVolume

/-! ## The model with both transport groups -/

/-- **The universe-`0` boundary model with both transport groups** (external review 54 §7): a
`BoundaryModel` (carrier, diffeomorphism `ψ`, EXACT pulled-back metric, transported boundary with
`count_eq`, `component_eq`) whose cusp maps are those of the member through `ψ`, with the same
hyperbolic cusps (same torus metrics). -/
structure BoundaryModelV2_BQ3 (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) extends BoundaryModel W g B where
  /-- The cusp maps of the model are those of the member, through `ψ`. -/
  collar_toFun : ∀ i, (ψ : W₀.Carrier → W.Carrier) ∘ (B₀.collar i).toFun =
    (B.collar (Fin.cast count_eq i)).toFun
  /-- The same hyperbolic cusps. -/
  collar_cusp : ∀ i, (B₀.collar i).cusp = (B.collar (Fin.cast count_eq i)).cusp

namespace BoundaryModel

variable {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {B : NearlyCuspidalBoundary W g K δ} (M : BoundaryModel W g B)

private local instance measurableMemberBQ3 : MeasurableSpace W.Carrier := borel W.Carrier
private local instance borelMemberBQ3 : BorelSpace W.Carrier := ⟨rfl⟩
private local instance measurableModelBQ3 : MeasurableSpace M.W₀.Carrier := borel M.W₀.Carrier
private local instance borelModelBQ3 : BorelSpace M.W₀.Carrier := ⟨rfl⟩

/-! ### Analytic transport (through the exact pulled-back metric) -/

/-- Riemannian distances of the model are those of the member. -/
theorem edist_eq_BQ3 (a b : M.W₀.Carrier) :
    riemannianEDistOf M.g₀ a b = riemannianEDistOf g (M.ψ a) (M.ψ b) := by
  rw [M.metric_eq]
  exact riemannianEDistOf_pullbackMetricCross g M.ψ a b

/-- Inner products of the model are those of the member through `dψ`. -/
theorem inner_eq_BQ3 (x : M.W₀.Carrier) (a b : TangentSpace M.W₀.model x) :
    M.g₀.inner x a b =
      g.inner (M.ψ x) (mfderiv M.W₀.model W.model M.ψ x a)
        (mfderiv M.W₀.model W.model M.ψ x b) := by
  rw [M.metric_eq]
  exact Diffeomorph.pullbackMetricCross_inner g M.ψ x a b

/-- Riemannian balls of the model are the preimages of the member's balls (original metric). -/
theorem ball_eq_preimage_BQ3 (p : M.W₀.Carrier) (r : ℝ) :
    riemannianBallOf M.g₀ p r = M.ψ ⁻¹' riemannianBallOf g (M.ψ p) r := by
  ext x
  change riemannianEDistOf M.g₀ p x < ENNReal.ofReal r ↔
    riemannianEDistOf g (M.ψ p) (M.ψ x) < ENNReal.ofReal r
  rw [M.edist_eq_BQ3]

/-- Ball volumes of the model are those of the member. -/
theorem ballVolume_eq_BQ3 (p : M.W₀.Carrier) (r : ℝ) :
    ballVolume M.g₀ p r = ballVolume g (M.ψ p) r := by
  have hmeas : MeasurableSet (riemannianBallOf g (M.ψ p) r) :=
    (isOpen_lt (Riemannian.continuous_riemannianEDist g (M.ψ p)) continuous_const).measurableSet
  rw [ballVolume, ballVolume, M.ball_eq_preimage_BQ3, M.metric_eq,
    ← Measure.map_apply M.ψ.continuous.measurable hmeas,
    map_riemannianVolumeMeasure_pullbackMetricCross_BQ3]

/-- First volume scales of the model are those of the member. -/
theorem firstVolumeScale_eq_BQ3 (p : M.W₀.Carrier) (w : ℝ) :
    firstVolumeScale M.g₀ p w = firstVolumeScale g (M.ψ p) w := by
  unfold firstVolumeScale
  simp only [M.ballVolume_eq_BQ3]

/-- Curvature scales of the model are those of the member. -/
theorem curvatureRadius_eq_BQ3 (p : M.W₀.Carrier) :
    curvatureRadius M.g₀ p = curvatureRadius g (M.ψ p) := by
  have hback : Diffeomorph.pullbackMetricCross M.g₀ M.ψ.symm = g := by
    rw [M.metric_eq, Diffeomorph.pullbackMetricCross_trans, Diffeomorph.symm_trans_self,
      Diffeomorph.pullbackMetricCross_refl]
  apply le_antisymm
  · refine iSup_le fun r => iSup_le fun hr => iSup_le fun hb => ?_
    apply le_iSup_of_le r
    apply le_iSup_of_le hr
    have hbd : ∀ y ∈ riemannianBallOf g (M.ψ p) r,
        SectionalBoundedBelowAt g y (-(r ^ 2)⁻¹) := by
      intro y hy
      have hyS : M.ψ.symm y ∈ riemannianBallOf M.g₀ p r := by
        rw [M.ball_eq_preimage_BQ3]
        simpa only [mem_preimage, Diffeomorph.apply_symm_apply] using hy
      have hbS := hb (M.ψ.symm y) hyS
      simpa only [hback, Diffeomorph.apply_symm_apply] using
        sectionalBoundedBelowAt_pullbackMetricCross M.g₀ M.ψ.symm y hbS
    exact le_iSup_of_le hbd le_rfl
  · refine iSup_le fun r => iSup_le fun hr => iSup_le fun hb => ?_
    apply le_iSup_of_le r
    apply le_iSup_of_le hr
    have hbd : ∀ y ∈ riemannianBallOf M.g₀ p r,
        SectionalBoundedBelowAt M.g₀ y (-(r ^ 2)⁻¹) := by
      intro y hy
      rw [M.metric_eq]
      apply sectionalBoundedBelowAt_pullbackMetricCross g M.ψ y
      exact hb (M.ψ y) ((M.ball_eq_preimage_BQ3 p r).le hy)
    exact le_iSup_of_le hbd le_rfl

/-- Curvature derivative norms of the model are those of the member. -/
theorem curvatureDerivativeNorm_eq_BQ3 (k : ℕ) (p : M.W₀.Carrier) :
    curvatureDerivativeNorm M.g₀ k p = curvatureDerivativeNorm g k (M.ψ p) :=
  curvatureDerivativeNorm_of_injective_local_isometry M.g₀ g M.ψ M.ψ.isLocalDiffeomorph
    M.ψ.injective M.inner_eq_BQ3 k p

/-- The boundary of the model is the preimage of the member's boundary. -/
theorem preimage_boundary_BQ3 :
    M.ψ ⁻¹' W.model.boundary W.Carrier = M.W₀.model.boundary M.W₀.Carrier :=
  M.ψ.preimage_boundary (by simp)

/-- Distances to the boundary of the model are those of the member. -/
theorem distanceToBoundary_eq_BQ3 (p : M.W₀.Carrier) :
    distanceToBoundary M.W₀ M.g₀ p = distanceToBoundary W g (M.ψ p) := by
  let e : M.W₀.model.boundary M.W₀.Carrier ≃ W.model.boundary W.Carrier :=
    M.ψ.toEquiv.subtypeEquiv fun x => by
      rw [← M.preimage_boundary_BQ3]
      rfl
  unfold distanceToBoundary
  rw [← e.iInf_comp]
  exact iInf_congr fun q => M.edist_eq_BQ3 p q

variable {M} in
/-- Volume collapse at the curvature scale transports. -/
theorem volumeCollapsedAtCurvatureScale_iff_BQ3 {w : ℝ} {p : M.W₀.Carrier} :
    volumeCollapsedAtCurvatureScale M.g₀ w p ↔ volumeCollapsedAtCurvatureScale g w (M.ψ p) := by
  simp only [volumeCollapsedAtCurvatureScale, M.curvatureRadius_eq_BQ3, M.ballVolume_eq_BQ3]

variable {M} in
/-- **The standing collapse hypothesis transports** (both directions). -/
theorem boundaryVolumeCollapsed_iff_BQ3 {w : ℝ} :
    boundaryVolumeCollapsed M.W₀ M.g₀ w ↔ boundaryVolumeCollapsed W g w := by
  unfold boundaryVolumeCollapsed
  rw [M.ψ.surjective.forall]
  simp only [Diffeomorph.coe_toEquiv, M.distanceToBoundary_eq_BQ3,
    volumeCollapsedAtCurvatureScale_iff_BQ3]

variable {M} in
/-- **The standing derivative control transports** (both directions). -/
theorem curvatureDerivativesControlled_iff_BQ3 {k₀ : ℕ} {A : ℝ → ℝ} {w₀ : ℝ} :
    curvatureDerivativesControlled M.g₀ k₀ A w₀ ↔ curvatureDerivativesControlled g k₀ A w₀ := by
  unfold curvatureDerivativesControlled
  rw [M.ψ.surjective.forall]
  refine forall_congr' fun p => ?_
  simp only [Diffeomorph.coe_toEquiv, M.curvatureRadius_eq_BQ3, M.ballVolume_eq_BQ3,
    M.ball_eq_preimage_BQ3, mem_preimage, M.curvatureDerivativeNorm_eq_BQ3]
  constructor
  · intro h w r hw hw' hr hrad hvol k hk q hq
    simpa only [Diffeomorph.apply_symm_apply] using
      h w r hw hw' hr hrad hvol k hk (M.ψ.symm q) (by simpa only [Diffeomorph.apply_symm_apply])
  · intro h w r hw hw' hr hrad hvol k hk q hq
    exact h w r hw hw' hr hrad hvol k hk (M.ψ q) hq

/-! ### Boundary and label transport available on every model -/

/-- The components of the model are the preimages of the member's components (same labels through
`Fin.cast count_eq`). -/
theorem component_eq_preimage_BQ3 (i : Fin M.B₀.count) :
    M.B₀.component i = M.ψ ⁻¹' B.component (Fin.cast M.count_eq i) := by
  rw [← M.component_eq i]
  exact (preimage_image_eq _ M.ψ.injective).symm

/-- Level sets of a function on the model, seen in the member. -/
theorem image_sublevel_BQ3 (F : M.W₀.Carrier → ℝ) (c : ℝ) :
    M.ψ '' {x | F x ≤ c} = {y | F (M.ψ.symm y) ≤ c} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [mem_ofPred_eq, Diffeomorph.symm_apply_apply] using hx
  · intro hy
    exact ⟨M.ψ.symm y, hy, M.ψ.apply_symm_apply y⟩

end BoundaryModel

namespace BoundaryModelV2_BQ3

variable {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {B : NearlyCuspidalBoundary W g K δ} (M : BoundaryModelV2_BQ3 W g B)

/-! ### Boundary transport of the cusp data -/

/-- The cusp maps of the model are those of the member through `ψ`, pointwise. -/
theorem collar_apply_BQ3 (i : Fin M.B₀.count) (q : CuspHalfSpace) :
    M.ψ ((M.B₀.collar i).toFun q) = (B.collar (Fin.cast M.count_eq i)).toFun q :=
  congrFun (M.collar_toFun i) q

/-- The cusp maps of the model are `ψ⁻¹ ∘` those of the member. -/
theorem collar_toFun_eq_BQ3 (i : Fin M.B₀.count) :
    (M.B₀.collar i).toFun = M.ψ.symm ∘ (B.collar (Fin.cast M.count_eq i)).toFun := by
  funext q
  rw [Function.comp_apply, ← M.collar_apply_BQ3 i q, Diffeomorph.symm_apply_apply]

/-- Actual collar subsets correspond: `ψ` maps the model's collar image of any set of cusp points
onto the member's collar image of the same set (e.g. the depth-`92` collars). -/
theorem image_collar_image_BQ3 (i : Fin M.B₀.count) (S : Set CuspHalfSpace) :
    M.ψ '' ((M.B₀.collar i).toFun '' S) = (B.collar (Fin.cast M.count_eq i)).toFun '' S := by
  rw [← image_comp, M.collar_toFun i]

/-- The torus metrics of the cusps are the member's. -/
theorem torusMetric_eq_BQ3 (i : Fin M.B₀.count) :
    (M.B₀.collar i).cusp.torusMetric = (B.collar (Fin.cast M.count_eq i)).cusp.torusMetric := by
  rw [M.collar_cusp i]

/-- The collar coordinates (hence the collar height `z`) of a model point are those of its image:
`invFunOn` of the model's cusp map at `x` is `invFunOn` of the member's at `ψ x`. -/
theorem invFunOn_collar_eq_BQ3 (i : Fin M.B₀.count) (x : M.W₀.Carrier) :
    Function.invFunOn (M.B₀.collar i).toFun cuspDomain x =
      Function.invFunOn (B.collar (Fin.cast M.count_eq i)).toFun cuspDomain (M.ψ x) := by
  have hpred : (fun a => a ∈ cuspDomain ∧ (M.B₀.collar i).toFun a = x) =
      (fun a => a ∈ cuspDomain ∧ (B.collar (Fin.cast M.count_eq i)).toFun a = M.ψ x) := by
    funext a
    rw [← M.collar_apply_BQ3 i a]
    exact propext (and_congr_right' ⟨fun h => by rw [h], fun h => M.ψ.injective h⟩)
  have key : ∀ (P Q : CuspHalfSpace → Prop), P = Q → ∀ (hP : ∃ a, P a) (hQ : ∃ a, Q a),
      Classical.choose hP = Classical.choose hQ := by
    intro P Q hPQ hP hQ
    subst hPQ
    rfl
  have hiff : (∃ a, a ∈ cuspDomain ∧ (M.B₀.collar i).toFun a = x) ↔
      ∃ a, a ∈ cuspDomain ∧ (B.collar (Fin.cast M.count_eq i)).toFun a = M.ψ x := by
    rw [hpred]
  unfold Function.invFunOn
  by_cases hc : ∃ a, a ∈ cuspDomain ∧ (M.B₀.collar i).toFun a = x
  · rw [dite_eq_left hc, dite_eq_left (hiff.mp hc)]
    exact key _ _ hpred hc (hiff.mp hc)
  · rw [dite_eq_right hc, dite_eq_right (mt hiff.mpr hc)]

end BoundaryModelV2_BQ3

/-! ## Existence on the whole carrier with boundary, and the standing transport for sequences -/

/-- **Existence of the universe-`0` boundary model with both transport groups**, on the WHOLE
carrier with boundary (X122's `smallManifoldModel` for the member's own model `W.model`, no
interior atlas): the small carrier with the pulled-back charts, the transported orientation, the
EXACT pulled-back metric and the transported nearly cuspidal boundary (`pullback_BQ3`). -/
theorem nonempty_boundaryModelV2_BQ3 (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    (g : SmoothRiemannianMetric W.model W.Carrier) {K : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) : Nonempty (BoundaryModelV2_BQ3 W g B) := by
  let S : SmallManifoldModel (I := W.model) W.Carrier := smallManifoldModel
  have kS : CompactSpace S.Carrier := S.diffeo.toHomeomorph.symm.compactSpace
  obtain ⟨o₀, -⟩ := S.exists_orientation W.orientation
  let W₀ : CompactCarrier.{0} := { kind := W.kind, Carrier := S.Carrier, orientation := o₀ }
  let ψ : W₀.Carrier ≃ₘ⟮W₀.model, W.model⟯ W.Carrier := S.diffeo
  have cS : ConnectedSpace W₀.Carrier := (ψ.toHomeomorph.connectedSpace_iff).mpr inferInstance
  exact ⟨{
    W₀ := W₀
    connected₀ := cS
    ψ := ψ
    g₀ := Diffeomorph.pullbackMetricCross g ψ
    metric_eq := rfl
    B₀ := B.pullback_BQ3 ψ
    count_eq := rfl
    component_eq := fun i => image_preimage_eq _ ψ.surjective
    collar_toFun := fun i => by
      funext q
      exact ψ.apply_symm_apply _
    collar_cusp := fun i => rfl }⟩

/-- **(h1), models for the WHOLE sequence first** (review 54 §7): universe-`0` boundary models of
every member of a boundary standing sequence, chosen at once, with the standing hypotheses
transported to the model sequence. -/
theorem exists_boundaryModelsV2_standing_BQ3 (K : ℕ) (A : ℝ → ℝ) (δStar : ℝ)
    (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
    (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
    (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1)))
    (hs : ∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δStar (n + 1)) ∧
      curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δStar (n + 1))) :
    ∃ M : ∀ n, BoundaryModelV2_BQ3 (W n) (g n) (B n),
      ∀ n, boundaryVolumeCollapsed (M n).W₀ (M n).g₀
          (boundaryCounterexampleRatio δStar (n + 1)) ∧
        curvatureDerivativesControlled (M n).g₀ K A (boundaryCounterexampleRatio δStar (n + 1)) :=
  ⟨fun n => (nonempty_boundaryModelV2_BQ3 (W n) (g n) (B n)).some, fun n =>
    ⟨BoundaryModel.boundaryVolumeCollapsed_iff_BQ3.mpr (hs n).1,
      BoundaryModel.curvatureDerivativesControlled_iff_BQ3.mpr (hs n).2⟩⟩

/-- **(h1), exactly the frozen target** `target_exists_boundaryModels_standing_BQ3` of the V2
targets file (V1 models: the projections of the V2 models). -/
theorem exists_boundaryModels_standing_BQ3 (K : ℕ) (A : ℝ → ℝ) (δStar : ℝ)
    (W : ℕ → CompactCarrier.{u}) [∀ n, ConnectedSpace (W n).Carrier]
    (g : ∀ n, SmoothRiemannianMetric (W n).model (W n).Carrier)
    (B : ∀ n, NearlyCuspidalBoundary (W n) (g n) K (boundaryCounterexampleRatio δStar (n + 1)))
    (hs : ∀ n, boundaryVolumeCollapsed (W n) (g n) (boundaryCounterexampleRatio δStar (n + 1)) ∧
      curvatureDerivativesControlled (g n) K A (boundaryCounterexampleRatio δStar (n + 1))) :
    ∃ M : ∀ n, BoundaryModel (W n) (g n) (B n),
      ∀ n, boundaryVolumeCollapsed (M n).W₀ (M n).g₀
          (boundaryCounterexampleRatio δStar (n + 1)) ∧
        curvatureDerivativesControlled (M n).g₀ K A
          (boundaryCounterexampleRatio δStar (n + 1)) := by
  obtain ⟨M, hM⟩ := exists_boundaryModelsV2_standing_BQ3 K A δStar W g B hs
  exact ⟨fun n => (M n).toBoundaryModel, hM⟩

end DifferentialGeometry.Geometry.Collapse
