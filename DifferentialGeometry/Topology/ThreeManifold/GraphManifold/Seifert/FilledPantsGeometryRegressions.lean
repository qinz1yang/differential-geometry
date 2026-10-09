import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryMap
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BlockGeometryEuclideanUnfilled

/-!
# Regression of the chart fold: the unfilled pants block

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §5,
first regression, with the errata after review 21). The fold engine `GeometricStructure.ofFold`
is run through the product chart of arbitrary charts `C` of a block with `d.k = 3` and no filling,
on `N = ⊤ ⊆ ModelCoordinates`, with `G = coreFoldMap F` for K16f's core fold `F` (the hypotheses of
`pantsQuotientDiffeo_of_core`). The fold `C.foldThroughProduct ⊤ G _` is a local diffeomorphism
(`isLocalDiffeomorph_foldThroughProduct`), its same-image pairs are related by the pants group and
the fibre translations (`metricFiberCompatible_foldThroughProduct`), and it is onto because the
product chart covers the interior. Completeness does not use an exhaustion function (review 21
§7.4: three cusps would need three terms): the fold factors through `PantsQuotient` by a bijective
local diffeomorphism `Φ`, so the fold metric is the pullback of `pantsQuotientGeometry.metric`
along `Φ⁻¹` (uniqueness of descended metrics) and is complete. The result
`unfilledCoreInteriorGeometryOfCharts` has model `.hyperbolicProduct` by `rfl`, as does route Q's
`unfilledPantsBlockGeometry`; `SeifertBlock.exists_unfilledCoreInteriorGeometry` runs it with
K16f's fold `exists_foldCore` on `B.unfilledCharts`. The hypothesis `hk : d.k = 3` is never
substituted: only membership in `planarOpen d.k` is transported.
-/

set_option autoImplicit false

noncomputable section
open Set UpperHalfPlane
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Manifold ContDiff Topology ComplexConjugate

universe u

namespace GC.Seifert

theorem planarOpen_three_iff (u : ℂ) : u ∈ planarOpen 3 ↔ planarFunction 3 u < 0 := by
  constructor
  · intro hu
    have h1 := chartPlanarInterior_hole_lt hu (1 : Fin 3) (by decide)
    have h2 := chartPlanarInterior_hole_lt hu (2 : Fin 3) (by decide)
    have e1 : u - ((planarCenter 3 (1 : Fin 3) : ℝ) : ℂ) = u - 3 / 2 := by
      simp only [planarCenter]
      norm_num
    have e2 : u - ((planarCenter 3 (2 : Fin 3) : ℝ) : ℂ) = u + 3 / 2 := by
      simp only [planarCenter]
      norm_num
    rw [e1] at h1
    rw [e2] at h2
    exact (planarFunction_three_neg_iff u).2 ⟨chartPlanarInterior_lt hu, h1, h2⟩
  · intro hu
    have ho : IsOpen {w : ℂ | planarFunction 3 w < 0} :=
      isOpen_lt (contDiff_planarFunction 3).continuous continuous_const
    have hs : {w : ℂ | planarFunction 3 w < 0} ⊆ planarModel 3 := fun w hw =>
      (planarFunction_nonpos_iff (Or.inr rfl) w).1 (le_of_lt hw)
    exact interior_maximal hs ho hu

variable {W : CompactCarrier.{u}} {d : SeifertData}

theorem planarFunction_neg_of_mem_planarOpen (hk : d.k = 3) {u : ℂ} (hu : u ∈ planarOpen d.k) :
    planarFunction 3 u < 0 := by
  rw [hk] at hu
  exact (planarOpen_three_iff u).1 hu

theorem mem_planarOpen_of_planarFunction_neg (hk : d.k = 3) {u : ℂ}
    (hu : planarFunction 3 u < 0) : u ∈ planarOpen d.k := by
  rw [hk]
  exact (planarOpen_three_iff u).2 hu

namespace SeifertBlockCharts

theorem throughProduct_eq_chartProductMap (C : SeifertBlockCharts W d) {X : Type*}
    (G : X → ℂ × Circle) (hG : ∀ x, (G x).1 ∈ planarOpen d.k) {x : X}
    {y : planarOpen d.k × Circle} (h : G x = ((y.1 : ℂ), y.2)) :
    C.throughProduct G hG x = C.chartProductMap y := by
  have h1 : (⟨(G x).1, hG x⟩ : planarOpen d.k) = y.1 := Subtype.ext (congrArg Prod.fst h)
  unfold throughProduct
  rw [h1, show (G x).2 = y.2 from congrArg Prod.snd h]

theorem exists_mem_productRegion (C : SeifertBlockCharts W d) (h0 : d.fillingCount = 0)
    (x : W.pieceInterior ⊤) : (x : W.Carrier) ∈ C.productRegion := by
  rcases C.covers x x.2.2 with hx | ⟨m, -⟩
  · exact hx
  · have := m.2
    omega

end SeifertBlockCharts

section Core

variable {F : ℂ → ℂ}

theorem coreFoldMap_mem_planarOpen (hk : d.k = 3)
    (hreal : ∀ i : Fin 3, ∀ z ∈ wall i, conj (F z) = F z)
    (hbij : Set.BijOn (fun z : ℍ => F z) idealTriangle
      {u : ℂ | planarFunction 3 u < 0 ∧ 0 ≤ u.im}) (p : ModelCoordinates) :
    (coreFoldMap F p).1 ∈ planarOpen d.k := by
  have h : coreFold F (logPoint p) ∈ Set.range (coreFold F) := ⟨_, rfl⟩
  rw [range_coreFold hreal hbij] at h
  exact mem_planarOpen_of_planarFunction_neg hk h

theorem coreQuotientMap_mem_planarOpen (hk : d.k = 3)
    (hreal : ∀ i : Fin 3, ∀ z ∈ wall i, conj (F z) = F z)
    (hbij : Set.BijOn (fun z : ℍ => F z) idealTriangle
      {u : ℂ | planarFunction 3 u < 0 ∧ 0 ≤ u.im}) (q : PantsQuotient) :
    (coreQuotientMap hreal q).1 ∈ planarOpen d.k := by
  obtain ⟨p, rfl⟩ := Quotient.mk''_surjective q
  exact coreFoldMap_mem_planarOpen hk hreal hbij p

theorem exists_coreQuotientMap_eq (hk : d.k = 3)
    (hreal : ∀ i : Fin 3, ∀ z ∈ wall i, conj (F z) = F z)
    (hbij : Set.BijOn (fun z : ℍ => F z) idealTriangle
      {u : ℂ | planarFunction 3 u < 0 ∧ 0 ≤ u.im}) (y : planarOpen d.k × Circle) :
    ∃ q : PantsQuotient, coreQuotientMap hreal q = ((y.1 : ℂ), y.2) := by
  have hy : ((y.1 : ℂ), y.2) ∈ (pantsImage : Set (ℂ × Circle)) :=
    planarFunction_neg_of_mem_planarOpen hk y.1.2
  rw [← range_coreQuotientMap hreal hbij] at hy
  exact hy

end Core

section Regression

variable (C : SeifertBlockCharts W d) (h0 : d.fillingCount = 0) (hk : d.k = 3)
  {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
  (hΔU : ∀ z : ℍ, z ∈ idealTriangle → (z : ℂ) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
  (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
    ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z))
  (hdet : ∀ z : ℍ, z ∈ idealTriangle → (fderiv ℝ F z).det ≠ 0)
  (hbij : Set.BijOn (fun z : ℍ => F z) idealTriangle
    {u : ℂ | planarFunction 3 u < 0 ∧ 0 ≤ u.im})

def coreChartFold : (⊤ : TopologicalSpace.Opens ModelCoordinates) → W.pieceInterior ⊤ :=
  C.foldThroughProduct ⊤ (coreFoldMap F)
    (fun p _ => coreFoldMap_mem_planarOpen hk (core_conj_of_mem_wall hwall) hbij p)

def coreChartQuotientMap : PantsQuotient → W.pieceInterior ⊤ :=
  C.throughProduct (coreQuotientMap (core_conj_of_mem_wall hwall))
    (coreQuotientMap_mem_planarOpen hk (core_conj_of_mem_wall hwall) hbij)

theorem coreChartFold_eq (p : (⊤ : TopologicalSpace.Opens ModelCoordinates)) :
    coreChartFold C hk hwall hbij p =
      coreChartQuotientMap C hk hwall hbij (Quotient.mk'' (p : ModelCoordinates)) :=
  rfl

include hU hΔU hF hdet in
theorem injective_coreChartQuotientMap :
    Function.Injective (coreChartQuotientMap C hk hwall hbij) := by
  have hreal := core_conj_of_mem_wall hwall
  have him : ∀ z : ℍ, z ∈ idealTriangle → 0 ≤ (F z).im := fun z hz => (hbij.mapsTo hz).2
  have hwim : ∀ z : ℍ, z ∈ idealTriangle → (F z).im = 0 → ∃ i, z ∈ wall i := fun z hz h =>
    core_exists_mem_wall_of_im_eq_zero hU hΔU hF hdet him hz h
  intro q q' h
  exact injective_coreQuotientMap hreal hbij.injOn him hwim
    ((C.throughProduct_eq_iff _ _).1 h)

include h0 in
theorem surjective_coreChartQuotientMap :
    Function.Surjective (coreChartQuotientMap C hk hwall hbij) := by
  intro x
  obtain ⟨y, rfl⟩ := C.exists_chartProductMap_eq (C.exists_mem_productRegion h0 x)
  obtain ⟨q, hq⟩ := exists_coreQuotientMap_eq hk (core_conj_of_mem_wall hwall) hbij y
  exact ⟨q, C.throughProduct_eq_chartProductMap _ _ hq⟩

include h0 in
theorem surjective_coreChartFold : Function.Surjective (coreChartFold C hk hwall hbij) := by
  intro x
  obtain ⟨q, rfl⟩ := surjective_coreChartQuotientMap C h0 hk hwall hbij x
  obtain ⟨p, rfl⟩ := Quotient.mk''_surjective q
  exact ⟨⟨p, trivial⟩, rfl⟩

include hU hΔU hF hdet in
theorem isLocalDiffeomorph_coreChartQuotientMap :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (coreChartQuotientMap C hk hwall hbij) := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  exact C.isLocalDiffeomorph_throughProduct _ _
    (isLocalDiffeomorph_coreQuotientMap hU hΔU hF hwall hdet)

include hU hΔU hF hdet in
theorem isLocalDiffeomorph_coreChartFold :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (coreChartFold C hk hwall hbij) := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  have h := isLocalDiffeomorph_comp
    (isLocalDiffeomorph_comp (isLocalDiffeomorph_coreChartQuotientMap C hk hU hΔU hF hwall hdet
      hbij) (isLocalDiffeomorph_orbitMk (𝓡 3) (pantsGroup × Multiplicative ℤ) ModelCoordinates))
    (isLocalDiffeomorph_subtype_val (⊤ : TopologicalSpace.Opens ModelCoordinates))
  exact h

include hU hΔU hF hwall hdet hbij in
theorem coreChartFold_pair (y y' : (⊤ : TopologicalSpace.Opens ModelCoordinates))
    (h : coreFoldMap F y = coreFoldMap F y') :
    ∃ γ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates,
      Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) γ =
        coordinateModelMetric .hyperbolicProduct ∧ γ (y : ModelCoordinates) = y' ∧
        ∃ V : TopologicalSpace.Opens ModelCoordinates, (y : ModelCoordinates) ∈ V ∧
          (V : Set ModelCoordinates) ⊆ (⊤ : TopologicalSpace.Opens ModelCoordinates) ∧
          Set.MapsTo γ (V : Set ModelCoordinates) (⊤ : TopologicalSpace.Opens ModelCoordinates) ∧
          ∀ z ∈ V, coreFoldMap F (γ z) = coreFoldMap F z := by
  have hreal := core_conj_of_mem_wall hwall
  have him : ∀ z : ℍ, z ∈ idealTriangle → 0 ≤ (F z).im := fun z hz => (hbij.mapsTo hz).2
  have hwim : ∀ z : ℍ, z ∈ idealTriangle → (F z).im = 0 → ∃ i, z ∈ wall i := fun z hz h =>
    core_exists_mem_wall_of_im_eq_zero hU hΔU hF hdet him hz h
  have hq : (Quotient.mk'' (y : ModelCoordinates) : PantsQuotient) =
      Quotient.mk'' (y' : ModelCoordinates) :=
    injective_coreQuotientMap hreal hbij.injOn him hwim h
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 (Quotient.eq''.1 hq))
  refine ⟨MulAction.smulDiffeomorph (n := ∞) (𝓡 3) γ⁻¹, pullbackMetric_pants_smul γ⁻¹, ?_, ⊤,
    trivial, fun _ _ => trivial, fun _ _ => trivial, fun z _ => coreFoldMap_smul hreal γ⁻¹ z⟩
  change γ⁻¹ • (y : ModelCoordinates) = y'
  rw [inv_smul_eq_iff, hγ]

theorem localPullMetric_congr_fun {E E' H H' M M' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [TopologicalSpace M']
    [ChartedSpace H' M'] [IsManifold J ∞ M'] (g : SmoothRiemannianMetric J M') {f f' : M → M'}
    (hf : IsLocalDiffeomorph I J ∞ f) (hf' : IsLocalDiffeomorph I J ∞ f') (h : f = f') :
    localPullMetric g f hf = localPullMetric g f' hf' := by
  subst h
  rfl

def unfilledCoreInteriorGeometryOfCharts : W.InteriorGeometry ⊤ := by
  letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
  have hFl := isLocalDiffeomorph_coreChartFold C hk hU hΔU hF hwall hdet hbij
  have hsurj := surjective_coreChartFold C h0 hk hwall hbij
  have hcompat := C.metricFiberCompatible_foldThroughProduct
    (coordinateModelMetric .hyperbolicProduct) ⊤ (coreFoldMap F) _ hFl
    (coreChartFold_pair hU hΔU hF hwall hdet hbij)
  have hQ := isLocalDiffeomorph_coreChartQuotientMap C hk hU hΔU hF hwall hdet hbij
  let Φ := hQ.diffeomorphOfBijective
    ⟨injective_coreChartQuotientMap C hk hU hΔU hF hwall hdet hbij,
      surjective_coreChartQuotientMap C h0 hk hwall hbij⟩
  have hmetric : foldMetric ((coordinateModelMetric .hyperbolicProduct).restrictOpen ⊤)
      (coreChartFold C hk hwall hbij) hFl hsurj hcompat =
        Diffeomorph.pullbackMetricCross pantsQuotientGeometry.metric Φ.symm := by
    apply localPullMetric_injective_of_surjective _ hFl hsurj
    refine (foldMetric_pullback _ _ hFl hsurj hcompat).trans ?_
    symm
    rw [Diffeomorph.pullbackMetricCross_eq_localPullMetric,
      localPullMetric_comp _ _ _ _ _ (isLocalDiffeomorph_comp Φ.symm.isLocalDiffeomorph hFl)]
    have hmk := isLocalDiffeomorph_orbitMk (𝓡 3) (pantsGroup × Multiplicative ℤ) ModelCoordinates
    have hval := isLocalDiffeomorph_subtype_val (I := 𝓡 3)
      (⊤ : TopologicalSpace.Opens ModelCoordinates)
    rw [localPullMetric_congr_fun _ _ (isLocalDiffeomorph_comp hmk hval) (funext fun p => by
      change Φ.symm (Φ (Quotient.mk'' (p : ModelCoordinates))) = _
      rw [Φ.symm_apply_apply]
      rfl), ← localPullMetric_comp _ _ _ hmk hval]
    erw [localPullMetric_quotientMetric (coordinateModelMetric .hyperbolicProduct)
      pullbackMetric_pants_smul]
    exact localPullMetric_subtype_val _ _
  exact GeometricStructure.ofFold ((coordinateModelMetric .hyperbolicProduct).restrictOpen ⊤)
    ((coordinateModelMetric_hasThurstonAtlas .hyperbolicProduct).foldRestrictOpen ⊤) (by decide)
    (coreChartFold C hk hwall hbij) hFl hsurj hcompat
    (by
      rw [hmetric]
      exact DifferentialGeometry.Geometry.Metric.riemannianMetricComplete_pullbackMetricCross
        pantsQuotientGeometry.complete Φ.symm)

theorem unfilledCoreInteriorGeometryOfCharts_model :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (unfilledCoreInteriorGeometryOfCharts C h0 hk hU hΔU hF hwall hdet hbij).model =
      ThurstonModel.hyperbolicProduct :=
  rfl

end Regression

theorem SeifertBlock.exists_unfilledCoreInteriorGeometry (B : SeifertBlock W d)
    (h0 : d.fillingCount = 0) (hk : d.k = 3) :
    ∃ G : W.InteriorGeometry ⊤,
      letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
      letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
      G.model = ThurstonModel.hyperbolicProduct := by
  obtain ⟨F, hF1, hF2, hF3, hF4, hF5, hF6⟩ := exists_foldCore
  have hwall := fold_hwall hF1
  have hbij : Set.BijOn (fun z : ℍ => F z) idealTriangle
      {u : ℂ | planarFunction 3 u < 0 ∧ 0 ≤ u.im} := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      exact hF5 ((coe_mem_triangleSet_iff z).2 hz)
    · intro z hz z' hz' h
      exact UpperHalfPlane.ext (hF4 ((coe_mem_triangleSet_iff z).2 hz)
        ((coe_mem_triangleSet_iff z').2 hz') h)
    · intro u hu
      obtain ⟨z, hz, rfl⟩ := fold_surjOn hF1 hF2 hF3 hF6 hwall u hu
      exact ⟨⟨z, hz.1⟩, (coe_mem_triangleSet_iff _).1 hz, rfl⟩
  exact ⟨unfilledCoreInteriorGeometryOfCharts (B.unfilledCharts h0) h0 hk
      (U := {z : ℂ | 0 < z.im}) (isOpen_lt continuous_const Complex.continuous_im)
      (fun z _ => z.im_pos) (fun z hz => (hF2 z hz).contDiffWithinAt) hwall
      (fun z _ => hF3 z z.im_pos) hbij,
    unfilledCoreInteriorGeometryOfCharts_model _ h0 hk _ _ _ hwall _ hbij⟩

theorem unfilledCoreInteriorGeometry_model_eq_routeQ (C : SeifertBlockCharts W d)
    (h0 : d.fillingCount = 0) (hk : d.k = 3) {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hΔU : ∀ z : ℍ, z ∈ idealTriangle → (z : ℂ) ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hwall : ∀ i : Fin 3, ∃ V : Set ℍ, IsOpen V ∧ wall i ⊆ V ∧
      ∀ z ∈ V, F ((wallReflection i • z : ℍ) : ℂ) = conj (F z))
    (hdet : ∀ z : ℍ, z ∈ idealTriangle → (fderiv ℝ F z).det ≠ 0)
    (hbij : Set.BijOn (fun z : ℍ => F z) idealTriangle
      {u : ℂ | planarFunction 3 u < 0 ∧ 0 ≤ u.im}) :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    letI := Manifold.interiorIsManifold W.model ∞ (M := W.pieceInterior ⊤)
    (unfilledCoreInteriorGeometryOfCharts C h0 hk hU hΔU hF hwall hdet hbij).model =
      (unfilledPantsBlockGeometry C h0 hk).model :=
  rfl

end GC.Seifert
