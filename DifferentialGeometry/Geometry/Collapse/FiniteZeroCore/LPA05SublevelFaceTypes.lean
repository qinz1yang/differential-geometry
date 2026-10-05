import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelTypeClause
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CoreBoundary
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MobiusBlockAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordGluing

/-!
# The boundary of an actual zero sublevel: empty, `S²` or `T²` (ZSP02 / ZSP03 face type)

Blueprint `master207B.tex`, ZSP02 (`thm:fibration-actual-zero-domains`, B:6374: "Every nonempty
boundary is a connected `S²` or `T²`. Empty-boundary cases retain their original compact types")
and ZSP03 (B:6481: the zero faces), on the conclusion predicates of LPA05's sublevel-type clause
(`FiniteZeroCore/LPA05SublevelTypeClause.lean`, LFR54 A:29526). Lane C14-ZSP35, kernel form: a
closed set `A` of a three-manifold `M` with one of the five LFR54 types has frontier

* empty, with `A = univ` (compact model; `CompactModelSublevel.frontier_eq_empty_ZSP35`);
* homeomorphic to the round `S²` (`D³`: `PointSoulCoreSublevel.frontier_sphere_ZSP35`;
  `ℝP³ ∖ int D³`: `ProjectiveSoulCoreSublevel.frontier_sphere_ZSP35`);
* homeomorphic to `ℝ²/ℤ²` (`S¹ × D²`: `CircleSoulCoreSublevel.frontier_torus_ZSP35`, the Clifford
  torus of the solid torus; `D(o(K))`: `KleinSoulCoreSublevel.frontier_torus_ZSP35`, the external
  boundary collar of the Möbius bundle).

The frontier goes to the top level of the disc core by the ambient partial diffeomorphism
(`frontierHomeomorphDiscLevel_ZSP35`, from `partialDiffeomorph_image_frontier_of_subset_source` and
`frontier_discCore_eq`), then to the model boundary by the core's diffeomorphism. Summary:
`zero_sublevel_frontier_type_ZSP35`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function Manifold Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.VectorBundle

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

section Level

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB ∞ F V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  {Nc : Type*} [TopologicalSpace Nc] [ChartedSpace E3 Nc]

/-- The frontier of a closed set carried onto a disc core is homeomorphic to the top level. -/
def frontierHomeomorphDiscLevel_ZSP35
    (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Nc ∞) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (Ψ : PartialDiffeomorph I3 I3 M Nc ∞) {A : Set M} (hA : IsClosed A) (hAs : A ⊆ Ψ.source)
    (hΨA : Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T₀}) :
    frontier A ≃ₜ {y : Nc | ‖(D.symm y).2‖ = T₀} := by
  have hu : Continuous fun y : Nc => ‖(D.symm y).2‖ :=
    continuous_discCoreRadius_of_isContMDiffRiemannianBundle D
  have hcl : IsClosed (Ψ '' A) := by
    rw [hΨA]
    exact isClosed_le hu continuous_const
  have hfr := partialDiffeomorph_image_frontier_of_subset_source Ψ hA hAs hcl
  have hfd : frontier {y : Nc | ‖(D.symm y).2‖ ≤ T₀} = {y : Nc | ‖(D.symm y).2‖ = T₀} :=
    frontier_discCore_eq D.toHomeomorph hu hT₀
  rw [hΨA, hfd] at hfr
  exact Ψ.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource
    (hA.frontier_subset.trans hAs) hfr


/-- A homeomorphism restricts to a homeomorphism between two sets that it matches pointwise. -/
def homeomorphSetOfIff_ZSP35 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y)
    {P : X → Prop} {Q : Y → Prop} (hPQ : ∀ x, P x ↔ Q (h x)) : {x | P x} ≃ₜ {y | Q y} :=
  (h.image {x | P x}).trans (Homeomorph.setCongr (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hPQ x).mp hx
    · intro hy
      refine ⟨h.symm y, (hPQ _).mpr ?_, h.apply_symm_apply y⟩
      rw [h.apply_symm_apply]
      exact hy))

/-- A level of a sublevel subtype is homeomorphic to the level in the ambient space. -/
def levelHomeomorphSubtype_ZSP35 {Y : Type*} [TopologicalSpace Y] {q P : Y → Prop}
    (hPq : ∀ y, P y → q y) : {y : Y | P y} ≃ₜ {z : {y : Y // q y} | P z.val} :=
  ((Topology.IsEmbedding.subtypeVal (p := q)).homeomorphImage {z : {y : Y // q y} | P z.val}).trans
    (Homeomorph.setCongr (by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨⟨y, hPq y hy⟩, hy, rfl⟩)) |>.symm
end Level


section Cases

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
  {Nc : Type} [TopologicalSpace Nc] [ChartedSpace E3 Nc] {A : Set M}

/-- The unit-norm level of the closed cell is the round sphere. -/
def closedCellLevelHomeomorph_ZSP35 :
    {w : ClosedCell 3 | ‖w.val‖ = 1} ≃ₜ Metric.sphere (0 : E3) 1 :=
  ((Topology.IsEmbedding.subtypeVal (p := fun x : E3 => ‖x‖ ≤ 1)).homeomorphImage
    {w : ClosedCell 3 | ‖w.val‖ = 1}).trans (Homeomorph.setCongr (by
      ext x
      rw [mem_sphere_zero_iff_norm]
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hx
        exact ⟨⟨x, le_of_eq hx⟩, hx, rfl⟩))

/-- **`D³` boundary.** The frontier of a closed point-soul core sublevel is a round `S²`. -/
theorem PointSoulCoreSublevel.frontier_sphere_ZSP35 (hA : IsClosed A)
    (h : PointSoulCoreSublevel Nc A) : Nonempty (frontier A ≃ₜ Metric.sphere (0 : E3) 1) := by
  obtain ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hAs, hΨA, Φ, -,
    hΦ⟩ := h
  have e1 := frontierHomeomorphDiscLevel_ZSP35 D hT₀ Ψ hA hAs hΨA
  have e2 := levelHomeomorphSubtype_ZSP35 (Y := Nc) (q := fun y => ‖(D.symm y).2‖ ≤ T₀)
    (P := fun y => ‖(D.symm y).2‖ = T₀) (fun y hy => le_of_eq hy)
  let := discCoreChartedSpace D hd T₀ hT₀
  let := DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2
  have e3 := homeomorphSetOfIff_ZSP35 Φ.toHomeomorph
    (P := fun z : {y : Nc // ‖(D.symm y).2‖ ≤ T₀} => ‖(D.symm z.val).2‖ = T₀)
    (Q := fun w : ClosedCell 3 => ‖w.val‖ = 1) (fun z => hΦ z)
  exact ⟨e1.trans (e2.trans (e3.trans closedCellLevelHomeomorph_ZSP35))⟩


/-- The Clifford torus `{cliffordHeight = 0}` of the solid torus is `ℝ²/ℤ²`. -/
def solidTorusLevelHomeomorph_ZSP35 :
    {y : GC.GraphManifold.solidTorusSet.{0} | GC.GraphManifold.cliffordHeight y.val = 0} ≃ₜ
      (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) := by
  have hemb : Topology.IsEmbedding GC.GraphManifold.cliffordTorusPoint.{0} :=
    (GC.GraphManifold.continuous_cliffordTorusPoint.isClosedEmbedding
      GC.GraphManifold.cliffordTorusPoint_injective).isEmbedding
  have hr : range GC.GraphManifold.cliffordTorusPoint.{0} =
      {y : GC.GraphManifold.solidTorusSet.{0} | GC.GraphManifold.cliffordHeight y.val = 0} := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact GC.GraphManifold.cliffordHeight_cliffordTorusPoint t
    · intro hy
      exact GC.GraphManifold.exists_cliffordTorusPoint_eq hy
  exact ((hemb.toHomeomorph.trans (Homeomorph.setCongr hr)).symm).trans
    (Homeomorph.prodCongr (AddCircle.homeomorphCircle one_ne_zero).symm
      (AddCircle.homeomorphCircle one_ne_zero).symm)

/-- **`S¹ × D²` boundary.** The frontier of a closed circle-soul core sublevel is `ℝ²/ℤ²`. -/
theorem CircleSoulCoreSublevel.frontier_torus_ZSP35 (hA : IsClosed A)
    (h : CircleSoulCoreSublevel Nc A) :
    Nonempty (frontier A ≃ₜ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by
  obtain ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hAs, hΨA, Φ, hΦ⟩ := h
  have e1 := frontierHomeomorphDiscLevel_ZSP35 D hT₀ Ψ hA hAs hΨA
  have e2 := levelHomeomorphSubtype_ZSP35 (Y := Nc) (q := fun y => ‖(D.symm y).2‖ ≤ T₀)
    (P := fun y => ‖(D.symm y).2‖ = T₀) (fun y hy => le_of_eq hy)
  let := discCoreChartedSpace D hd T₀ hT₀
  have e3 := homeomorphSetOfIff_ZSP35 Φ.toHomeomorph
    (P := fun y : GC.GraphManifold.solidTorusCarrier.{0}.Carrier =>
      GC.GraphManifold.cliffordHeight (y : GC.GraphManifold.solidTorusSet.{0}).val = 0)
    (Q := fun z : {y : Nc // ‖(D.symm y).2‖ ≤ T₀} => ‖(D.symm z.val).2‖ = T₀) (fun y => hΦ y)
  exact ⟨e1.trans (e2.trans (e3.symm.trans solidTorusLevelHomeomorph_ZSP35))⟩

/-- **`ℝP³ ∖ int D³` boundary.** The frontier of a closed projective-soul core sublevel is a
round `S²`. -/
theorem ProjectiveSoulCoreSublevel.frontier_sphere_ZSP35 (hA : IsClosed A)
    (h : ProjectiveSoulCoreSublevel Nc A) :
    Nonempty (frontier A ≃ₜ Metric.sphere (0 : E3) 1) := by
  obtain ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀,
    Ψ, hAs, hΨA, cb, f, hf, hrange, hiff⟩ := h
  have e1 := frontierHomeomorphDiscLevel_ZSP35 D hT₀ Ψ hA hAs hΨA
  have e2 := levelHomeomorphSubtype_ZSP35 (Y := Nc) (q := fun y => ‖(D.symm y).2‖ ≤ T₀)
    (P := fun y => ‖(D.symm y).2‖ = T₀) (fun y hy => le_of_eq hy)
  let := discCoreChartedSpace D hd T₀ hT₀
  have hsph : Metric.sphere (0 : E3) 1 ⊆ cb.chart.source := fun x hx =>
    cb.closedBall_subset_source (by
      rw [mem_closedBall, dist_zero_right]
      rw [mem_sphere_zero_iff_norm] at hx
      linarith)
  have himg : f '' {z : {y : Nc // ‖(D.symm y).2‖ ≤ T₀} | ‖(D.symm z.val).2‖ = T₀} =
      cb.chart '' Metric.sphere (0 : E3) 1 := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hiff z).mpr hz
    · rintro ⟨x, hx, rfl⟩
      have hnot : cb.chart x ∈ {w | w ∉ cb.chart '' Metric.ball (0 : E3) 1} := by
        rintro ⟨y, hy, hyx⟩
        have hyx' := cb.chart.toOpenPartialHomeomorph.injOn (cb.ball_subset_source hy)
          (hsph hx) hyx
        rw [mem_ball_zero_iff] at hy
        rw [mem_sphere_zero_iff_norm] at hx
        rw [hyx'] at hy
        linarith
      rw [← hrange] at hnot
      obtain ⟨z, hz⟩ := hnot
      exact ⟨z, (hiff z).mp (hz ▸ ⟨x, hx, rfl⟩), hz⟩
  have e3 := (hf.isEmbedding.homeomorphImage
    {z : {y : Nc // ‖(D.symm y).2‖ ≤ T₀} | ‖(D.symm z.val).2‖ = T₀}).trans
      (Homeomorph.setCongr himg)
  have e4 := (cb.chart.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource hsph rfl).symm
  exact ⟨e1.trans (e2.trans (e3.trans e4))⟩

/-- The boundary `{Q = 0}` of `D(o(K)) = {Q ≤ 0}` is `ℝ²/ℤ²` (its external boundary collar). -/
def mobiusBundleLevelHomeomorph_ZSP35 :
    {w : GC.Seifert.mobiusBundleSet.{0} | GC.Seifert.mobiusBundleFunction w.val = 0} ≃ₜ
      (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) := by
  let τ : GC.Endpoint.Torus → GC.Seifert.mobiusBundleSet.{0} := fun t =>
    GC.Seifert.mobiusExternalCollar.{0} (t, GC.Endpoint.halfZero)
  have hsrc : ∀ t, (t, GC.Endpoint.halfZero) ∈ GC.Seifert.mobiusExternalCollar.{0}.source :=
    fun t => by
      rw [GC.Seifert.mobiusExternalCollar_source]
      exact GC.GraphManifold.halfZero_mem_halfCollarSource t
  have hcont : Continuous τ :=
    (GC.Seifert.mobiusExternalCollar.{0}.contMDiffOn.comp_contMDiff
      (contMDiff_id.prodMk contMDiff_const) hsrc).continuous
  have hinj : Injective τ := fun t t' h => congrArg Prod.fst
    (GC.Seifert.mobiusExternalCollar.{0}.toOpenPartialHomeomorph.injOn (hsrc t) (hsrc t') h)
  have hr : range τ =
      {w : GC.Seifert.mobiusBundleSet.{0} | GC.Seifert.mobiusBundleFunction w.val = 0} := by
    ext w
    rw [mem_ofPred_eq, ← GC.Seifert.mobiusBundleSet_isBoundaryPoint_iff,
      GC.Seifert.isBoundaryPoint_iff_external]
    rfl
  exact (((hcont.isClosedEmbedding hinj).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hr)).symm).trans
    (Homeomorph.prodCongr (AddCircle.homeomorphCircle one_ne_zero).symm
      (AddCircle.homeomorphCircle one_ne_zero).symm)

/-- **`D(o(K))` boundary.** The frontier of a closed Klein-soul core sublevel is `ℝ²/ℤ²`. -/
theorem KleinSoulCoreSublevel.frontier_torus_ZSP35 (hA : IsClosed A)
    (h : KleinSoulCoreSublevel Nc A) :
    Nonempty (frontier A ≃ₜ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by
  obtain ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀,
    Ψ, hAs, hΨA, Φ, hΦ⟩ := h
  have e1 := frontierHomeomorphDiscLevel_ZSP35 D hT₀ Ψ hA hAs hΨA
  have e2 := levelHomeomorphSubtype_ZSP35 (Y := Nc) (q := fun y => ‖(D.symm y).2‖ ≤ T₀)
    (P := fun y => ‖(D.symm y).2‖ = T₀) (fun y hy => le_of_eq hy)
  let := discCoreChartedSpace D hd T₀ hT₀
  have e3 := homeomorphSetOfIff_ZSP35 Φ.toHomeomorph
    (P := fun z : {y : Nc // ‖(D.symm y).2‖ ≤ T₀} => ‖(D.symm z.val).2‖ = T₀)
    (Q := fun w : GC.Seifert.mobiusBundleSet.{0} => GC.Seifert.mobiusBundleFunction w.val = 0)
    (fun z => hΦ z)
  exact ⟨e1.trans (e2.trans (e3.trans mobiusBundleLevelHomeomorph_ZSP35))⟩

/-- **Compact model.** The frontier of the whole source is empty. -/
theorem CompactModelSublevel.frontier_eq_empty_ZSP35 [IsManifold I3 ∞ M]
    {oM : ManifoldOrientation I3 M 3}
    (h : CompactModelSublevel oM Nc A) : frontier A = ∅ := by
  rw [h.1, frontier_univ]
/-- **The frontier of an LFR54-typed closed sublevel** (ZSP02 / ZSP03 face type, kernel form):
empty with `A = univ`, or homeomorphic to the round `S²`, or homeomorphic to `ℝ²/ℤ²`. -/
theorem zero_sublevel_frontier_type_ZSP35 [IsManifold I3 ∞ M] {oM : ManifoldOrientation I3 M 3}
    (hA : IsClosed A)
    (h : CompactModelSublevel oM Nc A ∨ PointSoulCoreSublevel Nc A ∨ CircleSoulCoreSublevel Nc A ∨
      ProjectiveSoulCoreSublevel Nc A ∨ KleinSoulCoreSublevel Nc A) :
    (A = univ ∧ frontier A = ∅) ∨ Nonempty (frontier A ≃ₜ Metric.sphere (0 : E3) 1) ∨
      Nonempty (frontier A ≃ₜ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by
  rcases h with h | h | h | h | h
  · exact Or.inl ⟨h.1, h.frontier_eq_empty_ZSP35⟩
  · exact Or.inr (Or.inl (h.frontier_sphere_ZSP35 hA))
  · exact Or.inr (Or.inr (h.frontier_torus_ZSP35 hA))
  · exact Or.inr (Or.inl (h.frontier_sphere_ZSP35 hA))
  · exact Or.inr (Or.inr (h.frontier_torus_ZSP35 hA))

end Cases
end DifferentialGeometry.Geometry.Collapse
