import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelFaceStandardParam
import DifferentialGeometry.Topology.Manifold.SubmersionFiber
import DifferentialGeometry.Topology.Manifold.OpenEmbedding

/-!
# Zero faces: compatibility with the regular-level structure and match with the selected model

Lane C14-ZSP35b; external review 70 §4, disposition D70-5 (b) and (c). Kernel forms.

* (b) `regularLevel_diffeomorph_of_param_ZSP35`: if `f : M → ℝ` is smooth and regular at `c` and
  `e : S → M` is a smooth embedding of a boundaryless surface onto `{f = c}`, the corestriction of
  `e` is a DIFFEOMORPHISM onto the level with its natural `regularFiberChartedSpace` (the identity
  identification of the standard parametrization and the regular-level smooth structure is smooth
  both ways).
* (c) `image_frontier_discCore_ZSP35` and, for the four core types,
  `PointSoulCoreSublevel.frontier_model_boundary_ZSP35`, `CircleSoulCoreSublevel.…`,
  `ProjectiveSoulCoreSublevel.…`, `KleinSoulCoreSublevel.…`: the contract holds with the extra
  clause `Ψ '' frontier A = {‖(D⁻¹ y).2‖ = T₀}` — the face is exactly the preimage, under the
  contract's OWN `Ψ`, of the actual boundary of the disc core of the SAME soul bundle of the
  selected model (not another embedded surface of the same type).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function Manifold Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Topology.Manifold

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
local notation "E2" => EuclideanSpace ℝ (Fin 2)

section Regular

variable {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
  {HS : Type*} [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} [IS.Boundaryless]
  {S : Type*} [TopologicalSpace S] [ChartedSpace HS S] [IsManifold IS ∞ S]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

/-- **Compatibility with the natural regular-level structure** (review 70 §4, D70-5 (b)): if a
smooth `f : M → ℝ` is regular at `c` and `e : S → M` is a smooth embedding of a boundaryless
surface onto `{f = c}` (`dim S = dim M − 1`), then the corestriction of `e` is a DIFFEOMORPHISM onto
the level with its natural `regularFiberChartedSpace` structure. -/
theorem regularLevel_diffeomorph_of_param_ZSP35 (f : M → ℝ) (c : ℝ)
    (hf : ContMDiff I3 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, f x = c → Surjective (mfderiv I3 𝓘(ℝ, ℝ) f x)) {e : S → M}
    (he : IsSmoothEmbedding IS I3 ∞ e) (hr : range e = {x | f x = c})
    (hdim : Module.finrank ℝ ES = Module.finrank ℝ (Fin (Module.finrank ℝ E3 -
      Module.finrank ℝ ℝ) → ℝ)) :
    let := regularFiberChartedSpace f c hf hreg
    ∃ Θ : Diffeomorph IS 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) S
        {x : M // f x = c} ∞, ∀ s, (Θ s).val = e s := by
  let := regularFiberChartedSpace f c hf hreg
  let := regularFiberIsManifold f c hf hreg
  have hmem : ∀ s, f (e s) = c := fun s => by
    have : e s ∈ range e := mem_range_self s
    rw [hr] at this
    exact this
  let ê : S → {x : M // f x = c} := fun s => ⟨e s, hmem s⟩
  have hê : ContMDiff IS 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ) ∞ ê :=
    (contMDiff_regularFiber_iff f c hf hreg ê).mpr he.contMDiff
  have hval := contMDiff_regularFiberInclusion f c hf hreg
  have hdê : ∀ s, Injective (mfderiv IS 𝓘(ℝ, Fin (Module.finrank ℝ E3 - Module.finrank ℝ ℝ) → ℝ)
      ê s) := fun s =>
    mfderiv_injective_of_comp_ZSP35 (g := Subtype.val) (hê.mdifferentiableAt (by simp))
      (hval.mdifferentiableAt (by simp)) (he.isImmersion.mfderiv_injective (by simp) s)
  have hloc := isLocalDiffeomorph_of_injective_mfderiv ê hê hdê hdim
  have hbij : Bijective ê := by
    refine ⟨fun s t h => he.isEmbedding.injective (congrArg Subtype.val h), fun y => ?_⟩
    have : (y : M) ∈ range e := by
      rw [hr]
      exact y.2
    obtain ⟨s, hs⟩ := this
    exact ⟨s, Subtype.ext hs⟩
  exact ⟨hloc.diffeomorphOfBijective hbij, fun s => rfl⟩

end Regular

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

/-- The ambient partial diffeomorphism carries the frontier of a closed set carried onto a disc
core exactly onto the top level of that core. -/
theorem image_frontier_discCore_ZSP35
    (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Nc ∞) {T₀ : ℝ} (hT₀ : 0 < T₀)
    (Ψ : PartialDiffeomorph I3 I3 M Nc ∞) {A : Set M} (hA : IsClosed A) (hAs : A ⊆ Ψ.source)
    (hΨA : Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T₀}) :
    Ψ '' frontier A = {y : Nc | ‖(D.symm y).2‖ = T₀} := by
  have hu : Continuous fun y : Nc => ‖(D.symm y).2‖ :=
    continuous_discCoreRadius_of_isContMDiffRiemannianBundle D
  have hcl : IsClosed (Ψ '' A) := by
    rw [hΨA]
    exact isClosed_le hu continuous_const
  rw [partialDiffeomorph_image_frontier_of_subset_source Ψ hA hAs hcl, hΨA]
  exact frontier_discCore_eq D.toHomeomorph hu hT₀

end Level

section Match

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M]
  {Nc : Type} [TopologicalSpace Nc] [ChartedSpace E3 Nc] {A : Set M}

/-- **Match with the SELECTED model boundary, D³ (point soul)** (review 70 §4,
    D70-5 (c)): the contract of
`PointSoulCoreSublevel` holds with the additional clause that the contract's OWN ambient partial
diffeomorphism `Ψ` carries `frontier A` exactly onto the boundary level `{‖(D⁻¹ y).2‖ = T₀}` of
the disc core of the SAME soul bundle `D` of the selected model (so the standard parametrizations
of `LPA05SublevelFaceStandardParam` are parametrizations of that actual model boundary). -/
theorem PointSoulCoreSublevel.frontier_model_boundary_ZSP35 (hA : IsClosed A) (h :
    PointSoulCoreSublevel Nc A) :
  ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
    (_ : FiniteDimensional ℝ F) (V : (Fin 0 → ℝ) → Type)
    (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
    (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
    (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, Fin 0 → ℝ))
    (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, Fin 0 → ℝ) ∞ F V)
    (D : Diffeomorph (𝓘(ℝ, Fin 0 → ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Nc ∞)
    (hd : Module.finrank ℝ ((Fin 0 → ℝ) × F) = 2 + 1) (T₀ : ℝ) (hT₀ : 0 < T₀)
    (Ψ : PartialDiffeomorph I3 I3 M Nc ∞),
    A ⊆ Ψ.source ∧ Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T₀} ∧
      Ψ '' frontier A = {y | ‖(D.symm y).2‖ = T₀} ∧
    letI := discCoreChartedSpace D hd T₀ hT₀
    letI := DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2
    ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
        {y : Nc // ‖(D.symm y).2‖ ≤ T₀} (ClosedCell 3) ∞,
      (∀ y, T₀ * ‖(Φ y).val‖ = ‖(D.symm y.val).2‖) ∧
      ∀ y, ‖(D.symm y.val).2‖ = T₀ ↔ ‖(Φ y).val‖ = 1 := by
  obtain ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hAs, hΨA, hrest⟩ := h
  exact ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hAs, hΨA,
      image_frontier_discCore_ZSP35 D hT₀ Ψ hA hAs hΨA, hrest⟩

/-- **Match with the SELECTED model boundary, S¹ × D² (circle soul)** (review 70 §4,
    D70-5 (c)): the contract of
`CircleSoulCoreSublevel` holds with the additional clause that the contract's OWN ambient partial
diffeomorphism `Ψ` carries `frontier A` exactly onto the boundary level `{‖(D⁻¹ y).2‖ = T₀}` of
the disc core of the SAME soul bundle `D` of the selected model (so the standard parametrizations
of `LPA05SublevelFaceStandardParam` are parametrizations of that actual model boundary). -/
theorem CircleSoulCoreSublevel.frontier_model_boundary_ZSP35 (hA : IsClosed A) (h :
    CircleSoulCoreSublevel Nc A) :
  ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
    (_ : FiniteDimensional ℝ F) (V : AddCircle (1 : ℝ) → Type)
    (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
    (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
    (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V 𝓘(ℝ, ℝ))
    (_ : IsContMDiffRiemannianBundle 𝓘(ℝ, ℝ) ∞ F V)
    (D : Diffeomorph (𝓘(ℝ, ℝ).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Nc ∞)
    (hd : Module.finrank ℝ (ℝ × F) = 2 + 1) (T₀ : ℝ) (hT₀ : 0 < T₀)
    (Ψ : PartialDiffeomorph I3 I3 M Nc ∞),
    A ⊆ Ψ.source ∧ Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T₀} ∧
      Ψ '' frontier A = {y | ‖(D.symm y).2‖ = T₀} ∧
    letI := discCoreChartedSpace D hd T₀ hT₀
    ∃ Φ : Diffeomorph GC.GraphManifold.solidTorusCarrier.{0}.model
        (morseModelWithCornersHalfSpace 2) GC.GraphManifold.solidTorusCarrier.{0}.Carrier
        {y : Nc // ‖(D.symm y).2‖ ≤ T₀} ∞,
      ∀ y : GC.GraphManifold.solidTorusCarrier.{0}.Carrier,
        GC.GraphManifold.cliffordHeight (y : GC.GraphManifold.solidTorusSet.{0}).val = 0 ↔
          ‖(D.symm (Φ y).val).2‖ = T₀ := by
  obtain ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hAs, hΨA, hrest⟩ := h
  exact ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hAs, hΨA,
      image_frontier_discCore_ZSP35 D hT₀ Ψ hA hAs hΨA, hrest⟩

/-- **Match with the SELECTED model boundary, ℝP³ ∖ int D³ (surface soul)** (review 70 §4,
    D70-5 (c)): the contract of
`ProjectiveSoulCoreSublevel` holds with the additional clause that the contract's OWN ambient
    partial
diffeomorphism `Ψ` carries `frontier A` exactly onto the boundary level `{‖(D⁻¹ y).2‖ = T₀}` of
the disc core of the SAME soul bundle `D` of the selected model (so the standard parametrizations
of `LPA05SublevelFaceStandardParam` are parametrizations of that actual model boundary). -/
theorem ProjectiveSoulCoreSublevel.frontier_model_boundary_ZSP35 (hA : IsClosed A) (h :
    ProjectiveSoulCoreSublevel Nc A) :
  ∃ (B : Type) (_ : TopologicalSpace B) (_ : ChartedSpace E2 B) (_ : IsManifold (𝓡 2) ∞ B)
    (_ : CompactSpace B) (_ : T2Space B) (_ : ConnectedSpace B),
    ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
      (_ : FiniteDimensional ℝ F) (V : B → Type)
      (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
      (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
      (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V (𝓡 2))
      (_ : IsContMDiffRiemannianBundle (𝓡 2) ∞ F V)
      (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Nc ∞)
      (hd : Module.finrank ℝ (E2 × F) = 2 + 1) (T₀ : ℝ) (hT₀ : 0 < T₀)
      (Ψ : PartialDiffeomorph I3 I3 M Nc ∞),
      A ⊆ Ψ.source ∧ Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T₀} ∧
      Ψ '' frontier A = {y | ‖(D.symm y).2‖ = T₀} ∧
      letI := discCoreChartedSpace D hd T₀ hT₀
      ∃ (cb : OrientedBallChart projectiveThreeSpaceLift.{0}.toClosedOrientedManifold)
        (f : {y : Nc // ‖(D.symm y).2‖ ≤ T₀} → projectiveThreeSpaceLift.{0}.Carrier),
        IsSmoothEmbedding (morseModelWithCornersHalfSpace 2) (𝓡 3) ∞ f ∧
        range f = {w | w ∉ cb.chart '' Metric.ball (0 : E3) 1} ∧
        ∀ y, f y ∈ cb.chart '' Metric.sphere (0 : E3) 1 ↔ ‖(D.symm y.val).2‖ = T₀ := by
  obtain ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀,
      Ψ, hAs, hΨA, hrest⟩ := h
  exact ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀,
      Ψ, hAs, hΨA, image_frontier_discCore_ZSP35 D hT₀ Ψ hA hAs hΨA, hrest⟩

/-- **Match with the SELECTED model boundary, D(o(K)) (surface soul)** (review 70 §4,
    D70-5 (c)): the contract of
`KleinSoulCoreSublevel` holds with the additional clause that the contract's OWN ambient partial
diffeomorphism `Ψ` carries `frontier A` exactly onto the boundary level `{‖(D⁻¹ y).2‖ = T₀}` of
the disc core of the SAME soul bundle `D` of the selected model (so the standard parametrizations
of `LPA05SublevelFaceStandardParam` are parametrizations of that actual model boundary). -/
theorem KleinSoulCoreSublevel.frontier_model_boundary_ZSP35 (hA : IsClosed A) (h :
    KleinSoulCoreSublevel Nc A) :
  ∃ (B : Type) (_ : TopologicalSpace B) (_ : ChartedSpace E2 B) (_ : IsManifold (𝓡 2) ∞ B)
    (_ : CompactSpace B) (_ : T2Space B) (_ : ConnectedSpace B),
    ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℝ F)
      (_ : FiniteDimensional ℝ F) (V : B → Type)
      (_ : ∀ s, NormedAddCommGroup (V s)) (_ : ∀ s, InnerProductSpace ℝ (V s))
      (_ : TopologicalSpace (TotalSpace F V)) (_ : FiberBundle F V)
      (_ : VectorBundle ℝ F V) (_ : ContMDiffVectorBundle ∞ F V (𝓡 2))
      (_ : IsContMDiffRiemannianBundle (𝓡 2) ∞ F V)
      (D : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) Nc ∞)
      (hd : Module.finrank ℝ (E2 × F) = 2 + 1) (T₀ : ℝ) (hT₀ : 0 < T₀)
      (Ψ : PartialDiffeomorph I3 I3 M Nc ∞),
      A ⊆ Ψ.source ∧ Ψ '' A = {y | ‖(D.symm y).2‖ ≤ T₀} ∧
      Ψ '' frontier A = {y | ‖(D.symm y).2‖ = T₀} ∧
      letI := discCoreChartedSpace D hd T₀ hT₀
      ∃ Φ : Diffeomorph (morseModelWithCornersHalfSpace 2) (𝓡∂ 3)
          {y : Nc // ‖(D.symm y).2‖ ≤ T₀} GC.Seifert.mobiusBundleSet.{0} ∞,
        ∀ y, ‖(D.symm y.val).2‖ = T₀ ↔ GC.Seifert.mobiusBundleFunction (Φ y).val = 0 := by
  obtain ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀,
      Ψ, hAs, hΨA, hrest⟩ := h
  exact ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀,
      Ψ, hAs, hΨA, image_frontier_discCore_ZSP35 D hT₀ Ψ hA hAs hΨA, hrest⟩

end Match

end DifferentialGeometry.Geometry.Collapse
