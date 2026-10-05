import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.LPA05SublevelFaceTypes
import DifferentialGeometry.Geometry.Collapse.ZeroModel.SublevelEmbedding
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph
import DifferentialGeometry.Topology.Handle.Embedding
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.MixedBoundary

/-!
# Zero faces: standard SMOOTH parametrizations from the selected LFR54 core models (D70-5)

Lane C14-ZSP35b; external review 70 §4 and disposition D70-5. The homeomorphism form
`zero_sublevel_frontier_type_ZSP35` (`LPA05SublevelFaceTypes`) is a topological face type; FC39
needs standard smooth `S²` / `T²` parametrizations. They are obtained by RESTRICTING the selected
LFR54 smooth core models (no classification of surfaces):

* generic: `mfderiv_comp_injective_ZSP35`, `mfderiv_injective_of_comp_ZSP35`,
  `diffeomorph_mfderiv_injective_ZSP35` (also with corners),
  `partialDiffeomorph_mfderiv_injective_ZSP35`;
* `discCore_val_mfderiv_injective_ZSP35`: the inclusion of a disc core `D_T ⊂ N_c` (with its
  boundary charts) has injective differentials, also at boundary points (regular-sublevel embedding
  `isSmoothEmbedding_sublevel_val` of the closed disc bundle, then the pull-back diffeomorphisms
  and the carrier diffeomorphism);
* `exists_isSmoothEmbedding_frontier_of_level_ZSP35`: a smooth injective immersion of a compact
  boundaryless `S` onto `frontier (Ψ '' A)` gives the smooth embedding `Ψ⁻¹ ∘ j` onto `frontier A`;
* `collar_boundary_param_ZSP35`: the boundary torus `t ↦ κ(t, 0)` of a half collar;
* the four core branches: `PointSoulCoreSublevel.frontier_standard_param_ZSP35`
  (`S² → ∂D³ →(Φ⁻¹) D_T ⊂ N_c →(Ψ⁻¹) M`), `CircleSoulCoreSublevel…` (Clifford torus of the
  solid torus), `KleinSoulCoreSublevel…` (external boundary torus of `D(o(K))`),
  `ProjectiveSoulCoreSublevel…` (the chart sphere of `ℝP³` lifted through the EMBEDDING `f`: the
  lift is smooth because `f` is an immersion and `f ∘ g` is the chart sphere — no `f.symm`);
* summary `zero_sublevel_frontier_standard_param_ZSP35` (review 70 §4's statement; the only extra
  environment assumption is `[T2Space M]`): `A = univ ∧ frontier A = ∅`, or a smooth embedding
  `ClosureSphere.{0} → M` (model `𝓡 2`) with range `frontier A`, or `Torus → M`
  (model `torusModel`) with range `frontier A`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function Manifold Topology
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.VectorBundle
open DifferentialGeometry.Topology.Morse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

section Generic

variable {E E' E'' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {I' : ModelWithCorners ℝ E' H'} {I'' : ModelWithCorners ℝ E'' H''}
  {X Y Z : Type*} [TopologicalSpace X] [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H' Y]
  [TopologicalSpace Z] [ChartedSpace H'' Z]

/-- The differential of a composite is injective as soon as both factors' are. -/
theorem mfderiv_comp_injective_ZSP35 {f : X → Y} {g : Y → Z} {x : X}
    (hf : MDifferentiableAt I I' f x) (hg : MDifferentiableAt I' I'' g (f x))
    (hfi : Injective (mfderiv I I' f x)) (hgi : Injective (mfderiv I' I'' g (f x))) :
    Injective (mfderiv I I'' (g ∘ f) x) := by
  rw [mfderiv_comp x hg hf]
  exact hgi.comp hfi

/-- A diffeomorphism (also between manifolds with corners) has injective differentials. -/
theorem diffeomorph_mfderiv_injective_ZSP35 (Φ : X ≃ₘ⟮I, I'⟯ Y) (x : X) :
    Injective (mfderiv I I' Φ x) := by
  have h1 : MDifferentiableAt I I' Φ x := Φ.contMDiff.mdifferentiableAt (by simp)
  have h2 : MDifferentiableAt I' I Φ.symm (Φ x) := Φ.symm.contMDiff.mdifferentiableAt (by simp)
  have hid : mfderiv I I (Φ.symm ∘ Φ) x = mfderiv I I (@id X) x := by
    congr 1
    funext y
    exact Φ.symm_apply_apply y
  rw [mfderiv_comp x h2 h1, mfderiv_id] at hid
  intro v w hvw
  have := congrArg (mfderiv I' I Φ.symm (Φ x)) hvw
  have h3 := congrArg (fun L => L v) hid
  have h4 := congrArg (fun L => L w) hid
  simp only [ContinuousLinearMap.comp_apply] at h3 h4
  exact h3.symm.trans (this.trans h4)

/-- The first factor of a composite with injective differential has injective differential. -/
theorem mfderiv_injective_of_comp_ZSP35 {f : X → Y} {g : Y → Z} {x : X}
    (hf : MDifferentiableAt I I' f x) (hg : MDifferentiableAt I' I'' g (f x))
    (h : Injective (mfderiv I I'' (g ∘ f) x)) : Injective (mfderiv I I' f x) := by
  rw [mfderiv_comp x hg hf] at h
  exact Injective.of_comp h

/-- A partial diffeomorphism has injective differentials on its source. -/
theorem partialDiffeomorph_mfderiv_injective_ZSP35 (φ : PartialDiffeomorph I I' X Y ∞) {x : X}
    (hx : x ∈ φ.source) : Injective (mfderiv I I' φ x) := by
  have hmd : φ.toOpenPartialHomeomorph.MDifferentiable I I' :=
    ⟨φ.contMDiffOn_toFun.mdifferentiableOn (by decide),
      φ.contMDiffOn_invFun.mdifferentiableOn (by decide)⟩
  exact hmd.mfderiv_injective hx

end Generic

section DiscCore

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]
  [IsContMDiffRiemannianBundle IB ∞ F V]
  {EN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN]
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
  {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- **The inclusion of a disc core into the model has injective differentials** (at boundary
points too): it is the carrier diffeomorphism after the regular-sublevel embedding of the closed
disc bundle (`isSmoothEmbedding_sublevel_val`) and the disc core's pull-back diffeomorphisms. -/
theorem discCore_val_mfderiv_injective_ZSP35
    (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) {m : ℕ}
    (hd : Module.finrank ℝ (EB × F) = m + 1) (T : ℝ) (hT : 0 < T)
    (x : {x : N // ‖(D.symm x).2‖ ≤ T}) :
    let := discCoreChartedSpace D hd T hT
    Injective (mfderiv (morseModelWithCornersHalfSpace m) IN
      (Subtype.val : {x : N // ‖(D.symm x).2‖ ≤ T} → N) x) := by
  let := normClosedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := closedDiscBundleChartedSpace (IB := IB) (V := V) hd T hT
  let := closedDiscBundle_isManifold (IB := IB) (V := V) hd T hT
  let := normClosedDiscBundle_isManifold (IB := IB) (V := V) hd T hT
  let := discCoreChartedSpace D hd T hT
  have hf : ContMDiff ((IB.prod 𝓘(ℝ, F)).transContinuousLinearEquiv (bundleRadiusBoundaryEquiv hd))
      𝓘(ℝ, ℝ) ∞ (fiberRadiusSquared (F := F) (V := V)) :=
    (bundleRadiusBoundaryEquiv hd).contMDiff_transContinuousLinearEquiv_left.mpr
      contMDiff_fiberRadiusSquared
  have hr : ∀ z : TotalSpace F V, fiberRadiusSquared z = T ^ 2 →
      mfderiv ((IB.prod 𝓘(ℝ, F)).transContinuousLinearEquiv (bundleRadiusBoundaryEquiv hd))
        𝓘(ℝ, ℝ) (fiberRadiusSquared (F := F) (V := V)) z ≠ 0 := by
    intro z hz hzero
    apply mfderiv_fiberRadiusSquared_level_ne_zero (IB := IB) hT z hz
    exact (isCriticalPointAt_transContinuousLinearEquiv_iff (IB.prod 𝓘(ℝ, F))
      (bundleRadiusBoundaryEquiv hd) (fiberRadiusSquared (F := F) (V := V)) z).mp hzero
  have hemb := ZeroModel.SublevelEmbedding.isSmoothEmbedding_sublevel_val
    (J := IB.prod 𝓘(ℝ, F)) (e := bundleRadiusBoundaryEquiv hd) hf hr
  let Φ : Diffeomorph (morseModelWithCornersHalfSpace m) (morseModelWithCornersHalfSpace m)
      {x : N // ‖(D.symm x).2‖ ≤ T}
      {z : TotalSpace F V // fiberRadiusSquared z ≤ T ^ 2} ∞ :=
    (discCoreDiffeomorph D hd T hT).symm.trans
      (DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph
        (I := morseModelWithCornersHalfSpace m) (n := ∞)
        (normClosedDiscSublevelHomeomorph (F := F) (V := V) T hT))
  have hfun : (Subtype.val : {x : N // ‖(D.symm x).2‖ ≤ T} → N) =
      D ∘ ((Subtype.val : {z : TotalSpace F V // fiberRadiusSquared z ≤ T ^ 2} → TotalSpace F V) ∘
        Φ) := by
    funext y
    have hΦy : (Φ y).val = D.symm y.val := rfl
    simp only [Function.comp_apply, hΦy, D.apply_symm_apply]
  rw [hfun]
  have h1 : Injective (mfderiv (morseModelWithCornersHalfSpace m) (IB.prod 𝓘(ℝ, F))
      ((Subtype.val : {z : TotalSpace F V // fiberRadiusSquared z ≤ T ^ 2} → TotalSpace F V) ∘
        Φ) x) :=
    mfderiv_comp_injective_ZSP35 (Φ.contMDiff.mdifferentiableAt (by simp))
      (hemb.contMDiff.mdifferentiableAt (by simp)) (diffeomorph_mfderiv_injective_ZSP35 Φ x)
      (hemb.isImmersion.mfderiv_injective (by simp) _)
  exact mfderiv_comp_injective_ZSP35
    ((hemb.contMDiff.comp Φ.contMDiff).mdifferentiableAt (by simp))
    (D.contMDiff.mdifferentiableAt (by simp)) h1 (diffeomorph_mfderiv_injective_ZSP35 D _)

end DiscCore

section Assembly

variable {ES : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
  {HS : Type*} [TopologicalSpace HS] {IS : ModelWithCorners ℝ ES HS} [IS.Boundaryless]
  {S : Type*} [TopologicalSpace S] [ChartedSpace HS S] [IsManifold IS ∞ S] [CompactSpace S]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] [T2Space M]
  {Nc : Type*} [TopologicalSpace Nc] [ChartedSpace E3 Nc]

/-- **Standard parametrization through the ambient partial diffeomorphism.** If a closed `A` is
carried into the model by `Ψ` (`A ⊆ Ψ.source`, `Ψ '' A` closed) and a compact boundaryless `S`
maps smoothly and injectively, with injective differentials, onto `frontier (Ψ '' A)`, then
`Ψ⁻¹ ∘ j : S → M` is a smooth embedding onto `frontier A`. -/
theorem exists_isSmoothEmbedding_frontier_of_level_ZSP35
    (Ψ : PartialDiffeomorph I3 I3 M Nc ∞) {A : Set M} (hA : IsClosed A) (hAs : A ⊆ Ψ.source)
    (hcl : IsClosed (Ψ '' A)) (j : S → Nc) (hj : ContMDiff IS I3 ∞ j) (hinj : Injective j)
    (hdj : ∀ x, Injective (mfderiv IS I3 j x)) (hrange : range j = frontier (Ψ '' A)) :
    ∃ e : S → M, IsSmoothEmbedding IS I3 ∞ e ∧ range e = frontier A := by
  have hfr := partialDiffeomorph_image_frontier_of_subset_source Ψ hA hAs hcl
  have hsub : range j ⊆ Ψ.symm.source := by
    rw [hrange, PartialDiffeomorph.symm_source]
    exact hcl.frontier_subset.trans (fun y ⟨x, hx, hxy⟩ => hxy ▸ Ψ.map_source (hAs hx))
  have he : ContMDiff IS I3 ∞ (Ψ.symm ∘ j) := contMDiff_comp_partialDiffeomorph Ψ.symm hj hsub
  have heinj : Injective (Ψ.symm ∘ j) := fun x y hxy =>
    hinj (Ψ.symm.toOpenPartialHomeomorph.injOn (hsub (mem_range_self x)) (hsub (mem_range_self y))
      hxy)
  have hde : ∀ x, Injective (mfderiv IS I3 (Ψ.symm ∘ j) x) :=
    injective_mfderiv_comp_partialDiffeomorph Ψ.symm hj hdj hsub
  refine ⟨Ψ.symm ∘ j, ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv
    (by simp) he hde, (he.continuous.isClosedEmbedding heinj).isEmbedding⟩, ?_⟩
  rw [range_comp, hrange, ← hfr, image_image]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : (Ψ.symm.toPartialEquiv : Nc → M) (Ψ.toPartialEquiv x) = x :=
      Ψ.left_inv (hAs (hA.frontier_subset hx))
    beta_reduce
    rw [h1]
    exact hx
  · intro hy
    exact ⟨y, hy, Ψ.left_inv (hAs (hA.frontier_subset hy))⟩

end Assembly

section Ball

/-- `S²` as the unit sphere of `ℝ³` (the instance of `SphereTwo`). -/
local instance sphereTwoDim_ZSP35 : Fact (Module.finrank ℝ E3 = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The inclusion of the unit sphere of `ℝ³` has injective differentials. -/
theorem sphereTwo_val_mfderiv_injective_ZSP35 (v : Metric.sphere (0 : E3) 1) :
    Injective (mfderiv (𝓡 2) I3 ((↑) : Metric.sphere (0 : E3) 1 → E3) v) := by
  have h := injective_mvfderiv_subtypeVal_sphere (E := E3) (n := 2) v
  unfold mvfderiv at h
  rw [ContinuousLinearMap.coe_comp] at h
  exact h.of_comp

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] [T2Space M]
  {Nc : Type} [TopologicalSpace Nc] [ChartedSpace E3 Nc]
  {A : Set M}

/-- **`D³`, standard smooth parametrization of the boundary** (review 70 §4, ball branch): for a
closed point-soul core sublevel there is a smooth embedding of the round `S²` onto `frontier A`:
`S² → ∂D³ →(Φ⁻¹) D_T ⊂ N_c →(Ψ⁻¹) M`. -/
theorem PointSoulCoreSublevel.frontier_standard_param_ZSP35 (hA : IsClosed A)
    (h : PointSoulCoreSublevel Nc A) :
    ∃ e : Metric.sphere (0 : E3) 1 → M, IsSmoothEmbedding (𝓡 2) I3 ∞ e ∧ range e = frontier A := by
  obtain ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hAs, hΨA, Φ, -,
    hΦ⟩ := h
  let := discCoreChartedSpace D hd T₀ hT₀
  let := DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2
  let := DifferentialGeometry.Topology.Handle.closedCellIsManifold 2
  have hu : Continuous fun y : Nc => ‖(D.symm y).2‖ :=
    continuous_discCoreRadius_of_isContMDiffRiemannianBundle D
  have hcl : IsClosed (Ψ '' A) := by
    rw [hΨA]
    exact isClosed_le hu continuous_const
  have hfr : frontier (Ψ '' A) = {y : Nc | ‖(D.symm y).2‖ = T₀} := by
    rw [hΨA]
    exact frontier_discCore_eq D.toHomeomorph hu hT₀
  let s : Metric.sphere (0 : E3) 1 → ClosedCell 3 := fun x =>
    ⟨x.val, le_of_eq (mem_sphere_zero_iff_norm.mp x.2)⟩
  have hemb := DifferentialGeometry.Topology.Handle.closedCellInclusion_isSmoothEmbedding 2
  have hvs : (Subtype.val : ClosedCell 3 → E3) ∘ s = ((↑) : Metric.sphere (0 : E3) 1 → E3) := rfl
  have hs : ContMDiff (𝓡 2) (𝓡∂ 3) ∞ s := by
    refine (ContMDiff.iff_comp_isImmersion hemb.isImmersion).mpr ⟨?_, ?_⟩
    · exact continuous_induced_rng.2 continuous_subtype_val
    · rw [hvs]
      exact contMDiff_coe_sphere
  have hsinj : Injective s := fun x y hxy => by
    have h := congrArg Subtype.val hxy
    exact Subtype.ext h
  have hds : ∀ x, Injective (mfderiv (𝓡 2) (𝓡∂ 3) s x) := fun x =>
    mfderiv_injective_of_comp_ZSP35 (hs.mdifferentiableAt (by simp))
      (hemb.contMDiff.mdifferentiableAt (by simp))
      (by rw [hvs]; exact sphereTwo_val_mfderiv_injective_ZSP35 x)
  let j : Metric.sphere (0 : E3) 1 → Nc := fun x => (Φ.symm (s x)).val
  have hval := discCore_inclusion_contMDiff D hd T₀ hT₀
  have hj : ContMDiff (𝓡 2) I3 ∞ j := hval.comp (Φ.symm.contMDiff.comp hs)
  have hjinj : Injective j := Subtype.val_injective.comp (Φ.symm.injective.comp hsinj)
  have hdj : ∀ x, Injective (mfderiv (𝓡 2) I3 j x) := fun x =>
    mfderiv_comp_injective_ZSP35 (f := fun x => Φ.symm (s x)) (g := Subtype.val)
      ((Φ.symm.contMDiff.comp hs).mdifferentiableAt (by simp))
      (hval.mdifferentiableAt (by simp))
      (mfderiv_comp_injective_ZSP35 (hs.mdifferentiableAt (by simp))
        (Φ.symm.contMDiff.mdifferentiableAt (by simp)) (hds x)
        (diffeomorph_mfderiv_injective_ZSP35 Φ.symm _))
      (discCore_val_mfderiv_injective_ZSP35 D hd T₀ hT₀ _)
  have hrange : range j = {y : Nc | ‖(D.symm y).2‖ = T₀} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine (hΦ (Φ.symm (s x))).mpr ?_
      rw [Φ.apply_symm_apply]
      exact mem_sphere_zero_iff_norm.mp x.2
    · intro hy
      have hy' : ‖(D.symm y).2‖ ≤ T₀ := le_of_eq hy
      have hw := (hΦ ⟨y, hy'⟩).mp hy
      refine ⟨⟨(Φ ⟨y, hy'⟩).val, mem_sphere_zero_iff_norm.mpr hw⟩, ?_⟩
      change (Φ.symm (s _)).val = y
      have : s ⟨(Φ ⟨y, hy'⟩).val, mem_sphere_zero_iff_norm.mpr hw⟩ = Φ ⟨y, hy'⟩ := rfl
      rw [this, Φ.symm_apply_apply]
  exact exists_isSmoothEmbedding_frontier_of_level_ZSP35 Ψ hA hAs hcl j hj hjinj hdj
    (hrange.trans hfr.symm)

end Ball

section Collar

open GC.Endpoint

/-- **The boundary torus of a half collar.** For a half collar
`κ : T² × [0, ∞) ⇀ X` (`κ.source = halfCollarSource`), `t ↦ κ(t, 0)` is smooth, injective and has
injective differentials. -/
theorem collar_boundary_param_ZSP35 {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanHalfSpace 3) X]
    (κ : PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) X ∞)
    (hsrc : κ.source = halfCollarSource) :
    ContMDiff torusModel (𝓡∂ 3) ∞ (fun t : Torus => κ (t, halfZero)) ∧
    Injective (fun t : Torus => κ (t, halfZero)) ∧
    ∀ t, Injective (mfderiv torusModel (𝓡∂ 3) (fun t : Torus => κ (t, halfZero)) t) := by
  have hmem : ∀ t : Torus, (t, halfZero) ∈ κ.source := fun t => by
    rw [hsrc]
    exact GC.GraphManifold.halfZero_mem_halfCollarSource t
  have hι : ContMDiff torusModel halfCollarModel ∞ (fun t : Torus => (t, halfZero)) :=
    contMDiff_id.prodMk contMDiff_const
  refine ⟨κ.contMDiffOn.comp_contMDiff hι hmem, fun t t' h => congrArg Prod.fst
    (κ.toOpenPartialHomeomorph.injOn (hmem t) (hmem t') h), fun t => ?_⟩
  have hιi : Injective (mfderiv torusModel halfCollarModel (fun t : Torus => (t, halfZero)) t) := by
    refine mfderiv_injective_of_comp_ZSP35 (g := Prod.fst) (hι.mdifferentiableAt (by simp))
      mdifferentiableAt_fst ?_
    have hid : (Prod.fst ∘ fun t : Torus => (t, (halfZero : EuclideanHalfSpace 1))) = id := rfl
    rw [hid, mfderiv_id]
    exact fun v w h => h
  exact mfderiv_comp_injective_ZSP35 (f := fun t : Torus => (t, halfZero)) (g := κ)
    (hι.mdifferentiableAt (by simp))
    ((κ.contMDiffOn_toFun.contMDiffAt (κ.open_source.mem_nhds (hmem t))).mdifferentiableAt
      (by simp)) hιi (partialDiffeomorph_mfderiv_injective_ZSP35 κ (hmem t))

end Collar

section Tori

open GC.Endpoint

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] [T2Space M]
  {Nc : Type} [TopologicalSpace Nc] [ChartedSpace E3 Nc]
  {A : Set M}

/-- **`S¹ × D²`, standard smooth parametrization of the boundary** (review 70 §4, circle branch):
the Clifford boundary torus `t ↦ κ(t, 0)` of the solid torus, then `Φ`, the disc core and `Ψ⁻¹`. -/
theorem CircleSoulCoreSublevel.frontier_standard_param_ZSP35 (hA : IsClosed A)
    (h : CircleSoulCoreSublevel Nc A) :
    ∃ e : Torus → M, IsSmoothEmbedding torusModel I3 ∞ e ∧ range e = frontier A := by
  obtain ⟨F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀, Ψ, hAs, hΨA, Φ, hΦ⟩ := h
  let := discCoreChartedSpace D hd T₀ hT₀
  have hu : Continuous fun y : Nc => ‖(D.symm y).2‖ :=
    continuous_discCoreRadius_of_isContMDiffRiemannianBundle D
  have hcl : IsClosed (Ψ '' A) := by
    rw [hΨA]
    exact isClosed_le hu continuous_const
  have hfr : frontier (Ψ '' A) = {y : Nc | ‖(D.symm y).2‖ = T₀} := by
    rw [hΨA]
    exact frontier_discCore_eq D.toHomeomorph hu hT₀
  obtain ⟨hs, hsinj, hds⟩ := collar_boundary_param_ZSP35 GC.GraphManifold.solidTorusCollar.{0}
    GC.GraphManifold.solidTorusCollar_source.{0}
  let j : Torus → Nc := fun t => (Φ (GC.GraphManifold.solidTorusCollar.{0} (t, halfZero))).val
  have hval := discCore_inclusion_contMDiff D hd T₀ hT₀
  have hj : ContMDiff torusModel I3 ∞ j := hval.comp (Φ.contMDiff.comp hs)
  have hjinj : Injective j := Subtype.val_injective.comp (Φ.injective.comp hsinj)
  have hdj : ∀ t, Injective (mfderiv torusModel I3 j t) := fun t =>
    mfderiv_comp_injective_ZSP35
      (f := fun t => Φ (GC.GraphManifold.solidTorusCollar.{0} (t, halfZero)))
      (g := Subtype.val) ((Φ.contMDiff.comp hs).mdifferentiableAt (by simp))
      (hval.mdifferentiableAt (by simp))
      (mfderiv_comp_injective_ZSP35 (hs.mdifferentiableAt (by simp))
        (Φ.contMDiff.mdifferentiableAt (by simp)) (hds t)
        (diffeomorph_mfderiv_injective_ZSP35 Φ _))
      (discCore_val_mfderiv_injective_ZSP35 D hd T₀ hT₀ _)
  have hrange : range j = {y : Nc | ‖(D.symm y).2‖ = T₀} := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact (hΦ (GC.GraphManifold.solidTorusCollar.{0} (t, halfZero))).mp
        (GC.GraphManifold.cliffordHeight_cliffordTorusPoint t)
    · intro hy
      have hy' : ‖(D.symm y).2‖ ≤ T₀ := le_of_eq hy
      have hz := (hΦ (Φ.symm ⟨y, hy'⟩)).mpr (by rw [Φ.apply_symm_apply]; exact hy)
      obtain ⟨t, ht⟩ := GC.GraphManifold.exists_cliffordTorusPoint_eq hz
      refine ⟨t, ?_⟩
      change (Φ (GC.GraphManifold.cliffordTorusPoint t)).val = y
      rw [ht, Φ.apply_symm_apply]
  exact exists_isSmoothEmbedding_frontier_of_level_ZSP35 Ψ hA hAs hcl j hj hjinj hdj
    (hrange.trans hfr.symm)

/-- **`D(o(K))`, standard smooth parametrization of the boundary** (review 70 §4, Klein branch):
the external boundary torus `t ↦ κ(t, 0)` of the Möbius bundle, then `Φ⁻¹`, the disc core and
`Ψ⁻¹`. -/
theorem KleinSoulCoreSublevel.frontier_standard_param_ZSP35 (hA : IsClosed A)
    (h : KleinSoulCoreSublevel Nc A) :
    ∃ e : Torus → M, IsSmoothEmbedding torusModel I3 ∞ e ∧ range e = frontier A := by
  obtain ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀,
    Ψ, hAs, hΨA, Φ, hΦ⟩ := h
  let := discCoreChartedSpace D hd T₀ hT₀
  have hu : Continuous fun y : Nc => ‖(D.symm y).2‖ :=
    continuous_discCoreRadius_of_isContMDiffRiemannianBundle D
  have hcl : IsClosed (Ψ '' A) := by
    rw [hΨA]
    exact isClosed_le hu continuous_const
  have hfr : frontier (Ψ '' A) = {y : Nc | ‖(D.symm y).2‖ = T₀} := by
    rw [hΨA]
    exact frontier_discCore_eq D.toHomeomorph hu hT₀
  obtain ⟨hs, hsinj, hds⟩ := collar_boundary_param_ZSP35 GC.Seifert.mobiusExternalCollar.{0}
    GC.Seifert.mobiusExternalCollar_source.{0}
  let j : Torus → Nc := fun t => (Φ.symm (GC.Seifert.mobiusExternalCollar.{0} (t, halfZero))).val
  have hval := discCore_inclusion_contMDiff D hd T₀ hT₀
  have hj : ContMDiff torusModel I3 ∞ j := hval.comp (Φ.symm.contMDiff.comp hs)
  have hjinj : Injective j := Subtype.val_injective.comp (Φ.symm.injective.comp hsinj)
  have hdj : ∀ t, Injective (mfderiv torusModel I3 j t) := fun t =>
    mfderiv_comp_injective_ZSP35
      (f := fun t => Φ.symm (GC.Seifert.mobiusExternalCollar.{0} (t, halfZero)))
      (g := Subtype.val) ((Φ.symm.contMDiff.comp hs).mdifferentiableAt (by simp))
      (hval.mdifferentiableAt (by simp))
      (mfderiv_comp_injective_ZSP35 (hs.mdifferentiableAt (by simp))
        (Φ.symm.contMDiff.mdifferentiableAt (by simp)) (hds t)
        (diffeomorph_mfderiv_injective_ZSP35 Φ.symm _))
      (discCore_val_mfderiv_injective_ZSP35 D hd T₀ hT₀ _)
  have hbd : ∀ w : GC.Seifert.mobiusBundleSet.{0},
      GC.Seifert.mobiusBundleFunction w.val = 0 ↔
        ∃ t, GC.Seifert.mobiusExternalCollar.{0} (t, halfZero) = w := fun w => by
    rw [← GC.Seifert.isBoundaryPoint_iff_external, GC.Seifert.mobiusBundleSet_isBoundaryPoint_iff]
  have hrange : range j = {y : Nc | ‖(D.symm y).2‖ = T₀} := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      refine (hΦ (Φ.symm (GC.Seifert.mobiusExternalCollar.{0} (t, halfZero)))).mpr ?_
      rw [Φ.apply_symm_apply]
      exact (hbd _).mpr ⟨t, rfl⟩
    · intro hy
      have hy' : ‖(D.symm y).2‖ ≤ T₀ := le_of_eq hy
      obtain ⟨t, ht⟩ := (hbd (Φ ⟨y, hy'⟩)).mp ((hΦ ⟨y, hy'⟩).mp hy)
      refine ⟨t, ?_⟩
      change (Φ.symm (GC.Seifert.mobiusExternalCollar.{0} (t, halfZero))).val = y
      rw [ht, Φ.symm_apply_apply]
  exact exists_isSmoothEmbedding_frontier_of_level_ZSP35 Ψ hA hAs hcl j hj hjinj hdj
    (hrange.trans hfr.symm)

end Tori

section Projective

/-- `S²` as the unit sphere of `ℝ³`. -/
local instance sphereTwoDimP_ZSP35 : Fact (Module.finrank ℝ E3 = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] [T2Space M]
  {Nc : Type} [TopologicalSpace Nc] [ChartedSpace E3 Nc]
  {A : Set M}

/-- **`ℝP³ ∖ int D³`, standard smooth parametrization of the boundary** (review 70 §4, projective
branch). The contract's `f` is a smooth EMBEDDING with exact image, not a packaged diffeomorphism:
the boundary sphere `S² → ℝP³` of the ball chart lies in `range f`, and it lifts through `f` to a
smooth map `g : S² → D_T` (smoothness from `f`'s immersion property, `f ∘ g` being the chart
sphere; continuity from `f`'s embedding); then the disc core and `Ψ⁻¹`. -/
theorem ProjectiveSoulCoreSublevel.frontier_standard_param_ZSP35 (hA : IsClosed A)
    (h : ProjectiveSoulCoreSublevel Nc A) :
    ∃ e : Metric.sphere (0 : E3) 1 → M, IsSmoothEmbedding (𝓡 2) I3 ∞ e ∧ range e = frontier A := by
  obtain ⟨B, k1, k2, k3, k4, k5, k6, F, i1, i2, i3, V, j1, j2, j3, j4, j5, j6, j7, D, hd, T₀, hT₀,
    Ψ, hAs, hΨA, cb, f, hf, hrange, hiff⟩ := h
  let := discCoreChartedSpace D hd T₀ hT₀
  have hu : Continuous fun y : Nc => ‖(D.symm y).2‖ :=
    continuous_discCoreRadius_of_isContMDiffRiemannianBundle D
  have hcl : IsClosed (Ψ '' A) := by
    rw [hΨA]
    exact isClosed_le hu continuous_const
  have hfr : frontier (Ψ '' A) = {y : Nc | ‖(D.symm y).2‖ = T₀} := by
    rw [hΨA]
    exact frontier_discCore_eq D.toHomeomorph hu hT₀
  have hsph : Metric.sphere (0 : E3) 1 ⊆ cb.chart.source := fun x hx =>
    cb.closedBall_subset_source (by
      rw [mem_closedBall, dist_zero_right]
      rw [mem_sphere_zero_iff_norm] at hx
      linarith)
  let c : Metric.sphere (0 : E3) 1 → projectiveThreeSpaceLift.{0}.Carrier := fun x => cb.chart x.val
  have hc : ContMDiff (𝓡 2) (𝓡 3) ∞ c :=
    cb.chart.contMDiffOn.comp_contMDiff contMDiff_coe_sphere (fun x => hsph x.2)
  have hdc : ∀ x, Injective (mfderiv (𝓡 2) (𝓡 3) c x) := fun x =>
    mfderiv_comp_injective_ZSP35 (f := ((↑) : Metric.sphere (0 : E3) 1 → E3)) (g := cb.chart)
      ((contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp))
      ((cb.chart.contMDiffOn_toFun.contMDiffAt
        (cb.chart.open_source.mem_nhds (hsph x.2))).mdifferentiableAt (by simp))
      (sphereTwo_val_mfderiv_injective_ZSP35 x)
      (partialDiffeomorph_mfderiv_injective_ZSP35 cb.chart (hsph x.2))
  have hcr : ∀ x, c x ∈ range f := fun x => by
    rw [hrange]
    rintro ⟨y, hy, hyx⟩
    have hyx' := cb.chart.toOpenPartialHomeomorph.injOn (cb.ball_subset_source hy) (hsph x.2) hyx
    rw [mem_ball_zero_iff] at hy
    have hx := mem_sphere_zero_iff_norm.mp x.2
    rw [hyx'] at hy
    linarith
  let g : Metric.sphere (0 : E3) 1 → {y : Nc // ‖(D.symm y).2‖ ≤ T₀} := fun x =>
    hf.isEmbedding.toHomeomorph.symm ⟨c x, hcr x⟩
  have hfg : f ∘ g = c := by
    funext x
    have := congrArg Subtype.val (hf.isEmbedding.toHomeomorph.apply_symm_apply ⟨c x, hcr x⟩)
    exact this
  have hgc : Continuous g :=
    hf.isEmbedding.toHomeomorph.symm.continuous.comp (hc.continuous.subtype_mk hcr)
  have hg : ContMDiff (𝓡 2) (morseModelWithCornersHalfSpace 2) ∞ g :=
    (ContMDiff.iff_comp_isImmersion hf.isImmersion).mpr ⟨hgc, hfg ▸ hc⟩
  have hginj : Injective g := fun x y hxy => by
    have h1 := congrArg f hxy
    change (f ∘ g) x = (f ∘ g) y at h1
    rw [hfg] at h1
    exact Subtype.ext (cb.chart.toOpenPartialHomeomorph.injOn (hsph x.2) (hsph y.2) h1)
  have hdg : ∀ x, Injective (mfderiv (𝓡 2) (morseModelWithCornersHalfSpace 2) g x) := fun x =>
    mfderiv_injective_of_comp_ZSP35 (hg.mdifferentiableAt (by simp))
      (hf.contMDiff.mdifferentiableAt (by simp)) (by rw [hfg]; exact hdc x)
  let j : Metric.sphere (0 : E3) 1 → Nc := fun x => (g x).val
  have hval := discCore_inclusion_contMDiff D hd T₀ hT₀
  have hj : ContMDiff (𝓡 2) I3 ∞ j := hval.comp hg
  have hjinj : Injective j := Subtype.val_injective.comp hginj
  have hdj : ∀ x, Injective (mfderiv (𝓡 2) I3 j x) := fun x =>
    mfderiv_comp_injective_ZSP35 (f := g) (g := Subtype.val) (hg.mdifferentiableAt (by simp))
      (hval.mdifferentiableAt (by simp)) (hdg x)
      (discCore_val_mfderiv_injective_ZSP35 D hd T₀ hT₀ _)
  have hrange' : range j = {y : Nc | ‖(D.symm y).2‖ = T₀} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine (hiff (g x)).mp ?_
      change (f ∘ g) x ∈ _
      rw [hfg]
      exact ⟨x.val, x.2, rfl⟩
    · intro hy
      have hy' : ‖(D.symm y).2‖ ≤ T₀ := le_of_eq hy
      obtain ⟨x, hx, hxy⟩ := (hiff ⟨y, hy'⟩).mpr hy
      refine ⟨⟨x, hx⟩, ?_⟩
      have h1 : f (g ⟨x, hx⟩) = f ⟨y, hy'⟩ := by
        change (f ∘ g) ⟨x, hx⟩ = _
        rw [hfg]
        exact hxy
      exact congrArg Subtype.val (hf.isEmbedding.injective h1)
  exact exists_isSmoothEmbedding_frontier_of_level_ZSP35 Ψ hA hAs hcl j hj hjinj hdj
    (hrange'.trans hfr.symm)

end Projective

section Summary

open GC.Endpoint

/-- `S²` as the unit sphere of `ℝ³`. -/
local instance sphereTwoDimS_ZSP35 : Fact (Module.finrank ℝ E3 = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M] [T2Space M]
  {Nc : Type} [TopologicalSpace Nc] [ChartedSpace E3 Nc] {A : Set M}

omit [IsManifold I3 ∞ M] [T2Space M] in
/-- A smooth embedding of the round `S²` gives one of `ClosureSphere = ULift S²` with the same
range. -/
theorem closureSphere_param_of_sphere_ZSP35 {e : Metric.sphere (0 : E3) 1 → M}
    (he : IsSmoothEmbedding (𝓡 2) I3 ∞ e) :
    IsSmoothEmbedding (𝓡 2) I3 ∞
        (e ∘ (DifferentialGeometry.Topology.uliftDiffeomorph.{0, 0} (𝓡 2)
          (Metric.sphere (0 : E3) 1)).symm) ∧
      range (e ∘ (DifferentialGeometry.Topology.uliftDiffeomorph.{0, 0} (𝓡 2)
          (Metric.sphere (0 : E3) 1)).symm) = range e :=
  ⟨DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp e he _,
    (DifferentialGeometry.Topology.uliftDiffeomorph.{0, 0} (𝓡 2)
      (Metric.sphere (0 : E3) 1)).symm.surjective.range_comp e⟩

/-- **The frontier of an LFR54-typed closed sublevel, standard smooth parametrization**
(review 70 §4, D70-5; `zero_sublevel_frontier_standard_param`): `A = M` with empty frontier
(compact model), or a smooth embedding of the standard `S² = ClosureSphere` onto `frontier A`
(ball, projective), or of the standard `T² = Circle × Circle` (circle, Klein). The parametrization
restricts the SELECTED LFR54 smooth core model's boundary (no surface classification). -/
theorem zero_sublevel_frontier_standard_param_ZSP35 {oM : ManifoldOrientation I3 M 3}
    (hA : IsClosed A)
    (h : CompactModelSublevel oM Nc A ∨ PointSoulCoreSublevel Nc A ∨ CircleSoulCoreSublevel Nc A ∨
      ProjectiveSoulCoreSublevel Nc A ∨ KleinSoulCoreSublevel Nc A) :
    (A = univ ∧ frontier A = ∅) ∨
    (∃ e : GC.GraphManifold.ClosureSphere.{0} → M,
      IsSmoothEmbedding (𝓡 2) I3 ∞ e ∧ range e = frontier A) ∨
    (∃ e : Torus → M, IsSmoothEmbedding torusModel I3 ∞ e ∧ range e = frontier A) := by
  rcases h with h | h | h | h | h
  · exact Or.inl ⟨h.1, h.frontier_eq_empty_ZSP35⟩
  · obtain ⟨e, he, hr⟩ := h.frontier_standard_param_ZSP35 hA
    obtain ⟨he', hr'⟩ := closureSphere_param_of_sphere_ZSP35 he
    exact Or.inr (Or.inl ⟨_, he', hr'.trans hr⟩)
  · exact Or.inr (Or.inr (h.frontier_standard_param_ZSP35 hA))
  · obtain ⟨e, he, hr⟩ := h.frontier_standard_param_ZSP35 hA
    obtain ⟨he', hr'⟩ := closureSphere_param_of_sphere_ZSP35 he
    exact Or.inr (Or.inl ⟨_, he', hr'.trans hr⟩)
  · exact Or.inr (Or.inr (h.frontier_standard_param_ZSP35 hA))

end Summary

end DifferentialGeometry.Geometry.Collapse
