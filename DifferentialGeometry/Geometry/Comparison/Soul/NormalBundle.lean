import DifferentialGeometry.Geometry.Comparison.Soul.NormalFrames
import DifferentialGeometry.Geometry.Comparison.Soul.EmbeddedSliceManifold
import Mathlib.Geometry.Manifold.VectorBundle.Basic

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold BigOperators
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

private instance tangentFinite (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

private instance tangentT2 (x : M) : T2Space (TangentSpace I x) :=
  inferInstanceAs (T2Space E)


abbrev normalBundleFiber (g : SmoothRiemannianMetric I M) (S : Set M) (x : S) : Type _ :=
  normalSpace (I := I) g S x.1

def normalBundleInclusion (g : SmoothRiemannianMetric I M) (S : Set M) :
    TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
      (normalBundleFiber (I := I) g S) → TangentBundle I M :=
  fun z => ⟨z.proj.1, z.snd.1⟩

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)] in
theorem normalBundleInclusion_injective (g : SmoothRiemannianMetric I M) (S : Set M) :
    Function.Injective (normalBundleInclusion (I := I) g S) := by
  rintro ⟨p, v⟩ ⟨q, w⟩ h
  have hp : p = q := Subtype.ext (congrArg TotalSpace.proj h)
  subst q
  have hv : v = w := Subtype.ext (TotalSpace.mk_injective p.1 h)
  subst w
  rfl

variable (g : SmoothRiemannianMetric I M) {S : Set M}

local notation "FN" => (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)

private structure NormalFrameData (p : S) where
  functions : Fin (Module.finrank ℝ E - maxSliceDim I S) → M → ℝ
  domain : Set M
  mem_domain : p.1 ∈ domain
  family : IsSliceDefiningFamilyOn (I := I) g S functions domain

private def normalFrameData (hEnorm : IsMetricNorm (I := I) g)
    (hconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) (p : S) :
    NormalFrameData g p := by
  have h : Nonempty (NormalFrameData g p) := by
    obtain ⟨m, F, W, hp, hfam, hm, _, _⟩ :=
      exists_smooth_normal_frame g hEnorm hconv hB p.property
    subst m
    exact ⟨⟨F, W, hp, hfam⟩⟩
  exact Classical.choice h

namespace NormalFrameData

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

variable {g} {p : S} (D : NormalFrameData g p) (hB : relBoundary I S = ∅)

private def equiv (q : S) (hq : q.1 ∈ D.domain) : FN ≃ₗ[ℝ] normalBundleFiber g S q := by
  have hn : q.1 ∈ maxSliceLocus I S := by
    rw [relBoundary_eq_empty_iff.mp hB]
    exact q.property
  refine
    { toFun := fun c => ⟨normalFrameSynthesis (I := I) g D.functions q.1 c, ?_⟩
      invFun := fun v => normalGramInverse (I := I) g D.functions q.1
        (normalFramePairing (I := I) g D.functions q.1 v)
      left_inv := ?_
      right_inv := ?_
      map_add' := ?_
      map_smul' := ?_ }
  · simpa only [relBoundary_eq_empty_iff.mp hB] using
      D.family.synthesis_mem_normalSpace hq hn c
  · intro c d
    exact Subtype.ext (map_add (normalFrameSynthesis (I := I) g D.functions q.1) c d)
  · intro c v
    exact Subtype.ext (map_smul (normalFrameSynthesis (I := I) g D.functions q.1) c v)
  · intro c
    change normalGramInverse (I := I) g D.functions q.1
      (normalFramePairing (I := I) g D.functions q.1
        (normalFrameSynthesis (I := I) g D.functions q.1 c)) = c
    rw [D.family.normalGramInverse_apply hq hn, normalFramePairing_synthesis,
      ← D.family.gramEquiv_apply hq hn]
    exact (D.family.gramEquiv hq hn).symm_apply_apply c
  · intro v
    apply Subtype.ext
    change normalFrameSynthesis (I := I) g D.functions q.1
      (normalGramInverse (I := I) g D.functions q.1
        (normalFramePairing (I := I) g D.functions q.1 v)) = (v : TangentSpace I q.1)
    rw [D.family.normalGramInverse_apply hq hn]
    exact D.family.synthesis_gramEquiv_symm_pairing hq hn
      ⟨v, by rw [relBoundary_eq_empty_iff.mp hB]; exact v.property⟩

private theorem equiv_apply (q : S) (hq : q.1 ∈ D.domain) (v : FN) :
    (D.equiv hB q hq v : TangentSpace I q.1) =
      normalFrameSynthesis (I := I) g D.functions q.1 v := rfl

private theorem equiv_symm_apply (q : S) (hq : q.1 ∈ D.domain)
    (v : normalBundleFiber g S q) :
    (D.equiv hB q hq).symm v = normalGramInverse (I := I) g D.functions q.1
      (normalFramePairing (I := I) g D.functions q.1 v) := rfl

private theorem pairing_contMDiff [I.Boundaryless] :
    ContMDiff I.tangent 𝓘(ℝ, FN) ∞
      (fun z : TangentBundle I M =>
        normalFramePairing (I := I) g D.functions z.proj z.snd) := by
  apply contMDiff_pi_space.2
  intro j
  have hb : ContMDiff I.tangent I ∞
      (TotalSpace.proj : TangentBundle I M → M) := Bundle.contMDiff_proj _
  have happ : ContMDiff I.tangent (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun z : TangentBundle I M =>
        (⟨z.proj, g.inner z.proj (gradFun (I := I) g (D.functions j) z.proj) z.snd⟩ :
          TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
    ContMDiff.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := fun z : TangentBundle I M => z.proj) (g.contMDiff.comp hb)
      ((gradFun_contMDiff_total_section (I := I) g (D.family.contMDiff j)).comp hb)
      contMDiff_id
  intro z
  exact (Bundle.contMDiffAt_totalSpace.mp (happ z)).2

private def pretrivialization : Pretrivialization FN
    (TotalSpace.proj : TotalSpace FN (normalBundleFiber g S) → S) := by
  classical
  refine
    { toFun := fun z => (z.proj, if hq : z.proj.1 ∈ D.domain then
        (D.equiv hB z.proj hq).symm z.snd else 0)
      invFun := fun z => ⟨z.1, if hq : z.1.1 ∈ D.domain then D.equiv hB z.1 hq z.2 else 0⟩
      source := {z | z.proj.1 ∈ D.domain}
      target := {q : S | q.1 ∈ D.domain} ×ˢ (univ : Set FN)
      baseSet := {q : S | q.1 ∈ D.domain}
      open_baseSet := D.family.isOpen.preimage continuous_subtype_val
      open_target := (D.family.isOpen.preimage continuous_subtype_val).prod isOpen_univ
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ => rfl
      map_source' := fun z hz => ⟨hz, mem_univ _⟩
      map_target' := fun z hz => hz.1
      left_inv' := ?_
      right_inv' := ?_ }
  · rintro ⟨q, v⟩ hq
    change q.1 ∈ D.domain at hq
    simp only [dite_eq_left hq, LinearEquiv.apply_symm_apply]
  · rintro ⟨q, v⟩ ⟨hq, _⟩
    change q.1 ∈ D.domain at hq
    simp only [dite_eq_left hq, LinearEquiv.symm_apply_apply]

private theorem pretrivialization_apply (q : S) (hq : q.1 ∈ D.domain)
    (v : normalBundleFiber g S q) :
    D.pretrivialization hB ⟨q, v⟩ = (q, (D.equiv hB q hq).symm v) := by
  classical
  change (q, if h : q.1 ∈ D.domain then (D.equiv hB q h).symm v else 0) = _
  rw [dite_eq_left hq]

private theorem pretrivialization_symm (q : S) (hq : q.1 ∈ D.domain) (v : FN) :
    (D.pretrivialization hB).symm q v = D.equiv hB q hq v := by
  have h := (D.pretrivialization hB).symm_apply_apply_mk hq (D.equiv hB q hq v)
  rw [D.pretrivialization_apply hB q hq, LinearEquiv.symm_apply_apply] at h
  exact h

private theorem pretrivialization_isLinear : (D.pretrivialization hB).IsLinear ℝ := by
  constructor
  intro q hq
  convert! (D.equiv hB q hq).symm.toLinearMap.isLinear using 1
  funext v
  exact congrArg Prod.snd (D.pretrivialization_apply hB q hq v)

private def transition {p' : S} (D' : NormalFrameData g p') (x : M) : FN →L[ℝ] FN :=
  (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := FN)
    (Fin (Module.finrank ℝ E - maxSliceDim I S))).symm
    (fun j => normalGramInverse (I := I) g D'.functions x
      (normalFramePairing (I := I) g D'.functions x (gradFun (I := I) g (D.functions j) x)))

private theorem transition_apply {p' : S} (D' : NormalFrameData g p')
    (x : M) (v : FN) : D.transition D' x v =
    normalGramInverse (I := I) g D'.functions x
      (normalFramePairing (I := I) g D'.functions x
        (normalFrameSynthesis (I := I) g D.functions x v)) := by
  change ((LinearEquiv.piRing ℝ FN
    (Fin (Module.finrank ℝ E - maxSliceDim I S)) ℝ).symm _) v = _
  rw [LinearEquiv.piRing_symm_apply]
  simp only [normalFrameSynthesis_apply, map_sum, map_smul]

private theorem transition_contMDiffAt [I.Boundaryless] (hB : relBoundary I S = ∅)
    {p' : S} (D' : NormalFrameData g p')
    {x : M} (hx : x ∈ D'.domain) (hxS : x ∈ S) :
    ContMDiffAt I 𝓘(ℝ, FN →L[ℝ] FN) ∞ (D.transition D') x := by
  have hcols : ContMDiffAt I 𝓘(ℝ, Fin (Module.finrank ℝ E - maxSliceDim I S) → FN) ∞
      (fun y j => normalGramInverse (I := I) g D'.functions y
        (normalFramePairing (I := I) g D'.functions y (gradFun (I := I) g (D.functions j) y))) x := by
    apply contMDiffAt_pi_space.2
    intro j
    exact D'.family.normalCoordinates_contMDiffAt hx
      (by rw [relBoundary_eq_empty_iff.mp hB]; exact hxS)
      (gradFun_contMDiff_total_section (I := I) g (D.family.contMDiff j))
  exact (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := FN)
    (Fin (Module.finrank ℝ E - maxSliceDim I S))).symm.toContinuousLinearMap.contMDiff.contMDiffAt.comp
      x hcols

private theorem transition_eq_coordChange {p' : S} (D' : NormalFrameData g p')
    (q : S) (hq : q.1 ∈ D.domain) (hq' : q.1 ∈ D'.domain) (v : FN) :
    D.transition D' q.1 v =
      (D'.pretrivialization hB ⟨q, (D.pretrivialization hB).symm q v⟩).2 := by
  rw [D.pretrivialization_symm hB q hq, D'.pretrivialization_apply hB q hq']
  rw [D'.equiv_symm_apply hB q hq', D.equiv_apply hB q hq, D.transition_apply]

private theorem totalSpaceMk_isInducing :
    _root_.Topology.IsInducing
      (D.pretrivialization hB ∘ (TotalSpace.mk p : normalBundleFiber g S p →
        TotalSpace FN (normalBundleFiber g S))) := by
  have h := (D.equiv hB p D.mem_domain).symm.toContinuousLinearEquiv.toHomeomorph.isInducing
  have hp := (_root_.Topology.isInducing_const_prod (x := p)).mpr h
  convert! hp using 1
  funext v
  exact D.pretrivialization_apply hB p D.mem_domain v

end NormalFrameData

def normalBundlePrebundle (hEnorm : IsMetricNorm (I := I) g)
    (hconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) :
    VectorPrebundle ℝ FN (normalBundleFiber (I := I) g S) := by
  let D := normalFrameData g hEnorm hconv hB
  refine
    { pretrivializationAtlas := Set.range (fun p : S => (D p).pretrivialization hB)
      pretrivializationAt := fun p => (D p).pretrivialization hB
      mem_base_pretrivializationAt := fun p => (D p).mem_domain
      pretrivialization_mem_atlas := fun p => ⟨p, rfl⟩
      pretrivialization_linear' := ?_
      exists_coordChange := ?_
      totalSpaceMk_isInducing := fun p => (D p).totalSpaceMk_isInducing hB }
  · rintro _ ⟨p, rfl⟩
    exact (D p).pretrivialization_isLinear hB
  · rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩
    refine ⟨fun q : S => (D p).transition (D p') q.1, ?_, ?_⟩
    · intro q hq
      exact (((D p).transition_contMDiffAt hB (D p') hq.2 q.property).continuousAt.comp
        continuous_subtype_val.continuousAt).continuousWithinAt
    · intro q hq v
      exact (D p).transition_eq_coordChange hB (D p') q hq.1 hq.2 v

theorem exists_normalBundle_trivializationAt_frame (hEnorm : IsMetricNorm (I := I) g)
    (hconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) (p : S) :
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    ∃ (F : Fin (Module.finrank ℝ E - maxSliceDim I S) → M → ℝ) (W : Set M),
      IsSliceDefiningFamilyOn (I := I) g S F W ∧ p.1 ∈ W ∧
      (trivializationAt FN (normalBundleFiber g S) p).baseSet = {q : S | q.1 ∈ W} ∧
      ∀ (q : S), q.1 ∈ W → ∀ v : FN,
        ((trivializationAt FN (normalBundleFiber g S) p).symm q v : TangentSpace I q.1) =
          ∑ j, v j • gradFun (I := I) g (F j) q.1 := by
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let D := normalFrameData g hEnorm hconv hB p
  refine ⟨D.functions, D.domain, D.family, D.mem_domain, rfl, ?_⟩
  intro q hq v
  change ((D.pretrivialization hB).symm q v : TangentSpace I q.1) = _
  rw [D.pretrivialization_symm hB q hq, D.equiv_apply hB q hq,
    normalFrameSynthesis_apply]

theorem normalBundle_isContMDiff (hEnorm : IsMetricNorm (I := I) g)
    (hconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ContMDiffVectorBundle ∞ FN (normalBundleFiber (I := I) g S)
      𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) := by
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  have ha : a.IsContMDiff 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ) ∞ := by
    constructor
    rintro _ ⟨p, rfl⟩ _ ⟨p', rfl⟩
    let D := normalFrameData g hEnorm hconv hB
    refine ⟨fun q : S => (D p).transition (D p') q.1, ?_, ?_⟩
    · intro q hq
      exact (((D p).transition_contMDiffAt hB (D p') hq.2 q.property).comp q
        (embeddedSlice_inclusion_contMDiff hS q)).contMDiffWithinAt
    · intro q hq v
      exact (D p).transition_eq_coordChange hB (D p') q hq.1 hq.2 v
  let _ := ha
  exact a.contMDiffVectorBundle 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)

theorem normalBundleInclusion_contMDiff (hEnorm : IsMetricNorm (I := I) g)
    (hconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ContMDiff ((𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)).prod 𝓘(ℝ, FN)) I.tangent ∞
      (normalBundleInclusion (I := I) g S) := by
  classical
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  let IB := 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)
  let IN := IB.prod 𝓘(ℝ, FN)
  let b : TotalSpace FN (normalBundleFiber g S) → M := fun z => z.proj.1
  have hb : ContMDiff IN I ∞ b :=
    (embeddedSlice_inclusion_contMDiff hS).comp (Bundle.contMDiff_proj (normalBundleFiber g S))
  change ContMDiff IN I.tangent ∞ (normalBundleInclusion (I := I) g S)
  intro z
  let D := normalFrameData g hEnorm hconv hB z.proj
  let e := trivializationAt FN (normalBundleFiber g S) z.proj
  let eM := trivializationAt E (TangentSpace I) (b z)
  have hc : ContMDiffAt IN 𝓘(ℝ, FN) ∞ (fun y => (e y).2) z :=
    (Bundle.contMDiffAt_totalSpace.mp (contMDiffAt_id (I := IN))).2
  have hgrad (j : Fin (Module.finrank ℝ E - maxSliceDim I S)) :
      ContMDiffAt IN 𝓘(ℝ, E) ∞
        (fun y => (eM ⟨b y, gradFun (I := I) g (D.functions j) (b y)⟩).2) z :=
    ((Bundle.contMDiffAt_totalSpace.mp
      (gradFun_contMDiff_total_section (I := I) g (D.family.contMDiff j) (b z))).2).comp z (hb z)
  have hsum : ContMDiffAt IN 𝓘(ℝ, E) ∞
      (fun y => ∑ j, (e y).2 j •
        (eM ⟨b y, gradFun (I := I) g (D.functions j) (b y)⟩).2) z := by
    apply ContMDiffAt.sum
    intro j _
    exact ((contMDiffAt_pi_space.mp hc) j).smul (hgrad j)
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨hb z, hsum.congr_of_eventuallyEq ?_⟩
  have hD : ∀ᶠ y in 𝓝 z, b y ∈ D.domain :=
    (hb z).continuousAt (D.family.isOpen.mem_nhds D.mem_domain)
  have hM : ∀ᶠ y in 𝓝 z, b y ∈ eM.baseSet :=
    (hb z).continuousAt (eM.open_baseSet.mem_nhds (mem_baseSet_trivializationAt _ _ _))
  filter_upwards [hD, hM] with y hy hyM
  have he : (e y).2 = (D.equiv hB y.proj hy).symm y.snd :=
    congrArg Prod.snd (D.pretrivialization_apply hB y.proj hy y.snd)
  have hv : (y.snd : TangentSpace I (b y)) =
      normalFrameSynthesis (I := I) g D.functions (b y) (e y).2 := by
    rw [he, ← D.equiv_apply hB y.proj hy, LinearEquiv.apply_symm_apply]
  change (eM ⟨b y, (y.snd : TangentSpace I (b y))⟩).2 = _
  rw [hv, ← eM.continuousLinearMapAt_apply_of_mem ℝ hyM,
    normalFrameSynthesis_apply, map_sum]
  simp only [map_smul]
  simp only [eM.continuousLinearMapAt_apply_of_mem ℝ hyM]

theorem normalBundleInclusion_isEmbedding (hEnorm : IsMetricNorm (I := I) g)
    (hconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) :
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    _root_.Topology.IsEmbedding (normalBundleInclusion (I := I) g S) := by
  classical
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  let inc := normalBundleInclusion (I := I) g S
  have hi : Continuous inc :=
    (normalBundleInclusion_contMDiff g hEnorm hconv hB).continuous
  have hlift
      (f : Set.range inc → TotalSpace FN (normalBundleFiber g S)) (x : Set.range inc)
      (hf : ContinuousAt (inc ∘ f) x) : ContinuousAt f x := by
    let b : Set.range inc → M := fun y => (f y).proj.1
    have hb : ContinuousAt b x :=
      (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt.comp hf
    let D := normalFrameData g hEnorm hconv hB (f x).proj
    let e := trivializationAt FN (normalBundleFiber g S) (f x).proj
    have hN : b x ∈ maxSliceLocus I S := by
      rw [relBoundary_eq_empty_iff.mp hB]
      exact (f x).proj.property
    have hG : ContinuousAt (fun y => normalGramInverse (I := I) g D.functions (b y)) x :=
      (D.family.normalGramInverse_contMDiffAt (x := b x) D.mem_domain hN).continuousAt.comp hb
    have hP := (D.pairing_contMDiff.continuous.continuousAt).comp hf
    have hcoords : ContinuousAt (fun y => normalGramInverse (I := I) g D.functions (b y)
        (normalFramePairing (I := I) g D.functions (b y) (f y).snd)) x :=
      hG.clm_apply hP
    apply (FiberBundle.continuousAt_totalSpace FN f).mpr
    refine ⟨hb.codRestrict (fun y => (f y).proj.property), hcoords.congr_of_eventuallyEq ?_⟩
    have hD : ∀ᶠ y in 𝓝 x, b y ∈ D.domain :=
      hb (D.family.isOpen.mem_nhds D.mem_domain)
    filter_upwards [hD] with y hy
    change (D.pretrivialization hB (f y)).2 = _
    rw [D.pretrivialization_apply hB (f y).proj hy,
      D.equiv_symm_apply hB (f y).proj hy]
  let e := Equiv.ofInjective inc (normalBundleInclusion_injective g S)
  have he : Continuous e := by
    exact hi.subtype_mk _
  have he' : Continuous e.symm := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply hlift e.symm x
    change ContinuousAt (inc ∘ (Equiv.ofInjective inc
      (normalBundleInclusion_injective g S)).symm) x
    rw [Equiv.self_comp_ofInjective_symm]
    exact continuous_subtype_val.continuousAt
  let H : TotalSpace FN (normalBundleFiber g S) ≃ₜ Set.range inc :=
    { e with continuous_toFun := he, continuous_invFun := he' }
  exact _root_.Topology.IsEmbedding.subtypeVal.comp H.isEmbedding

end DifferentialGeometry.Geometry.Topology
