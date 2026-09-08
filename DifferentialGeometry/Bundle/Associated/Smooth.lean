import DifferentialGeometry.Bundle.Associated.VectorBundle
import DifferentialGeometry.Bundle.Principal.Smooth
import Mathlib.Geometry.Manifold.VectorBundle.Basic

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

namespace ContRepresentation

variable {k G B W : Type*} [NontriviallyNormedField k] [Group G]
  [TopologicalSpace G] [TopologicalSpace B] [NormedAddCommGroup W] [NormedSpace k W]
  {P : B → Type*} [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P] [IsPrincipalBundle P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners k E H) [ChartedSpace H B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace k EG]
  {HG : Type*} [TopologicalSpace HG] (IG : ModelWithCorners k EG HG) [ChartedSpace HG G]
  (n : ℕ∞ω)

@[instance_reducible]
def associatedFiberBundleOfAtlas (ρ : ContRepresentation k G W)
    (hρ : Continuous (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet) :
    letI := (ρ.associatedVectorPrebundle (P := P) hρ).totalSpaceTopology
    FiberBundle W (fun x => P x →ₑ[ρ.toRepresentation] W) := by
  letI := (ρ.associatedVectorPrebundle (P := P) hρ).totalSpaceTopology
  letI := (ρ.associatedVectorPrebundle (P := P) hρ).toFiberBundle
  let hact := (hρ.comp continuous_fst).clm_apply continuous_snd
  exact
    { totalSpaceMk_isInducing' := FiberBundle.totalSpaceMk_isInducing W _
      trivializationAtlas' := {e | ∃ (p : Trivialization G (π G P)) (hp : p ∈ A),
        e = @Representation.associatedTrivialization k G B W _ _ _ _ _ _ _
          P _ _ _ _ _ ρ.toRepresentation hact p (hA p hp)}
      trivializationAt' := fun x => @Representation.associatedTrivialization k G B W _ _ _ _ _ _ _
        P _ _ _ _ _ ρ.toRepresentation hact (e₀ x) (hA (e₀ x) (he₀ x))
      mem_baseSet_trivializationAt' := hx₀
      trivialization_mem_atlas' := fun x => ⟨e₀ x, he₀ x, rfl⟩ }

theorem associated_vector_bundle_of_atlas (ρ : ContRepresentation k G W)
    (hρ : Continuous (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ A hA e₀ he₀ hx₀
    VectorBundle k W (fun x => P x →ₑ[ρ.toRepresentation] W) := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ A hA e₀ he₀ hx₀
  refine { trivialization_linear' := ?_, continuousOn_coordChange' := ?_ }
  · rintro _ ⟨e, he, rfl⟩
    let := hA e he
    exact Representation.associatedTrivialization.isLinear _ _ _
  · rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    let := hA e he
    let := hA e' he'
    apply (hρ.comp_continuousOn (e.continuousOn_principalSection_sdiv e')).congr
    intro x hx
    ext w
    exact ρ.toRepresentation.associatedTrivialization_coordChangeL_apply _ e e' hx w

theorem associated_contMDiffVectorBundle_of_atlas (ρ : ContRepresentation k G W)
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) n (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ∀ e' ∈ A,
      ContMDiffOn I IG n (fun x => e'.principalSection x /ₛ e.principalSection x)
        (e.baseSet ∩ e'.baseSet)) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    ContMDiffVectorBundle n W (fun x => P x →ₑ[ρ.toRepresentation] W) I := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  constructor
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  let := hA e he
  let := hA e' he'
  apply (hρ.comp_contMDiffOn (hP e he e' he')).congr
  intro x hx
  ext w
  exact ρ.toRepresentation.associatedTrivialization_coordChangeL_apply _ e e' hx w

theorem associated_contMDiffVectorBundle_of_smooth_atlas
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace k EP]
    {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners k EP HP)
    [ChartedSpace HP (TotalSpace G P)]
    (ρ : ContRepresentation k G W)
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) n (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) n e e.source ∧
      ContMDiffOn (I.prod IG) IP n e.toOpenPartialHomeomorph.symm e.target) :
    letI := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    letI := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    letI := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    ContMDiffVectorBundle n W (fun x => P x →ₑ[ρ.toRepresentation] W) I := by
  apply ρ.associated_contMDiffVectorBundle_of_atlas I IG n hρ A hA e₀ he₀ hx₀
  intro e he e' he'
  let := hA e he
  exact e.contMDiffOn_principalSection_sdiv e' (hP e he).1 (hP e' he').2

variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace k W']

theorem contMDiff_totalSpace_associatedMap_of_atlas
    (ρ : ContRepresentation k G W) (σ : ContRepresentation k G W')
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) n (fun g => ρ g))
    (hσ : ContMDiff IG 𝓘(k, W' →L[k] W') n (fun g => σ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ∀ e' ∈ A,
      ContMDiffOn I IG n (fun x => e'.principalSection x /ₛ e.principalSection x)
        (e.baseSet ∩ e'.baseSet))
    (f : W → W') (hf : ∀ g w, f (ρ g w) = σ g (f w)) (hfc : ContDiff k n f) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    let := (σ.associatedVectorPrebundle (P := P) hσ.continuous).totalSpaceTopology
    let := σ.associatedFiberBundleOfAtlas hσ.continuous A hA e₀ he₀ hx₀
    let := σ.associated_vector_bundle_of_atlas hσ.continuous A hA e₀ he₀ hx₀
    ContMDiff (I.prod 𝓘(k, W)) (I.prod 𝓘(k, W')) n
      (fun z : TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W) =>
        (⟨z.proj, ρ.toRepresentation.associatedMap σ.toRepresentation f hf z.snd⟩ :
          TotalSpace W' (fun x => P x →ₑ[σ.toRepresentation] W'))) := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_contMDiffVectorBundle_of_atlas I IG n hρ A hA e₀ he₀ hx₀ hP
  let := (σ.associatedVectorPrebundle (P := P) hσ.continuous).totalSpaceTopology
  let := σ.associatedFiberBundleOfAtlas hσ.continuous A hA e₀ he₀ hx₀
  let := σ.associated_vector_bundle_of_atlas hσ.continuous A hA e₀ he₀ hx₀
  let := σ.associated_contMDiffVectorBundle_of_atlas I IG n hσ A hA e₀ he₀ hx₀ hP
  change ContMDiff (I.prod 𝓘(k, W)) (I.prod 𝓘(k, W')) n
    (fun z : TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W) =>
      (⟨z.proj, ρ.toRepresentation.associatedMap σ.toRepresentation f hf z.snd⟩ :
        TotalSpace W' (fun x => P x →ₑ[σ.toRepresentation] W')))
  intro z
  let e := trivializationAt W (fun x => P x →ₑ[ρ.toRepresentation] W) z.proj
  let e' := trivializationAt W' (fun x => P x →ₑ[σ.toRepresentation] W') z.proj
  have hez : z ∈ e.source := hx₀ z.proj
  apply (e'.contMDiffAt_iff (IB := I) (by exact hx₀ z.proj)).mpr
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hcoord := ((e.contMDiffAt_iff (IB := I) (f := id) hez).mp
    (contMDiffAt_id : ContMDiffAt (I.prod 𝓘(k, W)) (I.prod 𝓘(k, W)) n id z)).2
  exact hfc.contMDiff.contMDiffAt.comp z hcoord

theorem contMDiffOn_totalSpace_associatedMap_of_atlas
    {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace k EQ]
    {HQ : Type*} [TopologicalSpace HQ] (IQ : ModelWithCorners k EQ HQ)
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (ρ : ContRepresentation k G W) (σ : ContRepresentation k G W')
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) n (fun g => ρ g))
    (hσ : ContMDiff IG 𝓘(k, W' →L[k] W') n (fun g => σ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ∀ e' ∈ A,
      ContMDiffOn I IG n (fun x => e'.principalSection x /ₛ e.principalSection x)
        (e.baseSet ∩ e'.baseSet))
    (f : Q × W → W') (hf : ∀ q g w, f (q, ρ g w) = σ g (f (q, w)))
    {s : Set Q} (hfc : ContMDiffOn (IQ.prod 𝓘(k, W)) 𝓘(k, W') n f (s ×ˢ univ)) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    let := (σ.associatedVectorPrebundle (P := P) hσ.continuous).totalSpaceTopology
    let := σ.associatedFiberBundleOfAtlas hσ.continuous A hA e₀ he₀ hx₀
    let := σ.associated_vector_bundle_of_atlas hσ.continuous A hA e₀ he₀ hx₀
    ContMDiffOn (IQ.prod (I.prod 𝓘(k, W))) (I.prod 𝓘(k, W')) n
      (fun z : Q × TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W) =>
        (⟨z.2.proj, ρ.toRepresentation.associatedMap σ.toRepresentation
          (fun w => f (z.1, w)) (hf z.1) z.2.snd⟩ :
          TotalSpace W' (fun x => P x →ₑ[σ.toRepresentation] W'))) (s ×ˢ univ) := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_contMDiffVectorBundle_of_atlas I IG n hρ A hA e₀ he₀ hx₀ hP
  let := (σ.associatedVectorPrebundle (P := P) hσ.continuous).totalSpaceTopology
  let := σ.associatedFiberBundleOfAtlas hσ.continuous A hA e₀ he₀ hx₀
  let := σ.associated_vector_bundle_of_atlas hσ.continuous A hA e₀ he₀ hx₀
  let := σ.associated_contMDiffVectorBundle_of_atlas I IG n hσ A hA e₀ he₀ hx₀ hP
  change ContMDiffOn (IQ.prod (I.prod 𝓘(k, W))) (I.prod 𝓘(k, W')) n
    (fun z : Q × TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W) =>
      (⟨z.2.proj, ρ.toRepresentation.associatedMap σ.toRepresentation
        (fun w => f (z.1, w)) (hf z.1) z.2.snd⟩ :
        TotalSpace W' (fun x => P x →ₑ[σ.toRepresentation] W'))) (s ×ˢ univ)
  intro z hz
  let e := trivializationAt W (fun x => P x →ₑ[ρ.toRepresentation] W) z.2.proj
  let e' := trivializationAt W' (fun x => P x →ₑ[σ.toRepresentation] W') z.2.proj
  have hez : z.2 ∈ e.source := hx₀ z.2.proj
  apply (e'.contMDiffWithinAt_iff (IB := I) (by exact hx₀ z.2.proj)).mpr
  refine ⟨?_, ?_⟩
  · change ContMDiffWithinAt (IQ.prod (I.prod 𝓘(k, W))) I n
      (fun y : Q × TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W) => y.2.proj)
      (s ×ˢ univ) z
    exact (contMDiffAt_proj (fun x => P x →ₑ[ρ.toRepresentation] W)).comp_contMDiffWithinAt z
      contMDiffWithinAt_snd
  have hcoord := ((e.contMDiffAt_iff (IB := I) (f := id) hez).mp
    (contMDiffAt_id : ContMDiffAt (I.prod 𝓘(k, W)) (I.prod 𝓘(k, W)) n id z.2)).2
  have hq := hcoord.comp_contMDiffWithinAt z
    (contMDiffWithinAt_snd : ContMDiffWithinAt (IQ.prod (I.prod 𝓘(k, W)))
      (I.prod 𝓘(k, W)) n Prod.snd (s ×ˢ univ) z)
  change ContMDiffWithinAt (IQ.prod (I.prod 𝓘(k, W))) 𝓘(k, W') n
    (fun y : Q × TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W) =>
      f (y.1, (e y.2).2)) (s ×ˢ univ) z
  have hmaps : MapsTo
      (fun y : Q × TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W) =>
        (y.1, (e y.2).2)) (s ×ˢ univ) (s ×ˢ univ) := fun _ hy => ⟨hy.1, mem_univ _⟩
  exact (hfc (z.1, (e z.2).2) ⟨hz.1, mem_univ _⟩).comp z
    (contMDiffWithinAt_fst.prodMk hq) hmaps

theorem exists_contMDiffOn_associatedMap_of_equivariantOn
    {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace k EQ]
    {HQ : Type*} [TopologicalSpace HQ] (IQ : ModelWithCorners k EQ HQ)
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]
    (ρ : ContRepresentation k G W) (σ : ContRepresentation k G W')
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) n (fun g => ρ g))
    (hσ : ContMDiff IG 𝓘(k, W' →L[k] W') n (fun g => σ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ∀ e' ∈ A,
      ContMDiffOn I IG n (fun x => e'.principalSection x /ₛ e.principalSection x)
        (e.baseSet ∩ e'.baseSet))
    {s : Set Q} (f : Q × W → W')
    (hf : ∀ q ∈ s, ∀ g w, f (q, ρ g w) = σ g (f (q, w)))
    (hfc : ContMDiffOn (IQ.prod 𝓘(k, W)) 𝓘(k, W') n f (s ×ˢ univ)) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    let := (σ.associatedVectorPrebundle (P := P) hσ.continuous).totalSpaceTopology
    let := σ.associatedFiberBundleOfAtlas hσ.continuous A hA e₀ he₀ hx₀
    let := σ.associated_vector_bundle_of_atlas hσ.continuous A hA e₀ he₀ hx₀
    ∃ F : Q → ∀ x, (P x →ₑ[ρ.toRepresentation] W) → (P x →ₑ[σ.toRepresentation] W'),
      ContMDiffOn (IQ.prod (I.prod 𝓘(k, W))) (I.prod 𝓘(k, W')) n
        (fun z : Q × TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W) =>
          (⟨z.2.proj, F z.1 z.2.proj z.2.snd⟩ :
            TotalSpace W' (fun x => P x →ₑ[σ.toRepresentation] W'))) (s ×ˢ univ) ∧
      ∀ q ∈ s, ∀ x (v : P x →ₑ[ρ.toRepresentation] W) (p : P x),
        F q x v p = f (q, v p) := by
  classical
  let f₀ : Q × W → W' := fun z => if z.1 ∈ s then f z else 0
  have hf₀ : ∀ q g w, f₀ (q, ρ g w) = σ g (f₀ (q, w)) := by
    intro q g w
    by_cases hq : q ∈ s
    · simpa only [f₀, if_pos hq] using hf q hq g w
    · simp only [f₀, if_neg hq, map_zero]
  have hfc₀ : ContMDiffOn (IQ.prod 𝓘(k, W)) 𝓘(k, W') n f₀ (s ×ˢ univ) := by
    apply hfc.congr
    intro z hz
    exact if_pos hz.1
  refine ⟨fun q x v => ρ.toRepresentation.associatedMap σ.toRepresentation
    (fun w => f₀ (q, w)) (hf₀ q) v, ?_, ?_⟩
  · exact ρ.contMDiffOn_totalSpace_associatedMap_of_atlas I IG n IQ σ hρ hσ
      A hA e₀ he₀ hx₀ hP f₀ hf₀ hfc₀
  · intro q hq x v p
    change f₀ (q, v p) = f (q, v p)
    exact if_pos hq

section Evaluation

variable {EP : Type*} [NormedAddCommGroup EP] [NormedSpace k EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners k EP HP)
  [ChartedSpace HP (TotalSpace G P)]

private theorem contMDiffAt_associated_section_eval
    (ρ : ContRepresentation k G W)
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) n (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) n e e.source)
    (σ : ∀ x, P x →ₑ[ρ.toRepresentation] W) {p : TotalSpace G P} :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    ContMDiffAt I (I.prod 𝓘(k, W)) n
      (fun x => (⟨x, σ x⟩ : TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W))) p.proj →
    ContMDiffAt IP 𝓘(k, W) n (fun q : TotalSpace G P => σ q.proj q.snd) p := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  dsimp only
  intro hσ
  let e := e₀ p.proj
  let := hA e (he₀ p.proj)
  have hp : p ∈ e.source := e.mem_source.mpr (hx₀ p.proj)
  have he : ContMDiffAt IP (I.prod IG) n e p :=
    (hP e (he₀ p.proj)).contMDiffAt (e.open_source.mem_nhds hp)
  have hc : ContMDiffAt I 𝓘(k, W) n (fun x => σ x (e.principalSection x)) p.proj := by
    exact (contMDiffAt_section p.proj).mp hσ
  have hb : ContMDiffAt IP I n (fun q : TotalSpace G P => q.proj) p := by
    apply he.fst.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    exact (e.coe_fst' (e.mem_source.mp hq)).symm
  have ha := (hρ.contMDiffAt.comp p he.snd).clm_apply (hc.comp p hb)
  apply ha.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  have h := map_smulₛₗ (σ q.proj) (q.snd /ₛ e.principalSection q.proj) (e.principalSection q.proj)
  simp only [sdiv_smul, Module.End.smul_def] at h
  rw [e.sdiv_principalSection (e.mem_source.mp hq)] at h
  exact h

private theorem contMDiffAt_associated_section_of_eval
    (ρ : ContRepresentation k G W)
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) n (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn (I.prod IG) IP n e.toOpenPartialHomeomorph.symm e.target)
    (σ : ∀ x, P x →ₑ[ρ.toRepresentation] W) {p : TotalSpace G P} :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    ContMDiffAt IP 𝓘(k, W) n (fun q : TotalSpace G P => σ q.proj q.snd)
      (⟨p.proj, (e₀ p.proj).principalSection p.proj⟩ : TotalSpace G P) →
    ContMDiffAt I (I.prod 𝓘(k, W)) n
      (fun x => (⟨x, σ x⟩ : TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W))) p.proj := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  dsimp only
  intro hσ
  apply (contMDiffAt_section p.proj).mpr
  have he := ((e₀ p.proj).contMDiffOn_principalSection
    (hP (e₀ p.proj) (he₀ p.proj))).contMDiffAt
      ((e₀ p.proj).open_baseSet.mem_nhds (hx₀ p.proj))
  change ContMDiffAt I 𝓘(k, W) n
    (fun x => σ x ((e₀ p.proj).principalSection x)) p.proj
  exact hσ.comp p.proj he

theorem contMDiff_associated_section_iff
    (ρ : ContRepresentation k G W)
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) n (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) n e e.source ∧
      ContMDiffOn (I.prod IG) IP n e.toOpenPartialHomeomorph.symm e.target)
    (σ : ∀ x, P x →ₑ[ρ.toRepresentation] W) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    ContMDiff I (I.prod 𝓘(k, W)) n
      (fun x => (⟨x, σ x⟩ : TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W))) ↔
    ContMDiff IP 𝓘(k, W) n (fun q : TotalSpace G P => σ q.proj q.snd) := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  constructor
  · intro hσ p
    exact ρ.contMDiffAt_associated_section_eval I IG n IP hρ A hA e₀ he₀ hx₀
      (fun e he => (hP e he).1) σ (hσ p.proj)
  · intro hσ x
    exact ρ.contMDiffAt_associated_section_of_eval I IG n IP hρ A hA e₀ he₀ hx₀
      (fun e he => (hP e he).2) σ (p := ⟨x, (e₀ x).principalSection x⟩)
      (hσ ⟨x, (e₀ x).principalSection x⟩)

theorem exists_contMDiff_associated_section_of_equivariant
    (ρ : ContRepresentation k G W)
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) n (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A,
      ContMDiffOn (I.prod IG) IP n e.toOpenPartialHomeomorph.symm e.target)
    (f : TotalSpace G P → W)
    (hf : ∀ x (g : G) (p : P x), f ⟨x, g • p⟩ = ρ g (f ⟨x, p⟩))
    (hfc : ContMDiff IP 𝓘(k, W) n f) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    ∃ σ : ∀ x, P x →ₑ[ρ.toRepresentation] W,
      ContMDiff I (I.prod 𝓘(k, W)) n
        (fun x => (⟨x, σ x⟩ : TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W))) ∧
      ∀ x p, σ x p = f ⟨x, p⟩ := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  let σ : ∀ x, P x →ₑ[ρ.toRepresentation] W := fun x =>
    { toFun := fun p => f ⟨x, p⟩
      map_smul' := fun g p => hf x g p }
  refine ⟨σ, ?_, fun _ _ => rfl⟩
  intro x
  exact ρ.contMDiffAt_associated_section_of_eval I IG n IP hρ A hA e₀ he₀ hx₀ hP σ
    (p := ⟨x, (e₀ x).principalSection x⟩) (hfc ⟨x, (e₀ x).principalSection x⟩)

end Evaluation

end ContRepresentation
