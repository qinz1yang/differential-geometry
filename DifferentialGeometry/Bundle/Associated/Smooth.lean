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

end ContRepresentation
