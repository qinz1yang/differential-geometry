import DifferentialGeometry.Geometry.Connection.Principal
import DifferentialGeometry.Bundle.Associated.Smooth
import DifferentialGeometry.Bundle.Hom.Regularity
import DifferentialGeometry.Topology.GroupAction.Module
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

noncomputable section

open Set Bundle
open scoped Manifold ContDiff Bundle

namespace ContRepresentation

variable {k G B W : Type*} [NontriviallyNormedField k] [Group G]
  [TopologicalSpace G] [TopologicalSpace B] [NormedAddCommGroup W] [NormedSpace k W]
  {P : B → Type*} [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P] [IsPrincipalBundle P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners k E H) [ChartedSpace H B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace k EG]
  {HG : Type*} [TopologicalSpace HG] (IG : ModelWithCorners k EG HG) [ChartedSpace HG G]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace k EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners k EP HP)
  [ChartedSpace HP (TotalSpace G P)]

def associatedCovariantDerivativeOfLocalSections
    (ρ : ContRepresentation k G W) (hρ : Continuous (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (form : ∀ p : TotalSpace G P, TangentSpace IP p →L[k] GroupLieAlgebra IG G) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ A hA e₀ he₀ hx₀
    CovariantDerivative I W (fun x => P x →ₑ[ρ.toRepresentation] W) := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ A hA e₀ he₀ hx₀
  let s (x : B) (y : B) : TotalSpace G P := ⟨y, (e₀ x).principalSection y⟩
  let a (x : B) : TangentSpace I x →L[k] W →L[k] W :=
    (mvfderiv IG (fun g => ρ g) 1).comp ((form (s x x)).comp (mfderiv I IP (s x) x))
  let ev (x : B) := ρ.toRepresentation.evalContinuousLinearEquiv (fun g => (ρ g).continuous)
    ((e₀ x).principalSection x)
  let coords (σ : ∀ x, P x →ₑ[ρ.toRepresentation] W) (x : B) (y : B) : W :=
    σ y ((e₀ x).principalSection y)
  let D (σ : ∀ x, P x →ₑ[ρ.toRepresentation] W) (x : B) :
      TangentSpace I x →L[k] W :=
    mvfderiv I (coords σ x) x - (ContinuousLinearMap.apply k W (coords σ x x)).comp (a x)
  have hcoords {σ : ∀ x, P x →ₑ[ρ.toRepresentation] W} {x : B}
      (hσ : MDifferentiableAt I (I.prod 𝓘(k, W))
        (fun y => (⟨y, σ y⟩ : TotalSpace W (fun z => P z →ₑ[ρ.toRepresentation] W))) x) :
      MDifferentiableAt I 𝓘(k, W) (coords σ x) x := by
    exact (mdifferentiableAt_section I σ).mp hσ
  refine ⟨fun σ x => (ev x).symm.toContinuousLinearMap.comp (D σ x), ?_⟩
  constructor
  · intro σ τ x hσ hτ hx
    have hσ' := hcoords hσ
    have hτ' := hcoords hτ
    have hadd : coords (σ + τ) x = coords σ x + coords τ x := rfl
    apply ContinuousLinearMap.ext
    intro X
    simp only [ContinuousLinearMap.comp_apply, D, hadd, mvfderiv_add hσ' hτ',
      sub_apply, add_apply, ContinuousLinearMap.apply_apply]
    change (ev x).symm (mvfderiv I (coords σ x) x X + mvfderiv I (coords τ x) x X -
      a x X (coords σ x x + coords τ x x)) =
        (ev x).symm (mvfderiv I (coords σ x) x X - a x X (coords σ x x)) +
        (ev x).symm (mvfderiv I (coords τ x) x X - a x X (coords τ x x))
    rw [(a x X).map_add, ← (ev x).symm.map_add]
    congr 1
    abel
  · intro σ g x hσ hg hx
    have hσ' := hcoords hσ
    have hsmul : coords (g • σ) x = g • coords σ x := rfl
    apply ContinuousLinearMap.ext
    intro X
    simp only [ContinuousLinearMap.comp_apply, D, hsmul, mvfderiv_smul hg hσ',
      sub_apply, add_apply, smul_apply, ContinuousLinearMap.apply_apply,
      ContinuousLinearMap.smulRight_apply]
    change (ev x).symm (g x • mvfderiv I (coords σ x) x X +
      mvfderiv I g x X • coords σ x x - a x X (g x • coords σ x x)) = _
    rw [map_smul]
    have heq : g x • mvfderiv I (coords σ x) x X +
        mvfderiv I g x X • coords σ x x - g x • a x X (coords σ x x) =
        g x • (mvfderiv I (coords σ x) x X - a x X (coords σ x x)) +
          mvfderiv I g x X • coords σ x x := by
      rw [smul_sub]
      abel
    rw [heq, map_add, map_smul, map_smul]
    congr 1
    change mvfderiv I g x X • ((ev x).symm (ev x (σ x))) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]

theorem associatedCovariantDerivativeOfLocalSections_apply
    (ρ : ContRepresentation k G W) (hρ : Continuous (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (form : ∀ p : TotalSpace G P, TangentSpace IP p →L[k] GroupLieAlgebra IG G)
    (σ : ∀ x, P x →ₑ[ρ.toRepresentation] W) (x : B) (X : TangentSpace I x) (p : P x) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ A hA e₀ he₀ hx₀
    (ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ A hA e₀ he₀ hx₀ form σ x X) p =
      ρ (p /ₛ (e₀ x).principalSection x)
        (mvfderiv I (fun y => σ y ((e₀ x).principalSection y)) x X -
          mvfderiv IG (fun g => ρ g) 1
            (form ⟨x, (e₀ x).principalSection x⟩
              (mfderiv I IP (fun y => (⟨y, (e₀ x).principalSection y⟩ : TotalSpace G P)) x X))
            (σ x ((e₀ x).principalSection x))) := rfl

end ContRepresentation
namespace ContRepresentation

variable {k G B W : Type*} [NontriviallyNormedField k] [Group G]
  [TopologicalSpace G] [TopologicalSpace B] [NormedAddCommGroup W] [NormedSpace k W]
  {P : B → Type*} [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P] [IsPrincipalBundle P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners k E H) [ChartedSpace H B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace k EG]
  {HG : Type*} [TopologicalSpace HG] (IG : ModelWithCorners k EG HG) [ChartedSpace HG G]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace k EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners k EP HP)
  [ChartedSpace HP (TotalSpace G P)]

private theorem mdifferentiableAt_associated_section_eval
    (ρ : ContRepresentation k G W)
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) 1 (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) 1 e e.source)
    (σ : ∀ x, P x →ₑ[ρ.toRepresentation] W) {p : TotalSpace G P} :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    MDifferentiableAt I (I.prod 𝓘(k, W))
      (fun x => (⟨x, σ x⟩ : TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W))) p.proj →
    MDifferentiableAt IP 𝓘(k, W) (fun q : TotalSpace G P => σ q.proj q.snd) p := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  dsimp only
  intro hσ
  let e := e₀ p.proj
  let := hA e (he₀ p.proj)
  have hp : p ∈ e.source := e.mem_source.mpr (hx₀ p.proj)
  have he : MDifferentiableAt IP (I.prod IG) e p :=
    ((hP e (he₀ p.proj)).contMDiffAt (e.open_source.mem_nhds hp)).mdifferentiableAt (by simp)
  have hc : MDifferentiableAt I 𝓘(k, W) (fun x => σ x (e.principalSection x)) p.proj := by
    exact (mdifferentiableAt_section I σ).mp hσ
  have hb : MDifferentiableAt IP I (fun q : TotalSpace G P => q.proj) p := by
    apply he.fst.congr_of_eventuallyEq
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    exact (e.coe_fst' (e.mem_source.mp hq)).symm
  have ha := ((hρ.contMDiffAt.mdifferentiableAt (by simp)).comp p he.snd).clm_apply (hc.comp p hb)
  apply ha.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hp] with q hq
  have h := map_smulₛₗ (σ q.proj) (q.snd /ₛ e.principalSection q.proj) (e.principalSection q.proj)
  simp only [sdiv_smul, Module.End.smul_def] at h
  rw [e.sdiv_principalSection (e.mem_source.mp hq)] at h
  exact h


private theorem covariantDifferential_principalSection [ContMDiffMul IG 1 G]
    (ρ : ContRepresentation k G W)
    (hρ : MDifferentiableAt IG 𝓘(k, W →L[k] W) (fun g => ρ g) 1)
    [ContMDiffSMul IG IP 1 G (TotalSpace G P)]
    (form : ∀ p : TotalSpace G P, TangentSpace IP p →L[k] GroupLieAlgebra IG G)
    (hform : ∀ (g : G) (p : TotalSpace G P) (X : TangentSpace IP p),
      form (g • p) (mfderiv IP IP (fun q => g • q) p X) =
        mfderiv IG IG (fun h => g * h * g⁻¹) 1 (form p X))
    (e e' : Trivialization G (π G P)) [MemTrivializationAtlas e]
    (he : ContMDiffOn IP (I.prod IG) 1 e e.source)
    (hei : ContMDiffOn (I.prod IG) IP 1 e.toOpenPartialHomeomorph.symm e.target)
    (he'i : ContMDiffOn (I.prod IG) IP 1 e'.toOpenPartialHomeomorph.symm e'.target)
    {x : B} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet)
    {f : TotalSpace G P → W} (heq : ∀ g p, f (g • p) = ρ g (f p))
    (hf : MDifferentiableAt IP 𝓘(k, W) f ⟨x, e.principalSection x⟩)
    (hnorm : ∀ U : GroupLieAlgebra IG G,
      form ⟨x, e.principalSection x⟩
        (mfderiv IG IP (fun g : G => g • (⟨x, e.principalSection x⟩ : TotalSpace G P)) 1 U) = U)
    (X : TangentSpace I x) :
    ρ.covariantDifferential form f ⟨x, e'.principalSection x⟩
      (mfderiv I IP (fun y => (⟨y, e'.principalSection y⟩ : TotalSpace G P)) x X) =
      ρ (e'.principalSection x /ₛ e.principalSection x)
        (ρ.covariantDifferential form f ⟨x, e.principalSection x⟩
          (mfderiv I IP (fun y => (⟨y, e.principalSection y⟩ : TotalSpace G P)) x X)) := by
  let s : B → TotalSpace G P := fun y => ⟨y, e.principalSection y⟩
  let a : B → G := fun y => e'.principalSection y /ₛ e.principalSection y
  have hs : MDifferentiableAt I IP s x :=
    ((e.contMDiffOn_principalSection hei).contMDiffAt (e.open_baseSet.mem_nhds hx)).mdifferentiableAt
      (by simp)
  have ha : MDifferentiableAt I IG a x :=
    ((e.contMDiffOn_principalSection_sdiv e' he he'i).contMDiffAt
      ((e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨hx, hx'⟩)).mdifferentiableAt (by simp)
  have hh := ρ.covariantDifferential_smul_comp (IQ := I) (s := s) (a := a) (x := x)
    hρ form hform heq hf hs ha hnorm X
  have hequal : (fun y => a y • s y) =
      fun y => (⟨y, e'.principalSection y⟩ : TotalSpace G P) := by
    funext y
    change (⟨y, (e'.principalSection y /ₛ e.principalSection y) • e.principalSection y⟩ :
      TotalSpace G P) = _
    rw [sdiv_smul]
  have hpoint : ρ.covariantDifferential form f (a x • s x) =
      ρ.covariantDifferential form f ⟨x, e'.principalSection x⟩ := by
    unfold TangentSpace covariantDifferential
    rw [congrFun hequal x]
  have hd : mfderiv I IP (fun y => a y • s y) x =
      mfderiv I IP (fun y => (⟨y, e'.principalSection y⟩ : TotalSpace G P)) x := by
    rw [hequal]
  have hpoint' := congrArg (fun L => L (mfderiv I IP (fun y => a y • s y) x X)) hpoint
  have hd' := congrArg (fun L => L X) hd
  exact ((congrArg (ρ.covariantDifferential form f ⟨x, e'.principalSection x⟩) hd').symm.trans
    hpoint'.symm).trans hh

theorem associatedCovariantDerivativeOfLocalSections_eval_principalSection [ContMDiffMul IG 1 G]
    (ρ : ContRepresentation k G W)
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) 1 (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) 1 e e.source ∧
      ContMDiffOn (I.prod IG) IP 1 e.toOpenPartialHomeomorph.symm e.target)
    (form : ∀ p : TotalSpace G P, TangentSpace IP p →L[k] GroupLieAlgebra IG G)
    (hform : ∀ (g : G) (p : TotalSpace G P) (X : TangentSpace IP p),
      form (g • p) (mfderiv IP IP (fun q => g • q) p X) =
        mfderiv IG IG (fun h => g * h * g⁻¹) 1 (form p X))
    (hnorm : ∀ (p : TotalSpace G P) (U : GroupLieAlgebra IG G),
      form p (mfderiv IG IP (fun g : G => g • p) 1 U) = U)
    (σ : ∀ x, P x →ₑ[ρ.toRepresentation] W)
    (e : Trivialization G (π G P)) (he : e ∈ A) {x : B} (hx : x ∈ e.baseSet)
    (X : TangentSpace I x) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    MDifferentiableAt I (I.prod 𝓘(k, W))
      (fun y => (⟨y, σ y⟩ : TotalSpace W (fun z => P z →ₑ[ρ.toRepresentation] W))) x →
    (ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form
      σ x X) (e.principalSection x) =
      ρ.covariantDifferential form (fun p : TotalSpace G P => σ p.proj p.snd)
        ⟨x, e.principalSection x⟩
        (mfderiv I IP (fun y => (⟨y, e.principalSection y⟩ : TotalSpace G P)) x X) := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  let := Bundle.contMDiffSMul_of_principal_atlas I IG IP A hA e₀ he₀ hx₀ hP
  dsimp only
  intro hσ
  let e' := e₀ x
  let := hA e' (he₀ x)
  let f : TotalSpace G P → W := fun p => σ p.proj p.snd
  let s : B → TotalSpace G P := fun y => ⟨y, e'.principalSection y⟩
  have heq : ∀ (g : G) (p : TotalSpace G P), f (g • p) = ρ g (f p) := by
    intro g p
    exact map_smulₛₗ (σ p.proj) g p.snd
  have hf : MDifferentiableAt IP 𝓘(k, W) f (s x) :=
    ρ.mdifferentiableAt_associated_section_eval I IG IP hρ A hA e₀ he₀ hx₀
      (fun q hq => (hP q hq).1) σ (p := s x) hσ
  have hs : MDifferentiableAt I IP s x :=
    ((e'.contMDiffOn_principalSection (hP e' (he₀ x)).2).contMDiffAt
      (e'.open_baseSet.mem_nhds (hx₀ x))).mdifferentiableAt (by simp)
  have hcomp := hf.mvfderiv_comp_apply hs X
  have hc := ρ.covariantDifferential_principalSection I IG IP
    (hρ.contMDiffAt.mdifferentiableAt (by simp)) form hform e' e
    (hP e' (he₀ x)).1 (hP e' (he₀ x)).2 (hP e he).2 (hx₀ x) hx heq hf (hnorm (s x)) X
  rw [ρ.associatedCovariantDerivativeOfLocalSections_apply]
  refine (congrArg (ρ (e.principalSection x /ₛ e'.principalSection x)) ?_).trans hc.symm
  change mvfderiv I (f ∘ s) x X -
    mvfderiv IG (fun g => ρ g) 1 (form (s x) (mfderiv I IP s x X)) (f (s x)) =
      ρ.covariantDifferential form f (s x) (mfderiv I IP s x X)
  rw [ρ.covariantDifferential_apply, hcomp]

theorem associatedCovariantDerivativeOfLocalSections_eq [ContMDiffMul IG 1 G]
    (ρ : ContRepresentation k G W)
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) 1 (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (e₁ : B → Trivialization G (π G P)) (he₁ : ∀ x, e₁ x ∈ A)
    (hx₁ : ∀ x, x ∈ (e₁ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) 1 e e.source ∧
      ContMDiffOn (I.prod IG) IP 1 e.toOpenPartialHomeomorph.symm e.target)
    (form : ∀ p : TotalSpace G P, TangentSpace IP p →L[k] GroupLieAlgebra IG G)
    (hform : ∀ (g : G) (p : TotalSpace G P) (X : TangentSpace IP p),
      form (g • p) (mfderiv IP IP (fun q => g • q) p X) =
        mfderiv IG IG (fun h => g * h * g⁻¹) 1 (form p X))
    (hnorm : ∀ (p : TotalSpace G P) (U : GroupLieAlgebra IG G),
      form p (mfderiv IG IP (fun g : G => g • p) 1 U) = U)
    (σ : ∀ x, P x →ₑ[ρ.toRepresentation] W) (x : B) (X : TangentSpace I x) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    MDifferentiableAt I (I.prod 𝓘(k, W))
      (fun y => (⟨y, σ y⟩ : TotalSpace W (fun z => P z →ₑ[ρ.toRepresentation] W))) x →
    ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form
      σ x X =
      ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₁ he₁ hx₁ form
        σ x X := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  dsimp only
  intro hσ
  let e := e₁ x
  let := hA e (he₁ x)
  let f : TotalSpace G P → W := fun p => σ p.proj p.snd
  let s : B → TotalSpace G P := fun y => ⟨y, e.principalSection y⟩
  have hf : MDifferentiableAt IP 𝓘(k, W) f (s x) :=
    ρ.mdifferentiableAt_associated_section_eval I IG IP hρ A hA e₀ he₀ hx₀
      (fun q hq => (hP q hq).1) σ (p := s x) hσ
  have hs : MDifferentiableAt I IP s x :=
    ((e.contMDiffOn_principalSection (hP e (he₁ x)).2).contMDiffAt
      (e.open_baseSet.mem_nhds (hx₁ x))).mdifferentiableAt (by simp)
  have hcomp := hf.mvfderiv_comp_apply hs X
  apply (ρ.toRepresentation.evalContinuousLinearEquiv (fun g => (ρ g).continuous)
    (e.principalSection x)).injective
  change
    (ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form
      σ x X) (e.principalSection x) =
    (ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₁ he₁ hx₁ form
      σ x X) (e.principalSection x)
  rw [ρ.associatedCovariantDerivativeOfLocalSections_eval_principalSection I IG IP hρ A hA
    e₀ he₀ hx₀ hP form hform hnorm σ e (he₁ x) (hx₁ x) X hσ]
  rw [ρ.associatedCovariantDerivativeOfLocalSections_apply]
  simp only [e, sdiv_self, map_one, one_apply_eq_self]
  change ρ.covariantDifferential form f (s x) (mfderiv I IP s x X) =
    mvfderiv I (f ∘ s) x X -
      mvfderiv IG (fun g => ρ g) 1 (form (s x) (mfderiv I IP s x X)) (f (s x))
  rw [ρ.covariantDifferential_apply, hcomp]

theorem contMDiff_associatedCovariantDerivativeOfLocalSections
    {n : ℕ∞ω} [CompleteSpace k] [FiniteDimensional k E] [IsManifold I (n + 1) B]
    [IsManifold IP (n + 1) (TotalSpace G P)] [ContMDiffMul IG (n + 1) G]
    (ρ : ContRepresentation k G W)
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) (n + 1) (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) (n + 1) e e.source ∧
      ContMDiffOn (I.prod IG) IP (n + 1) e.toOpenPartialHomeomorph.symm e.target)
    (form : ∀ p : TotalSpace G P, TangentSpace IP p →L[k] GroupLieAlgebra IG G)
    (hform : ∀ (g : G) (p : TotalSpace G P) (X : TangentSpace IP p),
      form (g • p) (mfderiv IP IP (fun q => g • q) p X) =
        mfderiv IG IG (fun h => g * h * g⁻¹) 1 (form p X))
    (hnorm : ∀ (p : TotalSpace G P) (U : GroupLieAlgebra IG G),
      form p (mfderiv IG IP (fun g : G => g • p) 1 U) = U) :
    letI : IsManifold I 1 B := IsManifold.of_le (n := n + 1) le_add_self
    letI : IsManifold IP 1 (TotalSpace G P) := IsManifold.of_le (n := n + 1) le_add_self
    ContMDiff (M' := EG) IP.tangent 𝓘(k, EG) n
      (fun z : TangentBundle IP (TotalSpace G P) => (form z.proj z.snd : EG)) →
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    CovariantDerivative.ContMDiffCovariantDerivative
      (ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form) n := by
  let : IsManifold I 1 B := IsManifold.of_le (n := n + 1) le_add_self
  let : IsManifold IP 1 (TotalSpace G P) := IsManifold.of_le (n := n + 1) le_add_self
  dsimp only
  intro hforms
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := B) (n := n)
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_contMDiffVectorBundle_of_smooth_atlas I IG (n + 1) IP hρ A hA e₀ he₀ hx₀ hP
  let := Bundle.contMDiffSMul_of_principal_atlas I IG IP A hA e₀ he₀ hx₀ hP
  let cov := ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ.continuous A hA e₀ he₀ hx₀ form
  let : ContMDiffMul IG 1 G := ContMDiffMul.of_le (show 1 ≤ n + 1 from le_add_self)
  constructor
  constructor
  intro σ hσ
  rw [contMDiffOn_univ] at hσ ⊢
  have hσs : ContMDiff I (I.prod 𝓘(k, W)) (n + 1)
      (fun x => (⟨x, σ x⟩ : TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W))) := hσ
  let f : TotalSpace G P → W := fun p => σ p.proj p.snd
  have hf : ContMDiff IP 𝓘(k, W) (n + 1) f :=
    (ρ.contMDiff_associated_section_iff I IG (n + 1) IP hρ A hA e₀ he₀ hx₀ hP σ).mp hσs
  have hD := ρ.contMDiff_covariantDifferential form (m := n) le_rfl hforms hf
  have hmap : ContMDiff I.tangent (I.prod 𝓘(k, W)) n
      (fun z : TangentBundle I B => (⟨z.proj, cov σ z.proj z.snd⟩ :
        TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W))) := by
    intro z
    let e := e₀ z.proj
    let s : B → TotalSpace G P := fun x => ⟨x, e.principalSection x⟩
    have hs : ContMDiffOn I IP (n + 1) s e.baseSet :=
      e.contMDiffOn_principalSection (hP e (he₀ z.proj)).2
    have ht := hs.contMDiffOn_tangentMapWithin (m := n) le_rfl e.open_baseSet.uniqueMDiffOn
    have hopen : IsOpen ((TotalSpace.proj : TangentBundle I B → B) ⁻¹' e.baseSet) :=
      e.open_baseSet.preimage (FiberBundle.continuous_proj E (TangentSpace I))
    have hz : z ∈ (TotalSpace.proj : TangentBundle I B → B) ⁻¹' e.baseSet := hx₀ z.proj
    have ht' : ContMDiffAt I.tangent IP.tangent n (tangentMap I IP s) z := by
      apply (ht.contMDiffAt (hopen.mem_nhds hz)).congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds hz] with y hy
      unfold tangentMap tangentMapWithin
      rw [mfderivWithin_of_mem_nhds (e.open_baseSet.mem_nhds hy)]
    have hc := (hD _).comp z ht'
    rw [contMDiffAt_totalSpace]
    refine ⟨contMDiffAt_proj (TangentSpace I), ?_⟩
    apply hc.congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hz] with y hy
    change (cov σ y.proj y.snd) (e.principalSection y.proj) =
      ρ.covariantDifferential form f (s y.proj) (mfderiv I IP s y.proj y.snd)
    exact ρ.associatedCovariantDerivativeOfLocalSections_eval_principalSection I IG IP
      (hρ.of_le (show 1 ≤ n + 1 from le_add_self)) A hA e₀ he₀ hx₀
      (fun q hq => ⟨(hP q hq).1.of_le (show 1 ≤ n + 1 from le_add_self),
        (hP q hq).2.of_le (show 1 ≤ n + 1 from le_add_self)⟩)
      form hform hnorm σ e (he₀ z.proj) hy y.snd ((hσs y.proj).mdifferentiableAt (by simp))
  exact hmap.clm_bundle_of_map

def associatedCovariantDerivative [IsManifold IP 1 (TotalSpace G P)] {n : ℕ∞ω}
    (ρ : ContRepresentation k G W) (hρ : Continuous (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (form : PrincipalConnectionForm IG G IP P n) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ A hA e₀ he₀ hx₀
    CovariantDerivative I W (fun x => P x →ₑ[ρ.toRepresentation] W) :=
  ρ.associatedCovariantDerivativeOfLocalSections I IG IP hρ A hA e₀ he₀ hx₀ form.toFun

theorem associatedCovariantDerivative_eval_principalSection [ContMDiffMul IG 1 G]
    [IsManifold IP 1 (TotalSpace G P)] {n : ℕ∞ω}
    (ρ : ContRepresentation k G W)
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) 1 (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) 1 e e.source ∧
      ContMDiffOn (I.prod IG) IP 1 e.toOpenPartialHomeomorph.symm e.target)
    (form : PrincipalConnectionForm IG G IP P n)
    (σ : ∀ x, P x →ₑ[ρ.toRepresentation] W)
    (e : Trivialization G (π G P)) (he : e ∈ A) {x : B} (hx : x ∈ e.baseSet)
    (X : TangentSpace I x) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    MDifferentiableAt I (I.prod 𝓘(k, W))
      (fun y => (⟨y, σ y⟩ : TotalSpace W (fun z => P z →ₑ[ρ.toRepresentation] W))) x →
    (ρ.associatedCovariantDerivative I IG IP hρ.continuous A hA e₀ he₀ hx₀ form
      σ x X) (e.principalSection x) =
      ρ.covariantDifferential form.toFun (fun p : TotalSpace G P => σ p.proj p.snd)
        ⟨x, e.principalSection x⟩
        (mfderiv I IP (fun y => (⟨y, e.principalSection y⟩ : TotalSpace G P)) x X) :=
  ρ.associatedCovariantDerivativeOfLocalSections_eval_principalSection I IG IP hρ A hA e₀ he₀ hx₀ hP
    form.toFun form.apply_smul form.apply_fundamental σ e he hx X

theorem associatedCovariantDerivative_eq [ContMDiffMul IG 1 G]
    [IsManifold IP 1 (TotalSpace G P)] {n : ℕ∞ω}
    (ρ : ContRepresentation k G W)
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) 1 (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (e₁ : B → Trivialization G (π G P)) (he₁ : ∀ x, e₁ x ∈ A)
    (hx₁ : ∀ x, x ∈ (e₁ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) 1 e e.source ∧
      ContMDiffOn (I.prod IG) IP 1 e.toOpenPartialHomeomorph.symm e.target)
    (form : PrincipalConnectionForm IG G IP P n)
    (σ : ∀ x, P x →ₑ[ρ.toRepresentation] W) (x : B) (X : TangentSpace I x) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    MDifferentiableAt I (I.prod 𝓘(k, W))
      (fun y => (⟨y, σ y⟩ : TotalSpace W (fun z => P z →ₑ[ρ.toRepresentation] W))) x →
    ρ.associatedCovariantDerivative I IG IP hρ.continuous A hA e₀ he₀ hx₀ form σ x X =
      ρ.associatedCovariantDerivative I IG IP hρ.continuous A hA e₁ he₁ hx₁ form σ x X :=
  ρ.associatedCovariantDerivativeOfLocalSections_eq I IG IP hρ A hA e₀ he₀ hx₀ e₁ he₁ hx₁ hP
    form.toFun form.apply_smul form.apply_fundamental σ x X

theorem contMDiff_associatedCovariantDerivative
    {n : ℕ∞ω} [CompleteSpace k] [FiniteDimensional k E] [IsManifold I (n + 1) B]
    [IsManifold IP (n + 1) (TotalSpace G P)] [ContMDiffMul IG (n + 1) G]
    (ρ : ContRepresentation k G W)
    (hρ : ContMDiff IG 𝓘(k, W →L[k] W) (n + 1) (fun g => ρ g))
    (A : Set (Trivialization G (π G P)))
    (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ContMDiffOn IP (I.prod IG) (n + 1) e e.source ∧
      ContMDiffOn (I.prod IG) IP (n + 1) e.toOpenPartialHomeomorph.symm e.target) :
    letI : IsManifold I 1 B := IsManifold.of_le (n := n + 1) le_add_self
    letI : IsManifold IP 1 (TotalSpace G P) := IsManifold.of_le (n := n + 1) le_add_self
    (form : PrincipalConnectionForm IG G IP P n) →
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    CovariantDerivative.ContMDiffCovariantDerivative
      (ρ.associatedCovariantDerivative I IG IP hρ.continuous A hA e₀ he₀ hx₀ form) n := by
  let : IsManifold I 1 B := IsManifold.of_le (n := n + 1) le_add_self
  let : IsManifold IP 1 (TotalSpace G P) := IsManifold.of_le (n := n + 1) le_add_self
  dsimp only
  intro form
  exact ρ.contMDiff_associatedCovariantDerivativeOfLocalSections I IG IP hρ A hA e₀ he₀ hx₀ hP
    form.toFun form.apply_smul form.apply_fundamental form.contMDiff

end ContRepresentation
