import DifferentialGeometry.Analysis.ODE.InvariantSetEquiv
import DifferentialGeometry.Geometry.Metric.Associated

open Set

noncomputable section

open Bundle

namespace Representation

variable {G B W : Type*} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem isForwardInvariantForODEOn_associatedSet
    (ρ : Representation ℝ G W)
    (horth : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    (P : B → Type*) [∀ x, Torsor G (P x)]
    {J : Set ℝ} {C : Set W} (hC : ∀ g, MapsTo (ρ g) C C)
    (f : ℝ → W → W)
    (F : ℝ → ∀ x, (P x →ₑ[ρ] W) → (P x →ₑ[ρ] W))
    (hF : ∀ t ∈ J, ∀ x (v : P x →ₑ[ρ] W) (p : P x), F t x v p = f t (v p))
    (hinv : DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn f C J) :
    let metric := ρ.associatedRiemannianMetric horth P
    letI : ∀ x, NormedAddCommGroup (P x →ₑ[ρ] W) := fun x =>
      (metric.toCore x).toNormedAddCommGroupOfTopology
        (metric.continuousAt x) (metric.isVonNBounded x)
    letI : ∀ x, InnerProductSpace ℝ (P x →ₑ[ρ] W) := fun x =>
      InnerProductSpace.ofCoreOfTopology (metric.toCore x)
        (metric.continuousAt x) (metric.isVonNBounded x)
    ∀ x, DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn (fun t v => F t x v)
      (ρ.associatedSet (P x) C) J := by
  let metric := ρ.associatedRiemannianMetric horth P
  let : ∀ x, NormedAddCommGroup (P x →ₑ[ρ] W) := fun x =>
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : ∀ x, InnerProductSpace ℝ (P x →ₑ[ρ] W) := fun x =>
    InnerProductSpace.ofCoreOfTopology (metric.toCore x)
      (metric.continuousAt x) (metric.isVonNBounded x)
  dsimp only
  intro x
  let p := Classical.arbitrary (P x)
  let L := (ρ.evalLinearIsometryEquiv horth P x p).toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ∀ t ∈ J, ∀ v, L (F t x v) = f t (L v) := fun t ht v => hF t ht x v p
  have heq : ρ.associatedSet (P x) C = L ⁻¹' C := ρ.associatedSet_eq_preimage hC p
  rw [heq]
  exact hinv.preimage L hL

end Representation

open scoped Manifold ContDiff

namespace ContRepresentation

variable {G B W : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  {P : B → Type*} [∀ x, Torsor G (P x)] [∀ x, TopologicalSpace (P x)]
  [TopologicalSpace (TotalSpace G P)] [FiberBundle G P] [IsPrincipalBundle P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [ChartedSpace H B]
  {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  {HG : Type*} [TopologicalSpace HG] (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G]

theorem exists_contMDiffOn_associatedMap_of_isForwardInvariantForODEOn {n : ℕ∞ω}
    (ρ : ContRepresentation ℝ G W)
    (hρ : ContMDiff IG 𝓘(ℝ, W →L[ℝ] W) n (fun g => ρ g))
    (horth : ∀ g v w, inner ℝ (ρ g v) (ρ g w) = inner ℝ v w)
    (A : Set (Trivialization G (π G P))) (hA : ∀ e ∈ A, MemTrivializationAtlas e)
    (e₀ : B → Trivialization G (π G P)) (he₀ : ∀ x, e₀ x ∈ A)
    (hx₀ : ∀ x, x ∈ (e₀ x).baseSet)
    (hP : ∀ e ∈ A, ∀ e' ∈ A,
      ContMDiffOn I IG n (fun x => e'.principalSection x /ₛ e.principalSection x)
        (e.baseSet ∩ e'.baseSet))
    {J : Set ℝ} {C : Set W} (hC : ∀ g, MapsTo (ρ g) C C)
    (f : ℝ × W → W)
    (hf : ∀ t ∈ J, ∀ g w, f (t, ρ g w) = ρ g (f (t, w)))
    (hfc : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, W)) 𝓘(ℝ, W) n f (J ×ˢ univ))
    (hinv : DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn
      (fun t w => f (t, w)) C J) :
    let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
    let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
    let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
    let metric := ρ.toRepresentation.associatedRiemannianMetric horth P
    letI : ∀ x, NormedAddCommGroup (P x →ₑ[ρ.toRepresentation] W) := fun x =>
      (metric.toCore x).toNormedAddCommGroupOfTopology
        (metric.continuousAt x) (metric.isVonNBounded x)
    letI : ∀ x, InnerProductSpace ℝ (P x →ₑ[ρ.toRepresentation] W) := fun x =>
      InnerProductSpace.ofCoreOfTopology (metric.toCore x)
        (metric.continuousAt x) (metric.isVonNBounded x)
    ∃ F : ℝ → ∀ x, (P x →ₑ[ρ.toRepresentation] W) → (P x →ₑ[ρ.toRepresentation] W),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (I.prod 𝓘(ℝ, W))) (I.prod 𝓘(ℝ, W)) n
        (fun z : ℝ × TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W) =>
          (⟨z.2.proj, F z.1 z.2.proj z.2.snd⟩ :
            TotalSpace W (fun x => P x →ₑ[ρ.toRepresentation] W))) (J ×ˢ univ) ∧
      (∀ t ∈ J, ∀ x (v : P x →ₑ[ρ.toRepresentation] W) (p : P x), F t x v p = f (t, v p)) ∧
      ∀ x, DifferentialGeometry.Analysis.ODE.IsForwardInvariantForODEOn (fun t v => F t x v)
        (ρ.toRepresentation.associatedSet (P x) C) J := by
  let := (ρ.associatedVectorPrebundle (P := P) hρ.continuous).totalSpaceTopology
  let := ρ.associatedFiberBundleOfAtlas hρ.continuous A hA e₀ he₀ hx₀
  let := ρ.associated_vector_bundle_of_atlas hρ.continuous A hA e₀ he₀ hx₀
  let metric := ρ.toRepresentation.associatedRiemannianMetric horth P
  let : ∀ x, NormedAddCommGroup (P x →ₑ[ρ.toRepresentation] W) := fun x =>
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : ∀ x, InnerProductSpace ℝ (P x →ₑ[ρ.toRepresentation] W) := fun x =>
    InnerProductSpace.ofCoreOfTopology (metric.toCore x)
      (metric.continuousAt x) (metric.isVonNBounded x)
  dsimp only
  obtain ⟨F, hFs, hFe⟩ := ρ.exists_contMDiffOn_associatedMap_of_equivariantOn I IG n 𝓘(ℝ, ℝ)
    ρ hρ hρ A hA e₀ he₀ hx₀ hP f hf hfc
  refine ⟨F, hFs, hFe, ?_⟩
  exact ρ.toRepresentation.isForwardInvariantForODEOn_associatedSet horth P hC
    (fun t w => f (t, w)) F hFe hinv

end ContRepresentation
