/-
Copyright © 2023 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
Coauthors: Jack McCarthy
-/
import DifferentialGeometry.Tensor.Alternating.Composition
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Data.Bundle

noncomputable section

open Bundle Set ContinuousAlternatingMap

section defs

variable (𝕜 : Type*) [CommSemiring 𝕜] (ι : Type*) [Fintype ι]
variable {B : Type*}

protected abbrev Bundle.continuousAlternatingMap (_F₁ : Type*) (E₁ : B → Type*)
    [∀ x, AddCommMonoid (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
    (_F₂ : Type*) (E₂ : B → Type*) [∀ x, AddCommMonoid (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
    [∀ x, TopologicalSpace (E₂ x)] (x : B) : Type _ :=
  E₁ x [⋀^ι]→L[𝕜] E₂ x

notation3 "⋀^" ι "⟮" 𝕜 "; " F₁ ", " E₁ "; " F₂ ", " E₂ "⟯" =>
  Bundle.continuousAlternatingMap 𝕜 ι F₁ E₁ F₂ E₂

end defs

section smooth

open scoped Bundle Manifold

open Bundle Pretrivialization

variable {𝕜 ι B F₁ F₂ M : Type*} {E₁ : B → Type*} {E₂ : B → Type*}
  [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  [Fintype ι]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB]
  (IB : ModelWithCorners 𝕜 EB HB)
  [TopologicalSpace B] [ChartedSpace HB B]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (Bundle.TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜 (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (Bundle.TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM}
  [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M] {n : ℕ∞}
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

variable {F₃ F₄ : Type*}
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [NormedAddCommGroup F₄] [NormedSpace 𝕜 F₄]

local notation "AE₁E₂" =>
  Bundle.TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯

omit [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)] in
theorem contMDiffOn_continuousAlternatingMapCoordChange
    [ContMDiffVectorBundle ⊤ F₁ E₁ IB] [ContMDiffVectorBundle ⊤ F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(𝕜, (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^ι]→L[𝕜] F₂) ⊤
      (continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := ⊤)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := ⊤)
  have h₁_prod_h₂ := (h₁.mono (t := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
    (s := e₁'.baseSet ∩ e₁.baseSet) (by mfld_set_tac)).prodMk
      (h₂.mono (t := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet))
      (s := e₂.baseSet ∩ e₂'.baseSet) (by mfld_set_tac))
  let s (q : (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂)) :
      (F₁ →L[𝕜] F₁) × ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)) :=
    (q.1, ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂ ι q.2)
  have hs : ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁)).prod 𝓘(𝕜, (F₂ →L[𝕜] F₂)))
      (𝓘(𝕜, (F₁ →L[𝕜] F₁)).prod
        𝓘(𝕜, ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂)))) ⊤ s := by
    let t (p : (F₁ →L[𝕜] F₁) × (F₂ →L[𝕜] F₂)) :
        (F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂) :=
      ContinuousLinearMap.compContinuousAlternatingMapCLM 𝕜 F₁ F₂ F₂ ι p.2
    have ht : ContMDiff (𝓘(𝕜, (F₁ →L[𝕜] F₁)).prod 𝓘(𝕜, (F₂ →L[𝕜] F₂)))
        𝓘(𝕜, ((F₁ [⋀^ι]→L[𝕜] F₂) →L[𝕜] (F₁ [⋀^ι]→L[𝕜] F₂))) ⊤ t := by
      refine ContMDiff.clm_apply ?hg ?hf
      · exact contMDiff_const
      · exact contMDiff_snd
    exact ContMDiff.prodMk contMDiff_fst ht
  exact ((contMDiff_snd.clm_comp ((ContinuousAlternatingMap.compContinuousLinearMapCLM_contMDiff
    (𝕜 := 𝕜) (ι := ι) (F₁ := F₁) (F₂ := F₂)).comp contMDiff_fst)).comp hs).comp_contMDiffOn
    (s := e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) h₁_prod_h₂

variable [ContMDiffVectorBundle ⊤ F₁ E₁ IB] [ContMDiffVectorBundle ⊤ F₂ E₂ IB]

instance Bundle.continuousAlternatingMap.vectorPrebundle.isSmooth :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).IsContMDiff IB ⊤ where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    refine ⟨continuousAlternatingMapCoordChange 𝕜 ι e₁ e₁' e₂ e₂',
      contMDiffOn_continuousAlternatingMapCoordChange IB, ?_⟩
    rintro b hb v
    apply continuousAlternatingMapCoordChange_apply
    exact hb

instance SmoothVectorBundle.continuousAlternatingMap :
    ContMDiffVectorBundle ⊤ (F₁ [⋀^ι]→L[𝕜] F₂)
      (Bundle.continuousAlternatingMap 𝕜 ι F₁ E₁ F₂ E₂) IB :=
  (Bundle.ContinuousAlternatingMap.vectorPrebundle 𝕜 ι F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

notation "𝒜⟮" 𝕜 "," ι ";" F₁ "," E₁ ";" F₂ "," E₂ "⟯" =>
  Bundle.TotalSpace (F₁ [⋀^ι]→L[𝕜] F₂) ⋀^ι⟮𝕜; F₁, E₁; F₂, E₂⟯

end smooth

noncomputable section charted

variable
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM]
  (IM : ModelWithCorners ℝ EM HM)
  (M : Type*) [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]
  {m : ℕ}

open Bundle Set Function Filter
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry

@[instance_reducible]
def seminormedAddCommGroupTangentSpace (x : M) : SeminormedAddCommGroup (TangentSpace IM x) :=
  inferInstanceAs (SeminormedAddCommGroup EM)

attribute [local instance] seminormedAddCommGroupTangentSpace

@[instance_reducible]
def normedAddCommGroupTangentSpace (x : M) : NormedAddCommGroup (TangentSpace IM x) :=
  inferInstanceAs (NormedAddCommGroup EM)

attribute [local instance] normedAddCommGroupTangentSpace

@[instance_reducible]
def normedSpaceTangentSpace (x : M) : NormedSpace ℝ (TangentSpace IM x) :=
  inferInstanceAs (NormedSpace ℝ EM)

attribute [local instance] normedSpaceTangentSpace

lemma continuousAlternatingMap_trivializationAt_apply (m : ℕ) (x₀ x : M)
    (L : Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
      (Bundle.Trivial M ℝ) x) :
    (trivializationAt (EM [⋀^Fin m]→L[ℝ] ℝ)
      (Bundle.continuousAlternatingMap ℝ (Fin m) EM (TangentSpace IM) ℝ
        (Bundle.Trivial M ℝ)) x₀ ⟨x, L⟩).2 =
      L.compContinuousLinearMap ((trivializationAt EM (TangentSpace IM) x₀).symmL ℝ x) := by
  rw [FiberBundle.trivializationAt_continuousAlternatingMap_apply]
  ext v
  simp [ContinuousAlternatingMap.inCoordinates]

end DifferentialGeometry

instance ChartedSpace.alternatingBundle : ChartedSpace (ModelProd HM (EM [⋀^Fin m]→L[ℝ] ℝ))
    𝒜⟮ℝ,Fin m;EM,TangentSpace IM;ℝ,Bundle.Trivial M ℝ⟯ := inferInstance

end charted
