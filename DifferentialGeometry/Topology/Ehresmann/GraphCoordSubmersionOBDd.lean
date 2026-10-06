import DifferentialGeometry.Topology.Ehresmann.SurfaceIntervalProductEFE
import DifferentialGeometry.Bundle.PartialMfderiv.Composition

/-!
# The graph coordinate of a map with values on a graph-chart piece (lane S-BD2d, suffix `_OBDd`)

Lane O-BD1 (by S-BD2d), group G10a, kernel. For a smooth map `f : M → H` with `df ≠ 0` at `x`
whose values near `x` lie on the graph-chart piece `p '' dom` (`κ ∘ p = id` on the open `dom`),
the coordinate `κ ∘ f` has a surjective differential at `x`: near `x`, `f = p ∘ (κ ∘ f)`, so `df`
factors through `d(κ ∘ f)`, which is a functional into `ℝ`.

* `surjective_mfderiv_graphCoord_OBDd`: the statement, over any manifold `M` and any model.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology Manifold Filter
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E HM : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace HM]
  {I : ModelWithCorners ℝ E HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **The graph coordinate of a nonconstant map into a graph-chart piece is a submersion.** -/
theorem surjective_mfderiv_graphCoord_OBDd (f : M → H) (hf : ContMDiff I 𝓘(ℝ, H) ∞ f)
    (κ : H →L[ℝ] ℝ) (p : ℝ → H) (dom : Set ℝ) (hdom : IsOpen dom)
    (hp : ContDiffOn ℝ ∞ p dom) (hκp : ∀ b ∈ dom, κ (p b) = b) {x : M}
    (hx : f x ∈ p '' dom) (hloc : ∀ᶠ y in 𝓝 x, f y ∈ p '' dom)
    (hne : mfderiv I 𝓘(ℝ, H) f x ≠ 0) :
    Surjective (mfderiv I 𝓘(ℝ, ℝ) (fun y => κ (f y)) x) := by
  have hg : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y => κ (f y)) :=
    κ.contDiff.comp_contMDiff hf
  have hgx : (fun y => κ (f y)) x ∈ dom := by
    obtain ⟨b, hb, hfb⟩ := hx
    change κ (f x) ∈ dom
    rw [← hfb, hκp b hb]
    exact hb
  have hev : f =ᶠ[𝓝 x] p ∘ (fun y => κ (f y)) := by
    filter_upwards [hloc] with y hy
    obtain ⟨b, hb, hfb⟩ := hy
    change f y = p (κ (f y))
    rw [← hfb, hκp b hb]
  have hpd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, H) p ((fun y => κ (f y)) x) :=
    (hp.contDiffAt (hdom.mem_nhds hgx)).contMDiffAt.mdifferentiableAt (by simp)
  have hchain : mfderiv I 𝓘(ℝ, H) f x =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, H) p ((fun y => κ (f y)) x)).comp
        (mfderiv I 𝓘(ℝ, ℝ) (fun y => κ (f y)) x) := by
    rw [hev.mfderiv_eq]
    exact mfderiv_comp x hpd (hg.mdifferentiableAt (by simp))
  by_contra hns
  apply hne
  have hzero : ∀ v : TangentSpace I x, mfderiv I 𝓘(ℝ, ℝ) (fun y => κ (f y)) x v = 0 := by
    intro v
    by_contra hv
    apply hns
    intro a
    let c : ℝ := mfderiv I 𝓘(ℝ, ℝ) (fun y => κ (f y)) x v
    have hc : c ≠ 0 := hv
    let a' : ℝ := a
    refine ⟨(a' / c) • v, ?_⟩
    rw [map_smul]
    change (a' / c) * c = a'
    exact div_mul_cancel₀ a' hc
  rw [hchain]
  ext v
  rw [ContinuousLinearMap.comp_apply, hzero v, map_zero]
  rfl

/-- A continuous linear map that vanishes after a surjective one vanishes (no norm: it is
applied to tangent spaces, which carry no `NormedAddCommGroup` instance in this file). -/
theorem clm_eq_zero_of_comp_surjective_OBDd {E₁ F₁ G₁ : Type*} [TopologicalSpace E₁]
    [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace F₁] [AddCommGroup F₁] [Module ℝ F₁]
    [TopologicalSpace G₁] [AddCommGroup G₁] [Module ℝ G₁] (L₁ : F₁ →L[ℝ] G₁) (L₂ : E₁ →L[ℝ] F₁)
    (hs : Surjective L₂) (h : L₁.comp L₂ = 0) : L₁ = 0 := by
  ext v
  obtain ⟨u, rfl⟩ := hs v
  exact congrArg (fun L => L u) h

variable {EN HN : Type*} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [TopologicalSpace HN]
  {J : ModelWithCorners ℝ EN HN} {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]

/-- **A nonvanishing differential stays nonvanishing after a map with surjective differential.** -/
theorem mfderiv_comp_ne_zero_of_surjective_OBDd (φ : M → N) (g : N → H) (x : M)
    (hg : MDifferentiableAt J 𝓘(ℝ, H) g (φ x)) (hφ : MDifferentiableAt I J φ x)
    (hs : Surjective (mfderiv I J φ x)) (hne : mvfderiv J g (φ x) ≠ 0) :
    mfderiv I 𝓘(ℝ, H) (g ∘ φ) x ≠ 0 := by
  intro h0
  apply hne
  have h1 : mvfderiv I (g ∘ φ) x = 0 := by
    unfold mvfderiv
    rw [h0]
    simp
  rw [hg.mvfderiv_comp hφ] at h1
  exact clm_eq_zero_of_comp_surjective_OBDd _ _ hs h1

/-- The differential of a local diffeomorphism at a point is surjective. -/
theorem surjective_mfderiv_of_isLocalDiffeomorphAt_OBDd {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J ∞ f x) : Surjective (mfderiv I J f x) := by
  obtain ⟨e, he⟩ := hf.isInvertible_mfderiv (by simp)
  rw [← he]
  exact e.surjective

/-- The zero map has rank zero. -/
theorem finrank_range_clm_zero_OBDd {E₁ F₁ : Type*} [TopologicalSpace E₁] [AddCommGroup E₁]
    [Module ℝ E₁] [TopologicalSpace F₁] [AddCommGroup F₁] [Module ℝ F₁] (L : E₁ →L[ℝ] F₁)
    (h : L = 0) : Module.finrank ℝ (LinearMap.range (L : E₁ →ₗ[ℝ] F₁)) = 0 := by
  subst h
  rw [ContinuousLinearMap.toLinearMap_zero, LinearMap.range_zero, finrank_bot]

/-- The differential of a local diffeomorphism at a point is injective. -/
theorem injective_mfderiv_of_isLocalDiffeomorphAt_OBDd {f : M → N} {x : M}
    (hf : IsLocalDiffeomorphAt I J ∞ f x) : Injective (mfderiv I J f x) := by
  obtain ⟨e, he⟩ := hf.isInvertible_mfderiv (by simp)
  rw [← he]
  exact e.injective

variable {EP HP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [TopologicalSpace HP]
  {K' : ModelWithCorners ℝ EP HP} {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]

/-- The composite of two maps with injective differentials has an injective differential. -/
theorem injective_mfderiv_comp_OBDd {f : M → N} {g : N → P} {x : M}
    (hg : MDifferentiableAt J K' g (f x)) (hf : MDifferentiableAt I J f x)
    (hgi : Injective (mfderiv J K' g (f x))) (hfi : Injective (mfderiv I J f x)) :
    Injective (mfderiv I K' (g ∘ f) x) := by
  rw [mfderiv_comp x hg hf]
  exact hgi.comp hfi

end DifferentialGeometry.Topology.Ehresmann
