import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
# The base differentials of a family of face functions through a circle chart (lane S-BCF03)

Kernel of the independence step of the half charts of the circle-base curve of BCF03 (G6c's record
asks the family `v ↦ (mvfderiv (φ_f ∘ f₁) p v)_f` to be onto at every point `p` of the circle
fibre):

* `surjective_base_differential_BCF`: if `φ : ℝ² × S¹ → M` is a smooth embedding into a
  `3`-manifold, `F f ∘ φ = Ψ f ∘ fst` (`F f = φ_f ∘ f₁`, `Ψ f = φ_f ∘ σ`, because
  `f₁ ∘ φ = σ ∘ fst`) and `v ↦ (mvfderiv (F f) p v)_f` is onto at `p = φ (x₀, z₀)`, then
  `v ↦ (d(Ψ f)(x₀) v)_f` is onto `ℝ^ι`, i.e. the differentials `d(Ψ f)(x₀)` are linearly
  independent. The differentiability of the `F f` at `p` is NOT assumed: a non-differentiable `F f`
  has `mvfderiv = 0`, which contradicts surjectivity.

Route: `mfderiv φ` is injective (immersion) between spaces of the same finite dimension `3`,
hence onto; the chain rule gives `mvfderiv (F f) p (mfderiv φ u) = d(Ψ f)(x₀) u.1`.
-/

set_option autoImplicit false

open Set Function Manifold
open scoped ContDiff Manifold

noncomputable section

namespace DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **The base differentials of the face functions are onto** (see the module docstring). -/
theorem surjective_base_differential_BCF {EM HM M : Type*} [NormedAddCommGroup EM]
    [NormedSpace ℝ EM] [FiniteDimensional ℝ EM] [TopologicalSpace HM]
    {I : ModelWithCorners ℝ EM HM} [TopologicalSpace M] [ChartedSpace HM M] {ι : Type*}
    (F : ι → M → ℝ) (Ψ : ι → E2 → ℝ) (φ : E2 × Circle → M)
    (hφ : IsSmoothEmbedding ((𝓡 2).prod (𝓡 1)) I ∞ φ) (hdim : Module.finrank ℝ EM = 3)
    (x₀ : E2) (z₀ : Circle) (hΨ : ∀ f, DifferentiableAt ℝ (Ψ f) x₀)
    (hFΨ : ∀ f x z, F f (φ (x, z)) = Ψ f x)
    (hsurj : Surjective fun v : TangentSpace I (φ (x₀, z₀)) =>
      fun f : ι => mvfderiv I (F f) (φ (x₀, z₀)) v) :
    Surjective fun v : E2 => fun f : ι => fderiv ℝ (Ψ f) x₀ v := by
  classical
  have hF : ∀ f, MDiffAt (F f) (φ (x₀, z₀)) := by
    intro f
    by_contra hnd
    obtain ⟨v, hv⟩ := hsurj (Pi.single f 1)
    have h0 : mvfderiv I (F f) (φ (x₀, z₀)) v = 0 := by
      simp [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hnd]
    have h1 := congrFun hv f
    rw [Pi.single_eq_same] at h1
    exact zero_ne_one (h0.symm.trans h1)
  have hinj := hφ.isImmersion.mfderiv_injective (by simp) (x₀, z₀)
  have hφm : MDiffAt φ (x₀, z₀) := hφ.contMDiff.mdifferentiableAt (by simp)
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ EM := by
    simp [Module.finrank_prod, hdim]
  have hsA : Surjective (mfderiv ((𝓡 2).prod (𝓡 1)) I φ (x₀, z₀)) := by
    have h := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (mfderiv ((𝓡 2).prod (𝓡 1)) I φ (x₀, z₀) :
        EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1) →L[ℝ] EM).toLinearMap) hfr).mp hinj
    exact h
  have hchain : ∀ f (u : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)),
      mvfderiv I (F f) (φ (x₀, z₀)) (mfderiv ((𝓡 2).prod (𝓡 1)) I φ (x₀, z₀) u) =
        fderiv ℝ (Ψ f) x₀ u.1 := by
    intro f u
    have hcomp := mfderiv_comp (I := (𝓡 2).prod (𝓡 1)) (I' := I) (I'' := 𝓘(ℝ, ℝ)) (x₀, z₀)
      (hF f) hφm
    have heq : (F f ∘ φ) = fun q => Ψ f q.1 := funext fun q => hFΨ f q.1 q.2
    have hΨm : MDiffAt (Ψ f) x₀ := (hΨ f).mdifferentiableAt
    have hcomp2 := mfderiv_comp (I := (𝓡 2).prod (𝓡 1)) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ)) (x₀, z₀)
      (g := Ψ f) (f := Prod.fst) hΨm mdifferentiableAt_fst
    have h3 : mfderiv ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℝ) (F f ∘ φ) (x₀, z₀) u =
        fderiv ℝ (Ψ f) x₀ u.1 := by
      rw [heq]
      change mfderiv ((𝓡 2).prod (𝓡 1)) 𝓘(ℝ, ℝ) (Ψ f ∘ Prod.fst) (x₀, z₀) u = _
      rw [hcomp2]
      simp [mfderiv_fst, mfderiv_eq_fderiv]
      rfl
    rw [hcomp] at h3
    exact h3
  intro b
  obtain ⟨v, hv⟩ := hsurj b
  obtain ⟨u, rfl⟩ := hsA v
  refine ⟨u.1, ?_⟩
  funext f
  exact (hchain f u).symm.trans (congrFun hv f)

end DifferentialGeometry.Topology
