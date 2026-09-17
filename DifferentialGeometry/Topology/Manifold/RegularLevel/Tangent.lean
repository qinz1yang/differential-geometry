import DifferentialGeometry.Topology.Manifold.RegularLevel.Collar.LevelAtlas
import DifferentialGeometry.Topology.Manifold.ImmersionDifferential
import DifferentialGeometry.Topology.Embedding.TangentLift
import Mathlib.LinearAlgebra.Dual.Lemmas

open Manifold
open scoped ContDiff
open DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Manifold.RegularLevel

variable {m : ℕ} {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℝ (MorseModel (m + 1)) H)
  [I.Boundaryless] [IsManifold I ∞ M]

theorem range_mfderiv_level_inclusion {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) :
    let _ := levelChartedSpace I hf hr
    ∀ x : {y : M // f y = a},
      (mfderiv 𝓘(ℝ, MorseModel m) I Subtype.val x).range =
        (mfderiv I 𝓘(ℝ, ℝ) f x.val).ker := by
  let _ := levelChartedSpace I hf hr
  let _ := levelIsManifold I hf hr
  change ∀ x : {y : M // f y = a},
    (mfderiv 𝓘(ℝ, MorseModel m) I Subtype.val x).range =
      (mfderiv I 𝓘(ℝ, ℝ) f x.val).ker
  intro x
  let : FiniteDimensional ℝ (TangentSpace I x.val) :=
    inferInstanceAs (FiniteDimensional ℝ (MorseModel (m + 1)))
  have he := isSmoothEmbedding_level_inclusion I hf hr
  have hle : (mfderiv 𝓘(ℝ, MorseModel m) I Subtype.val x).range ≤
      (mfderiv I 𝓘(ℝ, ℝ) f x.val).ker := by
    rintro v ⟨w, rfl⟩
    change (mfderiv I 𝓘(ℝ, ℝ) f x.val).comp
      (mfderiv 𝓘(ℝ, MorseModel m) I Subtype.val x) w = 0
    rw [← mfderiv_comp x (hf.mdifferentiableAt (by simp))
      (he.contMDiff.mdifferentiableAt (by simp))]
    have hc : f ∘ (Subtype.val : {y : M // f y = a} → M) = fun _ => a :=
      funext Subtype.property
    rw [hc, mfderiv_const]
    rfl
  apply Submodule.eq_of_le_of_finrank_eq hle
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero
    (f := (mfderiv I 𝓘(ℝ, ℝ) f x.val).toLinearMap)
    (by intro h; exact hr x.val x.property (ContinuousLinearMap.coe_injective h))
  rw [LinearMap.finrank_range_of_inj
    ((he.isImmersion.isImmersionAt x).injective_mfderiv (by simp))]
  change Module.finrank ℝ (MorseModel m) = _
  change Module.finrank ℝ (mfderiv I 𝓘(ℝ, ℝ) f x.val).ker + 1 =
    Module.finrank ℝ (MorseModel (m + 1)) at hdim
  simp only [MorseModel, Module.finrank_fin_fun] at hdim ⊢
  omega

theorem exists_contMDiff_tangent_field {f : M → ℝ} {a : ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hr : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0)
    (V : (x : M) → TangentSpace I x)
    (hV : ContMDiff I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)))
    (hker : ∀ x, f x = a → mfderiv I 𝓘(ℝ, ℝ) f x (V x) = 0) :
    let _ := levelChartedSpace I hf hr
    let _ := levelIsManifold I hf hr
    ∃ W : (x : {y : M // f y = a}) → TangentSpace 𝓘(ℝ, MorseModel m) x,
      ContMDiff 𝓘(ℝ, MorseModel m) (𝓘(ℝ, MorseModel m)).tangent ∞
        (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, MorseModel m) {y : M // f y = a})) ∧
      (∀ x, mfderiv 𝓘(ℝ, MorseModel m) I Subtype.val x (W x) = V x.val) := by
  let _ := levelChartedSpace I hf hr
  let _ := levelIsManifold I hf hr
  have he := isSmoothEmbedding_level_inclusion I hf hr
  exact he.exists_contMDiff_tangent_lift (fun x => V x.val)
    (hV.comp he.contMDiff) (fun x => by
      rw [range_mfderiv_level_inclusion I hf hr]
      exact hker x.val x.property)

end DifferentialGeometry.Manifold.RegularLevel
