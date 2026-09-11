import DifferentialGeometry.Geometry.Comparison.Soul.EmbeddedSliceManifold
import DifferentialGeometry.Geometry.Comparison.Soul.NormalFrames
import Mathlib.Analysis.Normed.Operator.Banach

set_option autoImplicit false

noncomputable section

open Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {S : Set M} {d : ℕ}

private instance tangentFinite (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  inferInstanceAs (FiniteDimensional ℝ E)

theorem embeddedSlice_inclusion_mfderiv_injective
    (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    Function.Injective (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p) := by
  let _ := embeddedSliceChartedSpace hS
  let L := (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p).toLinearMap
  change Function.Injective L
  have hrange : Module.finrank ℝ L.range = d := by
    change Module.finrank ℝ
      (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p).range = d
    rw [embeddedSlice_inclusion_range_mfderiv hS p, finrank_sliceTangent hS p.2]
  have hsource : Module.finrank ℝ (TangentSpace 𝓘(ℝ, Fin d → ℝ) p) = d := by
    change Module.finrank ℝ (Fin d → ℝ) = d
    simp
  have hker : Module.finrank ℝ L.ker = 0 := by
    have hsum := L.finrank_range_add_finrank_ker
    rw [hrange, hsource] at hsum
    omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)

variable [IsManifold I ∞ M]

def normalSplitting (g : SmoothRiemannianMetric I M)
    (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    (TangentSpace 𝓘(ℝ, Fin d → ℝ) p × normalSpace (I := I) g S p.1) ≃L[ℝ]
      TangentSpace I p.1 := by
  let _ := embeddedSliceChartedSpace hS
  let : NormedAddCommGroup (TangentSpace 𝓘(ℝ, Fin d → ℝ) p) :=
    inferInstanceAs (NormedAddCommGroup (Fin d → ℝ))
  let : NormedSpace ℝ (TangentSpace 𝓘(ℝ, Fin d → ℝ) p) :=
    inferInstanceAs (NormedSpace ℝ (Fin d → ℝ))
  let : NormedAddCommGroup (TangentSpace I p.1) := inferInstanceAs (NormedAddCommGroup E)
  let : NormedSpace ℝ (TangentSpace I p.1) := inferInstanceAs (NormedSpace ℝ E)
  let L := mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p
  have hcompl : IsCompl L.range (normalSpace (I := I) g S p.1) := by
    change IsCompl
      (mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p).range
      (normalSpace (I := I) g S p.1)
    rw [embeddedSlice_inclusion_range_mfderiv hS p, isCompl_iff, disjoint_iff, codisjoint_iff]
    exact ⟨sliceTangent_inf_normalSpace (I := I) g S p.1,
      sliceTangent_sup_normalSpace (I := I) g S p.1⟩
  have hker : L.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr (embeddedSlice_inclusion_mfderiv_injective hS p)
  exact ContinuousLinearMap.coprodSubtypeLEquivOfIsCompl
    (𝕜 := ℝ) (E := TangentSpace 𝓘(ℝ, Fin d → ℝ) p) (F := TangentSpace I p.1)
    (G := normalSpace (I := I) g S p.1) L hcompl hker

@[simp] theorem normalSplitting_apply (g : SmoothRiemannianMetric I M)
    (hS : IsEmbeddedSlice I d S) (p : S) :
    let _ := embeddedSliceChartedSpace hS
    ∀ (a : TangentSpace 𝓘(ℝ, Fin d → ℝ) p) (n : normalSpace (I := I) g S p.1),
      normalSplitting g hS p (a, n) =
        mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p a + n.1 := by
  let _ := embeddedSliceChartedSpace hS
  change ∀ (a : TangentSpace 𝓘(ℝ, Fin d → ℝ) p) (n : normalSpace (I := I) g S p.1),
    normalSplitting g hS p (a, n) =
      mfderiv 𝓘(ℝ, Fin d → ℝ) I (Subtype.val : S → M) p a + n.1
  intro a n
  rfl

end DifferentialGeometry.Geometry.Topology
