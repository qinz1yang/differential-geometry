import DifferentialGeometry.Topology.Manifold.EmbeddedHypersurface.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
noncomputable section
open Set Bundle DifferentialGeometry.Topology.Morse
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Manifold.EmbeddedHypersurface

variable {m : ℕ} {H G S M : Type*}
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace S] [ChartedSpace H S]
  [TopologicalSpace M] [ChartedSpace G M]
  (I : ModelWithCorners ℝ (MorseModel m) H)
  (J : ModelWithCorners ℝ (MorseModel (m + 1)) G) (e : S → M)
  [IsManifold J 1 M]


abbrev normalSpace (s : S) := TangentSpace J (e s) ⧸ (mfderiv I J e s).range


def normalQuotientMap : TotalSpace (MorseModel (m + 1)) (e *ᵖ (TangentSpace J (M := M))) →
    TotalSpace ℝ (normalSpace I J e) :=
  fun z ↦ ⟨z.proj, (mfderiv I J e z.proj).range.mkQ z.snd⟩


instance normalBundleTopology : TopologicalSpace (TotalSpace ℝ (normalSpace I J e)) :=
  TopologicalSpace.coinduced (normalQuotientMap I J e) inferInstance

omit [IsManifold J 1 M] in
theorem normalQuotientMap_surjective : Function.Surjective (normalQuotientMap I J e) := by
  rintro ⟨s, v⟩
  obtain ⟨w, rfl⟩ := (mfderiv I J e s).range.mkQ_surjective v
  exact ⟨⟨s, w⟩, rfl⟩


theorem isQuotientMap_normalQuotientMap : Topology.IsQuotientMap (normalQuotientMap I J e) :=
  ⟨⟨rfl⟩, normalQuotientMap_surjective I J e⟩


theorem continuous_normalQuotientMap : Continuous (normalQuotientMap I J e) :=
  (isQuotientMap_normalQuotientMap I J e).continuous


theorem continuous_normalBundle_proj :
    Continuous (TotalSpace.proj : TotalSpace ℝ (normalSpace I J e) → S) := by
  apply (isQuotientMap_normalQuotientMap I J e).continuous_iff.mpr
  exact Pullback.continuous_proj _ _ e

variable (t : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (normalSpace I J e) → S))
  [t.IsLinear ℝ] (ht : t.baseSet = Set.univ)

def normalTrivializationSection (s : S) : normalSpace I J e s :=
  (t.linearEquivAt ℝ s (ht ▸ mem_univ s)).symm 1


theorem normalTrivializationSection_coordinate (s : S) :
    (t ⟨s, normalTrivializationSection I J e t ht s⟩).2 = 1 :=
  (t.linearEquivAt ℝ s (ht ▸ mem_univ s)).apply_symm_apply 1


theorem normalTrivializationSection_ne_zero (s : S) :
    normalTrivializationSection I J e t ht s ≠ 0 := by
  intro h
  exact one_ne_zero ((t.linearEquivAt ℝ s (ht ▸ mem_univ s)).symm.map_eq_zero_iff.mp h)


theorem continuous_normalTrivializationSection :
    Continuous (fun s ↦ (⟨s, normalTrivializationSection I J e t ht s⟩ :
      TotalSpace ℝ (normalSpace I J e))) := by
  have h := t.continuousOn_symm.comp_continuous
    (continuous_id.prodMk (continuous_const (y := (1 : ℝ))))
    (fun s ↦ ⟨ht ▸ mem_univ s, mem_univ (1 : ℝ)⟩)
  exact h

private local instance ambientNormed (s : S) : NormedAddCommGroup (TangentSpace J (e s)) :=
  inferInstanceAs (NormedAddCommGroup (MorseModel (m + 1)))
private local instance ambientNormedSpace (s : S) : NormedSpace ℝ (TangentSpace J (e s)) :=
  inferInstanceAs (NormedSpace ℝ (MorseModel (m + 1)))
private local instance ambientFinite (s : S) : FiniteDimensional ℝ (TangentSpace J (e s)) :=
  inferInstanceAs (FiniteDimensional ℝ (MorseModel (m + 1)))

omit [IsManifold J 1 M] in
theorem finrank_normalSpace [I.Boundaryless] [J.Boundaryless] (s : S)
    (he : Manifold.IsImmersionAt I J ∞ e s) :
    Module.finrank ℝ (normalSpace I J e s) = 1 := by
  have hi := injective_mfderiv_of_isImmersionAt I J he
  have hr := LinearMap.finrank_range_of_inj hi
  have hq := (mfderiv I J e s).range.finrank_quotient_add_finrank
  have hS : Module.finrank ℝ (TangentSpace I s) = m := by
    change Module.finrank ℝ (MorseModel m) = m
    simp [MorseModel]
  have hM : Module.finrank ℝ (TangentSpace J (e s)) = m + 1 := by
    change Module.finrank ℝ (MorseModel (m + 1)) = m + 1
    simp [MorseModel]
  rw [hS] at hr
  rw [hr, hM] at hq
  change Module.finrank ℝ (normalSpace I J e s) + m = m + 1 at hq
  omega


def normalTrivializationCovector (s : S) : TangentSpace J (e s) →L[ℝ] ℝ :=
  ((t.linearEquivAt ℝ s (ht ▸ mem_univ s)).toLinearMap.comp
    (mfderiv I J e s).range.mkQ).toContinuousLinearMap


theorem normalTrivializationCovector_apply (s : S) (v : TangentSpace J (e s)) :
    normalTrivializationCovector I J e t ht s v =
      (t ⟨s, (mfderiv I J e s).range.mkQ v⟩).2 := rfl


theorem ker_normalTrivializationCovector (s : S) :
    (normalTrivializationCovector I J e t ht s).ker = (mfderiv I J e s).range := by
  ext v
  change (t.linearEquivAt ℝ s (ht ▸ mem_univ s))
    ((mfderiv I J e s).range.mkQ v) = 0 ↔ v ∈ (mfderiv I J e s).range
  rw [LinearEquiv.map_eq_zero_iff]
  exact Submodule.Quotient.mk_eq_zero _


theorem normalTrivializationCovector_ne_zero (s : S) :
    normalTrivializationCovector I J e t ht s ≠ 0 := by
  obtain ⟨v, hv⟩ := (mfderiv I J e s).range.mkQ_surjective
    (normalTrivializationSection I J e t ht s)
  intro hz
  have h := normalTrivializationSection_coordinate I J e t ht s
  rw [← hv, ← normalTrivializationCovector_apply I J e t ht s v, hz] at h
  exact zero_ne_one h


theorem continuous_normalTrivializationCovector_apply :
    Continuous (fun z : TotalSpace (MorseModel (m + 1)) (e *ᵖ (TangentSpace J (M := M))) ↦
      normalTrivializationCovector I J e t ht z.proj z.snd) := by
  have hc : Continuous t := by
    apply continuousOn_univ.mp
    simpa only [t.source_eq, ht, Set.preimage_univ] using t.continuousOn
  exact hc.snd.comp (continuous_normalQuotientMap I J e)

end DifferentialGeometry.Manifold.EmbeddedHypersurface
