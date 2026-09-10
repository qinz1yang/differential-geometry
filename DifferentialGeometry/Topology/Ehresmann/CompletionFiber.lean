import DifferentialGeometry.Topology.Ehresmann.IntervalCompletionSpace
import DifferentialGeometry.Topology.Manifold.HomeomorphAtlas
import DifferentialGeometry.Topology.Manifold.SubmersionFiber
import DifferentialGeometry.Geometry.Boundary.FullRankFactorization

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Ehresmann

open Poincare.Topology.Manifold Poincare.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {M : Type*} [TopologicalSpace M] {u : M → ℝ} {a b s : ℝ}

def intervalCompletionFiberHomeomorph (hu : Continuous u) (hs : s ∈ Icc a b) :
    {x : M // u x = s} ≃ₜ {q : IntervalCompletionSpace u a b // intervalCompletionHeight u a b q = s} := by
  have hgraph (q : IntervalCompletionSpace u a b) (hq : intervalCompletionHeight u a b q = s) :
      q.1.2 = u q.1.1 := by
    change q.1.2 = s at hq
    rcases q.2 with h | ⟨h, hl⟩ | ⟨h, hr⟩
    · exact h
    · exact (le_antisymm hl (by rw [hq]; exact hs.1)).trans h.symm
    · exact (le_antisymm (by rw [hq]; exact hs.2) hr).trans h.symm
  let forward : {x : M // u x = s} →
      {q : IntervalCompletionSpace u a b // intervalCompletionHeight u a b q = s} :=
    fun x ↦ ⟨intervalCompletionInclusion u a b x.1, x.2⟩
  let inverse : {q : IntervalCompletionSpace u a b // intervalCompletionHeight u a b q = s} →
      {x : M // u x = s} := fun q ↦ ⟨q.1.1.1, (hgraph q.1 q.2).symm.trans q.2⟩
  refine ⟨⟨forward, inverse, fun _ ↦ rfl, ?_⟩, ?_, ?_⟩
  · intro q
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (hgraph q.1 q.2).symm
  · exact ((continuous_subtype_val.prodMk (hu.comp continuous_subtype_val)).subtype_mk _).subtype_mk _
  · exact (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [ChartedSpace E (IntervalCompletionSpace u a b)]
  [IsManifold 𝓘(ℝ, E) ∞ (IntervalCompletionSpace u a b)]

private theorem fiberAtlasData (hu : Continuous u) (hs : s ∈ Icc a b)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b))
    (hreg : ∀ q, intervalCompletionHeight u a b q = s →
      Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (intervalCompletionHeight u a b) q)) :
    let _ := regularFiberChartedSpace (intervalCompletionHeight u a b) s hf hreg
    ∃ C : ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) {x : M // u x = s},
      let _ := C
      IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) ∞ {x : M // u x = s} ∧
      ∃ d : Diffeomorph 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
          𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
          {q : IntervalCompletionSpace u a b // intervalCompletionHeight u a b q = s}
          {x : M // u x = s} ∞,
        (d : _ → _) = (intervalCompletionFiberHomeomorph hu hs).symm := by
  let _ := regularFiberChartedSpace (intervalCompletionHeight u a b) s hf hreg
  let := regularFiberIsManifold (intervalCompletionHeight u a b) s hf hreg
  exact exists_smoothAtlas_of_homeomorph (intervalCompletionFiberHomeomorph hu hs).symm

@[reducible]
def completionFiberChartedSpace (hu : Continuous u) (hs : s ∈ Icc a b)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b))
    (hreg : ∀ q, intervalCompletionHeight u a b q = s →
      Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (intervalCompletionHeight u a b) q)) :
    ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) {x : M // u x = s} :=
  (fiberAtlasData hu hs hf hreg).choose

theorem completionFiberIsManifold (hu : Continuous u) (hs : s ∈ Icc a b)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b))
    (hreg : ∀ q, intervalCompletionHeight u a b q = s →
      Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (intervalCompletionHeight u a b) q)) :
    let _ := completionFiberChartedSpace hu hs hf hreg
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) ∞ {x : M // u x = s} :=
  (fiberAtlasData hu hs hf hreg).choose_spec.1

def completionFiberDiffeomorph (hu : Continuous u) (hs : s ∈ Icc a b)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b))
    (hreg : ∀ q, intervalCompletionHeight u a b q = s →
      Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (intervalCompletionHeight u a b) q)) :
    let _ := regularFiberChartedSpace (intervalCompletionHeight u a b) s hf hreg
    let _ := completionFiberChartedSpace hu hs hf hreg
    Diffeomorph 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
      {q : IntervalCompletionSpace u a b // intervalCompletionHeight u a b q = s}
      {x : M // u x = s} ∞ :=
  (fiberAtlasData hu hs hf hreg).choose_spec.2.choose

@[simp]
theorem completionFiberDiffeomorph_apply (hu : Continuous u) (hs : s ∈ Icc a b)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b))
    (hreg : ∀ q, intervalCompletionHeight u a b q = s →
      Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (intervalCompletionHeight u a b) q))
    (q : {q : IntervalCompletionSpace u a b // intervalCompletionHeight u a b q = s}) :
    (completionFiberDiffeomorph hu hs hf hreg q).1 = q.1.1.1 :=
  congrArg Subtype.val (congrFun (fiberAtlasData hu hs hf hreg).choose_spec.2.choose_spec q)

@[simp]
theorem completionFiberDiffeomorph_symm_apply (hu : Continuous u) (hs : s ∈ Icc a b)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b))
    (hreg : ∀ q, intervalCompletionHeight u a b q = s →
      Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (intervalCompletionHeight u a b) q))
    (x : {x : M // u x = s}) :
    let _ := regularFiberChartedSpace (intervalCompletionHeight u a b) s hf hreg
    let _ := completionFiberChartedSpace hu hs hf hreg
    ((completionFiberDiffeomorph hu hs hf hreg).symm x).1 = intervalCompletionInclusion u a b x.1 := by
  dsimp only
  let _ := regularFiberChartedSpace (intervalCompletionHeight u a b) s hf hreg
  let _ := completionFiberChartedSpace hu hs hf hreg
  let d := completionFiberDiffeomorph hu hs hf hreg
  have hh : d ((intervalCompletionFiberHomeomorph hu hs) x) = x := by
    apply Subtype.ext
    exact completionFiberDiffeomorph_apply hu hs hf hreg _
  have heq : d.symm x = (intervalCompletionFiberHomeomorph hu hs) x := by
    apply d.injective
    exact (d.apply_symm_apply x).trans hh.symm
  exact congrArg Subtype.val heq

variable {H : Type*} [TopologicalSpace H] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [HasSmoothBoundary E H I] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_completionFiber_iff
    (hu : Continuous u) (hs : s ∈ Icc a b)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b))
    (hreg : ∀ q, intervalCompletionHeight u a b q = s →
      Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (intervalCompletionHeight u a b) q))
    (hi : ContMDiff I 𝓘(ℝ, E) ∞ (intervalCompletionInclusion u a b))
    (hemb : IsEmbedding (intervalCompletionInclusion u a b))
    (hj : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) (intervalCompletionInclusion u a b) x))
    {EP HP P : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
    [TopologicalSpace HP] [TopologicalSpace P] [ChartedSpace HP P]
    {J : ModelWithCorners ℝ EP HP} (g : P → {x : M // u x = s}) :
    let _ := completionFiberChartedSpace hu hs hf hreg
    ContMDiff J 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) ∞ g ↔
      ContMDiff J I ∞ (Subtype.val ∘ g) := by
  dsimp only
  let _ := regularFiberChartedSpace (intervalCompletionHeight u a b) s hf hreg
  let _ := completionFiberChartedSpace hu hs hf hreg
  let d := completionFiberDiffeomorph hu hs hf hreg
  have hdiff : ContMDiff J 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) ∞ g ↔
      ContMDiff J 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) ∞ (d.symm ∘ g) := by
    constructor
    · exact d.symm.contMDiff.comp
    · intro h
      simpa only [Function.comp_def, Diffeomorph.apply_symm_apply] using d.contMDiff.comp h
  have hfic := contMDiff_regularFiber_iff (IP := J)
    (intervalCompletionHeight u a b) s hf hreg (d.symm ∘ g)
  dsimp only at hfic
  rw [hdiff, hfic]
  have heq : Subtype.val ∘ (d.symm ∘ g) = intervalCompletionInclusion u a b ∘ (Subtype.val ∘ g) :=
    funext (fun x ↦ completionFiberDiffeomorph_symm_apply hu hs hf hreg (g x))
  rw [heq]
  exact (contMDiff_iff_comp_of_fullRank_embedding hi hemb hj rfl (Subtype.val ∘ g)).symm

theorem contMDiff_completionFiberInclusion
    (hu : Continuous u) (hs : s ∈ Icc a b)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (intervalCompletionHeight u a b))
    (hreg : ∀ q, intervalCompletionHeight u a b q = s →
      Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (intervalCompletionHeight u a b) q))
    (hi : ContMDiff I 𝓘(ℝ, E) ∞ (intervalCompletionInclusion u a b))
    (hemb : IsEmbedding (intervalCompletionInclusion u a b))
    (hj : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, E) (intervalCompletionInclusion u a b) x)) :
    let _ := completionFiberChartedSpace hu hs hf hreg
    ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) I ∞
      (Subtype.val : {x : M // u x = s} → M) := by
  let _ := completionFiberChartedSpace hu hs hf hreg
  exact (contMDiff_completionFiber_iff hu hs hf hreg hi hemb hj id).mp contMDiff_id

end Poincare.Topology.Ehresmann
