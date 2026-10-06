import DifferentialGeometry.Analysis.Calculus.MapConvergence.TransverseIntersection
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

noncomputable section

open Filter Function Manifold Set Topology
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.Manifold

/-- Local convergence in one fixed target chart transports the persistence of
transverse intersections to manifold-valued maps. The chart containment and
first-derivative convergence are required on compact subsets of the chart
preimage; the approximating maps themselves are injective on the source.

This does not construct a sequence of embedded maps or a convergent subsequence.
Its conclusion applies to the literal limit map. -/
theorem not_surjective_coprod_mfderiv_of_injective_c1_limit
    {E F M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
    {S : Set E} (hS : IsOpen S) {f : ℕ → E → M} {f₀ : E → M}
    (hf : ∀ᶠ n in atTop, MDifferentiableOn 𝓘(ℝ, E) 𝓘(ℝ, F) (f n) S)
    (hf₀ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) 1 f₀ S)
    (hinj : ∀ᶠ n in atTop, InjOn (f n) S)
    (hval : ∀ p : M, ∀ x ∈ S,
      f₀ x ∈ (extChartAt 𝓘(ℝ, F) p).source →
      Tendsto (fun n => extChartAt 𝓘(ℝ, F) p (f n x)) atTop
        (𝓝 (extChartAt 𝓘(ℝ, F) p (f₀ x))))
    (hchart : ∀ p : M, ∀ K : Set E, IsCompact K →
      K ⊆ S ∩ f₀ ⁻¹' (extChartAt 𝓘(ℝ, F) p).source →
      ∀ᶠ n in atTop, MapsTo (f n) K (extChartAt 𝓘(ℝ, F) p).source)
    (hder : ∀ p : M, ∀ K : Set E, IsCompact K →
      K ⊆ S ∩ f₀ ⁻¹' (extChartAt 𝓘(ℝ, F) p).source →
      TendstoUniformlyOn
        (fun n x => fderiv ℝ (fun z => extChartAt 𝓘(ℝ, F) p (f n z)) x)
        (fun x => fderiv ℝ (fun z => extChartAt 𝓘(ℝ, F) p (f₀ z)) x) atTop K)
    {a b : E} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (heq : f₀ a = f₀ b) :
    ¬ Function.Surjective
      ((show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f₀ a).coprod
        (-(show E →L[ℝ] F from mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f₀ b))) := by
  let χ := extChartAt 𝓘(ℝ, F) (f₀ a)
  let T : Set E := S ∩ f₀ ⁻¹' χ.source
  have hT : IsOpen T := hf₀.continuousOn.isOpen_inter_preimage
    hS (isOpen_extChartAt_source (f₀ a))
  have haT : a ∈ T := ⟨ha, mem_extChartAt_source (f₀ a)⟩
  have hbT : b ∈ T := by
    refine ⟨hb, ?_⟩
    change f₀ b ∈ (extChartAt 𝓘(ℝ, F) (f₀ a)).source
    rw [← heq]
    exact mem_extChartAt_source (f₀ a)
  have hpair : ({a} ∪ {b} : Set E) ⊆ T := by
    intro x hx
    simp only [mem_union, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact haT
    · exact hbT
  obtain ⟨K, hK, hpairK, hKT⟩ := exists_compact_between
    (isCompact_singleton.union isCompact_singleton) hT hpair
  let U : Set E := interior K
  have hUT : U ⊆ T := interior_subset.trans hKT
  have hUS : U ⊆ S := fun x hx => (hUT hx).1
  have haU : a ∈ U := hpairK (by simp)
  have hbU : b ∈ U := hpairK (by simp)
  let X : ℕ → E → F := fun n x => χ (f n x)
  let X₀ : E → F := fun x => χ (f₀ x)
  have hχ (x : E) (hx : x ∈ T) :
      ContMDiffAt 𝓘(ℝ, F) 𝓘(ℝ, F) ∞ χ (f₀ x) :=
    contMDiffAt_extChartAt' (by
      have hxχ : f₀ x ∈ χ.source := hx.2
      simpa only [χ, extChartAt_source] using hxχ)
  have hX₀ : ContDiffOn ℝ 1 X₀ U := by
    intro x hx
    exact (((hχ x (hUT hx)).of_le (by simp)).comp x
      (hf₀.contMDiffAt (hS.mem_nhds (hUS hx)))).contDiffAt.contDiffWithinAt
  have hX : ∀ᶠ n in atTop, DifferentiableOn ℝ (X n) U := by
    filter_upwards [hf, hchart (f₀ a) K hK hKT] with n hn hnχ x hx
    have hfx : f n x ∈ χ.source := hnχ (interior_subset hx)
    have hχdiff : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F) χ (f n x) :=
      mdifferentiableAt_extChartAt (by simpa only [χ, extChartAt_source] using hfx)
    have hfdiff := (hn x (hUS hx)).mdifferentiableAt (hS.mem_nhds (hUS hx))
    exact (hχdiff.comp x hfdiff).differentiableAt.differentiableWithinAt
  have hXinj : ∀ᶠ n in atTop, InjOn (X n) U := by
    filter_upwards [hinj, hchart (f₀ a) K hK hKT] with n hn hnχ x hx y hy hxy
    exact hn (hUS hx) (hUS hy)
      (χ.injOn (hnχ (interior_subset hx)) (hnχ (interior_subset hy)) hxy)
  have hXval : ∀ x ∈ U, Tendsto (fun n => X n x) atTop (𝓝 (X₀ x)) :=
    fun x hx => hval (f₀ a) x (hUS hx) (hUT hx).2
  have hXder : ∀ L : Set E, IsCompact L → L ⊆ U →
      TendstoUniformlyOn (fun n x => fderiv ℝ (X n) x)
        (fun x => fderiv ℝ X₀ x) atTop L :=
    fun L hL hLU => hder (f₀ a) L hL (hLU.trans hUT)
  have hNo := DifferentialGeometry.Analysis.not_surjective_coprod_fderiv_of_injective_c1_limit
    isOpen_interior hX hX₀ hXinj hXval hXder haU hbU hab
      (congrArg χ heq)
  let D (x : E) : E →L[ℝ] F := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f₀ x
  let C (x : E) : F →L[ℝ] F := mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) χ (f₀ x)
  have hchain (x : E) (hx : x ∈ T) (v : E) :
      fderiv ℝ X₀ x v = C x (D x v) := by
    have hh := mfderiv_comp_apply x
      ((hχ x hx).mdifferentiableAt (by simp))
      ((hf₀.contMDiffAt (hS.mem_nhds hx.1)).mdifferentiableAt (by simp)) v
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hC : (C a).IsInvertible :=
    isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ, F)) haT.2
  have hCb : C b = C a := congrArg
    (fun p : M => (show F →L[ℝ] F from mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F) χ p)) heq.symm
  intro hsurj
  apply hNo
  intro y
  obtain ⟨w, hw⟩ := hC.surjective y
  obtain ⟨v, hv⟩ := hsurj w
  refine ⟨v, ?_⟩
  change fderiv ℝ X₀ a v.1 + -(fderiv ℝ X₀ b v.2) = y
  rw [hchain a haT, hchain b hbT, hCb, ← map_neg, ← map_add]
  exact (congrArg (C a) hv).trans hw

end DifferentialGeometry.Topology.Manifold
