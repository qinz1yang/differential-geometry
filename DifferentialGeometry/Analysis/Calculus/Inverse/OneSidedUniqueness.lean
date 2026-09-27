import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.ODE.ExistUnique

open Set Filter Topology
open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem locallyLipschitzOn_open_prod
    {f : E × ℝ → F} {V : Set E} {J : Set ℝ}
    (hV : IsOpen V) (hJ : Convex ℝ J) (hf : ContDiffOn ℝ 1 f (V ×ˢ J)) :
    LocallyLipschitzOn (V ×ˢ J) f := by
  intro x hx
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hx.1)
  let B := Metric.ball x.1 δ ×ˢ (univ : Set ℝ)
  let S := Metric.ball x.1 δ ×ˢ J
  have hsub : S ⊆ V ×ˢ J := prod_mono hδV Subset.rfl
  obtain ⟨K, T, hT, hfT⟩ := ((hf x hx).mono hsub).exists_lipschitzOnWith
    ((convex_ball _ _).prod hJ)
  have hBS : B ∩ (V ×ˢ J) = S := by
    ext z
    exact ⟨fun hz ↦ ⟨hz.1.1, hz.2.2⟩,
      fun hz ↦ ⟨⟨hz.1, mem_univ _⟩, hδV hz.1, hz.2⟩⟩
  have hB : B ∈ 𝓝 x := (Metric.isOpen_ball.prod isOpen_univ).mem_nhds
    ⟨Metric.mem_ball_self hδ, mem_univ _⟩
  have hnhds : 𝓝[S] x = 𝓝[V ×ˢ J] x := by
    rw [← hBS, nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds hB)]
  exact ⟨K, T, hnhds ▸ hT, hfT⟩

theorem eqOn_of_one_sided_integral_curves
    {v : E × ℝ → E × ℝ} {V : Set E} {J : Set ℝ} {a b : ℝ}
    {γ η : ℝ → E × ℝ}
    (hV : IsOpen V) (hJ : Convex ℝ J) (hv : ContDiffOn ℝ 1 v (V ×ˢ J))
    (hγ : ContinuousOn γ (Icc a b))
    (hγd : ∀ t ∈ Ico a b, HasDerivWithinAt γ (v (γ t)) (Ici t) t)
    (hγmem : MapsTo γ (Icc a b) (V ×ˢ J))
    (hη : ContinuousOn η (Icc a b))
    (hηd : ∀ t ∈ Ico a b, HasDerivWithinAt η (v (η t)) (Ici t) t)
    (hηmem : MapsTo η (Icc a b) (V ×ˢ J)) (hinit : γ a = η a) :
    EqOn γ η (Icc a b) := by
  let K := γ '' Icc a b ∪ η '' Icc a b
  have hK : IsCompact K := (isCompact_Icc.image_of_continuousOn hγ).union
    (isCompact_Icc.image_of_continuousOn hη)
  have hKS : K ⊆ V ×ˢ J := union_subset hγmem.image_subset hηmem.image_subset
  obtain ⟨L, hL⟩ := ((locallyLipschitzOn_open_prod hV hJ hv).mono hKS).exists_lipschitzOnWith_of_compact hK
  exact ODE_solution_unique_of_mem_Icc_right (fun _ _ ↦ hL) hγ hγd
    (fun t ht ↦ Or.inl ⟨t, Ico_subset_Icc_self ht, rfl⟩) hη hηd
    (fun t ht ↦ Or.inr ⟨t, Ico_subset_Icc_self ht, rfl⟩) hinit

end DifferentialGeometry.Analysis
