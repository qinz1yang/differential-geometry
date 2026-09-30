import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskComplement
import DifferentialGeometry.Topology.PiecewiseLinear.IntervalHomeomorph

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem interval_marking {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < 1) :
    ∃ f : ℝ → ℝ, IsPLHomeomorphOn f (Icc 0 1) (Icc 0 1) ∧
      f 0 = 0 ∧ f 1 = 1 ∧ f (1 / 4) = s ∧ f (3 / 4) = t := by
  obtain ⟨f, hf, hf0, hf1, hfI⟩ := exists_isPLHomeomorphOn_Icc_map_Icc
    (a₀ := 0) (a₁ := 1 / 4) (a₂ := 3 / 4) (a₃ := 1)
    (by norm_num) (by norm_num) (by norm_num) hs hst ht
  have hmono := ContinuousOn.strictMonoOn_of_injOn_Icc zero_le_one
    (by rw [hf0, hf1]; exact zero_le_one) hf.isPiecewiseAffineOn.continuousOn hf.bijOn.injOn
  have hsub : Icc (1 / 4 : ℝ) (3 / 4) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc (by norm_num) (by norm_num)
  have hs' : f (1 / 4) ∈ Icc s t := hfI ▸ mem_image_of_mem f
    (show (1 / 4 : ℝ) ∈ Icc (1 / 4) (3 / 4) by norm_num)
  have ht' : f (3 / 4) ∈ Icc s t := hfI ▸ mem_image_of_mem f
    (show (3 / 4 : ℝ) ∈ Icc (1 / 4) (3 / 4) by norm_num)
  obtain ⟨u, hu, hfu⟩ : s ∈ f '' Icc (1 / 4) (3 / 4) := hfI.symm ▸ ⟨le_rfl, hst.le⟩
  obtain ⟨v, hv, hfv⟩ : t ∈ f '' Icc (1 / 4) (3 / 4) := hfI.symm ▸ ⟨hst.le, le_rfl⟩
  refine ⟨f, hf, hf0, hf1, le_antisymm ?_ hs'.1, le_antisymm ht'.2 ?_⟩
  · rw [← hfu]
    exact hmono.monotoneOn (by norm_num) (hsub hu) hu.1
  · rw [← hfv]
    exact hmono.monotoneOn (hsub hv) (by norm_num) hv.2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_arc_parametrization_marking_disjoint_caps
    {S D₀ D₁ T : Set E} {γ : ℝ → E} {q₀ q₁ : (Fin 3 → ℝ) → E} {x₀ x₁ : E}
    (hS : IsPLSphere 2 S) (hγ : IsPLHomeomorphOn γ (Icc 0 1) T) (hTS : T ⊆ S)
    (hq₀ : IsPLHomeomorphOn q₀ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₀)
    (hq₁ : IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁)
    (hD₀S : D₀ ⊆ S) (hdis : Disjoint D₀ D₁)
    (hzero : γ 0 ∈ D₀)
    (hzeroB : γ 0 ∉ q₀ '' stdSimplexBoundary 2)
    (honeB : γ 1 ∉ q₁ '' stdSimplexBoundary 2)
    (hb₀ : q₀ '' stdSimplexBoundary 2 ∩ T = {x₀})
    (hb₁ : q₁ '' stdSimplexBoundary 2 ∩ T = {x₁}) :
    ∃ δ : ℝ → E, IsPLHomeomorphOn δ (Icc 0 1) T ∧
      δ 0 = γ 0 ∧ δ 1 = γ 1 ∧ δ (1 / 4) = x₀ ∧ δ (3 / 4) = x₁ := by
  have hx₀ : x₀ ∈ q₀ '' stdSimplexBoundary 2 ∩ T := hb₀.symm ▸ mem_singleton x₀
  have hx₁ : x₁ ∈ q₁ '' stdSimplexBoundary 2 ∩ T := hb₁.symm ▸ mem_singleton x₁
  have hbd₀ : q₀ '' stdSimplexBoundary 2 ⊆ D₀ := by
    rw [← hq₀.image_eq]
    exact image_mono (fun _ h => h.1)
  have hbd₁ : q₁ '' stdSimplexBoundary 2 ⊆ D₁ := by
    rw [← hq₁.image_eq]
    exact image_mono (fun _ h => h.1)
  have hxne : x₀ ≠ x₁ := fun h =>
    disjoint_left.mp hdis (hbd₀ hx₀.1) (h ▸ hbd₁ hx₁.1)
  obtain ⟨s, hs, hγs⟩ := hγ.bijOn.surjOn hx₀.2
  obtain ⟨t, ht, hγt⟩ := hγ.bijOn.surjOn hx₁.2
  have hs0 : 0 < s := lt_of_le_of_ne hs.1 fun h => hzeroB (h.symm ▸ hγs.symm ▸ hx₀.1)
  have ht1 : t < 1 := lt_of_le_of_ne ht.2 fun h => honeB (h ▸ hγt.symm ▸ hx₁.1)
  have hst : s < t := by
    have hU : IsPreconnected (γ '' Icc 0 t) := isPreconnected_Icc.image γ
      (hγ.isPiecewiseAffineOn.continuousOn.mono (Icc_subset_Icc le_rfl ht.2))
    have hUS : γ '' Icc 0 t ⊆ S :=
      (image_subset_iff.mpr (hγ.bijOn.mapsTo.mono_left (Icc_subset_Icc le_rfl ht.2))).trans hTS
    have hcover : γ '' Icc 0 t ⊆ D₀ ∪ closure (S \ D₀) := by
      intro y hy
      by_cases hyD : y ∈ D₀
      · exact Or.inl hyD
      · exact Or.inr (subset_closure ⟨hUS hy, hyD⟩)
    obtain ⟨y, hyU, hyD, hyC⟩ := isPreconnected_closed_iff.mp hU D₀ (closure (S \ D₀))
      (show IsPLBall 2 D₀ from ⟨q₀, hq₀⟩).isPolyhedron.isClosed isClosed_closure hcover
      ⟨γ 0, ⟨0, ⟨le_rfl, ht.1⟩, rfl⟩, hzero⟩
      ⟨x₁, ⟨t, ⟨ht.1, le_rfl⟩, hγt⟩,
        subset_closure ⟨hTS hx₁.2, fun h => disjoint_left.mp hdis h (hbd₁ hx₁.1)⟩⟩
    have hyB : y ∈ q₀ '' stdSimplexBoundary 2 :=
      hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq₀ hD₀S ▸ ⟨hyD, hyC⟩
    obtain ⟨r, hr, hγr⟩ := hyU
    have hyT : y ∈ T := hγr ▸ hγ.bijOn.mapsTo ⟨hr.1, hr.2.trans ht.2⟩
    have hyx : y = x₀ := mem_singleton_iff.mp (hb₀ ▸ ⟨hyB, hyT⟩)
    have hrs : r = s := hγ.bijOn.injOn ⟨hr.1, hr.2.trans ht.2⟩ hs
      (hγr.trans (hyx.trans hγs.symm))
    apply lt_of_le_of_ne (hrs ▸ hr.2)
    intro heq
    exact hxne (hγs.symm.trans (heq ▸ hγt))
  obtain ⟨f, hf, hf0, hf1, hfs, hft⟩ := interval_marking hs0 hst ht1
  exact ⟨γ ∘ f, hf.trans hγ, by simp [hf0], by simp [hf1],
    by change γ (f (1 / 4)) = x₀; rw [hfs, hγs],
    by change γ (f (3 / 4)) = x₁; rw [hft, hγt]⟩

end DifferentialGeometry.Topology.PiecewiseLinear
