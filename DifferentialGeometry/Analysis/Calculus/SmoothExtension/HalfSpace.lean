import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLineParam
import Mathlib.Geometry.Manifold.PartitionOfUnity

open scoped ContDiff Manifold Topology

namespace ContDiffOn

open Set

theorem exists_contDiff_extension_Ici_prod
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ × E → F} {a : ℝ} (hf : ContDiffOn ℝ ∞ f (Ici a ×ˢ univ)) :
    ∃ G : ℝ × E → F, ContDiff ℝ ∞ G ∧ EqOn G f (Ici a ×ˢ univ) := by
  let g : ℝ → E → F := fun t z => f (t + a, z)
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Ici 0 ×ˢ univ) :=
    hf.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn
      (fun q hq => ⟨mem_Ici.mpr (le_add_of_nonneg_left (mem_Ici.mp hq.1)), mem_univ _⟩)
  let C : ℝ × E → Set F := fun q => {v | a ≤ q.1 → v = f q}
  have hC (q : ℝ × E) : Convex ℝ (C q) := by
    rw [convex_iff_add_mem]
    intro u hu v hv s t _ _ hsum hq
    rw [hu hq, hv hq, ← add_smul, hsum, one_smul]
  have hlocal (q₀ : ℝ × E) : ∃ U ∈ 𝓝 q₀, ∃ G : ℝ × E → F,
      ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, F) ∞ G U ∧ ∀ q ∈ U, G q ∈ C q := by
    obtain ⟨gext, V, hV, hgext, hgeq⟩ :=
      DifferentialGeometry.Analysis.borel_halfLine_extend_param
        g univ q₀.2 (by simp) hg
    refine ⟨univ ×ˢ V, prod_mem_nhds (by simp) hV,
      fun q => gext (q.1 - a) q.2, ?_, ?_⟩
    · apply contMDiffOn_iff_contDiffOn.mpr
      exact hgext.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn
        (fun _ hq => ⟨mem_univ _, hq.2⟩)
    · intro q hq ha
      change gext (q.1 - a) q.2 = f q
      simpa only [g, sub_add_cancel] using hgeq (q.1 - a) (sub_nonneg.mpr ha) q.2 hq.2
  obtain ⟨G, hG⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    (I := 𝓘(ℝ, ℝ × E)) (n := (⊤ : ℕ∞)) hC hlocal
  exact ⟨G, G.contMDiff.contDiff, fun q hq => hG q (mem_Ici.mp hq.1)⟩

end ContDiffOn
