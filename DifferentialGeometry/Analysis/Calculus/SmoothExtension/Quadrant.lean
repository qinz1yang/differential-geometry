import DifferentialGeometry.Analysis.Calculus.SmoothExtension.HalfSpace
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.JetGluing.Parametric
import DifferentialGeometry.Analysis.Calculus.Cutoff.Compact
import Mathlib.Geometry.Manifold.PartitionOfUnity

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis

open Set Filter

private theorem exists_contDiff_extension_quadrant_local
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ℝ × (ℝ × E) → F}
    (hf : ContDiffOn ℝ ∞ f (Ici 0 ×ˢ (Ici 0 ×ˢ univ))) (z₀ : ℝ × E) :
    ∃ W : Set (ℝ × E), W ∈ 𝓝 z₀ ∧ ∃ G : ℝ × (ℝ × E) → F,
      ContDiff ℝ ∞ G ∧ EqOn G f (Ici 0 ×ˢ ((Ici 0 ×ˢ univ) ∩ W)) := by
  classical
  let V : Set (ℝ × E) := Ici 0 ×ˢ univ
  let j : ℕ → (ℝ × E) → F := fun n z =>
    iteratedDerivWithin n (fun t => f (t, z)) (Ici 0) 0
  have hj (n : ℕ) : ContDiffOn ℝ ∞ (j n) V :=
    (contDiffOn_iteratedDerivWithin_fst_Ici hf n).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun _ hz => ⟨self_mem_Ici, hz⟩)
  choose B hB hBj using fun n => (hj n).exists_contDiff_extension_Ici_prod
  obtain ⟨ρ, hρ, hρsupp, hρone, _, _⟩ := exists_bump_compact
    (K := {z₀}) (U := univ) isCompact_singleton isOpen_univ (subset_univ _)
  have hρone' : ρ =ᶠ[𝓝 z₀] 1 := by simpa only [nhdsSet_singleton] using hρone
  let W : Set (ℝ × E) := {z | ρ z = 1}
  have hW : W ∈ 𝓝 z₀ := hρone'
  let a : ℕ → (ℝ × E) → F := fun n z => ρ z • B n z
  have ha (n : ℕ) : ContDiff ℝ ∞ (a n) := hρ.smul (hB n)
  have hasupp (n : ℕ) : HasCompactSupport (a n) := hρsupp.smul_right
  obtain ⟨Φ, hΦ, hΦjet⟩ := exists_contDiff_iteratedDeriv_fst_eq a ha hasupp
  let h : ℝ × (ℝ × E) → F := fun q => ρ q.2 • f q
  have hh : ContDiffOn ℝ ∞ h (Ici 0 ×ˢ V) :=
    (hρ.comp contDiff_snd).contDiffOn.smul hf
  have hjmatch (n : ℕ) (z : ℝ × E) (hz : z ∈ V) :
      iteratedDerivWithin n (fun t => Φ (t, z)) (Iic 0) 0 =
        iteratedDerivWithin n (fun t => h (t, z)) (Ici 0) 0 := by
    have hΦslice : ContDiff ℝ ∞ (fun t => Φ (t, z)) :=
      hΦ.comp (contDiff_id.prodMk contDiff_const)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Iic 0)
      (hΦslice.of_le (by exact_mod_cast le_top)).contDiffAt self_mem_Iic, hΦjet]
    change ρ z • B n z =
      iteratedDerivWithin n (fun t => ρ z • f (t, z)) (Ici 0) 0
    rw [iteratedDerivWithin_fun_const_smul_field, hBj n hz]
  have hVclo : V ⊆ closure (interior V) := by
    intro q hq
    simpa only [V, interior_prod_eq, interior_Ici, interior_univ, closure_prod_eq,
      closure_Ioi, closure_univ] using hq
  let H : ℝ × (ℝ × E) → F := fun q => if q.1 ≤ 0 then Φ q else h q
  have hH : ContDiffOn ℝ ∞ H (univ ×ˢ V) :=
    SmoothExtension.contDiffOn_glue_of_jet_param_of_uniqueDiffOn
      ((uniqueDiffOn_Ici 0).prod uniqueDiffOn_univ) hVclo Φ h
      hΦ.contDiffOn hh hjmatch
  have hHeq : EqOn H h (Ici 0 ×ˢ V) := by
    intro q hq
    change (if q.1 ≤ 0 then Φ q else h q) = h q
    split_ifs with hq0
    · have ht : q.1 = 0 := le_antisymm hq0 (mem_Ici.mp hq.1)
      have hzero := hjmatch 0 q.2 hq.2
      simpa only [iteratedDerivWithin_zero, ← ht] using hzero
    · rfl
  let σ : ℝ × (ℝ × E) → ℝ × (ℝ × E) := fun q => (q.2.1, (q.1, q.2.2))
  have hσ : ContDiff ℝ ∞ σ :=
    contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd)
  have hswap : ContDiffOn ℝ ∞ (H ∘ σ) (Ici 0 ×ˢ univ) :=
    hH.comp hσ.contDiffOn (fun _ hq => ⟨mem_univ _, hq.1, mem_univ _⟩)
  obtain ⟨G, hG, hGeq⟩ := hswap.exists_contDiff_extension_Ici_prod
  refine ⟨W, hW, G ∘ σ, hG.comp hσ, ?_⟩
  intro q hq
  have hsq : σ q ∈ (Ici 0 ×ˢ (univ : Set (ℝ × E))) := ⟨hq.2.1.1, mem_univ _⟩
  change G (σ q) = f q
  rw [hGeq hsq]
  change H q = f q
  rw [hHeq ⟨hq.1, hq.2.1⟩]
  change ρ q.2 • f q = f q
  rw [show ρ q.2 = 1 from hq.2.2, one_smul]

end DifferentialGeometry.Analysis

namespace ContDiffOn

open Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem exists_contDiff_extension_quadrant_zero
    {f : ℝ × (ℝ × E) → F} (hf : ContDiffOn ℝ ∞ f (Ici 0 ×ˢ (Ici 0 ×ˢ univ))) :
    ∃ G : ℝ × (ℝ × E) → F, ContDiff ℝ ∞ G ∧ EqOn G f (Ici 0 ×ˢ (Ici 0 ×ˢ univ)) := by
  let C : ℝ × (ℝ × E) → Set F := fun q =>
    {v | q ∈ (Ici 0 ×ˢ (Ici 0 ×ˢ univ)) → v = f q}
  have hC (q : ℝ × (ℝ × E)) : Convex ℝ (C q) := by
    rw [convex_iff_add_mem]
    intro u hu v hv s t _ _ hsum hq
    rw [hu hq, hv hq, ← add_smul, hsum, one_smul]
  have hlocal (q₀ : ℝ × (ℝ × E)) : ∃ U ∈ 𝓝 q₀, ∃ G : ℝ × (ℝ × E) → F,
      ContMDiffOn 𝓘(ℝ, ℝ × (ℝ × E)) 𝓘(ℝ, F) ∞ G U ∧ ∀ q ∈ U, G q ∈ C q := by
    obtain ⟨W, hW, G, hG, hGeq⟩ :=
      DifferentialGeometry.Analysis.exists_contDiff_extension_quadrant_local hf q₀.2
    refine ⟨univ ×ˢ W, prod_mem_nhds (by simp) hW, G, ?_, ?_⟩
    · exact contMDiffOn_iff_contDiffOn.mpr hG.contDiffOn
    · intro q hq hqQ
      exact hGeq ⟨hqQ.1, hqQ.2, hq.2⟩
  obtain ⟨G, hG⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    (I := 𝓘(ℝ, ℝ × (ℝ × E))) (n := (⊤ : ℕ∞)) hC hlocal
  exact ⟨G, G.contMDiff.contDiff, fun q hq => hG q hq⟩

theorem exists_contDiff_extension_quadrant
    {f : ℝ × (ℝ × E) → F} {a b : ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ici a ×ˢ (Ici b ×ˢ univ))) :
    ∃ G : ℝ × (ℝ × E) → F, ContDiff ℝ ∞ G ∧ EqOn G f (Ici a ×ˢ (Ici b ×ˢ univ)) := by
  let g : ℝ × (ℝ × E) → F := fun q => f (q.1 + a, (q.2.1 + b, q.2.2))
  have hg : ContDiffOn ℝ ∞ g (Ici 0 ×ˢ (Ici 0 ×ˢ univ)) :=
    hf.comp ((contDiff_fst.add contDiff_const).prodMk
      ((contDiff_snd.fst.add contDiff_const).prodMk contDiff_snd.snd)).contDiffOn
      (fun q hq => ⟨mem_Ici.mpr (le_add_of_nonneg_left (mem_Ici.mp hq.1)),
        mem_Ici.mpr (le_add_of_nonneg_left (mem_Ici.mp hq.2.1)), mem_univ _⟩)
  obtain ⟨G, hG, hGeq⟩ := exists_contDiff_extension_quadrant_zero hg
  refine ⟨fun q => G (q.1 - a, (q.2.1 - b, q.2.2)), ?_, ?_⟩
  · exact hG.comp ((contDiff_fst.sub contDiff_const).prodMk
      ((contDiff_snd.fst.sub contDiff_const).prodMk contDiff_snd.snd))
  · intro q hq
    have hmem : (q.1 - a, (q.2.1 - b, q.2.2)) ∈
        (Ici (0 : ℝ) ×ˢ (Ici (0 : ℝ) ×ˢ (univ : Set E))) :=
      ⟨mem_Ici.mpr (sub_nonneg.mpr (mem_Ici.mp hq.1)),
        mem_Ici.mpr (sub_nonneg.mpr (mem_Ici.mp hq.2.1)), mem_univ _⟩
    simpa only [g, sub_add_cancel] using hGeq hmem

end ContDiffOn
