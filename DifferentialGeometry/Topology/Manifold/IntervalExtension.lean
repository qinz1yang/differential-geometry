import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLineParam
import Mathlib.Geometry.Manifold.PartitionOfUnity

open scoped ContDiff Manifold Topology

namespace Manifold

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem exists_contMDiff_extension_Icc_zero
    {f : ℝ × M → F} {T : ℝ} (hT : 0 < T)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ f (Icc 0 T ×ˢ univ)) :
    ∃ G : ℝ × M → F, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ G ∧
      EqOn G f (Icc 0 T ×ˢ univ) := by
  let C : ℝ × M → Set F := fun q => {v | q.1 ∈ Icc 0 T → v = f q}
  have hC (q : ℝ × M) : Convex ℝ (C q) := by
    rw [convex_iff_add_mem]
    intro a ha b hb s t _ _ hsum hq
    rw [ha hq, hb hq, ← add_smul, hsum, one_smul]
  have hlocal (q₀ : ℝ × M) : ∃ U ∈ 𝓝 q₀, ∃ G : ℝ × M → F,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ G U ∧ ∀ q ∈ U, G q ∈ C q := by
    let x := q₀.2
    let g : ℝ → E → F := fun t z => f (t, (extChartAt I x).symm z)
    have hread : ContDiffOn ℝ ∞ (Function.uncurry g)
        (Icc 0 T ×ˢ (extChartAt I x).target) := by
      have hΨ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
          (fun q : ℝ × E => (q.1, (extChartAt I x).symm q.2))
          (Icc 0 T ×ˢ (extChartAt I x).target) :=
        contMDiffOn_fst.prodMk
          ((contMDiffOn_extChartAt_symm (I := I) (n := ∞) x).comp
            contMDiffOn_snd (fun _ hq => hq.2))
      have hcomp := hf.comp hΨ (fun _ hq => ⟨hq.1, mem_univ _⟩)
      rw [← contMDiffOn_iff_contDiffOn, ← chartedSpaceSelf_prod, modelWithCornersSelf_prod]
      exact hcomp
    have hxint : extChartAt I x x ∈ interior (extChartAt I x).target := by
      rw [(isOpen_extChartAt_target (I := I) x).interior_eq]
      exact mem_extChartAt_target x
    obtain ⟨gext, V, hV, hgext, hgeq⟩ :=
      DifferentialGeometry.Analysis.borel_interval_extend_param
        g T hT (extChartAt I x).target (extChartAt I x x) hxint hread
    obtain ⟨W, hWV, hWopen, hxW⟩ := mem_nhds_iff.mp hV
    let U : Set M := (chartAt H x).source ∩ (extChartAt I x) ⁻¹' W
    have hUopen : IsOpen U := by
      have hc : ContinuousOn (extChartAt I x) (chartAt H x).source := by
        rw [← extChartAt_source (I := I) x]
        exact continuousOn_extChartAt x
      exact hc.isOpen_inter_preimage (chartAt H x).open_source hWopen
    have hxU : x ∈ U := ⟨mem_chart_source H x, hxW⟩
    let G : ℝ × M → F := fun q => gext q.1 (extChartAt I x q.2)
    have hgextM : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞
        (Function.uncurry gext) (univ ×ˢ V) := by
      rw [← contMDiffOn_iff_contDiffOn, ← chartedSpaceSelf_prod,
        modelWithCornersSelf_prod] at hgext
      exact hgext
    have hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) ∞
        (fun q : ℝ × M => (q.1, extChartAt I x q.2)) (univ ×ˢ U) :=
      contMDiffOn_fst.prodMk
        ((contMDiffOn_extChartAt (I := I) (n := ∞) (x := x)).comp
          contMDiffOn_snd (fun _ hq => hq.2.1))
    refine ⟨univ ×ˢ U, (isOpen_univ.prod hUopen).mem_nhds ⟨mem_univ _, hxU⟩,
      G, hgextM.comp hΦ (fun _ hq => ⟨mem_univ _, hWV hq.2.2⟩), ?_⟩
    intro q hq ht
    change gext q.1 (extChartAt I x q.2) = f q
    rw [hgeq q.1 ht (extChartAt I x q.2) (hWV hq.2.2)]
    change f (q.1, (extChartAt I x).symm (extChartAt I x q.2)) = f q
    rw [(extChartAt I x).left_inv (by rw [extChartAt_source]; exact hq.2.1)]
  obtain ⟨G, hG⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    (I := 𝓘(ℝ, ℝ).prod I) (n := (⊤ : ℕ∞)) hC hlocal
  exact ⟨G, G.contMDiff, fun q hq => hG q hq.1⟩

theorem exists_contMDiff_extension_Icc
    {f : ℝ × M → F} {a b : ℝ}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ f (Icc a b ×ˢ univ)) :
    ∃ G : ℝ × M → F, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ G ∧
      EqOn G f (Icc a b ×ˢ univ) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · let g : ℝ × M → F := fun q => f (q.1 + a, q.2)
    have hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ g
        (Icc 0 (b - a) ×ˢ univ) := by
      refine hf.comp ((contMDiff_fst.add contMDiff_const).prodMk
        contMDiff_snd).contMDiffOn ?_
      intro q hq
      exact ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ _⟩
    obtain ⟨G, hG, hGe⟩ := exists_contMDiff_extension_Icc_zero (sub_pos.mpr hab) hg
    refine ⟨fun q => G (q.1 - a, q.2),
      hG.comp ((contMDiff_fst.sub contMDiff_const).prodMk contMDiff_snd), ?_⟩
    intro q hq
    have hmem : (q.1 - a, q.2) ∈ Icc 0 (b - a) ×ˢ (univ : Set M) :=
      ⟨⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩, mem_univ _⟩
    simpa only [g, sub_add_cancel] using hGe hmem
  · subst b
    have hslice : ContMDiff I 𝓘(ℝ, F) ∞ (fun x => f (a, x)) := by
      rw [← contMDiffOn_univ]
      exact hf.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
        (fun x _ => ⟨⟨le_rfl, le_rfl⟩, mem_univ x⟩)
    refine ⟨fun q => f (a, q.2), hslice.comp contMDiff_snd, ?_⟩
    intro q hq
    change f (a, q.2) = f (q.1, q.2)
    rw [show q.1 = a from le_antisymm hq.1.2 hq.1.1]
  · refine ⟨0, contMDiff_const, ?_⟩
    simp only [Icc_eq_empty_of_lt hab, empty_prod, eqOn_empty]

end Manifold
