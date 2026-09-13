import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Quadrant
import DifferentialGeometry.Analysis.Calculus.CompactCutoff
import Mathlib.Geometry.Manifold.Instances.Real
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.BorelHalfLineParam
import Mathlib.Geometry.Manifold.PartitionOfUnity

open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Analysis

open Set Filter

private theorem exists_contDiff_extension_strip_local_of_lt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b c : ℝ} {f : ℝ × (ℝ × E) → F} {U : Set (ℝ × (ℝ × E))}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ (Ici c ×ˢ univ)) ∩ U))
    {x : ℝ × (ℝ × E)} (hx : x ∈ U) (hxb : x.1 < b) :
    ∃ G : ℝ × (ℝ × E) → F, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[Icc a b ×ˢ (Ici c ×ˢ univ)] x] f := by
  let W : Set (ℝ × (ℝ × E)) := U ∩ {q | q.1 < b}
  have hW : IsOpen W := hU.inter (isOpen_lt continuous_fst continuous_const)
  have hread : ContDiffOn ℝ ∞ f ((Ici a ×ˢ (Ici c ×ˢ univ)) ∩ W) :=
    hf.mono (fun _ hq => ⟨⟨⟨hq.1.1, hq.2.2.le⟩, hq.1.2⟩, hq.2.1⟩)
  obtain ⟨g, hg, -, hgeq⟩ := exists_contDiffOn_cutoff_extension hW hread
    (show x ∈ W from ⟨hx, hxb⟩)
  obtain ⟨G, hG, hGg⟩ := hg.exists_contDiff_extension_quadrant
  refine ⟨G, hG, ?_⟩
  filter_upwards [self_mem_nhdsWithin, hgeq.filter_mono nhdsWithin_le_nhds] with q hq heq
  exact (hGg ⟨hq.1.1, hq.2⟩).trans heq

private theorem exists_contDiff_extension_strip_local
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b c : ℝ} (hab : a < b) {f : ℝ × (ℝ × E) → F} {U : Set (ℝ × (ℝ × E))}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ (Ici c ×ˢ univ)) ∩ U))
    {x : ℝ × (ℝ × E)} (hx : x ∈ U) :
    ∃ G : ℝ × (ℝ × E) → F, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[Icc a b ×ˢ (Ici c ×ˢ univ)] x] f := by
  by_cases hxb : x.1 < b
  · exact exists_contDiff_extension_strip_local_of_lt hU hf hx hxb
  · let σ : ℝ × (ℝ × E) → ℝ × (ℝ × E) := fun q => (-q.1, q.2)
    have hσ : ContDiff ℝ ∞ σ := contDiff_fst.neg.prodMk contDiff_snd
    have hread : ContDiffOn ℝ ∞ (f ∘ σ)
        ((Icc (-b) (-a) ×ˢ (Ici c ×ˢ univ)) ∩ (σ ⁻¹' U)) := by
      apply hf.comp hσ.contDiffOn
      intro q hq
      exact ⟨⟨⟨by dsimp [σ]; linarith [hq.1.1.2],
        by dsimp [σ]; linarith [hq.1.1.1]⟩, hq.1.2⟩, hq.2⟩
    obtain ⟨G, hG, hGeq⟩ := exists_contDiff_extension_strip_local_of_lt
      (hU.preimage hσ.continuous) hread
      (show σ x ∈ σ ⁻¹' U by simpa only [σ, mem_preimage, neg_neg] using hx)
      (show (σ x).1 < -a by dsimp [σ]; linarith)
    refine ⟨G ∘ σ, hG.comp hσ, ?_⟩
    have ht : Tendsto σ (𝓝[Icc a b ×ˢ (Ici c ×ˢ univ)] x)
        (𝓝[Icc (-b) (-a) ×ˢ (Ici c ×ˢ univ)] σ x) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hσ.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact ⟨⟨by dsimp [σ]; linarith [hq.1.2],
        by dsimp [σ]; linarith [hq.1.1]⟩, hq.2⟩
    filter_upwards [hGeq.comp_tendsto ht] with q hq
    simpa only [Function.comp_apply, σ, neg_neg] using hq

private theorem exists_contDiff_extension_Icc_halfspace_local
    {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b : ℝ} (hab : a < b)
    {f : ℝ × EuclideanSpace ℝ (Fin (d + 1)) → F}
    {U : Set (ℝ × EuclideanSpace ℝ (Fin (d + 1)))} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f ((Icc a b ×ˢ range (𝓡∂ (d + 1))) ∩ U))
    {x : ℝ × EuclideanSpace ℝ (Fin (d + 1))} (hx : x ∈ U) :
    ∃ G : ℝ × EuclideanSpace ℝ (Fin (d + 1)) → F, ContDiff ℝ ∞ G ∧
      G =ᶠ[𝓝[Icc a b ×ˢ range (𝓡∂ (d + 1))] x] f := by
  let κ : (ℝ × (Fin d → ℝ)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1)) :=
    (Fin.consEquivL ℝ (fun _ : Fin (d + 1) => ℝ)).trans
      (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm
  have hκzero (z : ℝ × (Fin d → ℝ)) : κ z 0 = z.1 := by simp [κ]
  let k : ℝ × (ℝ × (Fin d → ℝ)) → ℝ × EuclideanSpace ℝ (Fin (d + 1)) :=
    fun q => (q.1, κ q.2)
  let j : ℝ × EuclideanSpace ℝ (Fin (d + 1)) → ℝ × (ℝ × (Fin d → ℝ)) :=
    fun q => (q.1, κ.symm q.2)
  have hk : ContDiff ℝ ∞ k := contDiff_fst.prodMk (κ.contDiff.comp contDiff_snd)
  have hj : ContDiff ℝ ∞ j := contDiff_fst.prodMk (κ.symm.contDiff.comp contDiff_snd)
  have hkj (q : ℝ × EuclideanSpace ℝ (Fin (d + 1))) : k (j q) = q := by
    change (q.1, κ (κ.symm q.2)) = q
    rw [κ.apply_symm_apply]
  have hread : ContDiffOn ℝ ∞ (f ∘ k)
      ((Icc a b ×ˢ (Ici 0 ×ˢ univ)) ∩ (k ⁻¹' U)) := by
    apply hf.comp hk.contDiffOn
    intro q hq
    refine ⟨⟨hq.1.1, ?_⟩, hq.2⟩
    rw [range_modelWithCornersEuclideanHalfSpace]
    change 0 ≤ κ q.2 0
    rw [hκzero]
    exact mem_Ici.mp hq.1.2.1
  obtain ⟨G, hG, hGeq⟩ := exists_contDiff_extension_strip_local hab
    (hU.preimage hk.continuous) hread (show j x ∈ k ⁻¹' U by rwa [mem_preimage, hkj])
  refine ⟨G ∘ j, hG.comp hj, ?_⟩
  have ht : Tendsto j (𝓝[Icc a b ×ˢ range (𝓡∂ (d + 1))] x)
      (𝓝[Icc a b ×ˢ (Ici (0 : ℝ) ×ˢ univ)] j x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hj.continuous.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with q hq
    refine ⟨hq.1, mem_Ici.mpr ?_, mem_univ _⟩
    change 0 ≤ (κ.symm q.2).1
    rw [← hκzero _, κ.apply_symm_apply]
    simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hq.2
  filter_upwards [hGeq.comp_tendsto ht] with q hq
  simpa only [Function.comp_apply, hkj] using hq

end DifferentialGeometry.Analysis

namespace Manifold

open Set

private theorem exists_contMDiff_extension_Icc_of_local
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × M → F} {a b : ℝ}
    (hlocal : ∀ q₀ : ℝ × M, ∃ U ∈ 𝓝 q₀, ∃ G : ℝ × M → F,
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ G U ∧
        ∀ q ∈ U, q.1 ∈ Icc a b → G q = f q) :
    ∃ G : ℝ × M → F, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ G ∧
      EqOn G f (Icc a b ×ˢ univ) := by
  let C : ℝ × M → Set F := fun q => {v | q.1 ∈ Icc a b → v = f q}
  have hC (q : ℝ × M) : Convex ℝ (C q) := by
    rw [convex_iff_add_mem]
    intro u hu v hv s t _ _ hsum hq
    rw [hu hq, hv hq, ← add_smul, hsum, one_smul]
  obtain ⟨G, hG⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    (I := 𝓘(ℝ, ℝ).prod I) (n := (⊤ : ℕ∞)) hC hlocal
  exact ⟨G, G.contMDiff, fun q hq => hG q hq.1⟩

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
  apply exists_contMDiff_extension_Icc_of_local
  intro q₀
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

namespace Manifold

open Set Filter

section

variable {d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private theorem exists_contMDiff_extension_Icc_halfspace_of_lt
    {f : ℝ × M → F} {a b : ℝ} (hab : a < b)
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ f (Icc a b ×ˢ univ)) :
    ∃ G : ℝ × M → F, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ G ∧
      EqOn G f (Icc a b ×ˢ univ) := by
  apply exists_contMDiff_extension_Icc_of_local
  intro q₀
  let I := 𝓡∂ (d + 1)
  let x := q₀.2
  let A : Set (EuclideanSpace ℝ (Fin (d + 1))) :=
    I.symm ⁻¹' (chartAt (EuclideanHalfSpace (d + 1)) x).target
  have hA : IsOpen A :=
    (chartAt (EuclideanHalfSpace (d + 1)) x).open_target.preimage I.continuous_symm
  have hxA : extChartAt I x x ∈ A := by
    have hm := mem_extChartAt_target (I := I) x
    rw [extChartAt_target] at hm
    exact hm.1
  let g : ℝ × EuclideanSpace ℝ (Fin (d + 1)) → F :=
    fun q => f (q.1, (extChartAt I x).symm q.2)
  have hΨ : ContMDiffOn 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin (d + 1)))
      (𝓘(ℝ, ℝ).prod I) ∞
      (fun q : ℝ × EuclideanSpace ℝ (Fin (d + 1)) =>
        (q.1, (extChartAt I x).symm q.2)) (Icc a b ×ˢ (extChartAt I x).target) :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      ((contMDiffOn_extChartAt_symm (I := I) (n := ∞) x).comp
        contDiff_snd.contMDiff.contMDiffOn (fun _ hq => hq.2))
  have hread' : ContDiffOn ℝ ∞ g (Icc a b ×ˢ (extChartAt I x).target) :=
    (hf.comp hΨ (fun _ hq => ⟨hq.1, mem_univ _⟩)).contDiffOn
  have hread : ContDiffOn ℝ ∞ g ((Icc a b ×ˢ range I) ∩ (univ ×ˢ A)) := by
    apply hread'.mono
    intro q hq
    refine ⟨hq.1.1, ?_⟩
    rw [extChartAt_target]
    exact ⟨hq.2.2, hq.1.2⟩
  obtain ⟨G₀, hG₀, hG₀eq⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_extension_Icc_halfspace_local
      hab (isOpen_univ.prod hA) hread
      (show (q₀.1, extChartAt I x x) ∈ univ ×ˢ A from ⟨mem_univ _, hxA⟩)
  let G : ℝ × M → F := fun q => G₀ (q.1, extChartAt I x q.2)
  let D : Set (ℝ × M) := univ ×ˢ (chartAt (EuclideanHalfSpace (d + 1)) x).source
  have hD : IsOpen D :=
    isOpen_univ.prod (chartAt (EuclideanHalfSpace (d + 1)) x).open_source
  have hqD : q₀ ∈ D := ⟨mem_univ _, mem_chart_source (EuclideanHalfSpace (d + 1)) x⟩
  have hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin (d + 1))) ∞
      (fun q : ℝ × M => (q.1, extChartAt I x q.2)) D :=
    contMDiffOn_fst.prodMk_space
      ((contMDiffOn_extChartAt (I := I) (n := ∞) (x := x)).comp
        contMDiffOn_snd (fun _ hq => hq.2))
  have hG : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞ G D :=
    hG₀.contMDiff.comp_contMDiffOn hΦ
  have ht : Tendsto (fun q : ℝ × M => (q.1, extChartAt I x q.2))
      (𝓝[Icc a b ×ˢ univ] q₀) (𝓝[Icc a b ×ˢ range I] (q₀.1, extChartAt I x x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuousAt_fst.prodMk
      ((continuousAt_extChartAt (I := I) x).comp continuousAt_snd)).mono_left
        nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact ⟨hq.1, mem_range_self ((chartAt (EuclideanHalfSpace (d + 1)) x) q.2)⟩
  have hmatch : G =ᶠ[𝓝[Icc a b ×ˢ univ] q₀] f := by
    filter_upwards [hG₀eq.comp_tendsto ht,
      mem_nhdsWithin_of_mem_nhds (hD.mem_nhds hqD)] with q hq hqD
    change G₀ (q.1, extChartAt I x q.2) = f q
    change G₀ (q.1, extChartAt I x q.2) =
      f (q.1, (extChartAt I x).symm (extChartAt I x q.2)) at hq
    rwa [(extChartAt I x).left_inv (by rw [extChartAt_source]; exact hqD.2)] at hq
  have hnear : ∀ᶠ q in 𝓝 q₀, q.1 ∈ Icc a b → G q = f q := by
    filter_upwards [eventually_nhdsWithin_iff.mp hmatch] with q hq htime
    exact hq ⟨htime, mem_univ _⟩
  let B : Set (ℝ × M) := {q | q.1 ∈ Icc a b → G q = f q}
  have hqB : q₀ ∈ interior B := mem_interior_iff_mem_nhds.mpr hnear
  refine ⟨D ∩ interior B, (hD.inter isOpen_interior).mem_nhds ⟨hqD, hqB⟩,
    G, hG.mono inter_subset_left, ?_⟩
  intro q hq htime
  have hqB : q ∈ B := interior_subset hq.2
  exact hqB htime

theorem exists_contMDiff_extension_Icc_halfspace
    {f : ℝ × M → F} {a b : ℝ}
    (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ f (Icc a b ×ˢ univ)) :
    ∃ G : ℝ × M → F, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, F) ∞ G ∧
      EqOn G f (Icc a b ×ˢ univ) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact exists_contMDiff_extension_Icc_halfspace_of_lt hab hf
  · subst b
    have hslice : ContMDiff (𝓡∂ (d + 1)) 𝓘(ℝ, F) ∞ (fun x => f (a, x)) := by
      rw [← contMDiffOn_univ]
      exact hf.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
        (fun x _ => ⟨⟨le_rfl, le_rfl⟩, mem_univ x⟩)
    refine ⟨fun q => f (a, q.2), hslice.comp contMDiff_snd, ?_⟩
    intro q hq
    change f (a, q.2) = f (q.1, q.2)
    rw [show q.1 = a from le_antisymm hq.1.2 hq.1.1]
  · refine ⟨0, contMDiff_const, ?_⟩
    simp only [Icc_eq_empty_of_lt hab, empty_prod, eqOn_empty]

end

end Manifold
