import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.FamilyIsotopyStage

/-!
# CP1-D5: isotopy extension for finitely many families with pairwise disjoint images

For a finite family of jointly smooth families of embeddings `F i : ℝ × N i → M` of compact sets
`K i`, such that for each time the images `F i (t, K i)` are pairwise disjoint, one ambient
isotopy carries all of them simultaneously (needed for the several cores of CP1-D4).
-/

set_option autoImplicit false
open scoped Manifold ContDiff Topology
open Set Function Filter Bundle DifferentialGeometry.Analysis.ODE
noncomputable section
namespace GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem add_section_contMDiffWithinAt_CPD5
    (X Y : ℝ → ∀ x : M, TangentSpace I x)
    {u : Set (ℝ × M)} {q₀ : ℝ × M}
    (hX : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2) : TangentBundle I M)) u q₀)
    (hY : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (Y q.1 q.2) : TangentBundle I M)) u q₀) :
    ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E)) ∞
      (fun q : ℝ × M => (TotalSpace.mk' E q.2 (X q.1 q.2 + Y q.1 q.2) : TangentBundle I M))
      u q₀ := by
  rw [Bundle.contMDiffWithinAt_totalSpace] at hX hY ⊢
  obtain ⟨hXproj, hXfib⟩ := hX
  obtain ⟨-, hYfib⟩ := hY
  refine ⟨hXproj, ?_⟩
  set e := trivializationAt E (TangentSpace I) (q₀.2) with he
  have hfib := hXfib.add hYfib
  have hbase : ContinuousWithinAt (fun q : ℝ × M => q.2) u q₀ :=
    continuous_snd.continuousWithinAt
  have hmem : e.baseSet ∈ 𝓝 (q₀.2) :=
    e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' q₀.2)
  have hpre : (fun q : ℝ × M => q.2) ⁻¹' e.baseSet ∈ 𝓝[u] q₀ := hbase hmem
  refine hfib.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hpre] with x hx
    simpa using (e.linear ℝ hx).1 (X x.1 x.2) (Y x.1 x.2)
  · simpa using
      (e.linear ℝ (FiberBundle.mem_baseSet_trivializationAt' q₀.2)).1 (X q₀.1 q₀.2) (Y q₀.1 q₀.2)

omit [FiniteDimensional ℝ E] [I.Boundaryless] in
theorem contMDiff_finset_sum_section_CPD5 {ι : Type*} [DecidableEq ι]
    (Z : ι → ℝ → ∀ x : M, TangentSpace I x)
    (hZ : ∀ i, ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun q : ℝ × M => (⟨q.2, Z i q.1 q.2⟩ : TangentBundle I M))) (s : Finset ι) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun q : ℝ × M => (⟨q.2, ∑ i ∈ s, Z i q.1 q.2⟩ : TangentBundle I M)) := by
  induction s using Finset.induction_on with
  | empty =>
    have h0 : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
        (fun q : ℝ × M => (⟨q.2, (0 : TangentSpace I q.2)⟩ : TangentBundle I M)) :=
      (Bundle.contMDiff_zeroSection ℝ (TangentSpace I (M := M))).comp contMDiff_snd
    simp only [Finset.sum_empty]
    exact h0
  | insert j s hj ih =>
    intro q
    have h := add_section_contMDiffWithinAt_CPD5 (I := I) (Z j) (fun t y => ∑ i ∈ s, Z i t y)
      (u := univ) (q₀ := q) (hZ j q).contMDiffWithinAt (ih q).contMDiffWithinAt
    simp only [Finset.sum_insert hj]
    exact contMDiffWithinAt_univ.mp h

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → Type*}
  [∀ i, TopologicalSpace (N i)] [∀ i, ChartedSpace H (N i)] [∀ i, IsManifold I ∞ (N i)]

theorem exists_field_multi_CPD5 [T2Space M] [SigmaCompactSpace M]
    {F : ∀ i, ℝ × N i → M} {J : Set ℝ} {U : ∀ i, Set (N i)} (hJ : IsOpen J)
    (hU : ∀ i, IsOpen (U i))
    {K : ∀ i, Set (N i)} (hK : ∀ i, IsCompact (K i)) (hKU : ∀ i, K i ⊆ U i) {c d : ℝ}
    (hJcd : Icc c d ⊆ J)
    (hF : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (F i) (J ×ˢ U i))
    (himm : ∀ i, ∀ t ∈ J, ∀ x ∈ U i, Function.Injective (mfderiv I I (fun y => F i (t, y)) x))
    (hinj : ∀ i, ∀ t ∈ J, InjOn (fun y => F i (t, y)) (K i))
    (hdisj : ∀ i j, i ≠ j → ∀ t ∈ Icc c d, ∀ x ∈ K i, ∀ x' ∈ K j, F i (t, x) ≠ F j (t, x')) :
    ∃ (W : ℝ → ∀ y : M, TangentSpace I y) (C : Set M), IsCompact C ∧
      ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ∞
        (fun q : ℝ × M => (⟨q.2, W q.1 q.2⟩ : TangentBundle I M)) ∧
      (∀ s y, y ∉ C → W s y = 0) ∧
      ∀ i, ∀ s ∈ Icc c d, ∀ x ∈ K i,
        W s (F i (s, x)) = mfderiv (𝓘(ℝ, ℝ).prod I) I (F i) (s, x) ((1 : ℝ), (0 : E)) := by
  classical
  choose T X hT hST hXsm hXval using fun i =>
    exists_localField_CPD5 hJ (hU i) (hK i) (hKU i) hJcd (hF i) (himm i) (hinj i)
  let S' : ∀ i, Set (ℝ × M) := fun i => graphMap_CPD5 (F i) '' (Icc c d ×ˢ K i)
  have hS'c : ∀ i, IsCompact (S' i) := fun i => by
    have hGcont : ContinuousOn (graphMap_CPD5 (F i)) (J ×ˢ U i) :=
      (contMDiffOn_fst.prodMk (hF i)).continuousOn
    exact (isCompact_Icc.prod (hK i)).image_of_continuousOn
      (hGcont.mono (prod_mono hJcd (hKU i)))
  have hS'disj : ∀ i j, i ≠ j → ∀ q, q ∈ S' i → q ∉ S' j := by
    rintro i j hij _ ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩ ⟨⟨t', x'⟩, ⟨ht', hx'⟩, h⟩
    have h1 : t' = t := (Prod.ext_iff.mp h).1
    subst h1
    exact hdisj i j hij t' ht x hx x' hx' (Prod.ext_iff.mp h).2.symm
  let A : ι → Set (ℝ × M) := fun i => ⋃ j : {j // j ≠ i}, S' j
  have hAc : ∀ i, IsCompact (A i) := fun i => isCompact_iUnion fun j => hS'c j
  let T' : ι → Set (ℝ × M) := fun i => T i ∩ (A i)ᶜ
  have hT' : ∀ i, IsOpen (T' i) := fun i => (hT i).inter (hAc i).isClosed.isOpen_compl
  have hS'T' : ∀ i, S' i ⊆ T' i := fun i q hq =>
    ⟨hST i hq, fun hA => by
      obtain ⟨⟨j, hj⟩, hqj⟩ := Set.mem_iUnion.mp hA
      exact hS'disj i j (Ne.symm hj) q hq hqj⟩
  choose Z L hLc hLT hZsm hZ0 hZX using fun i =>
    exists_bumpSection_CPD5 (hT' i) (hS'c i) (hS'T' i) ((hXsm i).mono inter_subset_left)
  refine ⟨fun s y => ∑ i, Z i s y, ⋃ i, Prod.snd '' L i,
    isCompact_iUnion fun i => (hLc i).image continuous_snd,
    contMDiff_finset_sum_section_CPD5 Z hZsm Finset.univ, ?_, ?_⟩
  · intro s y hy
    refine Finset.sum_eq_zero fun i _ => hZ0 i s y (fun h => hy (Set.mem_iUnion.mpr ⟨i, _, h, rfl⟩))
  · intro i s hs x hx
    have hq : (s, F i (s, x)) ∈ S' i := ⟨(s, x), ⟨hs, hx⟩, rfl⟩
    change ∑ j, Z j s (F i (s, x)) = _
    rw [Finset.sum_eq_single i]
    · rw [hZX i s (F i (s, x)) hq]
      exact hXval i s hs x hx
    · intro j _ hji
      refine hZ0 j s (F i (s, x)) fun hL => ?_
      exact (hLT j hL).2 (Set.mem_iUnion.mpr ⟨⟨i, Ne.symm hji⟩, hq⟩)
    · exact fun h => absurd (Finset.mem_univ i) h

/-- **Isotopy extension for finitely many smooth families with pairwise disjoint images.** -/
theorem exists_ambient_isotopy_of_smooth_families_CPD5 [T2Space M] [SigmaCompactSpace M]
    {F : ∀ i, ℝ × N i → M} {J : Set ℝ} {U : ∀ i, Set (N i)} (hJ : IsOpen J)
    (hU : ∀ i, IsOpen (U i))
    {K : ∀ i, Set (N i)} (hK : ∀ i, IsCompact (K i)) (hKU : ∀ i, K i ⊆ U i) {a b : ℝ}
    (hab : a ≤ b) (hJab : Icc a b ⊆ J)
    (hF : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (F i) (J ×ˢ U i))
    (himm : ∀ i, ∀ t ∈ J, ∀ x ∈ U i, Function.Injective (mfderiv I I (fun y => F i (t, y)) x))
    (hinj : ∀ i, ∀ t ∈ J, InjOn (fun y => F i (t, y)) (K i))
    (hdisj : ∀ i j, i ≠ j → ∀ t ∈ J, ∀ x ∈ K i, ∀ x' ∈ K j, F i (t, x) ≠ F j (t, x')) :
    ∃ (Φ : ℝ → ℝ → M → M) (C : Set M), IsCompact C ∧
      ContMDiff ((𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod I) I ∞
        (fun q : (ℝ × ℝ) × M => Φ q.1.1 q.1.2 q.2) ∧
      (∀ s y, Φ s s y = y) ∧ (∀ s t u y, Φ t u (Φ s t y) = Φ s u y) ∧
      (∀ s t y, y ∉ C → Φ s t y = y) ∧
      ∀ i, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ x ∈ K i, Φ s t (F i (s, x)) = F i (t, x) := by
  obtain ⟨δ, hδ, hJ2⟩ := exists_thickening_Icc_subset_CPD5 hJ hab hJab
  obtain ⟨W, C, hCc, hWsm, hWsupp, hWF⟩ := exists_field_multi_CPD5 hJ hU hK hKU
    (c := a - 2 * δ) (d := b + 2 * δ) hJ2 hF himm hinj
    (fun i j hij t ht => hdisj i j hij t (hJ2 ht))
  obtain ⟨Φ, h1, h2, h3, h4, h5⟩ := exists_flow_of_reparamField_CPD5 W hCc hWsm hWsupp
    (contDiff_timeReparam_CPD5 a b δ)
  refine ⟨Φ, C, hCc, h1, h2, h3, h4, ?_⟩
  intro i s hs t ht x hx
  have := h5 (fun τ => F i (timeReparam_CPD5 a b δ τ, x))
    (fun τ => hasMFDerivAt_reparamCurve_CPD5 hJ (hU i) hδ hab hJ2 (hF i) (hKU i hx) W
      (fun s hs => hWF i s hs x hx) τ) s t
  simpa [timeReparam_eq_self_CPD5 hδ hs, timeReparam_eq_self_CPD5 hδ ht] using this.symm

/-- **Interface for CP1-D4, finitely many cores simultaneously.** -/
theorem exists_ambient_homeo_of_smooth_families_CPD5 [T2Space M] [SigmaCompactSpace M]
    {F : ∀ i, ℝ × N i → M} {J : Set ℝ} {U : ∀ i, Set (N i)} (hJ : IsOpen J)
    (hU : ∀ i, IsOpen (U i))
    {K : ∀ i, Set (N i)} (hK : ∀ i, IsCompact (K i)) (hKU : ∀ i, K i ⊆ U i) {a b : ℝ}
    (hab : a ≤ b) (hJab : Icc a b ⊆ J)
    (hF : ∀ i, ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ (F i) (J ×ˢ U i))
    (himm : ∀ i, ∀ t ∈ J, ∀ x ∈ U i, Function.Injective (mfderiv I I (fun y => F i (t, y)) x))
    (hinj : ∀ i, ∀ t ∈ J, InjOn (fun y => F i (t, y)) (K i))
    (hdisj : ∀ i j, i ≠ j → ∀ t ∈ J, ∀ x ∈ K i, ∀ x' ∈ K j, F i (t, x) ≠ F j (t, x'))
    {Ys Yt : Type*} [TopologicalSpace Ys] [TopologicalSpace Yt] [T2Space Ys]
    {ιs : M → Ys} {ιt : M → Yt} (hιs : Topology.IsOpenEmbedding ιs) (e : Ys ≃ₜ Yt)
    (he : ∀ p, e (ιs p) = ιt p) (fs : ∀ i, N i → Ys) (ft : ∀ i, N i → Yt) {s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (hfs : ∀ i, ∀ x ∈ K i, fs i x = ιs (F i (s, x)))
    (hft : ∀ i, ∀ x ∈ K i, ft i x = ιt (F i (t, x))) :
    ∃ Φ : Ys ≃ₜ Yt, ∀ i, ∀ x ∈ K i, Φ (fs i x) = ft i x := by
  obtain ⟨Ψ, C, hCc, hsm, hself, hcoc, hsupp, hmap⟩ :=
    exists_ambient_isotopy_of_smooth_families_CPD5 hJ hU hK hKU hab hJab hF himm hinj hdisj
  let ψ : M ≃ₜ M := isotopyHomeo_CPD5 Ψ hsm.continuous hself hcoc s t
  obtain ⟨ψ', hψ', -⟩ := exists_homeo_extension_CPD5 hιs hCc ψ (fun x hx => hsupp s t x hx)
  refine ⟨ψ'.trans e, fun i x hx => ?_⟩
  change e (ψ' (fs i x)) = ft i x
  rw [hfs i x hx, hψ', he, hft i x hx]
  exact congrArg ιt (hmap i s hs t ht x hx)

end GC.LongTime.CuspP1
