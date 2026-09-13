import DifferentialGeometry.Topology.Diffeomorph.TimeDependentFlow
import DifferentialGeometry.Topology.Embedding.ParametricVelocity
import DifferentialGeometry.Topology.Embedding.IntervalExtension

open scoped ContDiff Manifold

namespace Manifold

open Set

private theorem timeDependentFlow_eqOn_Icc
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (X : ℝ × V → V) (hX : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    {γ : ℝ → V} {a b : ℝ} (hγ : ContinuousOn γ (Icc a b))
    (hγ' : ∀ t ∈ Ico a b, HasDerivWithinAt γ (X (t, γ t)) (Ici t) t) :
    EqOn (fun t => Diffeomorph.timeDependentFlow X hX hXc a t (γ a)) γ (Icc a b) := by
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hX (by simp)
  have hslice (t : ℝ) : LipschitzWith L (fun x : V => X (t, x)) := by
    simpa only [mul_one, Function.comp_def] using hL.comp (LipschitzWith.prodMk_left t)
  have hflow := Diffeomorph.isIntegralCurve_timeDependentFlow X hX hXc a (γ a)
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
    (fun t _ => (hslice t).lipschitzOnWith)
    (continuous_iff_continuousAt.mpr (fun t => (hflow t).continuousAt)).continuousOn
    (fun t _ => (hflow t).hasDerivWithinAt) (fun _ _ => mem_univ _)
    hγ hγ' (fun _ _ => mem_univ _)
    (by simp only [Diffeomorph.timeDependentFlow_refl, Diffeomorph.coe_refl, id_eq])

theorem exists_contDiff_compact_ambient_isotopy_of_tsupport_image_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {U : Set V} (hU : IsOpen U) (heU : e '' ((Icc a b ×ˢ univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ U) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ U ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  have htrace : (fun q : ℝ × M => (q.1, e q)) ''
      ((Icc a b ×ˢ univ) ∩
        tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ univ ×ˢ U := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨mem_univ _, heU ⟨q, hq, rfl⟩⟩
  obtain ⟨X, hX, hXc, hXU, hXe⟩ :=
    exists_contDiff_compact_velocity_extension_Icc_of_tsupport_image_subset
      he hf (isOpen_univ.prod hU) htrace
  let Φ : ℝ → (V ≃ₘ[ℝ] V) := fun t => Diffeomorph.timeDependentFlow X hX hXc a t
  refine ⟨Φ, (Diffeomorph.contDiff_timeDependentFlow X hX hXc).comp
    (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)),
    (Diffeomorph.contDiff_timeDependentFlow_symm X hX hXc).comp
      (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)),
    Diffeomorph.timeDependentFlow_refl X hX hXc a, ?_,
    Prod.snd '' tsupport X, hXc.image continuous_snd, ?_,
    fun t => Diffeomorph.timeDependentFlow_eqOn_compl_image_tsupport X hX hXc a t⟩
  · intro t ht x
    have hγ : ContDiff ℝ ∞ (fun s => e (s, x)) :=
      (he.comp (contMDiff_id.prodMk contMDiff_const)).contDiff
    have hγ' (s : ℝ) (hs : s ∈ Ico a b) :
        HasDerivWithinAt (fun u => e (u, x)) (X (s, e (s, x))) (Ici s) s := by
      rw [hXe s ⟨hs.1, hs.2.le⟩ x]
      exact (hγ.differentiable (by simp) s).hasDerivAt.hasDerivWithinAt
    have hmatch : Φ t (e (a, x)) = e (t, x) :=
      timeDependentFlow_eqOn_Icc X hX hXc hγ.continuous.continuousOn hγ' ht
    refine ⟨hmatch, ?_⟩
    rw [← hmatch]
    exact (Φ t).symm_apply_apply _
  · rintro _ ⟨q, hq, rfl⟩
    exact (hXU hq).2

theorem exists_contDiff_compact_ambient_isotopy
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {U : Set V} (hU : IsOpen U) (heU : e '' (Icc a b ×ˢ univ) ⊆ U) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ U ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ :=
  exists_contDiff_compact_ambient_isotopy_of_tsupport_image_subset he hf hU
    ((image_mono inter_subset_left).trans heU)

theorem exists_contDiff_compact_ambient_isotopy_eqOn_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {U : Set V} (hU : IsOpen U)
    (heU : e '' ((Icc a b ×ˢ univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ U)
    {D : Set V} (hD : IsClosed D)
    (hDA : Disjoint D (e '' ((Icc a b ×ˢ univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)))) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ U ∧
        (∀ t : ℝ, EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ) ∧
        ∃ W : Set V, IsOpen W ∧ D ⊆ W ∧
          ∀ t : ℝ, EqOn (Φ t) id W ∧ EqOn (Φ t).symm id W := by
  have hactive : e '' ((Icc a b ×ˢ univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ U ∩ Dᶜ := by
    intro z hz
    exact ⟨heU hz, fun hzD => Set.disjoint_left.mp hDA hzD hz⟩
  obtain ⟨Φ, hΦ, hΦi, hΦa, hΦe, S, hS, hSU, hΦS⟩ :=
    exists_contDiff_compact_ambient_isotopy_of_tsupport_image_subset he hf
      (hU.inter hD.isOpen_compl) hactive
  refine ⟨Φ, hΦ, hΦi, hΦa, hΦe, S, hS, hSU.trans inter_subset_left, hΦS,
    Sᶜ, hS.isClosed.isOpen_compl, ?_, hΦS⟩
  intro z hz hzS
  exact (hSU hzS).2 hz

theorem exists_contDiff_compact_ambient_isotopy_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} {a b : ℝ}
    (he : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e (Icc a b ×ˢ univ))
    (hf : ∀ t ∈ Icc a b, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {U : Set V} (hU : IsOpen U) (heU : e '' (Icc a b ×ˢ univ) ⊆ U) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ U ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  by_cases hab : a ≤ b
  · obtain ⟨G, hG, hGemb, hGe⟩ := exists_isSmoothEmbedding_extension_Icc hab he hf
    have hGU : G '' (Icc a b ×ˢ univ) ⊆ U := by
      rintro _ ⟨q, hq, rfl⟩
      rw [hGe hq]
      exact heU ⟨q, hq, rfl⟩
    obtain ⟨Φ, hΦ, hΦi, hΦa, hΦe, hS⟩ :=
      exists_contDiff_compact_ambient_isotopy hG hGemb hU hGU
    refine ⟨Φ, hΦ, hΦi, hΦa, ?_, hS⟩
    intro t ht x
    have hGa : G (a, x) = e (a, x) := hGe ⟨⟨le_rfl, hab⟩, mem_univ x⟩
    have hGt : G (t, x) = e (t, x) := hGe ⟨ht, mem_univ x⟩
    simpa only [hGa, hGt] using hΦe t ht x
  · refine ⟨fun _ => Diffeomorph.refl 𝓘(ℝ, V) V ∞,
      contDiff_snd, contDiff_snd, rfl, ?_, ∅, isCompact_empty, empty_subset U, ?_⟩
    · intro t ht
      exact (hab (ht.1.trans ht.2)).elim
    · exact fun _ => ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end Manifold
