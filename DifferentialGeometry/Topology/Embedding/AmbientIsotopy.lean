import DifferentialGeometry.Topology.Diffeomorph.TimeDependentFlow
import DifferentialGeometry.Topology.Embedding.ParametricVelocity

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
        EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  have htrace : (fun q : ℝ × M => (q.1, e q)) '' (Icc a b ×ˢ univ) ⊆ univ ×ˢ U := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨mem_univ _, heU ⟨q, hq, rfl⟩⟩
  obtain ⟨X, hX, hXc, hXU, hXe⟩ := exists_contDiff_compact_velocity_extension_Icc
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

end Manifold
