import DifferentialGeometry.Topology.Diffeomorph.TimeDependentFlow
import DifferentialGeometry.Topology.Embedding.RelativeParametricVelocity
import DifferentialGeometry.Topology.Embedding.IntervalExtension

open Set Filter
open scoped ContDiff Manifold Topology

namespace Manifold

private theorem exists_contDiff_compact_ambient_isotopy_eqOn_integralCurve_of_velocity
    {M V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} (he : ∀ x, ContDiff ℝ ∞ (fun t => e (t, x)))
    {a b : ℝ} {O : Set V} (X : ℝ × V → V)
    (hX : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    (hXO : tsupport X ⊆ univ ×ˢ O)
    (hXe : ∀ t ∈ Icc a b, ∀ x, X (t, e (t, x)) = deriv (fun s => e (s, x)) t)
    {W : ℝ × V → V} {C : Set (ℝ × V)} (hXW : EqOn X W C)
    {P : Type*} {γ : P → ℝ → V} {c d : P → ℝ}
    (hγ : ∀ p, ContinuousOn (γ p) (Icc (c p) (d p)))
    (hγ' : ∀ p, ∀ t ∈ Ico (c p) (d p),
      HasDerivWithinAt (γ p) (W (t, γ p t)) (Ici t) t)
    (hγC : ∀ p, ∀ t ∈ Icc (c p) (d p), (t, γ p t) ∈ C) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      (∀ p, ∀ t ∈ Icc (c p) (d p), Φ t ((Φ (c p)).symm (γ p (c p))) = γ p t) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ O ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  let Φ : ℝ → (V ≃ₘ[ℝ] V) := fun t => Diffeomorph.timeDependentFlow X hX hXc a t
  refine ⟨Φ, (Diffeomorph.contDiff_timeDependentFlow X hX hXc).comp
    (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)),
    (Diffeomorph.contDiff_timeDependentFlow_symm X hX hXc).comp
      (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)),
    Diffeomorph.timeDependentFlow_refl X hX hXc a, ?_, ?_,
    Prod.snd '' tsupport X, hXc.image continuous_snd, ?_,
    fun t => Diffeomorph.timeDependentFlow_eqOn_compl_image_tsupport X hX hXc a t⟩
  · intro t ht x
    have he' : ContDiff ℝ ∞ (fun s => e (s, x)) := he x
    have hmatch : Φ t (e (a, x)) = e (t, x) :=
      Diffeomorph.timeDependentFlow_eqOn_Icc X hX hXc he'.continuous.continuousOn
        (fun s hs => by
          rw [hXe s ⟨hs.1, hs.2.le⟩ x]
          exact (he'.differentiable (by simp) s).hasDerivAt.hasDerivWithinAt) ht
    refine ⟨hmatch, ?_⟩
    rw [← hmatch]
    exact (Φ t).symm_apply_apply _
  · intro p t ht
    have hcurve : Diffeomorph.timeDependentFlow X hX hXc (c p) t (γ p (c p)) = γ p t :=
      Diffeomorph.timeDependentFlow_eqOn_Icc X hX hXc (hγ p)
        (fun s hs => by
          rw [hXW (hγC p s ⟨hs.1, hs.2.le⟩)]
          exact hγ' p s hs) ht
    change Diffeomorph.timeDependentFlow X hX hXc a t
      ((Diffeomorph.timeDependentFlow X hX hXc a (c p)).symm (γ p (c p))) = γ p t
    rw [Diffeomorph.timeDependentFlow_symm]
    exact (congrArg (fun f : V ≃ₘ[ℝ] V => f (γ p (c p)))
      (Diffeomorph.timeDependentFlow_trans X hX hXc (c p) a t)).trans hcurve
  · rintro _ ⟨q, hq, rfl⟩
    exact (hXO hq).2

theorem exists_contDiff_compact_ambient_isotopy_eqOn_integralCurve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} (he : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {O : Set V} (hO : IsOpen O)
    (heO : e '' ((Icc a b ×ˢ univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O)
    {U C : Set (ℝ × V)} (hU : IsOpen U) (hC : IsCompact C)
    (hCU : C ⊆ U ∩ (univ ×ˢ O))
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ t ∈ Icc a b, ∀ x, (t, e (t, x)) ∈ U →
      W (t, e (t, x)) = deriv (fun s => e (s, x)) t)
    {P : Type*} {γ : P → ℝ → V} {c d : P → ℝ}
    (hγ : ∀ p, ContinuousOn (γ p) (Icc (c p) (d p)))
    (hγ' : ∀ p, ∀ t ∈ Ico (c p) (d p),
      HasDerivWithinAt (γ p) (W (t, γ p t)) (Ici t) t)
    (hγC : ∀ p, ∀ t ∈ Icc (c p) (d p), (t, γ p t) ∈ C) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      (∀ p, ∀ t ∈ Icc (c p) (d p), Φ t ((Φ (c p)).symm (γ p (c p))) = γ p t) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ O ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  obtain ⟨X, hX, hXc, hXO, hXe, hXW⟩ :=
    exists_contDiff_compact_velocity_extension_Icc_eq_nhds he hf (isOpen_univ.prod hO)
      (by
        rintro _ ⟨q, hq, rfl⟩
        exact ⟨mem_univ _, heO (mem_image_of_mem e hq)⟩)
      hU hC hCU hW hWe
  exact exists_contDiff_compact_ambient_isotopy_eqOn_integralCurve_of_velocity
    (fun x => (he.comp (contMDiff_id.prodMk contMDiff_const)).contDiff)
    X hX hXc hXO hXe (fun _ hz => hXW.self_of_nhdsSet hz) hγ hγ' hγC

theorem exists_contDiff_compact_ambient_isotopy_Icc_eqOn_integralCurve
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} {a b : ℝ} (hab : a < b)
    (he : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e (Icc a b ×ˢ univ))
    (hf : ∀ t ∈ Icc a b, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {O : Set V} (hO : IsOpen O) (heO : e '' (Icc a b ×ˢ univ) ⊆ O)
    {U C : Set (ℝ × V)} (hU : IsOpen U) (hC : IsCompact C)
    (hCU : C ⊆ U ∩ (univ ×ˢ O))
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ t ∈ Icc a b, ∀ x, (t, e (t, x)) ∈ U →
      HasDerivWithinAt (fun s => e (s, x)) (W (t, e (t, x))) (Icc a b) t)
    {P : Type*} {γ : P → ℝ → V} {c d : P → ℝ}
    (hγ : ∀ p, ContinuousOn (γ p) (Icc (c p) (d p)))
    (hγ' : ∀ p, ∀ t ∈ Ico (c p) (d p),
      HasDerivWithinAt (γ p) (W (t, γ p t)) (Ici t) t)
    (hγC : ∀ p, ∀ t ∈ Icc (c p) (d p), (t, γ p t) ∈ C) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      (∀ p, ∀ t ∈ Icc (c p) (d p), Φ t ((Φ (c p)).symm (γ p (c p))) = γ p t) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ O ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  obtain ⟨G, hG, hGemb, hGe⟩ := exists_isSmoothEmbedding_extension_Icc hab.le he hf
  have hGU : G '' ((Icc a b ×ˢ univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => G (s, q.2)) q.1)) ⊆ O := by
    rintro _ ⟨q, hq, rfl⟩
    rw [hGe hq.1]
    exact heO ⟨q, hq.1, rfl⟩
  have hWG (t : ℝ) (ht : t ∈ Icc a b) (x : M) (hx : (t, G (t, x)) ∈ U) :
      W (t, G (t, x)) = deriv (fun s => G (s, x)) t := by
    have hGfun : ContDiff ℝ ∞ (fun s => G (s, x)) :=
      (hG.comp (contMDiff_id.prodMk contMDiff_const)).contDiff
    have hGet (s : ℝ) (hs : s ∈ Icc a b) : G (s, x) = e (s, x) :=
      hGe ⟨hs, mem_univ x⟩
    have hd := (hWe t ht x (by simpa only [hGet t ht] using hx)).congr_of_mem hGet ht
    rw [← hGet t ht] at hd
    exact (hd.derivWithin (uniqueDiffOn_Icc hab t ht)).symm.trans
      ((hGfun.differentiable (by simp) t).derivWithin (uniqueDiffOn_Icc hab t ht))
  obtain ⟨Φ, hΦ, hΦinv, hΦa, hΦG, hΦγ, hsupport⟩ :=
    exists_contDiff_compact_ambient_isotopy_eqOn_integralCurve hG hGemb hO hGU
      hU hC hCU hW hWG hγ hγ' hγC
  refine ⟨Φ, hΦ, hΦinv, hΦa, ?_, hΦγ, hsupport⟩
  intro t ht x
  have hGa : G (a, x) = e (a, x) := hGe ⟨⟨le_rfl, hab.le⟩, mem_univ x⟩
  have hGt : G (t, x) = e (t, x) := hGe ⟨ht, mem_univ x⟩
  simpa only [hGa, hGt] using hΦG t ht x

theorem exists_contDiff_compact_ambient_isotopy_halfspace_eqOn_integralCurve
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} (he : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ t, IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {a b : ℝ} {O : Set V} (hO : IsOpen O)
    (heO : e '' ((Icc a b ×ˢ univ) ∩
      tsupport (fun q : ℝ × M => deriv (fun s => e (s, q.2)) q.1)) ⊆ O)
    {U C : Set (ℝ × V)} (hU : IsOpen U) (hC : IsCompact C)
    (hCU : C ⊆ U ∩ (univ ×ˢ O))
    {W : ℝ × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ t ∈ Icc a b, ∀ x, (t, e (t, x)) ∈ U →
      W (t, e (t, x)) = deriv (fun s => e (s, x)) t)
    {P : Type*} {γ : P → ℝ → V} {c d : P → ℝ}
    (hγ : ∀ p, ContinuousOn (γ p) (Icc (c p) (d p)))
    (hγ' : ∀ p, ∀ t ∈ Ico (c p) (d p),
      HasDerivWithinAt (γ p) (W (t, γ p t)) (Ici t) t)
    (hγC : ∀ p, ∀ t ∈ Icc (c p) (d p), (t, γ p t) ∈ C) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      (∀ p, ∀ t ∈ Icc (c p) (d p), Φ t ((Φ (c p)).symm (γ p (c p))) = γ p t) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ O ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  obtain ⟨X, hX, hXc, hXO, hXe, hXW⟩ :=
    exists_contDiff_compact_velocity_extension_halfspace_Icc_eq_nhds he hf (isOpen_univ.prod hO)
      (by
        rintro _ ⟨q, hq, rfl⟩
        exact ⟨mem_univ _, heO (mem_image_of_mem e hq)⟩)
      hU hC hCU hW hWe
  exact exists_contDiff_compact_ambient_isotopy_eqOn_integralCurve_of_velocity
    (fun x => (he.comp (contMDiff_id.prodMk contMDiff_const)).contDiff)
    X hX hXc hXO hXe (fun _ hz => hXW.self_of_nhdsSet hz) hγ hγ' hγC


theorem exists_contDiff_compact_ambient_isotopy_Icc_eqOn_integralCurve_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {e : ℝ × M → V} {a b : ℝ} (hab : a < b)
    (he : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, V) ∞ e (Icc a b ×ˢ univ))
    (hf : ∀ t ∈ Icc a b, IsSmoothEmbedding I 𝓘(ℝ, V) ∞ (fun x => e (t, x)))
    {O : Set V} (hO : IsOpen O) (heO : e '' (Icc a b ×ˢ univ) ⊆ O)
    {ι : Type*} {U C : ι → Set (ℝ × V)} (hU : ∀ i, IsOpen (U i))
    (hC : IsCompact (⋃ i, C i)) (hCU : ∀ i, C i ⊆ U i ∩ (univ ×ˢ O))
    (W : ι → ℝ × V → V) (hW : ∀ i, ContDiffOn ℝ ∞ (W i) (U i))
    (hWe : ∀ i, ∀ t ∈ Icc a b, ∀ x, (t, e (t, x)) ∈ U i →
      HasDerivWithinAt (fun s => e (s, x)) (W i (t, e (t, x))) (Icc a b) t)
    (hagree : ∀ i j, EqOn (W i) (W j) (U i ∩ U j))
    {P : ι → Type*} {γ : (i : ι) → P i → ℝ → V} {c d : (i : ι) → P i → ℝ}
    (hγ : ∀ i p, ContinuousOn (γ i p) (Icc (c i p) (d i p)))
    (hγ' : ∀ i p, ∀ t ∈ Ico (c i p) (d i p),
      HasDerivWithinAt (γ i p) (W i (t, γ i p t)) (Ici t) t)
    (hγC : ∀ i p, ∀ t ∈ Icc (c i p) (d i p), (t, γ i p t) ∈ C i) :
    ∃ Φ : ℝ → (V ≃ₘ[ℝ] V),
      ContDiff ℝ ∞ (fun q : ℝ × V => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × V => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, V) V ∞ ∧
      (∀ t ∈ Icc a b, ∀ x, Φ t (e (a, x)) = e (t, x) ∧
        (Φ t).symm (e (t, x)) = e (a, x)) ∧
      (∀ i p, ∀ t ∈ Icc (c i p) (d i p),
        Φ t ((Φ (c i p)).symm (γ i p (c i p))) = γ i p t) ∧
      ∃ S : Set V, IsCompact S ∧ S ⊆ O ∧ ∀ t : ℝ,
        EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  classical
  let X : ℝ × V → V := fun z => if hz : ∃ i, z ∈ U i then W (Classical.choose hz) z else 0
  have hXeq (i : ι) : EqOn X (W i) (U i) := by
    intro z hz
    have hex : ∃ j, z ∈ U j := ⟨i, hz⟩
    dsimp only [X]
    rw [dif_pos hex]
    exact hagree _ i ⟨Classical.choose_spec hex, hz⟩
  have hX : ContDiffOn ℝ ∞ X (⋃ i, U i) := by
    intro z hz
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
    apply ContDiffAt.contDiffWithinAt
    apply ((hW i).contDiffAt ((hU i).mem_nhds hzi)).congr_of_eventuallyEq
    exact eventuallyEq_of_mem ((hU i).mem_nhds hzi) (fun y hy => hXeq i hy)
  have hXe : ∀ t ∈ Icc a b, ∀ x, (t, e (t, x)) ∈ ⋃ i, U i →
      HasDerivWithinAt (fun s => e (s, x)) (X (t, e (t, x))) (Icc a b) t := by
    intro t ht x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [hXeq i hi]
    exact hWe i t ht x hi
  have hCsub : (⋃ i, C i) ⊆ (⋃ i, U i) ∩ (univ ×ˢ O) := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact ⟨mem_iUnion.mpr ⟨i, (hCU i hi).1⟩, (hCU i hi).2⟩
  obtain ⟨Φ, hΦ, hΦi, hΦa, hΦe, hΦγ, hsupport⟩ :=
    exists_contDiff_compact_ambient_isotopy_Icc_eqOn_integralCurve hab he hf hO heO
      (isOpen_iUnion hU) hC hCsub hX hXe
      (γ := fun p : Σ i, P i => γ p.1 p.2) (c := fun p => c p.1 p.2)
      (d := fun p => d p.1 p.2) (fun p => hγ p.1 p.2)
      (fun p t ht => by
        rw [hXeq p.1 (hCU p.1 (hγC p.1 p.2 t ⟨ht.1, ht.2.le⟩)).1]
        exact hγ' p.1 p.2 t ht)
      (fun p t ht => mem_iUnion.mpr ⟨p.1, hγC p.1 p.2 t ht⟩)
  exact ⟨Φ, hΦ, hΦi, hΦa, hΦe, fun i p => hΦγ ⟨i, p⟩, hsupport⟩

end Manifold
