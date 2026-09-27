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

private theorem exists_contDiff_compact_parametric_extension
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M]
    {e : (ℝ × P) × M → V}
    (he : ContMDiff (𝓘(ℝ, ℝ × P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ q, IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (q, x)))
    {v : (ℝ × P) × M → V}
    (hv : ContMDiff (𝓘(ℝ, ℝ × P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ v)
    {a b : ℝ} {J : Set P} (hJ : IsCompact J)
    {O : Set (P × V)} (hO : IsOpen O)
    (heO : ∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x, (p, e ((t, p), x)) ∈ O)
    {U C : Set ((ℝ × P) × V)} (hU : IsOpen U) (hC : IsCompact C)
    (hCU : C ⊆ U ∩ {q | (q.1.2, q.2) ∈ O})
    {W : (ℝ × P) × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x, ((t, p), e ((t, p), x)) ∈ U →
      W ((t, p), e ((t, p), x)) = v ((t, p), x)) :
    ∃ Y : (ℝ × P) × V → V, ContDiff ℝ ∞ Y ∧ HasCompactSupport Y ∧
      tsupport Y ⊆ {q | (q.1.2, q.2) ∈ O} ∧
      (∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x, Y ((t, p), e ((t, p), x)) = v ((t, p), x)) ∧
      Y =ᶠ[𝓝ˢ C] W := by
  let K := (Icc a b ×ˢ J) ×ˢ (univ : Set M)
  have hK : IsCompact K := (isCompact_Icc.prod hJ).prod isCompact_univ
  have hgraph := isSmoothEmbedding_parametric_graph_halfspace he hf
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hgraph
  let O' : Set ((ℝ × P) × V) := {q | (q.1.2, q.2) ∈ O}
  have hO' : IsOpen O' := hO.preimage ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hKO : (fun q : (ℝ × P) × M => (q.1, e q)) '' (K ∩ tsupport v) ⊆ O' := by
    rintro _ ⟨⟨⟨t, p⟩, x⟩, hq, rfl⟩
    exact heO t hq.1.1.1 p hq.1.1.2 x
  obtain ⟨Y, hY, hYc, hYO, hYe, hYW⟩ :=
    hgraph.exists_contDiff_compact_extension_prod_halfspace_eq_nhds hv hK hO' hKO
      hU hC hCU hW (fun q hq => hWe q.1.1 hq.1.1 q.1.2 hq.1.2 q.2)
  exact ⟨Y, hY, hYc, hYO, fun t ht p hp x =>
    hYe (x := ((t, p), x)) ⟨⟨ht, hp⟩, mem_univ x⟩, hYW⟩

private theorem exists_contDiff_compact_parametric_velocity_extension
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M]
    {e : (ℝ × P) × M → V}
    (he : ContMDiff (𝓘(ℝ, ℝ × P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ q, IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (q, x)))
    {k : P → ℝ} (hk : ContDiff ℝ ∞ k) {v : (ℝ × P) × M → V}
    (hv : ContMDiff (𝓘(ℝ, ℝ × P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ v)
    {a b : ℝ} {J : Set P} (hJ : IsCompact J)
    (hve : ∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x,
      deriv (fun r => e ((r, p), x)) t = k p • v ((t, p), x))
    {O : Set (P × V)} (hO : IsOpen O)
    (heO : ∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x, (p, e ((t, p), x)) ∈ O)
    {U C : Set ((ℝ × P) × V)} (hU : IsOpen U) (hC : IsCompact C)
    (hCU : C ⊆ U ∩ {q | (q.1.2, q.2) ∈ O})
    {W : (ℝ × P) × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x, ((t, p), e ((t, p), x)) ∈ U →
      W ((t, p), e ((t, p), x)) = v ((t, p), x)) :
    ∃ X : ℝ × (P × V) → P × V, ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧
      tsupport X ⊆ univ ×ˢ O ∧
      (∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x,
        X (t, (p, e ((t, p), x))) = (0, deriv (fun r => e ((r, p), x)) t)) ∧
      (∀ q ∈ C, X (q.1.1, (q.1.2, q.2)) = (0, k q.1.2 • W q)) ∧
      (∀ q, (X q).1 = 0) ∧ (∀ r x, k x.1 = 0 → X (r, x) = 0) := by
  let A := ContinuousLinearEquiv.prodAssoc ℝ ℝ P V
  obtain ⟨Y, hY, hYc, hYO, hYe, hYW⟩ :=
    exists_contDiff_compact_parametric_extension he hf hv hJ hO heO hU hC hCU hW hWe
  let X : ℝ × (P × V) → P × V := fun q => (0, k q.2.1 • Y (A.symm q))
  have hX : ContDiff ℝ ∞ X := contDiff_const.prodMk
    ((hk.comp contDiff_snd.fst).smul (hY.comp A.symm.contDiff))
  have hYAc : HasCompactSupport (fun q : ℝ × (P × V) => k q.2.1 • Y (A.symm q)) :=
    (hYc.comp_homeomorph A.symm.toHomeomorph).smul_left (f := fun q : ℝ × (P × V) => k q.2.1)
  have hXc : HasCompactSupport X :=
    hYAc.comp_left (show (0, (0 : V)) = (0 : P × V) from rfl)
  have hXO : tsupport X ⊆ univ ×ˢ O := by
    intro q hq
    have hYq : A.symm q ∈ tsupport Y := by
      have hs : tsupport X ⊆ tsupport (fun q => Y (A.symm q)) :=
        (tsupport_comp_subset (g := fun y : V => ((0 : P), y)) rfl
          (fun q : ℝ × (P × V) => k q.2.1 • Y (A.symm q))).trans
          (tsupport_smul_subset_right (fun q : ℝ × (P × V) => k q.2.1)
            (fun q => Y (A.symm q)))
      have hsub := tsupport_comp_subset_preimage (f := A.symm) Y A.symm.continuous
      exact hsub (hs hq)
    exact ⟨mem_univ _, hYO hYq⟩
  have hXe (t : ℝ) (ht : t ∈ Icc a b) (p : P) (hp : p ∈ J) (x : M) :
      X (t, (p, e ((t, p), x))) = (0, deriv (fun r => e ((r, p), x)) t) := by
    have hh := hYe t ht p hp x
    change (0, k p • Y ((t, p), e ((t, p), x))) = _
    rw [hh, hve t ht p hp x]
  have hXW (q : (ℝ × P) × V) (hq : q ∈ C) : X (A q) = (0, k q.1.2 • W q) := by
    change (0, k q.1.2 • Y (A.symm (A q))) = _
    rw [A.symm_apply_apply, hYW.self_of_nhdsSet hq]
  refine ⟨X, hX, hXc, hXO, hXe, hXW, ?_, ?_⟩
  · intro q
    rfl
  · intro r x hx
    simp only [X, hx, zero_smul, Prod.mk_zero_zero]

theorem exists_contDiff_compact_ambient_isotopy_halfspace_parametric_eqOn_integralCurve_of_weighted_velocity
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M]
    {e : (ℝ × P) × M → V}
    (he : ContMDiff (𝓘(ℝ, ℝ × P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ q, IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (q, x)))
    {k : P → ℝ} (hk : ContDiff ℝ ∞ k) {v : (ℝ × P) × M → V}
    (hv : ContMDiff (𝓘(ℝ, ℝ × P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ v)
    {a b : ℝ} {J : Set P} (hJ : IsCompact J)
    (hve : ∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x,
      deriv (fun r => e ((r, p), x)) t = k p • v ((t, p), x))
    {O : Set (P × V)} (hO : IsOpen O)
    (heO : ∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x, (p, e ((t, p), x)) ∈ O)
    {U C : Set ((ℝ × P) × V)} (hU : IsOpen U) (hC : IsCompact C)
    (hCU : C ⊆ U ∩ {q | (q.1.2, q.2) ∈ O})
    {W : (ℝ × P) × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x, ((t, p), e ((t, p), x)) ∈ U →
      W ((t, p), e ((t, p), x)) = v ((t, p), x))
    {Q : Type*} {γ : Q → ℝ → P × V} {c f : Q → ℝ}
    (hγ : ∀ q, ContinuousOn (γ q) (Icc (c q) (f q)))
    (hγ' : ∀ q, ∀ t ∈ Ico (c q) (f q),
      HasDerivWithinAt (γ q) (0, k (γ q t).1 • W ((t, (γ q t).1), (γ q t).2)) (Ici t) t)
    (hγC : ∀ q, ∀ t ∈ Icc (c q) (f q), ((t, (γ q t).1), (γ q t).2) ∈ C) :
    ∃ Φ : ℝ → (P × V) ≃ₘ[ℝ] (P × V),
      ContDiff ℝ ∞ (fun q : ℝ × (P × V) => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × (P × V) => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, P × V) (P × V) ∞ ∧
      (∀ t x, (Φ t x).1 = x.1) ∧
      (∀ t x, k x.1 = 0 → Φ t x = x ∧ (Φ t).symm x = x) ∧
      (∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x,
        Φ t (p, e ((a, p), x)) = (p, e ((t, p), x))) ∧
      (∀ q, ∀ t ∈ Icc (c q) (f q),
        Φ t ((Φ (c q)).symm (γ q (c q))) = γ q t) ∧
      ∃ S : Set (P × V), IsCompact S ∧ S ⊆ O ∧
        ∀ t, EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  obtain ⟨X, hX, hXc, hXO, hXe, hXW, hXp, hXzero⟩ :=
    exists_contDiff_compact_parametric_velocity_extension he hf hk hv hJ hve
      hO heO hU hC hCU hW hWe
  let Φ : ℝ → (P × V) ≃ₘ[ℝ] (P × V) := fun t =>
    Diffeomorph.timeDependentFlow X hX hXc a t
  refine ⟨Φ, (Diffeomorph.contDiff_timeDependentFlow X hX hXc).comp
    (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)),
    (Diffeomorph.contDiff_timeDependentFlow_symm X hX hXc).comp
      (contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)),
    Diffeomorph.timeDependentFlow_refl X hX hXc a, ?_, ?_, ?_, ?_,
    Prod.snd '' tsupport X, hXc.image continuous_snd, ?_,
    fun t => Diffeomorph.timeDependentFlow_eqOn_compl_image_tsupport X hX hXc a t⟩
  · intro t x
    exact Diffeomorph.map_timeDependentFlow_eq_of_map_eq_zero X hX hXc
      (ContinuousLinearMap.fst ℝ P V) hXp a t x
  · intro t x hx
    have hzero (r : ℝ) : X (r, x) = 0 := hXzero r x hx
    refine ⟨Diffeomorph.timeDependentFlow_apply_eq_self_of_forall_eq_zero X hX hXc hzero a t, ?_⟩
    change (Diffeomorph.timeDependentFlow X hX hXc a t).symm x = x
    rw [Diffeomorph.timeDependentFlow_symm]
    exact Diffeomorph.timeDependentFlow_apply_eq_self_of_forall_eq_zero X hX hXc hzero t a
  · intro t ht p hp x
    have hepx : ContDiff ℝ ∞ (fun r => e ((r, p), x)) :=
      (he.comp ((contDiff_id.prodMk contDiff_const).contMDiff.prodMk contMDiff_const)).contDiff
    apply Diffeomorph.timeDependentFlow_eqOn_Icc X hX hXc
      (continuous_const.prodMk hepx.continuous).continuousOn _ ht
    intro r hr
    rw [hXe r (Ico_subset_Icc_self hr) p hp x]
    exact ((hasDerivAt_const r p).prodMk
      ((hepx.differentiable (by simp) r).hasDerivAt)).hasDerivWithinAt
  · intro q t ht
    have hcurve := Diffeomorph.timeDependentFlow_eqOn_Icc X hX hXc (hγ q)
      (fun r hr => by
        have hh := hXW _ (hγC q r (Ico_subset_Icc_self hr))
        change X (r, γ q r) = _ at hh
        rw [hh]
        exact hγ' q r hr) ht
    change Diffeomorph.timeDependentFlow X hX hXc a t
      ((Diffeomorph.timeDependentFlow X hX hXc a (c q)).symm (γ q (c q))) = γ q t
    rw [Diffeomorph.timeDependentFlow_symm]
    exact (congrArg (fun f : (P × V) ≃ₘ[ℝ] (P × V) => f (γ q (c q)))
      (Diffeomorph.timeDependentFlow_trans X hX hXc (c q) a t)).trans hcurve
  · rintro _ ⟨q, hq, rfl⟩
    exact (hXO hq).2

theorem exists_contDiff_compact_ambient_isotopy_halfspace_parametric_eqOn_integralCurve
    {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {d : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (d + 1)) M] [IsManifold (𝓡∂ (d + 1)) ∞ M]
    [CompactSpace M]
    {e : (ℝ × P) × M → V}
    (he : ContMDiff (𝓘(ℝ, ℝ × P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ e)
    (hf : ∀ q, IsSmoothEmbedding (𝓡∂ (d + 1)) 𝓘(ℝ, V) ∞ (fun x => e (q, x)))
    {a b : ℝ} {J : Set P} (hJ : IsCompact J)
    {O : Set (P × V)} (hO : IsOpen O)
    (heO : ∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x, (p, e ((t, p), x)) ∈ O)
    {U C : Set ((ℝ × P) × V)} (hU : IsOpen U) (hC : IsCompact C)
    (hCU : C ⊆ U ∩ {q | (q.1.2, q.2) ∈ O})
    {W : (ℝ × P) × V → V} (hW : ContDiffOn ℝ ∞ W U)
    (hWe : ∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x, ((t, p), e ((t, p), x)) ∈ U →
      W ((t, p), e ((t, p), x)) = deriv (fun r => e ((r, p), x)) t)
    {Q : Type*} {γ : Q → ℝ → P × V} {c f : Q → ℝ}
    (hγ : ∀ q, ContinuousOn (γ q) (Icc (c q) (f q)))
    (hγ' : ∀ q, ∀ t ∈ Ico (c q) (f q),
      HasDerivWithinAt (γ q) (0, W ((t, (γ q t).1), (γ q t).2)) (Ici t) t)
    (hγC : ∀ q, ∀ t ∈ Icc (c q) (f q), ((t, (γ q t).1), (γ q t).2) ∈ C) :
    ∃ Φ : ℝ → (P × V) ≃ₘ[ℝ] (P × V),
      ContDiff ℝ ∞ (fun q : ℝ × (P × V) => Φ q.1 q.2) ∧
      ContDiff ℝ ∞ (fun q : ℝ × (P × V) => (Φ q.1).symm q.2) ∧
      Φ a = Diffeomorph.refl 𝓘(ℝ, P × V) (P × V) ∞ ∧
      (∀ t x, (Φ t x).1 = x.1) ∧
      (∀ t ∈ Icc a b, ∀ p ∈ J, ∀ x,
        Φ t (p, e ((a, p), x)) = (p, e ((t, p), x))) ∧
      (∀ q, ∀ t ∈ Icc (c q) (f q),
        Φ t ((Φ (c q)).symm (γ q (c q))) = γ q t) ∧
      ∃ S : Set (P × V), IsCompact S ∧ S ⊆ O ∧
        ∀ t, EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  let v : (ℝ × P) × M → V := fun q => deriv (fun r => e ((r, q.1.2), q.2)) q.1.1
  have he' : ContMDiff (𝓘(ℝ).prod (𝓘(ℝ, P).prod (𝓡∂ (d + 1)))) 𝓘(ℝ, V) ∞
      (fun q : ℝ × (P × M) => e ((q.1, q.2.1), q.2.2)) := by
    have hpair : ContMDiff (𝓘(ℝ).prod (𝓘(ℝ, P).prod (𝓡∂ (d + 1))))
        (𝓘(ℝ).prod 𝓘(ℝ, P)) ∞ (fun q : ℝ × (P × M) => (q.1, q.2.1)) :=
      contMDiff_fst.prodMk contMDiff_snd.fst
    have hep : ContMDiff ((𝓘(ℝ).prod 𝓘(ℝ, P)).prod (𝓡∂ (d + 1)))
        𝓘(ℝ, V) ∞ e := by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact he
    exact hep.comp (hpair.prodMk contMDiff_snd.snd)
  have hv' : ContMDiff (𝓘(ℝ).prod (𝓘(ℝ, P).prod (𝓡∂ (d + 1)))) 𝓘(ℝ, V) ∞
      (fun q : ℝ × (P × M) => deriv (fun r => e ((r, q.2.1), q.2.2)) q.1) :=
    fun q => DifferentialGeometry.timeDeriv_smoothAt (he' q) (by simp)
  have hv : ContMDiff (𝓘(ℝ, ℝ × P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, V) ∞ v := by
    have hr : ContMDiff (𝓘(ℝ, ℝ × P).prod (𝓡∂ (d + 1))) 𝓘(ℝ) ∞
        (fun q : (ℝ × P) × M => q.1.1) := contDiff_fst.contMDiff.comp contMDiff_fst
    have hp : ContMDiff (𝓘(ℝ, ℝ × P).prod (𝓡∂ (d + 1))) 𝓘(ℝ, P) ∞
        (fun q : (ℝ × P) × M => q.1.2) := contDiff_snd.contMDiff.comp contMDiff_fst
    exact hv'.comp (hr.prodMk (hp.prodMk contMDiff_snd))
  obtain ⟨Φ, hΦ, hΦi, hΦa, hΦp, _, hΦe, hΦγ, hsupport⟩ :=
    exists_contDiff_compact_ambient_isotopy_halfspace_parametric_eqOn_integralCurve_of_weighted_velocity
      he hf (k := fun _ => 1) contDiff_const hv hJ
      (fun t _ p _ x => by simp only [one_smul]; rfl) hO heO hU hC hCU hW hWe hγ
      (fun q t ht => by simpa only [one_smul] using hγ' q t ht) hγC
  exact ⟨Φ, hΦ, hΦi, hΦa, hΦp, hΦe, hΦγ, hsupport⟩


end Manifold
