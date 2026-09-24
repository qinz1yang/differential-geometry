import DifferentialGeometry.Topology.LoopSpace.TransversePerturbation
import DifferentialGeometry.Topology.LoopSpace.FiniteSelfIntersections
import DifferentialGeometry.Topology.LoopSpace.ImmersionStability

noncomputable section

open Set Filter Metric Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Topology

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_generic_loop_family_approximation_of_contMDiff
    (hdim : Module.finrank ℝ E = 3)
    (e : M → F) (he : ContMDiff I 𝓘(ℝ, F) ∞ e)
    (hemb : _root_.Topology.IsEmbedding e)
    (heinj : ∀ x, Function.Injective (mfderiv I 𝓘(ℝ, F) e x))
    (c : ℝ × AddCircle (1 : ℝ) → M) {a b : ℝ} (hab : a < b)
    (hc : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) I ∞ c)
    (hi : ∀ x t, t ∈ Icc a b →
      mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => c (t, (y : AddCircle (1 : ℝ)))) x (1 : ℝ) ≠ 0)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ β : ℝ × AddCircle (1 : ℝ) → M,
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) I ∞ β ∧
      (∀ x t, t ∈ Icc a b →
        mfderiv 𝓘(ℝ, ℝ) I (fun y : ℝ => β (t, (y : AddCircle (1 : ℝ)))) x (1 : ℝ) ≠ 0) ∧
      (∃ exceptional : Finset ℝ, ∀ t ∈ Icc a b, t ∉ exceptional →
        _root_.Topology.IsEmbedding (fun z => β (t, z))) ∧
      ∀ m : ℕ, m ≤ n → ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b,
        ‖iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e (β (q.2, (q.1 : AddCircle (1 : ℝ)))))
            (univ ×ˢ Icc a b) p -
          iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e (c (q.2, (q.1 : AddCircle (1 : ℝ)))))
            (univ ×ˢ Icc a b) p‖ < ε := by
  classical
  have hlift {f : ℝ × AddCircle (1 : ℝ) → M}
      (hf : ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) I ∞ f) (J : Set ℝ) :
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞
        (fun p : ℝ × ℝ => f (p.2, (p.1 : AddCircle (1 : ℝ)))) (univ ×ˢ J) := by
    have hcoe : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ).prod 𝓘(ℝ)) ∞
        (fun p : ℝ × ℝ => (p.2, (p.1 : AddCircle (1 : ℝ)))) :=
      contDiff_snd.contMDiff.prodMk (AddCircle.contMDiff_coe.comp contDiff_fst.contMDiff)
    exact (hf.comp hcoe).contMDiffOn
  obtain ⟨η, hη, δ, hδ, hstable⟩ :=
    exists_loop_family_immersion_separation_radius e he heinj c hab (hlift hc _) hi
  let K : Set (ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
    {q | q.1 ∈ Icc a b ∧ δ ≤ dist q.2.1 q.2.2}
  let Z : Set (ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) :=
    {q | q ∈ K ∧ c (q.1, q.2.1) = c (q.1, q.2.2)}
  obtain ⟨t, charts, pairCharts, ρ, U, A, B, hK, hlocal, hcover⟩ :=
    DifferentialGeometry.Manifold.exists_finite_loop_family_coincidence_cover (a := a) (b := b) hc hδ
  change IsCompact K at hK
  change Z ⊆ ⋃ i ∈ t, interior (A i) at hcover
  choose hρ hρcompact hρbound hU hUi hUcompact hA hAU hpairCharts hB hsupp hlB hrB hBchart hcut using hlocal
  let W := ⋃ i ∈ t, interior (A i)
  have hW : IsOpen W := isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_interior
  let l : (ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) → ℝ × AddCircle (1 : ℝ) :=
    fun q => (q.1, q.2.1)
  let r : (ℝ × AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) → ℝ × AddCircle (1 : ℝ) :=
    fun q => (q.1, q.2.2)
  have hl : Continuous l := continuous_fst.prodMk continuous_snd.fst
  have hr : Continuous r := continuous_fst.prodMk continuous_snd.snd
  obtain ⟨ζ, hζ, hnocollision⟩ := DifferentialGeometry.Topology.exists_pos_coincidence_subset_of_comp_injective
    hK hW hc.continuous he.continuous hemb.injective hl hr
      (fun q hq heq => hcover ⟨hq, heq⟩)
  let ι := {i // i ∈ t}
  have hfootprint : IsCompact (l '' K ∪ r '' K) := (hK.image hl).union (hK.image hr)
  obtain ⟨β, hβ, _, hβclose, hβjets, hβtrans⟩ :=
    DifferentialGeometry.Manifold.exists_loop_family_perturbation_transverse_on_finite_union
      hdim e he hemb.isInducing
      (ι := ι) (fun i => charts i.1) (fun i => pairCharts i.1) (fun i => ρ i.1)
      (fun i => U i.1) (fun i => A i.1) (fun i => B i.1)
      (fun i => hρ i.1) (fun i => hρcompact i.1)
      (fun i p => by rw [Real.norm_of_nonneg (hρbound i.1 p).1]; exact (hρbound i.1 p).2)
      (fun i => hU i.1) (fun i => hA i.1)
      (fun i p hp => ⟨hAU i.1 hp, hpairCharts i.1 (subset_closure (hAU i.1 hp))⟩)
      (fun i => hB i.1) (fun i => hsupp i.1)
      (fun i q hq => ⟨hlB i.1 (subset_closure hq), hrB i.1 (subset_closure hq)⟩)
      (fun i q hq => (hcut i.1 q (subset_closure hq)).1)
      (fun i q hq => (hcut i.1 q (subset_closure hq)).2)
      hc (fun i => hBchart i.1) hfootprint isCompact_Icc (uniqueDiffOn_Icc hab)
      (max 1 n) (lt_min hε (lt_min hη hζ))
  let Γ : ℝ → freeLoop M := fun t =>
    ⟨fun z => β (t, z), hβ.continuous.comp (continuous_const.prodMk continuous_id)⟩
  obtain ⟨hΓi, hΓsep⟩ := hstable β (hlift hβ _) (fun q hq =>
    (hβjets 1 (le_max_left _ _) q hq).trans_le
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hcontain : ∀ q ∈ K, β (l q) = β (r q) → q ∈ W := by
    apply hnocollision β
    intro p hp
    have h := (hβclose p hp).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    simpa only [dist_eq_norm] using h
  have hbad : ∃ exceptional : Finset ℝ, ∀ t ∈ Icc a b, t ∉ exceptional → _root_.Topology.IsEmbedding (Γ t) := by
    apply DifferentialGeometry.Topology.exists_finset_embedding_outside_of_compact_transverse_double_points_of_contMDiff
      hdim Γ (hβ.of_le (by simp)) hK
    · intro q hq heq
      have h := hq.2
      rw [heq, dist_self] at h
      exact hδ.not_ge h
    · intro t ht z w hne heq
      exact ⟨ht, hΓsep t ht z w hne heq⟩
    · intro q hq hne heq
      have hqW := hcontain q hq heq
      obtain ⟨i, hit, hiA⟩ := mem_iUnion₂.mp hqW
      exact hβtrans ⟨i, hit⟩ q (interior_subset hiA) heq
  refine ⟨β, hβ, hΓi, hbad, ?_⟩
  intro m hm p hp
  exact (hβjets m (hm.trans (le_max_right _ _)) p hp).trans_le (min_le_left _ _)

end DifferentialGeometry.Topology

end
