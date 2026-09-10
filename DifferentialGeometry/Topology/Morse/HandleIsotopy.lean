import DifferentialGeometry.Topology.Morse.HandleCollar
import DifferentialGeometry.Topology.Diffeomorph.Collar


open scoped ContDiff Topology Manifold

private theorem exists_ambient_collar
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
    (O : TopologicalSpace.Opens E) (p : O)
    (Φ : OpenPartialHomeomorph (N × ℝ) O)
    (hΦ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Φ Φ.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) ∞ Φ.symm Φ.target) :
    ∃ Ψ : OpenPartialHomeomorph (N × ℝ) E,
      Ψ.source = Φ.source ∧ Ψ.target = Subtype.val '' Φ.target ∧
      Ψ.target ⊆ O ∧ (∀ q, Ψ q = (Φ q : E)) ∧
      (∀ x : O, Ψ.symm x = Φ.symm x) ∧
      ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Ψ Ψ.source ∧
      ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) ∞ Ψ.symm Ψ.target := by
  let ι := O.openPartialHomeomorphSubtypeCoe ⟨p⟩
  let Ψ := Φ.trans ι
  have hs : Ψ.source = Φ.source := by
    simp [Ψ, ι]
  have ht : Ψ.target = Subtype.val '' Φ.target := by
    ext x
    constructor
    · intro hx
      change x ∈ ι.target ∩ ι.symm ⁻¹' Φ.target at hx
      exact ⟨ι.symm x, hx.2, ι.right_inv hx.1⟩
    · rintro ⟨y, hy, rfl⟩
      change ι y ∈ ι.target ∩ ι.symm ⁻¹' Φ.target
      refine ⟨ι.map_source (by simp [ι]), ?_⟩
      simpa only [Set.mem_preimage, ι.left_inv (by simp [ι])] using hy
  have hι : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ ι.symm ι.target := by
    have hval : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
        (Subtype.val ∘ ι.symm) ι.target :=
      contMDiffOn_id.congr (fun x hx => ι.right_inv hx)
    intro x hx
    exact (ContMDiffWithinAt.subtypeVal_comp_iff O ι.symm ι.target x).mp (hval x hx)
  refine ⟨Ψ, hs, ht, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ht]
    rintro _ ⟨x, hx, rfl⟩
    exact x.property
  · intro q
    rfl
  · intro x
    change Φ.symm (ι.symm (ι x)) = Φ.symm x
    rw [ι.left_inv (by simp [ι])]
  · rw [hs]
    exact contMDiff_subtype_val.comp_contMDiffOn hΦ
  · change ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) ∞
      (Φ.symm ∘ ι.symm) Ψ.target
    apply hi.comp (hι.mono ?_) ?_
    · intro x hx
      change x ∈ ι.target ∩ ι.symm ⁻¹' Φ.target at hx
      exact hx.1
    · intro x hx
      change x ∈ ι.target ∩ ι.symm ⁻¹' Φ.target at hx
      exact hx.2
namespace DifferentialGeometry.Topology.Morse.ManifoldCellAttachment

open CellAttachment
open DifferentialGeometry.Topology.Handle

noncomputable section

attribute [local instance] cellBoundaryChartedSpace cellBoundaryIsManifold closedCellChartedSpace

theorem exists_isotopy_cocoreAttachingEmbedding
    {n k : ℕ} (hk : k ≤ n) [NeZero k] [NeZero (n - k)]
    {O : TopologicalSpace.Opens (MorseModel n)} (f : MorseModel n → ℝ) (c ε r : ℝ)
    (data : MorseChart n k hk c 𝓘(ℝ, MorseModel n) (fun x : O => f x))
    (hε : 0 < ε) (hr : r ≠ 0)
    (hR : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R)
    (hR' : Real.sqrt (2 * ε + 2 * r ^ 2) < data.R') :
    ∃ δ > 0, δ < ε ∧ ∃ H : ℝ → MorseModel n ≃ₘ[ℝ] MorseModel n,
      H 0 = Diffeomorph.refl 𝓘(ℝ, MorseModel n) (MorseModel n) ∞ ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, MorseModel n)) 𝓘(ℝ, MorseModel n) ∞
        (fun q : ℝ × MorseModel n => H q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, MorseModel n)) 𝓘(ℝ, MorseModel n) ∞
        (fun q : ℝ × MorseModel n => (H q.1).symm q.2) ∧
      ∃ K : Set (MorseModel n), IsCompact K ∧ K ⊆ O ∧
        (∀ t, Set.EqOn (H t) id Kᶜ ∧ Set.EqOn (H t).symm id Kᶜ) ∧
        ∀ (q : AttachingRegion k (n - k)) (t : ℝ), t ∈ Set.Ioo (-δ) δ →
          H t ((cocoreAttachingEmbedding hk c ε r data hε hR.le q).val : MorseModel n) =
            (data.χ (recombine hk
              (Real.sqrt (2 * ε + r ^ 2 * ‖q.2.val‖ ^ 2 - 2 * t) • q.1.val)
              (r • q.2.val)) : MorseModel n) ∧
          f (H t ((cocoreAttachingEmbedding hk c ε r data hε hR.le q).val : MorseModel n)) =
            c - ε + t := by
  obtain ⟨δ, hδ, hδε, Φ, hΦ, hi, hformula, hinv, hheight, hsource, hzero, hemb, _⟩ :=
    exists_isSmoothEmbedding_cocore_collar hk c ε r data hr hε hR hR'
  obtain ⟨Ψ, hs, ht, htarget, hval, hival, hΨ, hΨi⟩ :=
    exists_ambient_collar O data.p Φ hΦ hi
  let A : Set (CellBoundary k × EuclideanSpace ℝ (Fin (n - k))) :=
    Set.range (fun q : AttachingRegion k (n - k) => (q.1, q.2.val))
  have hA : IsCompact A := isCompact_range (continuous_fst.prodMk continuous_snd.subtype_val)
  have hwidth : A ×ˢ Set.Icc (-(δ / 2)) (δ / 2) ⊆ Ψ.source := by
    rintro ⟨p, t⟩ ⟨⟨q, rfl⟩, ht⟩
    rw [hs]
    exact hsource q t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  obtain ⟨H, hH0, hH, hHi, K, hK, hKt, hfix, hagree⟩ :=
    Diffeomorph.exists_isotopy_eq_collar Ψ hΨ hΨi hA (by positivity : 0 < δ / 2) hwidth
  refine ⟨δ / 2, by positivity, by linarith, H, hH0, hH, hHi, K, hK,
    hKt.trans htarget, hfix, ?_⟩
  intro q t ht
  have heq := hagree (q.1, q.2.val) ⟨q, rfl⟩ t ht
  have htδ : t ∈ Set.Ioo (-δ) δ := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hstart : Ψ ((q.1, q.2.val), 0) =
      ((cocoreAttachingEmbedding hk c ε r data hε hR.le q).val : MorseModel n) := by
    rw [hval, hzero]
  rw [hstart, hval] at heq
  refine ⟨?_, ?_⟩
  · exact heq.trans (congrArg Subtype.val (hformula ((q.1, q.2.val), t)))
  · rw [heq]
    exact hheight _ (hsource q t htδ)

end

end DifferentialGeometry.Topology.Morse.ManifoldCellAttachment
