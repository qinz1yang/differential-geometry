import DifferentialGeometry.Topology.Morse.RegularLevel.RelativeVectorField
import DifferentialGeometry.Topology.Diffeomorph.Flow
import DifferentialGeometry.Topology.Embedding.AmbientIsotopy
import DifferentialGeometry.Topology.Embedding.Diffeomorph

open Set Filter Manifold
open scoped ContDiff Topology

namespace DifferentialGeometry.Topology.Morse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem exists_diffeomorph_family_local_level_transport_relative
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {K C U O : Set M}
    (hK : IsCompact K) (hregular : ∀ x ∈ K, ¬ IsCriticalPointAt I f x)
    (hO : IsOpen O) (hKO : K ⊆ O)
    (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U)
    (W : (x : M) → TangentSpace I x)
    (hW : ContMDiffOn I I.tangent ∞
      (fun x => (⟨x, W x⟩ : TangentBundle I M)) U)
    (hWdf : ∀ x ∈ U,
      NormedSpace.fromTangentSpace (f x) (mfderiv I 𝓘(ℝ) f x (W x)) = 1) :
    ∃ δ > 0, ∃ N P : Set M, IsOpen N ∧ K ⊆ N ∧ IsOpen P ∧ C ⊆ P ∧ P ⊆ U ∧
      ∃ Φ : ℝ → M ≃ₘ⟮I, I⟯ M,
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
        Φ 0 = Diffeomorph.refl I M ∞ ∧
        (∀ t ∈ Icc (-δ) δ, ∀ x ∈ N, Φ t x ∈ O ∧ f (Φ t x) = f x + t) ∧
        (∀ t ∈ Icc (-δ) δ, MapsTo (Φ t) P U) ∧
        (∀ x ∈ P, IsMIntegralCurveOn (fun t => Φ t x) W (Icc (-δ) δ)) ∧
        ∃ S : Set M, IsCompact S ∧ ∀ t, EqOn (Φ t) id Sᶜ ∧ EqOn (Φ t).symm id Sᶜ := by
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  have hregopen : IsOpen {x | ¬ IsCriticalPointAt I f x} := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨A, hxA, hA, Z, hZ, _⟩ := exists_open_unitSpeedVectorField_at_noncritical I f hf hx
    filter_upwards [hA.mem_nhds hxA] with y hy hh
    have hz := hZ y hy
    change mfderiv I 𝓘(ℝ) f y = 0 at hh
    rw [hh] at hz
    simp at hz
  obtain ⟨L, hL, hKL, hLsub, hLc⟩ :=
    exists_open_between_and_isCompact_closure hK (hO.inter hregopen)
      (fun x hx => ⟨hKO hx, hregular x hx⟩)
  have hneg (x : M) : (mfderiv I 𝓘(ℝ) (fun y => -f y) x : E →L[ℝ] ℝ) =
      -(mfderiv I 𝓘(ℝ) f x : E →L[ℝ] ℝ) :=
    mfderiv_neg
  obtain ⟨X, hX, hXc, hXrate, _, hXW⟩ :=
    exists_unitSpeedVectorField_eq_nhds_on_compact hf.neg hLc
      (by
        intro x hx hh
        apply (hLsub hx).2
        change (mfderiv I 𝓘(ℝ) f x : E →L[ℝ] ℝ) = 0
        change (mfderiv I 𝓘(ℝ) (fun y => -f y) x : E →L[ℝ] ℝ) = 0 at hh
        exact neg_eq_zero.mp ((hneg x).symm.trans hh))
      hC hU hCU W hW (by
        intro x hx
        exact (congrArg (fun A : E →L[ℝ] ℝ => A (W x)) (hneg x)).trans
          (congrArg Neg.neg (hWdf x hx)))
  have hunit (x : M) (hx : x ∈ L) :
      NormedSpace.fromTangentSpace (f x) (mfderiv I 𝓘(ℝ) f x (X x)) = 1 := by
    have hh := hXrate x (subset_closure hx)
    have hnegvalue := (congrArg (fun A : E →L[ℝ] ℝ => A (X x)) (hneg x)).symm.trans hh
    change -(NormedSpace.fromTangentSpace (f x) (mfderiv I 𝓘(ℝ) f x (X x))) = -1 at hnegvalue
    linarith
  obtain ⟨N, hN, hKN, hNL, hNc⟩ := exists_open_between_and_isCompact_closure hK hL hKL
  obtain ⟨ε, hε, hheight⟩ := Diffeomorph.exists_pos_compactSupportFlow_height
    X hX hXc f hNc hL hNL hunit
  obtain ⟨P, hP, hCP, hPW⟩ := eventually_nhdsSet_iff_exists.mp hXW
  let Φ := Diffeomorph.compactSupportFlow X hX hXc
  have hΦ := Diffeomorph.contMDiff_compactSupportFlow X hX hXc
  have hzero (x : M) : Φ 0 x = x :=
    DFunLike.congr_fun (Diffeomorph.compactSupportFlow_zero X hX hXc) x
  have hslice : ({0} : Set ℝ) ×ˢ C ⊆ (fun p : ℝ × M => Φ p.1 p.2) ⁻¹' (P ∩ U) := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    have ht0 : t = 0 := ht
    subst t
    change Φ 0 x ∈ P ∩ U
    rw [hzero]
    exact ⟨hCP hx, hCU hx⟩
  obtain ⟨T, Q, hT, hQ, h0T, hCQ, hTQ⟩ :=
    generalized_tube_lemma isCompact_singleton hC ((hP.inter hU).preimage hΦ.continuous) hslice
  obtain ⟨ζ, hζ, hζT⟩ := Metric.isOpen_iff.mp hT 0 (h0T (mem_singleton 0))
  let δ := min (ε / 2) (ζ / 2)
  have hδ : 0 < δ := lt_min (half_pos hε) (half_pos hζ)
  have hstay (x : M) (hx : x ∈ Q) (t : ℝ) (ht : t ∈ Icc (-δ) δ) : Φ t x ∈ P ∩ U := by
    apply hTQ (a := (t, x))
    refine ⟨hζT ?_, hx⟩
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt]
    have hb : δ ≤ ζ / 2 := min_le_right _ _
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨δ, hδ, N, Q, hN, hKN, hQ, hCQ,
    fun x hx => by simpa only [hzero] using (hstay x hx 0 ⟨by linarith, hδ.le⟩).2, Φ,
    Diffeomorph.contMDiff_compactSupportFlow X hX hXc,
    Diffeomorph.contMDiff_compactSupportFlow_symm X hX hXc,
    Diffeomorph.compactSupportFlow_zero X hX hXc, ?_, ?_, ?_,
    tsupport X, hXc, Diffeomorph.compactSupportFlow_eqOn_compl_tsupport X hX hXc⟩
  · intro t ht x hx
    have hb : δ ≤ ε / 2 := min_le_left _ _
    have hh := hheight x (subset_closure hx) t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ⟨(hLsub (subset_closure hh.1)).1, hh.2⟩
  · intro t ht x hx
    exact (hstay x hx t ht).2
  · intro x hx t ht
    rw [← hPW (Φ t x) (hstay x hx t ht).1]
    exact (Diffeomorph.isMIntegralCurve_compactSupportFlow X hX hXc x t).hasMFDerivWithinAt

end DifferentialGeometry.Topology.Morse

namespace Manifold

private theorem exists_contDiff_compact_ambient_isotopy_diffeomorph_family
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M] [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : M → F} (he : IsSmoothEmbedding I 𝓘(ℝ, F) ∞ e)
    (Φ : ℝ → M ≃ₘ⟮I, I⟯ M)
    (hΦ : ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2))
    (hΦ0 : Φ 0 = Diffeomorph.refl I M ∞) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ H : ℝ → F ≃ₘ[ℝ] F,
      ContDiff ℝ ∞ (fun p : ℝ × F => H p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × F => (H p.1).symm p.2) ∧
      H 0 = Diffeomorph.refl 𝓘(ℝ, F) F ∞ ∧
      (∀ t ∈ Icc (-δ) δ, ∀ x, H t (e x) = e (Φ t x) ∧
        (H t).symm (e (Φ t x)) = e x) ∧
      ∃ S : Set F, IsCompact S ∧ ∀ t, EqOn (H t) id Sᶜ ∧ EqOn (H t).symm id Sᶜ := by
  obtain ⟨A, hA, hAi, _, hAe, S, hS, _, hAfix⟩ :=
    exists_contDiff_compact_ambient_isotopy (he.contMDiff.comp hΦ)
      (fun t => he.comp_diffeomorph (Φ t)) (a := -δ) (b := δ)
      isOpen_univ (subset_univ _)
  let H (t : ℝ) := (A 0).symm.trans (A t)
  have hH : ContDiff ℝ ∞ (fun p : ℝ × F => H p.1 p.2) :=
    hA.comp (contDiff_fst.prodMk ((A 0).symm.contDiff.comp contDiff_snd))
  have hHi : ContDiff ℝ ∞ (fun p : ℝ × F => (H p.1).symm p.2) :=
    (A 0).contDiff.comp hAi
  have hHzero : H 0 = Diffeomorph.refl 𝓘(ℝ, F) F ∞ := by
    ext x
    exact (A 0).apply_symm_apply x
  refine ⟨H, hH, hHi, hHzero, ?_, S, hS, ?_⟩
  · intro t ht x
    have hz : (A 0).symm (e x) = e (Φ (-δ) x) := by
      simpa only [Function.comp_apply, hΦ0, Diffeomorph.coe_refl, id_eq] using
        (hAe 0 ⟨neg_nonpos.mpr hδ, hδ⟩ x).2
    have hmain : H t (e x) = e (Φ t x) := by
      change A t ((A 0).symm (e x)) = _
      rw [hz]
      exact (hAe t ht x).1
    refine ⟨hmain, ?_⟩
    rw [← hmain]
    exact (H t).symm_apply_apply _
  · intro t
    constructor
    · intro x hx
      change A t ((A 0).symm x) = x
      rw [(hAfix 0).2 hx, id_eq, (hAfix t).1 hx]
      rfl
    · intro x hx
      change A 0 ((A t).symm x) = x
      rw [(hAfix t).2 hx, id_eq, (hAfix 0).1 hx]
      rfl

end Manifold

namespace DifferentialGeometry.Topology.Morse

theorem exists_ambient_isotopy_local_level_transport_relative
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [CompactSpace M]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {e : M → F} (he : IsSmoothEmbedding I 𝓘(ℝ, F) ∞ e) (l : F →L[ℝ] ℝ)
    {K C U O : Set M} (hK : IsCompact K)
    (hregular : ∀ x ∈ K, ¬ IsCriticalPointAt I (l ∘ e) x)
    (hO : IsOpen O) (hKO : K ⊆ O)
    (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U)
    (W : (x : M) → TangentSpace I x)
    (hW : ContMDiffOn I I.tangent ∞
      (fun x => (⟨x, W x⟩ : TangentBundle I M)) U)
    (hWdf : ∀ x ∈ U,
      NormedSpace.fromTangentSpace (l (e x)) (mfderiv I 𝓘(ℝ) (l ∘ e) x (W x)) = 1) :
    ∃ δ > 0, ∃ N P : Set M, IsOpen N ∧ K ⊆ N ∧ IsOpen P ∧ C ⊆ P ∧ P ⊆ U ∧
      ∃ Φ : ℝ → M ≃ₘ⟮I, I⟯ M,
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => Φ p.1 p.2) ∧
        ContMDiff (𝓘(ℝ).prod I) I ∞ (fun p : ℝ × M => (Φ p.1).symm p.2) ∧
        Φ 0 = Diffeomorph.refl I M ∞ ∧
        (∀ t ∈ Icc (-δ) δ, ∀ x ∈ N, Φ t x ∈ O ∧ l (e (Φ t x)) = l (e x) + t) ∧
        (∀ t ∈ Icc (-δ) δ, MapsTo (Φ t) P U) ∧
        (∀ x ∈ P, IsMIntegralCurveOn (fun t => Φ t x) W (Icc (-δ) δ)) ∧
        ∃ A : ℝ → F ≃ₘ[ℝ] F,
          ContDiff ℝ ∞ (fun p : ℝ × F => A p.1 p.2) ∧
          ContDiff ℝ ∞ (fun p : ℝ × F => (A p.1).symm p.2) ∧
          A 0 = Diffeomorph.refl 𝓘(ℝ, F) F ∞ ∧
          (∀ t ∈ Icc (-δ) δ, ∀ x, A t (e x) = e (Φ t x) ∧
            (A t).symm (e (Φ t x)) = e x) ∧
          ∃ S : Set F, IsCompact S ∧ ∀ t, EqOn (A t) id Sᶜ ∧ EqOn (A t).symm id Sᶜ := by
  obtain ⟨δ, hδ, N, P, hN, hKN, hP, hCP, hPU, Φ, hΦ, hΦi, hΦ0, hheight, hstay, hcurve, _⟩ :=
    exists_diffeomorph_family_local_level_transport_relative (l.contMDiff.comp he.contMDiff)
      hK hregular hO hKO hC hU hCU W hW hWdf
  obtain ⟨A, hA, hAi, hA0, hAe, hsupport⟩ :=
    Manifold.exists_contDiff_compact_ambient_isotopy_diffeomorph_family he Φ hΦ hΦ0 hδ.le
  exact ⟨δ, hδ, N, P, hN, hKN, hP, hCP, hPU, Φ, hΦ, hΦi, hΦ0, hheight, hstay, hcurve,
    A, hA, hAi, hA0, hAe, hsupport⟩

end DifferentialGeometry.Topology.Morse
