import DifferentialGeometry.Topology.Manifold.RelativeCollar
import DifferentialGeometry.Topology.Manifold.ChartSupportedExtension
import Mathlib.Geometry.Manifold.Instances.Real

set_option autoImplicit false

noncomputable section

open Set Filter Topology Manifold
open scoped Manifold ContDiff

private theorem contMDiffOn_deriv_snd_supported
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    {S : Set (N × ℝ)} (hS : IsOpen S) {Φ : N × ℝ → E}
    (hΦ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Φ S) :
    ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞
      (fun p => deriv (fun t => Φ (p.1, t)) p.2) S := by
  intro p hp
  have hΦp := hΦ.contMDiffAt (hS.mem_nhds hp)
  have hf : ContMDiffAt ((J.prod 𝓘(ℝ)).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞
      (fun q : (N × ℝ) × ℝ => Φ (q.1.1, q.2)) (p, p.2) :=
    hΦp.comp (p, p.2) (contMDiffAt_fst.fst.prodMk contMDiffAt_snd)
  have hv := hf.mfderiv_apply (m := ∞)
    (fun q : N × ℝ => fun t : ℝ => Φ (q.1, t))
    (fun q : N × ℝ => q.2) (fun q : N × ℝ => q) (fun _ : N × ℝ => (1 : ℝ))
    contMDiffAt_snd contMDiffAt_id contMDiffAt_const (by simp)
  apply ContMDiffAt.contMDiffWithinAt
  simpa only [inTangentCoordinates_model_space, mfderiv_eq_fderiv, deriv] using hv

namespace OpenPartialHomeomorph

theorem exists_contDiff_vector_field_eq_collar_velocity_supported
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    (Φ : OpenPartialHomeomorph (N × ℝ) E)
    (hΦ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Φ Φ.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) ∞ Φ.symm Φ.target)
    {A : Set N} (hA : IsCompact A) {ε : ℝ}
    (hw : A ×ˢ Set.Icc (-ε) ε ⊆ Φ.source)
    {P : Set E} (hP : IsOpen P) (hPsub : Φ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ P)
    (hPt : P ⊆ Φ.target) :
    ∃ V : E → E, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
      tsupport V ⊆ P ∧ ∃ W : Set E, IsOpen W ∧
        Φ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ W ∧ W ⊆ P ∧
        Set.EqOn V
          (fun x => deriv (fun t => Φ ((Φ.symm x).1, t)) (Φ.symm x).2) W := by
  let X := fun x : E => deriv (fun t => Φ ((Φ.symm x).1, t)) (Φ.symm x).2
  have hX : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ X Φ.target :=
    (contMDiffOn_deriv_snd_supported Φ.open_source hΦ).comp hi (fun _ hx => Φ.map_target hx)
  let K := Φ '' (A ×ˢ Set.Icc (-ε) ε)
  have hK : IsCompact K :=
    (hA.prod isCompact_Icc).image_of_continuousOn (hΦ.continuousOn.mono hw)
  have hKC : K ⊆ P := hPsub
  obtain ⟨C, hC, hKCint, hCt⟩ := exists_compact_between hK hP hKC
  obtain ⟨η, hηone, hηzero, hηrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, E) hK.isClosed hKCint (n := ⊤)
  obtain ⟨W, hW, hKW, hWone⟩ := eventually_nhdsSet_iff_exists.mp hηone
  let V := fun x => η x • X x
  have hVC : tsupport V ⊆ C := by
    apply closure_minimal _ hC.isClosed
    intro x hx
    by_contra hxC
    have hη : η x = 0 := hηzero x hxC
    exact hx (by simp only [V, hη, zero_smul])
  refine ⟨V, ?_, hC.of_isClosed_subset (isClosed_tsupport V) hVC, hVC.trans hCt,
    W ∩ P, hW.inter hP, Set.subset_inter hKW hKC, Set.inter_subset_right, ?_⟩
  · rw [← contMDiff_iff_contDiff]
    intro x
    by_cases hxt : x ∈ Φ.target
    · exact η.contMDiff.contMDiffAt.smul (hX.contMDiffAt (Φ.open_target.mem_nhds hxt))
    · have hxC : x ∈ Cᶜ := fun hx => hxt (hPt (hCt hx))
      have hz : V =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hxC] with y hy
        have hη : η y = 0 := hηzero y hy
        simp only [V, hη, zero_smul]
      exact contMDiffAt_const.congr_of_eventuallyEq hz
  · intro x hx
    have hη : η x = 1 := hWone x hx.1
    simp only [V, hη, one_smul, X]

end OpenPartialHomeomorph

namespace DifferentialGeometry.Topology.Collar

theorem exists_isotopy_eq_collar_supported
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    (Φ : OpenPartialHomeomorph (N × ℝ) E)
    (hΦ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Φ Φ.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) ∞ Φ.symm Φ.target)
    {A : Set N} (hA : IsCompact A) {ε : ℝ} (hε : 0 < ε)
    (hw : A ×ˢ Set.Icc (-ε) ε ⊆ Φ.source)
    {P : Set E} (hP : IsOpen P) (hPsub : Φ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ P)
    (hPt : P ⊆ Φ.target) :
    ∃ H : ℝ → E ≃ₘ[ℝ] E,
      H 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => H q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × E => (H q.1).symm q.2) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ P ∧
        (∀ t, Set.EqOn (H t) id Kᶜ ∧ Set.EqOn (H t).symm id Kᶜ) ∧
        ∀ p ∈ A, ∀ t ∈ Set.Ioo (-ε) ε, H t (Φ (p, 0)) = Φ (p, t) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨V, hV, hVs, hVt, W, hW, htrace, hWt, hfield⟩ :=
    Φ.exists_contDiff_vector_field_eq_collar_velocity_supported hΦ hi hA hw hP hPsub hPt
  have hVeq (p : N) (hp : p ∈ A) (t : ℝ) (ht : t ∈ Set.Icc (-ε) ε) :
      V (Φ (p, t)) = deriv (fun s => Φ (p, s)) t := by
    have hpt : (p, t) ∈ Φ.source := hw ⟨hp, ht⟩
    simpa only [Φ.left_inv hpt] using hfield (htrace ⟨(p, t), ⟨hp, ht⟩, rfl⟩)
  have hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x : E => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hV
  let H := _root_.Diffeomorph.compactSupportFlow V hv hVs
  refine ⟨H, _root_.Diffeomorph.compactSupportFlow_zero V hv hVs, _root_.Diffeomorph.contMDiff_compactSupportFlow V hv hVs,
    _root_.Diffeomorph.contMDiff_compactSupportFlow_symm V hv hVs, tsupport V, hVs, hVt,
    _root_.Diffeomorph.compactSupportFlow_eqOn_compl_tsupport V hv hVs, ?_⟩
  intro p hp t ht
  have hc : IsMIntegralCurveOn (I := 𝓘(ℝ, E)) (fun s => Φ (p, s)) V
      (Set.Ioo (-ε) ε) := by
    intro s hs
    have hps : (p, s) ∈ Φ.source := hw ⟨hp, ⟨hs.1.le, hs.2.le⟩⟩
    have hsm : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun s => Φ (p, s)) s :=
      (hΦ.contMDiffAt (Φ.open_source.mem_nhds hps)).comp s
        (contMDiffAt_const.prodMk contMDiffAt_id)
    have hd := (contMDiffAt_iff_contDiffAt.mp hsm).differentiableAt (by simp)
    rw [hVeq p hp s ⟨hs.1.le, hs.2.le⟩]
    exact hd.hasDerivAt.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
  have hzero : (0 : ℝ) ∈ Set.Ioo (-ε) ε := ⟨by linarith, hε⟩
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0)
    hzero (hv.of_le (by simp))
    ((_root_.Diffeomorph.isMIntegralCurve_compactSupportFlow V hv hVs (Φ (p, 0))).isMIntegralCurveOn _)
    hc (DFunLike.congr_fun (_root_.Diffeomorph.compactSupportFlow_zero (I := 𝓘(ℝ, E)) V hv hVs) (Φ (p, 0)))
  exact heq ht

theorem exists_relative_collar_isotopy_supported
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    {Φ₀ Φ₁ : OpenPartialHomeomorph (N × ℝ) E}
    (hΦ₀ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Φ₀ Φ₀.source)
    (hi₀ : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) ∞ Φ₀.symm Φ₀.target)
    (hΦ₁ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Φ₁ Φ₁.source)
    (hi₁ : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) ∞ Φ₁.symm Φ₁.target)
    {A : Set N} (hA : IsCompact A) {ε : ℝ} (hε : 0 < ε)
    (hw₀ : A ×ˢ Set.Icc (-ε) ε ⊆ Φ₀.source)
    (hw₁ : A ×ˢ Set.Icc (-ε) ε ⊆ Φ₁.source)
    (hcore : ∀ p ∈ A, Φ₀ (p, 0) = Φ₁ (p, 0))
    {P : Set E} (hP : IsOpen P)
    (hP₀ : Φ₀ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ P)
    (hP₁ : Φ₁ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ P)
    (hPt₀ : P ⊆ Φ₀.target) (hPt₁ : P ⊆ Φ₁.target) :
    ∃ Ψ : ℝ → E ≃ₘ[ℝ] E,
      Ψ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => Ψ q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => (Ψ q.1).symm q.2) ∧
      (∃ K : Set E, IsCompact K ∧ K ⊆ P ∧ (∀ t, Set.EqOn (Ψ t) id Kᶜ) ∧
        ∀ t, Set.EqOn (Ψ t).symm id Kᶜ) ∧
      ∀ p ∈ A, ∀ t ∈ Set.Ioo (-ε) ε, Ψ t (Φ₀ (p, t)) = Φ₁ (p, t) := by
  obtain ⟨H, hH0, hH, hHi, KH, hKH, hKHsub, hKHfix, hHiso⟩ :=
    exists_isotopy_eq_collar_supported Φ₀ hΦ₀ hi₀ hA hε hw₀ hP hP₀ hPt₀
  obtain ⟨G, hG0, hG, hGi, KG, hKG, hKGsub, hKGfix, hGiso⟩ :=
    exists_isotopy_eq_collar_supported Φ₁ hΦ₁ hi₁ hA hε hw₁ hP hP₁ hPt₁
  refine ⟨fun t => (H t).symm.trans (G t), ?_, ?_, ?_, ?_, ?_⟩
  · change (H 0).symm.trans (G 0) = Diffeomorph.refl 𝓘(ℝ, E) E ∞
    rw [hH0, hG0, Diffeomorph.symm_refl, Diffeomorph.refl_trans]
  · have hfun : (fun q : ℝ × E => ((H q.1).symm.trans (G q.1)) q.2) =
        fun q : ℝ × E => G q.1 ((H q.1).symm q.2) := by
      funext q
      change G q.1 ((H q.1).symm q.2) = G q.1 ((H q.1).symm q.2)
      rfl
    rw [hfun]
    exact hG.comp (contMDiff_fst.prodMk hHi)
  · have hfun : (fun q : ℝ × E => ((H q.1).symm.trans (G q.1)).symm q.2) =
        fun q : ℝ × E => H q.1 ((G q.1).symm q.2) := by
      funext q
      change H q.1 ((G q.1).symm q.2) = H q.1 ((G q.1).symm q.2)
      rfl
    rw [hfun]
    exact hH.comp (contMDiff_fst.prodMk hGi)
  · refine ⟨KH ∪ KG, hKH.union hKG, Set.union_subset hKHsub hKGsub, fun t => ?_, fun t => ?_⟩
    · intro x hx
      have hxH : x ∉ KH := fun h => hx (Or.inl h)
      have hxG : x ∉ KG := fun h => hx (Or.inr h)
      have hHx : (H t).symm x = x := by simpa using (hKHfix t).2 hxH
      have hGx : G t x = x := by simpa using (hKGfix t).1 hxG
      change G t ((H t).symm x) = id x
      rw [hHx, hGx]
      rfl
    · intro x hx
      have hxH : x ∉ KH := fun h => hx (Or.inl h)
      have hxG : x ∉ KG := fun h => hx (Or.inr h)
      have hHx : (H t).symm x = x := by simpa using (hKHfix t).2 hxH
      have hGx : G t x = x := by simpa using (hKGfix t).1 hxG
      have hx' : ((H t).symm.trans (G t)) x = x := by
        change G t ((H t).symm x) = x
        rw [hHx, hGx]
      have h2 := Diffeomorph.symm_apply_apply ((H t).symm.trans (G t)) x
      rw [hx'] at h2
      change ((H t).symm.trans (G t)).symm x = id x
      rw [h2]
      rfl
  · intro p hp t ht
    have hHt : (H t).symm (Φ₀ (p, t)) = Φ₁ (p, 0) := by
      rw [← hHiso p hp t ht, ← hcore p hp, Diffeomorph.symm_apply_apply]
    have hGt : G t (Φ₁ (p, 0)) = Φ₁ (p, t) := hGiso p hp t ht
    change G t ((H t).symm (Φ₀ (p, t))) = Φ₁ (p, t)
    rw [hHt, hGt]

theorem relativeCollarIsotopyShape_refl
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    (Φ : OpenPartialHomeomorph (N × ℝ) E) {A : Set N} {ε : ℝ} {P : Set E} :
    ∃ Ψ : ℝ → E ≃ₘ[ℝ] E,
      Ψ 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => Ψ q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => (Ψ q.1).symm q.2) ∧
      (∃ K : Set E, IsCompact K ∧ K ⊆ P ∧ (∀ t, Set.EqOn (Ψ t) id Kᶜ) ∧
        ∀ t, Set.EqOn (Ψ t).symm id Kᶜ) ∧
      ∀ p ∈ A, ∀ t ∈ Set.Ioo (-ε) ε, Ψ t (Φ (p, t)) = Φ (p, t) := by
  refine ⟨fun _ => Diffeomorph.refl 𝓘(ℝ, E) E ∞, rfl, contMDiff_snd, contMDiff_snd,
    ⟨∅, isCompact_empty, Set.empty_subset P, fun t => ?_, fun t => ?_⟩, ?_⟩
  · exact fun x _ => rfl
  · exact fun x _ => rfl
  · intro p _ t _
    rfl

theorem exists_relative_collar_isotopy_supported_manifold
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    {H : Type*} [TopologicalSpace H] {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [T2Space M] {I : ModelWithCorners ℝ E H}
    (e : OpenPartialHomeomorph M E) (htarget : e.target = univ)
    (he : ContMDiffOn I 𝓘(ℝ, E) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℝ, E) I ∞ e.symm e.target)
    {Φ₀ Φ₁ : OpenPartialHomeomorph (N × ℝ) E}
    (hΦ₀ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Φ₀ Φ₀.source)
    (hi₀ : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) ∞ Φ₀.symm Φ₀.target)
    (hΦ₁ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Φ₁ Φ₁.source)
    (hi₁ : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) ∞ Φ₁.symm Φ₁.target)
    {A : Set N} (hA : IsCompact A) {ε : ℝ} (hε : 0 < ε)
    (hw₀ : A ×ˢ Set.Icc (-ε) ε ⊆ Φ₀.source)
    (hw₁ : A ×ˢ Set.Icc (-ε) ε ⊆ Φ₁.source)
    (hcore : ∀ p ∈ A, Φ₀ (p, 0) = Φ₁ (p, 0))
    {P : Set E} (hP : IsOpen P)
    (hP₀ : Φ₀ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ P)
    (hP₁ : Φ₁ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ P)
    (hPt₀ : P ⊆ Φ₀.target) (hPt₁ : P ⊆ Φ₁.target) :
    ∃ Ψ : ℝ → Diffeomorph I I M M ∞,
      Ψ 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun q : ℝ × M => Ψ q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod I) I ∞ (fun q : ℝ × M => (Ψ q.1).symm q.2) ∧
      IsOpen (e.symm '' P) ∧
      (∃ K : Set M, IsCompact K ∧ K ⊆ e.symm '' P ∧
        (∀ t, Set.EqOn (Ψ t) id Kᶜ) ∧ ∀ t, Set.EqOn (Ψ t).symm id Kᶜ) ∧
      ∀ p ∈ A, ∀ t ∈ Set.Ioo (-ε) ε,
        Ψ t (e.symm (Φ₀ (p, t))) = e.symm (Φ₁ (p, t)) := by
  obtain ⟨D, hD0, hD, hDi, ⟨K₀, hK₀, hK₀sub, hK₀fix, hK₀fixi⟩, hDcollar⟩ :=
    exists_relative_collar_isotopy_supported hΦ₀ hi₀ hΦ₁ hi₁ hA hε hw₀ hw₁ hcore
      hP hP₀ hP₁ hPt₀ hPt₁
  have hDc' : ContMDiff 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => D q.1 q.2) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hD
  have hDic' : ContMDiff 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => (D q.1).symm q.2) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hDi
  have hDc : ContDiff ℝ ∞ (fun q : ℝ × E => D q.1 q.2) := contMDiff_iff_contDiff.mp hDc'
  have hDic : ContDiff ℝ ∞ (fun q : ℝ × E => (D q.1).symm q.2) := contMDiff_iff_contDiff.mp hDic'
  obtain ⟨J, hJ, hJi, hJeq, hJcomp, -, hJfix⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_extension_of_chart_family
      e htarget he hei D hDc hDic hK₀ (fun p z hz => ⟨hK₀fix p hz, hK₀fixi p hz⟩)
  have hJ0 : J 0 = Diffeomorph.refl I M ∞ := by
    refine Diffeomorph.ext fun x => ?_
    rw [(hJeq 0 x).1, hD0]
    change DifferentialGeometry.Topology.Manifold.extendChartById e (id : E → E) x = x
    by_cases hx : x ∈ e.source
    · exact (show DifferentialGeometry.Topology.Manifold.extendChartById e (id : E → E) x =
          e.symm (e x) from if_pos hx).trans (e.left_inv hx)
    · exact if_neg hx
  refine ⟨J, hJ0, hJ, hJi, ?_, ⟨e.symm '' K₀, hJcomp, Set.image_mono hK₀sub, ?_, ?_⟩, ?_⟩
  · refine (e.symm).isOpen_image_of_subset_source hP ?_
    rw [OpenPartialHomeomorph.symm_source, htarget]
    exact Set.subset_univ P
  · exact fun t x hx => (hJfix t x hx).1
  · exact fun t x hx => (hJfix t x hx).2
  · intro p hp t ht
    have hxs : e.symm (Φ₀ (p, t)) ∈ e.source :=
      e.map_target (htarget ▸ Set.mem_univ (Φ₀ (p, t)))
    rw [(hJeq t _).1]
    change DifferentialGeometry.Topology.Manifold.extendChartById e (⇑(D t))
      (e.symm (Φ₀ (p, t))) = e.symm (Φ₁ (p, t))
    rw [show DifferentialGeometry.Topology.Manifold.extendChartById e (⇑(D t))
        (e.symm (Φ₀ (p, t))) = e.symm (D t (e (e.symm (Φ₀ (p, t))))) from if_pos hxs,
      e.right_inv (htarget ▸ Set.mem_univ (Φ₀ (p, t))), hDcollar p hp t ht]

private theorem contMDiffOn_prodDomain_iff_contDiff
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] {f : ℝ × E → E'} :
    ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E') ∞ f univ ↔ ContDiff ℝ ∞ f := by
  rw [contMDiffOn_univ]
  constructor
  · intro h
    refine contMDiff_iff_contDiff.mp ?_
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h
  · intro h
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact contMDiff_iff_contDiff.mpr h

private theorem contMDiffOn_prodCodomain_iff_contDiff
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] {f : E → ℝ × E'} :
    ContMDiffOn 𝓘(ℝ, E) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E')) ∞ f univ ↔ ContDiff ℝ ∞ f := by
  rw [contMDiffOn_univ]
  constructor
  · intro h
    refine contMDiff_iff_contDiff.mp ?_
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h
  · intro h
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact contMDiff_iff_contDiff.mpr h

private def collarId : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun := fun q => q
  invFun := fun y => y
  source := univ
  target := univ
  map_source' := fun _ _ => trivial
  map_target' := fun _ _ => trivial
  left_inv' := fun _ _ => rfl
  right_inv' := fun _ _ => rfl
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun := continuous_id.continuousOn
  continuousOn_invFun := continuous_id.continuousOn

private def collarShift : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun := fun q => (q.1, 2 * q.2)
  invFun := fun y => (y.1, (1 / 2) * y.2)
  source := univ
  target := univ
  map_source' := fun _ _ => trivial
  map_target' := fun _ _ => trivial
  left_inv' := by
    intro x _
    refine Prod.ext rfl ?_
    ring
  right_inv' := by
    intro y _
    refine Prod.ext rfl ?_
    ring
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuousOn_toFun :=
    (continuous_fst.prodMk (continuous_const.mul continuous_snd)).continuousOn
  continuousOn_invFun :=
    (continuous_fst.prodMk (continuous_const.mul continuous_snd)).continuousOn

theorem relativeCollarInput_nonvacuous :
    ∃ Ψ : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ∀ p ∈ Metric.closedBall (0 : ℝ) 1, ∀ t ∈ Set.Ioo (-1 : ℝ) 1,
        Ψ t (collarId (p, t)) = collarShift (p, t) := by
  have hsrc : collarId.source = (univ : Set (ℝ × ℝ)) := rfl
  have htgt : collarId.target = (univ : Set (ℝ × ℝ)) := rfl
  have hsrc' : collarShift.source = (univ : Set (ℝ × ℝ)) := rfl
  have htgt' : collarShift.target = (univ : Set (ℝ × ℝ)) := rfl
  have hΦ₀ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞
      (collarId) collarId.source := by
    rw [hsrc]
    exact (contMDiffOn_prodDomain_iff_contDiff (E := ℝ) (E' := ℝ × ℝ)).mpr
      (show ContDiff ℝ ∞ (⇑collarId) from contDiff_id)
  have hi₀ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ)) ∞
      (collarId).symm (collarId).target := by
    rw [htgt]
    exact (contMDiffOn_prodCodomain_iff_contDiff (E := ℝ × ℝ) (E' := ℝ)).mpr
      (show ContDiff ℝ ∞ (⇑(collarId).symm) from contDiff_id)
  have hΦ₁ : ContMDiffOn ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ)) 𝓘(ℝ, ℝ × ℝ) ∞
      (collarShift) collarShift.source := by
    rw [hsrc']
    exact (contMDiffOn_prodDomain_iff_contDiff (E := ℝ) (E' := ℝ × ℝ)).mpr
      (show ContDiff ℝ ∞ (⇑collarShift) from by
        change ContDiff ℝ ∞ (fun q : ℝ × ℝ => (q.1, 2 * q.2))
        fun_prop)
  have hi₁ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ)) ∞
      (collarShift).symm (collarShift).target := by
    rw [htgt']
    exact (contMDiffOn_prodCodomain_iff_contDiff (E := ℝ × ℝ) (E' := ℝ)).mpr
      (show ContDiff ℝ ∞ (⇑(collarShift).symm) from by
        change ContDiff ℝ ∞ (fun y : ℝ × ℝ => (y.1, (1 / 2) * y.2))
        fun_prop)
  have hcore : ∀ p ∈ Metric.closedBall (0 : ℝ) 1,
      collarId (p, 0) = collarShift (p, 0) := by
    intro p _
    change ((p, (0 : ℝ)) : ℝ × ℝ) = (p, 2 * 0)
    simp
  obtain ⟨Ψ, -, -, -, -, hΨ⟩ :=
    exists_relative_collar_isotopy_supported hΦ₀ hi₀ hΦ₁ hi₁
      (isCompact_closedBall (0 : ℝ) 1) (by norm_num : (0 : ℝ) < 1)
      (fun _ _ => trivial) (fun _ _ => trivial) hcore isOpen_univ
      (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial) (fun _ _ => trivial)
  exact ⟨Ψ, hΨ⟩

end DifferentialGeometry.Topology.Collar
