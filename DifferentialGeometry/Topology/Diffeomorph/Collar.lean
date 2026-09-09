import DifferentialGeometry.Topology.Diffeomorph.Flow
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity

open scoped ContDiff Topology Manifold

private theorem contMDiffOn_deriv_snd
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

theorem exists_contDiff_vector_field_eq_collar_velocity
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    (Φ : OpenPartialHomeomorph (N × ℝ) E)
    (hΦ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Φ Φ.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) ∞ Φ.symm Φ.target)
    {A : Set N} (hA : IsCompact A) {ε : ℝ}
    (hw : A ×ˢ Set.Icc (-ε) ε ⊆ Φ.source) :
    ∃ V : E → E, ContDiff ℝ ∞ V ∧ HasCompactSupport V ∧
      tsupport V ⊆ Φ.target ∧ ∃ W : Set E, IsOpen W ∧
        Φ '' (A ×ˢ Set.Icc (-ε) ε) ⊆ W ∧ W ⊆ Φ.target ∧
        Set.EqOn V
          (fun x => deriv (fun t => Φ ((Φ.symm x).1, t)) (Φ.symm x).2) W := by
  let X := fun x : E => deriv (fun t => Φ ((Φ.symm x).1, t)) (Φ.symm x).2
  have hX : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ X Φ.target :=
    (contMDiffOn_deriv_snd Φ.open_source hΦ).comp hi (fun _ hx => Φ.map_target hx)
  let K := Φ '' (A ×ˢ Set.Icc (-ε) ε)
  have hK : IsCompact K :=
    (hA.prod isCompact_Icc).image_of_continuousOn (hΦ.continuousOn.mono hw)
  have hKt : K ⊆ Φ.target := Set.image_subset_iff.mpr (fun _ hx => Φ.map_source (hw hx))
  obtain ⟨C, hC, hKC, hCt⟩ := exists_compact_between hK Φ.open_target hKt
  obtain ⟨η, hηone, hηzero, hηrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, E) hK.isClosed hKC (n := ⊤)
  obtain ⟨W, hW, hKW, hWone⟩ := eventually_nhdsSet_iff_exists.mp hηone
  let V := fun x => η x • X x
  have hVC : tsupport V ⊆ C := by
    apply closure_minimal _ hC.isClosed
    intro x hx
    by_contra hxC
    have hη : η x = 0 := hηzero x hxC
    exact hx (by simp only [V, hη, zero_smul])
  refine ⟨V, ?_, hC.of_isClosed_subset (isClosed_tsupport V) hVC,
    hVC.trans hCt, W ∩ Φ.target, hW.inter Φ.open_target,
    Set.subset_inter hKW hKt, Set.inter_subset_right, ?_⟩
  · rw [← contMDiff_iff_contDiff]
    intro x
    by_cases hxt : x ∈ Φ.target
    · exact η.contMDiff.contMDiffAt.smul (hX.contMDiffAt (Φ.open_target.mem_nhds hxt))
    · have hxC : x ∈ Cᶜ := fun hx => hxt (hCt hx)
      have hz : V =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hxC] with y hy
        have hη : η y = 0 := hηzero y hy
        simp only [V, hη, zero_smul]
      exact contMDiffAt_const.congr_of_eventuallyEq hz
  · intro x hx
    have hη : η x = 1 := hWone x hx.1
    simp only [V, hη, one_smul, X]

end OpenPartialHomeomorph

namespace Diffeomorph

theorem exists_isotopy_eq_collar
    {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
    (Φ : OpenPartialHomeomorph (N × ℝ) E)
    (hΦ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ Φ Φ.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (J.prod 𝓘(ℝ)) ∞ Φ.symm Φ.target)
    {A : Set N} (hA : IsCompact A) {ε : ℝ} (hε : 0 < ε)
    (hw : A ×ˢ Set.Icc (-ε) ε ⊆ Φ.source) :
    ∃ H : ℝ → E ≃ₘ[ℝ] E,
      H 0 = Diffeomorph.refl 𝓘(ℝ, E) E ∞ ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ (fun q : ℝ × E => H q.1 q.2) ∧
      ContMDiff (𝓘(ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
        (fun q : ℝ × E => (H q.1).symm q.2) ∧
      ∃ K : Set E, IsCompact K ∧ K ⊆ Φ.target ∧
        (∀ t, Set.EqOn (H t) id Kᶜ ∧ Set.EqOn (H t).symm id Kᶜ) ∧
        ∀ p ∈ A, ∀ t ∈ Set.Ioo (-ε) ε, H t (Φ (p, 0)) = Φ (p, t) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨V, hV, hVs, hVt, W, hW, htrace, hWt, hfield⟩ :=
    Φ.exists_contDiff_vector_field_eq_collar_velocity hΦ hi hA hw
  have hVeq (p : N) (hp : p ∈ A) (t : ℝ) (ht : t ∈ Set.Icc (-ε) ε) :
      V (Φ (p, t)) = deriv (fun s => Φ (p, s)) t := by
    have hpt : (p, t) ∈ Φ.source := hw ⟨hp, ht⟩
    simpa only [Φ.left_inv hpt] using hfield (htrace ⟨(p, t), ⟨hp, ht⟩, rfl⟩)
  have hv : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x : E => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) E)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hV
  let H := compactSupportFlow V hv hVs
  refine ⟨H, compactSupportFlow_zero V hv hVs, contMDiff_compactSupportFlow V hv hVs,
    contMDiff_compactSupportFlow_symm V hv hVs, tsupport V, hVs, hVt,
    compactSupportFlow_eqOn_compl_tsupport V hv hVs, ?_⟩
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
    ((isMIntegralCurve_compactSupportFlow V hv hVs (Φ (p, 0))).isMIntegralCurveOn _)
    hc (DFunLike.congr_fun (compactSupportFlow_zero (I := 𝓘(ℝ, E)) V hv hVs) (Φ (p, 0)))
  exact heq ht

end Diffeomorph
