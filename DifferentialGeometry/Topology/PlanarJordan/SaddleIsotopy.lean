import DifferentialGeometry.Topology.Compactness.ProductNeighborhood
import DifferentialGeometry.Topology.Embedding.RelativeAmbientIsotopy
import DifferentialGeometry.Topology.Diffeomorph.SaddleFiberFlow
import DifferentialGeometry.External.Schoenflies.GeneralCrosscut
import DifferentialGeometry.Topology.Morse.NormalForm.Saddle
import Mathlib.Geometry.Manifold.Instances.Icc

open Set Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Morse
open Schoenflies (Plane IsCutPair)
open DifferentialGeometry.Analysis.ODE (saddleBandCurve)

namespace DifferentialGeometry.Topology.PlanarJordan

private theorem exists_compact_saddleBandCurve_neighborhood
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {t₀ : ℝ} {T : Set ℝ} {K : Set (ℝ × ℝ)}
    (hT : IsCompact T) (hK : IsCompact K)
    (hreg : ∀ z ∈ K, (1 - z.1 ^ 2) * z.2 ≠ 0)
    (hrad : ∀ t ∈ T, ∀ z ∈ K, 0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2)
    {U : Set (ℝ × Plane)} (hU : IsOpen U)
    (htrace : ∀ t ∈ T, ∀ z ∈ K, (t, B (saddleBandCurve z (t - t₀))) ∈ U) :
    ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K ⊆ interior K' ∧
      ∀ t ∈ T, ∀ z ∈ K', (1 - z.1 ^ 2) * z.2 ≠ 0 ∧
        0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2 ∧
        (t, B (saddleBandCurve z (t - t₀))) ∈ U := by
  let R := {p : ℝ × (ℝ × ℝ) | (1 - p.2.1 ^ 2) * p.2.2 ≠ 0}
  let r := fun p : ℝ × (ℝ × ℝ) =>
    1 + 2 * (1 - p.2.1 ^ 2)⁻¹ * (p.1 - t₀) / p.2.2 ^ 2
  have hR : IsOpen R := isOpen_ne_fun (by fun_prop) continuous_const
  have hr : ContDiffOn ℝ ∞ r R := by
    apply contDiffOn_const.add
    apply ContDiffOn.div
    · exact ((contDiffOn_const.mul
        ((contDiffOn_const.sub (contDiffOn_snd.fst.pow 2)).inv
          (fun p hp => (mul_ne_zero_iff.mp hp).1))).mul
        (contDiffOn_fst.sub contDiffOn_const))
    · exact contDiffOn_snd.snd.pow 2
    · intro p hp
      exact pow_ne_zero 2 (mul_ne_zero_iff.mp hp).2
  let D := R ∩ r ⁻¹' Ioi 0
  have hD : IsOpen D := hr.continuousOn.isOpen_inter_preimage hR isOpen_Ioi
  let f := fun p : ℝ × (ℝ × ℝ) => (p.1, B (saddleBandCurve p.2 (p.1 - t₀)))
  have hf : ContinuousOn f D := by
    apply continuousOn_fst.prodMk
    apply B.contDiffOn_comp_saddleBandCurve.continuousOn.comp
      ((continuousOn_fst.sub continuousOn_const).prodMk continuousOn_snd)
    intro p hp
    exact ⟨(mul_ne_zero_iff.mp hp.1).1, (mul_ne_zero_iff.mp hp.1).2, hp.2⟩
  have hsub : T ×ˢ K ⊆ D ∩ f ⁻¹' U := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    exact ⟨⟨hreg z hz, hrad t ht z hz⟩, htrace t ht z hz⟩
  obtain ⟨K', hK', hK'int, hsource, htrace⟩ := hf.exists_compact_prod_mapsTo hD hT hK
    (fun p hp => (hsub hp).1) hU (fun p hp => (hsub hp).2)
  refine ⟨K', hK', hK'int, ?_⟩
  intro t ht z hz
  have hp := hsource (a := (t, z)) ⟨ht, hz⟩
  exact ⟨hp.1, hp.2, htrace (x := (t, z)) ⟨ht, hz⟩⟩

theorem exists_ambient_isotopy_closing_arc_eqOn_saddleBandCurve
    {ι : Type*} [Finite ι] {γ : ℝ × unitInterval → Plane}
    (hγ : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {δ t₀ : ℝ} {a b : ι → ℝ}
    (ht₀flow : t₀ ∈ Icc (-δ) δ) (ht₀ : ∀ i, t₀ ∈ Icc (a i) (b i))
    (hJ : ∀ i, Icc (a i) (b i) ⊆ Ioo (-δ) δ)
    (hemb : ∀ t ∈ Icc (-δ) δ,
      IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => γ (t, u)))
    {K : ι → Set (ℝ × ℝ)} (hK : ∀ i, IsCompact (K i))
    (hreg : ∀ i, ∀ z ∈ K i, (1 - z.1 ^ 2) * z.2 ≠ 0)
    (hrad : ∀ i, ∀ t ∈ Icc (a i) (b i), ∀ z ∈ K i,
      0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2)
    {U : Set (ℝ × Plane)} (hU : IsOpen U)
    (hUreg : ∀ p ∈ U, (1 - (B.symm p.2).1 ^ 2) * (B.symm p.2).2 ≠ 0)
    (hUγ : ∀ t ∈ Ioo (-δ) δ, ∀ u, (t, γ (t, u)) ∈ U →
      B.saddleFiberVectorField (γ (t, u)) = deriv (fun q => γ (q, u)) t)
    {O : Set Plane} (hO : IsOpen O)
    (hγO : ∀ t ∈ Icc (-δ) δ, ∀ u, γ (t, u) ∈ O)
    (htrace : ∀ i, ∀ t ∈ Icc (a i) (b i), ∀ z ∈ K i,
      (t, B (saddleBandCurve z (t - t₀))) ∈ U ∩ (univ ×ˢ O)) :
    ∃ P : ℝ → Plane ≃ₘ[ℝ] Plane,
      ContDiff ℝ ∞ (fun p : ℝ × Plane => P p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Plane => (P p.1).symm p.2) ∧
      P t₀ = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
      (∀ t ∈ Icc (-δ) δ, ∀ u, P t (γ (t₀, u)) = γ (t, u)) ∧
      (∃ V : ι → Set (ℝ × ℝ), ∀ i, IsOpen (V i) ∧ K i ⊆ V i ∧
        (∀ z ∈ V i, (1 - z.1 ^ 2) * z.2 ≠ 0) ∧
        (∀ t ∈ Icc (a i) (b i), ∀ z ∈ V i,
          0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2) ∧
        ∀ t ∈ Icc (a i) (b i), ∀ z ∈ V i, P t (B z) = B (saddleBandCurve z (t - t₀))) ∧
      ∃ S : Set Plane, IsCompact S ∧ S ⊆ O ∧
        ∀ t, EqOn (P t) id Sᶜ ∧ EqOn (P t).symm id Sᶜ := by
  let U' := U ∩ (Ioo (-δ) δ ×ˢ O)
  have hU' : IsOpen U' := hU.inter (isOpen_Ioo.prod hO)
  choose K' hK' hK'int hK'U using fun i => exists_compact_saddleBandCurve_neighborhood B
    isCompact_Icc (hK i) (hreg i) (hrad i) hU' (fun t ht z hz =>
      ⟨(htrace i t ht z hz).1, hJ i ht, (htrace i t ht z hz).2.2⟩)
  let _ : ChartedSpace (EuclideanHalfSpace (0 + 1)) unitInterval :=
    inferInstanceAs (ChartedSpace (EuclideanHalfSpace 1) unitInterval)
  let _ : IsManifold (𝓡∂ (0 + 1)) ∞ unitInterval :=
    inferInstanceAs (IsManifold (𝓡∂ 1) ∞ unitInterval)
  obtain ⟨Γ, hΓ, hΓemb, hΓeq⟩ :=
    exists_isSmoothEmbedding_extension_Icc_halfspace (d := 0) (M := unitInterval)
      (le_trans ht₀flow.1 ht₀flow.2) hγ.contMDiffOn hemb
  have hΓpoint (t : ℝ) (ht : t ∈ Icc (-δ) δ) (u : unitInterval) : Γ (t, u) = γ (t, u) :=
    hΓeq ⟨ht, mem_univ u⟩
  let X : ℝ × Plane → Plane := fun p => B.saddleFiberVectorField p.2
  have hX : ContDiffOn ℝ ∞ X U' := B.contDiffOn_saddleFiberVectorField.comp
    contDiffOn_snd (fun p hp => hUreg p hp.1)
  have hXΓ (t : ℝ) (ht : t ∈ Icc (-δ) δ) (u : unitInterval) (htu : (t, Γ (t, u)) ∈ U') :
      X (t, Γ (t, u)) = deriv (fun q => Γ (q, u)) t := by
    have htflow : t ∈ Ioo (-δ) δ := htu.2.1
    have hevent : (fun q => Γ (q, u)) =ᶠ[𝓝 t] (fun q => γ (q, u)) := by
      filter_upwards [Ioo_mem_nhds htflow.1 htflow.2] with q hq
      exact hΓpoint q (Ioo_subset_Icc_self hq) u
    rw [hevent.deriv_eq, show X (t, Γ (t, u)) = B.saddleFiberVectorField (γ (t, u)) by
      dsimp only [X]; rw [hΓpoint t ht u]]
    exact hUγ t htflow u (by simpa only [hΓpoint t ht u] using htu.1)
  let M : ℝ × (ℝ × ℝ) → ℝ × Plane := fun p =>
    (p.1, B (saddleBandCurve p.2 (p.1 - t₀)))
  have hM (i : ι) : ContinuousOn M (Icc (a i) (b i) ×ˢ K' i) := by
    apply continuousOn_fst.prodMk
    apply B.contDiffOn_comp_saddleBandCurve.continuousOn.comp
      ((continuousOn_fst.sub continuousOn_const).prodMk continuousOn_snd)
    intro p hp
    have hh := hK'U i p.1 hp.1 p.2 hp.2
    exact ⟨(mul_ne_zero_iff.mp hh.1).1, (mul_ne_zero_iff.mp hh.1).2, hh.2.1⟩
  let T := ⋃ i, M '' (Icc (a i) (b i) ×ˢ K' i)
  have hT : IsCompact T := isCompact_iUnion fun i =>
    (isCompact_Icc.prod (hK' i)).image_of_continuousOn (hM i)
  have hTU : T ⊆ U' ∩ (univ ×ˢ O) := by
    intro p hp
    obtain ⟨i, ⟨⟨t, z⟩, ⟨ht, hz⟩, rfl⟩⟩ := mem_iUnion.mp hp
    exact ⟨(hK'U i t ht z hz).2.2, mem_univ _, (hK'U i t ht z hz).2.2.2.2⟩
  let ζ : (Σ i, K' i) → ℝ → Plane := fun z t => B (saddleBandCurve z.2.val (t - t₀))
  have hζd (z : Σ i, K' i) (t : ℝ) (ht : t ∈ Icc (a z.1) (b z.1)) :
      HasDerivAt (ζ z) (X (t, ζ z t)) t := by
    have hz := hK'U z.1 t ht z.2.val z.2.property
    have hd := (B.hasDerivAt_comp_saddleBandCurve (mul_ne_zero_iff.mp hz.1).2 hz.2.1).scomp t
      (show HasDerivAt (fun q : ℝ => q - t₀) 1 t from (hasDerivAt_id t).sub_const t₀)
    simpa only [one_smul, Function.comp_def, ζ, X] using hd
  obtain ⟨F, hF, hFi, _, hFΓ, hFζ, S, hS, hSsub, hFS⟩ :=
    exists_contDiff_compact_ambient_isotopy_halfspace_eqOn_integralCurve (d := 0) hΓ hΓemb hO
      (by
        rintro _ ⟨⟨t, u⟩, ⟨⟨ht, _⟩, _⟩, rfl⟩
        rw [hΓpoint t ht u]
        exact hγO t ht u) hU' hT hTU hX hXΓ
      (a := -δ) (b := δ) (γ := ζ) (c := fun z => a z.1)
      (fun z t ht => (hζd z t ht).continuousAt.continuousWithinAt)
      (fun z t ht => (hζd z t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
      (fun z t ht => mem_iUnion.mpr ⟨z.1, (t, z.2.val), ⟨ht, z.2.property⟩, rfl⟩)
  let P : ℝ → Plane ≃ₘ[ℝ] Plane := fun t => (F t₀).symm.trans (F t)
  have hP : ContDiff ℝ ∞ (fun p : ℝ × Plane => P p.1 p.2) :=
    hF.comp (contDiff_fst.prodMk ((F t₀).symm.contMDiff.contDiff.comp contDiff_snd))
  have hPi : ContDiff ℝ ∞ (fun p : ℝ × Plane => (P p.1).symm p.2) :=
    (F t₀).contMDiff.contDiff.comp hFi
  have hPγ (t : ℝ) (ht : t ∈ Icc (-δ) δ) (u : unitInterval) :
      P t (γ (t₀, u)) = γ (t, u) := by
    change F t ((F t₀).symm (γ (t₀, u))) = γ (t, u)
    rw [← hΓpoint t₀ ht₀flow u, (hFΓ t₀ ht₀flow u).2,
      (hFΓ t ht u).1, hΓpoint t ht u]
  have hPζ (z : Σ i, K' i) (t : ℝ) (ht : t ∈ Icc (a z.1) (b z.1)) :
      P t (B z.2.val) = ζ z t := by
    have hzero : ζ z t₀ = B z.2.val := by simp only [ζ, sub_self, DifferentialGeometry.Analysis.ODE.saddleBandCurve_zero]
    change F t ((F t₀).symm (B z.2.val)) = ζ z t
    rw [← hzero, ← hFζ z t₀ (ht₀ z.1), (F t₀).symm_apply_apply]
    exact hFζ z t ht
  refine ⟨P, hP, hPi, ?_, hPγ,
    ⟨fun i => interior (K' i), ?_⟩, S, hS, hSsub, ?_⟩
  · apply Diffeomorph.ext
    intro x
    exact (F t₀).apply_symm_apply x
  · intro i
    refine ⟨isOpen_interior, hK'int i, ?_, ?_, ?_⟩
    · intro z hz
      exact (hK'U i t₀ (ht₀ i) z (interior_subset hz)).1
    · intro t ht z hz
      exact (hK'U i t ht z (interior_subset hz)).2.1
    · intro t ht z hz
      exact hPζ ⟨i, z, interior_subset hz⟩ t ht
  · intro t
    constructor
    · intro x hx
      change F t ((F t₀).symm x) = x
      rw [(hFS t₀).2 hx, id_eq, (hFS t).1 hx, id_eq]
    · intro x hx
      change F t₀ ((F t).symm x) = x
      rw [(hFS t).2 hx, id_eq, (hFS t₀).1 hx, id_eq]

theorem exists_ambient_isotopy_closing_arc_eqOn_saddleBandCurve_of_endpoint
    {ι : Type*} [Finite ι] {γ : ℝ × unitInterval → Plane}
    (hγ : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {s σ δ t₀ : ℝ} {a b : ι → ℝ}
    (hσ : σ ^ 2 = 1)
    (ht₀flow : t₀ ∈ Icc (-δ) δ) (ht₀ : ∀ i, t₀ ∈ Icc (a i) (b i))
    (hJ : ∀ i, Icc (a i) (b i) ⊆ Ioo (-δ) δ)
    (hemb : ∀ t ∈ Icc (-δ) δ,
      IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => γ (t, u)))
    {K : ι → Set (ℝ × ℝ)} (hK : ∀ i, IsCompact (K i))
    (hreg : ∀ i, ∀ z ∈ K i, (1 - z.1 ^ 2) * z.2 ≠ 0)
    (hrad : ∀ i, ∀ t ∈ Icc (a i) (b i), ∀ z ∈ K i,
      0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2)
    {U : Set (ℝ × Plane)} (hU : IsOpen U)
    (hUreg : ∀ p ∈ U, (1 - (B.symm p.2).1 ^ 2) * (B.symm p.2).2 ≠ 0)
    {W : Set unitInterval} {v : unitInterval → ℝ}
    (hUend : ∀ t ∈ Ioo (-δ) δ, ∀ u, (t, γ (t, u)) ∈ U → u ∈ W)
    (hendpoint : ∀ u ∈ W, v u ∈ Ioo (-1 : ℝ) 1 ∧
      ∀ t ∈ Icc (-δ) δ, γ (t, u) = B (saddleBandLevelCurve s t σ (v u)))
    {O : Set Plane} (hO : IsOpen O)
    (hγO : ∀ t ∈ Icc (-δ) δ, ∀ u, γ (t, u) ∈ O)
    (htrace : ∀ i, ∀ t ∈ Icc (a i) (b i), ∀ z ∈ K i,
      (t, B (saddleBandCurve z (t - t₀))) ∈ U ∩ (univ ×ˢ O)) :
    ∃ P : ℝ → Plane ≃ₘ[ℝ] Plane,
      ContDiff ℝ ∞ (fun p : ℝ × Plane => P p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × Plane => (P p.1).symm p.2) ∧
      P t₀ = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
      (∀ t ∈ Icc (-δ) δ, ∀ u, P t (γ (t₀, u)) = γ (t, u)) ∧
      (∃ V : ι → Set (ℝ × ℝ), ∀ i, IsOpen (V i) ∧ K i ⊆ V i ∧
        (∀ z ∈ V i, (1 - z.1 ^ 2) * z.2 ≠ 0) ∧
        (∀ t ∈ Icc (a i) (b i), ∀ z ∈ V i,
          0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2) ∧
        ∀ t ∈ Icc (a i) (b i), ∀ z ∈ V i, P t (B z) = B (saddleBandCurve z (t - t₀))) ∧
      ∃ S : Set Plane, IsCompact S ∧ S ⊆ O ∧
        ∀ t, EqOn (P t) id Sᶜ ∧ EqOn (P t).symm id Sᶜ := by
  apply exists_ambient_isotopy_closing_arc_eqOn_saddleBandCurve hγ B ht₀flow ht₀ hJ
    hemb hK hreg hrad hU hUreg _ hO hγO htrace
  intro t ht u htu
  have huW := hUend t ht u htu
  have hu := (hendpoint u huW).1
  have hden : 0 < 1 - (v u) ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hu.2) (by linarith [hu.1] : 0 < v u + 1)]
  have hregular := hUreg (t, γ (t, u)) htu
  have hγt := (hendpoint u huW).2 t (Ioo_subset_Icc_self ht)
  rw [hγt, B.symm_apply_apply] at hregular
  have hpos : 0 < t + s * (v u) ^ 2 := by
    by_contra hn
    have hsqrt : Real.sqrt (2 * (t + s * (v u) ^ 2) / (1 - (v u) ^ 2)) = 0 :=
      Real.sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num) (le_of_not_gt hn)) hden.le)
    simp only [saddleBandLevelCurve, hsqrt, mul_zero, ne_eq, not_true_eq_false] at hregular
  have hevent : (fun q => γ (q, u)) =ᶠ[𝓝 t]
      (fun q => B (saddleBandLevelCurve s q σ (v u))) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with q hq
    exact (hendpoint u huW).2 q (Ioo_subset_Icc_self hq)
  have hd := (B.contMDiff.contDiff.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_saddleBandLevelCurve_time_of_pos hpos hσ hu)
  have hd' : HasDerivAt (fun q => B (saddleBandLevelCurve s q σ (v u)))
      (B.saddleFiberVectorField (B (saddleBandLevelCurve s t σ (v u)))) t := by
    simpa only [Diffeomorph.saddleFiberVectorField, B.symm_apply_apply, Function.comp_def] using hd
  rw [(hd'.congr_of_eventuallyEq hevent).deriv, hγt]

theorem exists_saddle_trace_neighborhood
    {γ : ℝ × unitInterval → Plane} (hγ : Continuous γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {s σ h a b δ : ℝ}
    (hs : 0 ≤ s) (hσ : σ ^ 2 = 1) (hh1 : h < 1)
    (hwindow : Icc a b ⊆ Ioo (0 : ℝ) δ)
    (hemb : ∀ t ∈ Icc a b, Function.Injective (fun u => γ (t, u)))
    {W : Set unitInterval} (hW : IsOpen W) (hW0 : (0 : unitInterval) ∈ W)
    (hW1 : (1 : unitInterval) ∈ W)
    (hends : ∀ t ∈ Icc a b,
      γ (t, 0) = B (saddleBandLevelCurve s t σ (-h)) ∧
      γ (t, 1) = B (saddleBandLevelCurve s t σ h))
    {C : ℝ → Set Plane}
    (hcut : ∀ t ∈ Icc a b, IsCutPair (C t)
      (B (saddleBandLevelCurve s t σ (-h))) (B (saddleBandLevelCurve s t σ h))
      (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h)) (range (fun u => γ (t, u)))) :
    ∃ U : Set (ℝ × Plane), IsOpen U ∧
      (∀ t ∈ Icc a b, ∀ u ∈ Icc (-h) h, (t, B (saddleBandLevelCurve s t σ u)) ∈ U) ∧
      (∀ p ∈ U, (1 - (B.symm p.2).1 ^ 2) * (B.symm p.2).2 ≠ 0) ∧
      ∀ t ∈ Icc a b, ∀ u, (t, γ (t, u)) ∈ U → u ∈ W := by
  let T := (fun p : ℝ × unitInterval => (p.1, γ p)) '' (Icc a b ×ˢ Wᶜ)
  have hT : IsCompact T := (isCompact_Icc.prod hW.isClosed_compl.isCompact).image
    (continuous_fst.prodMk hγ)
  let U := Tᶜ ∩ {p : ℝ × Plane | (1 - (B.symm p.2).1 ^ 2) * (B.symm p.2).2 ≠ 0}
  have hU : IsOpen U :=
    hT.isClosed.isOpen_compl.inter (isOpen_ne_fun (by fun_prop) continuous_const)
  refine ⟨U, hU, ?_, fun _ hp => hp.2, ?_⟩
  · intro t ht u hu
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨v, r⟩, ⟨hv, hr⟩, heq⟩
      have hvt : v = t := congrArg Prod.fst heq
      subst v
      have hyr : γ (t, r) = B (saddleBandLevelCurve s t σ u) := congrArg Prod.snd heq
      have hinter := (hcut t ht).inter_eq.subset
        ⟨⟨saddleBandLevelCurve s t σ u, ⟨u, hu, rfl⟩, rfl⟩, ⟨r, hyr⟩⟩
      rcases hinter with hp | hp
      · have hr0 : r = 0 := hemb t ht (hyr.trans (hp.trans (hends t ht).1.symm))
        exact hr (hr0.symm ▸ hW0)
      · have hr1 : r = 1 := hemb t ht (hyr.trans (hp.trans (hends t ht).2.symm))
        exact hr (hr1.symm ▸ hW1)
    · change (1 - (B.symm (B (saddleBandLevelCurve s t σ u))).1 ^ 2) *
        (B.symm (B (saddleBandLevelCurve s t σ u))).2 ≠ 0
      rw [B.symm_apply_apply]
      exact saddleBandLevelCurve_regular_of_pos
        (add_pos_of_pos_of_nonneg (hwindow ht).1 (mul_nonneg hs (sq_nonneg u)))
        (by intro h; rw [h] at hσ; norm_num at hσ)
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · intro t ht u hu
    by_contra hn
    exact hu.1 ⟨(t, u), ⟨ht, hn⟩, rfl⟩

theorem exists_ambient_isotopy_closing_arc_eqOn_saddle_of_isOpen
    {γ : ℝ × unitInterval → Plane}
    (hγ : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {s σ h δ t₀ : ℝ}
    (hs : 0 ≤ s) (hσ : σ ^ 2 = 1) (hh1 : h < 1) (ht₀ : t₀ ∈ Ioo (0 : ℝ) δ)
    (hemb : ∀ t ∈ Icc (-δ) δ,
      IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => γ (t, u)))
    {W : Set unitInterval} (hW : IsOpen W) (hW0 : (0 : unitInterval) ∈ W)
    (hW1 : (1 : unitInterval) ∈ W) {v : unitInterval → ℝ}
    (hendpoint : ∀ u ∈ W, v u ∈ Ioo (-1 : ℝ) 1 ∧
      ∀ t ∈ Icc (-δ) δ, γ (t, u) = B (saddleBandLevelCurve s t σ (v u)))
    (hends : ∀ t ∈ Ioc (0 : ℝ) δ,
      γ (t, 0) = B (saddleBandLevelCurve s t σ (-h)) ∧
      γ (t, 1) = B (saddleBandLevelCurve s t σ h))
    {C : ℝ → Set Plane}
    (hcut : ∀ t ∈ Ioc (0 : ℝ) δ, IsCutPair (C t)
      (B (saddleBandLevelCurve s t σ (-h))) (B (saddleBandLevelCurve s t σ h))
      (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h)) (range (fun u => γ (t, u))))
    {O : Set Plane} (hO : IsOpen O)
    (hγO : ∀ t ∈ Icc (-δ) δ, ∀ u, γ (t, u) ∈ O)
    (hκO : B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h) ⊆ O) :
    ∃ ε > 0, Icc (t₀ - ε) (t₀ + ε) ⊆ Ioo (0 : ℝ) δ ∧
      ∃ P : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun p : ℝ × Plane => P p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × Plane => (P p.1).symm p.2) ∧
        P t₀ = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
        (∀ t ∈ Icc (-δ) δ, ∀ u, P t (γ (t₀, u)) = γ (t, u)) ∧
        (∃ V : Set (ℝ × ℝ), IsOpen V ∧ saddleBandLevelCurve s t₀ σ '' Icc (-h) h ⊆ V ∧
          (∀ z ∈ V, z.1 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < σ * z.2) ∧
          (∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ∀ z ∈ V,
            0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2) ∧
          ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ∀ z ∈ V,
            P t (B z) = B (saddleBandCurve z (t - t₀))) ∧
        (∀ t ∈ Icc (t₀ - ε) (t₀ + ε), P t '' C t₀ = C t) ∧
        ∃ S : Set Plane, IsCompact S ∧ S ⊆ O ∧ ∀ t, EqOn (P t) id Sᶜ ∧ EqOn (P t).symm id Sᶜ := by
  have hδ : 0 < δ := ht₀.1.trans ht₀.2
  let D₀ : Set (ℝ × ℝ) := Ioo (0 : ℝ) δ ×ˢ Ioo (-1 : ℝ) 1
  let f₀ : ℝ × ℝ → Plane := fun z => B (saddleBandLevelCurve s z.1 σ z.2)
  have hf₀ : ContinuousOn f₀ D₀ := B.continuous.comp_continuousOn
    ((contDiffOn_saddleBandLevelCurve_family s σ).continuousOn.mono (fun z hz =>
      ⟨hz.2, add_pos_of_pos_of_nonneg hz.1.1 (mul_nonneg hs (sq_nonneg z.2))⟩))
  have hD₀ : IsOpen D₀ := isOpen_Ioo.prod isOpen_Ioo
  have hseed : ({t₀} : Set ℝ) ×ˢ Icc (-h) h ⊆ D₀ ∩ f₀ ⁻¹' O := by
    rintro ⟨t, u⟩ ⟨ht, hu⟩
    have ht' : t = t₀ := ht
    subst t
    exact ⟨⟨ht₀, ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩,
      hκO ⟨_, ⟨u, hu, rfl⟩, rfl⟩⟩
  obtain ⟨T₀, U₁, hT₀, _, ht₀T₀, hIU₁, hT₀U₁⟩ := generalized_tube_lemma
    isCompact_singleton isCompact_Icc (hf₀.isOpen_inter_preimage hD₀ hO) hseed
  obtain ⟨a₀, b₀, ht₀ab, habT⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hT₀.inter isOpen_Ioo).mem_nhds ⟨ht₀T₀ (mem_singleton t₀), ht₀⟩)
  let a := (a₀ + t₀) / 2
  let b := (t₀ + b₀) / 2
  have hat₀ : a < t₀ := by dsimp [a]; linarith [ht₀ab.1]
  have ht₀b : t₀ < b := by dsimp [b]; linarith [ht₀ab.2]
  have habsmall : Icc a b ⊆ Ioo a₀ b₀ := by
    intro t ht
    dsimp [a, b] at ht
    constructor <;> linarith [ht₀ab.1, ht₀ab.2, ht.1, ht.2]
  have hJa : Icc a b ⊆ Ioo (0 : ℝ) δ := fun _ ht => (habT (habsmall ht)).2
  have hselectedO (t : ℝ) (ht : t ∈ Icc a b) (u : ℝ) (hu : u ∈ Icc (-h) h) :
      B (saddleBandLevelCurve s t σ u) ∈ O :=
    (hT₀U₁ (a := (t, u)) ⟨(habT (habsmall ht)).1, hIU₁ hu⟩).2
  have hJflow : Icc a b ⊆ Icc (-δ) δ := fun t ht =>
    ⟨by linarith [(hJa ht).1], (hJa ht).2.le⟩
  obtain ⟨U₀, hU₀, htrace₀, hUreg, hUend⟩ :=
    exists_saddle_trace_neighborhood hγ.continuous B hs hσ hh1 hJa
    (fun t ht => (hemb t (hJflow ht)).isEmbedding.injective) hW hW0 hW1
    (fun t ht => hends t ⟨(hJa ht).1, (hJa ht).2.le⟩)
    (fun t ht => hcut t ⟨(hJa ht).1, (hJa ht).2.le⟩)
  let U := U₀ ∩ (Ioo a b ×ˢ O)
  have hU : IsOpen U := hU₀.inter (isOpen_Ioo.prod hO)
  let ε := min ((t₀ - a) / 2) ((b - t₀) / 2)
  have hε : 0 < ε := lt_min (half_pos (sub_pos.mpr hat₀)) (half_pos (sub_pos.mpr ht₀b))
  have hJa' : Icc (t₀ - ε) (t₀ + ε) ⊆ Ioo a b := by
    intro t ht
    have hε₁ : ε ≤ (t₀ - a) / 2 := min_le_left _ _
    have hε₂ : ε ≤ (b - t₀) / 2 := min_le_right _ _
    constructor <;> linarith [ht.1, ht.2]
  have hJsub : Icc (t₀ - ε) (t₀ + ε) ⊆ Icc a b :=
    hJa'.trans Ioo_subset_Icc_self
  have htrace : ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ∀ u ∈ Icc (-h) h,
      (t, B (saddleBandLevelCurve s t σ u)) ∈ U := by
    intro t ht u hu
    exact ⟨htrace₀ t (hJsub ht) u hu, hJa' ht, hselectedO t (hJsub ht) u hu⟩
  have huone (u : ℝ) (hu : u ∈ Icc (-h) h) : u ∈ Ioo (-1 : ℝ) 1 :=
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hpos (t : ℝ) (ht : t ∈ Icc (t₀ - ε) (t₀ + ε)) (u : ℝ) :
      0 < t + s * u ^ 2 :=
    add_pos_of_pos_of_nonneg (hJa (hJsub ht)).1 (mul_nonneg hs (sq_nonneg u))
  have ht₀small : t₀ ∈ Icc (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have ht₀flow := hJflow (hJsub ht₀small)
  let K := saddleBandLevelCurve s t₀ σ '' Icc (-h) h
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    ((contDiffOn_saddleBandLevelCurve hs ht₀.1 σ).continuousOn.mono huone)
  have hreg : ∀ z ∈ K, (1 - z.1 ^ 2) * z.2 ≠ 0 := by
    rintro _ ⟨u, hu, rfl⟩
    exact saddleBandLevelCurve_regular_of_pos (hpos t₀ ht₀small u)
      (by intro heq; rw [heq] at hσ; norm_num at hσ) (huone u hu)
  have hrad : ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ∀ z ∈ K,
      0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2 := by
    rintro t ht _ ⟨u, hu, rfl⟩
    change 0 < 1 + 2 * (1 - u ^ 2)⁻¹ * (t - t₀) /
      (saddleBandLevelCurve s t₀ σ u).2 ^ 2
    rw [saddleBandLevelCurve_flow_radicand (hpos t₀ ht₀small u) hσ (huone u hu)]
    exact div_pos (hpos t ht u) (hpos t₀ ht₀small u)
  have hflow (t : ℝ) (ht : t ∈ Icc (t₀ - ε) (t₀ + ε)) (u : ℝ)
      (hu : u ∈ Icc (-h) h) :
      saddleBandCurve (saddleBandLevelCurve s t₀ σ u) (t - t₀) =
        saddleBandLevelCurve s t σ u :=
    saddleBandCurve_saddleBandLevelCurve (hpos t₀ ht₀small u) (hpos t ht u).le hσ (huone u hu)
  obtain ⟨P, hP, hPi, hP₀, hPγ, ⟨V₀, hV₀⟩, S, hS, hSsub, hPS⟩ :=
    exists_ambient_isotopy_closing_arc_eqOn_saddleBandCurve_of_endpoint
      (ι := Unit) (K := fun _ => K) (a := fun _ => t₀ - ε) (b := fun _ => t₀ + ε)
      hγ B hσ ht₀flow (fun _ => ht₀small)
      (fun _ _ ht => ⟨by linarith [(hJa (hJsub ht)).1], (hJa (hJsub ht)).2⟩)
      hemb (fun _ => hK) (fun _ => hreg) (fun _ => hrad) hU (fun p hp => hUreg p hp.1)
      (fun t _ u htu => hUend t (Ioo_subset_Icc_self htu.2.1) u htu.1)
      hendpoint hO hγO (by
        rintro _ t ht _ ⟨u, hu, rfl⟩
        rw [hflow t ht u hu]
        exact ⟨htrace t ht u hu, mem_univ _, hselectedO t (hJsub ht) u hu⟩)
  let V := V₀ () ∩ (Ioo (-1 : ℝ) 1 ×ˢ {y : ℝ | 0 < σ * y})
  have hV : IsOpen V := (hV₀ ()).1.inter
    (isOpen_Ioo.prod (isOpen_lt continuous_const (continuous_const.mul continuous_id)))
  have hselectedV : saddleBandLevelCurve s t₀ σ '' Icc (-h) h ⊆ V := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨(hV₀ ()).2.1 ⟨u, hu, rfl⟩, huone u hu, ?_⟩
    change 0 < σ * (σ * Real.sqrt (2 * (t₀ + s * u ^ 2) / (1 - u ^ 2)))
    rw [← mul_assoc, ← sq, hσ, one_mul]
    apply Real.sqrt_pos.mpr
    have hden : 0 < 1 - u ^ 2 := by
      have hunit := huone u hu
      nlinarith [mul_pos (sub_pos.mpr hunit.2) (by linarith [hunit.1] : 0 < u + 1)]
    exact div_pos (mul_pos (by norm_num) (hpos t₀ ht₀small u)) hden
  have hPVflow (t : ℝ) (ht : t ∈ Icc (t₀ - ε) (t₀ + ε)) (z : ℝ × ℝ) (hz : z ∈ V) :
      P t (B z) = B (saddleBandCurve z (t - t₀)) :=
    (hV₀ ()).2.2.2.2 t ht z hz.1
  have hPselected (t : ℝ) (ht : t ∈ Icc (t₀ - ε) (t₀ + ε)) :
      P t '' (B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h)) =
        B '' (saddleBandLevelCurve s t σ '' Icc (-h) h) := by
    have hp (u : ℝ) (hu : u ∈ Icc (-h) h) :
        P t (B (saddleBandLevelCurve s t₀ σ u)) = B (saddleBandLevelCurve s t σ u) := by
      rw [hPVflow t ht _ (hselectedV ⟨u, hu, rfl⟩), hflow t ht u hu]
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨u, hu, rfl⟩, (hp u hu).symm⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, hp u hu⟩
  refine ⟨ε, hε, hJsub.trans hJa, P, hP, hPi, hP₀, hPγ,
    ⟨V, hV, hselectedV, fun _ hz => hz.2,
      fun t ht z hz => (hV₀ ()).2.2.2.1 t ht z hz.1, hPVflow⟩, ?_, S, hS, hSsub, hPS⟩
  intro t ht
  have hct := hcut t ⟨(hJa (hJsub ht)).1, (hJa (hJsub ht)).2.le⟩
  have hc₀ := hcut t₀ ⟨ht₀.1, ht₀.2.le⟩
  rw [← hc₀.union_eq, image_union, hPselected t ht]
  rw [show P t '' range (fun u => γ (t₀, u)) = range (fun u => γ (t, u)) by
    rw [← range_comp]; congr 1; funext u; exact hPγ t (hJflow (hJsub ht)) u]
  exact hct.union_eq

theorem exists_ambient_isotopy_closing_arc_eqOn_saddle_fixed_near_origin
    {γ : ℝ × unitInterval → Plane}
    (hγ : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {s σ h δ t₀ : ℝ}
    (hs : 0 ≤ s) (hσ : σ ^ 2 = 1) (hh1 : h < 1) (ht₀ : t₀ ∈ Ioo (0 : ℝ) δ)
    (hemb : ∀ t ∈ Icc (-δ) δ,
      IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => γ (t, u)))
    {W : Set unitInterval} (hW : IsOpen W) (hW0 : (0 : unitInterval) ∈ W)
    (hW1 : (1 : unitInterval) ∈ W) {v : unitInterval → ℝ}
    (hendpoint : ∀ u ∈ W, v u ∈ Ioo (-1 : ℝ) 1 ∧
      ∀ t ∈ Icc (-δ) δ, γ (t, u) = B (saddleBandLevelCurve s t σ (v u)))
    (hends : ∀ t ∈ Ioc (0 : ℝ) δ,
      γ (t, 0) = B (saddleBandLevelCurve s t σ (-h)) ∧
      γ (t, 1) = B (saddleBandLevelCurve s t σ h))
    {C : ℝ → Set Plane}
    (hcut : ∀ t ∈ Ioc (0 : ℝ) δ, IsCutPair (C t)
      (B (saddleBandLevelCurve s t σ (-h))) (B (saddleBandLevelCurve s t σ h))
      (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h)) (range (fun u => γ (t, u))))
    (havoid : ∀ t ∈ Icc (-δ) δ, ∀ u, γ (t, u) ≠ B (0, 0)) :
    ∃ ε > 0, Icc (t₀ - ε) (t₀ + ε) ⊆ Ioo (0 : ℝ) δ ∧
      ∃ P : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun p : ℝ × Plane => P p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × Plane => (P p.1).symm p.2) ∧
        P t₀ = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
        (∀ t ∈ Icc (-δ) δ, ∀ u, P t (γ (t₀, u)) = γ (t, u)) ∧
        (∃ V : Set (ℝ × ℝ), IsOpen V ∧ saddleBandLevelCurve s t₀ σ '' Icc (-h) h ⊆ V ∧
          (∀ z ∈ V, z.1 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < σ * z.2) ∧
          (∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ∀ z ∈ V,
            0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2) ∧
          ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ∀ z ∈ V,
            P t (B z) = B (saddleBandCurve z (t - t₀))) ∧
        (∀ t ∈ Icc (t₀ - ε) (t₀ + ε), P t '' C t₀ = C t) ∧
        ∃ ρ > 0, ∃ S : Set Plane, IsCompact S ∧
          S ⊆ (B '' Metric.closedBall (0 : ℝ × ℝ) ρ)ᶜ ∧
          ∀ t, EqOn (P t) id Sᶜ ∧ EqOn (P t).symm id Sᶜ := by
  let O : Set Plane := {B (0, 0)}ᶜ
  have hO : IsOpen O := isClosed_singleton.isOpen_compl
  have hγO : ∀ t ∈ Icc (-δ) δ, ∀ u, γ (t, u) ∈ O := havoid
  have hκO : B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h) ⊆ O := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩ heq
    have hz : saddleBandLevelCurve s t₀ σ u = (0, 0) := B.injective heq
    have hreg := saddleBandLevelCurve_regular_of_pos
      (add_pos_of_pos_of_nonneg ht₀.1 (mul_nonneg hs (sq_nonneg u)))
      (show σ ≠ 0 by intro heq; rw [heq] at hσ; norm_num at hσ)
      (show u ∈ Ioo (-1 : ℝ) 1 by constructor <;> linarith [hu.1, hu.2])
    rw [hz] at hreg
    norm_num at hreg
  obtain ⟨ε, hε, hJ, P, hP, hPi, hP₀, hParc, hPV, hPC, S, hS, hSO, hPS⟩ :=
    exists_ambient_isotopy_closing_arc_eqOn_saddle_of_isOpen
      hγ B hs hσ hh1 ht₀ hemb hW hW0 hW1 hendpoint hends hcut hO hγO hκO
  have hzero : (0 : ℝ × ℝ) ∈ B ⁻¹' Sᶜ := by
    intro hz
    exact hSO hz (mem_singleton _)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (hS.isClosed.isOpen_compl.preimage B.continuous) 0 hzero
  have hsub : S ⊆ (B '' Metric.closedBall (0 : ℝ × ℝ) (r / 2))ᶜ := by
    rintro y hy ⟨z, hz, rfl⟩
    exact hball (Metric.closedBall_subset_ball (half_lt_self hr) hz) hy
  exact ⟨ε, hε, hJ, P, hP, hPi, hP₀, hParc, hPV, hPC,
    r / 2, half_pos hr, S, hS, hsub, hPS⟩

theorem exists_ambient_isotopy_closing_arc_eqOn_saddle
    {γ : ℝ × unitInterval → Plane}
    (hγ : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {s σ h δ t₀ : ℝ}
    (hs : 0 ≤ s) (hσ : σ ^ 2 = 1) (hh1 : h < 1) (ht₀ : t₀ ∈ Ioo (0 : ℝ) δ)
    (hemb : ∀ t ∈ Icc (-δ) δ,
      IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => γ (t, u)))
    {W : Set unitInterval} (hW : IsOpen W) (hW0 : (0 : unitInterval) ∈ W)
    (hW1 : (1 : unitInterval) ∈ W) {v : unitInterval → ℝ}
    (hendpoint : ∀ u ∈ W, v u ∈ Ioo (-1 : ℝ) 1 ∧
      ∀ t ∈ Icc (-δ) δ, γ (t, u) = B (saddleBandLevelCurve s t σ (v u)))
    (hends : ∀ t ∈ Ioc (0 : ℝ) δ,
      γ (t, 0) = B (saddleBandLevelCurve s t σ (-h)) ∧
      γ (t, 1) = B (saddleBandLevelCurve s t σ h))
    {C : ℝ → Set Plane}
    (hcut : ∀ t ∈ Ioc (0 : ℝ) δ, IsCutPair (C t)
      (B (saddleBandLevelCurve s t σ (-h))) (B (saddleBandLevelCurve s t σ h))
      (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h)) (range (fun u => γ (t, u)))) :
    ∃ ε > 0, Icc (t₀ - ε) (t₀ + ε) ⊆ Ioo (0 : ℝ) δ ∧
      ∃ P : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun p : ℝ × Plane => P p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × Plane => (P p.1).symm p.2) ∧
        P t₀ = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
        (∀ t ∈ Icc (-δ) δ, ∀ u, P t (γ (t₀, u)) = γ (t, u)) ∧
        (∃ V : Set (ℝ × ℝ), IsOpen V ∧ saddleBandLevelCurve s t₀ σ '' Icc (-h) h ⊆ V ∧
          (∀ z ∈ V, z.1 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < σ * z.2) ∧
          (∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ∀ z ∈ V,
            0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2) ∧
          ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ∀ z ∈ V,
            P t (B z) = B (saddleBandCurve z (t - t₀))) ∧
        (∀ t ∈ Icc (t₀ - ε) (t₀ + ε), P t '' C t₀ = C t) ∧
        ∃ S : Set Plane, IsCompact S ∧ ∀ t, EqOn (P t) id Sᶜ ∧ EqOn (P t).symm id Sᶜ := by
  obtain ⟨ε, hε, hJ, P, hP, hPi, hP₀, hParc, hPV, hPC, S, hS, _, hPS⟩ :=
    exists_ambient_isotopy_closing_arc_eqOn_saddle_of_isOpen
      hγ B hs hσ hh1 ht₀ hemb hW hW0 hW1 hendpoint hends hcut
      isOpen_univ (fun _ _ _ => mem_univ _) (subset_univ _)
  exact ⟨ε, hε, hJ, P, hP, hPi, hP₀, hParc, hPV, hPC, S, hS, hPS⟩

theorem exists_saddle_outer_trace_neighborhood
    {γ : ℝ × unitInterval → Plane} (hγ : Continuous γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {s σ h δ ρ : ℝ}
    (hs : 0 ≤ s) (hh1 : h < 1) (hδsh : 4 * δ < s * h ^ 2)
    (hemb : ∀ t ∈ Icc (-δ) δ, Function.Injective (fun u => γ (t, u)))
    {W : Set unitInterval} (hW : IsOpen W) (hW0 : (0 : unitInterval) ∈ W)
    (hW1 : (1 : unitInterval) ∈ W)
    (hends : ∀ t ∈ Icc (-δ) δ,
      γ (t, 0) = B (saddleBandLevelCurve s t σ (-h)) ∧
      γ (t, 1) = B (saddleBandLevelCurve s t σ h))
    (hcontact : ∀ t ∈ Icc (-δ) δ, ∀ r,
      B.symm (γ (t, r)) ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ →
      B.symm (γ (t, r)) = saddleBandLevelCurve s t σ (-h) ∨
        B.symm (γ (t, r)) = saddleBandLevelCurve s t σ h)
    (hbox : ∀ t ∈ Icc (-δ) δ, ∀ σ' : ℝ, σ' ^ 2 = 1 →
      ∀ u ∈ Icc (-h) h, h ^ 2 / 4 ≤ u ^ 2 →
        saddleBandLevelCurve s t σ' u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ) :
    ∃ U : Set (ℝ × Plane), IsOpen U ∧
      (∀ t ∈ Icc (-δ) δ, ∀ σ' : ℝ, σ' ^ 2 = 1 →
        ∀ u ∈ Icc (-h) h, h ^ 2 / 4 ≤ u ^ 2 →
          (t, B (saddleBandLevelCurve s t σ' u)) ∈ U) ∧
      (∀ p ∈ U, (1 - (B.symm p.2).1 ^ 2) * (B.symm p.2).2 ≠ 0) ∧
      ∀ t ∈ Icc (-δ) δ, ∀ r, (t, γ (t, r)) ∈ U → r ∈ W := by
  let T := (fun p : ℝ × unitInterval => (p.1, γ p)) '' (Icc (-δ) δ ×ˢ Wᶜ)
  have hT : IsCompact T := (isCompact_Icc.prod hW.isClosed_compl.isCompact).image
    (continuous_fst.prodMk hγ)
  let U := Tᶜ ∩ {p : ℝ × Plane | (1 - (B.symm p.2).1 ^ 2) * (B.symm p.2).2 ≠ 0}
  have hU : IsOpen U :=
    hT.isClosed.isOpen_compl.inter (isOpen_ne_fun (by fun_prop) continuous_const)
  refine ⟨U, hU, ?_, fun _ hp => hp.2, ?_⟩
  · intro t ht σ' hσ' u hu hhu
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨v, r⟩, ⟨hv, hr⟩, heq⟩
      have hvt : v = t := congrArg Prod.fst heq
      subst v
      have hyr : γ (t, r) = B (saddleBandLevelCurve s t σ' u) := congrArg Prod.snd heq
      have hc := hcontact t ht r (by
        rw [hyr, B.symm_apply_apply]
        exact hbox t ht σ' hσ' u hu hhu)
      rcases hc with hc | hc
      · have heq : γ (t, r) = B (saddleBandLevelCurve s t σ (-h)) := by
          rw [← hc, B.apply_symm_apply]
        have hr0 : r = 0 := hemb t ht (heq.trans (hends t ht).1.symm)
        exact hr (hr0.symm ▸ hW0)
      · have heq : γ (t, r) = B (saddleBandLevelCurve s t σ h) := by
          rw [← hc, B.apply_symm_apply]
        have hr1 : r = 1 := hemb t ht (heq.trans (hends t ht).2.symm)
        exact hr (hr1.symm ▸ hW1)
    · change (1 - (B.symm (B (saddleBandLevelCurve s t σ' u))).1 ^ 2) *
        (B.symm (B (saddleBandLevelCurve s t σ' u))).2 ≠ 0
      rw [B.symm_apply_apply]
      have hrad : 0 < t + s * u ^ 2 := by
        have hh := mul_le_mul_of_nonneg_left hhu hs
        nlinarith [ht.1]
      exact saddleBandLevelCurve_regular_of_pos hrad
        (by intro heq; rw [heq] at hσ'; norm_num at hσ')
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · intro t ht r hr
    by_contra hn
    exact hr.1 ⟨(t, r), ⟨ht, hn⟩, rfl⟩

theorem exists_ambient_isotopy_closing_arc_eqOn_saddle_outer_branches
    {γ : ℝ × unitInterval → Plane}
    (hγ : ContMDiff (𝓘(ℝ).prod (𝓡∂ 1)) 𝓘(ℝ, Plane) ∞ γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {s σ h δ η t₀ ρ : ℝ}
    (hs : 0 ≤ s) (hσ : σ ^ 2 = 1) (hh1 : h < 1)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) η) (hηδ : η < δ) (hδsh : 4 * δ < s * h ^ 2)
    (hemb : ∀ t ∈ Icc (-δ) δ,
      IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, Plane) ∞ (fun u => γ (t, u)))
    {W : Set unitInterval} (hW : IsOpen W) (hW0 : (0 : unitInterval) ∈ W)
    (hW1 : (1 : unitInterval) ∈ W) {v : unitInterval → ℝ}
    (hendpoint : ∀ u ∈ W, v u ∈ Ioo (-1 : ℝ) 1 ∧
      ∀ t ∈ Icc (-δ) δ, γ (t, u) = B (saddleBandLevelCurve s t σ (v u)))
    (hends : ∀ t ∈ Icc (-δ) δ,
      γ (t, 0) = B (saddleBandLevelCurve s t σ (-h)) ∧
      γ (t, 1) = B (saddleBandLevelCurve s t σ h))
    {C : ℝ → Set Plane}
    (hcut : ∀ t ∈ Ioc (0 : ℝ) δ, IsCutPair (C t)
      (B (saddleBandLevelCurve s t σ (-h))) (B (saddleBandLevelCurve s t σ h))
      (B '' (saddleBandLevelCurve s t σ '' Icc (-h) h)) (range (fun u => γ (t, u))))
    (hcontact : ∀ t ∈ Icc (-δ) δ, ∀ r,
      B.symm (γ (t, r)) ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ →
      B.symm (γ (t, r)) = saddleBandLevelCurve s t σ (-h) ∨
        B.symm (γ (t, r)) = saddleBandLevelCurve s t σ h)
    (hbox : ∀ t ∈ Icc (-δ) δ, ∀ σ' : ℝ, σ' ^ 2 = 1 →
      ∀ u ∈ Icc (-h) h, h ^ 2 / 4 ≤ u ^ 2 →
        saddleBandLevelCurve s t σ' u ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ)
    {O : Set Plane} (hO : IsOpen O)
    (hγO : ∀ t ∈ Icc (-δ) δ, ∀ u, γ (t, u) ∈ O)
    (hκO : B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h) ⊆ O)
    (houterO : ∀ t ∈ Icc (-η) η, ∀ σ' : ℝ, σ' ^ 2 = 1 →
      ∀ u ∈ Icc (-h) h, h ^ 2 / 4 ≤ u ^ 2 → B (saddleBandLevelCurve s t σ' u) ∈ O) :
    ∃ ε > 0, Icc (t₀ - ε) (t₀ + ε) ⊆ Ioo (0 : ℝ) η ∧
      ∃ P : ℝ → Plane ≃ₘ[ℝ] Plane,
        ContDiff ℝ ∞ (fun p : ℝ × Plane => P p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × Plane => (P p.1).symm p.2) ∧
        P t₀ = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
        (∀ t ∈ Icc (-δ) δ, ∀ u, P t (γ (t₀, u)) = γ (t, u)) ∧
        (∃ V : Set (ℝ × ℝ), IsOpen V ∧
          (∀ σ' : ℝ, σ' ^ 2 = 1 → ∀ u ∈ Icc (-h) h, h ^ 2 / 4 ≤ u ^ 2 →
            saddleBandLevelCurve s t₀ σ' u ∈ V) ∧
          (∀ z ∈ V, z.1 ∈ Ioo (-1 : ℝ) 1 ∧ z.2 ≠ 0) ∧
          (∀ t ∈ Icc (-η) η, ∀ z ∈ V,
            0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2) ∧
          ∀ t ∈ Icc (-η) η, ∀ z ∈ V,
            P t (B z) = B (saddleBandCurve z (t - t₀))) ∧
        (∃ V : Set (ℝ × ℝ), IsOpen V ∧ saddleBandLevelCurve s t₀ σ '' Icc (-h) h ⊆ V ∧
          (∀ z ∈ V, z.1 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < σ * z.2) ∧
          (∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ∀ z ∈ V,
            0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2) ∧
          ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), ∀ z ∈ V,
            P t (B z) = B (saddleBandCurve z (t - t₀))) ∧
        (∀ t ∈ Icc (t₀ - ε) (t₀ + ε), P t '' C t₀ = C t) ∧
        ∃ S : Set Plane, IsCompact S ∧ S ⊆ O ∧
          ∀ t, EqOn (P t) id Sᶜ ∧ EqOn (P t).symm id Sᶜ := by
  have hη : 0 < η := ht₀.1.trans ht₀.2
  have hδ : 0 < δ := hη.trans hηδ
  have hinner : Icc (-η) η ⊆ Ioo (-δ) δ := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have ht₀δ : t₀ ∈ Ioo (0 : ℝ) δ := ⟨ht₀.1, ht₀.2.trans hηδ⟩
  have ht₀flow : t₀ ∈ Icc (-δ) δ := ⟨by linarith [ht₀.1], ht₀δ.2.le⟩
  have hcoord : Icc (-h) h ⊆ Ioo (-1 : ℝ) 1 := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  have hbase (u : ℝ) : 0 < t₀ + s * u ^ 2 :=
    add_pos_of_pos_of_nonneg ht₀.1 (mul_nonneg hs (sq_nonneg u))
  have houterpos (t : ℝ) (ht : t ∈ Icc (-δ) δ) (u : ℝ)
      (hu : h ^ 2 / 4 ≤ u ^ 2) : 0 < t + s * u ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hu hs
    nlinarith [ht.1]
  let D₀ : Set (ℝ × ℝ) := Ioo (0 : ℝ) η ×ˢ Ioo (-1 : ℝ) 1
  let f₀ : ℝ × ℝ → Plane := fun z => B (saddleBandLevelCurve s z.1 σ z.2)
  have hf₀ : ContinuousOn f₀ D₀ := B.continuous.comp_continuousOn
    ((contDiffOn_saddleBandLevelCurve_family s σ).continuousOn.mono (fun z hz =>
      ⟨hz.2, add_pos_of_pos_of_nonneg hz.1.1 (mul_nonneg hs (sq_nonneg z.2))⟩))
  have hD₀ : IsOpen D₀ := isOpen_Ioo.prod isOpen_Ioo
  have hseed : ({t₀} : Set ℝ) ×ˢ Icc (-h) h ⊆ D₀ ∩ f₀ ⁻¹' O := by
    rintro ⟨t, u⟩ ⟨ht, hu⟩
    have ht' : t = t₀ := ht
    subst t
    exact ⟨⟨ht₀, hcoord hu⟩, hκO ⟨_, ⟨u, hu, rfl⟩, rfl⟩⟩
  obtain ⟨T₀, U₁, hT₀, _, ht₀T₀, hIU₁, hT₀U₁⟩ := generalized_tube_lemma
    isCompact_singleton isCompact_Icc (hf₀.isOpen_inter_preimage hD₀ hO) hseed
  obtain ⟨a₀, b₀, ht₀ab, habT⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    ((hT₀.inter isOpen_Ioo).mem_nhds ⟨ht₀T₀ (mem_singleton t₀), ht₀⟩)
  let a := (a₀ + t₀) / 2
  let b := (t₀ + b₀) / 2
  have hat₀ : a < t₀ := by dsimp [a]; linarith [ht₀ab.1]
  have ht₀b : t₀ < b := by dsimp [b]; linarith [ht₀ab.2]
  have habsmall : Icc a b ⊆ Ioo a₀ b₀ := by
    intro t ht
    dsimp [a, b] at ht
    constructor <;> linarith [ht₀ab.1, ht₀ab.2, ht.1, ht.2]
  have hJa : Icc a b ⊆ Ioo (0 : ℝ) η := fun _ ht => (habT (habsmall ht)).2
  have hJδ : Icc a b ⊆ Icc (-δ) δ := by
    intro t ht
    exact ⟨by linarith [(hJa ht).1], ((hJa ht).2.trans hηδ).le⟩
  have hselectedO (t : ℝ) (ht : t ∈ Icc a b) (u : ℝ) (hu : u ∈ Icc (-h) h) :
      B (saddleBandLevelCurve s t σ u) ∈ O :=
    (hT₀U₁ (a := (t, u)) ⟨(habT (habsmall ht)).1, hIU₁ hu⟩).2
  obtain ⟨Uarc, hUarc, htracearc, hUarcreg, hUarcend⟩ :=
    exists_saddle_trace_neighborhood hγ.continuous B hs hσ hh1
      (fun t ht => ⟨(hJa ht).1, (hJa ht).2.trans hηδ⟩)
      (fun t ht => (hemb t (hJδ ht)).isEmbedding.injective) hW hW0 hW1
      (fun t ht => hends t (hJδ ht))
      (fun t ht => hcut t ⟨(hJa ht).1, ((hJa ht).2.trans hηδ).le⟩)
  obtain ⟨Uout, hUout, htraceout, hUoutreg, hUoutend⟩ :=
    exists_saddle_outer_trace_neighborhood hγ.continuous B hs hh1 hδsh
      (fun t ht => (hemb t ht).isEmbedding.injective) hW hW0 hW1 hends hcontact hbox
  let U := Uout ∪ (Uarc ∩ (Ioo a b ×ˢ univ))
  have hU : IsOpen U := hUout.union (hUarc.inter (isOpen_Ioo.prod isOpen_univ))
  have hUreg : ∀ p ∈ U, (1 - (B.symm p.2).1 ^ 2) * (B.symm p.2).2 ≠ 0 := by
    intro p hp
    rcases hp with hp | hp
    · exact hUoutreg p hp
    · exact hUarcreg p hp.1
  have hUend : ∀ t ∈ Ioo (-δ) δ, ∀ u, (t, γ (t, u)) ∈ U → u ∈ W := by
    intro t ht u hu
    rcases hu with hu | hu
    · exact hUoutend t (Ioo_subset_Icc_self ht) u hu
    · exact hUarcend t (Ioo_subset_Icc_self hu.2.1) u hu.1
  let ε := min ((t₀ - a) / 2) ((b - t₀) / 2)
  have hε : 0 < ε := lt_min (half_pos (sub_pos.mpr hat₀)) (half_pos (sub_pos.mpr ht₀b))
  have hJa' : Icc (t₀ - ε) (t₀ + ε) ⊆ Ioo a b := by
    intro t ht
    have hε₁ : ε ≤ (t₀ - a) / 2 := min_le_left _ _
    have hε₂ : ε ≤ (b - t₀) / 2 := min_le_right _ _
    constructor <;> linarith [ht.1, ht.2]
  have hJsub : Icc (t₀ - ε) (t₀ + ε) ⊆ Icc a b := hJa'.trans Ioo_subset_Icc_self
  let A : Set ℝ := Icc (-h) h ∩ {u | h ^ 2 / 4 ≤ u ^ 2}
  have hA : IsCompact A := isCompact_Icc.inter_right (isClosed_le continuous_const (by fun_prop))
  let Kout := saddleBandLevelCurve s t₀ 1 '' A ∪ saddleBandLevelCurve s t₀ (-1) '' A
  let Karc := saddleBandLevelCurve s t₀ σ '' Icc (-h) h
  have hcont (σ' : ℝ) : ContinuousOn (saddleBandLevelCurve s t₀ σ') (Icc (-h) h) :=
    (contDiffOn_saddleBandLevelCurve hs ht₀.1 σ').continuousOn.mono hcoord
  have hKout : IsCompact Kout := (hA.image_of_continuousOn ((hcont 1).mono inter_subset_left)).union
    (hA.image_of_continuousOn ((hcont (-1)).mono inter_subset_left))
  have hKarc : IsCompact Karc := isCompact_Icc.image_of_continuousOn (hcont σ)
  have hKoutmem (σ' : ℝ) (hσ' : σ' ^ 2 = 1) (u : ℝ) (hu : u ∈ Icc (-h) h)
      (hsq : h ^ 2 / 4 ≤ u ^ 2) : saddleBandLevelCurve s t₀ σ' u ∈ Kout := by
    rcases sq_eq_one_iff.mp hσ' with rfl | rfl
    · exact Or.inl ⟨u, ⟨hu, hsq⟩, rfl⟩
    · exact Or.inr ⟨u, ⟨hu, hsq⟩, rfl⟩
  have hKoutcases (z : ℝ × ℝ) (hz : z ∈ Kout) :
      ∃ σ' : ℝ, σ' ^ 2 = 1 ∧ ∃ u ∈ A, z = saddleBandLevelCurve s t₀ σ' u := by
    rcases hz with ⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩
    · exact ⟨1, by norm_num, u, hu, rfl⟩
    · exact ⟨-1, by norm_num, u, hu, rfl⟩
  let K : Bool → Set (ℝ × ℝ) := fun i => if i then Karc else Kout
  let lo : Bool → ℝ := fun i => if i then t₀ - ε else -η
  let hi : Bool → ℝ := fun i => if i then t₀ + ε else η
  have hK : ∀ i, IsCompact (K i) := by
    intro i
    cases i
    · exact hKout
    · exact hKarc
  have htime : ∀ i, t₀ ∈ Icc (lo i) (hi i) := by
    intro i
    cases i
    · exact ⟨by change -η ≤ t₀; linarith [ht₀.1], ht₀.2.le⟩
    · exact ⟨by change t₀ - ε ≤ t₀; linarith, by change t₀ ≤ t₀ + ε; linarith⟩
  have htimewindow : ∀ i, Icc (lo i) (hi i) ⊆ Ioo (-δ) δ := by
    intro i
    cases i
    · exact hinner
    · intro t ht
      exact hinner ⟨by linarith [(hJa (hJsub ht)).1], (hJa (hJsub ht)).2.le⟩
  have hreg : ∀ i, ∀ z ∈ K i, (1 - z.1 ^ 2) * z.2 ≠ 0 := by
    intro i z hz
    cases i
    · obtain ⟨σ', hσ', u, hu, rfl⟩ := hKoutcases z hz
      exact saddleBandLevelCurve_regular_of_pos (hbase u)
        (by intro heq; rw [heq] at hσ'; norm_num at hσ') (hcoord hu.1)
    · obtain ⟨u, hu, rfl⟩ := hz
      exact saddleBandLevelCurve_regular_of_pos (hbase u)
        (by intro heq; rw [heq] at hσ; norm_num at hσ) (hcoord hu)
  have hrad : ∀ i, ∀ t ∈ Icc (lo i) (hi i), ∀ z ∈ K i,
      0 < 1 + 2 * (1 - z.1 ^ 2)⁻¹ * (t - t₀) / z.2 ^ 2 := by
    intro i t ht z hz
    cases i
    · obtain ⟨σ', hσ', u, hu, rfl⟩ := hKoutcases z hz
      change 0 < 1 + 2 * (1 - u ^ 2)⁻¹ * (t - t₀) / (saddleBandLevelCurve s t₀ σ' u).2 ^ 2
      rw [saddleBandLevelCurve_flow_radicand (hbase u) hσ' (hcoord hu.1)]
      exact div_pos (houterpos t (Ioo_subset_Icc_self (hinner ht)) u hu.2) (hbase u)
    · obtain ⟨u, hu, rfl⟩ := hz
      change 0 < 1 + 2 * (1 - u ^ 2)⁻¹ * (t - t₀) / (saddleBandLevelCurve s t₀ σ u).2 ^ 2
      rw [saddleBandLevelCurve_flow_radicand (hbase u) hσ (hcoord hu)]
      exact div_pos (add_pos_of_pos_of_nonneg (hJa (hJsub ht)).1
        (mul_nonneg hs (sq_nonneg u))) (hbase u)
  have htrace : ∀ i, ∀ t ∈ Icc (lo i) (hi i), ∀ z ∈ K i,
      (t, B (saddleBandCurve z (t - t₀))) ∈ U ∩ (univ ×ˢ O) := by
    intro i t ht z hz
    cases i
    · obtain ⟨σ', hσ', u, hu, rfl⟩ := hKoutcases z hz
      have htδ := Ioo_subset_Icc_self (hinner ht)
      rw [saddleBandCurve_saddleBandLevelCurve (hbase u) (houterpos t htδ u hu.2).le hσ' (hcoord hu.1)]
      exact ⟨Or.inl (htraceout t htδ σ' hσ' u hu.1 hu.2),
        mem_univ _, houterO t ht σ' hσ' u hu.1 hu.2⟩
    · obtain ⟨u, hu, rfl⟩ := hz
      rw [saddleBandCurve_saddleBandLevelCurve (hbase u)
        (add_nonneg (hJa (hJsub ht)).1.le (mul_nonneg hs (sq_nonneg u))) hσ (hcoord hu)]
      exact ⟨Or.inr ⟨htracearc t (hJsub ht) u hu, hJa' ht, mem_univ _⟩,
        mem_univ _, hselectedO t (hJsub ht) u hu⟩
  obtain ⟨P, hP, hPi, hP₀, hPγ, ⟨V, hV⟩, S, hS, hSO, hPS⟩ :=
    exists_ambient_isotopy_closing_arc_eqOn_saddleBandCurve_of_endpoint
      hγ B hσ ht₀flow htime htimewindow hemb hK hreg hrad hU hUreg
      hUend hendpoint hO hγO htrace
  let Vout := V false ∩ {z : ℝ × ℝ | z.1 ∈ Ioo (-1 : ℝ) 1}
  let Varc := V true ∩ {z : ℝ × ℝ | z.1 ∈ Ioo (-1 : ℝ) 1 ∧ 0 < σ * z.2}
  have hVout : IsOpen Vout := (hV false).1.inter (isOpen_Ioo.preimage continuous_fst)
  have hVarc : IsOpen Varc := (hV true).1.inter
    ((isOpen_Ioo.preimage continuous_fst).inter
      (show IsOpen {z : ℝ × ℝ | 0 < σ * z.2} from
        isOpen_lt continuous_const (continuous_const.mul continuous_snd)))
  have hKarcV : Karc ⊆ Varc := by
    rintro z ⟨u, hu, rfl⟩
    refine ⟨(hV true).2.1 ⟨u, hu, rfl⟩, hcoord hu, ?_⟩
    change 0 < σ * (σ * Real.sqrt (2 * (t₀ + s * u ^ 2) / (1 - u ^ 2)))
    rw [← mul_assoc, ← sq, hσ, one_mul]
    apply Real.sqrt_pos.mpr
    have hden : 0 < 1 - u ^ 2 := by nlinarith [(hcoord hu).1, (hcoord hu).2]
    exact div_pos (mul_pos (by norm_num) (hbase u)) hden
  have hPselected (t : ℝ) (ht : t ∈ Icc (t₀ - ε) (t₀ + ε)) :
      P t '' (B '' (saddleBandLevelCurve s t₀ σ '' Icc (-h) h)) =
        B '' (saddleBandLevelCurve s t σ '' Icc (-h) h) := by
    have hp (u : ℝ) (hu : u ∈ Icc (-h) h) :
        P t (B (saddleBandLevelCurve s t₀ σ u)) = B (saddleBandLevelCurve s t σ u) := by
      rw [(hV true).2.2.2.2 t ht _ ((hKarcV ⟨u, hu, rfl⟩).1),
        saddleBandCurve_saddleBandLevelCurve (hbase u)
          (add_nonneg (hJa (hJsub ht)).1.le (mul_nonneg hs (sq_nonneg u))) hσ (hcoord hu)]
    ext y
    constructor
    · rintro ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨u, hu, rfl⟩, (hp u hu).symm⟩
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨u, hu, rfl⟩, rfl⟩, hp u hu⟩
  refine ⟨ε, hε, hJsub.trans hJa, P, hP, hPi, hP₀, hPγ,
    ⟨Vout, hVout, ?_, ?_, ?_, ?_⟩,
    ⟨Varc, hVarc, hKarcV, fun _ hz => hz.2, ?_, ?_⟩, ?_, S, hS, hSO, hPS⟩
  · intro σ' hσ' u hu hsq
    exact ⟨(hV false).2.1 (hKoutmem σ' hσ' u hu hsq), hcoord hu⟩
  · intro z hz
    exact ⟨hz.2, (mul_ne_zero_iff.mp ((hV false).2.2.1 z hz.1)).2⟩
  · intro t ht z hz
    exact (hV false).2.2.2.1 t ht z hz.1
  · intro t ht z hz
    exact (hV false).2.2.2.2 t ht z hz.1
  · intro t ht z hz
    exact (hV true).2.2.2.1 t ht z hz.1
  · intro t ht z hz
    exact (hV true).2.2.2.2 t ht z hz.1
  · intro t ht
    have hct := hcut t ⟨(hJa (hJsub ht)).1, ((hJa (hJsub ht)).2.trans hηδ).le⟩
    have hc₀ := hcut t₀ ⟨ht₀.1, ht₀δ.2.le⟩
    rw [← hc₀.union_eq, image_union, hPselected t ht]
    rw [show P t '' range (fun u => γ (t₀, u)) = range (fun u => γ (t, u)) by
      rw [← range_comp]; congr 1; funext u; exact hPγ t (hJδ (hJsub ht)) u]
    exact hct.union_eq

theorem exists_closing_arc_homotopy_field_neighborhood_of_saddle_rectangle
    {γ : ℝ × unitInterval → Plane} (hγ : Continuous γ)
    (B : (ℝ × ℝ) ≃ₘ[ℝ] Plane) {s σ h ρ δ t₀ a b : ℝ}
    (hs : 0 ≤ s) (hσ : σ ^ 2 = 1) (hh : 0 < h)
    (hδsh : 4 * δ < s * h ^ 2) (ht₀ : t₀ ∈ Ioo (-δ) δ)
    (hJ : Icc a b ⊆ Ioo (-δ) δ)
    (hemb : ∀ t ∈ Icc (-δ) δ, Function.Injective (fun u => γ (t, u)))
    {W : Set unitInterval} (hW : IsOpen W) (hW0 : (0 : unitInterval) ∈ W)
    (hW1 : (1 : unitInterval) ∈ W) {v : unitInterval → ℝ}
    (hendpoint : ∀ u ∈ W, v u ∈ Ioo (-1 : ℝ) 1 ∧
      ∀ t ∈ Icc (-δ) δ, γ (t, u) = B (saddleBandLevelCurve s t σ (v u)))
    (hends : ∀ t ∈ Icc (-δ) δ,
      γ (t, 0) = B (saddleBandLevelCurve s t σ (-h)) ∧
      γ (t, 1) = B (saddleBandLevelCurve s t σ h))
    (hcontact : ∀ t ∈ Icc (-δ) δ, ∀ u,
      B.symm (γ (t, u)) ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ →
      B.symm (γ (t, u)) = saddleBandLevelCurve s t σ (-h) ∨
        B.symm (γ (t, u)) = saddleBandLevelCurve s t σ h)
    {θ : ℝ × ℝ → ℝ} (hθ : ∀ t u, h / 2 ≤ |u| → θ (t, u) = 1)
    {Ω : Set ((ℝ × ℝ) × Plane)} (hΩ : IsOpen Ω) :
    ∃ N : Set ((ℝ × ℝ) × Plane), IsOpen N ∧
      Ω ∩ {q | B.symm q.2 ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ} ⊆ N ∧ N ⊆ Ω ∧
      ∀ r ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc a b, ∀ u,
        ((r, t), γ ((1 - r) * t + r * t₀, u)) ∈ N →
        θ (t, (B.symm (γ ((1 - r) * t + r * t₀, u))).1) •
            B.saddleFiberVectorField (γ ((1 - r) * t + r * t₀, u)) =
          deriv (fun q => γ (q, u)) ((1 - r) * t + r * t₀) := by
  let w : unitInterval → ℝ := fun u => (B.symm (γ (t₀, u))).1
  have hw : Continuous w := continuous_fst.comp (B.symm.continuous.comp
    (hγ.comp (continuous_const.prodMk continuous_id)))
  have hwv (u : unitInterval) (hu : u ∈ W) : w u = v u := by
    change (B.symm (γ (t₀, u))).1 = v u
    rw [(hendpoint u hu).2 t₀ (Ioo_subset_Icc_self ht₀), B.symm_apply_apply]
    rfl
  have hw0 : w 0 = -h := by
    change (B.symm (γ (t₀, 0))).1 = -h
    rw [(hends t₀ (Ioo_subset_Icc_self ht₀)).1, B.symm_apply_apply]
    rfl
  have hw1 : w 1 = h := by
    change (B.symm (γ (t₀, 1))).1 = h
    rw [(hends t₀ (Ioo_subset_Icc_self ht₀)).2, B.symm_apply_apply]
    rfl
  let W' := W ∩ {u | h / 2 < |w u|}
  have hW' : IsOpen W' := hW.inter (isOpen_lt continuous_const hw.abs)
  have hW'0 : (0 : unitInterval) ∈ W' := by
    refine ⟨hW0, ?_⟩
    change h / 2 < |w 0|
    rw [hw0, abs_neg, abs_of_pos hh]
    linarith
  have hW'1 : (1 : unitInterval) ∈ W' := by
    refine ⟨hW1, ?_⟩
    change h / 2 < |w 1|
    rw [hw1, abs_of_pos hh]
    linarith
  let τ : ℝ × ℝ → ℝ := fun p => (1 - p.1) * p.2 + p.1 * t₀
  have hτ (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (t : ℝ) (ht : t ∈ Icc a b) :
      τ (r, t) ∈ Ioo (-δ) δ :=
    (convex_Ioo (-δ) δ) (hJ ht) ht₀ (sub_nonneg.mpr hr.2) hr.1 (sub_add_cancel 1 r)
  let F : ((ℝ × ℝ) × unitInterval) → ((ℝ × ℝ) × Plane) :=
    fun q => (q.1, γ (τ q.1, q.2))
  have hF : Continuous F := continuous_fst.prodMk
    (hγ.comp ((show Continuous τ by fun_prop).comp continuous_fst |>.prodMk continuous_snd))
  let T := F '' ((Icc (0 : ℝ) 1 ×ˢ Icc a b) ×ˢ W'ᶜ)
  have hT : IsCompact T := ((isCompact_Icc.prod isCompact_Icc).prod
    hW'.isClosed_compl.isCompact).image hF
  let N := Ω ∩ Tᶜ
  have hN : IsOpen N := hΩ.inter hT.isClosed.isOpen_compl
  have hKN : Ω ∩ {q | B.symm q.2 ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ} ⊆ N := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    rintro ⟨⟨⟨r, t⟩, u⟩, ⟨⟨hr, ht⟩, hu⟩, heq⟩
    have hqp2 : γ (τ (r, t), u) = q.2 := congrArg Prod.snd heq
    have htδ := Ioo_subset_Icc_self (hτ r hr t ht)
    have hrect : B.symm (γ (τ (r, t), u)) ∈ Icc (-h) h ×ˢ Icc (-ρ) ρ := by
      rw [hqp2]
      exact hq.2
    rcases hcontact (τ (r, t)) htδ u hrect with he | he
    · have hueq : γ (τ (r, t), u) = γ (τ (r, t), 0) := by
        rw [(hends _ htδ).1, ← he, B.apply_symm_apply]
      have hu0 : u = 0 := hemb _ htδ hueq
      exact hu (hu0.symm ▸ hW'0)
    · have hueq : γ (τ (r, t), u) = γ (τ (r, t), 1) := by
        rw [(hends _ htδ).2, ← he, B.apply_symm_apply]
      have hu1 : u = 1 := hemb _ htδ hueq
      exact hu (hu1.symm ▸ hW'1)
  refine ⟨N, hN, hKN, inter_subset_left, ?_⟩
  intro r hr t ht u htu
  have hu : u ∈ W' := by
    by_contra hn
    exact htu.2 ⟨((r, t), u), ⟨⟨hr, ht⟩, hn⟩, rfl⟩
  have huW : u ∈ W := hu.1
  have huouter : h / 2 ≤ |v u| := by
    rw [← hwv u huW]
    exact hu.2.le
  have htime := hτ r hr t ht
  have hmodel := (hendpoint u huW).2 (τ (r, t)) (Ioo_subset_Icc_self htime)
  have huunit := (hendpoint u huW).1
  have hsq : h ^ 2 / 4 ≤ (v u) ^ 2 := by nlinarith [sq_abs (v u), abs_nonneg (v u)]
  have hrad : 0 < τ (r, t) + s * (v u) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hsq hs
    linarith [htime.1]
  have hevent : (fun q => γ (q, u)) =ᶠ[𝓝 (τ (r, t))]
      (fun q => B (saddleBandLevelCurve s q σ (v u))) := by
    filter_upwards [Ioo_mem_nhds htime.1 htime.2] with q hq
    exact (hendpoint u huW).2 q (Ioo_subset_Icc_self hq)
  have hd := (B.contMDiff.contDiff.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt
    (τ (r, t)) (hasDerivAt_saddleBandLevelCurve_time_of_pos hrad hσ huunit)
  have hd' : HasDerivAt (fun q => B (saddleBandLevelCurve s q σ (v u)))
      (B.saddleFiberVectorField (B (saddleBandLevelCurve s (τ (r, t)) σ (v u))))
      (τ (r, t)) := by
    simpa only [Diffeomorph.saddleFiberVectorField, B.symm_apply_apply, Function.comp_def] using hd
  change θ (t, (B.symm (γ (τ (r, t), u))).1) •
    B.saddleFiberVectorField (γ (τ (r, t), u)) = deriv (fun q => γ (q, u)) (τ (r, t))
  rw [hmodel, B.symm_apply_apply]
  change θ (t, v u) • B.saddleFiberVectorField
    (B (saddleBandLevelCurve s (τ (r, t)) σ (v u))) = _
  rw [hθ t (v u) huouter, one_smul, (hd'.congr_of_eventuallyEq hevent).deriv]


end DifferentialGeometry.Topology.PlanarJordan
