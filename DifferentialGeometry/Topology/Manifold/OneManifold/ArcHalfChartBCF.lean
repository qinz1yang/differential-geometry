import DifferentialGeometry.Topology.Manifold.OneManifold.GraphAtlasOfImmersionBCF
import DifferentialGeometry.Topology.Manifold.OneManifold.HalfChartComponentsBCF
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Half charts of an embedded smooth arc (lane S-BCF03; transfer step of the circle-base curve)

For a smooth injective immersion `τ : J → H` of an open interval `J ∋ 0` into a normed space which
is a topological embedding of `J` (the curve `σ ∘ c` of `PlaneCurveBCF`) and a set `T ⊆ H` which
near `τ 0` is `τ (J ∩ Iic 0)` (a corner) or `τ J` (an interior point) there is a half chart of `T`
at `τ 0` in the sense of `HalfChart_BCF.ofData_BCF` (affine coordinate `L z + κ` with a continuous
linear `L`); the embedding hypothesis is `hloc`: every open `U ⊆ J` is `τ⁻¹ G ∩ J` for an open `G`:

* `exists_graph_data_of_arc_BCF`: the graph chart of the arc (a continuous linear `ℓ` with
  `ℓ (τ' 0) = 1`, the local inverse of `ℓ ∘ τ`) with the monotonicity window used below;
* `exists_halfChart_data_corner_BCF`: `T ∩ O₀ = τ (J ∩ Iic 0) ∩ O₀` gives raw half chart data with
  coordinate `0` at `τ 0`;
* `exists_halfChart_data_interior_BCF`: `T ∩ O₀ = τ J ∩ O₀` gives raw data with positive
  coordinate at `τ 0`.
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **The graph data of an embedded arc**: see the module docstring. -/
theorem exists_graph_data_of_arc_BCF {τ : ℝ → H} {J : Set ℝ} (hJ : IsOpen J) (h0J : (0 : ℝ) ∈ J)
    (hτ : ContDiffOn ℝ ∞ τ J) (hd : deriv τ 0 ≠ 0)
    {O₀ : Set H} (hO₀ : IsOpen O₀) (h0 : τ 0 ∈ O₀) :
    ∃ (ℓ : H →L[ℝ] ℝ) (π : ℝ → H) (ρ r : ℝ) (D : Set ℝ), 0 < ρ ∧ 0 < r ∧ IsOpen D ∧
      Ioo (-ρ) ρ ⊆ J ∧ Ioo (ℓ (τ 0) - r) (ℓ (τ 0) + r) ⊆ D ∧ ContDiffOn ℝ ∞ π D ∧
      (∀ b ∈ D, ℓ (π b) = b) ∧
      (∀ t ∈ Ioo (-ρ) ρ, τ t ∈ O₀) ∧ StrictMonoOn (fun t => ℓ (τ t)) (Ioo (-ρ) ρ) ∧
      (∀ t ∈ Ioo (-ρ) ρ, ℓ (τ t) ∈ D ∧ π (ℓ (τ t)) = τ t) ∧
      (∀ b ∈ Ioo (ℓ (τ 0) - r) (ℓ (τ 0) + r), ∃ t ∈ Ioo (-ρ) ρ, ℓ (τ t) = b) := by
  obtain ⟨g, -, hg⟩ := exists_dual_vector ℝ (deriv τ 0) (norm_ne_zero_iff.mpr hd)
  set ℓ : H →L[ℝ] ℝ := ‖deriv τ 0‖⁻¹ • g with hℓ
  have hℓv : ℓ (deriv τ 0) = 1 := by
    rw [hℓ, smul_apply, hg]
    simp [norm_ne_zero_iff.mpr hd]
  have hτat : ∀ t ∈ J, ContDiffAt ℝ ∞ τ t := fun t ht => hτ.contDiffAt (hJ.mem_nhds ht)
  have hτd : ∀ t ∈ J, HasDerivAt τ (deriv τ t) t := fun t ht =>
    (((hτat t ht).differentiableAt (by simp))).hasDerivAt
  have hhd : ∀ t ∈ J, HasDerivAt (fun t => ℓ (τ t)) (ℓ (deriv τ t)) t := fun t ht =>
    ℓ.hasFDerivAt.comp_hasDerivAt t (hτd t ht)
  have hh : ContDiffOn ℝ ∞ (fun t => ℓ (τ t)) J := ℓ.contDiff.comp_contDiffOn hτ
  have hhat : ∀ t ∈ J, ContDiffAt ℝ ∞ (fun t => ℓ (τ t)) t := fun t ht =>
    hh.contDiffAt (hJ.mem_nhds ht)
  have hh0 : HasDerivAt (fun t => ℓ (τ t)) 1 0 := hℓv ▸ hhd 0 h0J
  set e := (hhat 0 h0J).toOpenPartialHomeomorph (fun t => ℓ (τ t))
    (hh0.hasFDerivAt_equiv one_ne_zero) (by simp) with he
  have he0 : (0 : ℝ) ∈ e.source := ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _
  have hecoe : ∀ t, e t = ℓ (τ t) := fun t => rfl
  have hderc : ContinuousOn (deriv τ) J := hτ.continuousOn_deriv_of_isOpen hJ (by simp)
  set V : Set ℝ := J ∩ {t | 0 < ℓ (deriv τ t)} with hV
  have hVo : IsOpen V := by
    have : V = J ∩ (fun t => ℓ (deriv τ t)) ⁻¹' Ioi 0 := rfl
    rw [this]
    exact (ℓ.continuous.comp_continuousOn hderc).isOpen_inter_preimage hJ isOpen_Ioi
  have hV0 : (0 : ℝ) ∈ V := by
    refine ⟨h0J, ?_⟩
    change 0 < ℓ (deriv τ 0)
    rw [hℓv]
    exact one_pos
  set e' := e.restrOpen V hVo with he'
  have he'0 : (0 : ℝ) ∈ e'.source := ⟨he0, hV0⟩
  have he'coe : ∀ t, e' t = ℓ (τ t) := fun t => rfl
  -- a window `(−ρ, ρ)` inside the source, where `ℓ ∘ τ` increases and `τ` stays in `O₀`
  have hWo : IsOpen (e'.source ∩ τ ⁻¹' O₀) := by
    have h1 : IsOpen (J ∩ τ ⁻¹' O₀) := hτ.continuousOn.isOpen_inter_preimage hJ hO₀
    have h2 : e'.source ∩ τ ⁻¹' O₀ = e'.source ∩ (J ∩ τ ⁻¹' O₀) := by
      ext t
      simp only [mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨ht, hO⟩
        exact ⟨ht, ht.2.1, hO⟩
      · rintro ⟨ht, -, hO⟩
        exact ⟨ht, hO⟩
    rw [h2]
    exact e'.open_source.inter h1
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hWo 0 ⟨he'0, h0⟩
  have hwin : Ioo (-ρ) ρ ⊆ e'.source ∩ τ ⁻¹' O₀ := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ht
  have hwinV : ∀ t ∈ Ioo (-ρ) ρ, 0 < ℓ (deriv τ t) := fun t ht => (hwin ht).1.2.2
  have hwinJ : Ioo (-ρ) ρ ⊆ J := fun t ht => (hwin ht).1.2.1
  have hmono : StrictMonoOn (fun t => ℓ (τ t)) (Ioo (-ρ) ρ) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) (hh.continuousOn.mono hwinJ) ?_
    intro t ht
    rw [interior_Ioo] at ht
    rw [(hhd t (hwinJ ht)).deriv]
    exact hwinV t ht
  have himg : IsOpen (e' '' Ioo (-ρ) ρ) :=
    e'.isOpen_image_of_subset_source isOpen_Ioo (fun t ht => (hwin ht).1)
  have hb0 : ℓ (τ 0) ∈ e' '' Ioo (-ρ) ρ := ⟨0, ⟨by linarith, hρ⟩, rfl⟩
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp himg _ hb0
  refine ⟨ℓ, τ ∘ e'.symm, ρ, r, e'.target, hρ, hr, e'.open_target, hwinJ, ?_, ?_, ?_, ?_, hmono, ?_,
    ?_⟩
  · intro b hb
    have : b ∈ e' '' Ioo (-ρ) ρ := hrball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hb.1, hb.2])
    obtain ⟨t, ht, rfl⟩ := this
    exact e'.map_source (hwin ht).1
  · intro b hb
    have hsb : e'.symm b ∈ e'.source := e'.map_target hb
    have hsymJ : e'.symm b ∈ J := hsb.2.1
    have hsym : ContDiffAt ℝ ∞ e'.symm b :=
      e'.contDiffAt_symm_deriv (ne_of_gt hsb.2.2) hb (hhd _ hsymJ) (hhat _ hsymJ)
    exact ((hτat _ hsymJ).comp b hsym).contDiffWithinAt
  · intro b hb
    change ℓ (τ (e'.symm b)) = b
    rw [← hecoe]
    exact e'.right_inv hb
  · exact fun t ht => (hwin ht).2
  · intro t ht
    refine ⟨?_, ?_⟩
    · rw [← he'coe]
      exact e'.map_source (hwin ht).1
    · change τ (e'.symm (ℓ (τ t))) = τ t
      rw [← he'coe, e'.left_inv (hwin ht).1]
  · intro b hb
    have : b ∈ e' '' Ioo (-ρ) ρ := hrball (by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hb.1, hb.2])
    obtain ⟨t, ht, rfl⟩ := this
    exact ⟨t, ht, rfl⟩

/-- **A corner of `T` at an embedded arc: raw half chart data** (coordinate `0` at `τ 0`). -/
theorem exists_halfChart_data_corner_BCF {τ : ℝ → H} {J : Set ℝ} (hJ : IsOpen J)
    (h0J : (0 : ℝ) ∈ J) (hτ : ContDiffOn ℝ ∞ τ J)
    (hloc : ∀ U : Set ℝ, IsOpen U → U ⊆ J → ∃ G : Set H, IsOpen G ∧ τ ⁻¹' G ∩ J = U)
    (hd : deriv τ 0 ≠ 0) {T O₀ : Set H} (hO₀ : IsOpen O₀) (h0 : τ 0 ∈ O₀)
    (hT : T ∩ O₀ = τ '' (J ∩ Iic 0) ∩ O₀) :
    ∃ (L : H →L[ℝ] ℝ) (κ : ℝ) (π : ℝ → H) (W V : Set ℝ) (O : Set H),
      IsOpen W ∧ IsOpen V ∧ V ⊆ W ∧ ContDiffOn ℝ ∞ π W ∧ (∀ t ∈ W, L (π t) + κ = t) ∧
      π '' W ⊆ O ∧ IsOpen O ∧ τ 0 ∈ O ∧ T ∩ O = π '' (V ∩ Ici 0) ∧ L (τ 0) + κ = 0 := by
  obtain ⟨ℓ, π, ρ, r, D, hρ, hr, hD, hρJ, hDsub, hπ, hℓπ, hτO, hmono, hπτ, hsurj⟩ :=
    exists_graph_data_of_arc_BCF hJ h0J hτ hd hO₀ h0
  set b₀ : ℝ := ℓ (τ 0) with hb₀
  set Q' : Set ℝ := {t | t ∈ Ioo (-ρ) ρ ∧ ℓ (τ t) ∈ Ioo (b₀ - r) (b₀ + r)} with hQ'
  have hgc : ContinuousOn (fun t => ℓ (τ t)) (Ioo (-ρ) ρ) :=
    (ℓ.continuous.comp_continuousOn hτ.continuousOn).mono hρJ
  have hQ'o : IsOpen Q' := by
    have : Q' = Ioo (-ρ) ρ ∩ (fun t => ℓ (τ t)) ⁻¹' Ioo (b₀ - r) (b₀ + r) := rfl
    rw [this]
    exact hgc.isOpen_inter_preimage isOpen_Ioo isOpen_Ioo
  have hQ'J : Q' ⊆ J := fun t ht => hρJ ht.1
  obtain ⟨G, hG, hGQ⟩ := hloc Q' hQ'o hQ'J
  have hmem0 : (0 : ℝ) ∈ Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
  have h0Q : (0 : ℝ) ∈ Q' := ⟨hmem0, by constructor <;> linarith⟩
  have hGt : ∀ t ∈ J, τ t ∈ G ↔ t ∈ Q' := fun t ht => by
    rw [← hGQ]
    simp [ht]
  have hge : ∀ t ∈ Q', ℓ (τ t) ∈ Ioo (b₀ - r) (b₀ + r) := fun t ht => ht.2
  have hrange : ∀ b ∈ Ioo (b₀ - r) (b₀ + r), ∃ t ∈ Q', ℓ (τ t) = b := fun b hb => by
    obtain ⟨t, ht, hgt⟩ := hsurj b hb
    exact ⟨t, ⟨ht, hgt ▸ hb⟩, hgt⟩
  have hIcc : ∀ t' ∈ Ioo (-r) r, b₀ - t' ∈ Ioo (b₀ - r) (b₀ + r) := fun t' ht =>
    ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine ⟨-ℓ, b₀, fun t' => π (b₀ - t'), Ioo (-r) r, Ioo (-r) r, O₀ ∩ G, isOpen_Ioo, isOpen_Ioo,
    subset_rfl, ?_, ?_, ?_, hO₀.inter hG, ⟨h0, (hGt 0 h0J).mpr h0Q⟩, ?_, ?_⟩
  · refine hπ.comp (contDiff_const.sub contDiff_id).contDiffOn fun t' ht => ?_
    exact hDsub (hIcc t' ht)
  · intro t' ht
    have := hℓπ (b₀ - t') (hDsub (hIcc t' ht))
    simp only [neg_apply, this]
    ring
  · rintro _ ⟨t', ht', rfl⟩
    obtain ⟨t, htQ, hgt⟩ := hrange (b₀ - t') (hIcc t' ht')
    have hπt := (hπτ t htQ.1).2
    have : π (b₀ - t') = τ t := by rw [← hgt]; exact hπt
    change π (b₀ - t') ∈ O₀ ∩ G
    rw [this]
    exact ⟨hτO t htQ.1, (hGt t (hρJ htQ.1)).mpr htQ⟩
  · ext z
    constructor
    · rintro ⟨hzT, hzO₀, hzG⟩
      have hz : z ∈ τ '' (J ∩ Iic 0) ∩ O₀ := hT ▸ ⟨hzT, hzO₀⟩
      obtain ⟨⟨t, ⟨htJ, ht0⟩, rfl⟩, -⟩ := hz
      have htQ := (hGt t htJ).mp hzG
      have hle : ℓ (τ t) ≤ b₀ := hmono.monotoneOn htQ.1 hmem0 ht0
      refine ⟨b₀ - ℓ (τ t), ⟨⟨by linarith [(hge t htQ).2, (hge t htQ).1],
        by linarith [(hge t htQ).1]⟩,
        mem_Ici.mpr (by linarith)⟩, ?_⟩
      change π (b₀ - (b₀ - ℓ (τ t))) = τ t
      rw [sub_sub_cancel]
      exact (hπτ t htQ.1).2
    · rintro ⟨t', ⟨ht', ht'0⟩, rfl⟩
      obtain ⟨t, htQ, hgt⟩ := hrange (b₀ - t') (hIcc t' ht')
      have hπt := (hπτ t htQ.1).2
      have hpt : π (b₀ - t') = τ t := by rw [← hgt]; exact hπt
      have ht0 : t ≤ 0 := by
        by_contra hcon
        have hlt : b₀ < ℓ (τ t) := hmono hmem0 htQ.1 (not_le.mp hcon)
        have ht'0' : 0 ≤ t' := ht'0
        linarith [hgt, hlt]
      have hmemT : τ t ∈ T ∩ O₀ := by
        rw [hT]
        exact ⟨⟨t, ⟨hρJ htQ.1, ht0⟩, rfl⟩, hτO t htQ.1⟩
      change π (b₀ - t') ∈ T ∩ (O₀ ∩ G)
      rw [hpt]
      exact ⟨hmemT.1, hmemT.2, (hGt t (hρJ htQ.1)).mpr htQ⟩
  · simp [hb₀]

/-- **An interior point of `T` on an embedded arc: raw half chart data** (positive coordinate at
`τ 0`). -/
theorem exists_halfChart_data_interior_BCF {τ : ℝ → H} {J : Set ℝ} (hJ : IsOpen J)
    (h0J : (0 : ℝ) ∈ J) (hτ : ContDiffOn ℝ ∞ τ J)
    (hloc : ∀ U : Set ℝ, IsOpen U → U ⊆ J → ∃ G : Set H, IsOpen G ∧ τ ⁻¹' G ∩ J = U)
    (hd : deriv τ 0 ≠ 0) {T O₀ : Set H} (hO₀ : IsOpen O₀) (h0 : τ 0 ∈ O₀)
    (hT : T ∩ O₀ = τ '' J ∩ O₀) :
    ∃ (L : H →L[ℝ] ℝ) (κ : ℝ) (π : ℝ → H) (W V : Set ℝ) (O : Set H),
      IsOpen W ∧ IsOpen V ∧ V ⊆ W ∧ ContDiffOn ℝ ∞ π W ∧ (∀ t ∈ W, L (π t) + κ = t) ∧
      π '' W ⊆ O ∧ IsOpen O ∧ τ 0 ∈ O ∧ T ∩ O = π '' (V ∩ Ici 0) ∧ 0 < L (τ 0) + κ := by
  obtain ⟨ℓ, π, ρ, r, D, hρ, hr, hD, hρJ, hDsub, hπ, hℓπ, hτO, hmono, hπτ, hsurj⟩ :=
    exists_graph_data_of_arc_BCF hJ h0J hτ hd hO₀ h0
  set b₀ : ℝ := ℓ (τ 0) with hb₀
  set Q' : Set ℝ := {t | t ∈ Ioo (-ρ) ρ ∧ ℓ (τ t) ∈ Ioo (b₀ - r) (b₀ + r)} with hQ'
  have hgc : ContinuousOn (fun t => ℓ (τ t)) (Ioo (-ρ) ρ) :=
    (ℓ.continuous.comp_continuousOn hτ.continuousOn).mono hρJ
  have hQ'o : IsOpen Q' := by
    have : Q' = Ioo (-ρ) ρ ∩ (fun t => ℓ (τ t)) ⁻¹' Ioo (b₀ - r) (b₀ + r) := rfl
    rw [this]
    exact hgc.isOpen_inter_preimage isOpen_Ioo isOpen_Ioo
  have hQ'J : Q' ⊆ J := fun t ht => hρJ ht.1
  obtain ⟨G, hG, hGQ⟩ := hloc Q' hQ'o hQ'J
  have hmem0 : (0 : ℝ) ∈ Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
  have h0Q : (0 : ℝ) ∈ Q' := ⟨hmem0, by constructor <;> linarith⟩
  have hGt : ∀ t ∈ J, τ t ∈ G ↔ t ∈ Q' := fun t ht => by
    rw [← hGQ]
    simp [ht]
  have hge : ∀ t ∈ Q', ℓ (τ t) ∈ Ioo (b₀ - r) (b₀ + r) := fun t ht => ht.2
  have hrange : ∀ b ∈ Ioo (b₀ - r) (b₀ + r), ∃ t ∈ Q', ℓ (τ t) = b := fun b hb => by
    obtain ⟨t, ht, hgt⟩ := hsurj b hb
    exact ⟨t, ⟨ht, hgt ▸ hb⟩, hgt⟩
  have hIcc : ∀ t' ∈ Ioo (0 : ℝ) (2 * r), t' + b₀ - r ∈ Ioo (b₀ - r) (b₀ + r) := fun t' ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨ℓ, r - b₀, fun t' => π (t' + b₀ - r), Ioo 0 (2 * r), Ioo 0 (2 * r), O₀ ∩ G,
    isOpen_Ioo, isOpen_Ioo, subset_rfl, ?_, ?_, ?_, hO₀.inter hG, ⟨h0, (hGt 0 h0J).mpr h0Q⟩, ?_, ?_⟩
  · refine hπ.comp ((contDiff_id.add contDiff_const).sub contDiff_const).contDiffOn fun t' ht => ?_
    exact hDsub (hIcc t' ht)
  · intro t' ht
    have := hℓπ (t' + b₀ - r) (hDsub (hIcc t' ht))
    simp only [this]
    ring
  · rintro _ ⟨t', ht', rfl⟩
    obtain ⟨t, htQ, hgt⟩ := hrange (t' + b₀ - r) (hIcc t' ht')
    have hπt := (hπτ t htQ.1).2
    have : π (t' + b₀ - r) = τ t := by rw [← hgt]; exact hπt
    change π (t' + b₀ - r) ∈ O₀ ∩ G
    rw [this]
    exact ⟨hτO t htQ.1, (hGt t (hρJ htQ.1)).mpr htQ⟩
  · ext z
    constructor
    · rintro ⟨hzT, hzO₀, hzG⟩
      have hz : z ∈ τ '' J ∩ O₀ := hT ▸ ⟨hzT, hzO₀⟩
      obtain ⟨⟨t, htJ, rfl⟩, -⟩ := hz
      have htQ := (hGt t htJ).mp hzG
      refine ⟨ℓ (τ t) - b₀ + r, ⟨⟨by linarith [(hge t htQ).1], by linarith [(hge t htQ).2]⟩,
        mem_Ici.mpr (by linarith [(hge t htQ).1])⟩, ?_⟩
      change π (ℓ (τ t) - b₀ + r + b₀ - r) = τ t
      rw [show ℓ (τ t) - b₀ + r + b₀ - r = ℓ (τ t) by ring]
      exact (hπτ t htQ.1).2
    · rintro ⟨t', ⟨ht', -⟩, rfl⟩
      obtain ⟨t, htQ, hgt⟩ := hrange (t' + b₀ - r) (hIcc t' ht')
      have hπt := (hπτ t htQ.1).2
      have hpt : π (t' + b₀ - r) = τ t := by rw [← hgt]; exact hπt
      have hmemT : τ t ∈ T ∩ O₀ := by
        rw [hT]
        exact ⟨⟨t, hρJ htQ.1, rfl⟩, hτO t htQ.1⟩
      change π (t' + b₀ - r) ∈ T ∩ (O₀ ∩ G)
      rw [hpt]
      exact ⟨hmemT.1, hmemT.2, (hGt t (hρJ htQ.1)).mpr htQ⟩
  · simp only [hb₀]
    linarith

end DifferentialGeometry.Topology
