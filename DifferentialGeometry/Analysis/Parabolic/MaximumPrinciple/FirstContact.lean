import DifferentialGeometry.Geometry.Operator.MetricFamily
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace DifferentialGeometry.Analysis.Parabolic

noncomputable section

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private theorem derivWithin_nonpos_at_interval_right_min
    {phi : Real → Real} {s t : Real}
    (hst : s < t) (hmin : IsLocalMinOn phi (Set.Icc s t) t) :
    derivWithin phi (Set.Icc s t) t ≤ 0 := by
  have hdir : s - t ∈ posTangentConeAt (Set.Icc s t) t := by
    have hseg : segment Real t s ⊆ Set.Icc s t := by
      rw [segment_symm, segment_eq_Icc hst.le]
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonneg :
      0 ≤ (fderivWithin Real phi (Set.Icc s t) t : Real →L[Real] Real) (s - t) :=
    hmin.fderivWithin_nonneg hdir
  have hlin :
      (fderivWithin Real phi (Set.Icc s t) t : Real →L[Real] Real) (s - t) =
        (s - t) * derivWithin phi (Set.Icc s t) t := by
    rw [← fderivWithin_derivWithin (f := phi) (s := Set.Icc s t) (x := t)]
    simpa [smul_eq_mul] using
      ((fderivWithin Real phi (Set.Icc s t) t : Real →L[Real] Real).map_smul
        (s - t) (1 : Real))
  rw [hlin] at hnonneg
  exact nonpos_of_mul_nonneg_right hnonneg (sub_neg.mpr hst)

theorem derivWithin_sub_heatOperatorWithDrift_nonpos_at_time_and_space_min
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    {ψ : ℝ → M → ℝ} {s t : ℝ} (hst : s < t) {x : M}
    (htime : IsLocalMinOn (fun q => ψ q x) (Icc s t) t)
    (hspace : IsLocalMin (ψ t) x)
    (hx : I.IsInteriorPoint x)
    (hψ : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (ψ t) y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (ψ t) y) x) :
    derivWithin (fun q => ψ q x) (Icc s t) t -
      heatOperatorWithDrift (I := I) G t (X t) (ψ t) x ≤ 0 := by
  have htime_nonpos := derivWithin_nonpos_at_interval_right_min hst htime
  have hheat_nonneg := heatOperatorWithDrift_at_spatial_min_nonneg_of_isInteriorPoint
    (I := I) G t (X t) hspace hx hψ.self_of_nhds hψ hgrad
  linarith

theorem derivWithin_sub_heatOperatorWithDrift_nonpos_at_spacetime_min
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (X : Real → (x : M) → TangentSpace I x)
    {psi : Real → M → Real} {s t : Real} (hst : s < t) {x : M}
    (hmin : IsLocalMinOn (fun p : Real × M ↦ psi p.1 p.2)
      (Set.Icc s t ×ˢ (Set.univ : Set M)) (t, x))
    (hx : I.IsInteriorPoint x)
    (hpsi : MDifferentiableAt I 𝓘(Real, Real) (psi t) x)
    (hpsi_near : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) (psi t) y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (psi t) y) x) :
    derivWithin (fun q : Real ↦ psi q x) (Set.Icc s t) t -
      heatOperatorWithDrift (I := I) G t (X t) (psi t) x ≤ 0 := by
  have htime_min : IsLocalMinOn (fun q : Real ↦ psi q x) (Set.Icc s t) t := by
    have hcomp := hmin.comp_continuousOn
      (s := Set.Icc s t) (g := fun q : Real ↦ (q, x))
      (by intro q hq; exact ⟨hq, Set.mem_univ x⟩)
      (continuous_id.prodMk continuous_const).continuousOn ⟨hst.le, le_rfl⟩
    exact hcomp
  have htime_nonpos :
      derivWithin (fun q : Real ↦ psi q x) (Set.Icc s t) t ≤ 0 :=
    derivWithin_nonpos_at_interval_right_min hst htime_min
  have hspace_min : IsLocalMin (psi t) x := by
    rw [← isLocalMinOn_univ_iff]
    have hcomp := hmin.comp_continuousOn
      (s := Set.univ) (g := fun y : M ↦ (t, y))
      (by intro y hy; exact ⟨⟨hst.le, le_rfl⟩, hy⟩)
      (continuous_const.prodMk continuous_id).continuousOn (Set.mem_univ x)
    exact hcomp
  have hheat_nonneg :
      0 ≤ heatOperatorWithDrift (I := I) G t (X t) (psi t) x :=
    heatOperatorWithDrift_at_spatial_min_nonneg_of_isInteriorPoint
      (I := I) G t (X t) hspace_min hx hpsi hpsi_near hgrad
  linarith

theorem derivWithin_sub_heatOperatorWithDrift_nonpos_of_lower_support
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (X : Real → (x : M) → TangentSpace I x)
    {theta psi : Real → M → Real} {s t : Real} (hst : s < t) {x : M}
    (htheta_nonneg : ∀ᶠ p in 𝓝[Set.Icc s t ×ˢ (Set.univ : Set M)] (t, x),
      0 ≤ theta p.1 p.2)
    (hsupport : ∀ᶠ p in 𝓝[Set.Icc s t ×ˢ (Set.univ : Set M)] (t, x),
      theta p.1 p.2 ≤ psi p.1 p.2)
    (heq : psi t x = theta t x) (hzero : theta t x = 0)
    (hx : I.IsInteriorPoint x)
    (hpsi : MDifferentiableAt I 𝓘(Real, Real) (psi t) x)
    (hpsi_near : ∀ᶠ y in nhds x,
      MDifferentiableAt I 𝓘(Real, Real) (psi t) y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (psi t) y) x) :
    derivWithin (fun q : Real ↦ psi q x) (Set.Icc s t) t -
      heatOperatorWithDrift (I := I) G t (X t) (psi t) x ≤ 0 := by
  apply derivWithin_sub_heatOperatorWithDrift_nonpos_at_spacetime_min
    (I := I) G X hst
  · unfold IsLocalMinOn IsMinFilter
    change ∀ᶠ p in 𝓝[Set.Icc s t ×ˢ (Set.univ : Set M)] (t, x),
      psi t x ≤ psi p.1 p.2
    rw [heq, hzero]
    filter_upwards [htheta_nonneg, hsupport] with p hpnonneg hple
    exact hpnonneg.trans hple
  · exact hx
  · exact hpsi
  · exact hpsi_near
  · exact hgrad

private theorem derivWithin_nonneg_at_interval_right_max
    {phi : ℝ → ℝ} {s t : ℝ}
    (hst : s < t) (hmax : IsLocalMaxOn phi (Icc s t) t) :
    0 ≤ derivWithin phi (Icc s t) t := by
  have hdir : s - t ∈ posTangentConeAt (Icc s t) t := by
    have hseg : segment ℝ t s ⊆ Icc s t := by
      rw [segment_symm, segment_eq_Icc hst.le]
    exact sub_mem_posTangentConeAt_of_segment_subset hseg
  have hnonpos := hmax.fderivWithin_nonpos hdir
  have hlin :
      (fderivWithin ℝ phi (Icc s t) t : ℝ →L[ℝ] ℝ) (s - t) =
        (s - t) * derivWithin phi (Icc s t) t := by
    rw [← fderivWithin_derivWithin (f := phi) (s := Icc s t) (x := t)]
    simpa [smul_eq_mul] using
      ((fderivWithin ℝ phi (Icc s t) t : ℝ →L[ℝ] ℝ).map_smul
        (s - t) (1 : ℝ))
  rw [hlin] at hnonpos
  exact nonneg_of_mul_nonpos_right hnonpos (sub_neg.mpr hst)

theorem derivWithin_sub_heatOperatorWithDrift_nonneg_at_spacetime_max
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    {psi : ℝ → M → ℝ} {s t : ℝ} (hst : s < t) {x : M}
    (hmax : IsLocalMaxOn (fun p : ℝ × M ↦ psi p.1 p.2)
      (Icc s t ×ˢ (Set.univ : Set M)) (t, x))
    (hx : I.IsInteriorPoint x)
    (hpsi : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (psi t) y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (psi t) y) x) :
    0 ≤ derivWithin (fun q : ℝ ↦ psi q x) (Icc s t) t -
      heatOperatorWithDrift (I := I) G t (X t) (psi t) x := by
  have htime_max : IsLocalMaxOn (fun q : ℝ ↦ psi q x) (Icc s t) t := by
    exact hmax.comp_continuousOn
      (s := Icc s t) (g := fun q : ℝ ↦ (q, x))
      (by intro q hq; exact ⟨hq, Set.mem_univ x⟩)
      (continuous_id.prodMk continuous_const).continuousOn ⟨hst.le, le_rfl⟩
  have htime_nonneg := derivWithin_nonneg_at_interval_right_max hst htime_max
  have hspace_max : IsLocalMax (psi t) x := by
    rw [← isLocalMaxOn_univ_iff]
    exact hmax.comp_continuousOn
      (s := Set.univ) (g := fun y : M ↦ (t, y))
      (by intro y hy; exact ⟨⟨hst.le, le_rfl⟩, hy⟩)
      (continuous_const.prodMk continuous_id).continuousOn (Set.mem_univ x)
  have hlap_nonpos := laplacianAt_nonpos_at_spatial_max_of_isInteriorPoint
    (I := I) G t hspace_max hx hpsi.self_of_nhds hpsi hgrad
  have hdrift : driftTerm (I := I) G t (X t) (psi t) x = 0 := by
    have hneg := driftTerm_eq_zero_at_spatial_min_of_isInteriorPoint
      (I := I) G t (X t) hspace_max.neg hx hpsi.self_of_nhds.neg
    have heq : (fun y => -psi t y) = (-1 : ℝ) • psi t := by funext y; simp
    rw [heq, driftTerm_const_smul (I := I) G t (X t) (-1) hpsi.self_of_nhds] at hneg
    linarith
  unfold heatOperatorWithDrift
  rw [hdrift, add_zero]
  exact sub_nonneg.mpr (hlap_nonpos.trans htime_nonneg)

theorem derivWithin_sub_heatOperatorWithDrift_nonneg_of_lower_support
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (X : ℝ → (x : M) → TangentSpace I x)
    {theta psi : ℝ → M → ℝ} {s t : ℝ} (hst : s < t) {x : M}
    (hmax : IsLocalMaxOn (fun p : ℝ × M ↦ theta p.1 p.2)
      (Icc s t ×ˢ (Set.univ : Set M)) (t, x))
    (hsupport : ∀ᶠ p in 𝓝[Icc s t ×ˢ (Set.univ : Set M)] (t, x),
      psi p.1 p.2 ≤ theta p.1 p.2)
    (heq : psi t x = theta t x)
    (hx : I.IsInteriorPoint x)
    (hpsi : ∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(ℝ, ℝ) (psi t) y)
    (hgrad : MDiffAt (T% fun y : M =>
      gradientFun (I := I) (G.metric t) (psi t) y) x) :
    0 ≤ derivWithin (fun q : ℝ ↦ psi q x) (Icc s t) t -
      heatOperatorWithDrift (I := I) G t (X t) (psi t) x := by
  apply derivWithin_sub_heatOperatorWithDrift_nonneg_at_spacetime_max
    (I := I) G X hst _ hx hpsi hgrad
  change ∀ᶠ p in 𝓝[Icc s t ×ˢ (Set.univ : Set M)] (t, x), psi p.1 p.2 ≤ psi t x
  filter_upwards [hmax, hsupport] with p hmaxp hsupp
  exact hsupp.trans (hmaxp.trans_eq heq.symm)

end


open Set Filter Topology in
theorem exists_first_zero_on_compact_superlevel
    {M : Type*} [TopologicalSpace M]
    {f z : ℝ → M → ℝ} {a b : ℝ} {K : Set M}
    (r : ℝ) (hK : IsCompact K)
    (hf : ContinuousOn (fun p : ℝ × M => f p.1 p.2) (Icc a b ×ˢ K))
    (hz : ContinuousOn (fun p : ℝ × M => z p.1 p.2) (Icc a b ×ˢ K))
    (hinit : ∀ x ∈ K, z a x < r)
    (hout : ∀ t ∈ Icc a b, ∀ x, x ∉ K → 0 ≤ f t x)
    (hbelow : ∀ t ∈ Icc a b, ∀ x ∈ K, z t x ≤ r → 0 ≤ f t x)
    (hboundary : ∀ t ∈ Icc a b, ∀ x ∈ K, z t x = r → 0 < f t x)
    (hfail : ∃ t ∈ Icc a b, ∃ x ∈ K, f t x < 0) :
    ∃ t ∈ Ioc a b, ∃ x ∈ K, r < z t x ∧ f t x = 0 ∧
      ∀ s ∈ Icc a t, ∀ y, 0 ≤ f s y := by
  let slab : Set (ℝ × M) := Icc a b ×ˢ K
  let nonpos : Set (ℝ × M) := slab ∩ (fun p : ℝ × M => f p.1 p.2) ⁻¹' Iic 0
  let bad : Set (ℝ × M) := nonpos ∩ (fun p : ℝ × M => z p.1 p.2) ⁻¹' Ici r
  have hslab : IsCompact slab := isCompact_Icc.prod hK
  have hnonpos : IsCompact nonpos :=
    hf.lowerSemicontinuousOn.isCompact_inter_preimage_Iic hslab 0
  have hbad : IsCompact bad :=
    ((hz.mono (show nonpos ⊆ slab from inter_subset_left)).upperSemicontinuousOn).isCompact_inter_preimage_Ici hnonpos r
  have z_gt_of_neg {t : ℝ} (ht : t ∈ Icc a b) {x : M} (hx : x ∈ K)
      (hneg : f t x < 0) : r < z t x := by
    by_contra hn
    exact (not_lt_of_ge (hbelow t ht x hx (not_lt.mp hn))) hneg
  obtain ⟨t₀, ht₀, x₀, hx₀, hfail₀⟩ := hfail
  have hbadne : bad.Nonempty :=
    ⟨(t₀, x₀), ⟨⟨⟨ht₀, hx₀⟩, hfail₀.le⟩, (z_gt_of_neg ht₀ hx₀ hfail₀).le⟩⟩
  obtain ⟨p, hp, hpmin⟩ := hbad.exists_isMinOn hbadne continuous_fst.continuousOn
  have ht : p.1 ∈ Icc a b := hp.1.1.1
  have hx : p.2 ∈ K := hp.1.1.2
  have hfnonpos : f p.1 p.2 ≤ 0 := hp.1.2
  have hzge : r ≤ z p.1 p.2 := hp.2
  have hat : a < p.1 := by
    by_contra hn
    have heq : p.1 = a := le_antisymm (not_lt.mp hn) ht.1
    exact (not_lt_of_ge (by simpa only [heq] using hzge)) (hinit p.2 hx)
  have hzgt : r < z p.1 p.2 := by
    apply lt_of_le_of_ne hzge
    intro heq
    exact (not_lt_of_ge hfnonpos) (hboundary p.1 ht p.2 hx heq.symm)
  have hleft {t : ℝ} (ht' : t ∈ Ioc a b) {x : M} (hx' : x ∈ K)
      (hneg : f t x < 0) : ∃ s ∈ Ioo a t, f s x < 0 := by
    have hfc : ContinuousOn (fun s : ℝ => f s x) (Icc a b) :=
      hf.comp (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs, hx'⟩)
    have hsub : Ioo a t ⊆ Icc a b := fun s hs =>
      ⟨hs.1.le, hs.2.le.trans ht'.2⟩
    have hnear : ∀ᶠ s in 𝓝[Ioo a t] t, f s x < 0 :=
      ((hfc t ⟨ht'.1.le, ht'.2⟩).eventually (Iio_mem_nhds hneg)).filter_mono
        (nhdsWithin_mono t hsub)
    let : NeBot (𝓝[Ioo a t] t) := right_nhdsWithin_Ioo_neBot ht'.1
    obtain ⟨s, hsneg, hs⟩ := (hnear.and self_mem_nhdsWithin).exists
    exact ⟨s, hs, hsneg⟩
  have hnonnegative : ∀ s ∈ Icc a p.1, ∀ y, 0 ≤ f s y := by
    intro s hs y
    have hsab : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
    by_cases hy : y ∈ K
    · by_contra hn
      have hneg : f s y < 0 := not_le.mp hn
      rcases hs.2.lt_or_eq with hst | hst
      · have hsy : (s, y) ∈ bad :=
          ⟨⟨⟨hsab, hy⟩, hneg.le⟩, (z_gt_of_neg hsab hy hneg).le⟩
        exact (not_lt_of_ge (hpmin hsy)) hst
      · subst s
        obtain ⟨r, hr, hrneg⟩ := hleft ⟨hat, ht.2⟩ hy hneg
        have hrab : r ∈ Icc a b := ⟨hr.1.le, hr.2.le.trans ht.2⟩
        have hry : (r, y) ∈ bad :=
          ⟨⟨⟨hrab, hy⟩, hrneg.le⟩, (z_gt_of_neg hrab hy hrneg).le⟩
        exact (not_lt_of_ge (hpmin hry)) hr.2
    · exact hout s hsab y hy
  exact ⟨p.1, ⟨hat, ht.2⟩, p.2, hx, hzgt,
    le_antisymm hfnonpos (hnonnegative p.1 ⟨hat.le, le_rfl⟩ p.2), hnonnegative⟩


end DifferentialGeometry.Analysis.Parabolic
