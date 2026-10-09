/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.KinkedBlockCoordinates

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem isCompact_blockBox (r tlo : ℝ) : IsCompact (blockBox r tlo) := by
  have h : blockBox r tlo = Icc (-r) r ×ˢ (Icc (-r) r ×ˢ Icc tlo r) := by
    ext p
    simp only [blockBox, mem_ofPred_eq, mem_prod, mem_Icc, abs_le]
  rw [h]
  exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

theorem blockHalfPlane_eq_univ {tlo : ℝ} (h : tlo ≠ 0) : blockHalfPlane tlo = univ :=
  eq_univ_of_forall fun _ h0 => absurd h0 h

theorem exists_pos_forall_mem_nhdsWithin_of_isPLHomeomorphOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {p : E → ℝ × ℝ} {S T : Set E}
    {H : Set (ℝ × ℝ)} (hpl : IsPLHomeomorphOn p T (p '' T)) {x₀ : E} (hx₀ : x₀ ∈ T)
    (hS : T ∈ 𝓝[S] x₀) (hH : p '' T ∈ 𝓝[H] (p x₀)) :
    ∃ ε > 0, ∀ x ∈ T, dist (p x) (p x₀) < ε → T ∈ 𝓝[S] x ∧ p '' T ∈ 𝓝[H] (p x) := by
  obtain ⟨O, hO, hx₀O, hOS⟩ := mem_nhdsWithin.mp hS
  obtain ⟨V, hV, hpV, hVH⟩ := mem_nhdsWithin.mp hH
  have hpx₀ : p x₀ ∈ p '' T := mem_image_of_mem p hx₀
  have hψ₀ : Function.invFunOn p T (p x₀) = x₀ := hpl.bijOn.invOn_invFunOn.1 hx₀
  have hψc : ContinuousWithinAt (Function.invFunOn p T) (p '' T) (p x₀) :=
    hpl.isPiecewiseAffineOn_invFunOn.continuousOn _ hpx₀
  have hpre : Function.invFunOn p T ⁻¹' O ∈ 𝓝[p '' T] (p x₀) :=
    hψc.preimage_mem_nhdsWithin (by rw [hψ₀]; exact hO.mem_nhds hx₀O)
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.isOpen_iff.mp hV (p x₀) hpV
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun x hx hdist => ⟨?_, ?_⟩⟩
  · have hxO : x ∈ O := by
      have h1 : Function.invFunOn p T (p x) ∈ O :=
        hball₁ ⟨mem_ball.mpr (hdist.trans_le (min_le_left _ _)), mem_image_of_mem p hx⟩
      rwa [hpl.bijOn.invOn_invFunOn.1 hx] at h1
    exact mem_nhdsWithin.mpr ⟨O, hO, hxO, hOS⟩
  · have hxV : p x ∈ V := hball₂ (mem_ball.mpr (hdist.trans_le (min_le_right _ _)))
    exact mem_nhdsWithin.mpr ⟨V, hV, hxV, hVH⟩

section Ambient

variable {M : Type u} [TopologicalSpace M]

theorem IsStableCrossingBlock.exists_kink_recentre [T2Space M]
    {f : EuclideanSpace ℝ (Fin 2) → M} {S SA SB : Set (EuclideanSpace ℝ (Fin 2))}
    {ec ec' : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ ℓ' : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A A' : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {a b : ℝ × ℝ → ℝ} {La Lb η α₁ β₁ κ : ℝ} {y : M} {O : Set M}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hBd : ∀ z ∈ ec.source, z ∈ BdM ↔ ℓ (ec z) = 0)
    (hyd : y ∈ doublePointSet f S) (hy : y ∈ innerChartBlock ec A r tlo)
    (hκ : -1 < κ) (hO : IsOpen O) (hyO : y ∈ O) (hOsrc : O ⊆ ec.source ∩ ec'.source)
    (hOpos : ∀ z ∈ O, tlo = 0 → (A (ec y)).2.2 ≠ 0 → 0 < (A (ec z)).2.2)
    (hA'y : A' (ec' y) = 0)
    (hrel : ∀ z ∈ O, (tlo = 0 → 0 ≤ (A (ec z)).2.2) → A' (ec' z) =
      ((A (ec z)).1 + kinkOffset (-(A (ec y)).1) α₁ (A (ec y)).2.2 (A (ec z)).2.2,
        (A (ec z)).2.1 + kinkOffset (-(A (ec y)).2.1) β₁ (A (ec y)).2.2 (A (ec z)).2.2,
        kinkHeight (A (ec y)).2.2 κ (A (ec z)).2.2))
    (hbd : tlo = 0 → (A (ec y)).2.2 = 0 → (∀ z, (A' z).2.2 = ℓ' z) ∧
      ∀ z ∈ O, (0 ≤ (A (ec z)).2.2 ↔ 0 ≤ (A' (ec' z)).2.2)) :
    ∃ (r' tlo' : ℝ) (a' b' : ℝ × ℝ → ℝ), 0 < r' ∧
      IsStableCrossingBlock f S ec' ℓ' BdM A' r' tlo' (SA ∩ f ⁻¹' chartBlock ec' A' r' tlo')
        (SB ∩ f ⁻¹' chartBlock ec' A' r' tlo') a' b' La Lb η ∧
      chartBlock ec' A' r' tlo' ⊆ O := by
  classical
  obtain ⟨hr, -, -, -, -, -, -, hside0, hpre, -, -, -, hplA, hplB, hnA, hnB, -, -, hpa, hpb⟩ :=
    id h
  set w₀ := A (ec y) with hw₀
  have htlo : tlo = -r ∨ tlo = 0 := hside0.imp (fun h => h.1) (fun h => h.1)
  have htle : tlo ≤ 0 := by
    rcases htlo with h | h
    · linarith
    · exact h.le
  have hyB : y ∈ chartBlock ec A r tlo := chartBlock_mono_of_half ec A hr.le htle hy
  obtain ⟨⟨xA, hxA, hfxA⟩, ⟨xB, hxB, hfxB⟩⟩ := sheets_nonempty_of_isStableCrossingBlock h hyd hyB
  have hfxA' : f xA = y := hfxA
  have hfxB' : f xB = y := hfxB
  have hinA : f xA ∈ innerChartBlock ec A r tlo := by rw [hfxA']; exact hy
  have hinB : f xB ∈ innerChartBlock ec A r tlo := by rw [hfxB']; exact hy
  obtain ⟨εA, hεA, hgoodA⟩ := exists_pos_forall_mem_nhdsWithin_of_isPLHomeomorphOn hplA hxA
    (hnA xA hxA hinA).1 (hnA xA hxA hinA).2
  obtain ⟨εB, hεB, hgoodB⟩ := exists_pos_forall_mem_nhdsWithin_of_isPLHomeomorphOn hplB hxB
    (hnB xB hxB hinB).1 (hnB xB hxB hinB).2
  have hw₀in : w₀ ∈ blockBox (r / 2) (tlo / 2) := hy.2
  have hw₀1 : |w₀.1| ≤ r / 2 := hw₀in.1
  have hw₀2 : |w₀.2.1| ≤ r / 2 := hw₀in.2.1
  have hw₀3 : tlo / 2 ≤ w₀.2.2 := hw₀in.2.2.1
  have hw₀4 : w₀.2.2 ≤ r / 2 := hw₀in.2.2.2
  have hyS : y ∈ ec.source := (hOsrc hyO).1
  set G : Set (ℝ × ℝ × ℝ) := A '' (ec.target ∩ ec.symm ⁻¹' O) with hGdef
  have hGo : IsOpen G := by
    have heq : G = A.symm ⁻¹' (ec.target ∩ ec.symm ⁻¹' O) := by
      ext w
      constructor
      · rintro ⟨x, hx, rfl⟩
        rwa [mem_preimage, A.symm_apply_apply]
      · intro hw
        exact ⟨A.symm w, hw, A.apply_symm_apply w⟩
    rw [heq]
    exact (ec.isOpen_inter_preimage_symm hO).preimage
      A.symm.toAffineMap.continuous_of_finiteDimensional
  have hw₀G : w₀ ∈ G :=
    ⟨ec y, ⟨ec.map_source hyS, by rw [mem_preimage, ec.left_inv hyS]; exact hyO⟩, rfl⟩
  obtain ⟨ρG, hρG, hballG⟩ := Metric.isOpen_iff.mp hGo w₀ hw₀G
  set ρ₂ := min (min εA εB) (min ρG (r / 2)) with hρ₂
  have hρ₂pos : 0 < ρ₂ := lt_min (lt_min hεA hεB) (lt_min hρG (by linarith))
  have hρA : ρ₂ ≤ εA := (min_le_left _ _).trans (min_le_left _ _)
  have hρB : ρ₂ ≤ εB := (min_le_left _ _).trans (min_le_right _ _)
  have hρG' : ρ₂ ≤ ρG := (min_le_right _ _).trans (min_le_left _ _)
  have hρr : ρ₂ ≤ r / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set K := kinkBound α₁ β₁ κ with hKdef
  have hKpos : 0 < K := by
    have h1 : 0 < 1 + κ := by linarith
    have h2 : 0 ≤ (1 + |α₁| + |β₁|) * (1 + 1 / (1 + κ)) := by positivity
    rw [hKdef, kinkBound]
    linarith
  set V' : Set (EuclideanSpace ℝ (Fin 3)) := ec'.target ∩ ec'.symm ⁻¹' O with hV'def
  have hV'o : IsOpen V' := ec'.isOpen_inter_preimage_symm hO
  have hyS' : y ∈ ec'.source := (hOsrc hyO).2
  have hyV' : ec' y ∈ V' :=
    ⟨ec'.map_source hyS', by rw [mem_preimage, ec'.left_inv hyS']; exact hyO⟩
  have hA'Vo : IsOpen (A' '' V') := by
    have heq : A' '' V' = A'.symm ⁻¹' V' := by
      ext w
      constructor
      · rintro ⟨x, hx, rfl⟩
        rwa [mem_preimage, A'.symm_apply_apply]
      · intro hw
        exact ⟨A'.symm w, hw, A'.apply_symm_apply w⟩
    rw [heq]
    exact hV'o.preimage A'.symm.toAffineMap.continuous_of_finiteDimensional
  obtain ⟨ρV, hρV, hballV⟩ := Metric.isOpen_iff.mp hA'Vo 0 ⟨ec' y, hyV', hA'y⟩
  set r' := min (ρ₂ / (2 * K)) (ρV / 2) with hr'def
  have hr' : 0 < r' := lt_min (div_pos hρ₂pos (mul_pos two_pos hKpos)) (by linarith)
  have hKr' : K * r' < ρ₂ := by
    have h1 : r' * (2 * K) ≤ ρ₂ := (le_div_iff₀ (mul_pos two_pos hKpos)).mp (min_le_left _ _)
    linarith
  have hr'V : r' < ρV := by
    have h1 : r' ≤ ρV / 2 := min_le_right _ _
    linarith
  set bnd : Prop := tlo = 0 ∧ w₀.2.2 = 0 with hbnd
  set tlo' : ℝ := if bnd then 0 else -r' with htlo'def
  have htlo'lo : -r' ≤ tlo' := by
    rw [htlo'def]
    split_ifs
    · linarith
    · exact le_rfl
  have htlo'le : tlo' ≤ 0 := by
    rw [htlo'def]
    split_ifs
    · exact le_rfl
    · linarith
  have hbox : ∀ q ∈ blockBox r' tlo', q ∈ ball (0 : ℝ × ℝ × ℝ) ρV := by
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hq
    rw [mem_ball, dist_zero_right, Prod.norm_def, Prod.norm_def, Real.norm_eq_abs,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have h5 : |q.2.2| ≤ r' := abs_le.mpr ⟨by linarith, h4⟩
    exact lt_of_le_of_lt (max_le h1 (max_le h2 h5)) hr'V
  have hNO : ∀ z ∈ chartBlock ec' A' r' tlo', z ∈ O := by
    rintro z ⟨hzs, hzb⟩
    obtain ⟨v, hv, hveq⟩ := hballV (hbox _ hzb)
    have hv' : v = ec' z := A'.injective hveq
    rw [hv'] at hv
    have h1 := hv.2
    rwa [mem_preimage, ec'.left_inv hzs] at h1
  have hNeq : chartBlock ec' A' r' tlo' = ec'.symm '' (A'.symm '' blockBox r' tlo') := by
    ext z
    constructor
    · rintro ⟨hzs, hzb⟩
      exact ⟨ec' z, ⟨A' (ec' z), hzb, A'.symm_apply_apply _⟩, ec'.left_inv hzs⟩
    · rintro ⟨x, ⟨q, hq, rfl⟩, rfl⟩
      obtain ⟨v, hv, hveq⟩ := hballV (hbox q hq)
      have hvq : A'.symm q = v := by rw [← hveq, A'.symm_apply_apply]
      have hvt : A'.symm q ∈ ec'.target := hvq ▸ hv.1
      refine ⟨ec'.map_target hvt, ?_⟩
      rw [mem_preimage, mem_preimage, ec'.right_inv hvt, A'.apply_symm_apply]
      exact hq
  have hNcpt : IsCompact (chartBlock ec' A' r' tlo') := by
    rw [hNeq]
    refine ((isCompact_blockBox r' tlo').image A'.symm.toAffineMap.continuous_of_finiteDimensional
      ).image_of_continuousOn (ec'.continuousOn_symm.mono ?_)
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨v, hv, hveq⟩ := hballV (hbox q hq)
    have hvq : A'.symm q = v := by rw [← hveq, A'.symm_apply_apply]
    change A'.symm q ∈ ec'.target
    rw [hvq]
    exact hv.1
  have hNclosure : closure (chartBlock ec' A' r' tlo') = chartBlock ec' A' r' tlo' :=
    hNcpt.isClosed.closure_eq
  have hpremN : ∀ z ∈ chartBlock ec' A' r' tlo', tlo = 0 → 0 ≤ (A (ec z)).2.2 := by
    intro z hz ht0
    by_cases hb : w₀.2.2 = 0
    · have hbnd' : bnd := ⟨ht0, hb⟩
      have htl : tlo' = 0 := by rw [htlo'def, ite_eq_left hbnd']
      have h1 : 0 ≤ (A' (ec' z)).2.2 := by
        have := hz.2.2.2.1
        rwa [htl] at this
      exact ((hbd ht0 hb).2 z (hNO z hz)).2 h1
    · exact (hOpos z (hNO z hz) ht0 hb).le
  set Ψ : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun w =>
    (w.1 + kinkOffset (-w₀.1) α₁ w₀.2.2 w.2.2, w.2.1 + kinkOffset (-w₀.2.1) β₁ w₀.2.2 w.2.2,
      kinkHeight w₀.2.2 κ w.2.2) with hΨdef
  have heqN : ∀ z ∈ chartBlock ec' A' r' tlo', A' (ec' z) = Ψ (A (ec z)) :=
    fun z hz => hrel z (hNO z hz) (hpremN z hz)
  have hdistN : ∀ z, Ψ (A (ec z)) ∈ blockBox r' tlo' → dist (A (ec z)) w₀ < ρ₂ :=
    fun z hz => (dist_le_kinkBound_mul (w := A (ec z)) (w₀ := w₀) hκ htlo'lo hz).trans_lt hKr'
  have hsub : chartBlock ec' A' r' tlo' ⊆ chartBlock ec A r tlo := by
    intro z hz
    have hzb : A' (ec' z) ∈ blockBox r' tlo' := hz.2
    rw [heqN z hz] at hzb
    have hd := hdistN z hzb
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq] at hd
    have hd1 : |(A (ec z)).1 - w₀.1| < ρ₂ := (le_max_left _ _).trans_lt hd
    have hd2 : |(A (ec z)).2.1 - w₀.2.1| < ρ₂ :=
      ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hd
    have hd3 : |(A (ec z)).2.2 - w₀.2.2| < ρ₂ :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hd
    rw [abs_lt] at hd1 hd2 hd3
    rw [abs_le] at hw₀1 hw₀2
    refine ⟨(hOsrc (hNO z hz)).1, ?_⟩
    change |(A (ec z)).1| ≤ r ∧ |(A (ec z)).2.1| ≤ r ∧ tlo ≤ (A (ec z)).2.2 ∧
      (A (ec z)).2.2 ≤ r
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr ⟨by linarith, by linarith⟩, ?_,
      by linarith⟩
    rcases htlo with ht | ht
    · rw [ht]
      rw [ht] at hw₀3
      linarith
    · rw [ht]
      exact hpremN z hz ht
  have hrelN : ∀ z ∈ chartBlock ec A r tlo,
      z ∈ chartBlock ec' A' r' tlo' ↔ Ψ (A (ec z)) ∈ blockBox r' tlo' := by
    intro z hz
    constructor
    · intro hzN
      rw [← heqN z hzN]
      exact hzN.2
    · intro hzb
      have hd := hdistN z hzb
      obtain ⟨x, hx, hxz⟩ := hballG (mem_ball.mpr (hd.trans_le hρG'))
      have hxz' : x = ec z := A.injective hxz
      have hzO : z ∈ O := by
        have h1 := hx.2
        rwa [mem_preimage, hxz', ec.left_inv hz.1] at h1
      have hprem : tlo = 0 → 0 ≤ (A (ec z)).2.2 := by
        intro ht0
        have h1 := hz.2.2.2.1
        rwa [ht0] at h1
      refine ⟨(hOsrc hzO).2, ?_⟩
      change A' (ec' z) ∈ blockBox r' tlo'
      rw [hrel z hzO hprem]
      exact hzb
  obtain ⟨a', ha'pl, ha'eq⟩ := exists_kinkGraph hpa (-w₀.1) α₁ (-w₀.2.1) β₁ w₀.2.2 hκ
  obtain ⟨b', hb'pl, hb'eq⟩ := exists_kinkGraph hpb (-w₀.2.1) β₁ (-w₀.1) α₁ w₀.2.2 hκ
  have hside : (tlo' = -r' ∧ Disjoint (chartBlock ec' A' r' tlo') BdM) ∨
      (tlo' = 0 ∧ tlo = 0 ∧ (∀ t, 0 ≤ kinkHeight w₀.2.2 κ t ↔ 0 ≤ t) ∧
        (∀ t, kinkHeight w₀.2.2 κ t = 0 ↔ t = 0) ∧ ∀ z, (A' z).2.2 = ℓ' z) := by
    by_cases hb : bnd
    · obtain ⟨ht0, hw0⟩ := hb
      right
      refine ⟨by rw [htlo'def, ite_eq_left ⟨ht0, hw0⟩], ht0, ?_, ?_, (hbd ht0 hw0).1⟩
      · rw [hw0]
        exact kinkHeight_nonneg_iff hκ
      · rw [hw0]
        exact kinkHeight_eq_zero_iff hκ
    · left
      refine ⟨by rw [htlo'def, ite_eq_right hb], ?_⟩
      rcases hside0 with ⟨-, hdis⟩ | ⟨ht, hheight, -⟩
      · exact hdis.mono_left hsub
      · rw [Set.disjoint_left]
        intro z hz hzB
        have hw0 : w₀.2.2 ≠ 0 := fun h0 => hb ⟨ht, h0⟩
        have hpos := hOpos z (hNO z hz) ht hw0
        have hzs : z ∈ ec.source := (hOsrc (hNO z hz)).1
        have h1 := (hBd z hzs).1 hzB
        rw [← hheight] at h1
        linarith
  have hdistIn : ∀ x, f x ∈ chartBlock ec' A' r' tlo' → dist (A (ec (f x))) w₀ < ρ₂ := by
    intro x hx
    have h1 : A' (ec' (f x)) ∈ blockBox r' tlo' := hx.2
    rw [heqN _ hx] at h1
    exact hdistN _ h1
  have hinSub : innerChartBlock ec' A' r' tlo' ⊆ chartBlock ec' A' r' tlo' :=
    chartBlock_mono_of_half ec' A' hr'.le htlo'le
  have hUform : ∀ (c₀ c₁ : ℝ) (P : Set (ℝ × ℝ)) (p : ℝ × ℝ) (z : M),
      z ∈ chartBlock ec' A' r' tlo' → p.2 = (A (ec z)).2.2 → P ∈ 𝓝[blockHalfPlane tlo] p →
      ∃ U ∈ 𝓝 p, U ∩ (fun q : ℝ × ℝ => (q.1 + kinkOffset c₀ c₁ w₀.2.2 q.2,
        kinkHeight w₀.2.2 κ q.2)) ⁻¹' blockHalfPlane tlo' ⊆ P := by
    intro c₀ c₁ P p z hz hpz hP
    rcases htlo with ht | ht
    · have hne : tlo ≠ 0 := by
        rw [ht]
        exact (neg_neg_of_pos hr).ne
      rw [blockHalfPlane_eq_univ hne, nhdsWithin_univ] at hP
      exact ⟨P, hP, inter_subset_left⟩
    · obtain ⟨U, hUo, hpU, hUP⟩ := mem_nhdsWithin.mp hP
      by_cases hb : w₀.2.2 = 0
      · refine ⟨U, hUo.mem_nhds hpU, fun q hq => hUP ⟨hq.1, fun _ => ?_⟩⟩
        have htl : tlo' = 0 := by rw [htlo'def, ite_eq_left ⟨ht, hb⟩]
        have h1 : 0 ≤ kinkHeight w₀.2.2 κ q.2 := hq.2 htl
        rw [hb] at h1
        exact (kinkHeight_nonneg_iff hκ q.2).1 h1
      · have hpos : 0 < p.2 := by
          rw [hpz]
          exact hOpos z (hNO z hz) ht hb
        refine ⟨U ∩ {q | 0 < q.2}, Filter.inter_mem (hUo.mem_nhds hpU)
          ((isOpen_lt continuous_const continuous_snd).mem_nhds hpos),
          fun q hq => hUP ⟨hq.1.1, fun _ => hq.1.2.le⟩⟩
  have hpxA : blockSheetProjA ec A f xA = w₀.2 := by
    simp only [blockSheetProjA, hfxA', hw₀, Prod.mk.eta]
  have hpxB : blockSheetProjB ec A f xB = (w₀.1, w₀.2.2) := by
    simp only [blockSheetProjB, hfxB', hw₀]
  have hgA : ∀ x ∈ SA, f x ∈ innerChartBlock ec' A' r' tlo' → SA ∈ 𝓝[S] x ∧
      ∃ U ∈ 𝓝 (blockSheetProjA ec A f x), U ∩ (fun q : ℝ × ℝ =>
        (q.1 + kinkOffset (-w₀.2.1) β₁ w₀.2.2 q.2, kinkHeight w₀.2.2 κ q.2)) ⁻¹'
          blockHalfPlane tlo' ⊆ blockSheetProjA ec A f '' SA := by
    intro x hx hxin
    have hxN := hinSub hxin
    have hd := hdistIn x hxN
    have hdp : dist (blockSheetProjA ec A f x) (blockSheetProjA ec A f xA) < εA := by
      rw [hpxA]
      have h2 : dist (A (ec (f x))).2 w₀.2 ≤ dist (A (ec (f x))) w₀ := by
        rw [Prod.dist_eq]
        exact le_max_right _ _
      exact (h2.trans_lt hd).trans_le hρA
    obtain ⟨hS, hP⟩ := hgoodA x hx hdp
    exact ⟨hS, hUform (-w₀.2.1) β₁ _ _ (f x) hxN rfl hP⟩
  have hgB : ∀ x ∈ SB, f x ∈ innerChartBlock ec' A' r' tlo' → SB ∈ 𝓝[S] x ∧
      ∃ U ∈ 𝓝 (blockSheetProjB ec A f x), U ∩ (fun q : ℝ × ℝ =>
        (q.1 + kinkOffset (-w₀.1) α₁ w₀.2.2 q.2, kinkHeight w₀.2.2 κ q.2)) ⁻¹'
          blockHalfPlane tlo' ⊆ blockSheetProjB ec A f '' SB := by
    intro x hx hxin
    have hxN := hinSub hxin
    have hd := hdistIn x hxN
    have hdp : dist (blockSheetProjB ec A f x) (blockSheetProjB ec A f xB) < εB := by
      rw [hpxB]
      have h2 : dist ((A (ec (f x))).1, (A (ec (f x))).2.2) (w₀.1, w₀.2.2) ≤
          dist (A (ec (f x))) w₀ := by
        rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq]
        exact max_le_max le_rfl (le_max_right _ _)
      exact (h2.trans_lt hd).trans_le hρB
    obtain ⟨hS, hP⟩ := hgoodB x hx hdp
    exact ⟨hS, hUform (-w₀.1) α₁ _ _ (f x) hxN rfl hP⟩
  have hblock := IsStableCrossingBlock.transfer (α := kinkOffset (-w₀.1) α₁ w₀.2.2)
    (β := kinkOffset (-w₀.2.1) β₁ w₀.2.2) (γ := kinkHeight w₀.2.2 κ) (ℓ' := ℓ') h
    (kinkHeight_surjective hκ) (isPLHomeomorphOn_kinkShear (-w₀.2.1) β₁ w₀.2.2 hκ)
    (isPLHomeomorphOn_kinkShear (-w₀.1) α₁ w₀.2.2 hκ)
    (isPiecewiseAffineOn_add_kinkOffset hpa (-w₀.1) α₁ w₀.2.2)
    (isPiecewiseAffineOn_add_kinkOffset hpb (-w₀.2.1) β₁ w₀.2.2)
    ha'eq hb'eq ha'pl hb'pl hr' (by rw [hNclosure]; exact hNcpt)
    (by rw [hNclosure]; exact fun z hz => hz.1) hside hsub hrelN heqN hgA hgB
  exact ⟨r', tlo', a', b', hr', hblock, hNO⟩

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
