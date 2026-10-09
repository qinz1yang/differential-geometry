/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.StableCrossingBlockRecentre
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import DifferentialGeometry.Topology.PiecewiseLinear.Product
import DifferentialGeometry.Topology.PiecewiseLinear.PLPiece
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem isHPolytope_blockBox (r tlo : ℝ) : IsHPolytope (blockBox r tlo) := by
  have h : blockBox r tlo = Icc (-r) r ×ˢ (Icc (-r) r ×ˢ Icc tlo r) := by
    ext p
    simp only [blockBox, mem_ofPred_eq, mem_prod, mem_Icc, abs_le]
  rw [h]
  exact isHPolytope_Icc.prod (isHPolytope_Icc.prod isHPolytope_Icc)

section Ambient

variable {M : Type u} [TopologicalSpace M]

theorem exists_isOpen_inter_preimage_subset_ball_union [T2Space M]
    {f : EuclideanSpace ℝ (Fin 2) → M} {S : Set (EuclideanSpace ℝ (Fin 2))} (hS : IsCompact S)
    (hf : ContinuousOn f S) {x₁ x₂ : EuclideanSpace ℝ (Fin 2)} {y : M}
    (hfib : ∀ x ∈ S, f x = y → x = x₁ ∨ x = x₂) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ O : Set M, IsOpen O ∧ y ∈ O ∧ S ∩ f ⁻¹' O ⊆ ball x₁ ρ ∪ ball x₂ ρ := by
  set K : Set (EuclideanSpace ℝ (Fin 2)) := S \ (ball x₁ ρ ∪ ball x₂ ρ) with hK
  have hKc : IsCompact K := hS.diff (isOpen_ball.union isOpen_ball)
  have hfK : IsCompact (f '' K) := hKc.image_of_continuousOn (hf.mono sdiff_subset)
  refine ⟨(f '' K)ᶜ, hfK.isClosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, ⟨hxS, hxb⟩, hxy⟩
    rcases hfib x hxS hxy with rfl | rfl
    · exact hxb (Or.inl (mem_ball_self hρ))
    · exact hxb (Or.inr (mem_ball_self hρ))
  · rintro x ⟨hxS, hxO⟩
    by_contra hxb
    exact hxO ⟨x, ⟨hxS, hxb⟩, rfl⟩

theorem exists_pos_chartBlock_subset_of_isOpen [T2Space M]
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) {y : M} (hy : y ∈ ec.source)
    (hA : A (ec y) = 0) {O : Set M} (hO : IsOpen O) (hyO : y ∈ O) :
    ∃ r₀ > 0, ∀ r tlo : ℝ, 0 < r → r ≤ r₀ → -r ≤ tlo →
      chartBlock ec A r tlo ⊆ O ∧ IsCompact (closure (chartBlock ec A r tlo)) ∧
        closure (chartBlock ec A r tlo) ⊆ ec.source ∧
          ∀ q ∈ blockBox r tlo, ∃ z ∈ chartBlock ec A r tlo, A (ec z) = q := by
  set O' : Set M := O ∩ ec.source with hO'
  have hO'o : IsOpen (ec '' O') :=
    ec.isOpen_image_of_subset_source (hO.inter ec.open_source) inter_subset_right
  have hAsc : Continuous A.symm := A.symm.toAffineMap.continuous_of_finiteDimensional
  have hW : IsOpen (A.symm ⁻¹' (ec '' O')) := hO'o.preimage hAsc
  have h0 : (0 : ℝ × ℝ × ℝ) ∈ A.symm ⁻¹' (ec '' O') := by
    change A.symm 0 ∈ ec '' O'
    rw [← hA, AffineEquiv.symm_apply_apply]
    exact ⟨y, ⟨hyO, hy⟩, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW 0 h0
  refine ⟨ε / 2, half_pos hε, fun r tlo hr hrε htlo => ?_⟩
  have hbox : ∀ p ∈ blockBox r tlo, A.symm p ∈ ec '' O' := by
    intro p hp
    apply hball
    obtain ⟨h1, h2, h3, h4⟩ := hp
    have h3' : |p.2.2| ≤ r := abs_le.mpr ⟨by linarith, h4⟩
    rw [mem_ball, dist_zero_right]
    have hle : ‖p‖ ≤ r := by
      rw [Prod.norm_def, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_le h1 (max_le h2 h3')
    linarith
  have hsub : chartBlock ec A r tlo ⊆ O := by
    rintro z ⟨hzs, hzb⟩
    obtain ⟨z', ⟨hz'O, hz's⟩, hz'z⟩ := hbox _ hzb
    rw [AffineEquiv.symm_apply_apply] at hz'z
    rw [← ec.injOn hz's hzs hz'z]
    exact hz'O
  have heq : chartBlock ec A r tlo = ec.symm '' (A.symm '' blockBox r tlo) := by
    ext z
    constructor
    · rintro ⟨hzs, hzb⟩
      exact ⟨ec z, ⟨A (ec z), hzb, AffineEquiv.symm_apply_apply A (ec z)⟩, ec.left_inv hzs⟩
    · rintro ⟨q, ⟨p, hp, rfl⟩, rfl⟩
      obtain ⟨z', ⟨-, hz's⟩, hz'z⟩ := hbox p hp
      have hqt : A.symm p ∈ ec.target := by rw [← hz'z]; exact ec.map_source hz's
      refine ⟨ec.map_target hqt, ?_⟩
      change A (ec (ec.symm (A.symm p))) ∈ blockBox r tlo
      rw [ec.right_inv hqt, AffineEquiv.apply_symm_apply]
      exact hp
  have hKt : A.symm '' blockBox r tlo ⊆ ec.target := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨z', ⟨-, hz's⟩, hz'z⟩ := hbox p hp
    rw [← hz'z]
    exact ec.map_source hz's
  have hcpt : IsCompact (chartBlock ec A r tlo) := by
    rw [heq]
    exact ((isCompact_blockBox r tlo).image hAsc).image_of_continuousOn
      (ec.continuousOn_symm.mono hKt)
  have hpts : ∀ q ∈ blockBox r tlo, ∃ z ∈ chartBlock ec A r tlo, A (ec z) = q := by
    intro q hq
    have hqt : A.symm q ∈ ec.target := hKt ⟨q, hq, rfl⟩
    refine ⟨ec.symm (A.symm q), ?_, ?_⟩
    · rw [heq]
      exact ⟨A.symm q, ⟨q, hq, rfl⟩, rfl⟩
    · rw [ec.right_inv hqt, AffineEquiv.apply_symm_apply]
  rw [hcpt.isClosed.closure_eq]
  exact ⟨hsub, hcpt, fun z hz => hz.1, hpts⟩

theorem isStableCrossingBlock_of_sheets {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))} {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo ρ La Lb η : ℝ}
    {a b : ℝ × ℝ → ℝ} {x₁ x₂ : EuclideanSpace ℝ (Fin 2)}
    {H₁ H₂ : Set (EuclideanSpace ℝ (Fin 2))} {O : Set M}
    (hr : 0 < r) (hη : 0 < η) (hLa : 0 ≤ La) (hLb : 0 ≤ Lb) (hLL : La * Lb ≤ 1 - η)
    (hcpt : IsCompact (closure (chartBlock ec A r tlo)))
    (hsrc : closure (chartBlock ec A r tlo) ⊆ ec.source)
    (hcase : (tlo = -r ∧ Disjoint (chartBlock ec A r tlo) BdM) ∨
      (tlo = 0 ∧ (∀ z, (A z).2.2 = ℓ z) ∧
        ∀ x ∈ H₁ ∪ H₂, (x ∈ frontier S ↔ (A (ec (f x))).2.2 = 0)))
    (hhalf : tlo = 0 → ∀ x ∈ S, f x ∈ ec.source → 0 ≤ (A (ec (f x))).2.2)
    (hfc : ContinuousOn f S) (hbox : chartBlock ec A r tlo ⊆ O)
    (hsep : S ∩ f ⁻¹' O ⊆ ball x₁ ρ ∪ ball x₂ ρ) (hballs : Disjoint (ball x₁ ρ) (ball x₂ ρ))
    (hH₁S : H₁ ⊆ S) (hH₂S : H₂ ⊆ S) (hloc₁ : S ∩ ball x₁ ρ ⊆ H₁)
    (hloc₂ : S ∩ ball x₂ ρ ⊆ H₂) (hfar₁ : Disjoint H₁ (ball x₂ ρ))
    (hfar₂ : Disjoint H₂ (ball x₁ ρ)) (hpoly₁ : IsPolyhedron H₁) (hpoly₂ : IsPolyhedron H₂)
    (hsrc₁ : ∀ x ∈ H₁, f x ∈ ec.source) (hsrc₂ : ∀ x ∈ H₂, f x ∈ ec.source)
    (hpl₁ : IsPiecewiseAffineOn (fun x => A (ec (f x))) H₁)
    (hpl₂ : IsPiecewiseAffineOn (fun x => A (ec (f x))) H₂)
    (hgraph₁ : ∀ x ∈ H₁, (A (ec (f x))).1 = a ((A (ec (f x))).2.1, (A (ec (f x))).2.2))
    (hgraph₂ : ∀ x ∈ H₂, (A (ec (f x))).2.1 = b ((A (ec (f x))).1, (A (ec (f x))).2.2))
    (hΦ₁ : ∃ Φ : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ,
      (∀ x ∈ H₁, blockSheetProjA ec A f x = Φ x) ∧
        ∀ x ∈ ball x₁ ρ, (x ∈ S ↔ (tlo = 0 → 0 ≤ (Φ x).2)))
    (hΦ₂ : ∃ Φ : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ,
      (∀ x ∈ H₂, blockSheetProjB ec A f x = Φ x) ∧
        ∀ x ∈ ball x₂ ρ, (x ∈ S ↔ (tlo = 0 → 0 ≤ (Φ x).2)))
    (hLipa : ∀ v v' t : ℝ, |a (v, t) - a (v', t)| ≤ La * |v - v'|)
    (hLipb : ∀ u u' t : ℝ, |b (u, t) - b (u', t)| ≤ Lb * |u - u'|)
    (hpa : IsPiecewiseAffineOn a univ) (hpb : IsPiecewiseAffineOn b univ) :
    IsStableCrossingBlock f S ec ℓ BdM A r tlo (H₁ ∩ f ⁻¹' chartBlock ec A r tlo)
      (H₂ ∩ f ⁻¹' chartBlock ec A r tlo) a b La Lb η := by
  set SA := H₁ ∩ f ⁻¹' chartBlock ec A r tlo with hSA
  set SB := H₂ ∩ f ⁻¹' chartBlock ec A r tlo with hSB
  have hSA1 : SA ⊆ ball x₁ ρ := by
    intro x hx
    rcases hsep ⟨hH₁S hx.1, hbox hx.2⟩ with h | h
    · exact h
    · exact absurd h (Set.disjoint_left.mp hfar₁ hx.1)
  have hSB2 : SB ⊆ ball x₂ ρ := by
    intro x hx
    rcases hsep ⟨hH₂S hx.1, hbox hx.2⟩ with h | h
    · exact absurd h (Set.disjoint_left.mp hfar₂ hx.1)
    · exact h
  have hpre : S ∩ f ⁻¹' chartBlock ec A r tlo = SA ∪ SB := by
    apply Subset.antisymm
    · rintro x ⟨hxS, hxB⟩
      rcases hsep ⟨hxS, hbox hxB⟩ with h | h
      · exact Or.inl ⟨hloc₁ ⟨hxS, h⟩, hxB⟩
      · exact Or.inr ⟨hloc₂ ⟨hxS, h⟩, hxB⟩
    · rintro x (hx | hx)
      · exact ⟨hH₁S hx.1, hx.2⟩
      · exact ⟨hH₂S hx.1, hx.2⟩
  have hdisj : Disjoint SA SB :=
    Set.disjoint_left.mpr fun x hxA hxB => Set.disjoint_left.mp hballs (hSA1 hxA) (hSB2 hxB)
  have hboxH : ∀ {H : Set (EuclideanSpace ℝ (Fin 2))}, (∀ x ∈ H, f x ∈ ec.source) →
      H ∩ f ⁻¹' chartBlock ec A r tlo = H ∩ (fun x => A (ec (f x))) ⁻¹' blockBox r tlo := by
    intro H hsrcH
    ext x
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hsrcH x h.1, h.2⟩⟩
  have hpolyS : ∀ {H : Set (EuclideanSpace ℝ (Fin 2))}, IsPolyhedron H →
      (∀ x ∈ H, f x ∈ ec.source) → IsPiecewiseAffineOn (fun x => A (ec (f x))) H →
      IsPolyhedron (H ∩ f ⁻¹' chartBlock ec A r tlo) := by
    intro H hH hsrcH hplH
    rw [hboxH hsrcH]
    refine isPolyhedron_inter_preimage_of_isCompact hplH (isHPolytope_blockBox r tlo) ?_
    exact hH.isCompact.of_isClosed_subset
      (hplH.continuousOn.preimage_isClosed_of_isClosed hH.isCompact.isClosed
        (isCompact_blockBox r tlo).isClosed) inter_subset_left
  have hnbS : ∀ x ∈ S, f x ∈ innerChartBlock ec A r tlo →
      f ⁻¹' chartBlock ec A r tlo ∈ 𝓝[S] x := by
    intro x hxS hin
    obtain ⟨hxs, h1, h2, h3, h4⟩ := hin
    have hAc : Continuous A := A.toAffineMap.continuous_of_finiteDimensional
    rcases hcase with ⟨ht, -⟩ | ⟨ht, -, -⟩
    · let Oin : Set M := ec.source ∩ ec ⁻¹' (⇑A ⁻¹'
        {p : ℝ × ℝ × ℝ | |p.1| < r ∧ |p.2.1| < r ∧ |p.2.2| < r})
      have hOin : IsOpen Oin := by
        refine ec.continuousOn.isOpen_inter_preimage ec.open_source (IsOpen.preimage hAc ?_)
        exact (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
          ((isOpen_lt (continuous_abs.comp continuous_snd.fst) continuous_const).inter
          (isOpen_lt (continuous_abs.comp continuous_snd.snd) continuous_const))
      have hfx : f x ∈ Oin := by
        refine ⟨hxs, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · rw [ht] at h3
          exact abs_lt.mpr ⟨by linarith, by linarith⟩
      have hsub : Oin ⊆ chartBlock ec A r tlo := by
        rintro z ⟨hzs, hz1, hz2, hz3⟩
        refine ⟨hzs, hz1.le, hz2.le, ?_, ?_⟩
        · rw [ht]
          exact (abs_lt.mp hz3).1.le
        · exact (abs_lt.mp hz3).2.le
      exact (hfc x hxS).preimage_mem_nhdsWithin
        (Filter.mem_of_superset (hOin.mem_nhds hfx) hsub)
    · let Oin : Set M := ec.source ∩ ec ⁻¹' (⇑A ⁻¹'
        {p : ℝ × ℝ × ℝ | |p.1| < r ∧ |p.2.1| < r ∧ p.2.2 < r})
      have hOin : IsOpen Oin := by
        refine ec.continuousOn.isOpen_inter_preimage ec.open_source (IsOpen.preimage hAc ?_)
        exact (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
          ((isOpen_lt (continuous_abs.comp continuous_snd.fst) continuous_const).inter
          (isOpen_lt continuous_snd.snd continuous_const))
      have hfx : f x ∈ Oin := by
        refine ⟨hxs, ?_, ?_, ?_⟩
        · linarith
        · linarith
        · linarith
      have hmem : f ⁻¹' Oin ∈ 𝓝[S] x := (hfc x hxS).preimage_mem_nhdsWithin (hOin.mem_nhds hfx)
      filter_upwards [hmem, self_mem_nhdsWithin] with x' hx' hx'S
      obtain ⟨hx's, hu, hv, htr⟩ := hx'
      refine ⟨hx's, hu.le, hv.le, ?_, htr.le⟩
      rw [ht]
      exact hhalf ht x' hx'S hx's
  have hSnbhd : ∀ {H : Set (EuclideanSpace ℝ (Fin 2))} {x₀ : EuclideanSpace ℝ (Fin 2)},
      H ⊆ S → S ∩ ball x₀ ρ ⊆ H → ∀ x ∈ H ∩ f ⁻¹' chartBlock ec A r tlo, x ∈ ball x₀ ρ →
        f x ∈ innerChartBlock ec A r tlo → H ∩ f ⁻¹' chartBlock ec A r tlo ∈ 𝓝[S] x := by
    intro H x₀ hHS hloc x hx hxb hin
    exact Filter.inter_mem (Filter.mem_of_superset (inter_mem_nhdsWithin S
      (isOpen_ball.mem_nhds hxb)) hloc) (hnbS x (hHS hx.1) hin)
  have hhalfimg : ∀ {x₀ : EuclideanSpace ℝ (Fin 2)} {Φ : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ}
      {T : Set (EuclideanSpace ℝ (Fin 2))},
      (∀ x ∈ ball x₀ ρ, (x ∈ S ↔ (tlo = 0 → 0 ≤ (Φ x).2))) → ∀ x ∈ ball x₀ ρ,
        T ∈ 𝓝[S] x → Φ '' T ∈ 𝓝[blockHalfPlane tlo] (Φ x) := by
    intro x₀ Φ T hS x hxb hT
    obtain ⟨U, hU, hxU, hUS⟩ := mem_nhdsWithin.mp hT
    have hU' : IsOpen (U ∩ ball x₀ ρ) := hU.inter isOpen_ball
    have himg : IsOpen (Φ '' (U ∩ ball x₀ ρ)) := Φ.isOpenMap _ hU'
    have hmem : blockHalfPlane tlo ∩ Φ '' (U ∩ ball x₀ ρ) ∈ 𝓝[blockHalfPlane tlo] (Φ x) :=
      inter_mem_nhdsWithin _ (himg.mem_nhds ⟨x, ⟨hxU, hxb⟩, rfl⟩)
    refine Filter.mem_of_superset hmem ?_
    rintro q ⟨hq, ⟨z, ⟨hzU, hzb⟩, rfl⟩⟩
    exact ⟨z, hUS ⟨hzU, (hS z hzb).mpr hq⟩, rfl⟩
  obtain ⟨Φ₁, hΦ₁eq, hΦ₁S⟩ := hΦ₁
  obtain ⟨Φ₂, hΦ₂eq, hΦ₂S⟩ := hΦ₂
  have hplA : IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA) := by
    have hpoly := hpolyS hpoly₁ hsrc₁ hpl₁
    refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly ?_ ?_
    · have h := (hpl₁.affine_comp (LinearMap.snd ℝ ℝ (ℝ × ℝ)).toAffineMap).mono_of_isPolyhedron
        hpoly inter_subset_left
      exact h.congr fun _ _ => rfl
    · refine InjOn.bijOn_image fun x hx x' hx' h => Φ₁.injective ?_
      rw [← hΦ₁eq x hx.1, ← hΦ₁eq x' hx'.1]
      exact h
  have hplB : IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB) := by
    have hpoly := hpolyS hpoly₂ hsrc₂ hpl₂
    refine isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hpoly ?_ ?_
    · have h := (hpl₂.affine_comp ((LinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
        ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ)))).toAffineMap).mono_of_isPolyhedron
        hpoly inter_subset_left
      exact h.congr fun _ _ => rfl
    · refine InjOn.bijOn_image fun x hx x' hx' h => Φ₂.injective ?_
      rw [← hΦ₂eq x hx.1, ← hΦ₂eq x' hx'.1]
      exact h
  have hnA : ∀ x ∈ SA, f x ∈ innerChartBlock ec A r tlo → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane tlo] (blockSheetProjA ec A f x) := by
    intro x hx hin
    have hT := hSnbhd hH₁S hloc₁ x hx (hSA1 hx) hin
    refine ⟨hT, ?_⟩
    rw [image_congr fun z hz => hΦ₁eq z hz.1, hΦ₁eq x hx.1]
    exact hhalfimg hΦ₁S x (hSA1 hx) hT
  have hnB : ∀ x ∈ SB, f x ∈ innerChartBlock ec A r tlo → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane tlo] (blockSheetProjB ec A f x) := by
    intro x hx hin
    have hT := hSnbhd hH₂S hloc₂ x hx (hSB2 hx) hin
    refine ⟨hT, ?_⟩
    rw [image_congr fun z hz => hΦ₂eq z hz.1, hΦ₂eq x hx.1]
    exact hhalfimg hΦ₂S x (hSB2 hx) hT
  refine ⟨hr, hη, hLa, hLb, hLL, hcpt, hsrc, ?_, hpre, hdisj, fun x hx => hgraph₁ x hx.1,
    fun x hx => hgraph₂ x hx.1, hplA, hplB, hnA, hnB, hLipa, hLipb, hpa, hpb⟩
  rcases hcase with h | ⟨ht, hℓ, hfr⟩
  · exact Or.inl h
  · exact Or.inr ⟨ht, hℓ, fun x hx => hfr x (hx.elim (fun h => Or.inl h.1) fun h => Or.inr h.1)⟩

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
