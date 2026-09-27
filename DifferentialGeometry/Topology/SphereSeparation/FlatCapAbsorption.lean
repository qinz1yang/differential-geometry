import DifferentialGeometry.Topology.SphereSeparation.FlatCapAttachment
import DifferentialGeometry.Topology.SphereSeparation.FlatCapBall
import DifferentialGeometry.Topology.Handle.HalfBallAbsorption

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

private theorem corner_chart_pullback
    {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace P]
    (Ψ : (E × ℝ) ≃ₘ[ℝ] F) (e : OpenPartialHomeomorph F (P × (ℝ × ℝ)))
    {R b ρ σ : ℝ}
    (hsource : e.source = Ψ '' {p : E × ℝ | p ∈ ball 0 R ×ˢ Ioo (-b) b ∧ 1 - ρ < ‖p.1‖ ^ 2})
    (hcoord : ∀ p : E × ℝ, (e (Ψ p)).2 = (1 - ‖p.1‖ ^ 2, σ * p.2))
    {q : P × (ℝ × ℝ)} (hq : q ∈ e.target) :
    ∃ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      e.symm q = Ψ p ∧ q.2 = (1 - ‖p.1‖ ^ 2, σ * p.2) := by
  have hs := e.map_target hq
  rw [hsource] at hs
  obtain ⟨p, hp, heq⟩ := hs
  refine ⟨p, hp.1, heq.symm, ?_⟩
  have hh := hcoord p
  rwa [heq, e.right_inv hq] at hh

variable (m : ℕ)

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨by simp⟩

theorem exists_diffeomorph_flat_cap_absorption
    (hm : 0 < m) {X : Type*}
    {e : X → EuclideanSpace ℝ (Fin ((m + 1) + 1))}
    {f g : Fin 2 → X → EuclideanSpace ℝ (Fin ((m + 1) + 1))}
    (d : SphereSides (range e)) (df : ∀ i, SphereSides (range (f i)))
    (dg : ∀ i, SphereSides (range (g i)))
    (Ψ : (EuclideanSpace ℝ (Fin (m + 1)) × ℝ) ≃ₘ[ℝ]
      EuclideanSpace ℝ (Fin ((m + 1) + 1)))
    (χ : Fin 2 → EuclideanSpace ℝ (Fin (m + 1)) → X)
    (D : EuclideanSpace ℝ (Fin ((m + 1) + 1)) ≃ₘ[ℝ]
      EuclideanSpace ℝ (Fin ((m + 1) + 1)))
    {S : Fin 2 → Set X} {R b σ : ℝ} {a : Fin 2 → ℝ}
    (hR : 1 < R) (ha : ∀ i, 0 < a i) (hab : ∀ i, a i < b) (hσ : σ = 1 ∨ σ = -1)
    (hχS : ∀ i, χ i '' closedBall 0 1 = S i)
    (hcap : ∀ i, ∀ x ∈ closedBall 0 1,
      f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap ((if i = 0 then σ else -σ) * a i) x))
    (hflat : ∀ i, ∀ x ∈ closedBall 0 1, g i (χ i x) = Ψ (x, 0))
    (hfix : ∀ i, EqOn (f i) e (S i)ᶜ) (hgfix : ∀ i, EqOn (g i) e (S i)ᶜ)
    (hret : ∀ i, ∀ p ∈ ball 0 R ×ˢ Ioo (-b) b,
      Ψ p ∈ e '' (S i)ᶜ ↔ ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2)
    (hS : ∀ p ∈ ball 0 R ×ˢ Ioo (-b) b, Ψ p ∈ range e ↔ ‖p.1‖ = 1)
    (hshared : range (g 0) ∩ range (g 1) = Ψ '' (closedBall 0 1 ×ˢ {(0 : ℝ)}))
    (hrel : (Disjoint (dg 0).compactSide (dg 1).compactSide ∧
        closure d.compactSide = closure (dg 0).compactSide ∪ closure (dg 1).compactSide ∧
        closure (dg 0).compactSide ∩ closure (dg 1).compactSide =
          Ψ '' (closedBall 0 1 ×ˢ {(0 : ℝ)})) ∨
      ((dg 0).compactSide ⊆ (dg 1).compactSide ∧
        closure d.compactSide = closure (interior (closure (dg 1).compactSide) \ closure (dg 0).compactSide) ∧
        closure (dg 1).compactSide = closure d.compactSide ∪ closure (dg 0).compactSide))
    (hD : D '' closedBall 0 1 = closure (df 0).compactSide) :
    ∃ H : EuclideanSpace ℝ (Fin ((m + 1) + 1)) ≃ₘ[ℝ]
        EuclideanSpace ℝ (Fin ((m + 1) + 1)),
      H '' closure (df 1).compactSide = closure d.compactSide ∧ H '' range (f 1) = range e := by
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let M := EuclideanSpace ℝ (Fin ((m + 1) + 1))
  have hb : 0 < b := (ha 0).trans (hab 0)
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hnegσ : -σ = 1 ∨ -σ = -1 := by rcases hσ with rfl | rfl <;> norm_num
  have htrace₀ := EuclideanGeometry.mem_range_flat_cap_iff (Ψ := Ψ) Ψ.injective (χ 0) (hχS 0) (hflat 0) (hgfix 0) (hret 0)
  have htrace₁ := EuclideanGeometry.mem_range_flat_cap_iff (Ψ := Ψ) Ψ.injective (χ 1) (hχS 1) (hflat 1) (hgfix 1) (hret 1)
  simp only [ite_true] at htrace₀
  simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false] at htrace₁
  have hside₀ := (dg 0).toTwoSidedSeparation.closed_positiveSide_in_flat_cap_cylinder_of_disjoint_or_subset
    (dg 1).toTwoSidedSeparation Ψ.toHomeomorph zero_lt_one hR hb hσne htrace₀ htrace₁
    (hrel.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
  have hpcenter : ((0 : E), σ * b / 2) ∈ ball (0 : E) R ×ˢ Ioo (-b) b := by
    refine ⟨mem_ball_self (zero_lt_one.trans hR), ?_⟩
    rcases hσ with rfl | rfl <;> simp only [one_mul, neg_one_mul, mem_Ioo] <;> constructor <;> linarith
  have hposcenter : 0 < σ * (σ * b / 2) := by
    rcases hσ with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;> linarith
  have hconvex : Ψ (0, σ * b / 2) ∈ closure (dg 0).compactSide :=
    (hside₀ _ hpcenter).mpr ⟨by simp, hposcenter.le⟩
  obtain ⟨F, hFA, U, hU, hDU, hFU⟩ := exists_diffeomorph_halfBall_flat_cap m (df 0) (dg 0)
    Ψ (χ 0) D hR (ha 0) (hab 0) hσ (hχS 0) (by simpa only [ite_true] using hcap 0)
    (hflat 0) (hfix 0) (hgfix 0) (by simpa only [ite_true] using hret 0) hconvex hD
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)
  let G := L.symm.toDiffeomorph.trans F
  let V := L.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage L.symm.continuous
  have hDV : closedBall (0 : E) 1 ×ˢ {(0 : ℝ)} ⊆ V := by
    intro p hp
    exact hDU (mem_image_of_mem _ hp)
  have hGV : EqOn G (fun p => Ψ ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2)) V := by
    intro p hp
    have hh := hFU hp
    change F (L.symm p) = _
    simpa only [L, ContinuousLinearEquiv.apply_symm_apply] using hh
  have hGA : G '' {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} = closure (dg 0).compactSide := by
    rw [← hFA]
    change (F ∘ L.symm) '' _ = _
    rw [image_comp]
    congr 1
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      change ‖L.symm p‖ ^ 2 ≤ 1 ∧ 0 ≤ (L (L.symm p)).2
      rw [L.apply_symm_apply]
      have hn := EuclideanSpace.norm_sq_equivProdLast_symm (m + 1) p
      simp only [Real.norm_eq_abs, sq_abs] at hn
      change ‖L.symm p‖ ^ 2 = _ at hn
      rw [hn]
      exact hp
    · intro hz
      refine ⟨L z, ?_, L.symm_apply_apply z⟩
      have hn := EuclideanSpace.norm_sq_equivProdLast (m + 1) z
      simp only [Real.norm_eq_abs, sq_abs] at hn
      change ‖z‖ ^ 2 = ‖(L z).1‖ ^ 2 + (L z).2 ^ 2 at hn
      change ‖z‖ ^ 2 ≤ 1 ∧ 0 ≤ (L z).2 at hz
      rw [hn] at hz
      exact hz
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (E := E) (x := 0) (r := (1 : ℝ))).mpr zero_le_one
  obtain ⟨ρ, hρ, hρ1, R', hR', hR'R, hR'ρ, c, hcs, hct, hcoord, hstrip, _⟩ :=
    exists_flat_cap_corner_chart_in_cylinder (n := m) (dg 1) Ψ ⟨v, hv⟩ hR hb hnegσ htrace₁
  have hcoord' (p : E × ℝ) : (c (Ψ p)).2 = (1 - ‖p.1‖ ^ 2, -σ * p.2) := congrArg Prod.snd (hcoord p)
  have hsource : Ψ '' (sphere (0 : E) 1 ×ˢ {(0 : ℝ)}) ⊆ c.source := by
    rintro z ⟨p, hp, rfl⟩
    rw [hcs]
    refine ⟨p, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
    · exact sphere_subset_ball hR' hp.1
    · have ht : p.2 = 0 := hp.2
      rw [ht]
      exact ⟨neg_neg_of_pos hb, hb⟩
    · have hn := mem_sphere_zero_iff_norm.mp hp.1
      rw [hn]
      linarith
  have hzero : (univ : Set (sphere (0 : E) 1)) ×ˢ {(0 : ℝ × ℝ)} ⊆ c.target := by
    rw [hct]
    intro p hp
    have hh : p.2 = 0 := hp.2
    exact ⟨mem_univ _, hh ▸ ⟨⟨neg_neg_of_pos hρ, hρ⟩, neg_neg_of_pos hb, hb⟩⟩
  have hret₁ : ∀ p ∈ ball (0 : E) R' ×ˢ Ioo (-b) b,
      Ψ p ∈ e '' (S 1)ᶜ ↔ ‖p.1‖ = 1 ∧ 0 < -σ * p.2 := by
    intro p hp
    simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false] using
      hret 1 p ⟨ball_subset_ball hR'R.le hp.1, hp.2⟩
  have hcap₁ : ∀ x ∈ closedBall (0 : E) 1,
      f 1 (χ 1 x) = Ψ (EuclideanGeometry.cylinderCap (-σ * a 1) x) := by
    simpa only [show (1 : Fin 2) ≠ 0 by decide, ite_false] using hcap 1
  have hfinish (H : M ≃ₘ[ℝ] M) (hH : H '' closure (df 1).compactSide = closure d.compactSide) :
      H '' range (f 1) = range e := by
    have hfront (d : SphereSides (range e)) : frontier (closure d.compactSide) = range e := by
      rw [frontier, closure_closure, d.interior_closure_compactSide,
        ← d.isOpen_compactSide.frontier_eq, d.frontier_compactSide]
    have hf : frontier (closure (df 1).compactSide) = range (f 1) := by
      rw [frontier, closure_closure, (df 1).interior_closure_compactSide,
        ← (df 1).isOpen_compactSide.frontier_eq, (df 1).frontier_compactSide]
    have hi : H '' frontier (closure (df 1).compactSide) =
        frontier (H '' closure (df 1).compactSide) := H.toHomeomorph.image_frontier _
    rw [hf, hH, hfront d] at hi
    exact hi
  rcases hrel with hdisj | hnest
  · have hside₁ := (dg 1).toTwoSidedSeparation.closed_positiveSide_in_flat_cap_cylinder_of_disjoint_or_subset
      (dg 0).toTwoSidedSeparation Ψ.toHomeomorph zero_lt_one hR hb (neg_ne_zero.mpr hσne)
      htrace₁ (by
        intro p hp
        change Ψ p ∈ range (g 0) ↔ (‖p.1‖ ≤ 1 ∧ p.2 = 0) ∨ (‖p.1‖ = 1 ∧ 0 < - -σ * p.2)
        simpa only [neg_neg] using htrace₀ p hp) (Or.inl hdisj.1.symm)
    change ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ closure (dg 1).compactSide ↔ ‖p.1‖ ≤ 1 ∧ 0 ≤ -σ * p.2 at hside₁
    have hraw : ∀ q ∈ c.target, c.toOpenPartialHomeomorph.symm q ∈ closure (dg 1).compactSide ↔
        0 ≤ q.2.1 ∧ 0 ≤ q.2.2 := by
      intro q hq
      obtain ⟨p, hp, hqp, hqcoord⟩ := corner_chart_pullback Ψ c.toOpenPartialHomeomorph hcs hcoord' hq
      rw [hqp, hside₁ p ⟨ball_subset_ball hR'R.le hp.1, hp.2⟩, hqcoord]
      apply and_congr_left
      intro _
      constructor <;> intro hh <;> nlinarith [norm_nonneg p.1]
    obtain ⟨k, hPk, hkA, hkK, hkB, hkapply⟩ := exists_halfBall_deletion_chart_of_disjoint_flat_caps
      (m + 1) (by omega) d (dg 0) (dg 1) Ψ G hR hb hσ hS hconvex hdisj.2.2 hdisj.2.1 hGA hV hDV hGV
    have hout (x : M) (hx : x ∉ k.target) : x ∈ closure (dg 1).compactSide ↔ x ∈ closure d.compactSide := by
      have hxA : x ∉ closure (dg 0).compactSide := by
        rw [← hkA]
        rintro ⟨p, hp, rfl⟩
        exact hx (k.map_source (hPk hp))
      rw [hdisj.2.1]
      exact (or_iff_right hxA).symm
    obtain ⟨δ, hδ, hAbs⟩ := Handle.exists_diffeomorph_image_halfBall_rounding Ψ G k
      c.toOpenPartialHomeomorph hσne hPk hkapply hV hDV hGV hsource hcoord' hzero hraw hkK hkB hout
    obtain ⟨ε, hε, hεall⟩ := exists_between (lt_min hδ (lt_min zero_lt_one (lt_min hb hρ)))
    have hεδ := hεall.trans_le (min_le_left _ _)
    have hεrest := hεall.trans_le (min_le_right _ _)
    have hε1 := hεrest.trans_le (min_le_left _ _)
    have hεb := (hεrest.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
    have hερ := (hεrest.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
    obtain ⟨A, hA, _⟩ := hAbs ε ⟨hε, hεδ⟩
    obtain ⟨Φ, hΦ, _⟩ := exists_diffeomorph_flat_cap_rounding_closure (df 1) (dg 1)
      Ψ (χ 1) c.toOpenPartialHomeomorph hR' (ha 1) (hab 1) hε hε1 hεb hερ hnegσ
      (hχS 1) hcap₁ (hflat 1) (hfix 1) (hgfix 1) hret₁ hcs (fun p _ _ => hcoord' p)
      hraw (hstrip ε hερ hεb)
    have himage : (Φ.trans A) '' closure (df 1).compactSide = closure d.compactSide := by
      change (A ∘ Φ) '' _ = _
      rw [image_comp, hΦ, hA]
    exact ⟨Φ.trans A, himage, hfinish _ himage⟩
  · have hside₁ : ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
        Ψ p ∈ closure (dg 1).compactSide ↔ 1 ≤ ‖p.1‖ ∨ -σ * p.2 ≤ 0 := by
      rcases (dg 1).toTwoSidedSeparation.closed_sides_in_flat_cap_cylinder Ψ.toHomeomorph
        zero_lt_one hR hb (neg_ne_zero.mpr hσne) htrace₁ with hh | hh
      · have hpB := closure_mono hnest.1 hconvex
        have hh' := (hh.1 _ hpcenter).mp hpB
        dsimp at hh'
        have ht : -σ * (σ * b / 2) = -(σ * (σ * b / 2)) := neg_mul _ _
        rw [ht] at hh'
        linarith [hh'.2]
      · exact hh.1
    have hraw : ∀ q ∈ c.target, c.toOpenPartialHomeomorph.symm q ∈ closure (dg 1).compactSide ↔
        q.2.1 ≤ 0 ∨ q.2.2 ≤ 0 := by
      intro q hq
      obtain ⟨p, hp, hqp, hqcoord⟩ := corner_chart_pullback Ψ c.toOpenPartialHomeomorph hcs hcoord' hq
      rw [hqp, hside₁ p ⟨ball_subset_ball hR'R.le hp.1, hp.2⟩, hqcoord]
      apply or_congr_left
      constructor <;> intro hh <;> nlinarith [norm_nonneg p.1]
    obtain ⟨k, hPk, hkA, hkK, _, hkapply⟩ := exists_halfBall_attachment_chart_of_nested_flat_caps
      (m + 1) (by omega) d (dg 0) (dg 1) Ψ G hR hb hσ hS htrace₀ hconvex hnest.1
      hshared hnest.2.1 hGA hV hDV hGV
    have hkB : ∀ p ∈ k.source, k p ∈ closure (dg 1).compactSide ↔
        p.2 ≤ 0 ∨ ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 := by
      intro p hp
      have hmA : k p ∈ closure (dg 0).compactSide ↔
          ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2 := by
        rw [← hkA]
        constructor
        · rintro ⟨q, hq, heq⟩
          have hqp : q = p := k.toOpenPartialHomeomorph.injOn (hPk hq) hp heq
          exact hqp ▸ hq
        · intro hh
          exact mem_image_of_mem _ hh
      rw [hnest.2.2, mem_union, hkK p hp, hmA]
      constructor
      · rintro (hh | ⟨hh, _⟩)
        · exact Or.inl hh
        · exact Or.inr hh
      · rintro (hh | hh)
        · exact Or.inl hh
        · exact (le_total p.2 0).elim Or.inl (fun ht => Or.inr ⟨hh, ht⟩)
    have hout (x : M) (hx : x ∉ k.target) : x ∈ closure (dg 1).compactSide ↔ x ∈ closure d.compactSide := by
      have hxA : x ∉ closure (dg 0).compactSide := by
        rw [← hkA]
        rintro ⟨p, hp, rfl⟩
        exact hx (k.map_source (hPk hp))
      rw [hnest.2.2]
      exact or_iff_left hxA
    obtain ⟨δ, hδ, hAbs⟩ := Handle.exists_diffeomorph_image_halfBall_reflex_rounding Ψ G k
      c.toOpenPartialHomeomorph hσne hPk hkapply hV hDV hGV hsource hcoord' hzero hraw hkK hkB hout
      (by rw [(dg 1).interior_closure_compactSide]) (by rw [d.interior_closure_compactSide])
    obtain ⟨ε, hε, hεall⟩ := exists_between (lt_min hδ (lt_min zero_lt_one (lt_min hb hρ)))
    have hεδ := hεall.trans_le (min_le_left _ _)
    have hεrest := hεall.trans_le (min_le_right _ _)
    have hε1 := hεrest.trans_le (min_le_left _ _)
    have hεb := (hεrest.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
    have hερ := (hεrest.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
    have hfull : (univ : Set (sphere (0 : E) 1)) ×ˢ closedBall (0 : ℝ × ℝ) ε ⊆ c.target := by
      rw [hct]
      intro p hp
      have hn := mem_closedBall_zero_iff.mp hp.2
      rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, max_le_iff] at hn
      exact ⟨mem_univ _, (abs_lt.mp (hn.1.trans_lt hερ)), (abs_lt.mp (hn.2.trans_lt hεb))⟩
    obtain ⟨A, hA, _⟩ := hAbs ε ⟨hε, hεδ⟩
    obtain ⟨Φ, hΦ, _⟩ := exists_diffeomorph_flat_cap_reflex_rounding_closure (df 1) (dg 1)
      Ψ (χ 1) c.toOpenPartialHomeomorph hR' (ha 1) (hab 1) hε hε1 hεb hερ hnegσ
      (hχS 1) hcap₁ (hflat 1) (hfix 1) (hgfix 1) hret₁ hcs (fun p _ _ => hcoord' p) hraw hfull
    have himage : (Φ.trans A) '' closure (df 1).compactSide = closure d.compactSide := by
      change (A ∘ Φ) '' _ = _
      rw [image_comp, hΦ, hA]
    exact ⟨Φ.trans A, himage, hfinish _ himage⟩

end DifferentialGeometry.Topology.SphereSeparation
