import DifferentialGeometry.Topology.SphereSeparation.LocalSides
import DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation
import DifferentialGeometry.Topology.ClosedBall.ClosedAnnulus

open Set Metric TopologicalSpace

namespace DifferentialGeometry.Topology.SphereSeparation.SphereSides

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

theorem radial_sides_of_cylinder_chart {S : Set X} (d : SphereSides S)
    (Ψ : (E × ℝ) ≃ₜ X) (hrank : 1 < Module.rank ℝ E) {ε r R : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hR : r < R)
    (hS : ∀ x ∈ ball (0 : E) R, ∀ t ∈ Ioo (-ε) ε,
      Ψ (x, t) ∈ S ↔ ‖x‖ = r) :
    ((∀ p ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε, Ψ p ∈ d.compactSide ↔ ‖p.1‖ < r) ∧
      (∀ p ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε, Ψ p ∈ d.endSide ↔ r < ‖p.1‖) ∧
      (∀ p ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε,
        Ψ p ∈ closure d.compactSide ↔ ‖p.1‖ ≤ r)) ∨
    ((∀ p ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε, Ψ p ∈ d.endSide ↔ ‖p.1‖ < r) ∧
      (∀ p ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε, Ψ p ∈ d.compactSide ↔ r < ‖p.1‖) ∧
      (∀ p ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε,
        Ψ p ∈ closure d.compactSide ↔ r ≤ ‖p.1‖)) := by
  let U : Set X := Ψ '' (ball (0 : E) r ×ˢ Ioo (-ε) ε)
  let V : Set X := Ψ '' (((norm : E → ℝ) ⁻¹' Ioo r R) ×ˢ Ioo (-ε) ε)
  let O : Set X := Ψ '' (ball (0 : E) R ×ˢ Ioo (-ε) ε)
  have htime : -ε < ε := by linarith
  have hU : IsConnected U :=
    ((convex_ball (0 : E) r).isConnected ⟨0, mem_ball_self hr⟩).prod
      (isConnected_Ioo htime) |>.image Ψ Ψ.continuous.continuousOn
  have hannulus : IsConnected ((norm : E → ℝ) ⁻¹' Ioo r R) :=
    DifferentialGeometry.Analysis.isConnected_preimage_norm hrank (isConnected_Ioo hR)
      (fun _ hx => hr.le.trans hx.1.le)
  have hV : IsConnected V :=
    (hannulus.prod (isConnected_Ioo htime)).image Ψ Ψ.continuous.continuousOn
  have hUS : U ⊆ Sᶜ := by
    rintro z ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ hs
    have hxnorm : ‖x‖ < r := mem_ball_zero_iff.mp hx
    have hxR : x ∈ ball 0 R := ball_subset_ball hR.le hx
    exact hxnorm.ne ((hS x hxR t ht).mp hs)
  have hVS : V ⊆ Sᶜ := by
    rintro z ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩ hs
    have hxR : x ∈ ball 0 R := mem_ball_zero_iff.mpr hx.2
    exact hx.1.ne' ((hS x hxR t ht).mp hs)
  have hO : IsOpen O := Ψ.isOpenMap _ (isOpen_ball.prod isOpen_Ioo)
  have hSO : (S ∩ O).Nonempty := by
    obtain ⟨x, hx⟩ := (isConnected_sphere hrank (0 : E) hr.le).nonempty
    have hxn : ‖x‖ = r := mem_sphere_zero_iff_norm.mp hx
    have hxR : x ∈ ball 0 R := mem_ball_zero_iff.mpr (hxn ▸ hR)
    have ht : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    exact ⟨Ψ (x, 0), (hS x hxR 0 ht).mpr hxn, ⟨(x, 0), ⟨hxR, ht⟩, rfl⟩⟩
  have hcover : O ⊆ (U ∪ S) ∪ V := by
    rintro z ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    rcases lt_trichotomy ‖x‖ r with hn | hn | hn
    · exact Or.inl (Or.inl ⟨(x, t), ⟨mem_ball_zero_iff.mpr hn, ht⟩, rfl⟩)
    · exact Or.inl (Or.inr ((hS x hx t ht).mpr hn))
    · exact Or.inr ⟨(x, t), ⟨⟨hn, mem_ball_zero_iff.mp hx⟩, ht⟩, rfl⟩
  have hiff {A B : Set X} (hA : U ⊆ A) (hB : V ⊆ B)
      (hAB : Disjoint A B) (hAS : A ⊆ Sᶜ) (hBS : B ⊆ Sᶜ) :
      (∀ p ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε, Ψ p ∈ A ↔ ‖p.1‖ < r) ∧
        (∀ p ∈ ball (0 : E) R ×ˢ Ioo (-ε) ε, Ψ p ∈ B ↔ r < ‖p.1‖) := by
    constructor
    · rintro ⟨x, t⟩ ⟨hx, ht⟩
      constructor
      · intro hxa
        rcases lt_trichotomy ‖x‖ r with hn | hn | hn
        · exact hn
        · exact False.elim (hAS hxa ((hS x hx t ht).mpr hn))
        · exact False.elim (hAB.le_bot ⟨hxa,
            hB ⟨(x, t), ⟨⟨hn, mem_ball_zero_iff.mp hx⟩, ht⟩, rfl⟩⟩)
      · intro hn
        exact hA ⟨(x, t), ⟨mem_ball_zero_iff.mpr hn, ht⟩, rfl⟩
    · rintro ⟨x, t⟩ ⟨hx, ht⟩
      constructor
      · intro hxb
        rcases lt_trichotomy ‖x‖ r with hn | hn | hn
        · exact False.elim (hAB.le_bot
            ⟨hA ⟨(x, t), ⟨mem_ball_zero_iff.mpr hn, ht⟩, rfl⟩, hxb⟩)
        · exact False.elim (hBS hxb ((hS x hx t ht).mpr hn))
        · exact hn
      · intro hn
        exact hB ⟨(x, t), ⟨⟨hn, mem_ball_zero_iff.mp hx⟩, ht⟩, rfl⟩
  rcases d.neighborhood_halves_opposite_of_inter_nonempty hU hV hUS hVS hO hSO hcover with
    ⟨⟨hUC, hVE⟩, _⟩ | ⟨⟨hUE, hVC⟩, _⟩
  · obtain ⟨hC, hE⟩ := hiff hUC hVE d.disjoint d.compactSide_subset_compl d.endSide_subset_compl
    refine Or.inl ⟨hC, hE, ?_⟩
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    rw [d.closure_compactSide, mem_union, hC (x, t) ⟨hx, ht⟩, hS x hx t ht]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      exact lt_or_eq_of_le h
  · obtain ⟨hE, hC⟩ := hiff hUE hVC d.disjoint.symm d.endSide_subset_compl d.compactSide_subset_compl
    refine Or.inr ⟨hE, hC, ?_⟩
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    rw [d.closure_compactSide, mem_union, hC (x, t) ⟨hx, ht⟩, hS x hx t ht]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      rcases lt_or_eq_of_le h with h | h
      · exact Or.inl h
      · exact Or.inr h.symm

end DifferentialGeometry.Topology.SphereSeparation.SphereSides

namespace DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation

theorem sides_of_cylinder {B X : Type*} [TopologicalSpace B] [ConnectedSpace B]
    [TopologicalSpace X] {S : Set X} (d : TwoSidedSeparation S)
    {ε : ℝ} (hε : 0 < ε) (V : Opens X)
    (C : (B × (⟨Ioo (-ε) ε, isOpen_Ioo⟩ : Opens ℝ)) ≃ₜ V)
    (hzero : ∀ p, (C p : X) ∈ S ↔ p.2.val = 0) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      (∀ p, (C p : X) ∈ d.positiveSide ↔ σ * p.2.val < 0) ∧
      (∀ p, (C p : X) ∈ d.negativeSide ↔ 0 < σ * p.2.val) ∧
      (∀ p, (C p : X) ∈ closure d.positiveSide ↔ σ * p.2.val ≤ 0) ∧
      (∀ p, (C p : X) ∈ closure d.negativeSide ↔ 0 ≤ σ * p.2.val) := by
  let T : Opens ℝ := ⟨Ioo (-ε) ε, isOpen_Ioo⟩
  let f : B × T → X := fun p => C p
  have hf : Continuous f := continuous_subtype_val.comp C.continuous
  let A : Set X := f '' (univ ×ˢ {t : T | t.val < 0})
  let D : Set X := f '' (univ ×ˢ {t : T | 0 < t.val})
  have hnegative : IsConnected {t : T | t.val < 0} := by
    refine ⟨⟨⟨-ε / 2, by constructor <;> linarith⟩, by dsimp; linarith⟩, ?_⟩
    apply (Topology.IsInducing.subtypeVal :
      _root_.Topology.IsInducing (Subtype.val : T → ℝ)).isPreconnected_image.mp
    have himage : Subtype.val '' {t : T | t.val < 0} = Ioo (-ε) 0 := by
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u.property.1, hu⟩
      · intro ht
        exact ⟨⟨t, ht.1, ht.2.trans hε⟩, ht.2, rfl⟩
    exact himage.symm ▸ isPreconnected_Ioo
  have hpositive : IsConnected {t : T | 0 < t.val} := by
    refine ⟨⟨⟨ε / 2, by constructor <;> linarith⟩, by dsimp; linarith⟩, ?_⟩
    apply (Topology.IsInducing.subtypeVal :
      _root_.Topology.IsInducing (Subtype.val : T → ℝ)).isPreconnected_image.mp
    have himage : Subtype.val '' {t : T | 0 < t.val} = Ioo 0 ε := by
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨hu, u.property.2⟩
      · intro ht
        exact ⟨⟨t, (by linarith [ht.1]), ht.2⟩, ht.1, rfl⟩
    exact himage.symm ▸ isPreconnected_Ioo
  have hA : IsConnected A := (isConnected_univ.prod hnegative).image f hf.continuousOn
  have hD : IsConnected D := (isConnected_univ.prod hpositive).image f hf.continuousOn
  have hAS : A ⊆ Sᶜ := by
    rintro x ⟨p, hp, rfl⟩ hx
    exact hp.2.ne ((hzero p).mp hx)
  have hDS : D ⊆ Sᶜ := by
    rintro x ⟨p, hp, rfl⟩ hx
    exact hp.2.ne' ((hzero p).mp hx)
  have hSne : (S ∩ (V : Set X)).Nonempty := by
    obtain ⟨b⟩ := (inferInstance : Nonempty B)
    let t : T := ⟨0, by constructor <;> linarith⟩
    exact ⟨f (b, t), (hzero (b, t)).mpr rfl, (C (b, t)).property⟩
  have hcover : (V : Set X) ⊆ (A ∪ S) ∪ D := by
    intro x hx
    obtain ⟨p, hp⟩ := C.surjective ⟨x, hx⟩
    have hp' : f p = x := congrArg Subtype.val hp
    rw [← hp']
    rcases lt_trichotomy p.2.val 0 with ht | ht | ht
    · exact Or.inl (Or.inl ⟨p, ⟨mem_univ _, ht⟩, rfl⟩)
    · exact Or.inl (Or.inr ((hzero p).mpr ht))
    · exact Or.inr ⟨p, ⟨mem_univ _, ht⟩, rfl⟩
  have hiff {P Q : Set X} (hP : A ⊆ P) (hQ : D ⊆ Q)
      (hPQ : Disjoint P Q) (hPS : P ⊆ Sᶜ) (hQS : Q ⊆ Sᶜ) :
      (∀ p, f p ∈ P ↔ p.2.val < 0) ∧ (∀ p, f p ∈ Q ↔ 0 < p.2.val) := by
    constructor
    · intro p
      constructor
      · intro hp
        rcases lt_trichotomy p.2.val 0 with ht | ht | ht
        · exact ht
        · exact False.elim (hPS hp ((hzero p).mpr ht))
        · exact False.elim (hPQ.le_bot ⟨hp, hQ ⟨p, ⟨mem_univ _, ht⟩, rfl⟩⟩)
      · intro ht
        exact hP ⟨p, ⟨mem_univ _, ht⟩, rfl⟩
    · intro p
      constructor
      · intro hp
        rcases lt_trichotomy p.2.val 0 with ht | ht | ht
        · exact False.elim (hPQ.le_bot ⟨hP ⟨p, ⟨mem_univ _, ht⟩, rfl⟩, hp⟩)
        · exact False.elim (hQS hp ((hzero p).mpr ht))
        · exact ht
      · intro ht
        exact hQ ⟨p, ⟨mem_univ _, ht⟩, rfl⟩
  have hclosed (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
      (hP : ∀ p, f p ∈ d.positiveSide ↔ σ * p.2.val < 0)
      (hQ : ∀ p, f p ∈ d.negativeSide ↔ 0 < σ * p.2.val) :
      (∀ p, f p ∈ closure d.positiveSide ↔ σ * p.2.val ≤ 0) ∧
        (∀ p, f p ∈ closure d.negativeSide ↔ 0 ≤ σ * p.2.val) := by
    have hn : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    constructor
    · intro p
      rw [closure_eq_self_union_frontier, d.frontier_positiveSide, mem_union, hP, hzero]
      constructor
      · rintro (h | h)
        · exact h.le
        · simp [h]
      · intro h
        rcases lt_or_eq_of_le h with h | h
        · exact Or.inl h
        · exact Or.inr ((mul_eq_zero.mp h).resolve_left hn)
    · intro p
      rw [closure_eq_self_union_frontier, d.frontier_negativeSide, mem_union, hQ, hzero]
      constructor
      · rintro (h | h)
        · exact h.le
        · simp [h]
      · intro h
        rcases lt_or_eq_of_le h with h | h
        · exact Or.inl h
        · exact Or.inr ((mul_eq_zero.mp h.symm).resolve_left hn)
  rcases d.neighborhood_halves_opposite_of_inter_nonempty hA hD hAS hDS V.isOpen hSne hcover with
    ⟨⟨hAP, hDQ⟩, _⟩ | ⟨⟨hAQ, hDP⟩, _⟩
  · obtain ⟨hP, hQ⟩ := hiff hAP hDQ d.disjoint d.positiveSide_subset_compl d.negativeSide_subset_compl
    have hP' : ∀ p, f p ∈ d.positiveSide ↔ 1 * p.2.val < 0 := by simpa only [one_mul] using hP
    have hQ' : ∀ p, f p ∈ d.negativeSide ↔ 0 < 1 * p.2.val := by simpa only [one_mul] using hQ
    exact ⟨1, Or.inl rfl, hP', hQ', hclosed 1 (Or.inl rfl) hP' hQ'⟩
  · obtain ⟨hQ, hP⟩ := hiff hAQ hDP d.disjoint.symm d.negativeSide_subset_compl d.positiveSide_subset_compl
    have hP' : ∀ p, f p ∈ d.positiveSide ↔ -1 * p.2.val < 0 := by simpa using hP
    have hQ' : ∀ p, f p ∈ d.negativeSide ↔ 0 < -1 * p.2.val := by simpa using hQ
    exact ⟨-1, Or.inr rfl, hP', hQ', hclosed (-1) (Or.inr rfl) hP' hQ'⟩

end DifferentialGeometry.Topology.SphereSeparation.TwoSidedSeparation
