import DifferentialGeometry.Topology.SphereSeparation.CylinderSides
import DifferentialGeometry.Topology.Handle.HalfBallCylinderCollar
import DifferentialGeometry.Topology.Handle.HalfBallInversion
import DifferentialGeometry.Analysis.InnerProductSpace.EuclideanSplit

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

theorem exists_halfBall_attachment_chart_of_nested_flat_caps
    (m : ℕ) (hm : 1 < m)
    {S S₀ S₁ : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (d : SphereSides S) (d₀ : SphereSides S₀) (d₁ : SphereSides S₁)
    (Ψ F : (EuclideanSpace ℝ (Fin m) × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    {R b σ : ℝ} (hR : 1 < R) (hb : 0 < b) (hσ : σ = 1 ∨ σ = -1)
    (hS : ∀ p ∈ ball (0 : EuclideanSpace ℝ (Fin m)) R ×ˢ Ioo (-b) b,
      Ψ p ∈ S ↔ ‖p.1‖ = 1)
    (hS₀ : ∀ p ∈ ball (0 : EuclideanSpace ℝ (Fin m)) R ×ˢ Ioo (-b) b,
      Ψ p ∈ S₀ ↔ (‖p.1‖ ≤ 1 ∧ p.2 = 0) ∨ (‖p.1‖ = 1 ∧ 0 < σ * p.2))
    (hconvex : Ψ (0, σ * b / 2) ∈ closure d₀.compactSide)
    (hnest : d₀.compactSide ⊆ d₁.compactSide)
    (hshared : S₀ ∩ S₁ = Ψ '' (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 ×ˢ {0}))
    (hK : closure d.compactSide =
      closure (interior (closure d₁.compactSide) \ closure d₀.compactSide))
    (hF : F '' {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} = closure d₀.compactSide)
    {U : Set (EuclideanSpace ℝ (Fin m) × ℝ)} (hU : IsOpen U)
    (hDU : closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 ×ˢ {(0 : ℝ)} ⊆ U)
    (hFU : EqOn F (fun p => Ψ ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2)) U) :
    ∃ c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × ℝ) (𝓡 (m + 1))
        (EuclideanSpace ℝ (Fin m) × ℝ) (EuclideanSpace ℝ (Fin (m + 1))) ∞,
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ c.source ∧
      c '' {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} = closure d₀.compactSide ∧
      (∀ p ∈ c.source, c p ∈ closure d.compactSide ↔ p.2 ≤ 0) ∧
      c '' (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 ×ˢ {(0 : ℝ)}) =
        closure d.compactSide ∩ closure d₀.compactSide ∧
      (∀ p, c p = F (PartialDiffeomorph.halfBallInversion 1 one_ne_zero p)) := by
  let E := EuclideanSpace ℝ (Fin m)
  let M := EuclideanSpace ℝ (Fin (m + 1))
  let P : Set (E × ℝ) := {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2}
  let A := closure d₀.compactSide
  let B := closure d₁.compactSide
  let K := closure d.compactSide
  let D := closedBall (0 : E) 1 ×ˢ {(0 : ℝ)}
  let W := ball (0 : E) R ×ˢ Ioo (-b) b
  let φ : E × ℝ → E × ℝ := fun p => ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2)
  have hφ : Continuous φ := EuclideanGeometry.contDiff_halfBallCylinderMap.continuous.fst.prodMk
    (continuous_const.mul continuous_snd)
  have hKsub : K ⊆ (interior A)ᶜ := by
    change closure d.compactSide ⊆ _
    rw [hK, ← closure_compl]
    exact closure_mono (sdiff_subset_compl _ _)
  have hKmem {x : M} (hx : x ∈ interior B) : x ∈ K ↔ x ∉ interior A := by
    constructor
    · exact fun hh => hKsub hh
    · intro hh
      rw [show K = closure (interior B \ A) from hK]
      have hc : x ∈ closure Aᶜ := by rw [closure_compl]; exact hh
      exact isOpen_interior.inter_closure ⟨hx, hc⟩
  have hcenterW : ((0 : E), σ * b / 2) ∈ W := by
    refine ⟨mem_ball_self (zero_lt_one.trans hR), ?_⟩
    rcases hσ with rfl | rfl <;> simp only [one_mul, neg_one_mul, mem_Ioo] <;>
      constructor <;> linarith
  have hcenterNot : Ψ (0, σ * b / 2) ∉ S₀ := by
    rw [hS₀ _ hcenterW]
    rcases hσ with rfl | rfl <;> simp only [norm_zero, one_mul, neg_one_mul] <;>
      rintro (⟨_, ht⟩ | ⟨hn, _⟩) <;> linarith
  have hcenterA : Ψ (0, σ * b / 2) ∈ interior A := by
    rw [show interior A = d₀.compactSide from d₀.interior_closure_compactSide]
    exact (d₀.closure_compactSide ▸ hconvex).resolve_right hcenterNot
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (show 1 < Module.finrank ℝ E by simpa [E] using hm)
  have hrad : ∀ p ∈ W, Ψ p ∈ K ↔ 1 ≤ ‖p.1‖ := by
    rcases d.radial_sides_of_cylinder_chart Ψ.toHomeomorph hrank hb zero_lt_one hR
        (fun x hx t ht => hS (x, t) ⟨hx, ht⟩) with ⟨_, _, hin⟩ | ⟨_, _, hout⟩
    · have hcK := (hin (0, σ * b / 2) hcenterW).mpr (by simp only [norm_zero]; norm_num)
      exact False.elim (hKsub hcK hcenterA)
    · exact hout
  have hFD : F '' D = Ψ '' D := by
    apply image_congr
    rintro ⟨x, t⟩ hp
    have ht : t = 0 := hp.2
    subst t
    rw [hFU (hDU hp)]
    change Ψ ((EuclideanGeometry.halfBallCylinderMap (x, 0)).1, σ⁻¹ * 0) = Ψ (x, 0)
    rw [EuclideanGeometry.halfBallCylinderMap_apply_zero, mul_zero]
  have hAoutside : A \ Ψ '' D ⊆ interior B := by
    intro x hx
    rw [show interior B = d₁.compactSide from d₁.interior_closure_compactSide]
    have hxB : x ∈ B := closure_mono hnest hx.1
    have hxA : x ∈ d₀.compactSide ∪ S₀ := by rw [← d₀.closure_compactSide]; exact hx.1
    rcases hxA with hx₀ | hx₀
    · exact hnest hx₀
    · have hxB' : x ∈ d₁.compactSide ∪ S₁ := by rw [← d₁.closure_compactSide]; exact hxB
      rcases hxB' with hx₁ | hx₁
      · exact hx₁
      · exact False.elim (hx.2 (hshared.subset ⟨hx₀, hx₁⟩))
  let V := (U ∩ {p : E × ℝ | |p.2| < 1 / 4}) ∩ φ ⁻¹' W
  have hV : IsOpen V := (hU.inter (isOpen_lt continuous_snd.abs continuous_const)).inter
    ((isOpen_ball.prod isOpen_Ioo).preimage hφ)
  have hDV : D ⊆ V := by
    intro p hp
    have ht : p.2 = 0 := hp.2
    refine ⟨⟨hDU hp, by change |p.2| < 1 / 4; rw [ht]; norm_num⟩, ?_⟩
    change φ p ∈ W
    have heq : p = (p.1, 0) := Prod.ext rfl ht
    rw [heq]
    change ((EuclideanGeometry.halfBallCylinderMap (p.1, 0)).1, σ⁻¹ * 0) ∈ W
    rw [EuclideanGeometry.halfBallCylinderMap_apply_zero, mul_zero]
    exact ⟨closedBall_subset_ball hR hp.1, neg_neg_of_pos hb, hb⟩
  have hVK : ∀ p ∈ V, F p ∈ K ↔ 1 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2 := by
    intro p hp
    rw [hFU hp.1.1, hrad (φ p) hp.2]
    have hn : 1 ≤ ‖(EuclideanGeometry.halfBallCylinderMap p).1‖ ↔
        1 ≤ ‖(EuclideanGeometry.halfBallCylinderMap p).1‖ ^ 2 := by
      constructor <;> intro hh <;> nlinarith [norm_nonneg (EuclideanGeometry.halfBallCylinderMap p).1]
    exact hn.trans (EuclideanGeometry.halfBallCylinderMap_norm_sq_ge_iff hp.1.2)
  have hPinterior {p : E × ℝ} (ht : 0 < p.2) :
      p ∈ interior P ↔ ‖p.1‖ ^ 2 + p.2 ^ 2 < 1 := by
    let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) m
    have hnorm (q : E × ℝ) : ‖L.symm q‖ ^ 2 = ‖q.1‖ ^ 2 + q.2 ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_equivProdLast_symm m q
    constructor
    · intro hp
      have hsub : P ⊆ L.symm ⁻¹' closedBall 0 1 := by
        intro q hq
        apply mem_closedBall_zero_iff.mpr
        have := hq.1
        rw [← hnorm] at this
        nlinarith [norm_nonneg (L.symm q)]
      have hh := interior_mono hsub hp
      change p ∈ interior (L.symm.toHomeomorph ⁻¹' closedBall (0 : M) 1) at hh
      rw [← L.symm.toHomeomorph.preimage_interior, interior_closedBall (0 : M) one_ne_zero] at hh
      have hh' := mem_ball_zero_iff.mp hh
      change ‖L.symm p‖ < 1 at hh'
      rw [← hnorm]
      nlinarith [norm_nonneg (L.symm p)]
    · intro hp
      let O : Set (E × ℝ) := {q | ‖q.1‖ ^ 2 + q.2 ^ 2 < 1 ∧ 0 < q.2}
      have hO : IsOpen O := (isOpen_lt ((continuous_fst.norm.pow 2).add (continuous_snd.pow 2))
        continuous_const).inter (isOpen_lt continuous_const continuous_snd)
      have hOP : O ⊆ P := fun _ hq => ⟨hq.1.le, hq.2.le⟩
      exact hO.subset_interior_iff.mpr hOP ⟨hp, ht⟩
  have hFAinterior (p : E × ℝ) : F p ∈ interior A ↔ p ∈ interior P := by
    have hh := F.toHomeomorph.image_interior P
    change F '' interior P = interior (F '' P) at hh
    rw [show F '' P = A from hF] at hh
    rw [← hh]
    exact F.injective.mem_set_image
  let N := V ∪ ({p : E × ℝ | 0 < p.2} ∩ F ⁻¹' interior B)
  have hN : IsOpen N := hV.union ((isOpen_lt continuous_const continuous_snd).inter
    (isOpen_interior.preimage F.continuous))
  have hPN : P ⊆ N := by
    intro p hp
    rcases eq_or_lt_of_le hp.2 with ht | ht
    · apply Or.inl
      apply hDV
      refine ⟨mem_closedBall_zero_iff.mpr ?_, ht.symm⟩
      have := hp.1
      rw [← ht] at this
      nlinarith [norm_nonneg p.1]
    · refine Or.inr ⟨ht, hAoutside ⟨?_, ?_⟩⟩
      · exact hF.subset (mem_image_of_mem F hp)
      · rw [← hFD]
        rintro ⟨q, hq, hqp⟩
        have heq := F.injective hqp
        exact ht.ne' (heq ▸ hq.2)
  have hNK : ∀ p ∈ N, F p ∈ K ↔ 1 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2 := by
    intro p hp
    rcases hp with hp | hp
    · exact hVK p hp
    · rw [hKmem hp.2, hFAinterior p, hPinterior hp.1, not_lt]
  let J := PartialDiffeomorph.halfBallInversion (E := E) 1 one_ne_zero
  let c := J.trans (DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    F.toPartialDiffeomorph N hN)
  have hJimage : J '' P = P := by
    simpa only [one_pow] using
      (PartialDiffeomorph.halfBallInversion_image_halfBall (E := E) zero_lt_one)
  have hcapply (p : E × ℝ) : c p = F (J p) := rfl
  have hPc : P ⊆ c.source := by
    intro p hp
    have hpJ : p ∈ J.source := PartialDiffeomorph.mem_halfBallInversion_source_of_snd_nonneg
      zero_lt_one hp.2
    exact ⟨hpJ, mem_univ _, hPN (hJimage.subset (mem_image_of_mem J hp))⟩
  have hcimage : c '' P = A := by
    calc
      c '' P = F '' (J '' P) := by rw [image_image]; rfl
      _ = F '' P := by rw [hJimage]
      _ = A := hF
  have hcK : ∀ p ∈ c.source, c p ∈ K ↔ p.2 ≤ 0 := by
    intro p hp
    have hpN : J p ∈ N := hp.2.2
    rw [hcapply, hNK (J p) hpN]
    simpa only [one_pow] using
      (PartialDiffeomorph.norm_sq_halfBallInversion_ge_iff zero_lt_one hp.1)
  refine ⟨c, hPc, hcimage, hcK, ?_, hcapply⟩
  apply Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    have hpP : p ∈ P := by
      have hn := mem_closedBall_zero_iff.mp hp.1
      have ht : p.2 = 0 := hp.2
      constructor <;> simp only [ht] <;> nlinarith [norm_nonneg p.1]
    exact ⟨(hcK p (hPc hpP)).mpr (le_of_eq hp.2),
      hcimage.subset (mem_image_of_mem c hpP)⟩
  · rintro x ⟨hxK, hxA⟩
    obtain ⟨p, hp, rfl⟩ := hcimage.symm.subset hxA
    have ht : p.2 = 0 := le_antisymm ((hcK p (hPc hp)).mp hxK) hp.2
    refine ⟨p, ⟨mem_closedBall_zero_iff.mpr ?_, ht⟩, rfl⟩
    have := hp.1
    rw [ht] at this
    nlinarith [norm_nonneg p.1]

theorem exists_halfBall_deletion_chart_of_disjoint_flat_caps
    (m : ℕ) (hm : 1 < m)
    {S S₀ S₁ : Set (EuclideanSpace ℝ (Fin (m + 1)))}
    (d : SphereSides S) (d₀ : SphereSides S₀) (d₁ : SphereSides S₁)
    (Ψ F : (EuclideanSpace ℝ (Fin m) × ℝ) ≃ₘ[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    {R b σ : ℝ} (hR : 1 < R) (hb : 0 < b) (hσ : σ = 1 ∨ σ = -1)
    (hS : ∀ p ∈ ball (0 : EuclideanSpace ℝ (Fin m)) R ×ˢ Ioo (-b) b,
      Ψ p ∈ S ↔ ‖p.1‖ = 1)
    (hconvex : Ψ (0, σ * b / 2) ∈ closure d₀.compactSide)
    (hshared : closure d₀.compactSide ∩ closure d₁.compactSide =
      Ψ '' (closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 ×ˢ {0}))
    (hK : closure d.compactSide = closure d₀.compactSide ∪ closure d₁.compactSide)
    (hF : F '' {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} = closure d₀.compactSide)
    {U : Set (EuclideanSpace ℝ (Fin m) × ℝ)} (hU : IsOpen U)
    (hDU : closedBall (0 : EuclideanSpace ℝ (Fin m)) 1 ×ˢ {(0 : ℝ)} ⊆ U)
    (hFU : EqOn F (fun p => Ψ ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2)) U) :
    ∃ c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin m) × ℝ) (𝓡 (m + 1))
        (EuclideanSpace ℝ (Fin m) × ℝ) (EuclideanSpace ℝ (Fin (m + 1))) ∞,
      {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} ⊆ c.source ∧
      c '' {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} = closure d₀.compactSide ∧
      (∀ p ∈ c.source, c p ∈ closure d.compactSide ↔ 0 ≤ p.2) ∧
      (∀ p ∈ c.source, c p ∈ closure d₁.compactSide ↔
        0 ≤ p.2 ∧ 1 ≤ ‖p.1‖ ^ 2 + p.2 ^ 2) ∧
      (∀ p, c p = F (PartialDiffeomorph.halfBallInversion 1 one_ne_zero p)) := by
  let E := EuclideanSpace ℝ (Fin m)
  let P : Set (E × ℝ) := {p | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2}
  let A := closure d₀.compactSide
  let B := closure d₁.compactSide
  let K := closure d.compactSide
  let D := closedBall (0 : E) 1 ×ˢ {(0 : ℝ)}
  let W := ball (0 : E) R ×ˢ Ioo (-b) b
  let φ : E × ℝ → E × ℝ := fun p => ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2)
  have hφ : Continuous φ := EuclideanGeometry.contDiff_halfBallCylinderMap.continuous.fst.prodMk
    (continuous_const.mul continuous_snd)
  have hcenterW : ((0 : E), σ * b / 2) ∈ W := by
    refine ⟨mem_ball_self (zero_lt_one.trans hR), ?_⟩
    rcases hσ with rfl | rfl <;> simp only [one_mul, neg_one_mul, mem_Ioo] <;>
      constructor <;> linarith
  have hcenterK : Ψ (0, σ * b / 2) ∈ K := by
    rw [show K = A ∪ B from hK]
    exact Or.inl hconvex
  have hrank : 1 < Module.rank ℝ E := by
    rw [← Module.finrank_eq_rank]
    exact_mod_cast (show 1 < Module.finrank ℝ E by simpa [E] using hm)
  have hrad : ∀ p ∈ W, Ψ p ∈ K ↔ ‖p.1‖ ≤ 1 := by
    rcases d.radial_sides_of_cylinder_chart Ψ.toHomeomorph hrank hb zero_lt_one hR
        (fun x hx t ht => hS (x, t) ⟨hx, ht⟩) with ⟨_, _, hin⟩ | ⟨_, _, hout⟩
    · exact hin
    · have hh := (hout (0, σ * b / 2) hcenterW).mp hcenterK
      simp only [norm_zero] at hh
      exact False.elim (by linarith)
  have hFD : F '' D = Ψ '' D := by
    apply image_congr
    rintro ⟨x, t⟩ hp
    have ht : t = 0 := hp.2
    subst t
    rw [hFU (hDU hp)]
    change Ψ ((EuclideanGeometry.halfBallCylinderMap (x, 0)).1, σ⁻¹ * 0) = Ψ (x, 0)
    rw [EuclideanGeometry.halfBallCylinderMap_apply_zero, mul_zero]
  have hFA (p : E × ℝ) : F p ∈ A ↔ p ∈ P := by
    rw [show A = F '' P from hF.symm]
    exact F.injective.mem_set_image
  have hFAB (p : E × ℝ) : F p ∈ A ∩ B ↔ p ∈ D := by
    rw [show A ∩ B = Ψ '' D from hshared, ← hFD]
    exact F.injective.mem_set_image
  let V := (U ∩ {p : E × ℝ | |p.2| < 1 / 4}) ∩ φ ⁻¹' W
  have hV : IsOpen V := (hU.inter (isOpen_lt continuous_snd.abs continuous_const)).inter
    ((isOpen_ball.prod isOpen_Ioo).preimage hφ)
  have hDV : D ⊆ V := by
    intro p hp
    have ht : p.2 = 0 := hp.2
    refine ⟨⟨hDU hp, by change |p.2| < 1 / 4; rw [ht]; norm_num⟩, ?_⟩
    change φ p ∈ W
    have heq : p = (p.1, 0) := Prod.ext rfl ht
    rw [heq]
    change ((EuclideanGeometry.halfBallCylinderMap (p.1, 0)).1, σ⁻¹ * 0) ∈ W
    rw [EuclideanGeometry.halfBallCylinderMap_apply_zero, mul_zero]
    exact ⟨closedBall_subset_ball hR hp.1, neg_neg_of_pos hb, hb⟩
  have hVK : ∀ p ∈ V, F p ∈ K ↔ ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 := by
    intro p hp
    rw [hFU hp.1.1, hrad (φ p) hp.2]
    have hn : ‖(EuclideanGeometry.halfBallCylinderMap p).1‖ ≤ 1 ↔
        ‖(EuclideanGeometry.halfBallCylinderMap p).1‖ ^ 2 ≤ 1 := by
      constructor <;> intro hh <;> nlinarith [norm_nonneg (EuclideanGeometry.halfBallCylinderMap p).1]
    exact hn.trans (EuclideanGeometry.halfBallCylinderMap_norm_sq_le_iff hp.1.2)
  let N := V ∪ ({p : E × ℝ | 0 < p.2} ∩ F ⁻¹' Bᶜ)
  have hN : IsOpen N := hV.union ((isOpen_lt continuous_const continuous_snd).inter
    (isClosed_closure.isOpen_compl.preimage F.continuous))
  have hPN : P ⊆ N := by
    intro p hp
    rcases eq_or_lt_of_le hp.2 with ht | ht
    · apply Or.inl
      apply hDV
      refine ⟨mem_closedBall_zero_iff.mpr ?_, ht.symm⟩
      have := hp.1
      rw [← ht] at this
      nlinarith [norm_nonneg p.1]
    · refine Or.inr ⟨ht, ?_⟩
      intro hh
      exact ht.ne' ((hFAB p).mp ⟨(hFA p).mpr hp, hh⟩).2
  have hNK : ∀ p ∈ N, F p ∈ K ↔ ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 := by
    intro p hp
    rcases hp with hp | hp
    · exact hVK p hp
    · rw [show K = A ∪ B from hK, mem_union, or_iff_left hp.2, hFA]
      exact and_iff_left hp.1.le
  have hNB : ∀ p ∈ N, F p ∈ B ↔ ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ p.2 ≤ 0 := by
    intro p hp
    constructor
    · intro hh
      have hnorm := (hNK p hp).mp (by rw [show K = A ∪ B from hK]; exact Or.inr hh)
      refine ⟨hnorm, ?_⟩
      by_contra ht
      have hpos : 0 < p.2 := lt_of_not_ge ht
      have hzero := ((hFAB p).mp ⟨(hFA p).mpr ⟨hnorm, hpos.le⟩, hh⟩).2
      exact hpos.ne' hzero
    · rintro ⟨hnorm, ht⟩
      by_cases hzero : p.2 = 0
      · apply ((hFAB p).mpr ?_).2
        refine ⟨mem_closedBall_zero_iff.mpr ?_, hzero⟩
        rw [hzero] at hnorm
        nlinarith [norm_nonneg p.1]
      · have hKp := (hNK p hp).mpr hnorm
        rw [show K = A ∪ B from hK] at hKp
        apply hKp.resolve_left
        intro hA
        exact hzero (le_antisymm ht ((hFA p).mp hA).2)
  let J := PartialDiffeomorph.halfBallInversion (E := E) 1 one_ne_zero
  let c := J.trans (DifferentialGeometry.Topology.PartialDiffeomorph.restrict
    F.toPartialDiffeomorph N hN)
  have hJimage : J '' P = P := by
    simpa only [one_pow] using
      (PartialDiffeomorph.halfBallInversion_image_halfBall (E := E) zero_lt_one)
  have hcapply (p : E × ℝ) : c p = F (J p) := rfl
  have hPc : P ⊆ c.source := by
    intro p hp
    exact ⟨PartialDiffeomorph.mem_halfBallInversion_source_of_snd_nonneg zero_lt_one hp.2,
      mem_univ _, hPN (hJimage.subset (mem_image_of_mem J hp))⟩
  have hcimage : c '' P = A := by
    calc
      c '' P = F '' (J '' P) := by rw [image_image]; rfl
      _ = F '' P := by rw [hJimage]
      _ = A := hF
  refine ⟨c, hPc, hcimage, ?_, ?_, hcapply⟩
  · intro p hp
    rw [hcapply, hNK (J p) hp.2.2]
    simpa only [one_pow] using
      (PartialDiffeomorph.norm_sq_halfBallInversion_le_iff zero_lt_one hp.1)
  · intro p hp
    rw [hcapply, hNB (J p) hp.2.2]
    apply Iff.and
    · simpa only [one_pow] using
        (PartialDiffeomorph.norm_sq_halfBallInversion_le_iff zero_lt_one hp.1)
    · simpa only [one_pow] using
        (PartialDiffeomorph.halfBallInversion_snd_nonpos_iff zero_lt_one hp.1)

end DifferentialGeometry.Topology.SphereSeparation
