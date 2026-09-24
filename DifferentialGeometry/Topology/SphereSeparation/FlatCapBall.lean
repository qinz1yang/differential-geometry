import DifferentialGeometry.Topology.Embedding.FlatCap
import DifferentialGeometry.Topology.SphereSeparation.FlatCapCollar
import DifferentialGeometry.Topology.SphereSeparation.FlatCapCorner
import DifferentialGeometry.Topology.Handle.FlatCapCollarRounding
import DifferentialGeometry.Topology.SphereSeparation.FlatCapRoundedRegions
import DifferentialGeometry.Topology.Handle.HalfBallComparison

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

variable (m : ℕ)

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) = m + 1) := ⟨by simp⟩

theorem exists_diffeomorph_halfBall_flat_cap
    {X : Type*} {e f g : X → EuclideanSpace ℝ (Fin ((m + 1) + 1))}
    (df : SphereSides (range f)) (dg : SphereSides (range g))
    (Ψ : (EuclideanSpace ℝ (Fin (m + 1)) × ℝ) ≃ₘ[ℝ]
      EuclideanSpace ℝ (Fin ((m + 1) + 1)))
    (χ : EuclideanSpace ℝ (Fin (m + 1)) → X)
    (D : EuclideanSpace ℝ (Fin ((m + 1) + 1)) ≃ₘ[ℝ]
      EuclideanSpace ℝ (Fin ((m + 1) + 1)))
    {S : Set X} {R b a σ : ℝ} (hR : 1 < R) (ha : 0 < a) (hab : a < b)
    (hσ : σ = 1 ∨ σ = -1)
    (hχS : χ '' closedBall 0 1 = S)
    (hcap : ∀ x ∈ closedBall 0 1, f (χ x) = Ψ (EuclideanGeometry.cylinderCap (σ * a) x))
    (hflat : ∀ x ∈ closedBall 0 1, g (χ x) = Ψ (x, 0))
    (hfix : EqOn f e Sᶜ) (hgfix : EqOn g e Sᶜ)
    (hret : ∀ p ∈ ball 0 R ×ˢ Ioo (-b) b,
      Ψ p ∈ e '' Sᶜ ↔ ‖p.1‖ = 1 ∧ 0 < σ * p.2)
    (hconvex : Ψ (0, σ * b / 2) ∈ closure dg.compactSide)
    (hD : D '' closedBall 0 1 = closure df.compactSide) :
    ∃ F : EuclideanSpace ℝ (Fin ((m + 1) + 1)) ≃ₘ[ℝ]
        EuclideanSpace ℝ (Fin ((m + 1) + 1)),
      F '' {z | ‖z‖ ^ 2 ≤ 1 ∧
        0 ≤ (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1) z).2} = closure dg.compactSide ∧
      ∃ U, IsOpen U ∧
        (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)).symm ''
          (closedBall 0 1 ×ˢ {(0 : ℝ)}) ⊆ U ∧
        EqOn F (fun z => Ψ
          ((EuclideanGeometry.halfBallCylinderMap
            (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1) z)).1,
            σ⁻¹ * (EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1) z).2)) U := by
  let E := EuclideanSpace ℝ (Fin (m + 1))
  let M := EuclideanSpace ℝ (Fin ((m + 1) + 1))
  let L := EuclideanSpace.equivProdLast (𝕜 := ℝ) (m + 1)
  let A := closure dg.compactSide
  have hb : 0 < b := ha.trans hab
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have htrace := EuclideanGeometry.mem_range_flat_cap_iff Ψ.injective χ hχS hflat hgfix hret
  have hside : ∀ p ∈ ball (0 : E) R ×ˢ Ioo (-b) b,
      Ψ p ∈ A ↔ ‖p.1‖ ≤ 1 ∧ 0 ≤ σ * p.2 := by
    rcases dg.toTwoSidedSeparation.closed_sides_in_flat_cap_cylinder Ψ.toHomeomorph
      zero_lt_one hR hb hσne htrace with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · have hp : ((0 : E), σ * b / 2) ∈ ball (0 : E) R ×ˢ Ioo (-b) b := by
        refine ⟨mem_ball_self (zero_lt_one.trans hR), ?_⟩
        rcases hσ with rfl | rfl <;> simp only [one_mul, neg_one_mul, mem_Ioo] <;>
          constructor <;> linarith
      have hpos : 0 < σ * (σ * b / 2) := by
        rcases hσ with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;> linarith
      have hn := (h (0, σ * b / 2) hp).mp hconvex
      simp only [norm_zero] at hn
      rcases hn with hn | hn <;> linarith
  obtain ⟨c, hKc, hcs, hct, hcp, _, _⟩ :=
    dg.toTwoSidedSeparation.exists_flat_cap_collar Ψ hR hb hσne htrace
  have hcA : c.toOpenPartialHomeomorph.IsImage
      {p : E × ℝ | ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2} A := by
    intro p hp
    have hphysical : ((EuclideanGeometry.halfBallCylinderMap p).1, σ⁻¹ * p.2) ∈
        ball (0 : E) R ×ˢ Ioo (-b) b := by
      obtain ⟨q, hq, hqc⟩ := hct (c.map_source hp)
      exact Ψ.injective (hqc.trans (hcp p)) ▸ hq
    change c p ∈ A ↔ _
    rw [hcp, hside _ hphysical, mul_inv_cancel_left₀ hσne]
    have hn : ‖(EuclideanGeometry.halfBallCylinderMap p).1‖ ≤ 1 ↔
        ‖(EuclideanGeometry.halfBallCylinderMap p).1‖ ^ 2 ≤ 1 := by
      constructor <;> intro h <;> nlinarith [norm_nonneg (EuclideanGeometry.halfBallCylinderMap p).1]
    rw [hn]
    exact EuclideanGeometry.halfBallCylinderMap_mem_cylinder_iff (hcs hp)
  obtain ⟨v₀, hv₀⟩ := NormedSpace.sphere_nonempty (E := E) (x := 0) (r := 1) |>.mpr zero_le_one
  let v : sphere (0 : E) 1 := ⟨v₀, hv₀⟩
  obtain ⟨ρ, hρ, _, R', hR', hRR', _, k, hks, _, hkcoord, hkstrip, _⟩ :=
    exists_flat_cap_corner_chart_in_cylinder (n := m) dg Ψ v hR hb hσ htrace
  have hraw : ∀ q ∈ k.target,
      k.toOpenPartialHomeomorph.symm q ∈ A ↔ 0 ≤ q.2.1 ∧ 0 ≤ q.2.2 := by
    intro q hq
    have hs := k.toOpenPartialHomeomorph.map_target hq
    change k.toOpenPartialHomeomorph.symm q ∈ k.source at hs
    rw [hks] at hs
    obtain ⟨p, hp, hpq⟩ := hs
    have hqcoord : q.2 = (1 - ‖p.1‖ ^ 2, σ * p.2) := by
      have hcoord := congrArg Prod.snd (hkcoord p)
      change (k.toOpenPartialHomeomorph (Ψ p)).2 = _ at hcoord
      rwa [hpq, k.toOpenPartialHomeomorph.right_inv hq] at hcoord
    rw [← hpq, hside p ⟨ball_subset_ball hRR'.le hp.1.1, hp.1.2⟩, hqcoord]
    apply and_congr_left
    intro _
    constructor <;> intro h <;> nlinarith [norm_nonneg p.1]
  have hseam : Ψ '' (sphere (0 : E) 1 ×ˢ {(0 : ℝ)}) ⊆ k.source := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    have ht0 : t = 0 := ht
    subst t
    rw [hks]
    refine ⟨(x, 0), ⟨⟨closedBall_subset_ball hR' (sphere_subset_closedBall hx),
      by exact ⟨neg_neg_of_pos hb, hb⟩⟩, ?_⟩, rfl⟩
    have hxnorm : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
    rw [hxnorm, one_pow]
    linarith
  let δ := min (1 : ℝ) (min b ρ)
  have hδ : 0 < δ := lt_min zero_lt_one (lt_min hb hρ)
  obtain ⟨ε, hε, hεδ, hεsmall, hbox, _, hround⟩ :=
    Handle.exists_flat_cap_collar_rounding_eq Ψ v c k hσne hδ hKc hcp hseam hkcoord hcA hraw
  have hε1 : ε < 1 := hεδ.trans_le (min_le_left _ _)
  have hεb : ε < b := hεδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hερ : ε < ρ := hεδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hstripe : {q : sphere (0 : E) 1 × (ℝ × ℝ) |
      0 ≤ q.2.1 ∧ 0 ≤ q.2.2 ∧ q.2.1 + q.2.2 ≤ ε} ⊆ k.target := hkstrip ε hερ hεb
  obtain ⟨Φ, hΦ, _⟩ := exists_diffeomorph_flat_cap_rounding_closure df dg Ψ χ
    k.toOpenPartialHomeomorph hR' ha hab hε hε1 hεb hερ hσ hχS hcap hflat hfix hgfix
    (fun p hp => hret p ⟨ball_subset_ball hRR'.le hp.1, hp.2⟩) hks
    (fun p _ _ => congrArg Prod.snd (hkcoord p)) hraw hstripe
  let C := L.toDiffeomorph.toPartialDiffeomorph.trans c
  let k₀ := OpenPartialHomeomorph.halfBallCorner 1 v
  let k₁ := (C.symm.toOpenPartialHomeomorph.trans L.toHomeomorph.toOpenPartialHomeomorph).trans k₀
  have hk₁ : k₁ = c.symm.toOpenPartialHomeomorph.trans k₀ := by
    apply OpenPartialHomeomorph.ext
    · intro x
      change k₀ (L (L.symm (c.symm x))) = k₀ (c.symm x)
      rw [L.apply_symm_apply]
    · intro q
      change c (L (L.symm (k₀.symm q))) = c (k₀.symm q)
      rw [L.apply_symm_apply]
    · ext x
      change (((x ∈ c.target ∧ True) ∧ True) ∧ L (L.symm (c.symm x)) ∈ k₀.source) ↔
        (x ∈ c.target ∧ c.symm x ∈ k₀.source)
      rw [L.apply_symm_apply]
      tauto
  have hCA : C.toOpenPartialHomeomorph.IsImage
      {z : M | ‖z‖ ^ 2 ≤ 1 ∧ 0 ≤ (L z).2} A := by
    intro z hz
    change c (L z) ∈ A ↔ _
    have hh := hcA hz.2
    change c (L z) ∈ A ↔ ‖(L z).1‖ ^ 2 + (L z).2 ^ 2 ≤ 1 ∧ 0 ≤ (L z).2 at hh
    rw [hh]
    change (_ ∧ _) ↔ ‖z‖ ^ 2 ≤ 1 ∧ 0 ≤ (L z).2
    rw [EuclideanSpace.norm_sq_equivProdLast (m + 1) z]
    simp only [Real.norm_eq_abs, sq_abs]
    rfl
  have hKC : L.symm '' (closedBall (0 : E) 1 ×ˢ {(0 : ℝ)}) ⊆ C.source := by
    rintro _ ⟨p, hp, rfl⟩
    change True ∧ L (L.symm p) ∈ c.source
    exact ⟨trivial, by rw [L.apply_symm_apply]; exact hKc hp⟩
  have hstrip : (univ : Set (sphere (0 : E) 1)) ×ˢ closedBall (0 : ℝ × ℝ) ε ⊆ k₁.target := by
    rw [hk₁]
    intro q hq
    apply hbox
    have hh := mem_closedBall_zero_iff.mp hq.2
    rwa [Prod.norm_def, max_le_iff, Real.norm_eq_abs, Real.norm_eq_abs] at hh
  have hroundD : (D.trans Φ) '' closedBall 0 1 = k₁.smoothAbsQuadrantSet A ε := by
    calc
      (D.trans Φ) '' closedBall 0 1 = Φ '' (D '' closedBall 0 1) :=
        (image_image (Φ : M → M) (D : M → M) (closedBall 0 1)).symm
      _ = k₁.smoothAbsQuadrantSet A ε := by
        rw [hD, hΦ, (hround ε hε le_rfl).1, hk₁]
  obtain ⟨F, hFA, U, hU, hKU, _, hFC⟩ :=
    C.exists_diffeomorph_halfBall_comparison m (D.trans Φ) v hε
      (hεsmall.trans (by norm_num)) hCA hKC hstrip hroundD
  refine ⟨F, hFA, U, hU, hKU, ?_⟩
  intro z hz
  exact (hFC hz).trans (hcp (L z))

end DifferentialGeometry.Topology.SphereSeparation
