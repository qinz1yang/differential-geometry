import DifferentialGeometry.Topology.Manifold.OneManifold.PlaneCurveBCF
import DifferentialGeometry.Topology.Manifold.OneManifold.ArcHalfChartBCF

/-!
# Half charts of a curve given by regular functions in a plane chart (lane S-BCF03)

The analytic core of the half charts of the circle-base curve `Γ` of BCF03: let `σ : ℝ² → H` be a
smooth embedding with injective differential onto the piece `Bs₀ ∩ Oσ` (a circle chart of the
whole-fibre layer), `T ⊆ Bs₀`, and `u, w` smooth near `0` with independent differentials at `0`
and `u 0 = w 0 = 0` such that in the chart `T` is `{u = 0, w ≤ 0}` (a corner) or `{u = 0}` (an
interior point) near `0`. Then `T` has a half chart `HalfChart_BCF` (own base, see
`HalfChartComponentsBCF`) at `σ 0`, with chart coordinate `0` (corner) or `> 0` (interior):

* `exists_halfChart_of_plane_corner_BCF`, `exists_halfChart_of_plane_interior_BCF`.

Route: `exists_curve_of_independent_BCF` (the curve `c`), `τ = σ ∘ c` (a smooth embedded arc),
`exists_halfChart_data_corner_BCF` / `…_interior_BCF`, `HalfChart_BCF.ofData_BCF`.
-/

set_option autoImplicit false

open Set Function Filter Topology
open scoped ContDiff

noncomputable section

namespace DifferentialGeometry.Topology

local notation "E2" => EuclideanSpace ℝ (Fin 2)

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The common part: the arc `τ = σ ∘ c` with its relative embedding property and the open set
`O₀` cutting out the piece of `T` described by the plane chart. -/
theorem exists_arc_of_plane_BCF {σ : E2 → H} (hσ : ContDiff ℝ ∞ σ) (hσe : IsEmbedding σ)
    (hσd : ∀ x, Injective (fderiv ℝ σ x)) {T Bs₀ Oσ : Set H} (hOσ : IsOpen Oσ)
    (hrange : range σ = Bs₀ ∩ Oσ) (hTB : T ⊆ Bs₀) {u w : E2 → ℝ} {P : Set E2} (hP : IsOpen P)
    (h0 : (0 : E2) ∈ P) (hu : ContDiffOn ℝ ∞ u P) (hw : ContDiffOn ℝ ∞ w P) (hu0 : u 0 = 0)
    (hw0 : w 0 = 0) (hind : Injective fun v : E2 => (fderiv ℝ u 0 v, fderiv ℝ w 0 v)) :
    ∃ (ε : ℝ) (c : ℝ → E2) (N : Set E2) (O₀ : Set H), 0 < ε ∧ IsOpen N ∧ N ⊆ P ∧
      (0 : E2) ∈ N ∧ IsOpen O₀ ∧ σ 0 ∈ O₀ ∧ c 0 = 0 ∧
      ContDiffOn ℝ ∞ (fun t => σ (c t)) (Ioo (-ε) ε) ∧
      deriv (fun t => σ (c t)) 0 ≠ 0 ∧
      (∀ U : Set ℝ, IsOpen U → U ⊆ Ioo (-ε) ε →
        ∃ G : Set H, IsOpen G ∧ (fun t => σ (c t)) ⁻¹' G ∩ Ioo (-ε) ε = U) ∧
      (∀ s ∈ Ioo (-ε) ε, c s ∈ N ∧ u (c s) = 0 ∧ w (c s) = s) ∧
      (∀ z, z ∈ T ∩ O₀ → ∃ x ∈ N, σ x = z) ∧ (∀ x ∈ N, σ x ∈ O₀) ∧
      (∀ x ∈ N, u x = 0 → w x ∈ Ioo (-ε) ε ∧ c (w x) = x) := by
  obtain ⟨ε, N, c, hε, hN, h0N, hNP, hc, hc0, hprop, hback, hder⟩ :=
    exists_curve_of_independent_BCF hP h0 hu hw hu0 hw0 hind
  obtain ⟨G, hG, hGN⟩ := hσe.isInducing.isOpen_iff.mp hN
  have hJ : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hσat : ∀ x, DifferentiableAt ℝ σ x := fun x => (hσ.differentiable (by simp)) x
  refine ⟨ε, c, N, G ∩ Oσ, hε, hN, hNP, h0N, hG.inter hOσ, ⟨?_, ?_⟩, hc0, ?_, ?_, ?_, hprop, ?_,
    ?_, hback⟩
  · rw [← mem_preimage, hGN]
    exact h0N
  · have : σ 0 ∈ range σ := mem_range_self 0
    rw [hrange] at this
    exact this.2
  · exact hσ.comp_contDiffOn hc
  · have hcd : DifferentiableAt ℝ c 0 := (hc.contDiffAt (isOpen_Ioo.mem_nhds hJ)).differentiableAt
      (by simp)
    have h1 : HasDerivAt (fun t => σ (c t)) (fderiv ℝ σ (c 0) (deriv c 0)) 0 := by
      have := (hσat (c 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcd.hasDerivAt
      exact this
    rw [h1.deriv]
    intro h
    exact hder 0 hJ (hσd (c 0) (by rw [h, map_zero]))
  · intro U hU hUJ
    have h1 : IsOpen (N ∩ (P ∩ w ⁻¹' U)) :=
      hN.inter (hw.continuousOn.isOpen_inter_preimage hP hU)
    obtain ⟨G', hG', hG'eq⟩ := hσe.isInducing.isOpen_iff.mp h1
    refine ⟨G', hG', ?_⟩
    ext t
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨ht, htJ⟩
      have : c t ∈ σ ⁻¹' G' := ht
      rw [hG'eq] at this
      have hw' := (hprop t htJ).2.2
      have := this.2.2
      rw [mem_preimage, hw'] at this
      exact this
    · intro htU
      have htJ := hUJ htU
      refine ⟨?_, htJ⟩
      have : c t ∈ σ ⁻¹' G' := by
        rw [hG'eq]
        refine ⟨(hprop t htJ).1, hNP (hprop t htJ).1, ?_⟩
        rw [mem_preimage, (hprop t htJ).2.2]
        exact htU
      exact this
  · rintro z ⟨hzT, hzG, hzO⟩
    have hz : z ∈ range σ := by
      rw [hrange]
      exact ⟨hTB hzT, hzO⟩
    obtain ⟨x, rfl⟩ := hz
    refine ⟨x, ?_, rfl⟩
    rw [← hGN]
    exact hzG
  · intro x hx
    refine ⟨?_, ?_⟩
    · rw [← mem_preimage, hGN]
      exact hx
    · have : σ x ∈ range σ := mem_range_self x
      rw [hrange] at this
      exact this.2

/-- **A corner of `T` in a plane chart has a half chart** (chart coordinate `0` at `σ 0`). -/
theorem exists_halfChart_of_plane_corner_BCF {σ : E2 → H} (hσ : ContDiff ℝ ∞ σ)
    (hσe : IsEmbedding σ) (hσd : ∀ x, Injective (fderiv ℝ σ x)) {T Bs₀ Oσ : Set H}
    (hOσ : IsOpen Oσ) (hrange : range σ = Bs₀ ∩ Oσ) (hTB : T ⊆ Bs₀) {u w : E2 → ℝ} {P : Set E2}
    (hP : IsOpen P) (h0 : (0 : E2) ∈ P) (hu : ContDiffOn ℝ ∞ u P) (hw : ContDiffOn ℝ ∞ w P)
    (hu0 : u 0 = 0) (hw0 : w 0 = 0)
    (hind : Injective fun v : E2 => (fderiv ℝ u 0 v, fderiv ℝ w 0 v))
    (hZ : ∀ x ∈ P, σ x ∈ T ↔ (u x = 0 ∧ w x ≤ 0)) :
    ∃ (B : Set H) (d : HalfChart_BCF B T), σ 0 ∈ d.O ∧ d.L (σ 0) + d.κ = 0 := by
  obtain ⟨ε, c, N, O₀, hε, hN, hNP, h0N, hO₀, h0O, hc0, hτ, hd, hloc, hprop, hT1, hNO, hback⟩ :=
    exists_arc_of_plane_BCF hσ hσe hσd hOσ hrange hTB hP h0 hu hw hu0 hw0 hind
  have hJ : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hτ0 : σ (c 0) = σ 0 := by rw [hc0]
  have hT : T ∩ O₀ = (fun t => σ (c t)) '' (Ioo (-ε) ε ∩ Iic 0) ∩ O₀ := by
    ext z
    constructor
    · rintro ⟨hzT, hzO⟩
      obtain ⟨x, hxN, rfl⟩ := hT1 z ⟨hzT, hzO⟩
      have hzx := (hZ x (hNP hxN)).mp hzT
      obtain ⟨hwx, hcx⟩ := hback x hxN hzx.1
      refine ⟨⟨w x, ⟨hwx, hzx.2⟩, ?_⟩, hzO⟩
      change σ (c (w x)) = σ x
      rw [hcx]
    · rintro ⟨⟨t, ⟨htJ, ht0⟩, rfl⟩, hzO⟩
      obtain ⟨hcN, hcu, hcw⟩ := hprop t htJ
      refine ⟨?_, hzO⟩
      exact (hZ (c t) (hNP hcN)).mpr ⟨hcu, by rw [hcw]; exact ht0⟩
  obtain ⟨L, κ, π, W, V, O, hW, hV, hVW, hπ, hcoord, hπO, hO, h0O', hTO, hLκ⟩ :=
    exists_halfChart_data_corner_BCF (J := Ioo (-ε) ε) isOpen_Ioo hJ hτ hloc hd hO₀
      (by rw [hτ0]; exact h0O) hT
  refine ⟨T ∪ π '' W, HalfChart_BCF.ofData_BCF L κ π W V O hW hV hVW hπ hcoord hπO hO hTO, ?_, ?_⟩
  · change σ 0 ∈ O
    have : (fun t => σ (c t)) 0 = σ 0 := by simp [hc0]
    rw [← this]
    exact h0O'
  · change L (σ 0) + κ = 0
    have : (fun t => σ (c t)) 0 = σ 0 := by simp [hc0]
    rw [← this]
    exact hLκ

/-- **An interior point of `T` in a plane chart has a half chart** (positive coordinate). -/
theorem exists_halfChart_of_plane_interior_BCF {σ : E2 → H} (hσ : ContDiff ℝ ∞ σ)
    (hσe : IsEmbedding σ) (hσd : ∀ x, Injective (fderiv ℝ σ x)) {T Bs₀ Oσ : Set H}
    (hOσ : IsOpen Oσ) (hrange : range σ = Bs₀ ∩ Oσ) (hTB : T ⊆ Bs₀) {u w : E2 → ℝ} {P : Set E2}
    (hP : IsOpen P) (h0 : (0 : E2) ∈ P) (hu : ContDiffOn ℝ ∞ u P) (hw : ContDiffOn ℝ ∞ w P)
    (hu0 : u 0 = 0) (hw0 : w 0 = 0)
    (hind : Injective fun v : E2 => (fderiv ℝ u 0 v, fderiv ℝ w 0 v))
    (hZ : ∀ x ∈ P, σ x ∈ T ↔ u x = 0) :
    ∃ (B : Set H) (d : HalfChart_BCF B T), σ 0 ∈ d.O ∧ 0 < d.L (σ 0) + d.κ := by
  obtain ⟨ε, c, N, O₀, hε, hN, hNP, h0N, hO₀, h0O, hc0, hτ, hd, hloc, hprop, hT1, hNO, hback⟩ :=
    exists_arc_of_plane_BCF hσ hσe hσd hOσ hrange hTB hP h0 hu hw hu0 hw0 hind
  have hJ : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hτ0 : σ (c 0) = σ 0 := by rw [hc0]
  have hT : T ∩ O₀ = (fun t => σ (c t)) '' Ioo (-ε) ε ∩ O₀ := by
    ext z
    constructor
    · rintro ⟨hzT, hzO⟩
      obtain ⟨x, hxN, rfl⟩ := hT1 z ⟨hzT, hzO⟩
      have hzx := (hZ x (hNP hxN)).mp hzT
      obtain ⟨hwx, hcx⟩ := hback x hxN hzx
      refine ⟨⟨w x, hwx, ?_⟩, hzO⟩
      change σ (c (w x)) = σ x
      rw [hcx]
    · rintro ⟨⟨t, htJ, rfl⟩, hzO⟩
      obtain ⟨hcN, hcu, hcw⟩ := hprop t htJ
      exact ⟨(hZ (c t) (hNP hcN)).mpr hcu, hzO⟩
  obtain ⟨L, κ, π, W, V, O, hW, hV, hVW, hπ, hcoord, hπO, hO, h0O', hTO, hLκ⟩ :=
    exists_halfChart_data_interior_BCF (J := Ioo (-ε) ε) isOpen_Ioo hJ hτ hloc hd hO₀
      (by rw [hτ0]; exact h0O) hT
  refine ⟨T ∪ π '' W, HalfChart_BCF.ofData_BCF L κ π W V O hW hV hVW hπ hcoord hπO hO hTO, ?_, ?_⟩
  · change σ 0 ∈ O
    have : (fun t => σ (c t)) 0 = σ 0 := by simp [hc0]
    rw [← this]
    exact h0O'
  · change 0 < L (σ 0) + κ
    have : (fun t => σ (c t)) 0 = σ 0 := by simp [hc0]
    rw [← this]
    exact hLκ

end DifferentialGeometry.Topology
