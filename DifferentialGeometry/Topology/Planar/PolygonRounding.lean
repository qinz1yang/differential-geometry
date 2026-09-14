import DifferentialGeometry.Analysis.Calculus.SmoothMax
import DifferentialGeometry.External.Schoenflies.Plane
import DifferentialGeometry.External.ClassificationOfSurfaces.Moise.LineSubdivision
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.Linarith
import DifferentialGeometry.External.Schoenflies.PrePolygonSep
import DifferentialGeometry.External.Schoenflies.PrePolygonArc
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import DifferentialGeometry.Topology.Planar.PolygonVertexCharts

section
open Set Metric
open scoped ContDiff Topology

namespace Schoenflies

open LeanEval.Topology.ClassificationOfSurfaces.Moise

private theorem norm_le_three_mul_of_corner_strip {ε : ℝ} (hε : 0 < ε)
    {p : Plane} (hx : |p 0| ≤ ε) (hy : 0 ≤ p 1) (hyε : p 1 ≤ 2 * ε) :
    ‖p‖ ≤ 3 * ε := by
  have hnorm : ‖p‖ ^ 2 = (p 0) ^ 2 + (p 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
  obtain ⟨hx₁, hx₂⟩ := abs_le.mp hx
  have hxx := mul_nonneg (sub_nonneg.mpr hx₂) (by linarith : 0 ≤ ε + p 0)
  have hyy := mul_nonneg (sub_nonneg.mpr hyε)
    (by linarith : 0 ≤ 2 * ε + p 1)
  apply (sq_le_sq₀ (norm_nonneg p) (by positivity : 0 ≤ 3 * ε)).mp
  nlinarith

private theorem smooth_corner_signs_eq_outside_ball {ε d σ : ℝ} (hε : 0 < ε)
    (hd : d = 0 ∨ d = 1) (hσ : σ = -1 ∨ σ = 1) {p : Plane}
    (hp : 3 * ε < ‖p‖) :
    (0 ≤ σ * (p 1 - d * Real.smoothMax ε (p 0) 0) ↔
      0 ≤ σ * (p 1 - d * max (p 0) 0)) ∧
    (0 < σ * (p 1 - d * Real.smoothMax ε (p 0) 0) ↔
      0 < σ * (p 1 - d * max (p 0) 0)) ∧
    (p 1 = d * Real.smoothMax ε (p 0) 0 ↔ p 1 = d * max (p 0) 0) := by
  rcases hd with rfl | rfl
  · simp only [zero_mul, iff_self, and_self]
  by_cases hx : ε ≤ |p 0|
  · rw [Real.smoothMax.eq_max_of_le (x := p 0) (y := 0) hε
      (by simpa only [sub_zero] using hx)]
    exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
  have hxε : |p 0| ≤ ε := (lt_of_not_ge hx).le
  have hmax₀ : 0 ≤ max (p 0) 0 := le_max_right _ _
  have hmaxε : max (p 0) 0 ≤ ε := max_le (abs_le.mp hxε).2 hε.le
  have hμ₀ : 0 ≤ Real.smoothMax ε (p 0) 0 :=
    hmax₀.trans (Real.smoothMax.max_le hε _ _)
  have hμε : Real.smoothMax ε (p 0) 0 ≤ 2 * ε := by
    linarith [Real.smoothMax.le_max_add hε (p 0) 0]
  have hy : p 1 < 0 ∨ 2 * ε < p 1 := by
    by_contra h
    push Not at h
    exact (not_le_of_gt hp) (norm_le_three_mul_of_corner_strip hε hxε h.1 h.2)
  rcases hy with hy | hy <;> rcases hσ with rfl | rfl
  all_goals
    simp only [one_mul, neg_one_mul]
    refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro h <;> linarith

private theorem affine_smooth_corner_regular
    (e : Plane ≃ᵃ[ℝ] Plane) (ε d σ : ℝ) (hσ : σ ≠ 0) :
    ContDiff ℝ ∞ (fun p => σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)) ∧
      ∀ p, fderiv ℝ (fun q => σ * ((e q) 1 - d * Real.smoothMax ε ((e q) 0) 0)) p ≠ 0 := by
  let f := cartesianX.comp e.toAffineMap
  let g := cartesianY.comp e.toAffineMap
  have hf : ContDiff ℝ ∞ f :=
    (⟨f, f.continuous_of_finiteDimensional⟩ : Plane →ᴬ[ℝ] ℝ).contDiff
  have hg : ContDiff ℝ ∞ g :=
    (⟨g, g.continuous_of_finiteDimensional⟩ : Plane →ᴬ[ℝ] ℝ).contDiff
  have hH : ContDiff ℝ ∞ (fun p => σ * (g p - d * Real.smoothMax ε (f p) 0)) :=
    contDiff_const.mul (hg.sub (contDiff_const.mul
      ((Real.smoothMax.contDiff ε).comp (hf.prodMk contDiff_const))))
  refine ⟨hH, fun p => ?_⟩
  let w := e.linear.symm (Plane.mk 0 1)
  have hfw : f.linear w = 0 := by
    change (e.linear (e.linear.symm (Plane.mk 0 1))) 0 = 0
    rw [e.linear.apply_symm_apply]
    rfl
  have hgw : g.linear w = 1 := by
    change (e.linear (e.linear.symm (Plane.mk 0 1))) 1 = 1
    rw [e.linear.apply_symm_apply]
    rfl
  have heq : (fun t : ℝ =>
      σ * (g (p + t • w) - d * Real.smoothMax ε (f (p + t • w)) 0)) =
      fun t => σ * (g p - d * Real.smoothMax ε (f p) 0) + t * σ := by
    funext t
    rw [add_comm p (t • w)]
    change σ * (g (t • w +ᵥ p) - d * Real.smoothMax ε (f (t • w +ᵥ p)) 0) = _
    rw [g.map_vadd, f.map_vadd, map_smul, map_smul, hgw, hfw]
    change σ * ((t * 1 + g p) - d * Real.smoothMax ε (t * 0 + f p) 0) = _
    simp only [mul_zero, zero_add, mul_one]
    ring
  have hline : HasLineDerivAt ℝ
      (fun q => σ * (g q - d * Real.smoothMax ε (f q) 0)) σ p w := by
    change HasDerivAt _ σ 0
    rw [heq]
    exact (hasDerivAt_mul_const σ).const_add
        (σ * (g p - d * Real.smoothMax ε (f p) 0))
  have hd := ((hH.differentiable (by simp)).differentiableAt (x := p)).hasFDerivAt
    |>.hasLineDerivAt w |>.unique hline
  intro hz
  change fderiv ℝ (fun q => σ * (g q - d * Real.smoothMax ε (f q) 0)) p = 0 at hz
  rw [hz, zero_apply] at hd
  exact hσ hd.symm

private theorem compact_region_replace_on_open
    {X : Type*} [TopologicalSpace X]
    {D N K R : Set X} (hD : IsCompact D) (hN : IsOpen N)
    (hK : IsCompact K) (hR : IsClosed R) (hNK : N ⊆ K)
    (heq : ∀ p ∈ K \ N, p ∈ R ↔ p ∈ D) :
    IsCompact ((D \ N) ∪ (K ∩ R)) ∧
      (∀ p ∈ N, p ∈ (D \ N) ∪ (K ∩ R) ↔ p ∈ R) ∧
      (∀ p ∉ N, p ∈ (D \ N) ∪ (K ∩ R) ↔ p ∈ D) := by
  refine ⟨(hD.diff hN).union (hK.inter_right hR), ?_, ?_⟩
  · intro p hp
    constructor
    · rintro (⟨_, hn⟩ | ⟨_, hr⟩)
      · exact False.elim (hn hp)
      · exact hr
    · intro hr
      exact Or.inr ⟨hNK hp, hr⟩
  · intro p hp
    constructor
    · rintro (⟨hd, _⟩ | ⟨hk, hr⟩)
      · exact hd
      · exact (heq p ⟨hk, hp⟩).mp hr
    · intro hd
      exact Or.inl ⟨hd, hp⟩

private theorem affine_preimage_isCompact (e : Plane ≃ᵃ[ℝ] Plane)
    {K : Set Plane} (hK : IsCompact K) : IsCompact (e ⁻¹' K) := by
  let h : Plane ≃ₜ Plane :=
    { e.toEquiv with
      continuous_toFun := e.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional }
  exact h.isCompact_preimage.mpr hK

private theorem regular_region_sides_of_local_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D N : Set E} {H : E → ℝ} (hD : IsClosed D) (hN : IsOpen N)
    (hH : Continuous H) (hreg : ∀ p ∈ N, H p = 0 → fderiv ℝ H p ≠ 0)
    (heq : ∀ p ∈ N, p ∈ D ↔ 0 ≤ H p) :
    ∀ p ∈ N, (p ∈ interior D ↔ 0 < H p) ∧
      (p ∈ frontier D ↔ H p = 0) := by
  intro p hp
  have hi : p ∈ interior D ↔ 0 < H p := by
    constructor
    · intro hi
      have hle : 0 ≤ H p := (heq p hp).mp (interior_subset hi)
      by_contra hn
      have hz : H p = 0 := le_antisymm (le_of_not_gt hn) hle
      have hmin : IsLocalMin H p := by
        filter_upwards [hN.mem_nhds hp, mem_interior_iff_mem_nhds.mp hi] with q hqN hqD
        change H p ≤ H q
        rw [hz]
        exact (heq q hqN).mp hqD
      exact hreg p hp hz hmin.fderiv_eq_zero
    · intro hpos
      apply interior_mono (s := N ∩ {q | 0 < H q}) (t := D)
        (fun q hq => (heq q hq.1).mpr hq.2.le)
      rw [(hN.inter (isOpen_lt continuous_const hH)).interior_eq]
      exact ⟨hp, hpos⟩
  refine ⟨hi, ?_⟩
  rw [hD.frontier_eq]
  change (p ∈ D ∧ p ∉ interior D) ↔ H p = 0
  rw [heq p hp, hi, not_lt]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

private theorem regular_region_replace_on_open
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D N K : Set E} {H : E → ℝ} (hD : IsCompact D) (hN : IsOpen N)
    (hK : IsCompact K) (hNK : N ⊆ K) (hH : Continuous H)
    (hreg : ∀ p ∈ N, H p = 0 → fderiv ℝ H p ≠ 0)
    (heq : ∀ p ∈ K \ N, 0 ≤ H p ↔ p ∈ D) :
    let D' := (D \ N) ∪ (K ∩ {p | 0 ≤ H p})
    IsCompact D' ∧
      (∀ p ∈ N, (p ∈ D' ↔ 0 ≤ H p) ∧
        (p ∈ interior D' ↔ 0 < H p) ∧ (p ∈ frontier D' ↔ H p = 0)) ∧
      (∀ p ∉ N, p ∈ D' ↔ p ∈ D) := by
  obtain ⟨hD', hlocal, hout⟩ := compact_region_replace_on_open hD hN hK
    (isClosed_le continuous_const hH) hNK heq
  have hsides := regular_region_sides_of_local_eq hD'.isClosed hN hH hreg hlocal
  exact ⟨hD', fun p hp => ⟨hlocal p hp, hsides p hp⟩, hout⟩

private theorem region_replace_eq_self_of_local_eq
    {X : Type*} {D N K A : Set X} (hNK : N ⊆ K)
    (heq : ∀ p ∈ K, p ∈ A ↔ p ∈ D) :
    (D \ N) ∪ (K ∩ A) = D := by
  ext p
  constructor
  · rintro (⟨hp, _⟩ | ⟨hpK, hpA⟩)
    · exact hp
    · exact (heq p hpK).mp hpA
  · intro hp
    by_cases hpN : p ∈ N
    · exact Or.inr ⟨hNK hpN, (heq p (hNK hpN)).mpr hp⟩
    · exact Or.inl ⟨hp, hpN⟩

private theorem affine_smooth_corner_side_eq_outside_ball
    (e : Plane ≃ᵃ[ℝ] Plane) {ε R d σ : ℝ} (hε : 0 < ε)
    (hεR : 3 * ε < R) (hd : d = 0 ∨ d = 1) (hσ : σ = -1 ∨ σ = 1)
    {p : Plane} (hp : p ∉ e ⁻¹' ball (0 : Plane) R) :
    (0 ≤ σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0) ↔
      0 ≤ σ * ((e p) 1 - d * max ((e p) 0) 0)) := by
  have hpR : R ≤ ‖e p‖ := by
    have hn : ¬ ‖e p‖ < R := by
      simpa only [Set.mem_preimage, mem_ball_zero_iff] using hp
    exact le_of_not_gt hn
  exact (smooth_corner_signs_eq_outside_ball hε hd hσ (hεR.trans_le hpR)).1

end Schoenflies

end

section
open Set Metric
open scoped ContDiff Topology

namespace Schoenflies

private theorem exists_affine_closed_ball_subset
    {U : Set Plane} (hU : IsOpen U) (e : Plane ≃ᵃ[ℝ] Plane)
    {a : Plane} (ha : a ∈ U) (hea : e a = 0) :
    ∃ R : ℝ, 0 < R ∧ a ∈ e ⁻¹' ball (0 : Plane) R ∧
      e ⁻¹' closedBall (0 : Plane) R ⊆ U := by
  have hei : Continuous e.symm := e.symm.toAffineMap.continuous_of_finiteDimensional
  have hz : (0 : Plane) ∈ e.symm ⁻¹' U := by
    change e.symm 0 ∈ U
    rw [← hea, e.symm_apply_apply]
    exact ha
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp (hU.preimage hei) 0 hz
  have hR : 0 < δ / 2 := half_pos hδ
  refine ⟨δ / 2, hR, ?_, ?_⟩
  · exact Set.mem_preimage.mpr
      ((congrArg (fun q : Plane => q ∈ ball (0 : Plane) (δ / 2)) hea).mpr
        (mem_ball_self hR))
  · intro p hp
    have hpδ : e p ∈ ball (0 : Plane) δ := by
      have hpR : dist (e p) 0 ≤ δ / 2 := hp
      exact lt_of_le_of_lt hpR (half_lt_self hδ)
    have hpU := hδU hpδ
    change e.symm (e p) ∈ U at hpU
    rwa [e.symm_apply_apply] at hpU

private theorem compact_corner_replacement_of_closed_ball_subset
    {D U : Set Plane} (hD : IsCompact D) (e : Plane ≃ᵃ[ℝ] Plane)
    {ε R d σ : ℝ} (hε : 0 < ε) (hεR : 3 * ε < R)
    (hd : d = 0 ∨ d = 1) (hσ : σ = -1 ∨ σ = 1)
    (hKU : e ⁻¹' closedBall (0 : Plane) R ⊆ U)
    (hside : ∀ p ∈ U, p ∈ D ↔ 0 ≤ σ * ((e p) 1 - d * max ((e p) 0) 0)) :
    let N := e ⁻¹' ball (0 : Plane) R
    let K := e ⁻¹' closedBall (0 : Plane) R
    let H : Plane → ℝ := fun p => σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)
    let D' := (D \ N) ∪ (K ∩ {p | 0 ≤ H p})
    IsCompact D' ∧ ContDiff ℝ ∞ H ∧ (∀ p, fderiv ℝ H p ≠ 0) ∧
      (∀ p ∈ N, (p ∈ D' ↔ 0 ≤ H p) ∧
        (p ∈ interior D' ↔ 0 < H p) ∧ (p ∈ frontier D' ↔ H p = 0)) ∧
      (∀ p ∉ N, p ∈ D' ↔ p ∈ D) ∧ (d = 0 → D' = D) := by
  let N := e ⁻¹' ball (0 : Plane) R
  let K := e ⁻¹' closedBall (0 : Plane) R
  let H : Plane → ℝ := fun p => σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)
  have he : Continuous e := e.toAffineMap.continuous_of_finiteDimensional
  have hN : IsOpen N := isOpen_ball.preimage he
  have hK : IsCompact K := affine_preimage_isCompact e (isCompact_closedBall (0 : Plane) R)
  have hNK : N ⊆ K := Set.preimage_mono (f := e)
    (ball_subset_closedBall (x := (0 : Plane)) (ε := R))
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  obtain ⟨hH, hreg⟩ := affine_smooth_corner_regular e ε d σ hσne
  have heq : ∀ p ∈ K \ N, 0 ≤ H p ↔ p ∈ D := fun p hp =>
    (affine_smooth_corner_side_eq_outside_ball e hε hεR hd hσ hp.2).trans
      (hside p (hKU hp.1)).symm
  obtain ⟨hD', hlocal, hout⟩ := regular_region_replace_on_open
    (D := D) (N := N) (K := K) (H := H) hD hN hK hNK hH.continuous
    (fun p _ _ => hreg p) heq
  refine ⟨hD', hH, hreg, hlocal, hout, fun hd0 => ?_⟩
  apply region_replace_eq_self_of_local_eq hNK
  intro p hp
  change 0 ≤ H p ↔ p ∈ D
  rw [hside p (hKU hp)]
  simp only [H, hd0, zero_mul, sub_zero]

private theorem exists_compact_corner_replacement
    {D U : Set Plane} (hD : IsCompact D) (hU : IsOpen U)
    (e : Plane ≃ᵃ[ℝ] Plane) {a : Plane} (ha : a ∈ U) (hea : e a = 0)
    {d σ : ℝ} (hd : d = 0 ∨ d = 1) (hσ : σ = -1 ∨ σ = 1)
    (hside : ∀ p ∈ U, p ∈ D ↔ 0 ≤ σ * ((e p) 1 - d * max ((e p) 0) 0)) :
    ∃ ε R : ℝ, 0 < ε ∧ 3 * ε < R ∧
      let N := e ⁻¹' ball (0 : Plane) R
      let K := e ⁻¹' closedBall (0 : Plane) R
      let H : Plane → ℝ := fun p => σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)
      let D' := (D \ N) ∪ (K ∩ {p | 0 ≤ H p})
      a ∈ N ∧ IsOpen N ∧ IsCompact K ∧ K ⊆ U ∧ IsCompact D' ∧
      ContDiff ℝ ∞ H ∧ (∀ p, fderiv ℝ H p ≠ 0) ∧
      (∀ p ∈ N, (p ∈ D' ↔ 0 ≤ H p) ∧
        (p ∈ interior D' ↔ 0 < H p) ∧ (p ∈ frontier D' ↔ H p = 0)) ∧
      (∀ p ∉ N, p ∈ D' ↔ p ∈ D) ∧ (d = 0 → D' = D) := by
  obtain ⟨R, hR, haN, hKU⟩ := exists_affine_closed_ball_subset hU e ha hea
  let ε := R / 4
  have hε : 0 < ε := div_pos hR (by norm_num)
  have hεR : 3 * ε < R := by dsimp [ε]; linarith
  have he : Continuous e := e.toAffineMap.continuous_of_finiteDimensional
  exact ⟨ε, R, hε, hεR, haN, isOpen_ball.preimage he,
    affine_preimage_isCompact e (isCompact_closedBall (0 : Plane) R), hKU,
    compact_corner_replacement_of_closed_ball_subset hD e hε hεR hd hσ hKU hside⟩

theorem PrePolygon.exists_compact_vertex_rounding
    {m : ℕ} (P : PrePolygon m) (i : ZMod (m + 3)) :
    ∃ (e : Plane ≃ᵃ[ℝ] Plane) (U : Set Plane) (d σ ε R : ℝ),
      IsOpen U ∧ P.vertex i ∈ U ∧ e (P.vertex i) = 0 ∧
      (d = 0 ∨ d = 1) ∧ (σ = -1 ∨ σ = 1) ∧
      (d = 0 ↔ Plane.det (P.vertex (i - 1) - P.vertex i)
        (P.vertex (i + 1) - P.vertex i) = 0) ∧
      0 < ε ∧ 3 * ε < R ∧
      let D := closure (inside P.carrier)
      let N := e ⁻¹' ball (0 : Plane) R
      let K := e ⁻¹' closedBall (0 : Plane) R
      let H : Plane → ℝ := fun p => σ * ((e p) 1 - d * Real.smoothMax ε ((e p) 0) 0)
      let D' := (D \ N) ∪ (K ∩ {p | 0 ≤ H p})
      (∀ p ∈ U, (p ∈ D ↔ 0 ≤ σ * ((e p) 1 - d * max ((e p) 0) 0)) ∧
        (p ∈ interior D ↔ 0 < σ * ((e p) 1 - d * max ((e p) 0) 0)) ∧
        (p ∈ frontier D ↔ (e p) 1 = d * max ((e p) 0) 0)) ∧
      P.vertex i ∈ N ∧ IsOpen N ∧ IsCompact K ∧ K ⊆ U ∧ IsCompact D' ∧
      ContDiff ℝ ∞ H ∧ (∀ p, fderiv ℝ H p ≠ 0) ∧
      (∀ p ∈ N, (p ∈ D' ↔ 0 ≤ H p) ∧
        (p ∈ interior D' ↔ 0 < H p) ∧ (p ∈ frontier D' ↔ H p = 0)) ∧
      (∀ p ∉ N, p ∈ D' ↔ p ∈ D) ∧ (d = 0 → D' = D) := by
  obtain ⟨e, U, _, d, σ, hU, _, hiU, _, hd, hσ, he0, _, _, hs, hside⟩ :=
    P.exists_affine_vertex_graph_sides i
  have hea : e (P.vertex i) = 0 := by
    rw [he0]
    ext j
    fin_cases j <;> rfl
  obtain ⟨ε, R, hε, hεR, hround⟩ := exists_compact_corner_replacement
    P.isSeparating_carrier.isBounded_inside.isCompact_closure hU e hiU hea hd hσ
    (fun p hp => (hside p hp).1)
  exact ⟨e, U, d, σ, ε, R, hU, hiU, hea, hd, hσ, hs, hε, hεR,
    fun p hp => ⟨(hside p hp).1, (hside p hp).2.1, (hside p hp).2.2.1⟩, hround⟩

end Schoenflies

end

section
open Set
open scoped ContDiff

namespace Schoenflies

private theorem PrePolygon.exists_straight_vertex_of_mem_open_edge
    {m : ℕ} (P : PrePolygon m) {i : ZMod (m + 3)} {p : Plane}
    (hp : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1))) :
    ∃ (Q : PrePolygon (m + 1)) (j : ZMod (m + 1 + 3)),
      Q.carrier = P.carrier ∧ Q.vertex j = p ∧
      Plane.det (Q.vertex (j - 1) - Q.vertex j) (Q.vertex (j + 1) - Q.vertex j) = 0 := by
  let Q := P.rotate (i + 1)
  have hQm : Q.vertex (-1) = P.vertex i := by
    change P.vertex (i + 1 + (-1)) = P.vertex i
    congr 1
    ring
  have hQ0 : Q.vertex 0 = P.vertex (i + 1) := by
    change P.vertex (i + 1 + 0) = P.vertex (i + 1)
    rw [add_zero]
  have hpQ : p ∈ openSegment ℝ (Q.vertex (-1)) (Q.vertex 0) := by
    rw [hQm, hQ0]
    exact hp
  let Q' := Q.insertLast hpQ
  have hv : Q'.vertex (-1) = p := Q.insVertex_neg_one _
  have hvpred : Q'.vertex (-1 - 1) = Q.vertex (-1) := by
    have he : PrePolygon.emb (-1 : ZMod (m + 3)) = (-1 - 1 : ZMod (m + 1 + 3)) :=
      PrePolygon.emb_eq_last (by rw [PrePolygon.val_neg_one])
    change Q.insVertex p (-1 - 1) = Q.vertex (-1)
    rw [← he, Q.insVertex_emb]
  have hvsucc : Q'.vertex (-1 + 1) = Q.vertex 0 := by
    have he : PrePolygon.emb (0 : ZMod (m + 3)) = (0 : ZMod (m + 1 + 3)) := by
      rw [PrePolygon.emb, ZMod.val_zero, Nat.cast_zero]
    change Q.insVertex p (-1 + 1) = Q.vertex 0
    rw [neg_add_cancel, ← he, Q.insVertex_emb]
  refine ⟨Q', -1, ?_, hv, ?_⟩
  · exact (PrePolygon.carrier_insertLast hpQ).trans (P.carrier_rotate (i + 1))
  · rw [hvpred, hvsucc, hv]
    exact det_eq_zero_of_mem_segment (left_mem_segment ℝ _ _)
      (right_mem_segment ℝ _ _) (openSegment_subset_segment ℝ _ _ hpQ)

private theorem PrePolygon.exists_regular_neighborhood_of_mem_carrier_not_vertex
    {m : ℕ} (P : PrePolygon m) {p : Plane} (hp : p ∈ P.carrier)
    (hn : p ∉ Set.range P.vertex) :
    ∃ (U : Set Plane) (H : Plane → ℝ), IsOpen U ∧ p ∈ U ∧
      ContDiff ℝ ∞ H ∧ (∀ q, fderiv ℝ H q ≠ 0) ∧
      ∀ q ∈ U,
        (q ∈ closure (inside P.carrier) ↔ 0 ≤ H q) ∧
        (q ∈ interior (closure (inside P.carrier)) ↔ 0 < H q) ∧
        (q ∈ frontier (closure (inside P.carrier)) ↔ H q = 0) := by
  obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
  have hopen : p ∈ openSegment ℝ (P.vertex i) (P.vertex (i + 1)) :=
    mem_openSegment_of_ne_left_right (fun he => hn ⟨i, he⟩)
      (fun he => hn ⟨i + 1, he⟩) hpi
  obtain ⟨Q, j, hcar, hj, hdet⟩ := P.exists_straight_vertex_of_mem_open_edge hopen
  obtain ⟨e, U, _, d, σ, hU, _, hjU, _, _, hσ, _, _, _, hs, hside⟩ :=
    Q.exists_affine_vertex_graph_sides j
  have hd0 : d = 0 := hs.mpr hdet
  subst d
  have hσne : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
  have hh := affine_smooth_corner_regular e 1 0 σ hσne
  simp only [zero_mul, sub_zero] at hh
  have hweak : ∀ q ∈ U, q ∈ closure (inside P.carrier) ↔ 0 ≤ σ * (e q) 1 := by
    intro q hq
    simpa only [hcar, zero_mul, sub_zero] using (hside q hq).1
  have hsides := regular_region_sides_of_local_eq isClosed_closure hU hh.1.continuous
    (fun q _ _ => hh.2 q) hweak
  exact ⟨U, _, hU, hj ▸ hjU, hh.1, hh.2,
    fun q hq => ⟨hweak q hq, hsides q hq⟩⟩

end Schoenflies

end

section
open Set

namespace Schoenflies

private theorem finite_disjoint_region_replacement
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {D : Set X} {U N K A : ι → Set X} (hD : IsCompact D)
    (hN : ∀ i, IsOpen (N i)) (hK : ∀ i, IsCompact (K i))
    (hA : ∀ i, IsClosed (A i)) (hNK : ∀ i, N i ⊆ K i)
    (hKU : ∀ i, K i ⊆ U i) (hdisj : Pairwise fun i j => Disjoint (U i) (U j))
    (heq : ∀ i, ∀ p ∈ U i \ N i, p ∈ A i ↔ p ∈ D) :
    let D' := (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ A i
    IsCompact D' ∧
      (∀ i, ∀ p ∈ U i, p ∈ D' ↔ p ∈ A i) ∧
      (∀ p ∉ ⋃ i, K i, p ∈ D' ↔ p ∈ D) := by
  have houtside (i : ι) {p : X} (hp : p ∈ U i) :
      ∀ j, j ≠ i → p ∉ U j := by
    intro j hji hpj
    exact Set.disjoint_left.mp (hdisj hji) hpj hp
  refine ⟨(hD.diff (isOpen_iUnion hN)).union
    (isCompact_iUnion fun i => (hK i).inter_right (hA i)), ?_, ?_⟩
  · intro i p hp
    constructor
    · rintro (⟨hpD, hpN⟩ | hpK)
      · exact (heq i p ⟨hp, fun h => hpN (Set.mem_iUnion.mpr ⟨i, h⟩)⟩).mpr hpD
      · obtain ⟨j, hpj, hpa⟩ := Set.mem_iUnion.mp hpK
        by_cases hji : j = i
        · exact hji ▸ hpa
        · exact False.elim (houtside i hp j hji (hKU j hpj))
    · intro hpA
      by_cases hpN : p ∈ N i
      · exact Or.inr (Set.mem_iUnion.mpr ⟨i, hNK i hpN, hpA⟩)
      · refine Or.inl ⟨(heq i p ⟨hp, hpN⟩).mp hpA, ?_⟩
        intro hpall
        obtain ⟨j, hpj⟩ := Set.mem_iUnion.mp hpall
        by_cases hji : j = i
        · exact hpN (hji ▸ hpj)
        · exact houtside i hp j hji (hKU j (hNK j hpj))
  · intro p hp
    constructor
    · rintro (⟨hpD, _⟩ | hpK)
      · exact hpD
      · obtain ⟨i, hpi, _⟩ := Set.mem_iUnion.mp hpK
        exact False.elim (hp (Set.mem_iUnion.mpr ⟨i, hpi⟩))
    · intro hpD
      refine Or.inl ⟨hpD, ?_⟩
      intro hpN
      obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpN
      exact hp (Set.mem_iUnion.mpr ⟨i, hNK i hpi⟩)

private theorem exists_pairwise_disjoint_open_neighborhoods
    {X ι : Type*} [TopologicalSpace X] [T2Space X] [Finite ι]
    (f : ι → X) (hf : Function.Injective f) (O : ι → Set X)
    (hO : ∀ i, IsOpen (O i)) (hfO : ∀ i, f i ∈ O i) :
    ∃ U : ι → Set X, (∀ i, IsOpen (U i) ∧ f i ∈ U i ∧ U i ⊆ O i) ∧
      Pairwise fun i j => Disjoint (U i) (U j) := by
  obtain ⟨V, hV, hdisj⟩ := (Set.finite_range f).t2_separation
  refine ⟨fun i => V (f i) ∩ O i, fun i =>
    ⟨(hV (f i)).2.inter (hO i), ⟨(hV (f i)).1, hfO i⟩, Set.inter_subset_right⟩, ?_⟩
  intro i j hij
  exact (hdisj (Set.mem_range_self i) (Set.mem_range_self j)
    (fun he => hij (hf he))).mono Set.inter_subset_left Set.inter_subset_left

end Schoenflies

end

section
open Set Metric
open scoped ContDiff Topology

namespace Schoenflies

private theorem PrePolygon.regular_frontier_of_finite_replacement
    {m : ℕ} (P : PrePolygon m) {D' : Set Plane} (hD' : IsClosed D')
    (U K : ZMod (m + 3) → Set Plane) (H : ZMod (m + 3) → Plane → ℝ)
    (hU : ∀ i, IsOpen (U i)) (hiU : ∀ i, P.vertex i ∈ U i)
    (hK : ∀ i, IsCompact (K i)) (hKU : ∀ i, K i ⊆ U i)
    (hH : ∀ i, ContDiff ℝ ∞ (H i)) (hreg : ∀ i p, fderiv ℝ (H i) p ≠ 0)
    (hlocal : ∀ i, ∀ p ∈ U i, p ∈ D' ↔ 0 ≤ H i p)
    (hout : ∀ p ∉ ⋃ i, K i, p ∈ D' ↔ p ∈ closure (inside P.carrier)) :
    ∀ p ∈ frontier D', ∃ (V : Set Plane) (G : Plane → ℝ),
      IsOpen V ∧ p ∈ V ∧ ContDiff ℝ ∞ G ∧ (∀ q, fderiv ℝ G q ≠ 0) ∧
      ∀ q ∈ V, (q ∈ D' ↔ 0 ≤ G q) ∧
        (q ∈ interior D' ↔ 0 < G q) ∧ (q ∈ frontier D' ↔ G q = 0) := by
  let D := closure (inside P.carrier)
  have hsides (i) := regular_region_sides_of_local_eq hD' (hU i)
    (hH i).continuous (fun p _ _ => hreg i p) (hlocal i)
  intro p hp
  by_cases hpU : p ∈ ⋃ i, U i
  · obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpU
    exact ⟨U i, H i, hU i, hpi, hH i, hreg i,
      fun q hq => ⟨hlocal i q hq, hsides i q hq⟩⟩
  · let L := (⋃ i, K i)ᶜ
    have hL : IsOpen L := (isCompact_iUnion hK).isClosed.isOpen_compl
    have hpL : p ∈ L := by
      intro hpK
      obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpK
      exact hpU (Set.mem_iUnion.mpr ⟨i, hKU i hpi⟩)
    have hsame : D' =ᶠ[𝓝 p] D := by
      filter_upwards [hL.mem_nhds hpL] with q hq
      exact propext (hout q hq)
    have hpD : p ∈ D := (hout p hpL).mp (hD'.frontier_subset hp)
    have hpfront : p ∈ frontier D := by
      rw [isClosed_closure.frontier_eq]
      refine ⟨hpD, ?_⟩
      intro hi
      exact hp.2 (hsame.mem_interior_iff.mpr hi)
    have hpcar : p ∈ P.carrier := by
      rw [← P.isSeparating_carrier.frontier_inside]
      exact frontier_closure_subset hpfront
    have hn : p ∉ Set.range P.vertex := by
      rintro ⟨i, rfl⟩
      exact hpU (Set.mem_iUnion.mpr ⟨i, hiU i⟩)
    obtain ⟨V, G, hV, hpV, hG, hGreg, hGsides⟩ :=
      P.exists_regular_neighborhood_of_mem_carrier_not_vertex hpcar hn
    have hweak : ∀ q ∈ L ∩ V, q ∈ D' ↔ 0 ≤ G q :=
      fun q hq => (hout q hq.1).trans (hGsides q hq.2).1
    have hnew := regular_region_sides_of_local_eq hD' (hL.inter hV)
      hG.continuous (fun q _ _ => hGreg q) hweak
    exact ⟨L ∩ V, G, hL.inter hV, ⟨hpL, hpV⟩, hG, hGreg,
      fun q hq => ⟨hweak q hq, hnew q hq⟩⟩

theorem PrePolygon.exists_finite_compact_vertex_rounding
    {m : ℕ} (P : PrePolygon m) (O : ZMod (m + 3) → Set Plane)
    (hO : ∀ i, IsOpen (O i)) (hiO : ∀ i, P.vertex i ∈ O i) :
    ∃ (e : ZMod (m + 3) → Plane ≃ᵃ[ℝ] Plane)
      (U : ZMod (m + 3) → Set Plane) (d σ ε R : ZMod (m + 3) → ℝ),
      (∀ i, IsOpen (U i) ∧ P.vertex i ∈ U i ∧ U i ⊆ O i ∧
        e i (P.vertex i) = 0 ∧ (d i = 0 ∨ d i = 1) ∧
        (σ i = -1 ∨ σ i = 1) ∧
        (d i = 0 ↔ Plane.det (P.vertex (i - 1) - P.vertex i)
          (P.vertex (i + 1) - P.vertex i) = 0) ∧ 0 < ε i ∧ 3 * ε i < R i ∧
        ∀ p ∈ U i, p ∈ closure (inside P.carrier) ↔
          0 ≤ σ i * ((e i p) 1 - d i * max ((e i p) 0) 0)) ∧
      (Pairwise fun i j => Disjoint (U i) (U j)) ∧
      let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
      let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
      let H := fun i p => σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
      let D := closure (inside P.carrier)
      let D' := (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ H i p}
      (∀ i, P.vertex i ∈ N i ∧ IsOpen (N i) ∧ IsCompact (K i) ∧ K i ⊆ U i) ∧
      IsCompact D' ∧ (∀ p ∉ ⋃ i, K i, p ∈ D' ↔ p ∈ D) ∧
      (∀ i, ContDiff ℝ ∞ (H i) ∧ (∀ p, fderiv ℝ (H i) p ≠ 0) ∧
        ∀ p ∈ U i, (p ∈ D' ↔ 0 ≤ H i p) ∧
          (p ∈ interior D' ↔ 0 < H i p) ∧ (p ∈ frontier D' ↔ H i p = 0)) ∧
      ∀ p ∈ frontier D', ∃ (V : Set Plane) (G : Plane → ℝ),
        IsOpen V ∧ p ∈ V ∧ ContDiff ℝ ∞ G ∧ (∀ q, fderiv ℝ G q ≠ 0) ∧
        ∀ q ∈ V, (q ∈ D' ↔ 0 ≤ G q) ∧
          (q ∈ interior D' ↔ 0 < G q) ∧ (q ∈ frontier D' ↔ G q = 0) := by
  classical
  choose e A _ d σ hA _ hiA _ hd hσ he0 _ _ hstraight hside using
    (fun i => P.exists_affine_vertex_graph_sides i)
  obtain ⟨U, hU, hdisj⟩ := exists_pairwise_disjoint_open_neighborhoods P.vertex P.vertex_inj
    (fun i => A i ∩ O i) (fun i => (hA i).inter (hO i)) (fun i => ⟨hiA i, hiO i⟩)
  have hea (i) : e i (P.vertex i) = 0 := by
    rw [he0 i]
    ext j
    fin_cases j <;> rfl
  have hD : IsCompact (closure (inside P.carrier)) :=
    P.isSeparating_carrier.isBounded_inside.isCompact_closure
  choose ε R hε hεR hround using fun i => exists_compact_corner_replacement hD (hU i).1
    (e i) (hU i).2.1 (hea i) (hd i) (hσ i)
    (fun p hp => (hside i p ((hU i).2.2 hp).1).1)
  let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
  let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
  let H := fun i p => σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
  let D := closure (inside P.carrier)
  have hN (i) : IsOpen (N i) := (hround i).2.1
  have hK (i) : IsCompact (K i) := (hround i).2.2.1
  have hKU (i) : K i ⊆ U i := (hround i).2.2.2.1
  have hNK (i) : N i ⊆ K i := Set.preimage_mono (f := e i)
    (ball_subset_closedBall (x := (0 : Plane)) (ε := R i))
  have hH (i) : ContDiff ℝ ∞ (H i) := (hround i).2.2.2.2.2.1
  have hreg (i) : ∀ p, fderiv ℝ (H i) p ≠ 0 := (hround i).2.2.2.2.2.2.1
  have heq (i) : ∀ p ∈ U i \ N i, p ∈ {p | 0 ≤ H i p} ↔ p ∈ D := by
    intro p hp
    have hpR : R i ≤ ‖e i p‖ := by
      have hn : ¬ ‖e i p‖ < R i := by
        simpa only [N, Set.mem_preimage, mem_ball_zero_iff] using hp.2
      exact le_of_not_gt hn
    exact (smooth_corner_signs_eq_outside_ball (hε i) (hd i) (hσ i)
      ((hεR i).trans_le hpR)).1.trans
        (hside i p ((hU i).2.2 hp.1).1).1.symm
  obtain ⟨hD', hlocal, hout⟩ := finite_disjoint_region_replacement hD hN hK
    (fun i => isClosed_le continuous_const (hH i).continuous) hNK hKU hdisj heq
  have hsides (i) := regular_region_sides_of_local_eq hD'.isClosed (hU i).1
    (hH i).continuous (fun p _ _ => hreg i p) (hlocal i)
  refine ⟨e, U, d, σ, ε, R, ?_, hdisj, ?_, hD', hout,
    fun i => ⟨hH i, hreg i, fun p hp => ⟨hlocal i p hp, hsides i p hp⟩⟩, ?_⟩
  · exact fun i => ⟨(hU i).1, (hU i).2.1,
      fun p hp => ((hU i).2.2 hp).2, hea i, hd i, hσ i, hstraight i, hε i, hεR i,
        fun p hp => (hside i p ((hU i).2.2 hp).1).1⟩
  · exact fun i => ⟨(hround i).1, hN i, hK i, hKU i⟩
  · exact P.regular_frontier_of_finite_replacement hD'.isClosed U K H
      (fun i => (hU i).1) (fun i => (hU i).2.1) hK hKU hH hreg hlocal hout

end Schoenflies

end

section
open Set Metric
open scoped ContDiff

namespace Schoenflies

theorem PrePolygon.exists_compact_rounding
    {m : ℕ} (P : PrePolygon m) {O : Set Plane}
    (hO : IsOpen O) (hvO : Set.range P.vertex ⊆ O) :
    ∃ D' : Set Plane, IsCompact D' ∧ (frontier D').Nonempty ∧
      (∀ p ∉ O, p ∈ D' ↔ p ∈ closure (inside P.carrier)) ∧
      ∀ p ∈ frontier D', ∃ (U : Set Plane) (H : Plane → ℝ),
        IsOpen U ∧ p ∈ U ∧ ContDiff ℝ ∞ H ∧ (∀ q, fderiv ℝ H q ≠ 0) ∧
        ∀ q ∈ U, (q ∈ D' ↔ 0 ≤ H q) ∧
          (q ∈ interior D' ↔ 0 < H q) ∧ (q ∈ frontier D' ↔ H q = 0) := by
  obtain ⟨e, U, d, σ, ε, R, hc, _, hn, hD, hout, hlocal, hglobal⟩ :=
    P.exists_finite_compact_vertex_rounding (fun _ => O) (fun _ => hO)
      (fun i => hvO (Set.mem_range_self i))
  let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
  let H := fun i p => σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
  let D' := (closure (inside P.carrier) \ ⋃ i, e i ⁻¹' ball (0 : Plane) (R i)) ∪
    ⋃ i, K i ∩ {p | 0 ≤ H i p}
  obtain ⟨_, _, _, _, hd, _, _, hε, hεR, _⟩ := hc 0
  let μ := Real.smoothMax (ε 0) 0 0
  have hμ : 0 ≤ μ := by
    simpa only [max_self] using Real.smoothMax.max_le hε 0 0
  have hμε : μ ≤ ε 0 := by
    simpa only [max_self, zero_add] using Real.smoothMax.le_max_add hε 0 0
  have hy : 0 ≤ d 0 * μ ∧ d 0 * μ ≤ ε 0 := by
    rcases hd with hd | hd
    · rw [hd, zero_mul]
      exact ⟨le_rfl, hε.le⟩
    · rw [hd, one_mul]
      exact ⟨hμ, hμε⟩
  let p := (e 0).symm (Plane.mk 0 (d 0 * μ))
  have hpN : p ∈ e 0 ⁻¹' ball (0 : Plane) (R 0) := by
    change (e 0) ((e 0).symm (Plane.mk 0 (d 0 * μ))) ∈ ball (0 : Plane) (R 0)
    rw [(e 0).apply_symm_apply, mem_ball_zero_iff]
    have hnorm : ‖Plane.mk 0 (d 0 * μ)‖ = d 0 * μ := by
      apply (sq_eq_sq₀ (norm_nonneg _) hy.1).mp
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [Fin.sum_univ_two, Plane.mk]
    rw [hnorm]
    linarith
  have hpU : p ∈ U 0 := (hn 0).2.2.2
    (Set.preimage_mono (f := e 0)
      (ball_subset_closedBall (x := (0 : Plane)) (ε := R 0)) hpN)
  have hpfront : p ∈ frontier D' := by
    apply ((hlocal 0).2.2 p hpU).2.2.mpr
    change σ 0 * (((e 0) ((e 0).symm (Plane.mk 0 (d 0 * μ)))) 1 - d 0 *
      Real.smoothMax (ε 0) (((e 0) ((e 0).symm (Plane.mk 0 (d 0 * μ)))) 0) 0) = 0
    rw [(e 0).apply_symm_apply]
    change σ 0 * (d 0 * μ - d 0 * μ) = 0
    ring
  refine ⟨D', hD, ⟨p, hpfront⟩, ?_, hglobal⟩
  intro q hq
  apply hout q
  intro hqK
  obtain ⟨i, hqi⟩ := Set.mem_iUnion.mp hqK
  exact hq ((hc i).2.2.1 ((hn i).2.2.2 hqi))

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Topology

namespace Schoenflies

private theorem region_sides_of_open_local_eq
    {X : Type*} [TopologicalSpace X] {D D' V : Set X}
    (hD : IsClosed D) (hD' : IsClosed D') (hV : IsOpen V)
    (heq : ∀ p ∈ V, p ∈ D' ↔ p ∈ D) :
    ∀ p ∈ V, (p ∈ D' ↔ p ∈ D) ∧
      (p ∈ interior D' ↔ p ∈ interior D) ∧
      (p ∈ frontier D' ↔ p ∈ frontier D) := by
  intro p hp
  have hsame : D' =ᶠ[𝓝 p] D := by
    filter_upwards [hV.mem_nhds hp] with q hq
    exact propext (heq q hq)
  refine ⟨heq p hp, hsame.mem_interior_iff, ?_⟩
  rw [hD'.frontier_eq, hD.frontier_eq]
  change (p ∈ D' ∧ p ∉ interior D') ↔ (p ∈ D ∧ p ∉ interior D)
  rw [heq p hp, hsame.mem_interior_iff]

private theorem PrePolygon.regular_frontier_of_partial_replacement
    {m : ℕ} (P : PrePolygon m) {D D' L W : Set Plane}
    (hD : IsClosed D) (hD' : IsClosed D') (hL : IsClosed L) (hLW : L ⊆ W)
    (hold : ∀ p ∉ L, p ∈ D ↔ p ∈ closure (inside P.carrier))
    (hgood : ∀ p ∈ frontier D, p ∈ W →
      ∃ (N : Set Plane) (G : Plane → ℝ), IsOpen N ∧ p ∈ N ∧
        ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
        ∀ q ∈ N, (q ∈ D ↔ 0 ≤ G q) ∧
          (q ∈ interior D ↔ 0 < G q) ∧ (q ∈ frontier D ↔ G q = 0))
    (U K : {i : ZMod (m + 3) // P.vertex i ∉ W} → Set Plane)
    (H : {i : ZMod (m + 3) // P.vertex i ∉ W} → Plane → ℝ)
    (hU : ∀ i, IsOpen (U i)) (hiU : ∀ i, P.vertex i.val ∈ U i)
    (hK : ∀ i, IsCompact (K i)) (hKU : ∀ i, K i ⊆ U i)
    (hH : ∀ i, ContDiff ℝ ∞ (H i)) (hreg : ∀ i p, fderiv ℝ (H i) p ≠ 0)
    (hlocal : ∀ i, ∀ p ∈ U i, p ∈ D' ↔ 0 ≤ H i p)
    (hout : ∀ p ∉ ⋃ i, K i, p ∈ D' ↔ p ∈ D) :
    ∀ p ∈ frontier D', ∃ (N : Set Plane) (G : Plane → ℝ),
      IsOpen N ∧ p ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
      ∀ q ∈ N, (q ∈ D' ↔ 0 ≤ G q) ∧
        (q ∈ interior D' ↔ 0 < G q) ∧ (q ∈ frontier D' ↔ G q = 0) := by
  have hsides (i) := regular_region_sides_of_local_eq hD' (hU i)
    (hH i).continuous (fun p _ _ => hreg i p) (hlocal i)
  let A := (⋃ i, K i)ᶜ
  have hA : IsOpen A := (isCompact_iUnion hK).isClosed.isOpen_compl
  have heqA := region_sides_of_open_local_eq hD hD' hA hout
  intro p hp
  by_cases hpU : p ∈ ⋃ i, U i
  · obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpU
    exact ⟨U i, H i, hU i, hpi, hH i, hreg i p,
      fun q hq => ⟨hlocal i q hq, hsides i q hq⟩⟩
  · have hpA : p ∈ A := by
      intro hpK
      obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpK
      exact hpU (Set.mem_iUnion.mpr ⟨i, hKU i hpi⟩)
    by_cases hpW : p ∈ W
    · obtain ⟨N, G, hN, hpN, hG, hGreg, hGsides⟩ :=
        hgood p ((heqA p hpA).2.2.mp hp) hpW
      refine ⟨N ∩ A, G, hN.inter hA, ⟨hpN, hpA⟩, hG, hGreg, ?_⟩
      intro q hq
      exact ⟨(heqA q hq.2).1.trans (hGsides q hq.1).1,
        (heqA q hq.2).2.1.trans (hGsides q hq.1).2.1,
        (heqA q hq.2).2.2.trans (hGsides q hq.1).2.2⟩
    · let B := A ∩ Lᶜ
      have hB : IsOpen B := hA.inter hL.isOpen_compl
      have hpB : p ∈ B := ⟨hpA, fun hpL => hpW (hLW hpL)⟩
      have hweak : ∀ q ∈ B, q ∈ D' ↔ q ∈ closure (inside P.carrier) :=
        fun q hq => (hout q hq.1).trans (hold q hq.2)
      have heqB := region_sides_of_open_local_eq isClosed_closure hD' hB hweak
      have hpfront : p ∈ frontier (closure (inside P.carrier)) :=
        (heqB p hpB).2.2.mp hp
      have hpcar : p ∈ P.carrier := by
        rw [← P.isSeparating_carrier.frontier_inside]
        exact frontier_closure_subset hpfront
      have hn : p ∉ Set.range P.vertex := by
        rintro ⟨i, rfl⟩
        exact hpU (Set.mem_iUnion.mpr ⟨⟨i, hpW⟩, hiU ⟨i, hpW⟩⟩)
      obtain ⟨N, G, hN, hpN, hG, hGreg, hGsides⟩ :=
        P.exists_regular_neighborhood_of_mem_carrier_not_vertex hpcar hn
      refine ⟨B ∩ N, G, hB.inter hN, ⟨hpB, hpN⟩, hG, hGreg p, ?_⟩
      intro q hq
      exact ⟨(heqB q hq.1).1.trans (hGsides q hq.2).1,
        (heqB q hq.1).2.1.trans (hGsides q hq.2).2.1,
        (heqB q hq.1).2.2.trans (hGsides q hq.2).2.2⟩

end Schoenflies

end

section

open Set Metric
open scoped ContDiff Topology

namespace Schoenflies

theorem PrePolygon.exists_relative_compact_rounding
    {m : ℕ} (P : PrePolygon m) {D L W O : Set Plane}
    (hD : IsCompact D) (hL : IsClosed L) (hW : IsOpen W) (hLW : L ⊆ W)
    (hO : IsOpen O) (hvO : ∀ i, P.vertex i ∉ W → P.vertex i ∈ O)
    (hold : ∀ p ∉ L, p ∈ D ↔ p ∈ closure (inside P.carrier))
    (hgood : ∀ p ∈ frontier D, p ∈ W →
      ∃ (N : Set Plane) (G : Plane → ℝ), IsOpen N ∧ p ∈ N ∧
        ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
        ∀ q ∈ N, (q ∈ D ↔ 0 ≤ G q) ∧
          (q ∈ interior D ↔ 0 < G q) ∧ (q ∈ frontier D ↔ G q = 0)) :
    ∃ (D' V : Set Plane), IsCompact D' ∧ IsOpen V ∧ L ⊆ V ∧ V ⊆ W ∧
      (∀ p ∈ V, (p ∈ D' ↔ p ∈ D) ∧
        (p ∈ interior D' ↔ p ∈ interior D) ∧
        (p ∈ frontier D' ↔ p ∈ frontier D)) ∧
      (∀ p ∉ O, (p ∈ D' ↔ p ∈ D) ∧
        (p ∈ interior D' ↔ p ∈ interior D) ∧
        (p ∈ frontier D' ↔ p ∈ frontier D)) ∧
      ∀ p ∈ frontier D', ∃ (N : Set Plane) (G : Plane → ℝ),
        IsOpen N ∧ p ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
        ∀ q ∈ N, (q ∈ D' ↔ 0 ≤ G q) ∧
          (q ∈ interior D' ↔ 0 < G q) ∧ (q ∈ frontier D' ↔ G q = 0) := by
  classical
  let I := {i : ZMod (m + 3) // P.vertex i ∉ W}
  choose e A _ d σ hA _ hiA _ hd hσ he0 _ _ _ hside using
    (fun i : I => P.exists_affine_vertex_graph_sides i.val)
  have hinj : Function.Injective (fun i : I => P.vertex i.val) :=
    P.vertex_inj.comp Subtype.val_injective
  obtain ⟨U, hU, hdisj⟩ := exists_pairwise_disjoint_open_neighborhoods
    (fun i : I => P.vertex i.val) hinj (fun i => (A i ∩ Lᶜ) ∩ O)
    (fun i => ((hA i).inter hL.isOpen_compl).inter hO)
    (fun i => ⟨⟨hiA i, fun hp => i.property (hLW hp)⟩, hvO i.val i.property⟩)
  have hea (i : I) : e i (P.vertex i.val) = 0 := by
    rw [he0 i]
    ext j
    fin_cases j <;> rfl
  have hsideD (i : I) : ∀ p ∈ U i,
      p ∈ D ↔ 0 ≤ σ i * ((e i p) 1 - d i * max ((e i p) 0) 0) := by
    intro p hp
    exact (hold p ((hU i).2.2 hp).1.2).trans (hside i p ((hU i).2.2 hp).1.1).1
  choose ε R hε hεR hround using fun i => exists_compact_corner_replacement hD (hU i).1
    (e i) (hU i).2.1 (hea i) (hd i) (hσ i) (hsideD i)
  let N := fun i => e i ⁻¹' ball (0 : Plane) (R i)
  let K := fun i => e i ⁻¹' closedBall (0 : Plane) (R i)
  let H := fun i p => σ i * ((e i p) 1 - d i * Real.smoothMax (ε i) ((e i p) 0) 0)
  have hN (i) : IsOpen (N i) := (hround i).2.1
  have hK (i) : IsCompact (K i) := (hround i).2.2.1
  have hKU (i) : K i ⊆ U i := (hround i).2.2.2.1
  have hNK (i) : N i ⊆ K i := Set.preimage_mono (f := e i)
    (ball_subset_closedBall (x := (0 : Plane)) (ε := R i))
  have hH (i) : ContDiff ℝ ∞ (H i) := (hround i).2.2.2.2.2.1
  have hreg (i) : ∀ p, fderiv ℝ (H i) p ≠ 0 := (hround i).2.2.2.2.2.2.1
  have heq (i) : ∀ p ∈ U i \ N i, p ∈ {p | 0 ≤ H i p} ↔ p ∈ D := by
    intro p hp
    exact (affine_smooth_corner_side_eq_outside_ball (e i) (hε i) (hεR i)
      (hd i) (hσ i) hp.2).trans (hsideD i p hp.1).symm
  obtain ⟨hD', hlocal, hout⟩ := finite_disjoint_region_replacement hD hN hK
    (fun i => isClosed_le continuous_const (hH i).continuous) hNK hKU hdisj heq
  let D' := (D \ ⋃ i, N i) ∪ ⋃ i, K i ∩ {p | 0 ≤ H i p}
  let V := W ∩ (⋃ i, K i)ᶜ
  have hV : IsOpen V := hW.inter (isCompact_iUnion hK).isClosed.isOpen_compl
  have hLV : L ⊆ V := by
    intro p hp
    refine ⟨hLW hp, ?_⟩
    intro hpK
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpK
    exact ((hU i).2.2 (hKU i hpi)).1.2 hp
  have heqV : ∀ p ∈ V, p ∈ D' ↔ p ∈ D := fun p hp => hout p hp.2
  have houtside : ∀ p ∉ O, (p ∈ D' ↔ p ∈ D) ∧
      (p ∈ interior D' ↔ p ∈ interior D) ∧
      (p ∈ frontier D' ↔ p ∈ frontier D) := by
    intro p hp
    apply region_sides_of_open_local_eq hD.isClosed hD'.isClosed
      (isCompact_iUnion hK).isClosed.isOpen_compl hout p
    intro hpK
    obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hpK
    exact hp ((hU i).2.2 (hKU i hpi)).2
  refine ⟨D', V, hD', hV, hLV, Set.inter_subset_left,
    region_sides_of_open_local_eq hD.isClosed hD'.isClosed hV heqV, houtside, ?_⟩
  exact P.regular_frontier_of_partial_replacement hD.isClosed hD'.isClosed
    hL hLW hold hgood U K H (fun i => (hU i).1) (fun i => (hU i).2.1)
    hK hKU hH hreg hlocal hout

end Schoenflies

end
