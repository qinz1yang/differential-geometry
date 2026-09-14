import DifferentialGeometry.Topology.Planar.PolygonIsotopy
import Mathlib.Geometry.Manifold.Diffeomorph
import DifferentialGeometry.External.ClassificationOfSurfaces.PrePolygonDeletion
import Mathlib.Topology.MetricSpace.Thickening
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

section

namespace Schoenflies

private theorem compact_region_replace_preserving_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D K W : Set E} {H : E → ℝ} (hD : IsCompact D) (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) (hH : Continuous H)
    (hreg : ∀ p ∈ W, H p = 0 → fderiv ℝ H p ≠ 0)
    (heq : ∀ p ∈ W \ interior K, p ∈ D ↔ 0 ≤ H p) :
    let D' := (D \ interior K) ∪ (K ∩ {p | 0 ≤ H p})
    IsCompact D' ∧
      (∀ p ∈ W, (p ∈ D' ↔ 0 ≤ H p) ∧
        (p ∈ interior D' ↔ 0 < H p) ∧ (p ∈ frontier D' ↔ H p = 0)) ∧
      (∀ p ∉ K, p ∈ D' ↔ p ∈ D) := by
  obtain ⟨hD', hlocal, hout⟩ := compact_region_replace_on_open hD isOpen_interior hK
    (isClosed_le continuous_const hH) interior_subset
    (fun p hp => (heq p ⟨hKW hp.1, hp.2⟩).symm)
  have hweak : ∀ p ∈ W,
      p ∈ (D \ interior K) ∪ (K ∩ {p | 0 ≤ H p}) ↔ 0 ≤ H p := by
    intro p hp
    by_cases hi : p ∈ interior K
    · exact hlocal p hi
    · exact (hout p hi).trans (heq p ⟨hp, hi⟩)
  have hsides := regular_region_sides_of_local_eq hD'.isClosed hW hH hreg hweak
  exact ⟨hD', fun p hp => ⟨hweak p hp, hsides p hp⟩,
    fun p hp => hout p (fun hi => hp (interior_subset hi))⟩

end Schoenflies

end

section

open scoped ContDiff Manifold Topology

namespace Schoenflies

private theorem PrePolygon.native_compact_region_with_prescribed_isotopy
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
    ∃ (v₀ v₁ : Plane) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ) (ε : ℝ)
      (U₀ U₁ V : Set Plane) (F : Plane → ℝ × ℝ),
      let s₀ := b.coord 2 v₀ / f₀ v₀
      let s₁ := b.coord 2 v₁ / f₁ v₁
      let A₀ := fun p => s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) - b.coord 2 p
      let A₁ := fun p => s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) - b.coord 2 p
      let B₀ := fun p => f₀ (b 2) / f₀ (b 1) *
        (s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) +
          Real.smoothMax ε (f₀ p) 0 / f₀ (b 2) - b.coord 2 p)
      let B₁ := fun p => f₁ (b 2) / f₁ (b 0) *
        (s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) +
          Real.smoothMax ε (f₁ p) 0 / f₁ (b 2) - b.coord 2 p)
      let H := fun q : ℝ × Plane => (1 - q.1) * (F q.2).1 + q.1 * (F q.2).2
      0 < ε ∧ ContDiff ℝ ∞ F ∧ IsOpen U₀ ∧ IsOpen U₁ ∧ IsOpen V ∧
      b 0 ∈ U₀ ∧ b 1 ∈ U₁ ∧ Disjoint U₀ U₁ ∧
      M.triangleCarrier T.1 ⊆ U₀ ∪ U₁ ∪ V ∧
      segment ℝ (b 0) v₀ ⊆ R ∧ segment ℝ (b 1) v₁ ⊆ R ∧
      f₀ (b 0) = 0 ∧ 0 < f₀ (b 1) ∧ 0 < f₀ (b 2) ∧ f₀ v₀ < 0 ∧
      f₁ (b 1) = 0 ∧ 0 < f₁ (b 0) ∧ 0 < f₁ (b 2) ∧ f₁ v₁ < 0 ∧
      (∀ p ∈ U₀, (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p) ∧
      (∀ p ∈ U₁, (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p) ∧
      Set.EqOn F (fun p => (A₀ p, B₀ p)) U₀ ∧
      Set.EqOn F (fun p => (A₁ p, B₁ p)) U₁ ∧
      Set.EqOn F (fun p => (-b.coord 2 p,
        -Real.smoothMax (1 / 4) (-b.coord 0 p) (-b.coord 1 p))) V ∧
      (∀ p ∈ U₀,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else
            f₀ p / f₀ (b 2))) ∧
      (∀ p ∈ U₁,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else
            f₁ p / f₁ (b 2))) ∧
      (∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => (F q).1) p ≠ 0 ∧
          fderiv ℝ (fun q => (F q).2) p ≠ 0) ∧
      ContDiff ℝ ∞ H ∧
      (∀ t p, deriv (fun s => H (s, p)) t = (F p).2 - (F p).1) ∧
      (∀ p, H (0, p) = (F p).1) ∧
      (∀ p, H (1, p) = (F p).2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => H (t, q)) p ≠ 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀, f₀ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁, f₁ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ p ∈ V, ε < f₀ p ∧ ε < f₁ p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ V, H (t, p) = 0 →
        p ∈ M.triangleCarrier T.1) ∧
      ∃ J : Set Plane, IsCompact J ∧ M.triangleCarrier T.1 ⊆ interior J ∧
        J ⊆ U₀ ∪ U₁ ∪ V ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
          H (t, p) = 0 → deriv (fun u => H (u, p)) t ≠ 0 → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀,
          H (t, p) = 0 → -ε ≤ f₀ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁,
          H (t, p) = 0 → -ε ≤ f₁ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V, H (t, p) = 0 → p ∉ J →
          (p ∈ U₀ ∧ f₀ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₀ ∩ {q | f₀ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₀ (b 2) / f₀ (b 1) * (F q).1) N) ∨
          (p ∈ U₁ ∧ f₁ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₁ ∩ {q | f₁ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₁ (b 2) / f₁ (b 0) * (F q).1) N)) ∧
        (∀ p ∈ V,
          (p ∈ M.toPlaneComplex.support ↔ 0 ≤ b.coord 2 p) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ 0 < b.coord 2 p) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ b.coord 2 p = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ M.toPlaneComplex.support ↔ (F p).1 ≤ 0) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ (F p).1 < 0) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ (F p).1 = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 ≤ 0) ∧
          (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 < 0) ∧
          (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 = 0)) ∧
        ∃ (K : Set Plane) (X : ℝ × Plane → Plane) (Ω : Set (ℝ × Plane))
          (κ : ℝ × Plane → ℝ),
          IsCompact K ∧ J ⊆ interior K ∧ K ⊆ U₀ ∪ U₁ ∪ V ∧
          ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧
          IsOpen Ω ∧ Set.Icc (0 : ℝ) 1 ×ˢ (U₀ ∪ U₁ ∪ V) ⊆ Ω ∧
          Ω ⊆ Set.univ ×ˢ (U₀ ∪ U₁ ∪ V) ∧ ContDiffOn ℝ ∞ κ Ω ∧
          (∀ z ∈ Ω,
            deriv (fun t => H (t, z.2)) z.1 +
              fderiv ℝ (fun y => H (z.1, y)) z.2 (X z) = κ z * H z) ∧
          (∀ t x, x ∉ K → X (t, x) = 0) ∧
          ∃ Φ : ℝ → (Plane ≃ₘ[ℝ] Plane),
            (∀ (hX : ContDiff ℝ ∞ X) (hsX : HasCompactSupport X) (t : ℝ),
              Φ t = Diffeomorph.timeDependentFlow X hX hsX 0 t) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => Φ q.1 q.2) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => (Φ q.1).symm q.2) ∧
            Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
            (∀ t : ℝ, Set.EqOn (Φ t) id Kᶜ ∧ Set.EqOn (Φ t).symm id Kᶜ) ∧
            (∀ t : ℝ, (∀ p, Φ t p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V) ∧
              (∀ p, (Φ t).symm p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              ((F p).1 = 0 ↔ H (t, Φ t p) = 0) ∧
              ((F p).1 < 0 ↔ H (t, Φ t p) < 0) ∧
              ((F p).1 ≤ 0 ↔ H (t, Φ t p) ≤ 0)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              (H (t, p) = 0 ↔ (F ((Φ t).symm p)).1 = 0) ∧
              (H (t, p) < 0 ↔ (F ((Φ t).symm p)).1 < 0) ∧
              (H (t, p) ≤ 0 ↔ (F ((Φ t).symm p)).1 ≤ 0)) ∧
            let D₀ := (M.toPlaneComplex.support \ interior K) ∪
              (K ∩ {p | (F p).1 ≤ 0})
            let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
            M.toPlaneComplex.support = closure (inside P.carrier) ∧
            IsCompact D₀ ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              (q ∈ D₀ ↔ (F q).1 ≤ 0) ∧
              (q ∈ interior D₀ ↔ (F q).1 < 0) ∧
              (q ∈ frontier D₀ ↔ (F q).1 = 0)) ∧
            (∀ q ∉ K, q ∈ D₀ ↔ q ∈ M.toPlaneComplex.support) ∧
            p ∈ interior K ∧ p ∈ frontier D₀ ∧ (frontier D₀).Nonempty ∧
            ContDiff ℝ ∞ (fun q => -(F q).1) ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              fderiv ℝ (fun z => -(F z).1) q ≠ 0) ∧
            ∀ q ∈ frontier D₀ ∩ (U₀ ∪ U₁ ∪ V),
              ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ K ⊆ N ∧ ContDiff ℝ ∞ G ∧
                (∀ z ∈ N, fderiv ℝ G z ≠ 0) ∧
                (∀ z, G z = -(F z).1) ∧
                ∀ z ∈ N, (z ∈ D₀ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₀ ↔ 0 < G z) ∧
                  (z ∈ frontier D₀ ↔ G z = 0) := by
  dsimp only
  let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
    (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
  let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
  obtain ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse⟩ :=
    P.exists_compactly_supported_isotopy_near_one_edge_free_triangle M hfrontier T k hfree
  let W := U₀ ∪ U₁ ∪ V
  let D₀ := (M.toPlaneComplex.support \ interior K) ∪ (K ∩ {q | (F q).1 ≤ 0})
  have hW : IsOpen W := (hU₀.union hU₁).union hV
  have hregneg (q : Plane) (hq : q ∈ W) :
      fderiv ℝ (fun z => -(F z).1) q ≠ 0 := by
    simpa only [fderiv_fun_neg, neg_ne_zero] using (hreg q hq).1
  obtain ⟨hcompact, hlocal, hout⟩ := compact_region_replace_preserving_germ
    M.toPlaneComplex.isCompact_support hK hW hKW hF.fst.neg.continuous
    (fun q hq _ => hregneg q hq) (by
      intro q hq
      simpa only [neg_nonneg] using
        (hsign q hq.1 (fun hqJ => hq.2 (hJK (interior_subset hqJ)))).1)
  have hD₀ : IsCompact D₀ := by
    simpa only [D₀, neg_nonneg] using hcompact
  have hsides (q : Plane) (hq : q ∈ W) :
      (q ∈ D₀ ↔ (F q).1 ≤ 0) ∧
      (q ∈ interior D₀ ↔ (F q).1 < 0) ∧
      (q ∈ frontier D₀ ↔ (F q).1 = 0) := by
    simpa only [D₀, neg_nonneg, neg_pos, neg_eq_zero] using hlocal q hq
  have houtside (q : Plane) (hq : q ∉ K) :
      q ∈ D₀ ↔ q ∈ M.toPlaneComplex.support := by
    simpa only [D₀, neg_nonneg] using hout q hq
  have hcoords (i : Fin 3) : b.coord i p =
      (1 - (1 : ℝ) / 2) * b.coord i (b 0) + (1 / 2) * b.coord i (b 1) := by
    change b.coord i (AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)) = _
    rw [AffineMap.apply_lineMap, AffineMap.lineMap_apply_ring]
  have hp₀ : b.coord 0 p = 1 / 2 := by norm_num [hcoords, b.coord_apply, Fin.ext_iff]
  have hp₁ : b.coord 1 p = 1 / 2 := by norm_num [hcoords, b.coord_apply, Fin.ext_iff]
  have hp₂ : b.coord 2 p = 0 := by norm_num [hcoords, b.coord_apply, Fin.ext_iff]
  have hpbase : p ∈ segment ℝ (b 0) (b 1) :=
    lineMap_mem_segment ℝ _ _ (show (1 : ℝ) / 2 ∈ Set.Icc 0 1 from
      ⟨by norm_num, by norm_num⟩)
  have hfree' : frontier M.toPlaneComplex.support ∩ M.triangleCarrier T.1 =
      segment ℝ (b 0) (b 1) := hfree
  have hpT : p ∈ M.triangleCarrier T.1 := (hfree'.symm ▸ hpbase).2
  have hpV : p ∈ V := by
    rcases hcover hpT with (hpU₀ | hpU₁) | hpV
    · have h := hgap₀ p hpU₀
      rw [hp₀, hp₁, sub_self] at h
      norm_num at h
    · have h := hgap₁ p hpU₁
      rw [hp₁, hp₀, sub_self] at h
      norm_num at h
    · exact hpV
  have hpzero : (F p).1 = 0 := by
    have h : (F p).1 = -b.coord 2 p := congrArg Prod.fst (heV hpV)
    rw [h, hp₂, neg_zero]
  have hpfront : p ∈ frontier D₀ := (hsides p (Or.inr hpV)).2.2.mpr hpzero
  have hTsub : M.triangleCarrier T.1 ⊆ M.toPlaneComplex.support := by
    rw [M.toPlaneComplex_support]
    exact Set.subset_iUnion_of_subset T.1 (Set.subset_iUnion_of_subset T.2 Set.Subset.rfl)
  have hsupport : M.toPlaneComplex.support = closure (inside P.carrier) :=
    eq_closure_inside_of_isCompact_frontier_eq P.isSeparating_carrier
      M.toPlaneComplex.isCompact_support hfrontier
      ((M.interior_triangleCarrier_nonempty T).mono (interior_mono hTsub))
  refine ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse, hsupport, hD₀, hsides, houtside,
    hJK (interior_subset (htriangleJ hpT)), hpfront, ⟨p, hpfront⟩,
    hF.fst.neg, hregneg, ?_⟩
  intro q hq
  refine ⟨W, (fun z => -(F z).1), hW, hq.2, hKW, hF.fst.neg, hregneg,
    fun _ => rfl, ?_⟩
  intro z hz
  simpa only [neg_nonneg, neg_pos, neg_eq_zero] using hsides z hz

end Schoenflies

end

section

namespace Schoenflies

private theorem PrePolygon.exists_compact_neighborhood_of_vertices_outside
    {m : ℕ} (P : PrePolygon m) {K W : Set Plane} (hK : IsClosed K) (hKW : K ⊆ W) :
    ∃ O : Set Plane, IsOpen O ∧ IsCompact (closure O) ∧ closure O ⊆ Kᶜ ∧
      ∀ i : ZMod (m + 3), P.vertex i ∉ W → P.vertex i ∈ O := by
  let I := {i : ZMod (m + 3) // P.vertex i ∉ W}
  let Q := Set.range (fun i : I => P.vertex i.val)
  have hQ : IsCompact Q := (Set.finite_range _).isCompact
  have hQK : Q ⊆ Kᶜ := by
    rintro _ ⟨i, rfl⟩ hp
    exact i.property (hKW hp)
  obtain ⟨ρ, hρ, hρQ⟩ := hQ.exists_cthickening_subset_open hK.isOpen_compl hQK
  let O := Metric.thickening ρ Q
  have hclosure : closure O ⊆ Metric.cthickening ρ Q :=
    Metric.closure_thickening_subset_cthickening ρ Q
  refine ⟨O, Metric.isOpen_thickening,
    hQ.cthickening.of_isClosed_subset isClosed_closure hclosure, hclosure.trans hρQ, ?_⟩
  intro i hi
  exact Metric.self_subset_thickening hρ Q (Set.mem_range_self (⟨i, hi⟩ : I))

end Schoenflies

end

section

open scoped ContDiff Manifold Topology

namespace Schoenflies

private theorem PrePolygon.native_global_rounding_with_prescribed_isotopy
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
    ∃ (v₀ v₁ : Plane) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ) (ε : ℝ)
      (U₀ U₁ V : Set Plane) (F : Plane → ℝ × ℝ),
      let s₀ := b.coord 2 v₀ / f₀ v₀
      let s₁ := b.coord 2 v₁ / f₁ v₁
      let A₀ := fun p => s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) - b.coord 2 p
      let A₁ := fun p => s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) - b.coord 2 p
      let B₀ := fun p => f₀ (b 2) / f₀ (b 1) *
        (s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) +
          Real.smoothMax ε (f₀ p) 0 / f₀ (b 2) - b.coord 2 p)
      let B₁ := fun p => f₁ (b 2) / f₁ (b 0) *
        (s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) +
          Real.smoothMax ε (f₁ p) 0 / f₁ (b 2) - b.coord 2 p)
      let H := fun q : ℝ × Plane => (1 - q.1) * (F q.2).1 + q.1 * (F q.2).2
      0 < ε ∧ ContDiff ℝ ∞ F ∧ IsOpen U₀ ∧ IsOpen U₁ ∧ IsOpen V ∧
      b 0 ∈ U₀ ∧ b 1 ∈ U₁ ∧ Disjoint U₀ U₁ ∧
      M.triangleCarrier T.1 ⊆ U₀ ∪ U₁ ∪ V ∧
      segment ℝ (b 0) v₀ ⊆ R ∧ segment ℝ (b 1) v₁ ⊆ R ∧
      f₀ (b 0) = 0 ∧ 0 < f₀ (b 1) ∧ 0 < f₀ (b 2) ∧ f₀ v₀ < 0 ∧
      f₁ (b 1) = 0 ∧ 0 < f₁ (b 0) ∧ 0 < f₁ (b 2) ∧ f₁ v₁ < 0 ∧
      (∀ p ∈ U₀, (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p) ∧
      (∀ p ∈ U₁, (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p) ∧
      Set.EqOn F (fun p => (A₀ p, B₀ p)) U₀ ∧
      Set.EqOn F (fun p => (A₁ p, B₁ p)) U₁ ∧
      Set.EqOn F (fun p => (-b.coord 2 p,
        -Real.smoothMax (1 / 4) (-b.coord 0 p) (-b.coord 1 p))) V ∧
      (∀ p ∈ U₀,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else
            f₀ p / f₀ (b 2))) ∧
      (∀ p ∈ U₁,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else
            f₁ p / f₁ (b 2))) ∧
      (∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => (F q).1) p ≠ 0 ∧
          fderiv ℝ (fun q => (F q).2) p ≠ 0) ∧
      ContDiff ℝ ∞ H ∧
      (∀ t p, deriv (fun s => H (s, p)) t = (F p).2 - (F p).1) ∧
      (∀ p, H (0, p) = (F p).1) ∧
      (∀ p, H (1, p) = (F p).2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => H (t, q)) p ≠ 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀, f₀ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁, f₁ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ p ∈ V, ε < f₀ p ∧ ε < f₁ p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ V, H (t, p) = 0 →
        p ∈ M.triangleCarrier T.1) ∧
      ∃ J : Set Plane, IsCompact J ∧ M.triangleCarrier T.1 ⊆ interior J ∧
        J ⊆ U₀ ∪ U₁ ∪ V ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
          H (t, p) = 0 → deriv (fun u => H (u, p)) t ≠ 0 → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀,
          H (t, p) = 0 → -ε ≤ f₀ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁,
          H (t, p) = 0 → -ε ≤ f₁ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V, H (t, p) = 0 → p ∉ J →
          (p ∈ U₀ ∧ f₀ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₀ ∩ {q | f₀ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₀ (b 2) / f₀ (b 1) * (F q).1) N) ∨
          (p ∈ U₁ ∧ f₁ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₁ ∩ {q | f₁ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₁ (b 2) / f₁ (b 0) * (F q).1) N)) ∧
        (∀ p ∈ V,
          (p ∈ M.toPlaneComplex.support ↔ 0 ≤ b.coord 2 p) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ 0 < b.coord 2 p) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ b.coord 2 p = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ M.toPlaneComplex.support ↔ (F p).1 ≤ 0) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ (F p).1 < 0) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ (F p).1 = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 ≤ 0) ∧
          (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 < 0) ∧
          (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 = 0)) ∧
        ∃ (K : Set Plane) (X : ℝ × Plane → Plane) (Ω : Set (ℝ × Plane))
          (κ : ℝ × Plane → ℝ),
          IsCompact K ∧ J ⊆ interior K ∧ K ⊆ U₀ ∪ U₁ ∪ V ∧
          ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧
          IsOpen Ω ∧ Set.Icc (0 : ℝ) 1 ×ˢ (U₀ ∪ U₁ ∪ V) ⊆ Ω ∧
          Ω ⊆ Set.univ ×ˢ (U₀ ∪ U₁ ∪ V) ∧ ContDiffOn ℝ ∞ κ Ω ∧
          (∀ z ∈ Ω,
            deriv (fun t => H (t, z.2)) z.1 +
              fderiv ℝ (fun y => H (z.1, y)) z.2 (X z) = κ z * H z) ∧
          (∀ t x, x ∉ K → X (t, x) = 0) ∧
          ∃ Φ : ℝ → (Plane ≃ₘ[ℝ] Plane),
            (∀ (hX : ContDiff ℝ ∞ X) (hsX : HasCompactSupport X) (t : ℝ),
              Φ t = Diffeomorph.timeDependentFlow X hX hsX 0 t) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => Φ q.1 q.2) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => (Φ q.1).symm q.2) ∧
            Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
            (∀ t : ℝ, Set.EqOn (Φ t) id Kᶜ ∧ Set.EqOn (Φ t).symm id Kᶜ) ∧
            (∀ t : ℝ, (∀ p, Φ t p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V) ∧
              (∀ p, (Φ t).symm p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              ((F p).1 = 0 ↔ H (t, Φ t p) = 0) ∧
              ((F p).1 < 0 ↔ H (t, Φ t p) < 0) ∧
              ((F p).1 ≤ 0 ↔ H (t, Φ t p) ≤ 0)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              (H (t, p) = 0 ↔ (F ((Φ t).symm p)).1 = 0) ∧
              (H (t, p) < 0 ↔ (F ((Φ t).symm p)).1 < 0) ∧
              (H (t, p) ≤ 0 ↔ (F ((Φ t).symm p)).1 ≤ 0)) ∧
            let D₀ := (M.toPlaneComplex.support \ interior K) ∪
              (K ∩ {p | (F p).1 ≤ 0})
            let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
            M.toPlaneComplex.support = closure (inside P.carrier) ∧
            IsCompact D₀ ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              (q ∈ D₀ ↔ (F q).1 ≤ 0) ∧
              (q ∈ interior D₀ ↔ (F q).1 < 0) ∧
              (q ∈ frontier D₀ ↔ (F q).1 = 0)) ∧
            (∀ q ∉ K, q ∈ D₀ ↔ q ∈ M.toPlaneComplex.support) ∧
            p ∈ interior K ∧ p ∈ frontier D₀ ∧ (frontier D₀).Nonempty ∧
            ContDiff ℝ ∞ (fun q => -(F q).1) ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              fderiv ℝ (fun z => -(F z).1) q ≠ 0) ∧
            (∀ q ∈ frontier D₀ ∩ (U₀ ∪ U₁ ∪ V),
              ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ K ⊆ N ∧ ContDiff ℝ ∞ G ∧
                (∀ z ∈ N, fderiv ℝ G z ≠ 0) ∧
                (∀ z, G z = -(F z).1) ∧
                ∀ z ∈ N, (z ∈ D₀ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₀ ↔ 0 < G z) ∧
                  (z ∈ frontier D₀ ↔ G z = 0)) ∧
            ∃ (O V₁ D₁ : Set Plane),
              IsOpen O ∧ IsCompact (closure O) ∧ closure O ⊆ Kᶜ ∧
              (∀ i : ZMod (m + 3), P.vertex i ∉ U₀ ∪ U₁ ∪ V → P.vertex i ∈ O) ∧
              IsCompact D₁ ∧ IsOpen V₁ ∧ K ⊆ V₁ ∧ V₁ ⊆ U₀ ∪ U₁ ∪ V ∧
              (∀ q ∈ V₁, (q ∈ D₁ ↔ q ∈ D₀) ∧
                (q ∈ interior D₁ ↔ q ∈ interior D₀) ∧
                (q ∈ frontier D₁ ↔ q ∈ frontier D₀)) ∧
              (∀ q ∉ O, (q ∈ D₁ ↔ q ∈ D₀) ∧
                (q ∈ interior D₁ ↔ q ∈ interior D₀) ∧
                (q ∈ frontier D₁ ↔ q ∈ frontier D₀)) ∧
              (∀ q ∉ K ∪ O, q ∈ D₁ ↔ q ∈ M.toPlaneComplex.support) ∧
              (∀ q ∈ V₁, (q ∈ D₁ ↔ (F q).1 ≤ 0) ∧
                (q ∈ interior D₁ ↔ (F q).1 < 0) ∧
                (q ∈ frontier D₁ ↔ (F q).1 = 0)) ∧
              p ∈ frontier D₁ ∧ (frontier D₁).Nonempty ∧
              ∀ q ∈ frontier D₁, ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G q ≠ 0 ∧
                ∀ z ∈ N, (z ∈ D₁ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₁ ↔ 0 < G z) ∧
                  (z ∈ frontier D₁ ↔ G z = 0) := by
  dsimp only
  let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
    (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
  let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
  obtain ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse,
    hsupport, hD₀, hsides, hout, hpK, hpfront, hnonempty, hHneg, hregneg, hgerms⟩ :=
    P.native_compact_region_with_prescribed_isotopy M hfrontier T k hfree
  let W := U₀ ∪ U₁ ∪ V
  let D₀ := (M.toPlaneComplex.support \ interior K) ∪ (K ∩ {q | (F q).1 ≤ 0})
  have hW : IsOpen W := (hU₀.union hU₁).union hV
  obtain ⟨O, hO, hOc, hOK, hvO⟩ := P.exists_compact_neighborhood_of_vertices_outside hK.isClosed hKW
  have hold (q : Plane) (hq : q ∉ K) : q ∈ D₀ ↔ q ∈ closure (inside P.carrier) := by
    rw [← hsupport]
    exact hout q hq
  have hgood (q : Plane) (hq : q ∈ frontier D₀) (hqW : q ∈ W) :
      ∃ (N : Set Plane) (G : Plane → ℝ), IsOpen N ∧ q ∈ N ∧
        ContDiff ℝ ∞ G ∧ fderiv ℝ G q ≠ 0 ∧
        ∀ z ∈ N, (z ∈ D₀ ↔ 0 ≤ G z) ∧
          (z ∈ interior D₀ ↔ 0 < G z) ∧ (z ∈ frontier D₀ ↔ G z = 0) := by
    obtain ⟨N, G, hN, hqN, _, hG, hGreg, _, hGside⟩ := hgerms q ⟨hq, hqW⟩
    exact ⟨N, G, hN, hqN, hG, hGreg q hqN, hGside⟩
  obtain ⟨D₁, V₁, hD₁, hV₁, hKV₁, hV₁W, heq, houtO, hregular⟩ :=
    P.exists_relative_compact_rounding hD₀ hK.isClosed hW hKW hO hvO hold hgood
  have hprescribed (q : Plane) (hq : q ∈ V₁) :
      (q ∈ D₁ ↔ (F q).1 ≤ 0) ∧
      (q ∈ interior D₁ ↔ (F q).1 < 0) ∧
      (q ∈ frontier D₁ ↔ (F q).1 = 0) :=
    ⟨(heq q hq).1.trans (hsides q (hV₁W hq)).1,
      (heq q hq).2.1.trans (hsides q (hV₁W hq)).2.1,
      (heq q hq).2.2.trans (hsides q (hV₁W hq)).2.2⟩
  have hpD₁ : p ∈ frontier D₁ :=
    (heq p (hKV₁ (interior_subset hpK))).2.2.mpr hpfront
  refine ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse,
    hsupport, hD₀, hsides, hout, hpK, hpfront, hnonempty, hHneg, hregneg, hgerms,
    O, V₁, D₁, hO, hOc, hOK, hvO, hD₁, hV₁, hKV₁, hV₁W, heq, houtO, ?_,
    hprescribed, hpD₁, ⟨p, hpD₁⟩, hregular⟩
  intro q hq
  have hqK : q ∉ K := fun h => hq (Or.inl h)
  have hqO : q ∉ O := fun h => hq (Or.inr h)
  exact (houtO q hqO).1.trans (hout q hqK)

end Schoenflies

end

section

open Set
open scoped ContDiff Manifold Topology

namespace Diffeomorph

private theorem fderiv_comp_symm_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃ₘ[ℝ] E) {G : E → ℝ} (hG : ContDiff ℝ ∞ G)
    {p : E} (hp : fderiv ℝ G p ≠ 0) : fderiv ℝ (G ∘ e.symm) (e p) ≠ 0 := by
  intro hz
  have hc := fderiv_comp p
    ((hG.comp e.symm.contDiff).differentiable (by simp)).differentiableAt
    (e.contDiff.differentiable (by simp)).differentiableAt
  have he : (G ∘ e.symm) ∘ e = G := by
    funext q
    simp only [Function.comp_apply, Diffeomorph.symm_apply_apply]
  rw [he, hz, ContinuousLinearMap.zero_comp] at hc
  exact hp hc

private theorem regular_frontier_image
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : E ≃ₘ[ℝ] E) {D : Set E}
    (hD : ∀ p ∈ frontier D, ∃ (N : Set E) (G : E → ℝ),
      IsOpen N ∧ p ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
      ∀ q ∈ N, (q ∈ D ↔ 0 ≤ G q) ∧
        (q ∈ interior D ↔ 0 < G q) ∧ (q ∈ frontier D ↔ G q = 0)) :
    ∀ p ∈ frontier (e '' D), ∃ (N : Set E) (G : E → ℝ),
      IsOpen N ∧ p ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G p ≠ 0 ∧
      ∀ q ∈ N, (q ∈ e '' D ↔ 0 ≤ G q) ∧
        (q ∈ interior (e '' D) ↔ 0 < G q) ∧
        (q ∈ frontier (e '' D) ↔ G q = 0) := by
  have hi : interior (e '' D) = e '' interior D :=
    (e.toHomeomorph.image_interior D).symm
  have hf : frontier (e '' D) = e '' frontier D :=
    (e.toHomeomorph.image_frontier D).symm
  have hm (A : Set E) (q : E) : q ∈ e '' A ↔ e.symm q ∈ A := by
    exact Set.mem_image_equiv
  intro p hp
  obtain ⟨N, G, hN, hpN, hG, hreg, hsides⟩ := hD (e.symm p) ((hm _ p).mp (hf ▸ hp))
  refine ⟨e.symm ⁻¹' N, G ∘ e.symm, hN.preimage e.symm.continuous,
    hpN, hG.comp e.symm.contDiff, ?_, ?_⟩
  · simpa only [Diffeomorph.apply_symm_apply] using e.fderiv_comp_symm_ne_zero hG hreg
  · intro q hq
    rw [hi, hf, hm D q, hm (interior D) q, hm (frontier D) q]
    exact hsides (e.symm q) hq

end Diffeomorph

end

section

open Set

namespace Homeomorph

private theorem image_region_sides
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) {D V : Set X} {F : X → ℝ} {G : Y → ℝ}
    (hD : ∀ p ∈ V, (p ∈ D ↔ F p ≤ 0) ∧
      (p ∈ interior D ↔ F p < 0) ∧ (p ∈ frontier D ↔ F p = 0))
    (hF : ∀ p ∈ e '' V, (G p = 0 ↔ F (e.symm p) = 0) ∧
      (G p < 0 ↔ F (e.symm p) < 0) ∧ (G p ≤ 0 ↔ F (e.symm p) ≤ 0)) :
    ∀ p ∈ e '' V, (p ∈ e '' D ↔ G p ≤ 0) ∧
      (p ∈ interior (e '' D) ↔ G p < 0) ∧
      (p ∈ frontier (e '' D) ↔ G p = 0) := by
  have hm (A : Set X) (p : Y) : p ∈ e '' A ↔ e.symm p ∈ A :=
    Set.mem_image_equiv
  intro p hp
  have hd := hD (e.symm p) ((hm V p).mp hp)
  have hf := hF p hp
  rw [← e.image_interior D, ← e.image_frontier D, hm D p,
    hm (interior D) p, hm (frontier D) p]
  exact ⟨hd.1.trans hf.2.2.symm, hd.2.1.trans hf.2.1.symm, hd.2.2.trans hf.1.symm⟩

private theorem image_neighborhood_of_eqOn_compl
    {X : Type*} [TopologicalSpace X] (e : X ≃ₜ X) {K V : Set X}
    (hV : IsOpen V) (hKV : K ⊆ V) (he : EqOn e id Kᶜ) :
    IsOpen (e '' V) ∧ K ⊆ e '' V ∧
      ∀ (D : Set X) p, p ∉ K →
        (p ∈ e '' D ↔ p ∈ D) ∧
        (p ∈ interior (e '' D) ↔ p ∈ interior D) ∧
        (p ∈ frontier (e '' D) ↔ p ∈ frontier D) := by
  have hm (A : Set X) (p : X) : p ∈ e '' A ↔ e.symm p ∈ A :=
    Set.mem_image_equiv
  refine ⟨e.isOpenMap V hV, ?_, ?_⟩
  · intro p hp
    apply (hm V p).mpr
    apply hKV
    by_contra hn
    have hh : e.symm p = p := by
      simpa only [Homeomorph.apply_symm_apply, id_eq] using (he hn).symm
    exact hn (hh.symm ▸ hp)
  · intro D p hp
    have hh : e.symm p = p := by
      calc
        e.symm p = e.symm (e p) := congrArg e.symm (he hp).symm
        _ = p := e.symm_apply_apply p
    rw [← e.image_interior D, ← e.image_frontier D, hm D p,
      hm (interior D) p, hm (frontier D) p, hh]
    exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

end Homeomorph

end

section

open Set

namespace Homeomorph

private theorem image_region_sides_outside_interior
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (e : X ≃ₜ X) {K : Set X} (he : EqOn e id Kᶜ) :
    ∀ (D : Set X) p, p ∉ interior K →
      (p ∈ e '' D ↔ p ∈ D) ∧
      (p ∈ interior (e '' D) ↔ p ∈ interior D) ∧
      (p ∈ frontier (e '' D) ↔ p ∈ frontier D) := by
  have hfix : EqOn e id (interior K)ᶜ := by
    simpa only [closure_compl] using he.closure e.continuous continuous_id
  exact (e.image_neighborhood_of_eqOn_compl isOpen_univ (subset_univ _) hfix).2.2

private theorem image_eq_local_replacement
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (e : X ≃ₜ X) {K D S : Set X} (he : EqOn e id Kᶜ)
    (hS : ∀ p ∈ K, p ∈ e '' D ↔ p ∈ S) :
    e '' D = (D \ interior K) ∪ (K ∩ S) := by
  have hout := e.image_region_sides_outside_interior he
  ext p
  constructor
  · intro hp
    by_cases hpK : p ∈ K
    · exact Or.inr ⟨hpK, (hS p hpK).mp hp⟩
    · have hpI : p ∉ interior K := fun h => hpK (interior_subset h)
      exact Or.inl ⟨(hout D p hpI).1.mp hp, hpI⟩
  · rintro (⟨hpD, hpI⟩ | ⟨hpK, hpS⟩)
    · exact (hout D p hpI).1.mpr hpD
    · exact (hS p hpK).mpr hpS

end Homeomorph

end

section

open scoped ContDiff Manifold Topology

namespace Schoenflies

private theorem PrePolygon.native_image_rounding_with_prescribed_isotopy
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
    ∃ (v₀ v₁ : Plane) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ) (ε : ℝ)
      (U₀ U₁ V : Set Plane) (F : Plane → ℝ × ℝ),
      let s₀ := b.coord 2 v₀ / f₀ v₀
      let s₁ := b.coord 2 v₁ / f₁ v₁
      let A₀ := fun p => s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) - b.coord 2 p
      let A₁ := fun p => s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) - b.coord 2 p
      let B₀ := fun p => f₀ (b 2) / f₀ (b 1) *
        (s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) +
          Real.smoothMax ε (f₀ p) 0 / f₀ (b 2) - b.coord 2 p)
      let B₁ := fun p => f₁ (b 2) / f₁ (b 0) *
        (s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) +
          Real.smoothMax ε (f₁ p) 0 / f₁ (b 2) - b.coord 2 p)
      let H := fun q : ℝ × Plane => (1 - q.1) * (F q.2).1 + q.1 * (F q.2).2
      0 < ε ∧ ContDiff ℝ ∞ F ∧ IsOpen U₀ ∧ IsOpen U₁ ∧ IsOpen V ∧
      b 0 ∈ U₀ ∧ b 1 ∈ U₁ ∧ Disjoint U₀ U₁ ∧
      M.triangleCarrier T.1 ⊆ U₀ ∪ U₁ ∪ V ∧
      segment ℝ (b 0) v₀ ⊆ R ∧ segment ℝ (b 1) v₁ ⊆ R ∧
      f₀ (b 0) = 0 ∧ 0 < f₀ (b 1) ∧ 0 < f₀ (b 2) ∧ f₀ v₀ < 0 ∧
      f₁ (b 1) = 0 ∧ 0 < f₁ (b 0) ∧ 0 < f₁ (b 2) ∧ f₁ v₁ < 0 ∧
      (∀ p ∈ U₀, (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p) ∧
      (∀ p ∈ U₁, (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p) ∧
      Set.EqOn F (fun p => (A₀ p, B₀ p)) U₀ ∧
      Set.EqOn F (fun p => (A₁ p, B₁ p)) U₁ ∧
      Set.EqOn F (fun p => (-b.coord 2 p,
        -Real.smoothMax (1 / 4) (-b.coord 0 p) (-b.coord 1 p))) V ∧
      (∀ p ∈ U₀,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else
            f₀ p / f₀ (b 2))) ∧
      (∀ p ∈ U₁,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else
            f₁ p / f₁ (b 2))) ∧
      (∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => (F q).1) p ≠ 0 ∧
          fderiv ℝ (fun q => (F q).2) p ≠ 0) ∧
      ContDiff ℝ ∞ H ∧
      (∀ t p, deriv (fun s => H (s, p)) t = (F p).2 - (F p).1) ∧
      (∀ p, H (0, p) = (F p).1) ∧
      (∀ p, H (1, p) = (F p).2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => H (t, q)) p ≠ 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀, f₀ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁, f₁ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ p ∈ V, ε < f₀ p ∧ ε < f₁ p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ V, H (t, p) = 0 →
        p ∈ M.triangleCarrier T.1) ∧
      ∃ J : Set Plane, IsCompact J ∧ M.triangleCarrier T.1 ⊆ interior J ∧
        J ⊆ U₀ ∪ U₁ ∪ V ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
          H (t, p) = 0 → deriv (fun u => H (u, p)) t ≠ 0 → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀,
          H (t, p) = 0 → -ε ≤ f₀ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁,
          H (t, p) = 0 → -ε ≤ f₁ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V, H (t, p) = 0 → p ∉ J →
          (p ∈ U₀ ∧ f₀ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₀ ∩ {q | f₀ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₀ (b 2) / f₀ (b 1) * (F q).1) N) ∨
          (p ∈ U₁ ∧ f₁ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₁ ∩ {q | f₁ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₁ (b 2) / f₁ (b 0) * (F q).1) N)) ∧
        (∀ p ∈ V,
          (p ∈ M.toPlaneComplex.support ↔ 0 ≤ b.coord 2 p) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ 0 < b.coord 2 p) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ b.coord 2 p = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ M.toPlaneComplex.support ↔ (F p).1 ≤ 0) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ (F p).1 < 0) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ (F p).1 = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 ≤ 0) ∧
          (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 < 0) ∧
          (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 = 0)) ∧
        ∃ (K : Set Plane) (X : ℝ × Plane → Plane) (Ω : Set (ℝ × Plane))
          (κ : ℝ × Plane → ℝ),
          IsCompact K ∧ J ⊆ interior K ∧ K ⊆ U₀ ∪ U₁ ∪ V ∧
          ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧
          IsOpen Ω ∧ Set.Icc (0 : ℝ) 1 ×ˢ (U₀ ∪ U₁ ∪ V) ⊆ Ω ∧
          Ω ⊆ Set.univ ×ˢ (U₀ ∪ U₁ ∪ V) ∧ ContDiffOn ℝ ∞ κ Ω ∧
          (∀ z ∈ Ω,
            deriv (fun t => H (t, z.2)) z.1 +
              fderiv ℝ (fun y => H (z.1, y)) z.2 (X z) = κ z * H z) ∧
          (∀ t x, x ∉ K → X (t, x) = 0) ∧
          ∃ Φ : ℝ → (Plane ≃ₘ[ℝ] Plane),
            (∀ (hX : ContDiff ℝ ∞ X) (hsX : HasCompactSupport X) (t : ℝ),
              Φ t = Diffeomorph.timeDependentFlow X hX hsX 0 t) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => Φ q.1 q.2) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => (Φ q.1).symm q.2) ∧
            Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
            (∀ t : ℝ, Set.EqOn (Φ t) id Kᶜ ∧ Set.EqOn (Φ t).symm id Kᶜ) ∧
            (∀ t : ℝ, (∀ p, Φ t p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V) ∧
              (∀ p, (Φ t).symm p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              ((F p).1 = 0 ↔ H (t, Φ t p) = 0) ∧
              ((F p).1 < 0 ↔ H (t, Φ t p) < 0) ∧
              ((F p).1 ≤ 0 ↔ H (t, Φ t p) ≤ 0)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              (H (t, p) = 0 ↔ (F ((Φ t).symm p)).1 = 0) ∧
              (H (t, p) < 0 ↔ (F ((Φ t).symm p)).1 < 0) ∧
              (H (t, p) ≤ 0 ↔ (F ((Φ t).symm p)).1 ≤ 0)) ∧
            let D₀ := (M.toPlaneComplex.support \ interior K) ∪
              (K ∩ {p | (F p).1 ≤ 0})
            let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
            M.toPlaneComplex.support = closure (inside P.carrier) ∧
            IsCompact D₀ ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              (q ∈ D₀ ↔ (F q).1 ≤ 0) ∧
              (q ∈ interior D₀ ↔ (F q).1 < 0) ∧
              (q ∈ frontier D₀ ↔ (F q).1 = 0)) ∧
            (∀ q ∉ K, q ∈ D₀ ↔ q ∈ M.toPlaneComplex.support) ∧
            p ∈ interior K ∧ p ∈ frontier D₀ ∧ (frontier D₀).Nonempty ∧
            ContDiff ℝ ∞ (fun q => -(F q).1) ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              fderiv ℝ (fun z => -(F z).1) q ≠ 0) ∧
            (∀ q ∈ frontier D₀ ∩ (U₀ ∪ U₁ ∪ V),
              ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ K ⊆ N ∧ ContDiff ℝ ∞ G ∧
                (∀ z ∈ N, fderiv ℝ G z ≠ 0) ∧
                (∀ z, G z = -(F z).1) ∧
                ∀ z ∈ N, (z ∈ D₀ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₀ ↔ 0 < G z) ∧
                  (z ∈ frontier D₀ ↔ G z = 0)) ∧
            ∃ (O V₁ D₁ : Set Plane),
              IsOpen O ∧ IsCompact (closure O) ∧ closure O ⊆ Kᶜ ∧
              (∀ i : ZMod (m + 3), P.vertex i ∉ U₀ ∪ U₁ ∪ V → P.vertex i ∈ O) ∧
              IsCompact D₁ ∧ IsOpen V₁ ∧ K ⊆ V₁ ∧ V₁ ⊆ U₀ ∪ U₁ ∪ V ∧
              (∀ q ∈ V₁, (q ∈ D₁ ↔ q ∈ D₀) ∧
                (q ∈ interior D₁ ↔ q ∈ interior D₀) ∧
                (q ∈ frontier D₁ ↔ q ∈ frontier D₀)) ∧
              (∀ q ∉ O, (q ∈ D₁ ↔ q ∈ D₀) ∧
                (q ∈ interior D₁ ↔ q ∈ interior D₀) ∧
                (q ∈ frontier D₁ ↔ q ∈ frontier D₀)) ∧
              (∀ q ∉ K ∪ O, q ∈ D₁ ↔ q ∈ M.toPlaneComplex.support) ∧
              (∀ q ∈ V₁, (q ∈ D₁ ↔ (F q).1 ≤ 0) ∧
                (q ∈ interior D₁ ↔ (F q).1 < 0) ∧
                (q ∈ frontier D₁ ↔ (F q).1 = 0)) ∧
              p ∈ frontier D₁ ∧ (frontier D₁).Nonempty ∧
              (∀ q ∈ frontier D₁, ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G q ≠ 0 ∧
                ∀ z ∈ N, (z ∈ D₁ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₁ ↔ 0 < G z) ∧
                  (z ∈ frontier D₁ ↔ G z = 0)) ∧
              let D₂ := (Φ 1) '' D₁
              let V₂ := (Φ 1) '' V₁
              IsCompact D₂ ∧ IsOpen V₂ ∧ K ⊆ V₂ ∧ V₂ ⊆ U₀ ∪ U₁ ∪ V ∧
              (∀ q ∈ V₂, (q ∈ D₂ ↔ (F q).2 ≤ 0) ∧
                (q ∈ interior D₂ ↔ (F q).2 < 0) ∧
                (q ∈ frontier D₂ ↔ (F q).2 = 0)) ∧
              (∀ q ∉ K, (q ∈ D₂ ↔ q ∈ D₁) ∧
                (q ∈ interior D₂ ↔ q ∈ interior D₁) ∧
                (q ∈ frontier D₂ ↔ q ∈ frontier D₁)) ∧
              (∀ q ∉ K ∪ O, q ∈ D₂ ↔ q ∈ M.toPlaneComplex.support) ∧
              D₂ = (D₁ \ interior K) ∪ (K ∩ {q | (F q).2 ≤ 0}) ∧
              (∀ q ∈ V₂, q ∉ interior J →
                (q ∈ D₂ ↔ q ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
                (q ∈ interior D₂ ↔
                  q ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
                (q ∈ frontier D₂ ↔
                  q ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support)) ∧
              Φ 1 p ∈ frontier D₂ ∧ (frontier D₂).Nonempty ∧
              ∀ q ∈ frontier D₂, ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G q ≠ 0 ∧
                ∀ z ∈ N, (z ∈ D₂ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₂ ↔ 0 < G z) ∧
                  (z ∈ frontier D₂ ↔ G z = 0) := by
  dsimp only
  let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
    (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
  let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
  obtain ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse,
    hsupport, hD₀, hsides, hout, hpK, hpfront, hnonempty, hHneg, hregneg, hgerms,
    O, V₁, D₁, hO, hOc, hOK, hvO, hD₁, hV₁, hKV₁, hV₁W, heqV₁, houtO, hold,
    hprescribed, hpD₁, hnonemptyD₁, hregular⟩ :=
    P.native_global_rounding_with_prescribed_isotopy M hfrontier T k hfree
  let D₂ := (Φ 1) '' D₁
  let V₂ := (Φ 1) '' V₁
  obtain ⟨hV₂, hKV₂, houtside⟩ := (Φ 1).toHomeomorph.image_neighborhood_of_eqOn_compl
    hV₁ hKV₁ (hΦfix 1).1
  have hV₂W : V₂ ⊆ U₀ ∪ U₁ ∪ V := by
    rintro _ ⟨q, hq, rfl⟩
    exact ((hΦW 1).1 q).mpr (hV₁W hq)
  have hsign₂ (q : Plane) (hq : q ∈ V₂) :
      ((F q).2 = 0 ↔ (F ((Φ 1).symm q)).1 = 0) ∧
      ((F q).2 < 0 ↔ (F ((Φ 1).symm q)).1 < 0) ∧
      ((F q).2 ≤ 0 ↔ (F ((Φ 1).symm q)).1 ≤ 0) := by
    have hi := hinverse 1 (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨by norm_num, le_rfl⟩)
      q (hV₂W hq)
    simpa only [sub_self, zero_mul, one_mul, zero_add] using hi
  have hsides₂ := (Φ 1).toHomeomorph.image_region_sides hprescribed hsign₂
  have hliteral : D₂ = (D₁ \ interior K) ∪ (K ∩ {q | (F q).2 ≤ 0}) :=
    (Φ 1).toHomeomorph.image_eq_local_replacement (hΦfix 1).1
      (fun q hq => (hsides₂ q (hKV₂ hq)).1)
  have hretained (q : Plane) (hq : q ∈ V₂) (hqJ : q ∉ interior J) :
      (q ∈ D₂ ↔ q ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
      (q ∈ interior D₂ ↔ q ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
      (q ∈ frontier D₂ ↔ q ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support) := by
    have hraw₂ := hremoved q (hV₂W hq) hqJ
    exact ⟨(hsides₂ q hq).1.trans hraw₂.1.symm,
      (hsides₂ q hq).2.1.trans hraw₂.2.1.symm,
      (hsides₂ q hq).2.2.trans hraw₂.2.2.symm⟩
  have hfront : frontier D₂ = (Φ 1) '' frontier D₁ :=
    ((Φ 1).toHomeomorph.image_frontier D₁).symm
  have hpD₂ : Φ 1 p ∈ frontier D₂ := by
    rw [hfront]
    exact ⟨p, hpD₁, rfl⟩
  refine ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse,
    hsupport, hD₀, hsides, hout, hpK, hpfront, hnonempty, hHneg, hregneg, hgerms,
    O, V₁, D₁, hO, hOc, hOK, hvO, hD₁, hV₁, hKV₁, hV₁W, heqV₁, houtO, hold,
    hprescribed, hpD₁, hnonemptyD₁, hregular,
    hD₁.image (Φ 1).continuous, hV₂, hKV₂, hV₂W, hsides₂, houtside D₁, ?_,
    hliteral, hretained, hpD₂, ⟨Φ 1 p, hpD₂⟩, (Φ 1).regular_frontier_image hregular⟩
  intro q hq
  exact (houtside D₁ q (fun h => hq (Or.inl h))).1.trans (hold q hq)

end Schoenflies

end

section

open scoped Topology

namespace Schoenflies

private theorem mesh_erase_triangle_sides_of_not_mem
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) {p : Plane} (hp : p ∉ M.triangleCarrier T.1) :
    (p ∈ M.toPlaneComplex.support ↔ p ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
    (p ∈ interior M.toPlaneComplex.support ↔
      p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
    (p ∈ frontier M.toPlaneComplex.support ↔
      p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support) := by
  have hclosed : IsClosed (M.triangleCarrier T.1) :=
    (T.1.finite_toSet.image M.position).isClosed_convexHull ℝ
  have hsplit := M.support_eq_eraseTriangle_union_triangleCarrier T.2
  have heq (q : Plane) (hq : q ∉ M.triangleCarrier T.1) :
      q ∈ M.toPlaneComplex.support ↔ q ∈ (M.eraseTriangle T.1).toPlaneComplex.support := by
    rw [hsplit]
    exact or_iff_left hq
  have hs : M.toPlaneComplex.support =ᶠ[𝓝 p] (M.eraseTriangle T.1).toPlaneComplex.support := by
    filter_upwards [hclosed.isOpen_compl.mem_nhds hp] with q hq
    exact propext (heq q hq)
  refine ⟨heq p hp, hs.mem_interior_iff, ?_⟩
  rw [M.toPlaneComplex.isCompact_support.isClosed.frontier_eq,
    (M.eraseTriangle T.1).toPlaneComplex.isCompact_support.isClosed.frontier_eq]
  change (p ∈ M.toPlaneComplex.support ∧ p ∉ interior M.toPlaneComplex.support) ↔
    (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ∧
      p ∉ interior (M.eraseTriangle T.1).toPlaneComplex.support)
  rw [heq p hp, hs.mem_interior_iff]

end Schoenflies

end

section

open scoped ContDiff Topology

namespace Schoenflies

private theorem compact_sublevel_replacement_preserving_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D K W : Set E} {H : E → ℝ} (hD : IsCompact D) (hK : IsCompact K)
    (hW : IsOpen W) (hKW : K ⊆ W) (hH : Continuous H)
    (hreg : ∀ p ∈ W, H p = 0 → fderiv ℝ H p ≠ 0)
    (heq : ∀ p ∈ W \ interior K, p ∈ D ↔ H p ≤ 0) :
    let E₀ := (D \ interior K) ∪ (K ∩ {p | H p ≤ 0})
    IsCompact E₀ ∧
      (∀ p ∈ W, (p ∈ E₀ ↔ H p ≤ 0) ∧
        (p ∈ interior E₀ ↔ H p < 0) ∧ (p ∈ frontier E₀ ↔ H p = 0)) ∧
      (∀ p ∉ K, (p ∈ E₀ ↔ p ∈ D) ∧
        (p ∈ interior E₀ ↔ p ∈ interior D) ∧
        (p ∈ frontier E₀ ↔ p ∈ frontier D)) := by
  have hneg : ∀ p ∈ W, -H p = 0 → fderiv ℝ (fun q => -H q) p ≠ 0 := by
    intro p hp hz
    simpa only [fderiv_fun_neg, neg_ne_zero] using hreg p hp (neg_eq_zero.mp hz)
  obtain ⟨hc, hs, ho⟩ := compact_region_replace_preserving_germ (H := fun p => -H p)
    hD hK hW hKW hH.neg
    hneg (fun p hp => by simpa only [neg_nonneg] using heq p hp)
  have hc' : IsCompact ((D \ interior K) ∪ (K ∩ {p | H p ≤ 0})) := by
    simpa only [neg_nonneg] using hc
  refine ⟨hc', ?_, ?_⟩
  · intro p hp
    simpa only [neg_nonneg, neg_pos, neg_eq_zero] using hs p hp
  · exact region_sides_of_open_local_eq hD.isClosed hc'.isClosed hK.isClosed.isOpen_compl
      (fun p hp => by simpa only [neg_nonneg] using ho p hp)

private theorem matched_erased_region_of_prescribed_germs
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (T : M.Triangle) {J K W O V₂ D₁ D₂ : Set Plane} {F : Plane → ℝ × ℝ}
    (hK : IsCompact K) (hW : IsOpen W) (hJK : J ⊆ interior K) (hKW : K ⊆ W)
    (hTK : M.triangleCarrier T.1 ⊆ K) (hF : ContDiff ℝ ∞ F)
    (hreg : ∀ p ∈ W, (F p).2 = 0 → fderiv ℝ (fun q => (F q).2) p ≠ 0)
    (hremoved : ∀ p ∈ W, p ∉ interior J →
      (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 ≤ 0))
    (hKV₂ : K ⊆ V₂) (hV₂W : V₂ ⊆ W) (hOK : O ⊆ Kᶜ)
    (hsides₂ : ∀ p ∈ V₂, (p ∈ D₂ ↔ (F p).2 ≤ 0) ∧
      (p ∈ interior D₂ ↔ (F p).2 < 0) ∧ (p ∈ frontier D₂ ↔ (F p).2 = 0))
    (houtside : ∀ p ∉ K, (p ∈ D₂ ↔ p ∈ D₁) ∧
      (p ∈ interior D₂ ↔ p ∈ interior D₁) ∧
      (p ∈ frontier D₂ ↔ p ∈ frontier D₁))
    (houter : ∀ p ∉ O,
      (p ∈ D₁ ↔ p ∈ (M.toPlaneComplex.support \ interior K) ∪ (K ∩ {q | (F q).1 ≤ 0})) ∧
      (p ∈ interior D₁ ↔
        p ∈ interior ((M.toPlaneComplex.support \ interior K) ∪ (K ∩ {q | (F q).1 ≤ 0}))) ∧
      (p ∈ frontier D₁ ↔
        p ∈ frontier ((M.toPlaneComplex.support \ interior K) ∪ (K ∩ {q | (F q).1 ≤ 0})))) :
    let E₀ := ((M.eraseTriangle T.1).toPlaneComplex.support \ interior K) ∪
      (K ∩ {q | (F q).2 ≤ 0})
    IsCompact E₀ ∧
      (∀ p ∈ W, (p ∈ E₀ ↔ (F p).2 ≤ 0) ∧
        (p ∈ interior E₀ ↔ (F p).2 < 0) ∧
        (p ∈ frontier E₀ ↔ (F p).2 = 0)) ∧
      (∀ p ∉ K,
        (p ∈ E₀ ↔ p ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
        (p ∈ interior E₀ ↔ p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
        (p ∈ frontier E₀ ↔ p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support)) ∧
      (∀ p ∈ V₂, (p ∈ D₂ ↔ p ∈ E₀) ∧
        (p ∈ interior D₂ ↔ p ∈ interior E₀) ∧
        (p ∈ frontier D₂ ↔ p ∈ frontier E₀)) ∧
      (∀ p ∉ O, (p ∈ D₂ ↔ p ∈ E₀) ∧
        (p ∈ interior D₂ ↔ p ∈ interior E₀) ∧
        (p ∈ frontier D₂ ↔ p ∈ frontier E₀)) ∧
      D₂ = (E₀ \ O) ∪ (D₁ ∩ O) := by
  let D₀ := (M.toPlaneComplex.support \ interior K) ∪ (K ∩ {q | (F q).1 ≤ 0})
  let E₀ := ((M.eraseTriangle T.1).toPlaneComplex.support \ interior K) ∪
    (K ∩ {q | (F q).2 ≤ 0})
  have hD₀ : IsCompact D₀ :=
    (M.toPlaneComplex.isCompact_support.diff isOpen_interior).union
      (hK.inter_right (isClosed_le hF.fst.continuous continuous_const))
  have hraw₀ := region_sides_of_open_local_eq M.toPlaneComplex.isCompact_support.isClosed
    hD₀.isClosed hK.isClosed.isOpen_compl (by
      intro p hp
      change p ∉ K at hp
      have hpI : p ∉ interior K := fun hi => hp (interior_subset hi)
      simp only [D₀, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff,
        hp, hpI, not_false_eq_true, and_true, false_and, or_false])
  obtain ⟨hE₀, hsignE, hrawE⟩ := compact_sublevel_replacement_preserving_germ
    (M.eraseTriangle T.1).toPlaneComplex.isCompact_support hK hW hKW hF.snd.continuous
    hreg (fun p hp => hremoved p hp.1 (fun hj => hp.2 (hJK (interior_subset hj))))
  have hnear (p : Plane) (hp : p ∈ V₂) :
      (p ∈ D₂ ↔ p ∈ E₀) ∧ (p ∈ interior D₂ ↔ p ∈ interior E₀) ∧
        (p ∈ frontier D₂ ↔ p ∈ frontier E₀) := by
    have hd := hsides₂ p hp
    have he := hsignE p (hV₂W hp)
    exact ⟨hd.1.trans he.1.symm, hd.2.1.trans he.2.1.symm, hd.2.2.trans he.2.2.symm⟩
  have hout (p : Plane) (hp : p ∉ O) :
      (p ∈ D₂ ↔ p ∈ E₀) ∧ (p ∈ interior D₂ ↔ p ∈ interior E₀) ∧
        (p ∈ frontier D₂ ↔ p ∈ frontier E₀) := by
    by_cases hpK : p ∈ K
    · exact hnear p (hKV₂ hpK)
    have hd := houtside p hpK
    have ho := houter p hp
    have ha := hraw₀ p hpK
    have hb := mesh_erase_triangle_sides_of_not_mem M T (fun ht => hpK (hTK ht))
    have he := hrawE p hpK
    exact ⟨hd.1.trans (ho.1.trans (ha.1.trans (hb.1.trans he.1.symm))),
      hd.2.1.trans (ho.2.1.trans (ha.2.1.trans (hb.2.1.trans he.2.1.symm))),
      hd.2.2.trans (ho.2.2.trans (ha.2.2.trans (hb.2.2.trans he.2.2.symm)))⟩
  refine ⟨hE₀, hsignE, hrawE, hnear, hout, ?_⟩
  ext p
  by_cases hpO : p ∈ O
  · have he := (houtside p (hOK hpO)).1
    simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, hpO,
      not_true_eq_false, and_false, false_or, and_true]
    exact he
  · simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, hpO,
      not_false_eq_true, and_true, and_false, or_false]
    exact (hout p hpO).1

end Schoenflies

end

section

open scoped ContDiff Manifold Topology

namespace Schoenflies

theorem PrePolygon.exists_prescribed_rounding_isotopy_of_one_edge_free_triangle
    {m : ℕ} (P : PrePolygon m)
    (M : LeanEval.Topology.ClassificationOfSurfaces.Moise.TriangleMesh)
    (hfrontier : frontier M.toPlaneComplex.support = P.carrier)
    (T : M.Triangle) (k : Fin 3) (hfree : M.IsOneEdgeFreeTriangle T k) :
    let b := LeanEval.Topology.ClassificationOfSurfaces.Moise.affineBasisOfTriangle
      (M.freeTriangleOrder T k) (M.freeTriangleOrder_affineIndependent T k)
    let R := closure (P.carrier \ segment ℝ (b 0) (b 1))
    ∃ (v₀ v₁ : Plane) (f₀ f₁ : Plane →ᵃ[ℝ] ℝ) (ε : ℝ)
      (U₀ U₁ V : Set Plane) (F : Plane → ℝ × ℝ),
      let s₀ := b.coord 2 v₀ / f₀ v₀
      let s₁ := b.coord 2 v₁ / f₁ v₁
      let A₀ := fun p => s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) - b.coord 2 p
      let A₁ := fun p => s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) - b.coord 2 p
      let B₀ := fun p => f₀ (b 2) / f₀ (b 1) *
        (s₀ * (f₀ p - Real.smoothMax ε (f₀ p) 0) +
          Real.smoothMax ε (f₀ p) 0 / f₀ (b 2) - b.coord 2 p)
      let B₁ := fun p => f₁ (b 2) / f₁ (b 0) *
        (s₁ * (f₁ p - Real.smoothMax ε (f₁ p) 0) +
          Real.smoothMax ε (f₁ p) 0 / f₁ (b 2) - b.coord 2 p)
      let H := fun q : ℝ × Plane => (1 - q.1) * (F q.2).1 + q.1 * (F q.2).2
      0 < ε ∧ ContDiff ℝ ∞ F ∧ IsOpen U₀ ∧ IsOpen U₁ ∧ IsOpen V ∧
      b 0 ∈ U₀ ∧ b 1 ∈ U₁ ∧ Disjoint U₀ U₁ ∧
      M.triangleCarrier T.1 ⊆ U₀ ∪ U₁ ∪ V ∧
      segment ℝ (b 0) v₀ ⊆ R ∧ segment ℝ (b 1) v₁ ⊆ R ∧
      f₀ (b 0) = 0 ∧ 0 < f₀ (b 1) ∧ 0 < f₀ (b 2) ∧ f₀ v₀ < 0 ∧
      f₁ (b 1) = 0 ∧ 0 < f₁ (b 0) ∧ 0 < f₁ (b 2) ∧ f₁ v₁ < 0 ∧
      (∀ p ∈ U₀, (1 : ℝ) / 4 < b.coord 0 p - b.coord 1 p) ∧
      (∀ p ∈ U₁, (1 : ℝ) / 4 < b.coord 1 p - b.coord 0 p) ∧
      Set.EqOn F (fun p => (A₀ p, B₀ p)) U₀ ∧
      Set.EqOn F (fun p => (A₁ p, B₁ p)) U₁ ∧
      Set.EqOn F (fun p => (-b.coord 2 p,
        -Real.smoothMax (1 / 4) (-b.coord 0 p) (-b.coord 1 p))) V ∧
      (∀ p ∈ U₀,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else f₀ p / f₀ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₀ p < 0 then b.coord 2 v₀ / f₀ v₀ * f₀ p else
            f₀ p / f₀ (b 2))) ∧
      (∀ p ∈ U₁,
        (p ∈ M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ≤ b.coord 2 p) ∧
        (p ∈ interior M.toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) < b.coord 2 p) ∧
        (p ∈ frontier M.toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else 0) ∧
        (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) ≤
            b.coord 2 p) ∧
        (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔
          (if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else f₁ p / f₁ (b 2)) <
            b.coord 2 p) ∧
        (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔
          b.coord 2 p = if f₁ p < 0 then b.coord 2 v₁ / f₁ v₁ * f₁ p else
            f₁ p / f₁ (b 2))) ∧
      (∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => (F q).1) p ≠ 0 ∧
          fderiv ℝ (fun q => (F q).2) p ≠ 0) ∧
      ContDiff ℝ ∞ H ∧
      (∀ t p, deriv (fun s => H (s, p)) t = (F p).2 - (F p).1) ∧
      (∀ p, H (0, p) = (F p).1) ∧
      (∀ p, H (1, p) = (F p).2) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
        fderiv ℝ (fun q => H (t, q)) p ≠ 0) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀, f₀ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁, f₁ p ≤ -ε → H (t, p) = 0 →
        (F p).1 = 0 ∧ (F p).2 = 0 ∧ (∀ u : ℝ, H (u, p) = 0) ∧
          (∀ u : ℝ, deriv (fun s => H (s, p)) u = 0)) ∧
      (∀ p ∈ V, ε < f₀ p ∧ ε < f₁ p) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ V, H (t, p) = 0 →
        p ∈ M.triangleCarrier T.1) ∧
      ∃ J : Set Plane, IsCompact J ∧ M.triangleCarrier T.1 ⊆ interior J ∧
        J ⊆ U₀ ∪ U₁ ∪ V ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
          H (t, p) = 0 → deriv (fun u => H (u, p)) t ≠ 0 → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀,
          H (t, p) = 0 → -ε ≤ f₀ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₁,
          H (t, p) = 0 → -ε ≤ f₁ p → p ∈ interior J) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V, H (t, p) = 0 → p ∉ J →
          (p ∈ U₀ ∧ f₀ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₀ ∩ {q | f₀ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₀ (b 2) / f₀ (b 1) * (F q).1) N) ∨
          (p ∈ U₁ ∧ f₁ p < -ε ∧ ∃ N : Set Plane,
            IsOpen N ∧ p ∈ N ∧ N ⊆ U₁ ∩ {q | f₁ q < -ε} ∧
              Set.EqOn (fun q => (F q).2) (fun q => f₁ (b 2) / f₁ (b 0) * (F q).1) N)) ∧
        (∀ p ∈ V,
          (p ∈ M.toPlaneComplex.support ↔ 0 ≤ b.coord 2 p) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ 0 < b.coord 2 p) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ b.coord 2 p = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ M.toPlaneComplex.support ↔ (F p).1 ≤ 0) ∧
          (p ∈ interior M.toPlaneComplex.support ↔ (F p).1 < 0) ∧
          (p ∈ frontier M.toPlaneComplex.support ↔ (F p).1 = 0)) ∧
        (∀ p ∈ U₀ ∪ U₁ ∪ V, p ∉ interior J →
          (p ∈ (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 ≤ 0) ∧
          (p ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 < 0) ∧
          (p ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support ↔ (F p).2 = 0)) ∧
        ∃ (K : Set Plane) (X : ℝ × Plane → Plane) (Ω : Set (ℝ × Plane))
          (κ : ℝ × Plane → ℝ),
          IsCompact K ∧ J ⊆ interior K ∧ K ⊆ U₀ ∪ U₁ ∪ V ∧
          ContDiff ℝ ∞ X ∧ HasCompactSupport X ∧
          IsOpen Ω ∧ Set.Icc (0 : ℝ) 1 ×ˢ (U₀ ∪ U₁ ∪ V) ⊆ Ω ∧
          Ω ⊆ Set.univ ×ˢ (U₀ ∪ U₁ ∪ V) ∧ ContDiffOn ℝ ∞ κ Ω ∧
          (∀ z ∈ Ω,
            deriv (fun t => H (t, z.2)) z.1 +
              fderiv ℝ (fun y => H (z.1, y)) z.2 (X z) = κ z * H z) ∧
          (∀ t x, x ∉ K → X (t, x) = 0) ∧
          ∃ Φ : ℝ → (Plane ≃ₘ[ℝ] Plane),
            (∀ (hX : ContDiff ℝ ∞ X) (hsX : HasCompactSupport X) (t : ℝ),
              Φ t = Diffeomorph.timeDependentFlow X hX hsX 0 t) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => Φ q.1 q.2) ∧
            ContDiff ℝ ∞ (fun q : ℝ × Plane => (Φ q.1).symm q.2) ∧
            Φ 0 = Diffeomorph.refl 𝓘(ℝ, Plane) Plane ∞ ∧
            (∀ t : ℝ, Set.EqOn (Φ t) id Kᶜ ∧ Set.EqOn (Φ t).symm id Kᶜ) ∧
            (∀ t : ℝ, (∀ p, Φ t p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V) ∧
              (∀ p, (Φ t).symm p ∈ U₀ ∪ U₁ ∪ V ↔ p ∈ U₀ ∪ U₁ ∪ V)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              ((F p).1 = 0 ↔ H (t, Φ t p) = 0) ∧
              ((F p).1 < 0 ↔ H (t, Φ t p) < 0) ∧
              ((F p).1 ≤ 0 ↔ H (t, Φ t p) ≤ 0)) ∧
            (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ p ∈ U₀ ∪ U₁ ∪ V,
              (H (t, p) = 0 ↔ (F ((Φ t).symm p)).1 = 0) ∧
              (H (t, p) < 0 ↔ (F ((Φ t).symm p)).1 < 0) ∧
              (H (t, p) ≤ 0 ↔ (F ((Φ t).symm p)).1 ≤ 0)) ∧
            let D₀ := (M.toPlaneComplex.support \ interior K) ∪
              (K ∩ {p | (F p).1 ≤ 0})
            let p := AffineMap.lineMap (b 0) (b 1) ((1 : ℝ) / 2)
            M.toPlaneComplex.support = closure (inside P.carrier) ∧
            IsCompact D₀ ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              (q ∈ D₀ ↔ (F q).1 ≤ 0) ∧
              (q ∈ interior D₀ ↔ (F q).1 < 0) ∧
              (q ∈ frontier D₀ ↔ (F q).1 = 0)) ∧
            (∀ q ∉ K, q ∈ D₀ ↔ q ∈ M.toPlaneComplex.support) ∧
            p ∈ interior K ∧ p ∈ frontier D₀ ∧ (frontier D₀).Nonempty ∧
            ContDiff ℝ ∞ (fun q => -(F q).1) ∧
            (∀ q ∈ U₀ ∪ U₁ ∪ V,
              fderiv ℝ (fun z => -(F z).1) q ≠ 0) ∧
            (∀ q ∈ frontier D₀ ∩ (U₀ ∪ U₁ ∪ V),
              ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ K ⊆ N ∧ ContDiff ℝ ∞ G ∧
                (∀ z ∈ N, fderiv ℝ G z ≠ 0) ∧
                (∀ z, G z = -(F z).1) ∧
                ∀ z ∈ N, (z ∈ D₀ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₀ ↔ 0 < G z) ∧
                  (z ∈ frontier D₀ ↔ G z = 0)) ∧
            ∃ (O V₁ D₁ : Set Plane),
              IsOpen O ∧ IsCompact (closure O) ∧ closure O ⊆ Kᶜ ∧
              (∀ i : ZMod (m + 3), P.vertex i ∉ U₀ ∪ U₁ ∪ V → P.vertex i ∈ O) ∧
              IsCompact D₁ ∧ IsOpen V₁ ∧ K ⊆ V₁ ∧ V₁ ⊆ U₀ ∪ U₁ ∪ V ∧
              (∀ q ∈ V₁, (q ∈ D₁ ↔ q ∈ D₀) ∧
                (q ∈ interior D₁ ↔ q ∈ interior D₀) ∧
                (q ∈ frontier D₁ ↔ q ∈ frontier D₀)) ∧
              (∀ q ∉ O, (q ∈ D₁ ↔ q ∈ D₀) ∧
                (q ∈ interior D₁ ↔ q ∈ interior D₀) ∧
                (q ∈ frontier D₁ ↔ q ∈ frontier D₀)) ∧
              (∀ q ∉ K ∪ O, q ∈ D₁ ↔ q ∈ M.toPlaneComplex.support) ∧
              (∀ q ∈ V₁, (q ∈ D₁ ↔ (F q).1 ≤ 0) ∧
                (q ∈ interior D₁ ↔ (F q).1 < 0) ∧
                (q ∈ frontier D₁ ↔ (F q).1 = 0)) ∧
              p ∈ frontier D₁ ∧ (frontier D₁).Nonempty ∧
              (∀ q ∈ frontier D₁, ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G q ≠ 0 ∧
                ∀ z ∈ N, (z ∈ D₁ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₁ ↔ 0 < G z) ∧
                  (z ∈ frontier D₁ ↔ G z = 0)) ∧
              let D₂ := (Φ 1) '' D₁
              let V₂ := (Φ 1) '' V₁
              IsCompact D₂ ∧ IsOpen V₂ ∧ K ⊆ V₂ ∧ V₂ ⊆ U₀ ∪ U₁ ∪ V ∧
              (∀ q ∈ V₂, (q ∈ D₂ ↔ (F q).2 ≤ 0) ∧
                (q ∈ interior D₂ ↔ (F q).2 < 0) ∧
                (q ∈ frontier D₂ ↔ (F q).2 = 0)) ∧
              (∀ q ∉ K, (q ∈ D₂ ↔ q ∈ D₁) ∧
                (q ∈ interior D₂ ↔ q ∈ interior D₁) ∧
                (q ∈ frontier D₂ ↔ q ∈ frontier D₁)) ∧
              (∀ q ∉ K ∪ O, q ∈ D₂ ↔ q ∈ M.toPlaneComplex.support) ∧
              D₂ = (D₁ \ interior K) ∪ (K ∩ {q | (F q).2 ≤ 0}) ∧
              (∀ q ∈ V₂, q ∉ interior J →
                (q ∈ D₂ ↔ q ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
                (q ∈ interior D₂ ↔
                  q ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
                (q ∈ frontier D₂ ↔
                  q ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support)) ∧
              Φ 1 p ∈ frontier D₂ ∧ (frontier D₂).Nonempty ∧
              (∀ q ∈ frontier D₂, ∃ (N : Set Plane) (G : Plane → ℝ),
                IsOpen N ∧ q ∈ N ∧ ContDiff ℝ ∞ G ∧ fderiv ℝ G q ≠ 0 ∧
                ∀ z ∈ N, (z ∈ D₂ ↔ 0 ≤ G z) ∧
                  (z ∈ interior D₂ ↔ 0 < G z) ∧
                  (z ∈ frontier D₂ ↔ G z = 0)) ∧
              let E₀ := ((M.eraseTriangle T.1).toPlaneComplex.support \ interior K) ∪
                (K ∩ {q | (F q).2 ≤ 0})
              IsCompact E₀ ∧
              (∀ q ∈ U₀ ∪ U₁ ∪ V, (q ∈ E₀ ↔ (F q).2 ≤ 0) ∧
                (q ∈ interior E₀ ↔ (F q).2 < 0) ∧
                (q ∈ frontier E₀ ↔ (F q).2 = 0)) ∧
              (∀ q ∉ K,
                (q ∈ E₀ ↔ q ∈ (M.eraseTriangle T.1).toPlaneComplex.support) ∧
                (q ∈ interior E₀ ↔ q ∈ interior (M.eraseTriangle T.1).toPlaneComplex.support) ∧
                (q ∈ frontier E₀ ↔ q ∈ frontier (M.eraseTriangle T.1).toPlaneComplex.support)) ∧
              (∀ q ∈ V₂, (q ∈ D₂ ↔ q ∈ E₀) ∧
                (q ∈ interior D₂ ↔ q ∈ interior E₀) ∧
                (q ∈ frontier D₂ ↔ q ∈ frontier E₀)) ∧
              (∀ q ∉ O, (q ∈ D₂ ↔ q ∈ E₀) ∧
                (q ∈ interior D₂ ↔ q ∈ interior E₀) ∧
                (q ∈ frontier D₂ ↔ q ∈ frontier E₀)) ∧
              D₂ = (E₀ \ O) ∪ (D₁ ∩ O) := by
  dsimp only
  obtain ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse,
    hsupport, hD₀, hsides, hout, hpK, hpfront, hnonempty, hHneg, hregneg, hgerms,
    O, V₁, D₁, hO, hOc, hOK, hvO, hD₁, hV₁, hKV₁, hV₁W, heqV₁, houtO, hold,
    hprescribed, hpD₁, hnonemptyD₁, hregular,
    hD₂, hV₂, hKV₂, hV₂W, hsides₂, houtside, hraw₂, hliteral, hretained,
    hpD₂, hnonemptyD₂, hregular₂⟩ :=
    P.native_image_rounding_with_prescribed_isotopy M hfrontier T k hfree
  obtain ⟨hE₀, hsignE, hrawE, hnearE, houtE, hliteralE⟩ :=
    matched_erased_region_of_prescribed_germs M T hK ((hU₀.union hU₁).union hV) hJK hKW
      (fun _ ht => interior_subset (hJK (interior_subset (htriangleJ ht)))) hF
      (fun q hq _ => (hreg q hq).2) (fun q hq hqJ => (hremoved q hq hqJ).1)
      hKV₂ hV₂W (fun _ hq => hOK (subset_closure hq)) hsides₂ houtside houtO
  exact ⟨v₀, v₁, f₀, f₁, ε, U₀, U₁, V, F,
    hε, hF, hU₀, hU₁, hV, hb₀, hb₁, hdisj, hcover, hs₀, hs₁,
    hf₀, hfb, hfc₀, hfv₀, hf₁, hfa, hfc₁, hfv₁, hgap₀, hgap₁,
    he₀, he₁, heV, hgraph₀, hgraph₁, hreg, hH, hderiv, hstart, hend,
    hregH, hstat₀, hstat₁, hposV, hcentral,
    J, hJ, htriangleJ, hJW, hactive, hweak₀, hweak₁, hexterior, hraw, hsign, hremoved,
    K, X, Ω, κ, hK, hJK, hKW, hX, hsX, hΩ, hΩcover, hΩW, hκ, htransport, hXzero,
    Φ, hΦeq, hΦ, hΦinv, hΦzero, hΦfix, hΦW, hforward, hinverse,
    hsupport, hD₀, hsides, hout, hpK, hpfront, hnonempty, hHneg, hregneg, hgerms,
    O, V₁, D₁, hO, hOc, hOK, hvO, hD₁, hV₁, hKV₁, hV₁W, heqV₁, houtO, hold,
    hprescribed, hpD₁, hnonemptyD₁, hregular,
    hD₂, hV₂, hKV₂, hV₂W, hsides₂, houtside, hraw₂, hliteral, hretained,
    hpD₂, hnonemptyD₂, hregular₂,
    hE₀, hsignE, hrawE, hnearE, houtE, hliteralE⟩

end Schoenflies

end
