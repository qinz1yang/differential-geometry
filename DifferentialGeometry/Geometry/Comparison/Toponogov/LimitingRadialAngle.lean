import DifferentialGeometry.Geometry.Comparison.Toponogov.MetricComparisonAngle
import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngleOrder
import DifferentialGeometry.Geometry.Comparison.Toponogov.EuclideanSector
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Order.Filter.Prod
import Mathlib.Topology.Order.Monotone

open Filter Set Topology
open scoped RealInnerProductSpace

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Toponogov

def positiveRectangleValues (L₁ L₂ : ℝ) (f : ℝ → ℝ → ℝ) : Set ℝ :=
  {z | ∃ s ∈ Ioc (0 : ℝ) L₁, ∃ t ∈ Ioc (0 : ℝ) L₂, z = f s t}

def CoordinatewiseNonincreasingOn (L₁ L₂ : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  (∀ ⦃s₁ s₂ t : ℝ⦄, s₁ ∈ Ioc (0 : ℝ) L₁ → s₂ ∈ Ioc (0 : ℝ) L₁ →
      t ∈ Ioc (0 : ℝ) L₂ → s₁ ≤ s₂ → f s₂ t ≤ f s₁ t) ∧
    ∀ ⦃s t₁ t₂ : ℝ⦄, s ∈ Ioc (0 : ℝ) L₁ → t₁ ∈ Ioc (0 : ℝ) L₂ →
      t₂ ∈ Ioc (0 : ℝ) L₂ → t₁ ≤ t₂ → f s t₂ ≤ f s t₁

theorem tendsto_sSup_positiveRectangle {L₁ L₂ : ℝ} {f : ℝ → ℝ → ℝ}
    (hL₁ : 0 < L₁) (hL₂ : 0 < L₂)
    (hmono : CoordinatewiseNonincreasingOn L₁ L₂ f)
    (hbdd : BddAbove (positiveRectangleValues L₁ L₂ f)) :
    Tendsto (fun p : ℝ × ℝ ↦ f p.1 p.2) (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 (sSup (positiveRectangleValues L₁ L₂ f))) := by
  have hne : (positiveRectangleValues L₁ L₂ f).Nonempty := by
    exact ⟨f L₁ L₂, L₁, ⟨hL₁, le_rfl⟩, L₂, ⟨hL₂, le_rfl⟩, rfl⟩
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro q hq
    obtain ⟨z, hz, hqz⟩ := exists_lt_of_lt_csSup hne hq
    rcases hz with ⟨s, hs, t, ht, rfl⟩
    rw [Filter.eventually_prod_iff]
    refine ⟨fun u ↦ u ∈ Ioc (0 : ℝ) s, Ioc_mem_nhdsGT hs.1,
      fun v ↦ v ∈ Ioc (0 : ℝ) t, Ioc_mem_nhdsGT ht.1, ?_⟩
    intro u hu v hv
    have huL : u ∈ Ioc (0 : ℝ) L₁ := ⟨hu.1, hu.2.trans hs.2⟩
    have hvL : v ∈ Ioc (0 : ℝ) L₂ := ⟨hv.1, hv.2.trans ht.2⟩
    exact hqz.trans_le <| (hmono.1 huL hs ht hu.2).trans
      (hmono.2 huL hvL ht hv.2)
  · intro q hq
    rw [Filter.eventually_prod_iff]
    refine ⟨fun s ↦ s ∈ Ioc (0 : ℝ) L₁, Ioc_mem_nhdsGT hL₁,
      fun t ↦ t ∈ Ioc (0 : ℝ) L₂, Ioc_mem_nhdsGT hL₂, ?_⟩
    intro s hs t ht
    exact (le_csSup hbdd ⟨s, hs, t, ht, rfl⟩).trans_lt hq


def IsRadialFamily {X : Type*} [MetricSpace X] (E : X) {ι : Type*}
    (L : ι → ℝ) (γ : ι → ℝ → X) : Prop :=
  ∀ i s, s ∈ Ioc (0 : ℝ) (L i) → dist E (γ i s) = s


def radialComparisonAngle {X : Type*} [MetricSpace X] {ι : Type*}
    (γ : ι → ℝ → X) (i j : ι) (s t : ℝ) : ℝ :=
  comparisonAngle s t (dist (γ i s) (γ j t))

def limitingRadialAngle {X : Type*} [MetricSpace X] {ι : Type*}
    (L : ι → ℝ) (γ : ι → ℝ → X) (i j : ι) : ℝ :=
  sSup (positiveRectangleValues (L i) (L j) (radialComparisonAngle γ i j))

theorem radialComparisonAngle_sideInequalities {X : Type*} [MetricSpace X]
    {ι : Type*} {E : X} {L : ι → ℝ} {γ : ι → ℝ → X}
    (hrad : IsRadialFamily E L γ) {i j : ι} {s t : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) (L i)) (ht : t ∈ Ioc (0 : ℝ) (L j)) :
    |s - t| ≤ dist (γ i s) (γ j t) ∧
      dist (γ i s) (γ j t) ≤ s + t := by
  simpa only [hrad i s hs, hrad j t ht] using
    (metricComparisonAngle_sideInequalities (γ i s) E (γ j t))


theorem radialComparisonAngle_mem_Icc {X : Type*} [MetricSpace X] {ι : Type*}
    (γ : ι → ℝ → X) (i j : ι) (s t : ℝ) :
    radialComparisonAngle γ i j s t ∈ Icc (0 : ℝ) Real.pi :=
  comparisonAngle_mem_Icc _ _ _

theorem positiveRectangleValues_radial_nonempty {X : Type*} [MetricSpace X]
    {ι : Type*} {L : ι → ℝ} (γ : ι → ℝ → X) {i j : ι}
    (hLi : 0 < L i) (hLj : 0 < L j) :
    (positiveRectangleValues (L i) (L j)
      (radialComparisonAngle γ i j)).Nonempty := by
  exact ⟨radialComparisonAngle γ i j (L i) (L j), L i, ⟨hLi, le_rfl⟩,
    L j, ⟨hLj, le_rfl⟩, rfl⟩


theorem positiveRectangleValues_radial_bddAbove {X : Type*} [MetricSpace X]
    {ι : Type*} (L : ι → ℝ) (γ : ι → ℝ → X) (i j : ι) :
    BddAbove (positiveRectangleValues (L i) (L j)
      (radialComparisonAngle γ i j)) := by
  refine ⟨Real.pi, ?_⟩
  rintro z ⟨s, hs, t, ht, rfl⟩
  exact (radialComparisonAngle_mem_Icc γ i j s t).2


theorem limitingRadialAngle_mem_Icc {X : Type*} [MetricSpace X] {ι : Type*}
    {L : ι → ℝ} (γ : ι → ℝ → X) {i j : ι}
    (hLi : 0 < L i) (hLj : 0 < L j) :
    limitingRadialAngle L γ i j ∈ Icc (0 : ℝ) Real.pi := by
  constructor
  · exact (radialComparisonAngle_mem_Icc γ i j (L i) (L j)).1.trans
      (le_csSup (positiveRectangleValues_radial_bddAbove L γ i j)
        ⟨L i, ⟨hLi, le_rfl⟩, L j, ⟨hLj, le_rfl⟩, rfl⟩)
  · exact csSup_le (positiveRectangleValues_radial_nonempty γ hLi hLj) <| by
      rintro z ⟨s, hs, t, ht, rfl⟩
      exact (radialComparisonAngle_mem_Icc γ i j s t).2

theorem tendsto_limitingRadialAngle {X : Type*} [MetricSpace X] {ι : Type*}
    {L : ι → ℝ} (γ : ι → ℝ → X) {i j : ι}
    (hLi : 0 < L i) (hLj : 0 < L j)
    (hmono : CoordinatewiseNonincreasingOn (L i) (L j)
      (radialComparisonAngle γ i j)) :
    Tendsto (fun p : ℝ × ℝ ↦ radialComparisonAngle γ i j p.1 p.2)
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
      (𝓝 (limitingRadialAngle L γ i j)) := by
  exact tendsto_sSup_positiveRectangle hLi hLj hmono
    (positiveRectangleValues_radial_bddAbove L γ i j)


theorem limitingRadialAngle_comm {X : Type*} [MetricSpace X] {ι : Type*}
    (L : ι → ℝ) (γ : ι → ℝ → X) (i j : ι) :
    limitingRadialAngle L γ i j = limitingRadialAngle L γ j i := by
  apply congrArg sSup
  ext z
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    refine ⟨t, ht, s, hs, ?_⟩
    simp only [radialComparisonAngle, comparisonAngle_comm, dist_comm]
  · rintro ⟨t, ht, s, hs, rfl⟩
    refine ⟨s, hs, t, ht, ?_⟩
    simp only [radialComparisonAngle, comparisonAngle_comm, dist_comm]

private theorem euclideanPlane_cosineLaw (O X Y : EuclideanPlane) :
    dist X Y ^ 2 = dist O X ^ 2 + dist O Y ^ 2 -
      2 * dist O X * dist O Y *
        Real.cos (InnerProductGeometry.angle (X - O) (Y - O)) := by
  have h :=
    InnerProductGeometry.norm_sub_sq_eq_norm_sq_add_norm_sq_sub_two_mul_norm_mul_norm_mul_cos_angle
      (X - O) (Y - O)
  rw [show X - O - (Y - O) = X - Y by abel] at h
  simpa only [pow_two, dist_eq_norm, norm_sub_rev] using h

private theorem limitingRadialAngle_triangle_fin3 {X : Type*} [MetricSpace X]
    (E : X) (L : Fin 3 → ℝ) (γ : Fin 3 → ℝ → X)
    (hL : ∀ i, 0 < L i) (hrad : IsRadialFamily E L γ)
    (hmono : ∀ i j, i ≠ j → CoordinatewiseNonincreasingOn (L i) (L j)
      (radialComparisonAngle γ i j)) :
    limitingRadialAngle L γ 0 2 ≤
      limitingRadialAngle L γ 0 1 + limitingRadialAngle L γ 1 2 := by
  let A : ℝ := limitingRadialAngle L γ 0 1
  let B : ℝ := limitingRadialAngle L γ 1 2
  have hA := limitingRadialAngle_mem_Icc γ (hL 0) (hL 1)
  have hB := limitingRadialAngle_mem_Icc γ (hL 1) (hL 2)
  have h02 := limitingRadialAngle_mem_Icc γ (hL 0) (hL 2)
  change limitingRadialAngle L γ 0 2 ≤ A + B
  by_cases hlarge : Real.pi ≤ A + B
  · exact h02.2.trans hlarge
  · have hsum : A + B < Real.pi := lt_of_not_ge hlarge
    obtain ⟨O, X₀, Y, Z₀, hOX, hOZ, hOYpos, hOYle, hYseg,
        hangleA, hangleB⟩ :=
      exists_euclideanSector_interpolation hA.1 hB.1 hsum
    have hne02 := positiveRectangleValues_radial_nonempty γ (hL 0) (hL 2)
    apply csSup_le hne02
    rintro z ⟨s, hs, t, ht, rfl⟩
    let ρ : ℝ := min (min s t) (L 1)
    have hρpos : 0 < ρ := by
      dsimp only [ρ]
      exact lt_min (lt_min hs.1 ht.1) (hL 1)
    have hρs : ρ ≤ s := le_trans (min_le_left _ _) (min_le_left _ _)
    have hρt : ρ ≤ t := le_trans (min_le_left _ _) (min_le_right _ _)
    have hρL₁ : ρ ≤ L 1 := min_le_right _ _
    have hρ0 : ρ ∈ Ioc (0 : ℝ) (L 0) :=
      ⟨hρpos, hρs.trans hs.2⟩
    have hρ2 : ρ ∈ Ioc (0 : ℝ) (L 2) :=
      ⟨hρpos, hρt.trans ht.2⟩
    have hρYpos : 0 < ρ * dist O Y := mul_pos hρpos hOYpos
    have hρYleρ : ρ * dist O Y ≤ ρ :=
      mul_le_of_le_one_right hρpos.le hOYle
    have hρY1 : ρ * dist O Y ∈ Ioc (0 : ℝ) (L 1) :=
      ⟨hρYpos, hρYleρ.trans hρL₁⟩
    have hΘ01 : radialComparisonAngle γ 0 1 ρ (ρ * dist O Y) ≤ A := by
      exact le_csSup (positiveRectangleValues_radial_bddAbove L γ 0 1)
        ⟨ρ, hρ0, ρ * dist O Y, hρY1, rfl⟩
    have hΘ12 : radialComparisonAngle γ 1 2 (ρ * dist O Y) ρ ≤ B := by
      exact le_csSup (positiveRectangleValues_radial_bddAbove L γ 1 2)
        ⟨ρ * dist O Y, hρY1, ρ, hρ2, rfl⟩
    have hsides01 := radialComparisonAngle_sideInequalities hrad hρ0 hρY1
    have hsides12 := radialComparisonAngle_sideInequalities hrad hρY1 hρ2
    have hd01sq :
        dist (γ 0 ρ) (γ 1 (ρ * dist O Y)) ^ 2 ≤
          ρ ^ 2 + (ρ * dist O Y) ^ 2 -
            2 * ρ * (ρ * dist O Y) * Real.cos A := by
      exact sq_le_cos_of_comparisonAngle_le hρpos hρYpos hsides01.1 hsides01.2
        hA.2 hΘ01
    have hd12sq :
        dist (γ 1 (ρ * dist O Y)) (γ 2 ρ) ^ 2 ≤
          (ρ * dist O Y) ^ 2 + ρ ^ 2 -
            2 * (ρ * dist O Y) * ρ * Real.cos B := by
      exact sq_le_cos_of_comparisonAngle_le hρYpos hρpos hsides12.1 hsides12.2
        hB.2 hΘ12
    have hmodelXY := euclideanPlane_cosineLaw O X₀ Y
    rw [hOX, hangleA] at hmodelXY
    have hmodelYZ := euclideanPlane_cosineLaw O Y Z₀
    rw [hOZ, hangleB] at hmodelYZ
    have hscaledXY :
        (ρ * dist X₀ Y) ^ 2 =
          ρ ^ 2 + (ρ * dist O Y) ^ 2 -
            2 * ρ * (ρ * dist O Y) * Real.cos A := by
      rw [mul_pow, hmodelXY]
      ring
    have hscaledYZ :
        (ρ * dist Y Z₀) ^ 2 =
          (ρ * dist O Y) ^ 2 + ρ ^ 2 -
            2 * (ρ * dist O Y) * ρ * Real.cos B := by
      rw [mul_pow, hmodelYZ]
      ring
    have hd01 : dist (γ 0 ρ) (γ 1 (ρ * dist O Y)) ≤ ρ * dist X₀ Y := by
      apply (sq_le_sq₀ dist_nonneg (mul_nonneg hρpos.le dist_nonneg)).1
      simpa only [hscaledXY] using hd01sq
    have hd12 : dist (γ 1 (ρ * dist O Y)) (γ 2 ρ) ≤ ρ * dist Y Z₀ := by
      apply (sq_le_sq₀ dist_nonneg (mul_nonneg hρpos.le dist_nonneg)).1
      simpa only [hscaledYZ] using hd12sq
    have hsegment : dist X₀ Y + dist Y Z₀ = dist X₀ Z₀ :=
      dist_add_dist_of_mem_segment hYseg
    have hd02 : dist (γ 0 ρ) (γ 2 ρ) ≤ ρ * dist X₀ Z₀ := by
      calc
        dist (γ 0 ρ) (γ 2 ρ) ≤
            dist (γ 0 ρ) (γ 1 (ρ * dist O Y)) +
              dist (γ 1 (ρ * dist O Y)) (γ 2 ρ) := dist_triangle _ _ _
        _ ≤ ρ * dist X₀ Y + ρ * dist Y Z₀ := add_le_add hd01 hd12
        _ = ρ * dist X₀ Z₀ := by rw [← mul_add, hsegment]
    let C : ℝ := InnerProductGeometry.angle (X₀ - O) (Z₀ - O)
    have hC0 : 0 ≤ C := InnerProductGeometry.angle_nonneg _ _
    have hCpi : C ≤ Real.pi := InnerProductGeometry.angle_le_pi _ _
    have hmodelXZ := euclideanPlane_cosineLaw O X₀ Z₀
    rw [hOX, hOZ] at hmodelXZ
    have hscaledXZ :
        (ρ * dist X₀ Z₀) ^ 2 =
          ρ ^ 2 + ρ ^ 2 - 2 * ρ * ρ * Real.cos C := by
      rw [mul_pow, hmodelXZ]
      ring
    have hd02sq :
        dist (γ 0 ρ) (γ 2 ρ) ^ 2 ≤
          ρ ^ 2 + ρ ^ 2 - 2 * ρ * ρ * Real.cos C := by
      rw [← hscaledXZ]
      exact (sq_le_sq₀ dist_nonneg (mul_nonneg hρpos.le dist_nonneg)).2 hd02
    have hΘρ : radialComparisonAngle γ 0 2 ρ ρ ≤ C := by
      exact comparisonAngle_le_of_sq_le_cos hρpos hρpos hC0 hCpi hd02sq
    have hC : C ≤ A + B := by
      dsimp only [C]
      calc
        InnerProductGeometry.angle (X₀ - O) (Z₀ - O) ≤
            InnerProductGeometry.angle (X₀ - O) (Y - O) +
              InnerProductGeometry.angle (Y - O) (Z₀ - O) :=
          InnerProductGeometry.angle_le_angle_add_angle _ _ _
        _ = A + B := by rw [hangleA, hangleB]
    have hΘsmall : radialComparisonAngle γ 0 2 s t ≤
        radialComparisonAngle γ 0 2 ρ ρ := by
      have hm := hmono 0 2 (by decide)
      exact (hm.1 hρ0 hs ht hρs).trans (hm.2 hρ0 hρ2 ht hρt)
    exact hΘsmall.trans (hΘρ.trans hC)

theorem limitingRadialAngle_triangle {X : Type*} [MetricSpace X] {ι : Type*}
    (E : X) (L : ι → ℝ) (γ : ι → ℝ → X)
    (hL : ∀ i, 0 < L i) (hrad : IsRadialFamily E L γ)
    (hmono : ∀ i j, i ≠ j → CoordinatewiseNonincreasingOn (L i) (L j)
      (radialComparisonAngle γ i j))
    {i j k : ι} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    limitingRadialAngle L γ i k ≤
      limitingRadialAngle L γ i j + limitingRadialAngle L γ j k := by
  let L' : Fin 3 → ℝ := ![L i, L j, L k]
  let γ' : Fin 3 → ℝ → X := ![γ i, γ j, γ k]
  have hL' : ∀ n : Fin 3, 0 < L' n := by
    intro n
    fin_cases n
    · exact hL i
    · exact hL j
    · exact hL k
  have hrad' : IsRadialFamily E L' γ' := by
    intro n s hs
    fin_cases n
    · exact hrad i s hs
    · exact hrad j s hs
    · exact hrad k s hs
  have hpair : ∀ n m : Fin 3, n ≠ m →
      CoordinatewiseNonincreasingOn (L' n) (L' m) (radialComparisonAngle γ' n m) := by
    intro n m hnm
    fin_cases n <;> fin_cases m
    · exact absurd rfl hnm
    · exact hmono i j hij
    · exact hmono i k hik
    · exact hmono j i (Ne.symm hij)
    · exact absurd rfl hnm
    · exact hmono j k hjk
    · exact hmono k i (Ne.symm hik)
    · exact hmono k j (Ne.symm hjk)
    · exact absurd rfl hnm
  have h := limitingRadialAngle_triangle_fin3 E L' γ' hL' hrad' hpair
  have e₀₂ : limitingRadialAngle L' γ' (0 : Fin 3) (2 : Fin 3) =
      limitingRadialAngle L γ i k := by
    simp only [L', γ', limitingRadialAngle, positiveRectangleValues, radialComparisonAngle]
    simp
  have e₀₁ : limitingRadialAngle L' γ' (0 : Fin 3) (1 : Fin 3) =
      limitingRadialAngle L γ i j := by
    simp only [L', γ', limitingRadialAngle, positiveRectangleValues, radialComparisonAngle]
    simp
  have e₁₂ : limitingRadialAngle L' γ' (1 : Fin 3) (2 : Fin 3) =
      limitingRadialAngle L γ j k := by
    simp only [L', γ', limitingRadialAngle, positiveRectangleValues, radialComparisonAngle]
    simp
  rwa [e₀₂, e₀₁, e₁₂] at h

theorem limitingRadialAngle_package {X : Type*} [MetricSpace X]
    (E : X) (L : Fin 3 → ℝ) (γ : Fin 3 → ℝ → X)
    (hL : ∀ i, 0 < L i) (hrad : IsRadialFamily E L γ)
    (hmono : ∀ i j, i ≠ j → CoordinatewiseNonincreasingOn (L i) (L j)
      (radialComparisonAngle γ i j)) :
    (∀ i j, i ≠ j → limitingRadialAngle L γ i j ∈ Icc (0 : ℝ) Real.pi) ∧
      (∀ i j, i ≠ j →
        Tendsto (fun p : ℝ × ℝ ↦ radialComparisonAngle γ i j p.1 p.2)
          (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ))
          (𝓝 (limitingRadialAngle L γ i j))) ∧
      (∀ i j, i ≠ j →
        limitingRadialAngle L γ i j = limitingRadialAngle L γ j i) ∧
      limitingRadialAngle L γ 0 2 ≤
        limitingRadialAngle L γ 0 1 + limitingRadialAngle L γ 1 2 := by
  refine ⟨fun i j _ ↦ limitingRadialAngle_mem_Icc γ (hL i) (hL j), ?_,
    fun i j _ ↦ limitingRadialAngle_comm L γ i j, ?_⟩
  · exact fun i j hij ↦
      tendsto_limitingRadialAngle γ (hL i) (hL j) (hmono i j hij)
  · exact limitingRadialAngle_triangle_fin3 E L γ hL hrad hmono

end DifferentialGeometry.Toponogov
