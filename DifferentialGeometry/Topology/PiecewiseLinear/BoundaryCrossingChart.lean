/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorphOpen
import DifferentialGeometry.Topology.PiecewiseLinear.TransversePlaneNormalForm
import DifferentialGeometry.Topology.PiecewiseLinear.VertexChartTransport
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# Boundary crossing charts in a slab
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem frontier_fst_nonneg :
    frontier {z : ℝ × ℝ × ℝ | 0 ≤ z.1} = {z : ℝ × ℝ × ℝ | z.1 = 0} := by
  change frontier ((Prod.fst : ℝ × ℝ × ℝ → ℝ) ⁻¹' Ici 0) = _
  rw [← isOpenMap_fst.preimage_frontier_eq_frontier_preimage continuous_fst, frontier_Ici]
  rfl

theorem HasPLBoundaryCrossingAt.exists_openPartialHomeomorph_halfSpace
    {M A B W : Set E} {x : E} (hx : HasPLBoundaryCrossingAt M A B x) (hW : W ∈ 𝓝 x) :
    ∃ e : OpenPartialHomeomorph E (ℝ × ℝ × ℝ),
      x ∈ e.source ∧ e.source ⊆ W ∧ e x = 0 ∧
        IsPiecewiseAffineOn e e.source ∧ IsPiecewiseAffineOn e.symm e.target ∧
          e.IsImage M {z | 0 ≤ z.1} ∧ e.IsImage (frontier M) {z | z.1 = 0} ∧
            e.IsImage A {z | z.2.2 = 0 ∧ 0 ≤ z.1} ∧
              e.IsImage B {z | z.2.1 = 0 ∧ 0 ≤ z.1} ∧
                e.IsImage (A ∩ B) {z | z.2 = 0 ∧ 0 ≤ z.1} := by
  obtain ⟨U, V, h, L, hU, hV, hxU, hh, hhx, hnear⟩ := hx.exists_linearEquiv_normalForm
  let φ : E → ℝ × ℝ × ℝ := fun y => L (h y)
  have hV' : IsOpen ((fun y => L y) '' V) :=
    L.toContinuousLinearEquiv.toHomeomorph.isOpenMap V hV
  have hφ : IsPLHomeomorphOn φ U ((fun y => L y) '' V) :=
    hh.trans (isPLHomeomorphOn_linearEquiv L hV)
  have hN : {y | y ∈ U ∧ y ∈ W ∧ (y ∈ M ↔ 0 ≤ (φ y).1) ∧
      (y ∈ A ↔ (φ y).2.2 = 0 ∧ 0 ≤ (φ y).1) ∧
      (y ∈ B ↔ (φ y).2.1 = 0 ∧ 0 ≤ (φ y).1)} ∈ 𝓝 x := by
    filter_upwards [hU.mem_nhds hxU, hW, hnear] with y hyU hyW hy
    exact ⟨hyU, hyW, hy.1, hy.2.1, hy.2.2.1⟩
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp hN
  have hOU : O ⊆ U := fun y hy => (hOsub hy).1
  have hO' : IsOpen (φ '' O) := hφ.isOpen_image_of_isOpen hV' hO hOU
  have hφO := hφ.restrict_isOpen hO hOU hO'
  let e := hφO.toOpenPartialHomeomorph hO hO'
  have hM : e.IsImage M {z | 0 ≤ z.1} := by
    intro y hy
    exact (hOsub hy).2.2.1.symm
  have hBd : e.IsImage (frontier M) {z | z.1 = 0} := by
    simpa only [frontier_fst_nonneg] using hM.frontier
  refine ⟨e, hxO, fun y hy => (hOsub hy).2.1, ?_, hφO.isPiecewiseAffineOn,
    hφO.isPiecewiseAffineOn_invFunOn, hM, hBd, ?_, ?_, ?_⟩
  · change L (h x) = 0
    rw [hhx, map_zero]
  · intro y hy
    exact (hOsub hy).2.2.2.1.symm
  · intro y hy
    exact (hOsub hy).2.2.2.2.symm
  · intro y hy
    change ((φ y).2 = 0 ∧ 0 ≤ (φ y).1) ↔ y ∈ A ∩ B
    rw [mem_inter_iff, (hOsub hy).2.2.2.1, (hOsub hy).2.2.2.2,
      Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
    tauto

theorem HasPLBoundaryCrossingAt.exists_openPartialHomeomorph_slab_left
    {M A B W : Set E} {x : E} (hx : HasPLBoundaryCrossingAt M A B x) (hW : W ∈ 𝓝 x)
    {c : ℝ} (hc : 0 < c) :
    ∃ e : OpenPartialHomeomorph E (ℝ × ℝ × ℝ),
      x ∈ e.source ∧ e.source ⊆ W ∧ e x = 0 ∧
        IsPiecewiseAffineOn e e.source ∧ IsPiecewiseAffineOn e.symm e.target ∧
          (∀ y ∈ e.source, (e y).1 < c) ∧
            e.IsImage M {z | 0 ≤ z.1 ∧ z.1 ≤ c} ∧
              e.IsImage (frontier M) {z | z.1 = 0 ∨ z.1 = c} ∧
                e.IsImage A {z | z.2.2 = 0 ∧ 0 ≤ z.1 ∧ z.1 ≤ c} ∧
                  e.IsImage B {z | z.2.1 = 0 ∧ 0 ≤ z.1 ∧ z.1 ≤ c} ∧
                    e.IsImage (A ∩ B) {z | z.2 = 0 ∧ 0 ≤ z.1 ∧ z.1 ≤ c} := by
  obtain ⟨e, hxe, heW, he0, he, hei, hM, hBd, hA, hB, hAB⟩ :=
    hx.exists_openPartialHomeomorph_halfSpace hW
  have hlt : {y | (e y).1 < c} ∈ 𝓝 x :=
    (e.continuousOn.continuousAt (e.open_source.mem_nhds hxe)).fst.preimage_mem_nhds
      (Iio_mem_nhds (by simpa only [he0, Prod.fst_zero] using hc))
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp hlt
  let e' := e.restrOpen O hO
  have hsrc : e'.source ⊆ e.source := inter_subset_left
  have htgt : e'.target ⊆ e.target := inter_subset_left
  have hbound : ∀ y ∈ e'.source, (e y).1 < c := fun y hy => hOsub hy.2
  refine ⟨e', ⟨hxe, hxO⟩, hsrc.trans heW, he0,
    he.mono e'.open_source hsrc, hei.mono e'.open_target htgt, hbound, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    change (0 ≤ (e y).1 ∧ (e y).1 ≤ c) ↔ y ∈ M
    exact ⟨fun hz => (hM hy.1).mp hz.1,
      fun hz => ⟨(hM hy.1).mpr hz, (hbound y hy).le⟩⟩
  · intro y hy
    change ((e y).1 = 0 ∨ (e y).1 = c) ↔ y ∈ frontier M
    rw [or_iff_left (hbound y hy).ne]
    exact hBd hy.1
  · intro y hy
    change ((e y).2.2 = 0 ∧ 0 ≤ (e y).1 ∧ (e y).1 ≤ c) ↔ y ∈ A
    exact ⟨fun hz => (hA hy.1).mp ⟨hz.1, hz.2.1⟩,
      fun hz => ⟨((hA hy.1).mpr hz).1, ((hA hy.1).mpr hz).2, (hbound y hy).le⟩⟩
  · intro y hy
    change ((e y).2.1 = 0 ∧ 0 ≤ (e y).1 ∧ (e y).1 ≤ c) ↔ y ∈ B
    exact ⟨fun hz => (hB hy.1).mp ⟨hz.1, hz.2.1⟩,
      fun hz => ⟨((hB hy.1).mpr hz).1, ((hB hy.1).mpr hz).2, (hbound y hy).le⟩⟩
  · intro y hy
    change ((e y).2 = 0 ∧ 0 ≤ (e y).1 ∧ (e y).1 ≤ c) ↔ y ∈ A ∩ B
    exact ⟨fun hz => (hAB hy.1).mp ⟨hz.1, hz.2.1⟩,
      fun hz => ⟨((hAB hy.1).mpr hz).1, ((hAB hy.1).mpr hz).2, (hbound y hy).le⟩⟩

theorem HasPLBoundaryCrossingAt.exists_openPartialHomeomorph_slab_right
    {M A B W : Set E} {x : E} (hx : HasPLBoundaryCrossingAt M A B x) (hW : W ∈ 𝓝 x)
    {c : ℝ} (hc : 0 < c) :
    ∃ e : OpenPartialHomeomorph E (ℝ × ℝ × ℝ),
      x ∈ e.source ∧ e.source ⊆ W ∧ e x = (c, 0, 0) ∧
        IsPiecewiseAffineOn e e.source ∧ IsPiecewiseAffineOn e.symm e.target ∧
          (∀ y ∈ e.source, 0 < (e y).1) ∧
            e.IsImage M {z | 0 ≤ z.1 ∧ z.1 ≤ c} ∧
              e.IsImage (frontier M) {z | z.1 = 0 ∨ z.1 = c} ∧
                e.IsImage A {z | z.2.2 = 0 ∧ 0 ≤ z.1 ∧ z.1 ≤ c} ∧
                  e.IsImage B {z | z.2.1 = 0 ∧ 0 ≤ z.1 ∧ z.1 ≤ c} ∧
                    e.IsImage (A ∩ B) {z | z.2 = 0 ∧ 0 ≤ z.1 ∧ z.1 ≤ c} := by
  obtain ⟨e, hxe, heW, he0, he, hei, hlt, hM, hBd, hA, hB, hAB⟩ :=
    hx.exists_openPartialHomeomorph_slab_left hW hc
  let r : (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ) :=
    (Homeomorph.subLeft c).prodCongr (Homeomorph.refl (ℝ × ℝ))
  let R : (ℝ × ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ × ℝ) :=
    (AffineMap.const ℝ (ℝ × ℝ × ℝ) c -
      (LinearMap.fst ℝ ℝ (ℝ × ℝ)).toAffineMap).prod
      (LinearMap.snd ℝ ℝ (ℝ × ℝ)).toAffineMap
  have hr : IsPiecewiseAffineOn r univ :=
    (isPiecewiseAffineOn_of_affine R isOpen_univ).congr fun _ _ => rfl
  have hri : IsPiecewiseAffineOn r.symm univ := by
    refine (isPiecewiseAffineOn_of_affine R isOpen_univ).congr ?_
    intro y _
    change (-y.1 + c, y.2) = (c - y.1, y.2)
    rw [sub_eq_add_neg, add_comm (-y.1) c]
  let e' := e.trans r.toOpenPartialHomeomorph
  have hsource : e'.source = e.source := by
    change e.source ∩ e ⁻¹' univ = e.source
    rw [preimage_univ, inter_univ]
  have he' : IsPiecewiseAffineOn e' e'.source := by
    have hcomp := hr.comp he
    exact hcomp
  have hei' : IsPiecewiseAffineOn e'.symm e'.target := hei.comp hri
  have hinterval (t : ℝ) : (0 ≤ c - t ∧ c - t ≤ c) ↔ (0 ≤ t ∧ t ≤ c) := by
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
  have hends (t : ℝ) : (c - t = 0 ∨ c - t = c) ↔ (t = 0 ∨ t = c) := by
    constructor
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl (by linarith)
  refine ⟨e', hsource.symm ▸ hxe, hsource.symm ▸ heW, ?_, he', hei', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (c - (e x).1, (e x).2) = (c, 0, 0)
    rw [he0]
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero]
    rfl
  · intro y hy
    change 0 < c - (e y).1
    exact sub_pos.mpr (hlt y (hsource ▸ hy))
  · intro y hy
    change (0 ≤ c - (e y).1 ∧ c - (e y).1 ≤ c) ↔ y ∈ M
    rw [hinterval]
    exact hM (hsource ▸ hy)
  · intro y hy
    change (c - (e y).1 = 0 ∨ c - (e y).1 = c) ↔ y ∈ frontier M
    rw [hends]
    exact hBd (hsource ▸ hy)
  · intro y hy
    change ((e y).2.2 = 0 ∧ 0 ≤ c - (e y).1 ∧ c - (e y).1 ≤ c) ↔ y ∈ A
    rw [hinterval]
    exact hA (hsource ▸ hy)
  · intro y hy
    change ((e y).2.1 = 0 ∧ 0 ≤ c - (e y).1 ∧ c - (e y).1 ≤ c) ↔ y ∈ B
    rw [hinterval]
    exact hB (hsource ▸ hy)
  · intro y hy
    change ((e y).2 = 0 ∧ 0 ≤ c - (e y).1 ∧ c - (e y).1 ≤ c) ↔ y ∈ A ∩ B
    rw [hinterval]
    exact hAB (hsource ▸ hy)

theorem HasPLCrossingAt.exists_openPartialHomeomorph_slab_interior
    {M A B W : Set E} {x : E} (hx : HasPLCrossingAt A B x) (hxM : x ∈ interior M)
    (hW : W ∈ 𝓝 x) {c r : ℝ} (hr : 0 < r) (hrc : r < c) :
    ∃ e : OpenPartialHomeomorph E (ℝ × ℝ × ℝ),
      x ∈ e.source ∧ e.source ⊆ W ∧ e x = (r, 0, 0) ∧
        IsPiecewiseAffineOn e e.source ∧ IsPiecewiseAffineOn e.symm e.target ∧
          (∀ y ∈ e.source, 0 < (e y).1 ∧ (e y).1 < c) ∧
            e.IsImage M {z | 0 ≤ z.1 ∧ z.1 ≤ c} ∧
              e.IsImage (frontier M) {z | z.1 = 0 ∨ z.1 = c} ∧
                (∀ y ∈ e.source, y ∈ A → (e y).2.2 = 0) ∧
                  (∀ y ∈ e.source, y ∈ B → (e y).2.1 = 0) := by
  obtain ⟨U, V, h, L, hU, hV, hxU, hh, hhx, hcase⟩ := hx.exists_linearEquiv_normalForm
  have hnear : ∀ᶠ y in 𝓝 x,
      (y ∈ A → (L (h y)).2.2 = 0) ∧ (y ∈ B → (L (h y)).2.1 = 0) := by
    rcases hcase with hc | hc | hc
    · filter_upwards [hc] with y hy
      exact ⟨fun hyA => hy.1.mp hyA, fun hyB => hy.2.mp hyB⟩
    · filter_upwards [hc] with y hy
      exact ⟨fun hyA => hy.1.mp hyA, fun hyB => (hy.2.mp hyB).1⟩
    · filter_upwards [hc] with y hy
      exact ⟨fun hyA => (hy.1.mp hyA).1, fun hyB => hy.2.mp hyB⟩
  let t : (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ) := Homeomorph.addRight (r, 0, 0)
  let φ : E → ℝ × ℝ × ℝ := fun y => t (L (h y))
  have hV' : IsOpen ((fun y => L y) '' V) :=
    L.toContinuousLinearEquiv.toHomeomorph.isOpenMap V hV
  have ht : IsPiecewiseAffineOn t univ :=
    (isPLHomeomorphOn_add_const (r, (0 : ℝ), (0 : ℝ))).isPiecewiseAffineOn
  have hφ : IsPLHomeomorphOn φ U (t '' ((fun y => L y) '' V)) :=
    (hh.trans (isPLHomeomorphOn_linearEquiv L hV)).postcomp_openPartialHomeomorph
      t.toOpenPartialHomeomorph ht (subset_univ _)
  have hφopen : IsOpen (t '' ((fun y => L y) '' V)) := t.isOpenMap _ hV'
  have hφx : φ x = (r, 0, 0) := by
    change L (h x) + (r, 0, 0) = (r, 0, 0)
    rw [hhx, map_zero, zero_add]
  have hcont : ContinuousAt (fun y => (φ y).1) x :=
    (hφ.isPiecewiseAffineOn.continuousOn.continuousAt (hU.mem_nhds hxU)).fst
  have hgt : {y | 0 < (φ y).1} ∈ 𝓝 x :=
    hcont.preimage_mem_nhds (Ioi_mem_nhds (by simpa only [hφx] using hr))
  have hlt : {y | (φ y).1 < c} ∈ 𝓝 x :=
    hcont.preimage_mem_nhds (Iio_mem_nhds (by simpa only [hφx] using hrc))
  have hN : {y | y ∈ U ∧ y ∈ W ∧ y ∈ interior M ∧ 0 < (φ y).1 ∧ (φ y).1 < c ∧
      (y ∈ A → (φ y).2.2 = 0) ∧ (y ∈ B → (φ y).2.1 = 0)} ∈ 𝓝 x := by
    filter_upwards [hU.mem_nhds hxU, hW, isOpen_interior.mem_nhds hxM, hgt, hlt, hnear]
      with y hyU hyW hyM hygt hylt hy
    refine ⟨hyU, hyW, hyM, hygt, hylt, ?_, ?_⟩
    · intro hyA
      change (L (h y)).2.2 + 0 = 0
      rw [hy.1 hyA, zero_add]
    · intro hyB
      change (L (h y)).2.1 + 0 = 0
      rw [hy.2 hyB, zero_add]
  obtain ⟨O, hOsub, hO, hxO⟩ := mem_nhds_iff.mp hN
  have hOU : O ⊆ U := fun y hy => (hOsub hy).1
  have hO' : IsOpen (φ '' O) := hφ.isOpen_image_of_isOpen hφopen hO hOU
  have hφO := hφ.restrict_isOpen hO hOU hO'
  let e := hφO.toOpenPartialHomeomorph hO hO'
  refine ⟨e, hxO, fun y hy => (hOsub hy).2.1, hφx, hφO.isPiecewiseAffineOn,
    hφO.isPiecewiseAffineOn_invFunOn, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun y hy => ⟨(hOsub hy).2.2.2.1, (hOsub hy).2.2.2.2.1⟩
  · intro y hy
    exact iff_of_true ⟨(hOsub hy).2.2.2.1.le, (hOsub hy).2.2.2.2.1.le⟩
      (interior_subset (hOsub hy).2.2.1)
  · intro y hy
    have hnot : y ∉ frontier M :=
      (mem_interior_iff_notMem_frontier (interior_subset (hOsub hy).2.2.1)).mp
        (hOsub hy).2.2.1
    exact iff_of_false (fun hz => hz.elim (hOsub hy).2.2.2.1.ne'
      (hOsub hy).2.2.2.2.1.ne) hnot
  · exact fun y hy => (hOsub hy).2.2.2.2.2.1
  · exact fun y hy => (hOsub hy).2.2.2.2.2.2

end DifferentialGeometry.Topology.PiecewiseLinear
