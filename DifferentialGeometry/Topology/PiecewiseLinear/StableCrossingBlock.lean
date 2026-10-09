/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def blockBox (r tlo : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | |p.1| ≤ r ∧ |p.2.1| ≤ r ∧ p.2.2 ∈ Icc tlo r}

def blockHalfPlane (tlo : ℝ) : Set (ℝ × ℝ) :=
  {p | tlo = 0 → 0 ≤ p.2}

section Ambient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]

def chartBlock (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ) : Set M :=
  ec.source ∩ ⇑ec ⁻¹' (⇑A ⁻¹' blockBox r tlo)

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem chartBlock_mono_of_half (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) {r tlo : ℝ} (hr : 0 ≤ r) (ht : tlo ≤ 0) :
    chartBlock ec A (r / 2) (tlo / 2) ⊆ chartBlock ec A r tlo := by
  intro x hx
  obtain ⟨hxs, hxb⟩ := hx
  refine ⟨hxs, ?_⟩
  simp only [mem_preimage, blockBox, mem_ofPred_eq, mem_Icc] at hxb ⊢
  exact ⟨hxb.1.trans (by linarith), hxb.2.1.trans (by linarith),
    by linarith [hxb.2.2.1], by linarith [hxb.2.2.2]⟩

def innerChartBlock (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ) : Set M :=
  chartBlock ec A (r / 2) (tlo / 2)

noncomputable def blockSheetProjA (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (f : EuclideanSpace ℝ (Fin 2) → M) :
    EuclideanSpace ℝ (Fin 2) → ℝ × ℝ :=
  fun x => ((A (ec (f x))).2.1, (A (ec (f x))).2.2)

noncomputable def blockSheetProjB (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (f : EuclideanSpace ℝ (Fin 2) → M) :
    EuclideanSpace ℝ (Fin 2) → ℝ × ℝ :=
  fun x => ((A (ec (f x))).1, (A (ec (f x))).2.2)

def IsStableCrossingBlock (f : EuclideanSpace ℝ (Fin 2) → M)
    (S : Set (EuclideanSpace ℝ (Fin 2)))
    (ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ) (BdM : Set M)
    (A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ) (r tlo : ℝ)
    (SA SB : Set (EuclideanSpace ℝ (Fin 2))) (a b : ℝ × ℝ → ℝ) (La Lb η : ℝ) : Prop :=
  0 < r ∧ 0 < η ∧ 0 ≤ La ∧ 0 ≤ Lb ∧ La * Lb ≤ 1 - η ∧
    IsCompact (closure (chartBlock ec A r tlo)) ∧
    closure (chartBlock ec A r tlo) ⊆ ec.source ∧
    ((tlo = -r ∧ Disjoint (chartBlock ec A r tlo) BdM) ∨
        (tlo = 0 ∧ (∀ z, (A z).2.2 = ℓ z) ∧
          ∀ x ∈ SA ∪ SB, (x ∈ frontier S ↔ (A (ec (f x))).2.2 = 0))) ∧
    S ∩ f ⁻¹' chartBlock ec A r tlo = SA ∪ SB ∧ Disjoint SA SB ∧
    (∀ x ∈ SA, (A (ec (f x))).1 = a ((A (ec (f x))).2.1, (A (ec (f x))).2.2)) ∧
    (∀ x ∈ SB, (A (ec (f x))).2.1 = b ((A (ec (f x))).1, (A (ec (f x))).2.2)) ∧
    IsPLHomeomorphOn (blockSheetProjA ec A f) SA (blockSheetProjA ec A f '' SA) ∧
    IsPLHomeomorphOn (blockSheetProjB ec A f) SB (blockSheetProjB ec A f '' SB) ∧
    (∀ x ∈ SA, f x ∈ innerChartBlock ec A r tlo → SA ∈ 𝓝[S] x ∧
      blockSheetProjA ec A f '' SA ∈ 𝓝[blockHalfPlane tlo] (blockSheetProjA ec A f x)) ∧
    (∀ x ∈ SB, f x ∈ innerChartBlock ec A r tlo → SB ∈ 𝓝[S] x ∧
      blockSheetProjB ec A f '' SB ∈ 𝓝[blockHalfPlane tlo] (blockSheetProjB ec A f x)) ∧
    (∀ v v' t : ℝ, |a (v, t) - a (v', t)| ≤ La * |v - v'|) ∧
    (∀ u u' t : ℝ, |b (u, t) - b (u', t)| ≤ Lb * |u - u'|) ∧
    IsPiecewiseAffineOn a univ ∧ IsPiecewiseAffineOn b univ

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem IsStableCrossingBlock.margin_pos {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) : 0 < η :=
  h.2.1

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem sheets_nonempty_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) {y : M}
    (hy : y ∈ doublePointSet f S) (hyB : y ∈ chartBlock ec A r tlo) :
    (SA ∩ f ⁻¹' {y}).Nonempty ∧ (SB ∩ f ⁻¹' {y}).Nonempty := by
  obtain ⟨-, -, -, -, -, -, -, -, hpre, -, -, -, hplA, hplB, -, -, -, -, -, -⟩ := h
  obtain ⟨x, hxS, z, hzS, hxz, hxy, hzy⟩ := hy
  have hfeq : f x = f z := by rw [hxy, hzy]
  have hxmem : x ∈ SA ∪ SB := by
    rw [← hpre]
    exact ⟨hxS, by simp only [mem_preimage, hxy]; exact hyB⟩
  have hzmem : z ∈ SA ∪ SB := by
    rw [← hpre]
    exact ⟨hzS, by simp only [mem_preimage, hzy]; exact hyB⟩
  have hnotA : ¬(x ∈ SA ∧ z ∈ SA) := by
    rintro ⟨hxA, hzA⟩
    exact hxz (hplA.bijOn.injOn hxA hzA (by simp only [blockSheetProjA, hfeq]))
  have hnotB : ¬(x ∈ SB ∧ z ∈ SB) := by
    rintro ⟨hxB, hzB⟩
    exact hxz (hplB.bijOn.injOn hxB hzB (by simp only [blockSheetProjB, hfeq]))
  rcases hxmem with hxA | hxB
  · rcases hzmem with hzA | hzB
    · exact absurd ⟨hxA, hzA⟩ hnotA
    · exact ⟨⟨x, hxA, hxy⟩, ⟨z, hzB, hzy⟩⟩
  · rcases hzmem with hzA | hzB
    · exact ⟨⟨z, hzA, hzy⟩, ⟨x, hxB, hxy⟩⟩
    · exact absurd ⟨hxB, hzB⟩ hnotB

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem eq_of_snd_eq_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η) {y z : M}
    (hy : y ∈ doublePointSet f S) (hyB : y ∈ chartBlock ec A r tlo)
    (hz : z ∈ doublePointSet f S) (hzB : z ∈ chartBlock ec A r tlo)
    (ht : (A (ec y)).2.2 = (A (ec z)).2.2) : y = z := by
  have hgraph : ∀ p : M, p ∈ doublePointSet f S → p ∈ chartBlock ec A r tlo →
      (A (ec p)).1 = a ((A (ec p)).2.1, (A (ec p)).2.2) ∧
        (A (ec p)).2.1 = b ((A (ec p)).1, (A (ec p)).2.2) := by
    intro p hp hpB
    obtain ⟨⟨x, hxA, hxp⟩, ⟨x', hx'B, hx'p⟩⟩ :=
      sheets_nonempty_of_isStableCrossingBlock h hp hpB
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hgA, hgB, -, -, -, -, -, -, -, -⟩ := h
    have hfx : f x = p := hxp
    have hfx' : f x' = p := hx'p
    exact ⟨by simpa only [hfx] using hgA x hxA, by simpa only [hfx'] using hgB x' hx'B⟩
  obtain ⟨hay, hby⟩ := hgraph y hy hyB
  obtain ⟨haz, hbz⟩ := hgraph z hz hzB
  obtain ⟨-, hη, hLa, hLb, hmar, -, -, -, -, -, -, -, -, -, -, -, hLipa, hLipb, -, -⟩ := h
  have hP : (0 : ℝ) ≤ |(A (ec y)).1 - (A (ec z)).1| := abs_nonneg _
  have hQ : (0 : ℝ) ≤ |(A (ec y)).2.1 - (A (ec z)).2.1| := abs_nonneg _
  have h1 : |(A (ec y)).1 - (A (ec z)).1| ≤ La * |(A (ec y)).2.1 - (A (ec z)).2.1| := by
    rw [hay, haz, ht]
    exact hLipa _ _ _
  have h2 : |(A (ec y)).2.1 - (A (ec z)).2.1| ≤ Lb * |(A (ec y)).1 - (A (ec z)).1| := by
    rw [hby, hbz, ht]
    exact hLipb _ _ _
  have h3 : La * |(A (ec y)).2.1 - (A (ec z)).2.1| ≤ La * (Lb * |(A (ec y)).1 - (A (ec z)).1|) :=
    mul_le_mul_of_nonneg_left h2 hLa
  have h5 : La * Lb * |(A (ec y)).1 - (A (ec z)).1| ≤ (1 - η) * |(A (ec y)).1 - (A (ec z)).1| :=
    mul_le_mul_of_nonneg_right hmar hP
  have hu : (A (ec y)).1 = (A (ec z)).1 := by
    have hzero : |(A (ec y)).1 - (A (ec z)).1| = 0 := by
      by_contra hne
      have hpos : 0 < |(A (ec y)).1 - (A (ec z)).1| := lt_of_le_of_ne hP (Ne.symm hne)
      nlinarith [h1, h3, h5, hpos, hη]
    exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
  have hv : (A (ec y)).2.1 = (A (ec z)).2.1 := by
    have hzero : |(A (ec y)).2.1 - (A (ec z)).2.1| = 0 := by
      have : |(A (ec y)).2.1 - (A (ec z)).2.1| ≤ 0 := by
        have hu0 : |(A (ec y)).1 - (A (ec z)).1| = 0 := by
          rw [hu, sub_self, abs_zero]
        nlinarith [h2, hu0]
      exact le_antisymm this hQ
    exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
  have hAeq : A (ec y) = A (ec z) := Prod.ext_iff.2 ⟨hu, Prod.ext_iff.2 ⟨hv, ht⟩⟩
  have hecyz : ec y = ec z := by
    have := congrArg (⇑A.symm) hAeq
    simpa only [AffineEquiv.symm_apply_apply] using this
  exact ec.injOn hyB.1 hzB.1 hecyz

omit [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] in
theorem eq_of_mem_wall_of_isStableCrossingBlock {f : EuclideanSpace ℝ (Fin 2) → M}
    {S : Set (EuclideanSpace ℝ (Fin 2))}
    {ec : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    {ℓ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ} {BdM Wl : Set M}
    {A : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] ℝ × ℝ × ℝ} {r tlo : ℝ}
    {SA SB : Set (EuclideanSpace ℝ (Fin 2))} {a b : ℝ × ℝ → ℝ} {La Lb η : ℝ}
    (h : IsStableCrossingBlock f S ec ℓ BdM A r tlo SA SB a b La Lb η)
    (hwall : ∀ x ∈ chartBlock ec A r tlo, x ∈ Wl ↔ (A (ec x)).2.2 = 0) {y z : M}
    (hy : y ∈ doublePointSet f S) (hyB : y ∈ chartBlock ec A r tlo) (hyW : y ∈ Wl)
    (hz : z ∈ doublePointSet f S) (hzB : z ∈ chartBlock ec A r tlo) (hzW : z ∈ Wl) : y = z :=
  eq_of_snd_eq_of_isStableCrossingBlock h hy hyB hz hzB
    (((hwall y hyB).1 hyW).trans ((hwall z hzB).1 hzW).symm)

end Ambient

end DifferentialGeometry.Topology.PiecewiseLinear
