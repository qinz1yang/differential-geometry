/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homeomorph.SphereExtension
import DifferentialGeometry.Topology.Simplex.NormedBall
import DifferentialGeometry.Topology.PiecewiseLinear.LocalSurfaceLink
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "P2" => EuclideanSpace ℝ (Fin 2)

local notation "P3" => EuclideanSpace ℝ (Fin 3)

section Cells

variable {X : Type*} [TopologicalSpace X]

theorem homeomorphClosedBall_mem_iff {n : ℕ} {C I : Set X}
    (φ : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 ≃ₜ C)
    (hI : I = Subtype.val '' (φ '' {q | ‖(q : EuclideanSpace ℝ (Fin n))‖ < 1}))
    (q : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (φ q : X) ∈ I ↔ ‖(q : EuclideanSpace ℝ (Fin n))‖ < 1 := by
  rw [hI]
  constructor
  · rintro ⟨w, ⟨q', hq', rfl⟩, hw⟩
    rwa [φ.injective (Subtype.ext hw)] at hq'
  · intro hq
    exact ⟨φ q, ⟨q, hq, rfl⟩, rfl⟩

theorem exists_homeomorph_closedBall_eq_on_sphere {A Aint B Bint : Set X}
    (α : Metric.closedBall (0 : P2) 1 ≃ₜ A)
    (hα : Aint = Subtype.val '' (α '' {q | ‖(q : P2)‖ < 1}))
    (β : Metric.closedBall (0 : P2) 1 ≃ₜ B)
    (hβ : Bint = Subtype.val '' (β '' {q | ‖(q : P2)‖ < 1}))
    (hBA : B \ Bint = A \ Aint) :
    ∃ β' : Metric.closedBall (0 : P2) 1 ≃ₜ B,
      Bint = Subtype.val '' (β' '' {q | ‖(q : P2)‖ < 1}) ∧
        ∀ q : Metric.closedBall (0 : P2) 1, ‖(q : P2)‖ = 1 → (β' q : X) = α q := by
  have hαb := homeomorphClosedBall_mem_iff α hα
  have hβb := homeomorphClosedBall_mem_iff β hβ
  have hle : ∀ q : Metric.closedBall (0 : P2) 1, ‖(q : P2)‖ ≤ 1 :=
    fun q => mem_closedBall_zero_iff.mp q.2
  have hαS : ∀ q : Metric.closedBall (0 : P2) 1, ‖(q : P2)‖ = 1 → (α q : X) ∈ B \ Bint := by
    intro q hq
    rw [hBA]
    exact ⟨(α q).2, fun h => ((hαb q).mp h).ne hq⟩
  have hβS : ∀ q : Metric.closedBall (0 : P2) 1, ‖(q : P2)‖ = 1 → (β q : X) ∈ A \ Aint := by
    intro q hq
    rw [← hBA]
    exact ⟨(β q).2, fun h => ((hβb q).mp h).ne hq⟩
  let ι : Metric.sphere (0 : P2) 1 → Metric.closedBall (0 : P2) 1 :=
    Set.inclusion Metric.sphere_subset_closedBall
  have hι : ∀ s, ‖((ι s : Metric.closedBall (0 : P2) 1) : P2)‖ = 1 :=
    fun s => mem_sphere_zero_iff_norm.mp s.2
  let a : Metric.sphere (0 : P2) 1 → Metric.closedBall (0 : P2) 1 := fun s =>
    β.symm ⟨α (ι s), (hαS (ι s) (hι s)).1⟩
  let b : Metric.sphere (0 : P2) 1 → Metric.closedBall (0 : P2) 1 := fun s =>
    α.symm ⟨β (ι s), (hβS (ι s) (hι s)).1⟩
  have ha : ∀ s, (β (a s) : X) = α (ι s) := fun s => by
    simp only [a, Homeomorph.apply_symm_apply]
  have hb : ∀ s, (α (b s) : X) = β (ι s) := fun s => by
    simp only [b, Homeomorph.apply_symm_apply]
  have han : ∀ s, ‖(a s : P2)‖ = 1 := by
    intro s
    refine le_antisymm (hle _) (not_lt.mp fun h => ?_)
    have h1 := (hβb (a s)).mpr h
    rw [ha s] at h1
    exact (hαS (ι s) (hι s)).2 h1
  have hbn : ∀ s, ‖(b s : P2)‖ = 1 := by
    intro s
    refine le_antisymm (hle _) (not_lt.mp fun h => ?_)
    have h1 := (hαb (b s)).mpr h
    rw [hb s] at h1
    exact (hβS (ι s) (hι s)).2 h1
  have hac : Continuous a := β.symm.continuous.comp
    ((continuous_subtype_val.comp (α.continuous.comp (continuous_inclusion _))).subtype_mk _)
  have hbc : Continuous b := α.symm.continuous.comp
    ((continuous_subtype_val.comp (β.continuous.comp (continuous_inclusion _))).subtype_mk _)
  let fwd : Metric.sphere (0 : P2) 1 → Metric.sphere (0 : P2) 1 := fun s =>
    ⟨a s, mem_sphere_zero_iff_norm.mpr (han s)⟩
  let bwd : Metric.sphere (0 : P2) 1 → Metric.sphere (0 : P2) 1 := fun s =>
    ⟨b s, mem_sphere_zero_iff_norm.mpr (hbn s)⟩
  have hιf : ∀ s, ι (fwd s) = a s := fun s => Subtype.ext rfl
  have hιb : ∀ s, ι (bwd s) = b s := fun s => Subtype.ext rfl
  have hinj : ∀ s t, ι s = ι t → s = t := fun s t h =>
    Subtype.ext (congrArg (fun z : Metric.closedBall (0 : P2) 1 => (z : P2)) h)
  let f : Metric.sphere (0 : P2) 1 ≃ₜ Metric.sphere (0 : P2) 1 :=
    { toFun := fwd
      invFun := bwd
      left_inv := fun s => by
        apply hinj
        have h1 : (α (b (fwd s)) : X) = α (ι s) := by rw [hb, hιf, ha]
        rw [hιb, α.injective (Subtype.ext h1)]
      right_inv := fun s => by
        apply hinj
        have h1 : (β (a (bwd s)) : X) = β (ι s) := by rw [ha, hιb, hb]
        rw [hιf, β.injective (Subtype.ext h1)]
      continuous_toFun := (continuous_subtype_val.comp hac).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp hbc).subtype_mk _ }
  let e := DifferentialGeometry.Topology.closedBallHomeomorphExtension f
  have hen : ∀ q : Metric.closedBall (0 : P2) 1, ‖((e q : Metric.closedBall (0 : P2) 1) : P2)‖ =
      ‖(q : P2)‖ := fun q => DifferentialGeometry.Topology.norm_sphereRadialHomeomorph f q
  refine ⟨e.trans β, ?_, ?_⟩
  · ext y
    constructor
    · intro hy
      have hyB : y ∈ B := by
        rw [hβ] at hy
        obtain ⟨w, -, rfl⟩ := hy
        exact w.2
      obtain ⟨q, hq⟩ := (e.trans β).surjective ⟨y, hyB⟩
      refine ⟨(e.trans β) q, ⟨q, ?_, rfl⟩, by rw [hq]⟩
      have h1 : (β (e q) : X) ∈ Bint := by
        change ((e.trans β) q : X) ∈ Bint
        rw [hq]
        exact hy
      have h2 := (hβb _).mp h1
      rw [hen] at h2
      exact h2
    · rintro ⟨w, ⟨q, hq, rfl⟩, rfl⟩
      refine (hβb (e q)).mpr ?_
      rw [hen]
      exact hq
  · intro q hq
    let s : Metric.sphere (0 : P2) 1 := ⟨q, mem_sphere_zero_iff_norm.mpr hq⟩
    have hqs : q = ι s := Subtype.ext rfl
    change (β (e q) : X) = α q
    have h1 : e (ι s) = a s := by
      have h2 := DifferentialGeometry.Topology.closedBallHomeomorphExtension_apply_sphere f s
      exact h2
    rw [hqs, h1, ha]

theorem IsTopologicalCellWithInterior.isTopologicalSphere_union [T2Space X]
    {A Aint B Bint : Set X} (hA : IsTopologicalCellWithInterior 2 A Aint)
    (hB : IsTopologicalCellWithInterior 2 B Bint) (hAB : A ∩ B = A \ Aint)
    (hBA : B \ Bint = A \ Aint) : IsTopologicalSphere 2 (A ∪ B) := by
  classical
  obtain ⟨α, hα⟩ := hA
  obtain ⟨β₀, hβ₀⟩ := hB
  obtain ⟨β, hβ, hαβ⟩ := exists_homeomorph_closedBall_eq_on_sphere α hα β₀ hβ₀ hBA
  have hαb := homeomorphClosedBall_mem_iff α hα
  have hβb := homeomorphClosedBall_mem_iff β hβ
  have hle : ∀ q : Metric.closedBall (0 : P2) 1, ‖(q : P2)‖ ≤ 1 :=
    fun q => mem_closedBall_zero_iff.mp q.2
  let π : P3 → P2 := fun p => WithLp.toLp 2 fun i : Fin 2 => p (Fin.castSucc i)
  have hπc : Continuous π := by fun_prop
  have hπ0 : ∀ p : P3, π p 0 = p 0 := fun p => rfl
  have hπ1 : ∀ p : P3, π p 1 = p 1 := fun p => rfl
  have hnorm2 : ∀ q : P2, ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
    intro q
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    simp
  have hnorm3 : ∀ p : P3, ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
    intro p
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp
  have hsph : ∀ p ∈ Metric.sphere (0 : P3) 1, ‖π p‖ ^ 2 = 1 - p 2 ^ 2 := by
    intro p hp
    have h1 := hnorm3 p
    rw [mem_sphere_zero_iff_norm.mp hp, one_pow] at h1
    rw [hnorm2, hπ0, hπ1]
    linarith
  have hπb : ∀ p : Metric.sphere (0 : P3) 1, π p ∈ Metric.closedBall (0 : P2) 1 := by
    intro p
    rw [mem_closedBall_zero_iff]
    have h1 := hsph p p.2
    have h2 : ‖π p‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ((p : P3) 2)]
    exact (sq_le_one_iff₀ (norm_nonneg _)).mp h2
  let ρ : Metric.sphere (0 : P3) 1 → Metric.closedBall (0 : P2) 1 := fun p => ⟨π p, hπb p⟩
  have hρc : Continuous ρ := (hπc.comp continuous_subtype_val).subtype_mk _
  have hρ1 : ∀ p : Metric.sphere (0 : P3) 1, (p : P3) 2 = 0 → ‖(ρ p : P2)‖ = 1 := by
    intro p hp
    have h2 := hsph p p.2
    rw [hp] at h2
    have h3 : ‖π p‖ ^ 2 = 1 ^ 2 := by rw [h2]; ring
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h3
  have hρ2 : ∀ p : Metric.sphere (0 : P3) 1, ‖(ρ p : P2)‖ = 1 → (p : P3) 2 = 0 := by
    intro p hp
    have h2 := hsph p p.2
    change ‖π p‖ = 1 at hp
    rw [hp] at h2
    nlinarith [sq_nonneg ((p : P3) 2)]
  let Θ : Metric.sphere (0 : P3) 1 → X := fun p =>
    if (0 : ℝ) ≤ (p : P3) 2 then (α (ρ p) : X) else (β (ρ p) : X)
  have hΘc : Continuous Θ := by
    refine continuous_if_le continuous_const (by fun_prop)
      (continuous_subtype_val.comp (α.continuous.comp hρc)).continuousOn
      (continuous_subtype_val.comp (β.continuous.comp hρc)).continuousOn ?_
    intro p hp
    exact (hαβ (ρ p) (hρ1 p hp.symm)).symm
  have hΘmem : ∀ p, Θ p ∈ A ∪ B := by
    intro p
    simp only [Θ]
    split_ifs
    · exact Or.inl (α (ρ p)).2
    · exact Or.inr (β (ρ p)).2
  have hext : ∀ p p' : Metric.sphere (0 : P3) 1, ρ p = ρ p' → (p : P3) 2 = (p' : P3) 2 →
      p = p' := by
    intro p p' hρ h2
    have hπ : π p = π p' := congrArg Subtype.val hρ
    apply Subtype.ext
    ext i
    fin_cases i
    · have := congrArg (fun z : P2 => z 0) hπ
      simpa [hπ0] using this
    · have := congrArg (fun z : P2 => z 1) hπ
      simpa [hπ1] using this
    · exact h2
  have hsq : ∀ p p' : Metric.sphere (0 : P3) 1, ρ p = ρ p' → (p : P3) 2 ^ 2 = (p' : P3) 2 ^ 2 := by
    intro p p' hρ
    have e1 := hsph p p.2
    have e2 := hsph p' p'.2
    have hπ : π p = π p' := congrArg Subtype.val hρ
    rw [hπ] at e1
    linarith
  have hinj : Function.Injective Θ := by
    intro p p' hpp'
    by_cases hp : (0 : ℝ) ≤ (p : P3) 2 <;> by_cases hp' : (0 : ℝ) ≤ (p' : P3) 2 <;>
      simp only [Θ, hp, hp', ite_true, ite_false] at hpp'
    · have hρ := α.injective (Subtype.ext hpp')
      exact hext p p' hρ ((pow_left_inj₀ hp hp' two_ne_zero).mp (hsq p p' hρ))
    · exfalso
      have hmem : (β (ρ p') : X) ∈ A ∩ B := ⟨hpp' ▸ (α (ρ p)).2, (β (ρ p')).2⟩
      rw [hAB, ← hBA] at hmem
      have h1 := hρ2 p' (le_antisymm (hle _) (not_lt.mp fun h => hmem.2 ((hβb _).mpr h)))
      exact hp' h1.ge
    · exfalso
      have hmem : (β (ρ p) : X) ∈ A ∩ B := ⟨hpp' ▸ (α (ρ p')).2, (β (ρ p)).2⟩
      rw [hAB, ← hBA] at hmem
      have h1 := hρ2 p (le_antisymm (hle _) (not_lt.mp fun h => hmem.2 ((hβb _).mpr h)))
      exact hp h1.ge
    · have hρ := β.injective (Subtype.ext hpp')
      have h2 : -(p : P3) 2 = -(p' : P3) 2 := by
        refine (pow_left_inj₀ (by linarith [not_le.mp hp]) (by linarith [not_le.mp hp'])
          two_ne_zero).mp ?_
        rw [neg_sq, neg_sq]
        exact hsq p p' hρ
      exact hext p p' hρ (neg_injective h2)
  let lift : P2 → ℝ → P3 := fun q t => !₂[q 0, q 1, t]
  have hliftρ : ∀ (q : Metric.closedBall (0 : P2) 1) (t : ℝ)
      (ht : lift q t ∈ Metric.sphere (0 : P3) 1), ρ ⟨lift q t, ht⟩ = q := by
    intro q t ht
    apply Subtype.ext
    change π (lift q t) = q
    ext i
    fin_cases i <;> simp [π, lift]
  have hlift2 : ∀ q t, (lift q t) 2 = t := fun q t => by simp [lift]
  have hliftS : ∀ (q : Metric.closedBall (0 : P2) 1) (t : ℝ), t ^ 2 = 1 - ‖(q : P2)‖ ^ 2 →
      lift q t ∈ Metric.sphere (0 : P3) 1 := by
    intro q t ht
    rw [mem_sphere_zero_iff_norm]
    have h1 := hnorm3 (lift q t)
    have h2 := hnorm2 (q : P2)
    have hc0 : (lift q t) 0 = (q : P2) 0 := by simp [lift]
    have hc1 : (lift q t) 1 = (q : P2) 1 := by simp [lift]
    rw [hc0, hc1, hlift2] at h1
    have h3 : ‖lift q t‖ ^ 2 = 1 ^ 2 := by
      rw [h1]
      linarith
    exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h3
  have hsurj : ∀ y ∈ A ∪ B, ∃ p, Θ p = y := by
    rintro y (hyA | hyB)
    · let q := α.symm ⟨y, hyA⟩
      have hq := hle q
      let t := Real.sqrt (1 - ‖(q : P2)‖ ^ 2)
      have ht : t ^ 2 = 1 - ‖(q : P2)‖ ^ 2 :=
        Real.sq_sqrt (by nlinarith [norm_nonneg (q : P2)])
      let p : Metric.sphere (0 : P3) 1 := ⟨lift q t, hliftS q t ht⟩
      refine ⟨p, ?_⟩
      have h0 : (0 : ℝ) ≤ (p : P3) 2 := by
        change (0 : ℝ) ≤ lift q t 2
        rw [hlift2]
        exact Real.sqrt_nonneg _
      simp only [Θ, h0, ite_true]
      rw [hliftρ q t]
      simp [q]
    · let q := β.symm ⟨y, hyB⟩
      have hq := hle q
      by_cases hq1 : ‖(q : P2)‖ = 1
      · have ht : (0 : ℝ) ^ 2 = 1 - ‖(q : P2)‖ ^ 2 := by rw [hq1]; ring
        let p : Metric.sphere (0 : P3) 1 := ⟨lift q 0, hliftS q 0 ht⟩
        refine ⟨p, ?_⟩
        have h0 : (0 : ℝ) ≤ (p : P3) 2 := by
          change (0 : ℝ) ≤ lift q 0 2
          rw [hlift2]
        simp only [Θ, h0, ite_true]
        rw [hliftρ q 0, ← hαβ q hq1]
        simp [q]
      · have hlt : ‖(q : P2)‖ < 1 := lt_of_le_of_ne hq hq1
        let t := -Real.sqrt (1 - ‖(q : P2)‖ ^ 2)
        have ht : t ^ 2 = 1 - ‖(q : P2)‖ ^ 2 := by
          simp only [t, neg_sq]
          exact Real.sq_sqrt (by nlinarith [norm_nonneg (q : P2)])
        let p : Metric.sphere (0 : P3) 1 := ⟨lift q t, hliftS q t ht⟩
        refine ⟨p, ?_⟩
        have h0 : ¬ (0 : ℝ) ≤ (p : P3) 2 := by
          change ¬ (0 : ℝ) ≤ lift q t 2
          rw [hlift2]
          have : 0 < Real.sqrt (1 - ‖(q : P2)‖ ^ 2) :=
            Real.sqrt_pos.mpr (by nlinarith [norm_nonneg (q : P2)])
          simp only [t]
          linarith
        simp only [Θ, h0, ite_false]
        rw [hliftρ q t]
        simp [q]
  let Θ' : Metric.sphere (0 : P3) 1 → ↥(A ∪ B) := fun p => ⟨Θ p, hΘmem p⟩
  have hΘ'c : Continuous Θ' := hΘc.subtype_mk _
  have hΘ'b : Function.Bijective Θ' := by
    refine ⟨fun p p' h => hinj (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨p, hp⟩ := hsurj y.1 y.2
    exact ⟨p, Subtype.ext hp⟩
  exact ⟨(Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective Θ' hΘ'b) hΘ'c).symm⟩

theorem IsTopologicalCellWithInterior.sdiff_union_of_subcell [T2Space X]
    {D Dint D₁ D₁int B₁ B₁int : Set X} (hD : IsTopologicalCellWithInterior 2 D Dint)
    (hD₁ : IsTopologicalCellWithInterior 2 D₁ D₁int)
    (hB₁ : IsTopologicalCellWithInterior 2 B₁ B₁int) (hD₁D : D₁ ⊆ Dint)
    (hopen : ∃ W : Set X, IsOpen W ∧ D₁int = W ∩ D) (hBD : B₁ ∩ D = D₁ \ D₁int)
    (hBb : B₁ \ B₁int = D₁ \ D₁int) :
    IsTopologicalCellWithInterior 2 ((D \ D₁int) ∪ B₁) ((Dint \ D₁) ∪ B₁) ∧
      ((D \ D₁int) ∪ B₁) \ ((Dint \ D₁) ∪ B₁) = D \ Dint := by
  classical
  obtain ⟨φ, hφ⟩ := hD
  obtain ⟨δ₁, hδ₁⟩ := hD₁
  obtain ⟨b₀, hb₀⟩ := hB₁
  obtain ⟨b, hb, hbδ⟩ := exists_homeomorph_closedBall_eq_on_sphere δ₁ hδ₁ b₀ hb₀ hBb
  have hδb := homeomorphClosedBall_mem_iff δ₁ hδ₁
  have hbb := homeomorphClosedBall_mem_iff b hb
  have hle : ∀ q : Metric.closedBall (0 : P2) 1, ‖(q : P2)‖ ≤ 1 :=
    fun q => mem_closedBall_zero_iff.mp q.2
  have hcpt : ∀ {C : Set X} (ψ : Metric.closedBall (0 : P2) 1 ≃ₜ C), IsCompact C := by
    intro C ψ
    have h := isCompact_univ.image (continuous_subtype_val.comp ψ.continuous)
    rwa [image_univ, range_comp, ψ.surjective.range_eq, image_univ,
      Subtype.range_coe] at h
  have hintsub : ∀ {C I : Set X} (ψ : Metric.closedBall (0 : P2) 1 ≃ₜ C),
      I = Subtype.val '' (ψ '' {q | ‖(q : P2)‖ < 1}) → I ⊆ C := by
    rintro C I ψ rfl _ ⟨w, -, rfl⟩
    exact w.2
  have hDc : IsClosed D := (hcpt φ).isClosed
  have hD₁c : IsClosed D₁ := (hcpt δ₁).isClosed
  have hDintD : Dint ⊆ D := hintsub φ hφ
  have hD₁intD₁ : D₁int ⊆ D₁ := hintsub δ₁ hδ₁
  have hD₁sub : D₁ ⊆ D := hD₁D.trans hDintD
  let γ : ↥D₁ ≃ₜ ↥B₁ := δ₁.symm.trans b
  have hγfix : ∀ y : ↥D₁, (y : X) ∉ D₁int → (γ y : X) = y := by
    intro y hy
    have hq : ‖(δ₁.symm y : P2)‖ = 1 := by
      refine le_antisymm (hle _) (not_lt.mp fun h => hy ?_)
      have h1 := (hδb (δ₁.symm y)).mpr h
      rwa [Homeomorph.apply_symm_apply] at h1
    change (b (δ₁.symm y) : X) = y
    rw [hbδ _ hq, Homeomorph.apply_symm_apply]
  have hγint : ∀ y : ↥D₁, (y : X) ∈ D₁int → (γ y : X) ∈ B₁int := by
    intro y hy
    have hq : ‖(δ₁.symm y : P2)‖ < 1 := by
      have h1 := (hδb (δ₁.symm y)).mp
      rw [Homeomorph.apply_symm_apply] at h1
      exact h1 hy
    exact (hbb _).mpr hq
  have hB₁intB₁ : B₁int ⊆ B₁ := hintsub b hb
  have hB₁intD : Disjoint B₁int D := by
    refine Set.disjoint_left.mpr fun z hz hzD => ?_
    have hzBD : z ∈ B₁ ∩ D := ⟨hB₁intB₁ hz, hzD⟩
    rw [hBD, ← hBb] at hzBD
    exact hzBD.2 hz
  let Θ₀ : X → X := fun y => if hy : y ∈ D₁ then (γ ⟨y, hy⟩ : X) else y
  have hΘ₁ : ∀ y (hy : y ∈ D₁), Θ₀ y = γ ⟨y, hy⟩ := fun y hy => dite_eq_left hy
  have hΘ₂ : ∀ y, y ∉ D₁int → Θ₀ y = y := by
    intro y hy
    by_cases hy₁ : y ∈ D₁
    · rw [hΘ₁ y hy₁]
      exact hγfix ⟨y, hy₁⟩ hy
    · exact dite_eq_right hy₁
  obtain ⟨W, hW, hWeq⟩ := hopen
  have hΘc : ContinuousOn Θ₀ D := by
    have hsplit : D = D₁ ∪ (D \ D₁int) := by
      ext y
      constructor
      · intro hy
        by_cases hy₁ : y ∈ D₁int
        · exact Or.inl (hD₁intD₁ hy₁)
        · exact Or.inr ⟨hy, hy₁⟩
      · rintro (hy | hy)
        · exact hD₁sub hy
        · exact hy.1
    have hc₂ : IsClosed (D \ D₁int) := by
      have heq : D \ D₁int = D ∩ Wᶜ := by
        rw [hWeq]
        ext y
        simp only [mem_sdiff, mem_inter_iff, mem_compl_iff]
        tauto
      rw [heq]
      exact hDc.inter hW.isClosed_compl
    rw [hsplit]
    refine ContinuousOn.union_of_isClosed ?_ ?_ hD₁c hc₂
    · rw [continuousOn_iff_continuous_domRestrict]
      have heq : D₁.domRestrict Θ₀ = fun y => (γ y : X) := funext fun y => hΘ₁ y.1 y.2
      rw [heq]
      exact continuous_subtype_val.comp γ.continuous
    · exact continuousOn_id.congr fun y hy => hΘ₂ y hy.2
  have hΘinj : InjOn Θ₀ D := by
    intro y hy y' hy' hyy'
    by_cases h₁ : y ∈ D₁int <;> by_cases h₂ : y' ∈ D₁int
    · rw [hΘ₁ y (hD₁intD₁ h₁), hΘ₁ y' (hD₁intD₁ h₂)] at hyy'
      exact congrArg Subtype.val (γ.injective (Subtype.ext hyy'))
    · exfalso
      rw [hΘ₁ y (hD₁intD₁ h₁), hΘ₂ y' h₂] at hyy'
      exact Set.disjoint_left.mp hB₁intD (hγint ⟨y, hD₁intD₁ h₁⟩ h₁) (hyy' ▸ hy')
    · exfalso
      rw [hΘ₂ y h₁, hΘ₁ y' (hD₁intD₁ h₂)] at hyy'
      exact Set.disjoint_left.mp hB₁intD (hγint ⟨y', hD₁intD₁ h₂⟩ h₂) (hyy'.symm ▸ hy)
    · rwa [hΘ₂ y h₁, hΘ₂ y' h₂] at hyy'
  have hγsurj : ∀ z ∈ B₁, ∃ y ∈ D₁, Θ₀ y = z := by
    intro z hz
    refine ⟨γ.symm ⟨z, hz⟩, (γ.symm ⟨z, hz⟩).2, ?_⟩
    rw [hΘ₁ _ (γ.symm ⟨z, hz⟩).2, Subtype.coe_eta, Homeomorph.apply_symm_apply]
  have himgD : Θ₀ '' D = (D \ D₁int) ∪ B₁ := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      by_cases h₁ : y ∈ D₁int
      · rw [hΘ₁ y (hD₁intD₁ h₁)]
        exact Or.inr (γ ⟨y, hD₁intD₁ h₁⟩).2
      · rw [hΘ₂ y h₁]
        exact Or.inl ⟨hy, h₁⟩
    · rintro (hz | hz)
      · exact ⟨z, hz.1, hΘ₂ z hz.2⟩
      · obtain ⟨y, hy, hyz⟩ := hγsurj z hz
        exact ⟨y, hD₁sub hy, hyz⟩
  have himgI : Θ₀ '' Dint = (Dint \ D₁) ∪ B₁ := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      by_cases h₁ : y ∈ D₁
      · rw [hΘ₁ y h₁]
        exact Or.inr (γ ⟨y, h₁⟩).2
      · rw [hΘ₂ y fun h => h₁ (hD₁intD₁ h)]
        exact Or.inl ⟨hy, h₁⟩
    · rintro (hz | hz)
      · exact ⟨z, hz.1, hΘ₂ z fun h => hz.2 (hD₁intD₁ h)⟩
      · obtain ⟨y, hy, hyz⟩ := hγsurj z hz
        exact ⟨y, hD₁D hy, hyz⟩
  let g : Metric.closedBall (0 : P2) 1 → X := fun q => Θ₀ (φ q : X)
  have hgc : Continuous g := hΘc.comp_continuous (continuous_subtype_val.comp φ.continuous)
    fun q => (φ q).2
  have hgi : Function.Injective g := fun q q' h =>
    φ.injective (Subtype.ext (hΘinj (φ q).2 (φ q').2 h))
  have hemb := (hgc.isClosedEmbedding hgi).isEmbedding
  have hrange : range g = (D \ D₁int) ∪ B₁ := by
    rw [← himgD]
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨φ q, (φ q).2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨q, hq⟩ := φ.surjective ⟨y, hy⟩
      exact ⟨q, by simp only [g, hq]⟩
  have hcomp : Subtype.val ∘ (hemb.toHomeomorph.trans (Homeomorph.setCongr hrange)) = g :=
    funext fun q => rfl
  refine ⟨⟨hemb.toHomeomorph.trans (Homeomorph.setCongr hrange), ?_⟩, ?_⟩
  · rw [← image_comp, hcomp, ← himgI, hφ, image_image, image_image]
  · ext y
    simp only [mem_sdiff, mem_union]
    constructor
    · rintro ⟨hy | hy, hn⟩
      · refine ⟨hy.1, fun hyI => ?_⟩
        have hy₁ : y ∈ D₁ := by
          by_contra h
          exact hn (Or.inl ⟨hyI, h⟩)
        have hyB : y ∈ B₁ ∩ D := by
          rw [hBD]
          exact ⟨hy₁, hy.2⟩
        exact hn (Or.inr hyB.1)
      · exact (hn (Or.inr hy)).elim
    · rintro ⟨hy, hyI⟩
      refine ⟨Or.inl ⟨hy, fun h => hyI (hD₁D (hD₁intD₁ h))⟩, ?_⟩
      rintro (h | h)
      · exact hyI h.1
      · have hyB : y ∈ B₁ ∩ D := ⟨h, hy⟩
        rw [hBD] at hyB
        exact hyI (hD₁D hyB.1)

end Cells

theorem IsPLHomeomorphOn.isTopologicalCellWithInterior {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {r : (Fin 3 → ℝ) → E} {Δ : Set E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ) :
    IsTopologicalCellWithInterior 2 Δ (Δ \ r '' stdSimplexBoundary 2) := by
  let τ := DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph (n := 2)
    (EuclideanSpace.equiv (Fin 2) ℝ).symm
  have hrc : Continuous (hr.bijOn.mapsTo.restrict r _ _) :=
    hr.isPiecewiseAffineOn.continuousOn.mapsToRestrict hr.bijOn.mapsTo
  let ρ : ↥(Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) ≃ₜ ↥Δ :=
    Continuous.homeoOfEquivCompactToT2 (f := hr.bijOn.equiv r) hrc
  refine ⟨τ.symm.trans ρ, ?_⟩
  have hbd : ∀ x : ↥(Convexity.StdSimplex.coordinateSet ℝ (Fin 3)),
      (x : Fin 3 → ℝ) ∈ stdSimplexBoundary 2 ↔ x ∈ DifferentialGeometry.Simplex.boundary (Fin 3) :=
    fun x => ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  ext y
  constructor
  · rintro ⟨hyΔ, hyb⟩
    obtain ⟨x, hx⟩ := ρ.surjective ⟨y, hyΔ⟩
    have hxb : x ∉ DifferentialGeometry.Simplex.boundary (Fin 3) := by
      intro h
      apply hyb
      refine ⟨x, (hbd x).mpr h, ?_⟩
      have := congrArg Subtype.val hx
      exact this
    refine ⟨ρ x, ⟨τ x, ?_, by simp⟩, by rw [hx]⟩
    change ‖((τ x : Metric.closedBall (0 : P2) 1) : P2)‖ < 1
    refine lt_of_le_of_ne (mem_closedBall_zero_iff.mp (τ x).2) fun h => hxb ?_
    exact (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph_mem_sphere_iff
      (EuclideanSpace.equiv (Fin 2) ℝ).symm x).mp
      (mem_sphere_zero_iff_norm.mpr h)
  · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨((τ.symm.trans ρ) q).2, ?_⟩
    rintro ⟨x, hx, hxy⟩
    have hq' : ¬ τ.symm q ∈ DifferentialGeometry.Simplex.boundary (Fin 3) := by
      intro h
      have h1 := (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph_mem_sphere_iff
        (EuclideanSpace.equiv (Fin 2) ℝ).symm (τ.symm q)).mpr h
      rw [Homeomorph.apply_symm_apply, mem_sphere_zero_iff_norm] at h1
      exact (ne_of_lt hq) h1
    apply hq'
    have hxeq : x = (τ.symm q : Fin 3 → ℝ) := hr.bijOn.injOn hx.1 (τ.symm q).2 hxy
    exact (hbd (τ.symm q)).mp (hxeq ▸ hx)

theorem IsTopologicalSphere.isCombinatorialManifold {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hL : IsTopologicalSphere 2 L.space) : IsCombinatorialManifold 2 L := by
  intro v hv
  obtain ⟨θ⟩ := hL
  have hvL : v ∈ L.space := L.subset_space hv (Finset.mem_singleton_self v)
  have : Fact (Module.finrank ℝ P3 = 2 + 1) := ⟨by simp⟩
  let s₀ := θ ⟨v, hvL⟩
  let s₁ : Metric.sphere (0 : P3) 1 :=
    ⟨-(s₀ : P3), by rw [mem_sphere_zero_iff_norm, norm_neg]; exact mem_sphere_zero_iff_norm.mp s₀.2⟩
  have hs₁ : s₀ ≠ s₁ := by
    intro h
    have h1 : (s₀ : P3) = -(s₀ : P3) := congrArg Subtype.val h
    have h2 : (s₀ : P3) = 0 := by
      have h3 : (2 : ℝ) • (s₀ : P3) = 0 := by
        rw [two_smul]
        nth_rw 2 [h1]
        exact add_neg_cancel _
      exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
    have h3 := mem_sphere_zero_iff_norm.mp s₀.2
    rw [h2, norm_zero] at h3
    exact zero_ne_one h3
  let w : E := θ.symm s₁
  have hwv : v ≠ w := by
    intro h
    apply hs₁
    have h1 : θ.symm s₁ = ⟨v, hvL⟩ := Subtype.ext h.symm
    change θ ⟨v, hvL⟩ = s₁
    rw [← h1, Homeomorph.apply_symm_apply]
  let σ := stereographic' 2 s₁
  have hσs : ∀ s, s ≠ s₁ → s ∈ σ.source := fun s hs => by
    rw [stereographic'_source]
    exact hs
  have hσt : ∀ u, u ∈ σ.target := fun u => by
    rw [stereographic'_target]
    exact mem_univ u
  let M := L.space \ {w}
  let ιM : ↥M → ↥L.space := Set.inclusion sdiff_subset
  have hMθ : ∀ y : ↥M, θ (ιM y) ≠ s₁ := by
    intro y h
    apply y.2.2
    change (y : E) = (θ.symm s₁ : E)
    rw [← h, Homeomorph.symm_apply_apply]
  let toF : ↥M → ↥(univ : Set P2) := fun y => ⟨σ (θ (ιM y)), mem_univ _⟩
  have hinv : ∀ u, (θ.symm (σ.symm u) : E) ∈ M := by
    intro u
    refine ⟨(θ.symm (σ.symm u)).2, fun h => ?_⟩
    have h1 : θ.symm (σ.symm u) = θ.symm s₁ := Subtype.ext h
    have h2 := σ.map_target (hσt u)
    rw [θ.symm.injective h1, stereographic'_source] at h2
    exact h2 rfl
  let invF : ↥(univ : Set P2) → ↥M := fun u => ⟨θ.symm (σ.symm u.1), hinv u.1⟩
  let ψ : ↥M ≃ₜ ↥(univ : Set P2) :=
    { toFun := toF
      invFun := invF
      left_inv := fun y => by
        apply Subtype.ext
        change (θ.symm (σ.symm (σ (θ (ιM y)))) : E) = y.1
        rw [σ.left_inv (hσs _ (hMθ y)), Homeomorph.symm_apply_apply]
      right_inv := fun u => by
        apply Subtype.ext
        change σ (θ (ιM (invF u))) = u.1
        have h1 : ιM (invF u) = θ.symm (σ.symm u.1) := Subtype.ext rfl
        rw [h1, Homeomorph.apply_symm_apply, σ.right_inv (hσt _)]
      continuous_toFun := by
        exact (σ.continuousOn.comp_continuous (θ.continuous.comp (continuous_inclusion _))
          fun y => hσs _ (hMθ y)).subtype_mk _
      continuous_invFun := by
        refine ((continuous_subtype_val.comp θ.symm.continuous).comp ?_).subtype_mk _
        exact σ.continuousOn_symm.comp_continuous continuous_subtype_val fun u => hσt _ }
  refine isPLSphere_one_geometricLink_of_homeomorph L isOpen_univ ψ hv ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds hwv] with y hy
  exact ⟨fun h => ⟨h, hy⟩, fun h => h.1⟩

theorem IsTopologicalSphere.isConnected {X : Type*} [TopologicalSpace X] {S : Set X}
    (h : IsTopologicalSphere 2 S) : IsConnected S := by
  obtain ⟨θ⟩ := h
  have hconn : IsConnected (Metric.sphere (0 : P3) 1) :=
    isConnected_sphere (by rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one
  have : ConnectedSpace (Metric.sphere (0 : P3) 1) := isConnected_iff_connectedSpace.mp hconn
  have h1 := isConnected_univ.image (fun s => (θ.symm s : X))
    (continuous_subtype_val.comp θ.symm.continuous).continuousOn
  have h2 : (range fun s => (θ.symm s : X)) = S := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact (θ.symm s).2
    · intro hy
      exact ⟨θ ⟨y, hy⟩, by simp⟩
  rwa [image_univ, h2] at h1

end DifferentialGeometry.Topology.PiecewiseLinear
