import DifferentialGeometry.Topology.Manifold.RelativeCollarStraightening
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpaceProd
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Composition
import Mathlib.Geometry.Manifold.Instances.Sphere

set_option autoImplicit false

noncomputable section

open Manifold Set Topology
open DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Collar

universe u

theorem collarImage_subset_of_supported_matching_of_le
    {S M : Type*} (c₀ c₁ : S × EuclideanHalfSpace 1 → M) (Φ : M → M) {δ η : ℝ}
    (hδη : δ ≤ η) (hinj : Function.Injective Φ)
    (hsupp : Set.EqOn Φ id
      (c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < η})ᶜ)
    (hmatch : ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
      Φ (c₀ (p, t)) = c₁ (p, t)) :
    c₁ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ} ⊆
      c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < η} := by
  have hfix : ∀ z ∈ c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < η},
      Φ z ∈ c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < η} := by
    intro z hz
    by_contra hz'
    have h2 : Φ (Φ z) = Φ z := hsupp hz'
    have h3 : Φ z = z := hinj h2
    exact hz' (h3.symm ▸ hz)
  rintro y ⟨⟨s, t⟩, hq, rfl⟩
  rw [← hmatch s t hq]
  exact hfix _ ⟨(s, t), lt_of_lt_of_le hq hδη, rfl⟩

theorem eqOn_symm_comp_of_eqOn_id {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
    {Φ Ψ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞} {K : Set M}
    (hΦ : Set.EqOn Φ id Kᶜ) (hΨ : Set.EqOn Ψ id Kᶜ) :
    Set.EqOn (Φ.trans Ψ) id Kᶜ ∧ Set.EqOn (Φ.trans Ψ).symm id Kᶜ := by
  have hfix : ∀ {Λ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞}, Set.EqOn Λ id Kᶜ →
      Set.EqOn Λ.symm id Kᶜ := by
    intro Λ hΛ x hx
    have h1 : Λ x = x := hΛ hx
    calc Λ.symm x = Λ.symm (Λ x) := by rw [h1]
      _ = x := Diffeomorph.symm_apply_apply Λ x
  have hcomp : Set.EqOn (Φ.trans Ψ) id Kᶜ := by
    intro x hx
    change Ψ (Φ x) = x
    have h1 : Φ x = x := hΦ hx
    have h2 : Ψ x = x := hΨ hx
    rw [h1]
    exact h2
  refine ⟨hcomp, fun x hx => ?_⟩
  have h1 : (Φ.trans Ψ) x = x := hcomp hx
  calc (Φ.trans Ψ).symm x = (Φ.trans Ψ).symm ((Φ.trans Ψ) x) := by rw [h1]
    _ = x := Diffeomorph.symm_apply_apply _ x

private theorem eqOn_symm_of_eqOn_id' {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
    {Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞} {X : Set M}
    (h : Set.EqOn Φ id X) : Set.EqOn Φ.symm id X := by
  intro x hx
  have h1 : Φ x = x := h hx
  calc Φ.symm x = Φ.symm (Φ x) := by rw [h1]
    _ = x := Diffeomorph.symm_apply_apply Φ x

def BoundaryCollarStraighteningWithPrescribedSupport : Prop :=
  ∀ {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × EuclideanHalfSpace 1) M ∞),
    (∀ p : S, (p, 0) ∈ c₀.source ∧ (p, 0) ∈ c₁.source) →
    (∀ p : S, c₀ (p, 0) = c₁ (p, 0)) →
    (∀ p : S, c₀ (p, 0) ∈ (𝓡∂ 3).boundary M) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
        ∃ Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞,
          (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
            Φ (c₀ (p, t)) = c₁ (p, t)) ∧
          Set.EqOn Φ id (c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < ε})ᶜ

theorem relativeCollarUniqueness_of_boundaryCollarStraighteningWithPrescribedSupport
    (h : BoundaryCollarStraighteningWithPrescribedSupport.{u}) :
    ∀ {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
      [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S]
      {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
      [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
      (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
        (S × EuclideanHalfSpace 1) M ∞),
      (∀ p : S, (p, 0) ∈ c₀.source ∧ (p, 0) ∈ c₁.source) →
      (∀ p : S, c₀ (p, 0) = c₁ (p, 0)) →
      (∀ p : S, c₀ (p, 0) ∈ (𝓡∂ 3).boundary M) →
        ∀ U : Set M, IsOpen U →
          (∃ ε : ℝ, 0 < ε ∧ ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < ε →
            c₀ (p, t) ∈ U ∧ c₁ (p, t) ∈ U) →
          ∃ δ : ℝ, 0 < δ ∧
            (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
              (p, t) ∈ c₀.source ∧ (p, t) ∈ c₁.source ∧
                c₀ (p, t) ∈ U ∧ c₁ (p, t) ∈ U) ∧
            ∃ Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞,
              (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
                Φ (c₀ (p, t)) = c₁ (p, t)) ∧
              Set.EqOn Φ id Uᶜ ∧ Set.EqOn Φ.symm id Uᶜ := by
  intro S _ _ _ _ _ M _ _ _ _ _ c₀ c₁ hsrc hcore hbdy U _ ⟨ε, hε, hU⟩
  obtain ⟨δsrc, hδsrc, hstrip⟩ := exists_pos_forall_mem_of_compact_zeroSection
    (S := S) (W := c₀.source ∩ c₁.source) (c₀.open_source.inter c₁.open_source)
    (fun p => ⟨(hsrc p).1, (hsrc p).2⟩)
  obtain ⟨δ, hδ, hδε, Φ, hmatch, hsupp⟩ := h c₀ c₁ hsrc hcore hbdy ε hε
  have hsub : Uᶜ ⊆ (c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < ε})ᶜ := by
    intro x hx hmem
    obtain ⟨⟨q, s⟩, hq, rfl⟩ := hmem
    exact hx (hU q s hq).1
  have hsupp' : Set.EqOn Φ id Uᶜ := Set.EqOn.mono hsub hsupp
  refine ⟨min δ δsrc, lt_min hδ hδsrc, fun p t ht => ?_, Φ, fun p t ht => ?_,
    hsupp', eqOn_symm_of_eqOn_id' hsupp'⟩
  · exact ⟨(hstrip p t (lt_of_lt_of_le ht (min_le_right δ δsrc))).1,
      (hstrip p t (lt_of_lt_of_le ht (min_le_right δ δsrc))).2,
      (hU p t (lt_of_lt_of_le ht ((min_le_left δ δsrc).trans hδε))).1,
      (hU p t (lt_of_lt_of_le ht ((min_le_left δ δsrc).trans hδε))).2⟩
  · exact hmatch p t (lt_of_lt_of_le ht (min_le_left δ δsrc))

theorem boundaryCollarStraighteningWithPrescribedSupport_of_boundaryCollarStraightening
    {C : ℝ} (hC : 1 ≤ C) (h : BoundaryCollarStraightening.{u} C) :
    BoundaryCollarStraighteningWithPrescribedSupport.{u} := by
  intro S _ _ _ _ _ M _ _ _ _ _ c₀ c₁ hsrc hcore hbdy ε hε
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨δ, hδ, hδε, Φ, hmatch, hsupp⟩ :=
    h c₀ c₁ hsrc hcore hbdy (ε / C) (div_pos hε hCpos)
  have hδC : C * δ ≤ ε := by
    have h1 : δ * C ≤ (ε / C) * C := mul_le_mul_of_nonneg_right hδε hCpos.le
    rw [div_mul_cancel₀ ε hCpos.ne'] at h1
    linarith [h1]
  have hδε' : δ ≤ ε := by
    have h1 : ε / C ≤ ε := by
      rw [div_le_iff₀ hCpos]
      exact le_mul_of_one_le_right hε.le hC
    exact hδε.trans h1
  have hstrip_mono : {q : S × EuclideanHalfSpace 1 | q.2.1 0 < C * δ} ⊆
      {q : S × EuclideanHalfSpace 1 | q.2.1 0 < ε} := by
    intro q hq
    exact lt_of_lt_of_le hq hδC
  exact ⟨δ, hδ, hδε', Φ, hmatch,
    Set.EqOn.mono (Set.compl_subset_compl.mpr (Set.image_mono hstrip_mono)) hsupp⟩

theorem boundaryCollarStraighteningWithPrescribedSupport_of_boundedSupport
    (h : BoundaryCollarStraighteningWithBoundedSupport.{u}) :
    BoundaryCollarStraighteningWithPrescribedSupport.{u} := by
  obtain ⟨C, hC, h'⟩ := h
  exact boundaryCollarStraighteningWithPrescribedSupport_of_boundaryCollarStraightening hC h'

theorem boundaryCollarStraighteningWithPrescribedSupport_of_regularization
    (h : BoundaryCollarRegularization.{u}) :
    BoundaryCollarStraighteningWithPrescribedSupport.{u} := by
  intro S _ _ _ _ _ M _ _ _ _ _ c₀ c₁ hsrc hcore hbdy ε hε
  obtain ⟨δ, hδ, hδε, Φ, hmatch, hsupp⟩ := h c₀ c₁ hsrc hcore hbdy ε hε
  have hstrip_mono : {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ} ⊆
      {q : S × EuclideanHalfSpace 1 | q.2.1 0 < ε} := fun q hq => lt_of_lt_of_le hq hδε
  exact ⟨δ, hδ, hδε, Φ, hmatch,
    Set.EqOn.mono (Set.compl_subset_compl.mpr (Set.image_mono hstrip_mono)) hsupp⟩

theorem exists_dilationStrip_subset_of_prescribedStrip
    (S : Type*) (lam ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
      {q : S × EuclideanHalfSpace 1 | q.2.1 0 < lam * δ} ⊆
        {q : S × EuclideanHalfSpace 1 | q.2.1 0 < ε} := by
  refine ⟨ε / max lam 1, div_pos hε (lt_of_lt_of_le zero_lt_one (le_max_right lam 1)),
    div_le_self hε.le (le_max_right lam 1), fun q hq => ?_⟩
  simp only [Set.mem_ofPred_eq] at hq ⊢
  have hb : (0 : ℝ) < max lam 1 := lt_of_lt_of_le zero_lt_one (le_max_right lam 1)
  have h2 : lam / max lam 1 ≤ 1 := by
    rw [div_le_iff₀ hb]
    linarith [le_max_left lam 1]
  have h1 : lam * (ε / max lam 1) = ε * (lam / max lam 1) := by ring
  nlinarith [hq, hε, h2, h1]

theorem exists_supported_diffeomorph_of_eqOn_prescribedStrip
    {S : Type u} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S]
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × EuclideanHalfSpace 1) M ∞)
    {ε : ℝ} (hε : 0 < ε)
    (hagree : ∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < ε → c₀ (p, t) = c₁ (p, t)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
      ∃ Φ : Diffeomorph (𝓡∂ 3) (𝓡∂ 3) M M ∞,
        (∀ (p : S) (t : EuclideanHalfSpace 1), t.1 0 < δ →
          Φ (c₀ (p, t)) = c₁ (p, t)) ∧
        Set.EqOn Φ id (c₀ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < ε})ᶜ :=
  ⟨ε, hε, le_rfl, Diffeomorph.refl (𝓡∂ 3) M ∞, fun p t ht => hagree p t ht,
    fun _ _ => rfl⟩

private abbrev SphereTwo : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private abbrev ModelSpace : Type := SphereTwo × EuclideanHalfSpace 1

private theorem instT2SpaceHalfSpaceOne : T2Space (EuclideanHalfSpace 1) :=
  T2Space.of_injective_continuous (f := Subtype.val) Subtype.val_injective continuous_subtype_val

private theorem instSigmaCompactSpaceHalfSpaceOne : SigmaCompactSpace (EuclideanHalfSpace 1) :=
  IsClosed.sigmaCompactSpace
    (isClosed_Ici.preimage (EuclideanSpace.proj (𝕜 := ℝ) 0).continuous)

attribute [local instance] instT2SpaceHalfSpaceOne instSigmaCompactSpaceHalfSpaceOne
attribute [local instance] DifferentialGeometry.Manifold.euclideanHalfSpaceProdChartedSpace

private theorem modelSpace_isManifold : IsManifold (𝓡∂ 3) ∞ ModelSpace :=
  DifferentialGeometry.Manifold.euclideanHalfSpaceProd_isManifold ModelSpace

attribute [local instance] modelSpace_isManifold

private theorem halfSpaceOneLift_coordinate (t : ℝ) : (halfSpaceOneLift t).1 0 = max t 0 := rfl

private theorem halfSpaceOneLift_eq_self (t : EuclideanHalfSpace 1) :
    halfSpaceOneLift (t.1 0) = t := by
  rw [halfSpaceOneLift_eq]
  have heq : (⟨max 0 (t.1 0), le_max_left 0 (t.1 0)⟩ : Ici (0 : ℝ)) =
      halfSpaceOneHomeomorph t := Subtype.ext (max_eq_right t.2)
  rw [heq]
  exact halfSpaceOneHomeomorph.symm_apply_apply t

private theorem halfSpaceOneLift_mul {lam t : ℝ} (h : 0 ≤ lam * t) :
    (halfSpaceOneLift (lam * t)).1 0 = lam * t := by
  rw [halfSpaceOneLift_coordinate, max_eq_left h]

private theorem halfSpaceOneLift_zero : halfSpaceOneLift (0 : ℝ) = 0 := by
  rw [show (0 : ℝ) = ((0 : EuclideanHalfSpace 1).1 0) from rfl]
  exact halfSpaceOneLift_eq_self 0

private theorem zero_mem_boundary_halfSpaceOne :
    (0 : EuclideanHalfSpace 1) ∈ (𝓡∂ 1).boundary (EuclideanHalfSpace 1) := by
  change (Subtype.val (0 : EuclideanHalfSpace 1)) ∈ frontier (range Subtype.val)
  rw [range_euclideanHalfSpace, frontier_halfSpace]
  rfl

private theorem sphereTwoBasePoint_mem :
    EuclideanSpace.single (0 : Fin 3) (1 : ℝ) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  simp

private def sphereTwoBasePoint : SphereTwo :=
  ⟨EuclideanSpace.single (0 : Fin 3) (1 : ℝ), sphereTwoBasePoint_mem⟩

private noncomputable def halfLineDilation (lam : ℝ) (hlam : 0 < lam) :
    PartialDiffeomorph (𝓡∂ 1) (𝓡∂ 1)
      (EuclideanHalfSpace 1) (EuclideanHalfSpace 1) ∞ where
  toPartialEquiv :=
    { toFun := fun t => halfSpaceOneLift (lam * t.1 0)
      invFun := fun t => halfSpaceOneLift (lam⁻¹ * t.1 0)
      source := univ
      target := univ
      map_source' := fun _ _ => mem_univ _
      map_target' := fun _ _ => mem_univ _
      left_inv' := fun t _ => by
        rw [halfSpaceOneLift_mul (lam := lam) (t := t.1 0) (mul_nonneg hlam.le t.2)]
        have h2 : lam⁻¹ * (lam * t.1 0) = t.1 0 := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hlam), one_mul]
        rw [h2]
        exact halfSpaceOneLift_eq_self t
      right_inv' := fun t _ => by
        rw [halfSpaceOneLift_mul (lam := lam⁻¹) (t := t.1 0)
          (mul_nonneg (inv_pos.mpr hlam).le t.2)]
        have h2 : lam * (lam⁻¹ * t.1 0) = t.1 0 := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hlam), one_mul]
        rw [h2]
        exact halfSpaceOneLift_eq_self t }
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    have h1 : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ (fun t : EuclideanHalfSpace 1 => lam * t.1 0) :=
      (contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_halfSpaceOneCoordinate
    exact ((contMDiffOn_halfSpaceOneLift).comp_contMDiff h1
      (fun t => by simp only [Set.mem_Ici]; exact mul_nonneg hlam.le t.2)).contMDiffOn
  contMDiffOn_invFun := by
    have h1 : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞
        (fun t : EuclideanHalfSpace 1 => lam⁻¹ * t.1 0) :=
      (contDiff_const.mul contDiff_id).contMDiff.comp contMDiff_halfSpaceOneCoordinate
    exact ((contMDiffOn_halfSpaceOneLift).comp_contMDiff h1
      (fun t => by
        simp only [Set.mem_Ici]
        exact mul_nonneg (inv_pos.mpr hlam).le t.2)).contMDiffOn

private noncomputable def modelDilation (lam : ℝ) (hlam : 0 < lam) :
    PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1))
      ModelSpace ModelSpace ∞ :=
  DifferentialGeometry.Topology.PartialDiffeomorph.prod
    (DifferentialGeometry.PartialDiffeomorph.refl (I := 𝓡 2) SphereTwo)
    (halfLineDilation lam hlam)

private theorem modelDilation_source (lam : ℝ) (hlam : 0 < lam) :
    (modelDilation lam hlam).source = univ := by
  change (DifferentialGeometry.PartialDiffeomorph.refl (I := 𝓡 2) SphereTwo).source ×ˢ
    (halfLineDilation lam hlam).source = univ
  rw [show (DifferentialGeometry.PartialDiffeomorph.refl (I := 𝓡 2) SphereTwo).source = univ
      from rfl,
    show (halfLineDilation lam hlam).source = univ from rfl]
  ext x
  simp

private theorem modelDilation_target (lam : ℝ) (hlam : 0 < lam) :
    (modelDilation lam hlam).target = univ := by
  change (DifferentialGeometry.PartialDiffeomorph.refl (I := 𝓡 2) SphereTwo).target ×ˢ
    (halfLineDilation lam hlam).target = univ
  rw [show (DifferentialGeometry.PartialDiffeomorph.refl (I := 𝓡 2) SphereTwo).target = univ
      from rfl,
    show (halfLineDilation lam hlam).target = univ from rfl]
  ext x
  simp

private noncomputable def modelIdentity :
    PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ModelSpace ModelSpace ∞ where
  toPartialEquiv := PartialEquiv.refl ModelSpace
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun :=
    (DifferentialGeometry.Manifold.contMDiffOn_chartedSpaceTransHomeomorph_iff
      (I := (𝓡 2).prod (𝓡∂ 1)) (J := 𝓡∂ 3)
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph_model
      (I₀ := (𝓡 2).prod (𝓡∂ 1))).mpr contMDiff_id.contMDiffOn
  contMDiffOn_invFun :=
    (DifferentialGeometry.Manifold.contMDiffOn_chartedSpaceTransHomeomorph_iff
      (I := (𝓡 2).prod (𝓡∂ 1)) (J := 𝓡∂ 3)
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdCoordinates
      DifferentialGeometry.Manifold.euclideanHalfSpaceProdHomeomorph_model
      (I₀ := 𝓡∂ 3)).mp contMDiff_id.contMDiffOn

private noncomputable def modelStraighteningCollar (lam : ℝ) (hlam : 0 < lam) :
    PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ModelSpace ModelSpace ∞ where
  toPartialEquiv := (modelDilation lam hlam).toPartialEquiv
  open_source := (modelDilation lam hlam).open_source
  open_target := (modelDilation lam hlam).open_target
  contMDiffOn_toFun := by
    have hD : ContMDiffOn ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1)) ∞
        (fun x => (modelDilation lam hlam) x) (modelDilation lam hlam).source :=
      (modelDilation lam hlam).contMDiffOn_toFun
    have hid : ContMDiffOn ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞
        (id : ModelSpace → ModelSpace) univ :=
      modelIdentity.contMDiffOn_toFun
    exact hid.comp hD (fun x _ => mem_univ _)
  contMDiffOn_invFun := by
    have hD : ContMDiffOn ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod (𝓡∂ 1)) ∞
        (fun x => (modelDilation lam hlam).symm x) univ :=
      (modelDilation lam hlam).contMDiffOn_invFun.mono (fun x _ => by
        rw [modelDilation_target lam hlam]
        exact mem_univ x)
    have hid : ContMDiffOn (𝓡∂ 3) ((𝓡 2).prod (𝓡∂ 1)) ∞
        (id : ModelSpace → ModelSpace) (modelDilation lam hlam).target := by
      rw [modelDilation_target lam hlam]
      exact modelIdentity.contMDiffOn_invFun
    exact hD.comp hid (fun x _ => mem_univ _)

private theorem modelStraighteningCollar_apply (lam : ℝ) (hlam : 0 < lam)
    (p : SphereTwo) (t : EuclideanHalfSpace 1) :
    modelStraighteningCollar lam hlam (p, t) = (p, halfSpaceOneLift (lam * t.1 0)) :=
  rfl

private theorem modelStraighteningCollar_source (lam : ℝ) (hlam : 0 < lam) :
    (modelStraighteningCollar lam hlam).source = univ :=
  modelDilation_source lam hlam

private theorem sphereTwo_mem_boundary (p : SphereTwo) :
    ((p, (0 : EuclideanHalfSpace 1)) : ModelSpace) ∈ (𝓡∂ 3).boundary ModelSpace := by
  rw [DifferentialGeometry.Manifold.euclideanHalfSpaceProd_boundary ModelSpace,
    ModelWithCorners.boundary_prod]
  exact Or.inl ⟨mem_univ _, zero_mem_boundary_halfSpaceOne⟩

theorem not_boundaryCollarStraightening_of_dilation_collar {C : ℝ}
    (S : Type u) [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S]
    (M : Type u) [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    [IsManifold (𝓡∂ 3) ∞ M] [T2Space M] [SigmaCompactSpace M]
    (p₀ : S)
    (c₀ c₁ : PartialDiffeomorph ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3)
      (S × EuclideanHalfSpace 1) M ∞)
    (hsrc : ∀ p : S, (p, 0) ∈ c₀.source ∧ (p, 0) ∈ c₁.source)
    (hcore : ∀ p : S, c₀ (p, 0) = c₁ (p, 0))
    (hbdy : ∀ p : S, c₀ (p, 0) ∈ (𝓡∂ 3).boundary M)
    {lam ε : ℝ} (hC1 : 1 ≤ C) (hlam : 0 < lam) (hClam : C < lam) (hε : 0 < ε)
    (hdil : ∀ (p : S) (t : EuclideanHalfSpace 1),
      c₁ (p, t) = c₀ (p, halfSpaceOneLift (lam * t.1 0)))
    (hinj : Set.InjOn c₀ {q : S × EuclideanHalfSpace 1 | q.2.1 0 < lam * ε}) :
    ¬ BoundaryCollarStraightening.{u} C := by
  intro h
  obtain ⟨δ, hδ, hδε, Φ, hmatch, hsupp⟩ := h c₀ c₁ hsrc hcore hbdy ε hε
  have hnest := collarImage_subset_of_supported_matching_of_le c₀ c₁ (⇑Φ)
    (δ := δ) (η := C * δ) (by nlinarith [hC1, hδ]) Φ.injective hsupp hmatch
  have hkey : 2 * C < max C 0 + lam := by
    rcases le_or_gt 0 C with hC0 | hC0
    · rw [max_eq_left hC0]; linarith
    · rw [max_eq_right hC0.le]; linarith
  set t0 : ℝ := δ * (max C 0 + lam) / (2 * lam) with ht0
  have ht0_nonneg : 0 ≤ t0 := by
    rw [ht0]
    exact div_nonneg (mul_nonneg hδ.le (by have := le_max_right C 0; linarith)) (by positivity)
  have ht0_lt : t0 < δ := by
    rw [ht0, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * lam)]
    have h1 : max C 0 + lam < 2 * lam := by have := max_lt hClam hlam; linarith
    have h2 : δ * (max C 0 + lam) < δ * (2 * lam) := mul_lt_mul_of_pos_left h1 hδ
    linarith [h2]
  have ht0_gt : C * δ / lam < t0 := by
    rw [ht0, div_lt_div_iff₀ hlam (by positivity : (0 : ℝ) < 2 * lam)]
    have h2 : (2 * C) * (δ * lam) < (max C 0 + lam) * (δ * lam) :=
      mul_lt_mul_of_pos_right hkey (by positivity : (0 : ℝ) < δ * lam)
    nlinarith [h2]
  have hlift0 : (halfSpaceOneLift t0).1 0 = t0 := by
    rw [halfSpaceOneLift_coordinate, max_eq_left ht0_nonneg]
  have hmem : c₁ (p₀, halfSpaceOneLift t0) ∈
      c₁ '' {q : S × EuclideanHalfSpace 1 | q.2.1 0 < δ} :=
    ⟨(p₀, halfSpaceOneLift t0), by
      simp only [Set.mem_ofPred_eq]
      rw [hlift0]
      exact ht0_lt, rfl⟩
  obtain ⟨q, hq, hqx⟩ := hnest hmem
  have hq' : q.2.1 0 < C * δ := hq
  have hx : c₁ (p₀, halfSpaceOneLift t0) = c₀ (p₀, halfSpaceOneLift (lam * t0)) := by
    rw [hdil p₀ (halfSpaceOneLift t0), hlift0]
  have hlamt0_lift : (halfSpaceOneLift (lam * t0)).1 0 = lam * t0 :=
    halfSpaceOneLift_mul (lam := lam) (t := t0) (mul_nonneg hlam.le ht0_nonneg)
  have hqin : q ∈ {q : S × EuclideanHalfSpace 1 | q.2.1 0 < lam * ε} := by
    simp only [Set.mem_ofPred_eq]
    have h1 : C * δ < lam * δ := by nlinarith [hClam, hδ]
    have h2 : lam * δ ≤ lam * ε := by nlinarith [hδε, hlam]
    linarith
  have hlin : (p₀, halfSpaceOneLift (lam * t0)) ∈
      {q : S × EuclideanHalfSpace 1 | q.2.1 0 < lam * ε} := by
    simp only [Set.mem_ofPred_eq]
    rw [hlamt0_lift]
    have h1 : lam * t0 < lam * δ := by nlinarith [ht0_lt, hlam]
    have h2 : lam * δ ≤ lam * ε := by nlinarith [hδε, hlam]
    linarith
  have heq : q = (p₀, halfSpaceOneLift (lam * t0)) := hinj hqin hlin (hqx.trans hx)
  have hqeq : q.2.1 0 = lam * t0 := by rw [heq, hlamt0_lift]
  have hcontr : lam * t0 < C * δ := by rw [← hqeq]; exact hq'
  have hgt : C * δ < lam * t0 := by
    have hh := mul_lt_mul_of_pos_right ht0_gt hlam
    rw [div_mul_cancel₀ _ (ne_of_gt hlam)] at hh
    linarith [hh]
  exact absurd hcontr (not_lt.mpr hgt.le)

theorem not_boundaryCollarStraightening_sphereTwoHalfSpace (C : ℝ) (hC : 1 ≤ C) :
    ¬ BoundaryCollarStraightening.{0} C := by
  set lam : ℝ := max C 0 + 1 with hlamdef
  have hlam : 0 < lam := by rw [hlamdef]; positivity
  have hClam : C < lam := by rw [hlamdef]; linarith [le_max_left C 0]
  refine not_boundaryCollarStraightening_of_dilation_collar (C := C) SphereTwo ModelSpace
    sphereTwoBasePoint modelIdentity (modelStraighteningCollar lam hlam) ?_ ?_ ?_
    hC hlam hClam one_pos ?_ ?_
  · intro p
    refine ⟨mem_univ _, ?_⟩
    rw [modelStraighteningCollar_source lam hlam]
    exact mem_univ _
  · intro p
    rw [modelStraighteningCollar_apply]
    change ((p, (0 : EuclideanHalfSpace 1)) : ModelSpace) = (p, halfSpaceOneLift (lam * (0 : ℝ)))
    rw [mul_zero, halfSpaceOneLift_zero]
  · intro p
    exact sphereTwo_mem_boundary p
  · intro p t
    rw [modelStraighteningCollar_apply]
    rfl
  · intro a b _ _ h
    exact h

theorem not_boundaryCollarStraighteningWithBoundedSupport :
    ¬ BoundaryCollarStraighteningWithBoundedSupport.{0} := by
  rintro ⟨C, hC, h⟩
  exact not_boundaryCollarStraightening_sphereTwoHalfSpace C hC h

end DifferentialGeometry.Topology.Collar
