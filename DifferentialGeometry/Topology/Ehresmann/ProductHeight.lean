import DifferentialGeometry.Topology.Ehresmann.BoundaryCompletion
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Icc
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

variable {E F H G W B : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace W] [ChartedSpace H W]
  [TopologicalSpace B] [ChartedSpace G B]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F G}

def heightOfIntervalProduct (D : Diffeomorph (J.prod (𝓡∂ 1)) I (B × unitInterval) W ∞) : W → ℝ :=
  fun w ↦ (D.symm w).2.val

theorem heightOfIntervalProduct_apply
    (D : Diffeomorph (J.prod (𝓡∂ 1)) I (B × unitInterval) W ∞) (q : B × unitInterval) :
    heightOfIntervalProduct D (D q) = q.2.val := by
  simp only [heightOfIntervalProduct, D.symm_apply_apply]

theorem preimage_heightOfIntervalProduct_singleton
    (D : Diffeomorph (J.prod (𝓡∂ 1)) I (B × unitInterval) W ∞) (t : unitInterval) :
    heightOfIntervalProduct D ⁻¹' {(t : ℝ)} = range (fun p : B ↦ D (p, t)) := by
  ext w
  constructor
  · intro hw
    have ht : (D.symm w).2 = t := Subtype.ext hw
    refine ⟨(D.symm w).1, ?_⟩
    rw [← ht]
    exact D.apply_symm_apply w
  · rintro ⟨p, rfl⟩
    exact heightOfIntervalProduct_apply D (p, t)

theorem isBoundaryPoint_iff_heightOfIntervalProduct
    [BoundarylessManifold J B]
    (D : Diffeomorph (J.prod (𝓡∂ 1)) I (B × unitInterval) W ∞) (w : W) :
    I.IsBoundaryPoint w ↔ heightOfIntervalProduct D w = 0 ∨ heightOfIntervalProduct D w = 1 := by
  rw [(D.symm.isLocalDiffeomorph w).isBoundaryPoint_iff (by decide)]
  change D.symm w ∈ (J.prod (𝓡∂ 1)).boundary (B × unitInterval) ↔ _
  rw [J.boundary_of_boundaryless_left, boundary_Icc]
  change (True ∧ ((D.symm w).2 = 0 ∨ (D.symm w).2 = 1)) ↔ _
  simp only [true_and, heightOfIntervalProduct, Subtype.ext_iff]
  rfl

theorem boundary_eq_range_intervalProduct_ends
    [BoundarylessManifold J B]
    (D : Diffeomorph (J.prod (𝓡∂ 1)) I (B × unitInterval) W ∞) :
    I.boundary W = range (fun p : B ↦ D (p, 0)) ∪ range (fun p : B ↦ D (p, 1)) := by
  rw [← preimage_heightOfIntervalProduct_singleton D 0,
    ← preimage_heightOfIntervalProduct_singleton D 1]
  ext w
  exact isBoundaryPoint_iff_heightOfIntervalProduct D w

private theorem intervalProjection_noncritical (q : B × unitInterval) :
    mfderiv (J.prod (𝓡∂ 1)) 𝓘(ℝ) (fun p : B × unitInterval ↦ p.2.val) q ≠ 0 := by
  have hc := mfderiv_comp (I := J.prod (𝓡∂ 1)) q
    ((contMDiff_subtypeVal_Icc (n := ∞)).mdifferentiable (by decide) q.2) mdifferentiableAt_snd
  change mfderiv (J.prod (𝓡∂ 1)) 𝓘(ℝ) (fun p : B × unitInterval ↦ p.2.val) q =
    (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) q.2).comp
      (mfderiv (J.prod (𝓡∂ 1)) (𝓡∂ 1) Prod.snd q) at hc
  intro hz
  have he : (mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : unitInterval → ℝ) q.2) 1 = 0 := by
    have h := congrArg (fun L : (TangentSpace J q.1 × TangentSpace (𝓡∂ 1) q.2) →L[ℝ] ℝ ↦
      L (0, (1 : TangentSpace (𝓡∂ 1) q.2))) hz
    rw [hc, mfderiv_snd] at h
    exact h
  rw [mfderiv_subtypeVal_Icc_one] at he
  change (1 : ℝ) = 0 at he
  exact one_ne_zero he

theorem regularIntervalDatum_heightOfIntervalProduct
    [CompactSpace W] [PreconnectedSpace W] [Nonempty B] [BoundarylessManifold J B]
    (D : Diffeomorph (J.prod (𝓡∂ 1)) I (B × unitInterval) W ∞) :
    RegularIntervalDatum I (heightOfIntervalProduct D) 0 1 := by
  have hu : ContMDiff I 𝓘(ℝ) ∞ (heightOfIntervalProduct D) :=
    contMDiff_subtypeVal_Icc.comp (contMDiff_snd.comp D.symm.contMDiff)
  have hreg : ∀ w, mfderiv I 𝓘(ℝ) (heightOfIntervalProduct D) w ≠ 0 := by
    intro w hw
    let q := D.symm w
    have heq : heightOfIntervalProduct D ∘ D = (fun p : B × unitInterval ↦ p.2.val) :=
      funext (heightOfIntervalProduct_apply D)
    have hc := mfderiv_comp q (hu.mdifferentiable (by decide) (D q))
      (D.contMDiff.mdifferentiable (by decide) q)
    rw [heq] at hc
    have hDq : D q = w := D.apply_symm_apply w
    have huq : mfderiv I 𝓘(ℝ) (heightOfIntervalProduct D) (D q) = 0 := by
      rw [hDq]
      exact hw
    rw [huq, ContinuousLinearMap.zero_comp] at hc
    exact intervalProjection_noncritical q hc
  have hbdy : ∀ w, I.IsBoundaryPoint w →
      heightOfIntervalProduct D w = 0 ∨ heightOfIntervalProduct D w = 1 := by
    intro w hw
    have hb := ((D.symm.isLocalDiffeomorph w).isBoundaryPoint_iff (by decide)).mp hw
    change D.symm w ∈ (J.prod (𝓡∂ 1)).boundary (B × unitInterval) at hb
    rw [J.boundary_of_boundaryless_left, boundary_Icc] at hb
    rcases hb.2 with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  let b := Classical.arbitrary B
  exact regularIntervalDatum_of_boundary_values zero_lt_one hu hreg hbdy
    ⟨D (b, 0), heightOfIntervalProduct_apply D (b, 0)⟩
    ⟨D (b, 1), heightOfIntervalProduct_apply D (b, 1)⟩

end DifferentialGeometry.Topology.Ehresmann
