import DifferentialGeometry.Topology.Manifold.StereographicChart
import DifferentialGeometry.Topology.Manifold.StereographicClosedBall
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.BallComplement

noncomputable section

open Set Metric Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S3" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

private def stereographicInversePartial (p : S3) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ where
  toPartialEquiv := (stereographic' 3 p).symm.toPartialEquiv
  open_source := (stereographic' 3 p).symm.open_source
  open_target := (stereographic' 3 p).symm.open_target
  contMDiffOn_toFun := (stereographicInverse_isLocalDiffeomorph p).contMDiff.contMDiffOn
  contMDiffOn_invFun := (stereographic_isLocalDiffeomorphOn p).contMDiffOn

private def doubleSpace : E3 ≃ₘ[ℝ] E3 :=
  (LinearEquiv.smulOfNeZero ℝ E3 (2 : ℝ) (by norm_num)).toContinuousLinearEquiv.toDiffeomorph

private def standardHemisphereChart (p : S3) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ :=
  doubleSpace.toPartialDiffeomorph.trans (stereographicInversePartial p)

private def oppositeHemisphereChart (p : S3) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ :=
  (standardHemisphereChart p).trans
    (sphereAntipodalDiffeomorph (E := EuclideanSpace ℝ (Fin 4)) (n := 3)).toPartialDiffeomorph

private theorem standardHemisphereChart_source (p : S3) :
    (standardHemisphereChart p).source = univ := by
  ext x
  change (x ∈ (univ : Set E3) ∧ doubleSpace x ∈ (stereographic' 3 p).target) ↔ x ∈ univ
  rw [stereographic'_target]
  simp only [mem_univ, and_self]

private theorem oppositeHemisphereChart_source (p : S3) :
    (oppositeHemisphereChart p).source = univ := by
  ext x
  change (x ∈ (standardHemisphereChart p).source ∧
    standardHemisphereChart p x ∈ (univ : Set S3)) ↔ x ∈ univ
  rw [standardHemisphereChart_source]
  simp only [mem_univ, and_self]

private theorem doubleSpace_image_ball : doubleSpace '' ball (0 : E3) 1 = ball 0 2 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_ball_zero_iff]
    change ‖(2 : ℝ) • y‖ < 2
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := mem_ball_zero_iff.mp hy
    linarith
  · intro hx
    refine ⟨(1 / 2 : ℝ) • x, ?_, ?_⟩
    · rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have h := mem_ball_zero_iff.mp hx
      linarith
    · change (2 : ℝ) • ((1 / 2 : ℝ) • x) = x
      rw [smul_smul]
      norm_num

private theorem doubleSpace_image_closedBall :
    doubleSpace '' closedBall (0 : E3) 1 = closedBall 0 2 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_closedBall_zero_iff]
    change ‖(2 : ℝ) • y‖ ≤ 2
    rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have h := mem_closedBall_zero_iff.mp hy
    linarith
  · intro hx
    refine ⟨(1 / 2 : ℝ) • x, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have h := mem_closedBall_zero_iff.mp hx
      linarith
    · change (2 : ℝ) • ((1 / 2 : ℝ) • x) = x
      rw [smul_smul]
      norm_num

private theorem hemisphere_complement (p : S3) :
    (oppositeHemisphereChart p) '' closedBall (0 : E3) 1 =
      ((standardHemisphereChart p) '' ball (0 : E3) 1)ᶜ := by
  have h := antipodal_image_stereographic_symm_closedBall (n := 3) p (by norm_num : (0 : ℝ) < 2)
  norm_num only [show (4 : ℝ) / 2 = 2 by norm_num] at h
  change (Neg.neg ∘ ((stereographic' 3 p).symm ∘ doubleSpace)) '' closedBall 0 1 =
    (((stereographic' 3 p).symm ∘ doubleSpace) '' ball 0 1)ᶜ
  rw [image_comp, image_comp, image_comp, doubleSpace_image_closedBall, doubleSpace_image_ball]
  exact h

theorem exists_sphere_diffeomorph_of_complementary_ball_charts
    {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
    (A B : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 M ∞)
    (hA : closedBall (0 : E3) 1 ⊆ A.source)
    (hB : closedBall (0 : E3) 1 ⊆ B.source)
    (hcover : B '' ball (0 : E3) 1 = (A '' closedBall (0 : E3) 1)ᶜ) :
    ∃ e : S3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ M,
      ∃ a b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞,
        a.source = univ ∧ b.source = univ ∧
        a '' closedBall (0 : E3) 1 = (b '' ball (0 : E3) 1)ᶜ ∧
        (∀ z ∈ closedBall (0 : E3) 1, e (a z) = A z) ∧
        ∃ D : E3 ≃ₘ[ℝ] E3,
          D '' closedBall (0 : E3) 1 = closedBall (0 : E3) 1 ∧
          ∀ z ∈ closedBall (0 : E3) 1, e (b z) = B (D z) := by
  let p : S3 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let b := standardHemisphereChart p
  let a := oppositeHemisphereChart p
  have ha : a.source = univ := oppositeHemisphereChart_source p
  have hb : b.source = univ := standardHemisphereChart_source p
  have hcomp : a '' closedBall (0 : E3) 1 = (b '' ball (0 : E3) 1)ᶜ :=
    hemisphere_complement p
  have hainv (z : E3) : a.symm (a z) = z := a.left_inv' (ha ▸ mem_univ z)
  let P := a.symm.trans A
  have hKP : (b '' ball (0 : E3) 1)ᶜ ⊆ P.source := by
    rw [← hcomp]
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨a.map_source (ha ▸ mem_univ z), ?_⟩
    change a.symm (a z) ∈ A.source
    rw [hainv z]
    exact hA hz
  have hPU : P '' (b '' ball (0 : E3) 1)ᶜ = A '' closedBall (0 : E3) 1 := by
    rw [← hcomp, image_image]
    apply image_congr
    intro z hz
    change A (a.symm (a z)) = A z
    rw [hainv z]
  obtain ⟨e, heP, _, D, hD, heB, _, _, _, _, _⟩ :=
    exists_diffeomorph_of_ball_complement_and_ball b P B
      (hb ▸ subset_univ _) hKP hB hPU hcover
  refine ⟨e, a, b, ha, hb, hcomp, ?_, D, hD, heB⟩
  intro z hz
  have he := heP (hcomp ▸ mem_image_of_mem a hz)
  change e (a z) = A (a.symm (a z)) at he
  rwa [hainv z] at he

end DifferentialGeometry.Topology.Manifold
