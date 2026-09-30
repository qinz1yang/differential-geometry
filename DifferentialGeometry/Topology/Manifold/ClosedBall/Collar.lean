import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.Manifold.HalfCollarExtension
import DifferentialGeometry.Topology.Manifold.SpherePolarCoordinates

set_option autoImplicit false
noncomputable section

open Set Manifold Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {m : ℕ}
local notation "EuN" => EuclideanSpace ℝ (Fin (m + 1))
local notation "Sphere" => Metric.sphere (0 : EuN) 1
local notation "Half" => Ico (0 : ℝ) (1 / 2)
local notation "CI" => ModelWithCorners.prod (𝓡 m) (𝓡∂ 1)
local notation "PI" => ModelWithCorners.prod (𝓡 m) 𝓘(ℝ, ℝ)

private local instance closedCellCharts : ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  Handle.closedCellChartedSpaceSucc m
private local instance closedCellSmooth : IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  Handle.closedCellIsManifold m
private local instance sphereDimension : Fact (Module.finrank ℝ EuN = m + 1) := ⟨by simp⟩
private local instance halfCharts : ChartedSpace (EuclideanHalfSpace 1) Half :=
  halfClosedIntervalChartedSpace (by norm_num : (0 : ℝ) < 1 / 2)
private local instance halfSmooth : IsManifold (𝓡∂ 1) ∞ Half :=
  halfClosedInterval_isManifold (by norm_num : (0 : ℝ) < 1 / 2)

private theorem norm_radial_le (z : Sphere) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ‖(1 - t) • z.val‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht'), norm_eq_of_mem_sphere, mul_one]
  linarith

private def radialHalfCell (p : Sphere × Half) : ClosedCell (m + 1) :=
  ⟨(1 - p.2.val) • p.1.val, norm_radial_le p.1 p.2.property.1 (by linarith [p.2.property.2])⟩

private theorem radialHalfCell_contMDiff : ContMDiff CI (𝓡∂ (m + 1)) ∞ (radialHalfCell (m := m)) := by
  have hi : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (Subtype.val : Half → ℝ) :=
    (isSmoothEmbedding_halfClosedInterval_inclusion (by norm_num : (0 : ℝ) < 1 / 2)).contMDiff
  have hrad : ContMDiff CI (𝓡 (m + 1)) ∞
      (fun p : Sphere × Half => (1 - p.2.val) • p.1.val) :=
    (contMDiff_const.sub (hi.comp contMDiff_snd)).smul
      (contMDiff_coe_sphere.comp contMDiff_fst)
  apply (ContMDiff.iff_comp_isImmersion (isSmoothEmbedding_closedCell_inclusion (m := m)).isImmersion).mpr
  exact ⟨hrad.continuous.subtype_mk _, hrad⟩

private def reverseRadius : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun t := 1 - t
  invFun t := 1 - t
  left_inv t := by dsimp; ring
  right_inv t := by dsimp; ring
  contMDiff_toFun := contMDiff_const.sub contMDiff_id
  contMDiff_invFun := contMDiff_const.sub contMDiff_id

private theorem radialHalfCell_mfderiv_bijective (p : Sphere × Half) :
    Function.Bijective (mfderiv CI (𝓡∂ (m + 1)) radialHalfCell p) := by
  let e : Sphere × Half → Sphere × ℝ := Prod.map id Subtype.val
  have hs : IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (Subtype.val : Half → ℝ) :=
    isSmoothEmbedding_halfClosedInterval_inclusion (by norm_num : (0 : ℝ) < 1 / 2)
  have he : ContMDiff CI PI ∞ e := contMDiff_id.prodMap hs.contMDiff
  have hBe : Function.Bijective (mfderiv CI PI e p) := by
    have hBs : Function.Bijective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (Subtype.val : Half → ℝ) p.2) :=
      bijective_mfderiv_of_isImmersionAt (𝓡∂ 1) 𝓘(ℝ, ℝ) Subtype.val p.2
        (hs.isImmersion.isImmersionAt p.2) (by simp)
    rw [mfderiv_prodMap mdifferentiableAt_id (hs.contMDiff.mdifferentiable (by simp) _), mfderiv_id]
    exact Function.bijective_id.prodMap hBs
  let R : Diffeomorph PI PI (Sphere × ℝ) (Sphere × ℝ) ∞ :=
    (Diffeomorph.refl (𝓡 m) Sphere ∞).prodCongr reverseRadius
  let g : Sphere × ℝ → EuN := fun q => (R q).2 • ((R q).1 : EuN)
  have hpos : 0 < (R (e p)).2 := by
    change 0 < 1 - p.2.val
    linarith [p.2.property.2]
  have hg : IsLocalDiffeomorphAt PI (𝓡 (m + 1)) ∞ g (e p) :=
    (R.isLocalDiffeomorph (e p)).comp (𝓡 (m + 1)) EuN
      (isLocalDiffeomorphAt_sphere_smul (R (e p)) hpos)
  have hBg : Function.Bijective (mfderiv PI (𝓡 (m + 1)) g (e p)) :=
    (hg.mfderivToContinuousLinearEquiv (by simp)).bijective
  have hcomp : mfderiv CI (𝓡 (m + 1))
      ((Subtype.val : ClosedCell (m + 1) → EuN) ∘ radialHalfCell) p =
      (mfderiv PI (𝓡 (m + 1)) g (e p)).comp (mfderiv CI PI e p) :=
    mfderiv_comp p (hg.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))
  have hB : Function.Bijective (mfderiv CI (𝓡 (m + 1))
      ((Subtype.val : ClosedCell (m + 1) → EuN) ∘ radialHalfCell) p) := by
    rw [hcomp]
    exact hBg.comp hBe
  have hchain := mfderiv_comp p
    ((isSmoothEmbedding_closedCell_inclusion (m := m)).contMDiff.mdifferentiableAt (by simp))
    ((radialHalfCell_contMDiff (m := m)).mdifferentiableAt (by simp))
  rw [hchain] at hB
  change Function.Bijective
    ((mfderiv (𝓡∂ (m + 1)) (𝓡 (m + 1))
      (Subtype.val : ClosedCell (m + 1) → EuN) (radialHalfCell p)) ∘
      (mfderiv CI (𝓡∂ (m + 1)) radialHalfCell p)) at hB
  exact Function.Bijective.of_comp_left hB
    (((isSmoothEmbedding_closedCell_inclusion (m := m)).isImmersion.isImmersionAt _).mfderiv_injective
      (by simp))

variable {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) N]
  [IsManifold (𝓡 (m + 1)) ∞ N] [T2Space N]

theorem exists_smoothTwoSidedCollar_of_closedCell_embedding
    (f : ClosedCell (m + 1) → N)
    (hf : IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞ f) :
    ∃ d : SmoothTwoSidedCollar (𝓡 m) (𝓡 (m + 1))
        (fun z : Sphere => f ⟨z.val, (norm_eq_of_mem_sphere z).le⟩),
      ∃ hwidth : d.radius ≤ 1 / 2,
      ∀ (p : Sphere × symmetricOpenInterval d.radius) (hp : 0 ≤ p.2.val),
        d.toFun p = f ⟨(1 - p.2.val) • p.1.val, by
          apply norm_radial_le p.1 hp
          linarith [p.2.property.2]⟩ := by
  let c : Sphere × Half → N := f ∘ radialHalfCell
  have hc : ContMDiff CI (𝓡 (m + 1)) ∞ c := hf.contMDiff.comp radialHalfCell_contMDiff
  have hinj : Function.Injective (fun z : Sphere => c (z, (⟨0, by constructor <;> norm_num⟩ : Half))) := by
    intro z w h
    have h' := congrArg Subtype.val (hf.isEmbedding.injective h)
    apply Subtype.ext
    simpa only [radialHalfCell, sub_zero, one_smul] using h'
  have hderiv : ∀ z : Sphere, Function.Bijective (mfderiv CI (𝓡 (m + 1)) c
      (z, (⟨0, by constructor <;> norm_num⟩ : Half))) := by
    intro z
    rw [show c = f ∘ radialHalfCell from rfl, mfderiv_comp _
      (hf.contMDiff.mdifferentiableAt (by simp))
      ((radialHalfCell_contMDiff (m := m)).mdifferentiableAt (by simp))]
    exact (bijective_mfderiv_of_isImmersionAt (𝓡∂ (m + 1)) (𝓡 (m + 1)) f _
      (hf.isImmersion.isImmersionAt _) rfl).comp (radialHalfCell_mfderiv_bijective _)
  have hzero : (fun z : Sphere => c (z, (⟨0, by constructor <;> norm_num⟩ : Half))) =
      fun z : Sphere => f ⟨z.val, (norm_eq_of_mem_sphere z).le⟩ := by
    funext z
    change f ⟨(1 - 0) • z.val, _⟩ = _
    congr 1
    exact Subtype.ext (by simp)
  obtain ⟨d, hwidth, hd⟩ := exists_smoothTwoSidedCollar_of_halfClosedInterval
    (J := 𝓡 m) (I := 𝓡 (m + 1)) (by norm_num : (0 : ℝ) < 1 / 2) c hc hinj hderiv
  let d' : SmoothTwoSidedCollar (𝓡 m) (𝓡 (m + 1))
      (fun z : Sphere => f ⟨z.val, (norm_eq_of_mem_sphere z).le⟩) :=
    { radius := d.radius
      radius_pos := d.radius_pos
      neighborhood := d.neighborhood
      toDiffeomorph := d.toDiffeomorph
      zero_eq := fun z => (d.zero_eq z).trans (congrFun hzero z) }
  exact ⟨d', hwidth, hd⟩

end DifferentialGeometry.Topology.Manifold
