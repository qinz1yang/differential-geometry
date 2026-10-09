import DifferentialGeometry.Topology.ThreeManifold.PrimeDecomposition.Irreducible
import DifferentialGeometry.Topology.Manifold.SmoothBicollar
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.ThreeManifold.Surgery.FiniteCap.OriginalTubularEmbedding

/-!
# Tubes around smoothly embedded spheres

Every smoothly embedded `2`-sphere `e` in a closed oriented `3`-manifold has a smooth two-sided
collar (`exists_smoothTwoSidedCollar_of_smoothSphereEmbedding`). Rescaling the collar parameter
gives a buffered cylinder chart, whose restriction to `S² × [-2, 2]` is a one-tube spherical tube
system with middle sphere `e`. This proves `SphereTubeExtension`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set Metric
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Topology.ThreeManifold.Surgery
open scoped Manifold ContDiff

namespace GC.Endpoint

universe u

private local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

private theorem mem_bufferedCylinder_half (q : bufferedCylinder (1 / 2)) :
    -3 < q.1.2 ∧ q.1.2 < 3 := by
  have h : -(1 / 2 : ℝ)⁻¹ - 1 < q.1.2 ∧ q.1.2 < (1 / 2 : ℝ)⁻¹ + 1 := q.2
  norm_num at h
  exact h

private def bufferedCollarScale (r : ℝ) (hr : 0 < r) :
    bufferedCylinder (1 / 2) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ), (𝓡 2).prod 𝓘(ℝ)⟯
      (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × symmetricOpenInterval r) where
  toFun q := (q.1.1, ⟨r / 3 * q.1.2, by
    obtain ⟨h₁, h₂⟩ := mem_bufferedCylinder_half q
    constructor <;> nlinarith⟩)
  invFun p := ⟨(p.1, 3 / r * p.2.1), by
    have h : -r < p.2.1 ∧ p.2.1 < r := p.2.2
    change -(1 / 2 : ℝ)⁻¹ - 1 < 3 / r * p.2.1 ∧ 3 / r * p.2.1 < (1 / 2 : ℝ)⁻¹ + 1
    rw [div_mul_eq_mul_div]
    norm_num
    constructor
    · rw [lt_div_iff₀ hr]; nlinarith
    · rw [div_lt_iff₀ hr]; nlinarith⟩
  left_inv q := by
    refine Subtype.ext (Prod.ext rfl ?_)
    change 3 / r * (r / 3 * q.1.2) = q.1.2
    field_simp
  right_inv p := by
    refine Prod.ext rfl (Subtype.ext ?_)
    change r / 3 * (3 / r * p.2.1) = p.2.1
    field_simp
  contMDiff_toFun := by
    refine (contMDiff_fst.comp contMDiff_subtype_val).prodMk ?_
    exact (ContMDiff.subtypeVal_comp_iff (symmetricOpenInterval r) _).mp
      (contMDiff_const.mul (contMDiff_snd.comp contMDiff_subtype_val))
  contMDiff_invFun := by
    refine (ContMDiff.subtypeVal_comp_iff (bufferedCylinder (1 / 2)) _).mp ?_
    exact contMDiff_fst.prodMk
      (contMDiff_const.mul (contMDiff_subtype_val.comp contMDiff_snd))

variable {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  {e : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → X}

private def collarBufferedChart (h : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) e) :
    bufferedCylinder (1 / 2) → X :=
  h.toFun ∘ bufferedCollarScale h.radius h.radius_pos

private theorem isOpenEmbedding_collarBufferedChart
    (h : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) e) :
    Topology.IsOpenEmbedding (collarBufferedChart h) :=
  h.isOpenEmbedding_toFun.comp
    (bufferedCollarScale h.radius h.radius_pos).toHomeomorph.isOpenEmbedding

private theorem isLocalDiffeomorph_collarBufferedChart
    (h : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) e) :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ)) (𝓡 3) ∞ (collarBufferedChart h) :=
  isLocalDiffeomorph_comp
    (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val h.neighborhood)
      h.toDiffeomorph.isLocalDiffeomorph)
    (bufferedCollarScale h.radius h.radius_pos).isLocalDiffeomorph

private theorem collarBufferedChart_zero (h : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) e)
    (z : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    originalTubularMap (by norm_num) (by norm_num) (collarBufferedChart h)
      (z, ⟨0, by norm_num, by norm_num⟩) = e z :=
  (congrArg (fun t => h.toFun (z, t)) (Subtype.ext (mul_zero _))).trans (h.toFun_zero z)

private theorem isSmoothEmbedding_collarTube [IsManifold (𝓡 3) ∞ X]
    (h : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) e) :
    Manifold.IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞
      (originalTubularMap (by norm_num) (by norm_num) (collarBufferedChart h)) :=
  originalTubularMap_isSmoothEmbedding (𝓡 3) (by simp) _ _ _
    (isOpenEmbedding_collarBufferedChart h) (isLocalDiffeomorph_collarBufferedChart h)

private def collarTubeSystem {M : ClosedOrientedManifold.{u} 3}
    {e : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M.Carrier}
    (h : SmoothTwoSidedCollar (𝓡 2) (𝓡 3) e) : SphericalTubeSystem M where
  Index := Unit
  tube _ := ⟨originalTubularMap (by norm_num) (by norm_num) (collarBufferedChart h),
    (isSmoothEmbedding_collarTube h).isEmbedding.continuous⟩
  smooth _ := isSmoothEmbedding_collarTube h
  disjoint a b hab := (hab (Subsingleton.elim a b)).elim

theorem sphereTubeExtension : SphereTubeExtension.{u} := by
  intro M e he
  obtain ⟨h⟩ := exists_smoothTwoSidedCollar_of_smoothSphereEmbedding e he
  exact ⟨collarTubeSystem (M := M.toClosedOrientedManifold) h,
    inferInstanceAs (Subsingleton Unit), (), funext fun z => collarBufferedChart_zero h z⟩

end GC.Endpoint
