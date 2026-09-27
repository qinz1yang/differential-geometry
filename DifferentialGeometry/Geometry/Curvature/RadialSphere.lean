import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.ImmersionCriterion
import DifferentialGeometry.Topology.NormedSphere
import Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section
open Set Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Curvature

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev Sphere2 := Metric.sphere (0 : E3) 1
private abbrev I2 := 𝓡 2
private abbrev I3 := 𝓡 3
private abbrev IC := I2.prod 𝓘(ℝ)

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private theorem isSmoothEmbedding_cylinder_slice
    (F : PartialDiffeomorph IC I3 (Sphere2 × ℝ) E3 ∞)
    {level : ℝ} (hsource : ∀ q : Sphere2, (q, level) ∈ F.source) :
    IsSmoothEmbedding I2 I3 ∞ (fun q : Sphere2 => F (q, level)) := by
  have hc : ContMDiff I2 I3 ∞ (fun q : Sphere2 => F (q, level)) :=
    contMDiffOn_univ.mp (F.contMDiffOn_toFun.comp
      (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun q _ => hsource q))
  refine ⟨DifferentialGeometry.Topology.Manifold.isImmersion_of_injective_mfderiv (by decide) hc ?_,
    hc.continuous.isClosedEmbedding (fun q z h =>
      congrArg Prod.fst (F.toPartialEquiv.injOn (hsource q) (hsource z) h)) |>.isEmbedding⟩
  intro q
  have hmd : F.toOpenPartialHomeomorph.MDifferentiable IC I3 :=
    ⟨F.contMDiffOn_toFun.mdifferentiableOn (by decide),
      F.contMDiffOn_invFun.mdifferentiableOn (by decide)⟩
  change Function.Injective (mfderiv I2 I3 (F ∘ fun z : Sphere2 => (z, level)) q)
  have hinc : ContMDiff I2 IC ∞ (fun z : Sphere2 => (z, level)) :=
    contMDiff_id.prodMk contMDiff_const
  rw [mfderiv_comp q (F.mdifferentiableAt (by decide) (hsource q))
    (hinc.mdifferentiableAt (by decide)), mfderiv_prod_left]
  exact (hmd.mfderiv_injective (hsource q)).comp (fun _ _ h => congrArg Prod.fst h)

theorem tangent_sectional_lower_bound_of_cylinder_chart
    (F : PartialDiffeomorph IC I3 (Sphere2 × ℝ) E3 ∞)
    (U : TopologicalSpace.Opens (Sphere2 × ℝ)) (hU : (U : Set (Sphere2 × ℝ)) ⊆ F.source)
    (hslice : ∀ z : Sphere2, (z, 0) ∈ U)
    (G : SmoothRiemannianMetric IC (Sphere2 × ℝ)) (h : SmoothRiemannianMetric I3 E3)
    (hmetric : ∀ x : U, ∀ v w : TangentSpace IC x,
      G.inner x.val v w = h.inner (F x.val) (mfderiv IC I3 F x.val v)
        (mfderiv IC I3 F x.val w))
    {c : ℝ} (hsec : ∀ (z : Sphere2) (u v : TangentSpace I2 z),
      c * (G.inner (z, 0) (u, 0) (u, 0) * G.inner (z, 0) (v, 0) (v, 0) -
        G.inner (z, 0) (u, 0) (v, 0) ^ 2) ≤
      metricRm04StandardAt G (z, 0) (u, 0) (v, 0) (v, 0) (u, 0)) :
    ∀ (z : Sphere2) (u v : TangentSpace I2 z),
      c * (h.inner (F (z, 0)) (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z u)
          (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z u) *
        h.inner (F (z, 0)) (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z v)
          (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z v) -
        h.inner (F (z, 0)) (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z u)
          (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z v) ^ 2) ≤
      metricRm04StandardAt h (F (z, 0))
        (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z u)
        (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z v)
        (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z v)
        (mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z u) := by
  intro z u v
  have hd (w : TangentSpace I2 z) :
      mfderiv I2 I3 (fun q : Sphere2 => F (q, 0)) z w =
        mfderiv IC I3 F (z, 0) (w, 0) := by
    change mfderiv I2 I3 (F ∘ fun q : Sphere2 => (q, 0)) z w = _
    have hi : ContMDiff I2 IC ∞ (fun q : Sphere2 => (q, (0 : ℝ))) :=
      contMDiff_id.prodMk contMDiff_const
    rw [mfderiv_comp z (F.mdifferentiableAt (by decide) (hU (hslice z)))
      (hi.mdifferentiableAt (by decide)), mfderiv_prod_left]
    rfl
  simp only [hd]
  have ht := hsec z u v
  have hg (a b : TangentSpace IC (z, (0 : ℝ))) :
      G.inner (z, 0) a b = h.inner (F (z, 0))
        (mfderiv IC I3 F (z, 0) a) (mfderiv IC I3 F (z, 0) b) :=
    hmetric ⟨(z, 0), hslice z⟩ a b
  have hr : metricRm04StandardAt G (z, 0) (u, 0) (v, 0) (v, 0) (u, 0) =
      metricRm04StandardAt h (F (z, 0)) (mfderiv IC I3 F (z, 0) (u, 0))
        (mfderiv IC I3 F (z, 0) (v, 0)) (mfderiv IC I3 F (z, 0) (v, 0))
        (mfderiv IC I3 F (z, 0) (u, 0)) :=
    metricRm04StandardAt_eq_of_partialDiffeomorph_restriction F U hU G h hmetric
      ⟨(z, 0), hslice z⟩ (u, 0) (v, 0) (v, 0) (u, 0)
  rwa [hg (u, 0) (u, 0), hg (v, 0) (v, 0), hg (u, 0) (v, 0), hr] at ht

theorem isSmoothEmbedding_and_frontier_and_tangent_sectional_lower_bound_of_radial_chart
    (F : PartialDiffeomorph IC I3 (Sphere2 × ℝ) E3 ∞)
    (U : TopologicalSpace.Opens (Sphere2 × ℝ)) (hU : (U : Set (Sphere2 × ℝ)) ⊆ F.source)
    (hslice : ∀ z : Sphere2, (z, 0) ∈ U)
    (G : SmoothRiemannianMetric IC (Sphere2 × ℝ)) (h : SmoothRiemannianMetric I3 E3)
    (hmetric : ∀ x : U, ∀ v w : TangentSpace IC x,
      G.inner x.val v w = h.inner (F x.val) (mfderiv IC I3 F x.val v)
        (mfderiv IC I3 F x.val w))
    {c : ℝ} (hsec : ∀ (z : Sphere2) (u v : TangentSpace I2 z),
      c * (G.inner (z, 0) (u, 0) (u, 0) * G.inner (z, 0) (v, 0) (v, 0) -
        G.inner (z, 0) (u, 0) (v, 0) ^ 2) ≤
      metricRm04StandardAt G (z, 0) (u, 0) (v, 0) (v, 0) (u, 0))
    {r : ℝ} (hr : 0 < r) (O : E3 ≃ₗᵢ[ℝ] E3)
    (hradial : ∀ z : Sphere2, F (z, 0) = r • O z.val) :
    let f : Sphere2 → E3 := fun z => F (z, 0)
    IsSmoothEmbedding I2 I3 ∞ f ∧
      frontier (Metric.closedBall (0 : E3) r) = range f ∧
      ∀ (z : Sphere2) (u v : TangentSpace I2 z),
        c * (h.inner (f z) (mfderiv I2 I3 f z u) (mfderiv I2 I3 f z u) *
          h.inner (f z) (mfderiv I2 I3 f z v) (mfderiv I2 I3 f z v) -
          h.inner (f z) (mfderiv I2 I3 f z u) (mfderiv I2 I3 f z v) ^ 2) ≤
        metricRm04StandardAt h (f z) (mfderiv I2 I3 f z u) (mfderiv I2 I3 f z v)
          (mfderiv I2 I3 f z v) (mfderiv I2 I3 f z u) := by
  refine ⟨isSmoothEmbedding_cylinder_slice F (fun z => hU (hslice z)), ?_,
    tangent_sectional_lower_bound_of_cylinder_chart F U hU hslice G h hmetric hsec⟩
  rw [Metric.frontier_closedBall_eq_range_smul_linearIsometryEquiv O hr]
  congr 1
  exact funext (fun z => (hradial z).symm)

end DifferentialGeometry.Geometry.Curvature
