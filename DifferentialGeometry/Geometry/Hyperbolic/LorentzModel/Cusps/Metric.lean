import DifferentialGeometry.Geometry.Curvature.Naturality.FlatCover
import DifferentialGeometry.Geometry.Hyperbolic.HorosphericalCoordinates.AffineMetric
import DifferentialGeometry.Geometry.Hyperbolic.Hyperboloid.RiemannianIsometry
import DifferentialGeometry.Topology.Manifold.HalfLine
import DifferentialGeometry.Geometry.Metric.WarpedProduct.Exponential
import DifferentialGeometry.Geometry.Hyperbolic.CuspMetric
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import Mathlib.Geometry.Manifold.Immersion
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Manifold
import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.SignedCylinder
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.SmoothCylinder
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.SmoothEmbedding

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Hyperboloid

open Horospherical

private theorem contMDiff_horospherical_halfSpace (m : ℕ) (b : ℝ) :
    ContMDiff ((𝓘(ℝ, Horizontal m)).prod (𝓡∂ 1))
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞
      (fun p : Horizontal m × EuclideanHalfSpace 1 =>
        (horosphericalLogDiffeomorph m).symm (p.1, (1 / 2) * p.2.val 0 + b)) := by
  apply (horosphericalLogDiffeomorph m).symm.contMDiff.comp
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact contMDiff_fst.prodMk
    ((contMDiff_const.mul
      (Topology.Manifold.contMDiff_halfSpaceOneCoordinate.comp contMDiff_snd)).add
      contMDiff_const)

private theorem riemannianMetric_inner_horospherical_halfSpace
    (m : ℕ) (b : ℝ) (p : Horizontal m × EuclideanHalfSpace 1)
    (v w : TangentSpace ((𝓘(ℝ, Horizontal m)).prod (𝓡∂ 1)) p) :
    let F : Horizontal m × EuclideanHalfSpace 1 →
      Hyperboloid (EuclideanSpace ℝ (Fin (m + 1))) := fun x =>
        (horosphericalLogDiffeomorph m).symm (x.1, (1 / 2) * x.2.val 0 + b)
    4 * riemannianMetric.inner (F p)
      (mfderiv ((𝓘(ℝ, Horizontal m)).prod (𝓡∂ 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) F p v)
      (mfderiv ((𝓘(ℝ, Horizontal m)).prod (𝓡∂ 1))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) F p w) =
      v.2 0 * w.2 0 + Real.exp (-p.2.val 0) *
        ((4 * Real.exp (-2 * b)) * inner ℝ v.1 w.1) := by
  let A : Horizontal m × ℝ → Hyperboloid (EuclideanSpace ℝ (Fin (m + 1))) :=
    fun x => (horosphericalLogDiffeomorph m).symm (x.1, (1 / 2) * x.2 + b)
  let B : Horizontal m × EuclideanHalfSpace 1 → Horizontal m × ℝ :=
    fun x => (x.1, x.2.val 0)
  have hA : ContMDiff 𝓘(ℝ, Horizontal m × ℝ)
      𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ A :=
    (horosphericalLogDiffeomorph m).symm.contMDiff.comp
      (contDiff_fst.prodMk ((contDiff_const.mul contDiff_snd).add contDiff_const)).contMDiff
  have hB : ContMDiff ((𝓘(ℝ, Horizontal m)).prod (𝓡∂ 1))
      𝓘(ℝ, Horizontal m × ℝ) ∞ B := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiff_id.prodMap Topology.Manifold.contMDiff_halfSpaceOneCoordinate
  have hd (u : TangentSpace ((𝓘(ℝ, Horizontal m)).prod (𝓡∂ 1)) p) :
      mfderiv ((𝓘(ℝ, Horizontal m)).prod (𝓡∂ 1))
        𝓘(ℝ, Horizontal m × ℝ) B p u =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (B p)).symm (u.1, u.2 0) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    change mfderiv ((𝓘(ℝ, Horizontal m)).prod (𝓡∂ 1))
      ((𝓘(ℝ, Horizontal m)).prod 𝓘(ℝ, ℝ))
      (Prod.map id (fun r : EuclideanHalfSpace 1 => r.val 0)) p u = _
    rw [mfderiv_prodMap mdifferentiableAt_id
      (Topology.Manifold.hasMFDerivAt_halfSpaceOneCoordinate p.2).mdifferentiableAt,
      mfderiv_id, (Topology.Manifold.hasMFDerivAt_halfSpaceOneCoordinate p.2).mfderiv]
    rfl
  change 4 * riemannianMetric.inner (A (B p))
    (mfderiv _ _ (A ∘ B) p v) (mfderiv _ _ (A ∘ B) p w) = _
  rw [mfderiv_comp_apply p (hA.mdifferentiableAt (by simp))
      (hB.mdifferentiableAt (by simp)),
    mfderiv_comp_apply p (hA.mdifferentiableAt (by simp))
      (hB.mdifferentiableAt (by simp)), hd, hd]
  rw [riemannianMetric_inner_horosphericalLogDiffeomorph_symm_affine]
  change 4 * (Real.exp (-2 * ((1 / 2) * p.2.val 0 + b)) * inner ℝ v.1 w.1 +
    (1 / 2) ^ 2 * v.2 0 * w.2 0) = _
  rw [show -2 * ((1 / 2) * p.2.val 0 + b) = -p.2.val 0 + -2 * b by ring,
    Real.exp_add]
  ring

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

private theorem metric_inner_horospherical_halfSpace
    (m : ℕ) (g : SmoothRiemannianMetric I N)
    (G : Hyperboloid (EuclideanSpace ℝ (Fin (m + 1))) → N)
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I ∞ G)
    (hmetric : ∀ (x : Hyperboloid (EuclideanSpace ℝ (Fin (m + 1))))
      (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) x),
      g.inner (G x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I G x v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I G x w) =
      4 * riemannianMetric.inner x v w)
    (b : ℝ) (p : Horizontal m × EuclideanHalfSpace 1)
    (v w : TangentSpace ((𝓘(ℝ, Horizontal m)).prod (𝓡∂ 1)) p) :
    let F : Horizontal m × EuclideanHalfSpace 1 → N := fun x =>
      G ((horosphericalLogDiffeomorph m).symm (x.1, (1 / 2) * x.2.val 0 + b))
    g.inner (F p)
      (mfderiv ((𝓘(ℝ, Horizontal m)).prod (𝓡∂ 1)) I F p v)
      (mfderiv ((𝓘(ℝ, Horizontal m)).prod (𝓡∂ 1)) I F p w) =
      v.2 0 * w.2 0 + Real.exp (-p.2.val 0) *
        ((4 * Real.exp (-2 * b)) * inner ℝ v.1 w.1) := by
  let A : Horizontal m × EuclideanHalfSpace 1 →
      Hyperboloid (EuclideanSpace ℝ (Fin (m + 1))) := fun x =>
    (horosphericalLogDiffeomorph m).symm (x.1, (1 / 2) * x.2.val 0 + b)
  change g.inner (G (A p))
    (mfderiv _ _ (G ∘ A) p v) (mfderiv _ _ (G ∘ A) p w) = _
  have hA := contMDiff_horospherical_halfSpace m b
  rw [mfderiv_comp_apply p (hG.mdifferentiableAt (by simp))
      (hA.mdifferentiableAt (by simp)),
    mfderiv_comp_apply p (hG.mdifferentiableAt (by simp))
      (hA.mdifferentiableAt (by simp)), hmetric]
  exact riemannianMetric_inner_horospherical_halfSpace m b p v w

end DifferentialGeometry.Hyperboloid

namespace DifferentialGeometry

open Geometry.Curvature

variable {E F K M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace K] {I : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace K M] [IsManifold I ∞ M] [T2Space M]

private theorem exists_flat_metric_of_exponential_euclidean_cover
    (g : SmoothRiemannianMetric (I.prod (𝓡∂ 1)) (M × EuclideanHalfSpace 1))
    (f : E → M) (hf : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ f)
    (hsurj : Function.Surjective f) (c : ℝ) (hc : 0 < c)
    (hmetric : ∀ (x : E) (r : EuclideanHalfSpace 1)
      (v w : E) (a b : EuclideanSpace ℝ (Fin 1)),
      g.inner (f x, r)
        (mfderiv 𝓘(ℝ, E) I f x ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm v), a)
        (mfderiv 𝓘(ℝ, E) I f x ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm w), b) =
      a 0 * b 0 + Real.exp (-r.val 0) * (c * inner ℝ v w)) :
    ∃ q : SmoothRiemannianMetric I M,
      (∀ (x : M) (v w : TangentSpace I x),
        q.inner x v w = g.inner (x, (⟨0, by simp⟩ : EuclideanHalfSpace 1)) (v, 0) (w, 0)) ∧
      (∀ (x : M) (v w z u : TangentSpace I x),
        metricRm04StandardAt q x v w z u = 0) ∧
      g = q.exponentialWarpedEnd (1 / 2) := by
  let _ : T2Space (EuclideanHalfSpace 1) := by
    unfold EuclideanHalfSpace
    infer_instance
  let q := g.sliceFst (⟨0, by simp⟩ : EuclideanHalfSpace 1)
  have hq : ∀ (x v w : E),
      q.inner (f x)
        (mfderiv 𝓘(ℝ, E) I f x ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm v))
        (mfderiv 𝓘(ℝ, E) I f x ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm w)) =
      c * inner ℝ v w := by
    intro x v w
    rw [SmoothRiemannianMetric.sliceFst_inner, hmetric]
    simp only [PiLp.zero_apply,
      neg_zero, Real.exp_zero, mul_zero, zero_add, one_mul]
  refine ⟨q, ?_, ?_, ?_⟩
  · exact fun x v w => SmoothRiemannianMetric.sliceFst_inner g (⟨0, by simp⟩ : EuclideanHalfSpace 1) x v w
  · exact Geometry.Curvature.metricRm04StandardAt_eq_zero_of_euclidean_cover
      q f hf hsurj c hc hq
  · apply SmoothRiemannianMetric.ext_inner
    rintro ⟨y, r⟩ v w
    obtain ⟨x, rfl⟩ := hsurj y
    let D := hf.mfderivToContinuousLinearEquiv (by simp) x
    have hD (V : TangentSpace I (f x)) : mfderiv 𝓘(ℝ, E) I f x (D.symm V) = V := by
      rw [← hf.mfderivToContinuousLinearEquiv_coe (by simp)]
      exact D.apply_symm_apply V
    have hm := hmetric x r ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) (D.symm v.1))
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) (D.symm w.1)) v.2 w.2
    have hq' := hq x ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) (D.symm v.1))
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x) (D.symm w.1))
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hm hq'
    erw [hD, hD] at hm hq'
    erw [hm, SmoothRiemannianMetric.exponentialWarpedEnd_inner, hq']
    congr 2
    congr 1
    ring

end DifferentialGeometry

namespace DifferentialGeometry.Geometry.Hyperbolic

open GC.Endpoint Horospherical

variable {E K N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace K]
  {I : ModelWithCorners ℝ E K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold I ∞ N]

private theorem exists_hyperbolicCusp_of_horospherical_cover
    (g : SmoothRiemannianMetric I N) (f : CuspHalfSpace → N)
    (hf : Manifold.IsImmersion halfCollarModel I ∞ f)
    (c : Horizontal 2 → Torus)
    (hc : IsLocalDiffeomorph 𝓘(ℝ, Horizontal 2) torusModel ∞ c)
    (hsurj : Function.Surjective c)
    (G : Hyperboloid (EuclideanSpace ℝ (Fin 3)) → N)
    (hG : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) I ∞ G)
    (hmetric : ∀ (x : Hyperboloid (EuclideanSpace ℝ (Fin 3)))
      (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x),
      g.inner (G x)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) I G x v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) I G x w) =
      4 * Hyperboloid.riemannianMetric.inner x v w)
    (b : ℝ)
    (hmap : ∀ (x : Horizontal 2) (r : EuclideanHalfSpace 1),
      f (c x, r) = G ((Hyperboloid.horosphericalLogDiffeomorph 2).symm
        (x, (1 / 2) * r.val 0 + b))) :
    ∃ C : HyperbolicCusp,
      (∀ (x : Torus) (v w : TangentSpace torusModel x),
        C.torusMetric.inner x v w = g.inner (f (x, halfZero))
          (mfderiv halfCollarModel I f (x, halfZero) (v, 0))
          (mfderiv halfCollarModel I f (x, halfZero) (w, 0))) ∧
      (∀ (p : CuspHalfSpace) (v w : TangentSpace halfCollarModel p),
        g.inner (f p) (mfderiv halfCollarModel I f p v)
          (mfderiv halfCollarModel I f p w) = C.metric.inner p v w) := by
  let _ : T2Space (EuclideanHalfSpace 1) := by
    unfold EuclideanHalfSpace
    infer_instance
  let gp := g.pullbackOfImmersion f hf.contMDiff
    (fun p => (hf.isImmersionAt p).mfderiv_injective (by simp))
  let q : Horizontal 2 × EuclideanHalfSpace 1 → CuspHalfSpace := Prod.map c id
  have hq : ContMDiff ((𝓘(ℝ, Horizontal 2)).prod (𝓡∂ 1)) halfCollarModel ∞ q :=
    hc.contMDiff.prodMap contMDiff_id
  have hd (p : Horizontal 2 × EuclideanHalfSpace 1)
      (v : TangentSpace ((𝓘(ℝ, Horizontal 2)).prod (𝓡∂ 1)) p) :
      mfderiv ((𝓘(ℝ, Horizontal 2)).prod (𝓡∂ 1)) halfCollarModel q p v =
        (mfderiv 𝓘(ℝ, Horizontal 2) torusModel c p.1 v.1, v.2) := by
    rw [mfderiv_prodMap (hc.contMDiff.mdifferentiableAt (by simp))
      mdifferentiableAt_id, mfderiv_id]
    rfl
  have hmap' : f ∘ q = fun p : Horizontal 2 × EuclideanHalfSpace 1 =>
      G ((Hyperboloid.horosphericalLogDiffeomorph 2).symm
        (p.1, (1 / 2) * p.2.val 0 + b)) := by
    funext p
    exact hmap p.1 p.2
  have hcover : ∀ (x : Horizontal 2) (r : EuclideanHalfSpace 1)
      (v w : Horizontal 2) (a d : EuclideanSpace ℝ (Fin 1)),
      gp.inner (c x, r)
        (mfderiv 𝓘(ℝ, Horizontal 2) torusModel c x
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm v), a)
        (mfderiv 𝓘(ℝ, Horizontal 2) torusModel c x
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) x).symm w), d) =
      a 0 * d 0 + Real.exp (-r.val 0) *
        ((4 * Real.exp (-2 * b)) * inner ℝ v w) := by
    intro x r v w a d
    have h := Hyperboloid.metric_inner_horospherical_halfSpace 2 g G hG hmetric b
      (x, r) (v, a) (w, d)
    change g.inner ((fun p : Horizontal 2 × EuclideanHalfSpace 1 =>
      G ((Hyperboloid.horosphericalLogDiffeomorph 2).symm
        (p.1, (1 / 2) * p.2.val 0 + b))) (x, r)) _ _ = _ at h
    rw [← hmap'] at h
    erw [mfderiv_comp_apply (x, r) (hf.contMDiff.mdifferentiableAt (by simp))
        (hq.mdifferentiableAt (by simp)),
      mfderiv_comp_apply (x, r) (hf.contMDiff.mdifferentiableAt (by simp))
        (hq.mdifferentiableAt (by simp)), hd, hd] at h
    exact h
  obtain ⟨g₀, hg₀, hflat, hgp⟩ := exists_flat_metric_of_exponential_euclidean_cover
    gp c hc hsurj (4 * Real.exp (-2 * b)) (by positivity) hcover
  let C := HyperbolicCusp.ofFlatMetric g₀ (fun p v w => hflat p v w w v)
  refine ⟨C, ?_, ?_⟩
  · intro x v w
    exact hg₀ x v w
  · intro p v w
    change gp.inner p v w = (g₀.exponentialWarpedEnd (1 / 2)).inner p v w
    rw [hgp]

end DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.Hyperboloid

variable {E K N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace K] {I : ModelWithCorners ℝ E K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold I ∞ N]

private theorem metric_inner_comp_hUpperDiffeomorph_symm
    (m : ℕ) (g : SmoothRiemannianMetric I N)
    (F : Hyperbolic.HUpper (m + 1) → N)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I ∞ F)
    (hmetric : ∀ (p : Hyperbolic.HUpper (m + 1))
      (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) p),
      g.inner (F p)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I F p v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I F p w) =
      4 * riemannianMetric.inner ((hUpperDiffeomorph (m + 1)) p)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (hUpperDiffeomorph (m + 1)) p v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (hUpperDiffeomorph (m + 1)) p w))
    (x : Hyperboloid (EuclideanSpace ℝ (Fin (m + 1))))
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) x) :
    g.inner ((F ∘ (hUpperDiffeomorph (m + 1)).symm) x)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I
        (F ∘ (hUpperDiffeomorph (m + 1)).symm) x v)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I
        (F ∘ (hUpperDiffeomorph (m + 1)).symm) x w) =
      4 * riemannianMetric.inner x v w := by
  let J := hUpperDiffeomorph (m + 1)
  have hJ : (J : Hyperbolic.HUpper (m + 1) →
      Hyperboloid (EuclideanSpace ℝ (Fin (m + 1)))) ∘ J.symm = id := by
    funext y
    exact J.apply_symm_apply y
  change g.inner ((F ∘ J.symm) x) (mfderiv _ _ (F ∘ J.symm) x v)
    (mfderiv _ _ (F ∘ J.symm) x w) = _
  rw [mfderiv_comp_apply x (hF.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_comp_apply x (hF.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp))]
  change g.inner (F (J.symm x)) _ _ = _
  rw [hmetric]
  have he : 4 * riemannianMetric.inner ((J ∘ J.symm) x)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (J ∘ J.symm) x v)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
        𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (J ∘ J.symm) x w) =
      4 * riemannianMetric.inner x v w := by
    rw [hJ, mfderiv_id]
    rfl
  rw [mfderiv_comp_apply x (J.contMDiff.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_comp_apply x (J.contMDiff.mdifferentiableAt (by simp))
      (J.symm.contMDiff.mdifferentiableAt (by simp))] at he
  exact he

private theorem metric_inner_projective_normalization
    (m : ℕ) (g : SmoothRiemannianMetric I N)
    (F : Hyperbolic.HUpper (m + 1) → N)
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I ∞ F)
    (hmetric : ∀ (p : Hyperbolic.HUpper (m + 1))
      (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) p),
      g.inner (F p)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I F p v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I F p w) =
      4 * riemannianMetric.inner ((hUpperDiffeomorph (m + 1)) p)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (hUpperDiffeomorph (m + 1)) p v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) (hUpperDiffeomorph (m + 1)) p w))
    (a : ProjectiveOrthogonalGroup.PO (m + 1) 1)
    (x : Hyperboloid (EuclideanSpace ℝ (Fin (m + 1))))
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) x) :
    let G := F ∘ (hUpperDiffeomorph (m + 1)).symm ∘
      (projectiveOrthogonalGroupEquiv m).symm a
    g.inner (G x)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I G x v)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) I G x w) =
      4 * riemannianMetric.inner x v w := by
  let K := F ∘ (hUpperDiffeomorph (m + 1)).symm
  let A := (projectiveOrthogonalGroupEquiv m).symm a
  have hK := hF.comp (hUpperDiffeomorph (m + 1)).symm.contMDiff
  have hA := contMDiff_isometryEquiv (n := ∞) A
  change g.inner (K (A x)) (mfderiv _ _ (K ∘ A) x v)
    (mfderiv _ _ (K ∘ A) x w) = _
  rw [mfderiv_comp_apply x (hK.mdifferentiableAt (by simp))
      (hA.mdifferentiableAt (by simp)),
    mfderiv_comp_apply x (hK.mdifferentiableAt (by simp))
      (hA.mdifferentiableAt (by simp))]
  rw [metric_inner_comp_hUpperDiffeomorph_symm m g F hF hmetric,
    riemannianMetric_inner_mfderiv_isometryEquiv]

end DifferentialGeometry.Hyperboloid

namespace DifferentialGeometry.Geometry.Hyperbolic

open GC.Endpoint Horospherical

variable {E K N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace K]
  {I : ModelWithCorners ℝ E K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold I ∞ N]

private theorem exists_hyperbolicCusp_of_upper_halfSpace_cover
    (g : SmoothRiemannianMetric I N) (f : CuspHalfSpace → N)
    (hf : Manifold.IsImmersion halfCollarModel I ∞ f)
    (c : Horizontal 2 → Torus)
    (hc : IsLocalDiffeomorph 𝓘(ℝ, Horizontal 2) torusModel ∞ c)
    (hsurj : Function.Surjective c)
    (F : DifferentialGeometry.Hyperbolic.HUpper 3 → N)
    (hF : ContMDiff (𝓡 3) I ∞ F)
    (hmetric : ∀ (p : DifferentialGeometry.Hyperbolic.HUpper 3)
      (v w : TangentSpace (𝓡 3) p),
      g.inner (F p) (mfderiv (𝓡 3) I F p v) (mfderiv (𝓡 3) I F p w) =
      4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w))
    (a : ProjectiveOrthogonalGroup.PO 3 1) (b : ℝ)
    (hmap : ∀ (x : Horizontal 2) (r : EuclideanHalfSpace 1),
      f (c x, r) = F ((HyperbolicAction.poMulAction (Nat.le_add_left 1 2)).smul a⁻¹
        (ofCoords x (Real.exp ((1 / 2) * r.val 0 + b)) (Real.exp_pos _)))) :
    ∃ C : HyperbolicCusp,
      (∀ (x : Torus) (v w : TangentSpace torusModel x),
        C.torusMetric.inner x v w = g.inner (f (x, halfZero))
          (mfderiv halfCollarModel I f (x, halfZero) (v, 0))
          (mfderiv halfCollarModel I f (x, halfZero) (w, 0))) ∧
      (∀ (p : CuspHalfSpace) (v w : TangentSpace halfCollarModel p),
        g.inner (f p) (mfderiv halfCollarModel I f p v)
          (mfderiv halfCollarModel I f p w) = C.metric.inner p v w) := by
  let A := (Hyperboloid.projectiveOrthogonalGroupEquiv 2).symm a⁻¹
  let G := F ∘ (Hyperboloid.hUpperDiffeomorph 3).symm ∘ A
  have hG : ContMDiff (𝓡 3) I ∞ G :=
    hF.comp ((Hyperboloid.hUpperDiffeomorph 3).symm.contMDiff.comp
      (Hyperboloid.contMDiff_isometryEquiv (n := ∞) A))
  have hGmetric (x : Hyperboloid (EuclideanSpace ℝ (Fin 3)))
      (v w : TangentSpace (𝓡 3) x) :
      g.inner (G x) (mfderiv (𝓡 3) I G x v) (mfderiv (𝓡 3) I G x w) =
        4 * Hyperboloid.riemannianMetric.inner x v w :=
    Hyperboloid.metric_inner_projective_normalization 2 g F hF hmetric a⁻¹ x v w
  apply exists_hyperbolicCusp_of_horospherical_cover g f hf c hc hsurj G hG hGmetric b
  intro x r
  rw [hmap]
  change F _ = F ((Hyperboloid.hUpperDiffeomorph 3).symm
    (A ((Hyperboloid.horosphericalLogDiffeomorph 2).symm
      (x, (1 / 2) * r.val 0 + b))))
  rw [Hyperboloid.horosphericalLogDiffeomorph_symm_apply,
    Hyperboloid.hUpperDiffeomorph_apply,
    Hyperboloid.projectiveOrthogonalGroupEquiv_symm_apply,
    Hyperboloid.hUpperDiffeomorph_symm_apply,
    (Hyperboloid.hUpperIsometryEquiv 3).symm_apply_apply]

end DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.CuspTruncation.FiniteCuspTruncation

open ProjectiveOrthogonalGroup (PO)
open Hyperbolic (HUpper)
open CuspCrossSections (endStabilizer)
open Horospherical (Horizontal)
open HorosphereProjection (quotientHorosphereCoordinates)
open Geometry.Hyperbolic
open GC.Endpoint

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) :
    MulAction Δ (HUpper (m + 1)) :=
  EquivariantMap.subAction (Nat.le_add_left 1 m) Δ

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) :
    ContinuousConstSMul Δ (HUpper (m + 1)) :=
  ⟨fun γ => (HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)).continuous⟩

private local instance {m : ℕ} (Δ : Subgroup (PO (m + 1) 1)) :
    ContMDiffConstSMul 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1))) ∞ Δ (HUpper (m + 1)) :=
  ⟨fun γ => HyperbolicAction.contMDiff_po_smul m ∞ (γ : PO (m + 1) 1)⟩

variable {Γ : Subgroup (PO (2 + 1) 1)} [DiscreteTopology Γ]
  [IsCancelSMul Γ (HUpper (2 + 1))] {r : ℝ}
  (D : FiniteCuspTruncation (Nat.le_add_left 1 2) Γ r) (ξ : D.centers)

local notation "hΓ" => (isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology Γ))
local notation "P" => endStabilizer (Nat.le_add_left 1 2) Γ (Set.singleton ξ.val)
local notation "QΓ" => MulAction.orbitRel.Quotient Γ (HUpper (2 + 1))
local notation "πΓ" => Quotient.mk (MulAction.orbitRel Γ (HUpper (2 + 1)))
local notation "πP" => Quotient.mk (MulAction.orbitRel P (HUpper (2 + 1)))
local notation "S" => (πP '' Busemann.horosphere ξ.val (D.level ξ))

private local instance : IsCancelSMul P (HUpper (2 + 1)) :=
  EquivariantMap.isCancelSMul_subAction (Nat.le_add_left 1 2) (show P ≤ Γ from inf_le_left)

private local instance : ProperlyDiscontinuousSMul P (HUpper (2 + 1)) :=
  OrbifoldCompactness.properlyDiscontinuous_subAction (Nat.le_add_left 1 2) P
    ((hΓ).mono inf_le_left)

private local instance : ChartedSpace (Fin 2 → ℝ) S :=
  D.horosphereQuotientChartedSpace hΓ ξ

theorem exists_hyperbolicCusp_horoballCylinderMap_at_depth
    (H : FiniteVolumeHyperbolicModel) (e : QΓ ≃ₜ H.Carrier)
    (he : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (e ∘ πΓ))
    (hmetric : ∀ (p : HUpper 3) (v w : TangentSpace (𝓡 3) p),
      H.metric.inner ((e ∘ πΓ) p)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ πΓ) p v)
        (mfderiv (𝓡 3) (𝓡 3) (e ∘ πΓ) p w) =
      4 * Hyperboloid.riemannianMetric.inner ((Hyperboloid.hUpperDiffeomorph 3) p)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p v)
        (mfderiv (𝓡 3) (𝓡 3) (Hyperboloid.hUpperDiffeomorph 3) p w))
    (F : Diffeomorph torusModel 𝓘(ℝ, Fin 2 → ℝ) Torus S ∞)
    (a : PO 3 1)
    (ha : (HyperbolicBoundary.poBoundaryMulAction (Nat.le_add_left 1 2)).smul a ξ.val =
      MobiusBoundary.ptInfty)
    (R : ℝ) (hR : 0 < R) :
    let f : CuspHalfSpace → H.Carrier := fun p =>
      e (D.horoballCylinderMap hΓ ξ
        (F p.1, ⟨R + p.2.val 0 / 2, add_nonneg hR.le (div_nonneg p.2.property (by norm_num))⟩))
    ∃ C : HyperbolicCusp,
      (∀ (x : Torus) (v w : TangentSpace torusModel x),
        C.torusMetric.inner x v w = H.metric.inner (f (x, halfZero))
          (mfderiv halfCollarModel (𝓡 3) f (x, halfZero) (v, 0))
          (mfderiv halfCollarModel (𝓡 3) f (x, halfZero) (w, 0))) ∧
      (∀ (p : CuspHalfSpace) (v w : TangentSpace halfCollarModel p),
        H.metric.inner (f p) (mfderiv halfCollarModel (𝓡 3) f p v)
          (mfderiv halfCollarModel (𝓡 3) f p w) = C.metric.inner p v w) := by
  dsimp only
  have hf := (D.isSmoothEmbedding_horoballCylinderMap_at_depth ξ e he F R hR).isImmersion
  let q := quotientHorosphereCoordinates P ξ.val (D.level ξ) a ha
  have hq : IsLocalDiffeomorph 𝓘(ℝ, Horizontal 2) 𝓘(ℝ, Fin 2 → ℝ) ∞ q :=
    HorosphereProjection.isLocalDiffeomorph_quotientHorosphereCoordinates
      P ξ.val (CuspCrossSections.horospherical_endStabilizer
        (Nat.le_add_left 1 2) Γ hΓ (D.region_nonempty ξ)) (D.level ξ) a ha
  let c : Horizontal 2 → Torus := F.symm ∘ q
  have hc : IsLocalDiffeomorph 𝓘(ℝ, Horizontal 2) torusModel ∞ c :=
    isLocalDiffeomorph_comp F.symm.isLocalDiffeomorph hq
  have hs : Function.Surjective c :=
    F.symm.surjective.comp
      (HorosphereProjection.quotientHorosphereCoordinates_surjective P ξ.val (D.level ξ) a ha)
  apply exists_hyperbolicCusp_of_upper_halfSpace_cover H.metric _ hf c hc hs
    (e ∘ πΓ) he.contMDiff hmetric a
    (Real.log (BusemannCocycle.poConfFactor (Nat.le_add_left 1 2) a ξ.val) - D.level ξ + R)
  intro x s
  change e (D.horoballCylinderMap hΓ ξ (F (F.symm (q x)), _)) = _
  rw [F.apply_symm_apply, D.horoballCylinderMap_quotientHorosphereCoordinates hΓ ξ a ha]
  apply congrArg e
  apply congrArg πΓ
  apply congrArg ((HyperbolicAction.poMulAction (Nat.le_add_left 1 2)).smul a⁻¹)
  congr 1
  congr 1
  ring

end DifferentialGeometry.CuspTruncation.FiniteCuspTruncation
