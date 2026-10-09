import DifferentialGeometry.Geometry.Metric.Cylinder
import DifferentialGeometry.Geometry.Metric.DerivativeENorm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Pullback
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false
noncomputable section
open Set TopologicalSpace Manifold DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.Metric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

def cylinderAxialDiffeomorph (a σ : ℝ) (hσ : σ ^ 2 = 1) :
    (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯ (M × ℝ) where
  toFun x := (x.1, a + σ * x.2)
  invFun x := (x.1, σ * (x.2 - a))
  left_inv x := by
    refine Prod.ext (by rfl) ?_
    change σ * (a + σ * x.2 - a) = x.2
    calc
      _ = σ ^ 2 * x.2 := by ring
      _ = x.2 := by rw [hσ, one_mul]
  right_inv x := by
    refine Prod.ext (by rfl) ?_
    change a + σ * (σ * (x.2 - a)) = x.2
    calc
      _ = a + σ ^ 2 * (x.2 - a) := by ring
      _ = x.2 := by rw [hσ]; ring
  contMDiff_toFun :=
    contMDiff_fst.prodMk (contMDiff_const.add (contMDiff_const.mul contMDiff_snd))
  contMDiff_invFun :=
    contMDiff_fst.prodMk (contMDiff_const.mul (contMDiff_snd.sub contMDiff_const))

@[simp] theorem cylinderAxialDiffeomorph_apply (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (x : M × ℝ) :
    cylinderAxialDiffeomorph (I := I) a σ hσ x = (x.1, a + σ * x.2) := rfl

@[simp] theorem cylinderAxialDiffeomorph_symm_apply (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (x : M × ℝ) :
    (cylinderAxialDiffeomorph (I := I) a σ hσ).symm x = (x.1, σ * (x.2 - a)) := rfl

theorem cylinderAxialDiffeomorph_mfderiv (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (x : M × ℝ) (v : TangentSpace (I.prod 𝓘(ℝ)) x) :
    mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
      (cylinderAxialDiffeomorph (I := I) a σ hσ) x v = (v.1, σ * v.2) := by
  change mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
    (Prod.map (id : M → M) (fun z : ℝ => a + σ * z)) x v = _
  have hd : HasDerivAt (fun z : ℝ => a + σ * z) σ x.2 := by
    simpa using ((hasDerivAt_id x.2).const_mul σ).const_add a
  rw [mfderiv_prodMap mdifferentiableAt_id hd.differentiableAt.mdifferentiableAt,
    mfderiv_id, mfderiv_eq_fderiv, hd.hasFDerivAt.fderiv]
  change (v.1, v.2 * σ) = (v.1, σ * v.2)
  rw [mul_comm v.2 σ]

def cylinderAxialImage (a σ : ℝ) (hσ : σ ^ 2 = 1) (U : Opens (M × ℝ)) :
    Opens (M × ℝ) :=
  ⟨cylinderAxialDiffeomorph (I := I) a σ hσ '' (U : Set (M × ℝ)),
    (cylinderAxialDiffeomorph (I := I) a σ hσ).toHomeomorph.isOpenMap _ U.isOpen⟩

@[simp] theorem mem_cylinderAxialImage (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : Opens (M × ℝ)) (x : M × ℝ) :
    x ∈ cylinderAxialImage (I := I) a σ hσ U ↔ (x.1, σ * (x.2 - a)) ∈ U := by
  change x ∈ cylinderAxialDiffeomorph (I := I) a σ hσ '' (U : Set (M × ℝ)) ↔ _
  rw [Diffeomorph.image_eq_preimage_symm]
  rfl

def cylinderAxialRestrict (a σ : ℝ) (hσ : σ ^ 2 = 1) (U : Opens (M × ℝ)) :
    U ≃ₘ⟮I.prod 𝓘(ℝ), I.prod 𝓘(ℝ)⟯ cylinderAxialImage (I := I) a σ hσ U :=
  PartialDiffeomorph.toOpensDiffeo
    (cylinderAxialDiffeomorph (I := I) a σ hσ).toPartialDiffeomorph
    (fun _ _ => mem_univ _)

@[simp] theorem cylinderAxialRestrict_apply (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : Opens (M × ℝ)) (x : U) :
    (cylinderAxialRestrict (I := I) a σ hσ U x : M × ℝ) = (x.val.1, a + σ * x.val.2) := rfl

@[simp] theorem cylinderAxialRestrict_symm_apply (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : Opens (M × ℝ)) (x : cylinderAxialImage (I := I) a σ hσ U) :
    ((cylinderAxialRestrict (I := I) a σ hσ U).symm x : M × ℝ) =
      (x.val.1, σ * (x.val.2 - a)) := rfl

theorem cylinderAxialRestrict_mfderiv (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : Opens (M × ℝ)) (x : U) (v : TangentSpace (I.prod 𝓘(ℝ)) x) :
    mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
      (cylinderAxialRestrict (I := I) a σ hσ U) x v = (v.1, σ * v.2) :=
  (PartialDiffeomorph.mfderiv_toOpensDiffeo
    (cylinderAxialDiffeomorph (I := I) a σ hσ).toPartialDiffeomorph
    (fun _ _ => mem_univ _) x v).trans
      (cylinderAxialDiffeomorph_mfderiv a σ hσ (x : M × ℝ) v)

variable [IsManifold I ∞ M] [FiniteDimensional ℝ E] [T2Space M]

theorem pullback_cylinderMetric_cylinderAxialDiffeomorph
    (g : SmoothRiemannianMetric I M) (a σ : ℝ) (hσ : σ ^ 2 = 1) :
    Diffeomorph.pullbackMetric (cylinderMetric g) (cylinderAxialDiffeomorph (I := I) a σ hσ) =
      cylinderMetric g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have heq : (σ * v.2) * (σ * w.2) = v.2 * w.2 := by
    calc
      _ = σ ^ 2 * (v.2 * w.2) := by ring
      _ = _ := by rw [hσ, one_mul]
  rw [Diffeomorph.pullbackMetric_inner]
  calc
    _ = g.inner (cylinderAxialDiffeomorph (I := I) a σ hσ x).1
        (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
          (cylinderAxialDiffeomorph (I := I) a σ hσ) x v).1
        (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
          (cylinderAxialDiffeomorph (I := I) a σ hσ) x w).1 +
        (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
          (cylinderAxialDiffeomorph (I := I) a σ hσ) x v).2 *
        (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
          (cylinderAxialDiffeomorph (I := I) a σ hσ) x w).2 :=
      cylinderMetric_inner g _ _ _
    _ = g.inner x.1 v.1 w.1 + (σ * v.2) * (σ * w.2) := by
      rw [cylinderAxialDiffeomorph_mfderiv, cylinderAxialDiffeomorph_mfderiv]
      rfl
    _ = g.inner x.1 v.1 w.1 + v.2 * w.2 := by rw [heq]
    _ = (cylinderMetric g).inner x v w := (cylinderMetric_inner g x v w).symm

theorem metricDerivNorm_pullback_cylinderAxialDiffeomorph
    (g : SmoothRiemannianMetric I M)
    (gk gInf : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (M × ℝ))
    (a σ : ℝ) (hσ : σ ^ 2 = 1) (j : ℕ) (x : M × ℝ) :
    metricDerivNorm j
      (Diffeomorph.pullbackMetric gk (cylinderAxialDiffeomorph (I := I) a σ hσ))
      (Diffeomorph.pullbackMetric gInf (cylinderAxialDiffeomorph (I := I) a σ hσ))
      (cylinderMetric g) x =
    metricDerivNorm j gk gInf (cylinderMetric g) (cylinderAxialDiffeomorph (I := I) a σ hσ x) := by
  simpa only [pullback_cylinderMetric_cylinderAxialDiffeomorph] using
    metricDerivNorm_pullback gk gInf (cylinderMetric g) (cylinderAxialDiffeomorph (I := I) a σ hσ) j x

theorem metricDerivENormSupOn_pullback_cylinderAxialDiffeomorph
    (g : SmoothRiemannianMetric I M)
    (gk gInf : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (M × ℝ))
    (a σ : ℝ) (hσ : σ ^ 2 = 1) (K : Set (M × ℝ)) (p : ℕ) :
    metricDerivENormSupOn K p
      (Diffeomorph.pullbackMetric gk (cylinderAxialDiffeomorph (I := I) a σ hσ))
      (Diffeomorph.pullbackMetric gInf (cylinderAxialDiffeomorph (I := I) a σ hσ))
      (cylinderMetric g) =
    metricDerivENormSupOn (cylinderAxialDiffeomorph (I := I) a σ hσ '' K) p
      gk gInf (cylinderMetric g) := by
  simp only [metricDerivENormSupOn, metricDerivNorm_pullback_cylinderAxialDiffeomorph, iSup_image]

theorem pullback_cylinderMetric_cylinderAxialRestrict
    (g : SmoothRiemannianMetric I M) (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : Opens (M × ℝ)) :
    Diffeomorph.pullbackMetric
      ((cylinderMetric g).restrictOpen (cylinderAxialImage (I := I) a σ hσ U))
      (cylinderAxialRestrict (I := I) a σ hσ U) = (cylinderMetric g).restrictOpen U := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hglobal := congrArg
    (fun k : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (M × ℝ) => k.inner (x : M × ℝ) v w)
    (pullback_cylinderMetric_cylinderAxialDiffeomorph g a σ hσ)
  have hambient := (Diffeomorph.pullbackMetric_inner (cylinderMetric g)
    (cylinderAxialDiffeomorph (I := I) a σ hσ) (x : M × ℝ) v w).symm.trans hglobal
  rw [Diffeomorph.pullbackMetric_inner]
  change (cylinderMetric g).inner (cylinderAxialDiffeomorph (I := I) a σ hσ (x : M × ℝ))
    (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (cylinderAxialRestrict (I := I) a σ hσ U) x v)
    (mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (cylinderAxialRestrict (I := I) a σ hσ U) x w) =
    (cylinderMetric g).inner (x : M × ℝ) v w
  have hdv : mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
      (cylinderAxialRestrict (I := I) a σ hσ U) x v =
      mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
        (cylinderAxialDiffeomorph (I := I) a σ hσ) (x : M × ℝ) v :=
    PartialDiffeomorph.mfderiv_toOpensDiffeo
      (cylinderAxialDiffeomorph (I := I) a σ hσ).toPartialDiffeomorph
      (fun _ _ => mem_univ _) x v
  have hdw : mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
      (cylinderAxialRestrict (I := I) a σ hσ U) x w =
      mfderiv (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ))
        (cylinderAxialDiffeomorph (I := I) a σ hσ) (x : M × ℝ) w :=
    PartialDiffeomorph.mfderiv_toOpensDiffeo
      (cylinderAxialDiffeomorph (I := I) a σ hσ).toPartialDiffeomorph
      (fun _ _ => mem_univ _) x w
  rw [hdv, hdw]
  exact hambient

theorem metricDerivNorm_pullback_cylinderAxialRestrict
    (g : SmoothRiemannianMetric I M) (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : Opens (M × ℝ))
    (gk gInf : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (cylinderAxialImage (I := I) a σ hσ U))
    (j : ℕ) (x : U) :
    metricDerivNorm j
      (Diffeomorph.pullbackMetric gk (cylinderAxialRestrict (I := I) a σ hσ U))
      (Diffeomorph.pullbackMetric gInf (cylinderAxialRestrict (I := I) a σ hσ U))
      ((cylinderMetric g).restrictOpen U) x =
    metricDerivNorm j gk gInf
      ((cylinderMetric g).restrictOpen (cylinderAxialImage (I := I) a σ hσ U))
      (cylinderAxialRestrict (I := I) a σ hσ U x) := by
  simpa only [pullback_cylinderMetric_cylinderAxialRestrict] using
    metricDerivNorm_pullback gk gInf
      ((cylinderMetric g).restrictOpen (cylinderAxialImage (I := I) a σ hσ U))
      (cylinderAxialRestrict (I := I) a σ hσ U) j x

theorem metricDerivENormSupOn_pullback_cylinderAxialRestrict
    (g : SmoothRiemannianMetric I M) (a σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : Opens (M × ℝ))
    (gk gInf : SmoothRiemannianMetric (I.prod 𝓘(ℝ)) (cylinderAxialImage (I := I) a σ hσ U))
    (K : Set U) (p : ℕ) :
    metricDerivENormSupOn K p
      (Diffeomorph.pullbackMetric gk (cylinderAxialRestrict (I := I) a σ hσ U))
      (Diffeomorph.pullbackMetric gInf (cylinderAxialRestrict (I := I) a σ hσ U))
      ((cylinderMetric g).restrictOpen U) =
    metricDerivENormSupOn (cylinderAxialRestrict (I := I) a σ hσ U '' K) p gk gInf
      ((cylinderMetric g).restrictOpen (cylinderAxialImage (I := I) a σ hσ U)) := by
  simp only [metricDerivENormSupOn, metricDerivNorm_pullback_cylinderAxialRestrict, iSup_image]

end DifferentialGeometry.Geometry.Metric
