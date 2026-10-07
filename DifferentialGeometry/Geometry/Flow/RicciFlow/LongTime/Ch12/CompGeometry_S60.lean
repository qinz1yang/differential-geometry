import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompAbstract_S60
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrBridge_S57
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.FixedDomain

set_option autoImplicit false

/-!
# CH12-S60 / G2: geometric bridge for `hcomp` on `↥U`, `U = ball R`

For a global diffeomorphism `e` of `H.Carrier`, an open `U`, and `f` smooth and an immersion on the
open set `e '' U`:

* `ckErr_S45 H g' c (f ∘ e) q x` is the `metricDerivNorm q` of the pull-back (under `e`, fixed
  domain `U`) of the metric `(f|_W)^*(c g')` of `W = e '' U`, against the reference `h|_U`;
* the pulled-back reference is `e^*h|_U`, whose `metricDerivNorm` against `h|_U` is
  `ckErr_S45 H H.metric 1 e`;
* naturality (`metricDerivNorm_fixedDomainPullback`) turns the hypothesis on `f` into the
  `e^*h`-reference hypothesis of the abstract chain `ckComp_abstract_S60`.
-/

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

section Geom

variable (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]

/-- the image of an open set under a global diffeomorphism, as an `Opens`. -/
def diffImage_S60 (e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier) (U : Opens H.Carrier) :
    Opens H.Carrier :=
  ⟨e '' (U : Set H.Carrier), e.toHomeomorph.isOpenMap U U.isOpen⟩

theorem subset_diffImage_S60 (e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier) (U : Opens H.Carrier) :
    e '' (U : Set H.Carrier) ⊆ (diffImage_S60 H e U : Set H.Carrier) := fun _ hy => hy

omit [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] in
theorem mfderiv_inj_S60 (e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier) (x : H.Carrier) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x) := by
  intro v w hvw
  have h := congrArg
    (mfderiv (𝓡 3) (𝓡 3) (e.symm : H.Carrier → H.Carrier) (e x)) hvw
  rwa [Diffeomorph.mfderiv_symm_self, Diffeomorph.mfderiv_symm_self] at h

omit [IsManifold (𝓡 3) ∞ N] in
theorem contMDiffOn_comp_diff_S60 (e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier) (U : Opens H.Carrier)
    (f : H.Carrier → N) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (e '' (U : Set H.Carrier))) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (f ∘ e) U :=
  hf.comp e.contMDiff.contMDiffOn (fun x hx => ⟨x, hx, rfl⟩)

omit [IsManifold (𝓡 3) ∞ N] in
theorem mfderiv_comp_diff_S60 (e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier) (U : Opens H.Carrier)
    (f : H.Carrier → N) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (e '' (U : Set H.Carrier)))
    (x : U) (v : TangentSpace (𝓡 3) (x : H.Carrier)) :
    mfderiv (𝓡 3) (𝓡 3) (f ∘ e) (x : H.Carrier) v =
      mfderiv (𝓡 3) (𝓡 3) f (e x) (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x v) := by
  have hf' : MDifferentiableAt (𝓡 3) (𝓡 3) f (e x) :=
    (hf.contMDiffAt ((diffImage_S60 H e U).isOpen.mem_nhds ⟨x, x.2, rfl⟩)).mdifferentiableAt
      infty_ne_zero_C4
  have he' : MDifferentiableAt (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x :=
    e.contMDiff.mdifferentiableAt infty_ne_zero_C4
  exact mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) (x : H.Carrier) hf' he' (v := v)

omit [IsManifold (𝓡 3) ∞ N] in
theorem mfderiv_inj_comp_diff_S60 (e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier) (U : Opens H.Carrier)
    (f : H.Carrier → N) (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (e '' (U : Set H.Carrier)))
    (hinj : ∀ y ∈ e '' (U : Set H.Carrier), Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)) :
    ∀ y ∈ (U : Set H.Carrier), Function.Injective (mfderiv (𝓡 3) (𝓡 3) (f ∘ e) y) := by
  intro y hy v w hvw
  have h1 := mfderiv_comp_diff_S60 H e U f hf ⟨y, hy⟩ v
  have h2 := mfderiv_comp_diff_S60 H e U f hf ⟨y, hy⟩ w
  exact mfderiv_inj_S60 H e y (hinj (e y) ⟨y, hy, rfl⟩ (h1.symm.trans (hvw.trans h2)))

/-- **(E2)** the pulled-back reference. -/
theorem pullbackRestrict_self_eq_fixed_S60 (e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier)
    (U : Opens H.Carrier) (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e : H.Carrier → H.Carrier) U)
    (hinj : ∀ y ∈ (U : Set H.Carrier),
      Function.Injective (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) y)) :
    pullbackRestrict_S57 H (scaleMetric (I := 𝓡 3) 1 one_pos H.metric) (e : H.Carrier → H.Carrier)
        U he hinj =
      fixedDomainPullbackMetric e U (diffImage_S60 H e U) (subset_diffImage_S60 H e U)
        (H.metric.restrictOpen (diffImage_S60 H e U)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [fixedDomainPullbackMetric_inner]
  simp only [pullbackRestrict_S57, SmoothRiemannianMetric.pullbackOfImmersion_inner,
    scaleMetric_inner, one_mul, mfderiv_comp_val_C4 (e : H.Carrier → H.Carrier) U he x]
  rfl

/-- **(E1)** the pulled-back target metric. -/
theorem pullbackRestrict_comp_eq_fixed_S60 (g : SmoothRiemannianMetric (𝓡 3) N)
    (f : H.Carrier → N) (e : H.Carrier ≃ₘ⟮𝓡 3, 𝓡 3⟯ H.Carrier) (U : Opens H.Carrier)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (e '' (U : Set H.Carrier)))
    (hinj : ∀ y ∈ e '' (U : Set H.Carrier), Function.Injective (mfderiv (𝓡 3) (𝓡 3) f y)) :
    pullbackRestrict_S57 H g (f ∘ e) U (contMDiffOn_comp_diff_S60 H e U f hf)
        (mfderiv_inj_comp_diff_S60 H e U f hf hinj) =
      fixedDomainPullbackMetric e U (diffImage_S60 H e U) (subset_diffImage_S60 H e U)
        (pullbackRestrict_S57 H g f (diffImage_S60 H e U) hf hinj) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [fixedDomainPullbackMetric_inner]
  have hL := SmoothRiemannianMetric.pullbackOfImmersion_inner (I := 𝓡 3) g
    (fun z : U => (f ∘ e) z) (contMDiff_restrict_C4 (f ∘ e) U (contMDiffOn_comp_diff_S60 H e U f hf))
    (fun z => immersion_restrict_inj_S57 H (f ∘ e) U (contMDiffOn_comp_diff_S60 H e U f hf)
      (mfderiv_inj_comp_diff_S60 H e U f hf hinj) z) x v w
  have hR := SmoothRiemannianMetric.pullbackOfImmersion_inner (I := 𝓡 3) g
    (fun z : diffImage_S60 H e U => f z) (contMDiff_restrict_C4 f _ hf)
    (fun z => immersion_restrict_inj_S57 H f (diffImage_S60 H e U) hf hinj z)
    ⟨e x, x, x.2, rfl⟩ (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x v)
    (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x w)
  refine hL.trans (Eq.trans ?_ hR.symm)
  rw [mfderiv_comp_val_C4 (f ∘ e) U (contMDiffOn_comp_diff_S60 H e U f hf) x v,
    mfderiv_comp_val_C4 (f ∘ e) U (contMDiffOn_comp_diff_S60 H e U f hf) x w]
  have e1 := mfderiv_comp_val_C4 f (diffImage_S60 H e U) hf ⟨e x, x, x.2, rfl⟩
    (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x v)
  have e2 := mfderiv_comp_val_C4 f (diffImage_S60 H e U) hf ⟨e x, x, x.2, rfl⟩
    (mfderiv (𝓡 3) (𝓡 3) (e : H.Carrier → H.Carrier) x w)
  exact congrArg₂ (fun a b => g.inner (f (e x)) a b)
    ((mfderiv_comp_diff_S60 H e U f hf x v).trans e1.symm)
    ((mfderiv_comp_diff_S60 H e U f hf x w).trans e2.symm)

end Geom

end GC.LongTime.Ch12
