import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryNaturalityRaw
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryPreimage
import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Topology.Manifold.ImmersionInterior
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Topology.Manifold.EuclideanHalfSpace.Instances

/-!
# CH12 C4 (G1): transfer of the `C^k` metric error along `cuspMap`

`interior_rawNorm_eq_C4`: at a point of positive height, the raw covariant-derivative error norm of
`(f ∘ cuspMap)^*g - H_cusp` in cusp coordinates equals that of `f^*g - H.metric` at the image point.
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace DifferentialGeometry DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Connection DifferentialGeometry.CheegerGromovCompactness
  DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Topology.Manifold GC.Endpoint
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

def cuspInterior_C4 : Opens CuspHalfSpace :=
  ⟨{p | 0 < p.2.val 0 ∧ p.2.val 0 < 100},
    (isOpen_lt continuous_const ((EuclideanSpace.proj 0).continuous.comp
      (continuous_subtype_val.comp continuous_snd))).inter
    (isOpen_lt ((EuclideanSpace.proj 0).continuous.comp
      (continuous_subtype_val.comp continuous_snd)) continuous_const)⟩

theorem cuspInterior_subset_C4 {p : CuspHalfSpace} (hp : p ∈ cuspInterior_C4) :
    p ∈ cuspDomain := hp.2

instance sigmaCompact_halfSpace_C4 : SigmaCompactSpace (EuclideanHalfSpace 1) :=
  _root_.EuclideanHalfSpace.sigmaCompactSpace 1

instance t2_halfSpace_C4 : T2Space (EuclideanHalfSpace 1) :=
  _root_.EuclideanHalfSpace.t2Space 1

instance sigmaCompact_cuspInterior_C4 : SigmaCompactSpace cuspInterior_C4 :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen halfCollarModel cuspInterior_C4.isOpen)

section Interior

variable {W : CompactCarrier.{u}} {H : FiniteVolumeHyperbolicModel.{u}}
  (T : HyperbolicTruncation H) (i : Fin T.count)

theorem cuspMap_immersion_C4 (x : CuspHalfSpace) :
    Function.Injective (mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) x) :=
  ((T.cuspEmbedding i).isImmersion.isImmersionAt x).mfderiv_injective (by simp)

theorem finrank_cusp_C4 : Module.finrank ℝ
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
  simp [Module.finrank_prod]

/-- The cusp map on the open interior collar. -/
def cuspInteriorMap_C4 : cuspInterior_C4 → H.Carrier := fun x => T.cuspMap i x

theorem contMDiff_cuspInteriorMap_C4 :
    ContMDiff halfCollarModel (𝓡 3) ∞ (cuspInteriorMap_C4 T i) :=
  (T.cuspEmbedding i).contMDiff.comp
    (contMDiff_subtype_val (I := halfCollarModel) (U := cuspInterior_C4))

theorem mfderiv_cuspInteriorMap_C4 (x : cuspInterior_C4) (v : TangentSpace halfCollarModel x) :
    mfderiv halfCollarModel (𝓡 3) (cuspInteriorMap_C4 T i) x v =
      mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) (x : CuspHalfSpace) v :=
  mfderiv_comp_val_C4 (T.cuspMap i) cuspInterior_C4 (T.cuspEmbedding i).contMDiff.contMDiffOn x v

theorem cuspInteriorMap_immersion_C4 (x : cuspInterior_C4) :
    Function.Injective (mfderiv halfCollarModel (𝓡 3) (cuspInteriorMap_C4 T i) x) := by
  intro v w h
  exact cuspMap_immersion_C4 T i x
    ((mfderiv_cuspInteriorMap_C4 T i x v).symm.trans (h.trans (mfderiv_cuspInteriorMap_C4 T i x w)))

theorem cuspInteriorMap_injective_C4 : Function.Injective (cuspInteriorMap_C4 T i) :=
  fun _ _ h => Subtype.ext ((T.cuspEmbedding i).isEmbedding.injective h)

theorem isLocalDiffeomorph_cuspInterior_C4 :
    IsLocalDiffeomorph halfCollarModel (𝓡 3) ∞ (cuspInteriorMap_C4 T i) := fun x =>
  isLocalDiffeomorphAt_of_isInteriorPoint_of_injective_mfderiv
    (contMDiff_cuspInteriorMap_C4 T i)
    ((halfCollarModel.isInteriorPoint_iff_isInteriorPoint_val).mpr (halfCollar_interior_C4 x.2.1))
    (finrank_cusp_C4) (cuspInteriorMap_immersion_C4 T i x)

/-- The cusp map restricted to the open interior collar is a diffeomorphism onto an open set. -/
def cuspInteriorDiffeo_C4 :
    cuspInterior_C4 ≃ₘ⟮halfCollarModel, 𝓡 3⟯ (isLocalDiffeomorph_cuspInterior_C4 T i).image :=
  diffeomorphOntoImage (cuspInteriorMap_C4 T i) (isLocalDiffeomorph_cuspInterior_C4 T i)
    (cuspInteriorMap_injective_C4 T i)

theorem mfderiv_cuspInteriorDiffeo_C4 (y : cuspInterior_C4) (v : TangentSpace halfCollarModel y) :
    (mfderiv halfCollarModel (𝓡 3) (cuspInteriorDiffeo_C4 T i) y v :
        TangentSpace (𝓡 3) ((cuspInteriorDiffeo_C4 T i y : H.Carrier))) =
      mfderiv halfCollarModel (𝓡 3) (T.cuspMap i) (y : CuspHalfSpace) v := by
  have hD : MDifferentiableAt halfCollarModel (𝓡 3) (cuspInteriorDiffeo_C4 T i) y :=
    ((cuspInteriorDiffeo_C4 T i).contMDiff).mdifferentiableAt infty_ne_zero_C4
  have hval : MDifferentiableAt (𝓡 3) (𝓡 3)
      (Subtype.val : (isLocalDiffeomorph_cuspInterior_C4 T i).image → H.Carrier)
      (cuspInteriorDiffeo_C4 T i y) :=
    (contMDiff_subtype_val (I := 𝓡 3)
      (U := (isLocalDiffeomorph_cuspInterior_C4 T i).image)).mdifferentiableAt infty_ne_zero_C4
  have hcomp := mfderiv_comp (I := halfCollarModel) (I' := 𝓡 3) (I'' := 𝓡 3) y hval hD
  have hfun : ((Subtype.val : (isLocalDiffeomorph_cuspInterior_C4 T i).image → H.Carrier) ∘
      (cuspInteriorDiffeo_C4 T i)) = cuspInteriorMap_C4 T i := rfl
  rw [hfun] at hcomp
  refine Eq.trans ?_ (mfderiv_cuspInteriorMap_C4 T i y v)
  rw [hcomp]
  exact (DifferentialGeometry.mfderiv_subtype_val_apply (I := 𝓡 3)
    (isLocalDiffeomorph_cuspInterior_C4 T i).image (cuspInteriorDiffeo_C4 T i y)
    (mfderiv halfCollarModel (𝓡 3) (cuspInteriorDiffeo_C4 T i) y v)).symm

/-- **Interior transfer.** At a point of positive height, the raw `C^k` error of
`(f ∘ cuspMap)^*g - H_cusp` in cusp coordinates equals that of `f^*g - H.metric` at the image. -/
theorem interior_rawNorm_eq_C4 (g : SmoothRiemannianMetric W.model W.Carrier)
    (f : H.Carrier → W.Carrier) (Uo : Opens H.Carrier)
    (hrange : ∀ p ∈ cuspDomain, T.cuspMap i p ∈ Uo)
    (hf : ContMDiffOn (𝓡 3) W.model ∞ f Uo)
    (himm : ∀ y ∈ Uo, Function.Injective (mfderiv (𝓡 3) W.model f y)) (k : ℕ)
    (x : cuspInterior_C4) :
    tensor0SFiberNorm (T.cusp i).metric (x : CuspHalfSpace) (2 + k)
        (iteratedMetricCovariantDerivative (T.cusp i).metric 2
          (rawPullbackError_C4 g (T.cusp i).metric (f ∘ T.cuspMap i)) k (x : CuspHalfSpace)) =
      tensor0SFiberNorm H.metric (T.cuspMap i x) (2 + k)
        (iteratedMetricCovariantDerivative H.metric 2
          (rawPullbackError_C4 g H.metric f) k (T.cuspMap i x)) := by
  classical
  let D := cuspInteriorDiffeo_C4 T i
  let hl := isLocalDiffeomorph_cuspInterior_C4 T i
  let V := hl.image
  have hVU : (V : Set H.Carrier) ⊆ Uo := by
    have hco : (V : Set H.Carrier) = Set.range (cuspInteriorMap_C4 T i) := hl.image_coe
    rw [hco]
    rintro _ ⟨y, rfl⟩
    exact hrange _ (cuspInterior_subset_C4 y.2)
  have hfe : ContMDiffOn halfCollarModel W.model ∞ (f ∘ T.cuspMap i) cuspInterior_C4 :=
    hf.comp (T.cuspEmbedding i).contMDiff.contMDiffOn
      (fun y hy => hrange y (cuspInterior_subset_C4 hy))
  have himme : ∀ y ∈ (cuspInterior_C4 : Set CuspHalfSpace),
      Function.Injective (mfderiv halfCollarModel W.model (f ∘ T.cuspMap i) y) := by
    intro y hy v w h
    have hyU : T.cuspMap i y ∈ Uo := hrange y (cuspInterior_subset_C4 hy)
    have hfd : MDifferentiableAt (𝓡 3) W.model f (T.cuspMap i y) :=
      (hf.contMDiffAt (Uo.isOpen.mem_nhds hyU)).mdifferentiableAt infty_ne_zero_C4
    have hφd : MDifferentiableAt halfCollarModel (𝓡 3) (T.cuspMap i) y :=
      (T.cuspEmbedding i).contMDiff.mdifferentiableAt infty_ne_zero_C4
    rw [mfderiv_comp y hfd hφd] at h
    exact cuspMap_immersion_C4 T i y (himm _ hyU h)
  rw [rawNorm_eq_metricDerivNorm_C4 g (T.cusp i).metric (f ∘ T.cuspMap i) cuspInterior_C4 hfe
    himme k x]
  have hfV : ContMDiffOn (𝓡 3) W.model ∞ f V := hf.mono hVU
  have himmV : ∀ y ∈ (V : Set H.Carrier), Function.Injective (mfderiv (𝓡 3) W.model f y) :=
    fun y hy => himm y (hVU hy)
  have hH := rawNorm_eq_metricDerivNorm_C4 g H.metric f V hfV himmV k (D x)
  have hpt : T.cuspMap i x = ((D x : V) : H.Carrier) := rfl
  rw [hpt, hH]
  haveI : IsManifold halfCollarModel 1 cuspInterior_C4 := IsManifold.of_le (n := ∞) (by decide)
  haveI : IsManifold halfCollarModel 2 cuspInterior_C4 := IsManifold.of_le (n := ∞) (by decide)
  haveI : IsManifold halfCollarModel ((∞ : WithTop ℕ∞) + 1) cuspInterior_C4 := by
    simpa using (inferInstance : IsManifold halfCollarModel ∞ cuspInterior_C4)
  haveI : IsManifold (𝓡 3) 1 V := IsManifold.of_le (n := ∞) (by decide)
  haveI : IsManifold (𝓡 3) 2 V := IsManifold.of_le (n := ∞) (by decide)
  haveI : IsManifold (𝓡 3) ((∞ : WithTop ℕ∞) + 1) V := by
    simpa using (inferInstance : IsManifold (𝓡 3) ∞ V)
  have main : ∀ (qe : SmoothRiemannianMetric halfCollarModel cuspInterior_C4)
      (qv : SmoothRiemannianMetric (𝓡 3) V)
      (hP : SmoothRiemannianMetric halfCollarModel cuspInterior_C4)
      (hV : SmoothRiemannianMetric (𝓡 3) V),
      (∀ y v w, qe.inner y v w = qv.inner (D y) (mfderiv halfCollarModel (𝓡 3) D y v)
        (mfderiv halfCollarModel (𝓡 3) D y w)) →
      (∀ y v w, hP.inner y v w = hV.inner (D y) (mfderiv halfCollarModel (𝓡 3) D y v)
        (mfderiv halfCollarModel (𝓡 3) D y w)) →
      metricDerivNorm k qe hP hP x = metricDerivNorm k qv hV hV (D x) := by
    intro qe qv hP hV h1 h2
    have e1 : qe = Diffeomorph.pullbackMetricCross qv D :=
      SmoothRiemannianMetric.ext_inner (fun y v w =>
        (h1 y v w).trans (Diffeomorph.pullbackMetricCross_inner qv D y v w).symm)
    have e2 : hP = Diffeomorph.pullbackMetricCross hV D :=
      SmoothRiemannianMetric.ext_inner (fun y v w =>
        (h2 y v w).trans (Diffeomorph.pullbackMetricCross_inner hV D y v w).symm)
    rw [e1, e2]
    exact metricDerivNorm_pullbackCross qv hV hV D k x
  refine main _ _ _ _ ?_ ?_
  · intro y v w
    have hF2 : ContMDiff (𝓡 3) W.model ∞ (fun z : V => f z) := contMDiff_restrict_C4 f V hfV
    have hDd : MDifferentiableAt halfCollarModel (𝓡 3) D y := D.contMDiff.mdifferentiableAt infty_ne_zero_C4
    have hc : mfderiv halfCollarModel W.model (fun z : cuspInterior_C4 => (f ∘ T.cuspMap i) z) y =
        (mfderiv (𝓡 3) W.model (fun z : V => f z) (D y)).comp
          (mfderiv halfCollarModel (𝓡 3) D y) :=
      mfderiv_comp y (hF2.mdifferentiableAt infty_ne_zero_C4) hDd
    change localPullInner (I := halfCollarModel) (J := W.model) g
        (fun z : cuspInterior_C4 => (f ∘ T.cuspMap i) z) y v w =
      localPullInner (I := 𝓡 3) (J := W.model) g (fun z : V => f z) (D y)
        (mfderiv halfCollarModel (𝓡 3) D y v) (mfderiv halfCollarModel (𝓡 3) D y w)
    rw [localPullInner_apply, localPullInner_apply, hc]
    rfl
  · intro y v w
    change (T.cusp i).metric.inner (y : CuspHalfSpace) v w = H.metric.inner (D y : H.Carrier)
      (mfderiv halfCollarModel (𝓡 3) D y v) (mfderiv halfCollarModel (𝓡 3) D y w)
    rw [mfderiv_cuspInteriorDiffeo_C4 T i y v, mfderiv_cuspInteriorDiffeo_C4 T i y w]
    exact (T.cuspIsometry i (y : CuspHalfSpace) v w).symm

end Interior

end GC.LongTime.Ch12
