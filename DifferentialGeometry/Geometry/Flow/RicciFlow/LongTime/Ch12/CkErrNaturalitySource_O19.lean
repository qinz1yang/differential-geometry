import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CkErrNaturality_O19
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryNaturalityRaw
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

/-!
# CH12-O19 G1: isometry naturality of `ckErr_O19` (source side)

`ckErr_comp_isometry_source_O19` (N2): for a smooth isometric equivalence `e : H ≃ H'` and a map
`φ` that is smooth and immersive on an open `U'`, `ckErr (φ ∘ e) = ckErr φ ∘ e` (any `c > 0`).
Route: scale `c` into the target metric; `rawNorm_eq_metricDerivNorm_C4` on the open sets
`e⁻¹ U'` and `e '' e⁻¹ U'`; `metricDerivNorm_pullbackCross` for the restricted diffeomorphism.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open Set
open scoped Manifold ContDiff Topology

namespace GC.LongTime.Ch12

universe u

/-- `ckErr` with `c = 1` is the raw error norm of `ThinBoundaryNaturalityRaw`. -/
theorem ckErr_one_eq_raw_O19 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g : SmoothRiemannianMetric (𝓡 3) N) (F : H.Carrier → N) (j : ℕ) (p : H.Carrier) :
    ckErr_O19 H g 1 F j p = tensor0SFiberNorm H.metric p (2 + j)
      (iteratedMetricCovariantDerivative H.metric 2 (rawPullbackError_C4 g H.metric F) j p) := by
  unfold ckErr_O19 rawPullbackError_C4
  simp only [one_smul]

/-- Scaling `c > 0` into the target metric. -/
theorem ckErr_eq_scale_O19 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    (g : SmoothRiemannianMetric (𝓡 3) N) (c : ℝ) (hc : 0 < c) (F : H.Carrier → N) (j : ℕ)
    (p : H.Carrier) :
    ckErr_O19 H g c F j p = ckErr_O19 H (scaleMetric c hc g) 1 F j p := by
  have h : ∀ q : H.Carrier, c • localPullInner (I := 𝓡 3) g F q =
      (1 : ℝ) • localPullInner (I := 𝓡 3) (scaleMetric c hc g) F q := by
    intro q
    ext v w
    simp [localPullInner_apply, scaleMetric_inner]
  unfold ckErr_O19
  simp only [h]

/-- `e` as a diffeomorphism. -/
def isoDiffeo_O19 {H H' : FiniteVolumeHyperbolicModel.{u}} (e : H.Carrier ≃ H'.Carrier)
    (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e) (he' : ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm) :
    Diffeomorph (𝓡 3) (𝓡 3) H.Carrier H'.Carrier ∞ where
  toEquiv := e
  contMDiff_toFun := he
  contMDiff_invFun := he'

/-- **N2 (source-side isometry naturality).** -/
theorem ckErr_comp_isometry_source_O19 (H H' : FiniteVolumeHyperbolicModel.{u})
    (e : H.Carrier ≃ H'.Carrier) (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e)
    (he' : ContMDiff (𝓡 3) (𝓡 3) ∞ e.symm)
    (hiso : ∀ p, localPullInner H'.metric e p = H.metric.inner p)
    {N : Type u} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
    [IsManifold (𝓡 3) ∞ N] (gN : SmoothRiemannianMetric (𝓡 3) N)
    (U' : TopologicalSpace.Opens H'.Carrier) (φ : H'.Carrier → N)
    (hφ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U')
    (hinj : ∀ y ∈ U', Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ y))
    (c : ℝ) (hc : 0 < c) (j : ℕ) (p : H.Carrier) (hp : e p ∈ U') :
    ckErr_O19 H gN c (fun q => φ (e q)) j p = ckErr_O19 H' gN c φ j (e p) := by
  have hinf : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  rw [ckErr_eq_scale_O19 H gN c hc, ckErr_eq_scale_O19 H' gN c hc]
  set g := scaleMetric c hc gN
  let Φ := (isoDiffeo_O19 e he he').toPartialDiffeomorph
  let V : TopologicalSpace.Opens H.Carrier := ⟨e ⁻¹' U', U'.isOpen.preimage he.continuous⟩
  have hV : (V : Set H.Carrier) ⊆ Φ.source := fun x _ => mem_univ x
  let W : TopologicalSpace.Opens H'.Carrier :=
    ⟨(Φ : H.Carrier → H'.Carrier) '' (V : Set H.Carrier),
      image_opens_isOpen Φ hV⟩
  have hWU : (W : Set H'.Carrier) ⊆ U' := by
    rintro y ⟨x, hx, rfl⟩; exact hx
  let eV : Diffeomorph (𝓡 3) (𝓡 3) V W ∞ := PartialDiffeomorph.toOpensDiffeo Φ hV
  have hpV : p ∈ V := hp
  have hpW : e p ∈ W := ⟨p, hpV, rfl⟩
  -- derivative facts
  have hDe : ∀ z : H.Carrier, Function.Injective (mfderiv (𝓡 3) (𝓡 3) e z) := by
    intro z v w hvw
    have hc1 : ∀ u : TangentSpace (𝓡 3) z,
        mfderiv (𝓡 3) (𝓡 3) e.symm (e z) (mfderiv (𝓡 3) (𝓡 3) e z u) = u := by
      intro u
      have h1 := mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) z
        ((he' (e z)).mdifferentiableAt hinf) ((he z).mdifferentiableAt hinf) (v := u)
      have h2 : (e.symm ∘ e) = id := funext e.symm_apply_apply
      rw [← h1, h2, mfderiv_id]
      rfl
    rw [← hc1 v, ← hc1 w, hvw]
  have hcomp : ∀ z ∈ V, ∀ v : TangentSpace (𝓡 3) z,
      mfderiv (𝓡 3) (𝓡 3) (fun q => φ (e q)) z v =
        mfderiv (𝓡 3) (𝓡 3) φ (e z) (mfderiv (𝓡 3) (𝓡 3) e z v) := by
    intro z hz v
    exact mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3) (I'' := 𝓡 3) z
      ((hφ.contMDiffAt (U'.isOpen.mem_nhds hz)).mdifferentiableAt hinf)
      ((he z).mdifferentiableAt hinf) (v := v)
  have hFV : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun q => φ (e q)) V :=
    hφ.comp he.contMDiffOn (fun z hz => hz)
  have hinjV : ∀ z ∈ V, Function.Injective (mfderiv (𝓡 3) (𝓡 3) (fun q => φ (e q)) z) := by
    intro z hz v w hvw
    rw [hcomp z hz v, hcomp z hz w] at hvw
    exact hDe z (hinj (e z) hz hvw)
  have hφW : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ W := hφ.mono hWU
  have hinjW : ∀ y ∈ W, Function.Injective (mfderiv (𝓡 3) (𝓡 3) φ y) :=
    fun y hy => hinj y (hWU hy)
  rw [ckErr_one_eq_raw_O19, ckErr_one_eq_raw_O19]
  rw [rawNorm_eq_metricDerivNorm_C4 g H.metric (fun q => φ (e q)) V hFV hinjV j ⟨p, hpV⟩,
    rawNorm_eq_metricDerivNorm_C4 g H'.metric φ W hφW hinjW j ⟨e p, hpW⟩]
  have hiso_apply : ∀ (x : H.Carrier) (a b : TangentSpace (𝓡 3) x),
      H'.metric.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x a) (mfderiv (𝓡 3) (𝓡 3) e x b) =
        H.metric.inner x a b := by
    intro x a b
    rw [← localPullInner_apply, hiso]
  have hDeV : ∀ (z : V) (v : TangentSpace (𝓡 3) z),
      mfderiv (𝓡 3) (𝓡 3) (eV : V → W) z v = mfderiv (𝓡 3) (𝓡 3) e (z : H.Carrier) v :=
    fun z v => PartialDiffeomorph.mfderiv_toOpensDiffeo Φ hV z v
  have hmet1 : H.metric.restrictOpen V =
      Diffeomorph.pullbackMetricCross (H'.metric.restrictOpen W) eV := by
    ext z v w
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.restrictOpen_inner,
      SmoothRiemannianMetric.restrictOpen_inner, hDeV, hDeV]
    exact (hiso_apply (z : H.Carrier) v w).symm
  rw [hmet1]
  have hpt : (⟨e p, hpW⟩ : W) = eV ⟨p, hpV⟩ := rfl
  have : SecondCountableTopology H.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin 3)) H.Carrier
  have : LocallyCompactSpace V := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) V
  rw [hpt, ← metricDerivNorm_pullbackCross]
  congr 1
  ext z v w
  rw [Diffeomorph.pullbackMetricCross_inner]
  change localPullInner (I := 𝓡 3) g (fun q : V => φ (e q)) z v w =
    localPullInner (I := 𝓡 3) g (fun q : W => φ q) (eV z) _ _
  rw [localPullInner_apply, localPullInner_apply,
    DifferentialGeometry.mfderiv_restrict_open (fun q => φ (e q)) V z,
    DifferentialGeometry.mfderiv_restrict_open φ W (eV z), hDeV, hDeV]
  exact congrArg₂ (fun a b => g.inner (φ (e (z : H.Carrier))) a b)
    (hcomp (z : H.Carrier) z.2 v) (hcomp (z : H.Carrier) z.2 w)

end GC.LongTime.Ch12
