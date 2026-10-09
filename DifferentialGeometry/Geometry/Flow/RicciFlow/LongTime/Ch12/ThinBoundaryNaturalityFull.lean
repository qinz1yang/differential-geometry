import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryDensity
import DifferentialGeometry.Geometry.Collapse.CuspBoundary

/-!
# CH12 C4 (G1): transfer of the `C^k` error from `H` to the cusp coordinates (boundary included)

`rawNorm_eq_all_C4`: for every point `p` of `cuspDomain` (height `0` included) the raw `C^k` error
norm of `(f ∘ cuspMap)^*g - H_cusp` at `p` equals that of `f^*g - H.metric` at `cuspMap p`
(interior points by the diffeomorphism `cuspInteriorDiffeo_C4`; boundary points by continuity and
density).  `cuspMetricErrorBound_of_H_C4` is the resulting `metric_error` field.
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace DifferentialGeometry DifferentialGeometry.Tensor0SBundle
  DifferentialGeometry.Geometry.Connection DifferentialGeometry.CheegerGromovCompactness
  DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse GC.Endpoint
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

variable {W : CompactCarrier.{u}} {H : FiniteVolumeHyperbolicModel.{u}}
  (T : HyperbolicTruncation H) (i : Fin T.count)

theorem rawNorm_eq_all_C4 (g : SmoothRiemannianMetric W.model W.Carrier)
    (f : H.Carrier → W.Carrier) (Uo : Opens H.Carrier)
    (hrange : ∀ p ∈ cuspDomain, T.cuspMap i p ∈ Uo)
    (hf : ContMDiffOn (𝓡 3) W.model ∞ f Uo)
    (himm : ∀ y ∈ Uo, Function.Injective (mfderiv (𝓡 3) W.model f y)) (k : ℕ)
    (p : CuspHalfSpace) (hp : p ∈ cuspDomain) :
    tensor0SFiberNorm (T.cusp i).metric p (2 + k)
        (iteratedMetricCovariantDerivative (T.cusp i).metric 2
          (rawPullbackError_C4 g (T.cusp i).metric (f ∘ T.cuspMap i)) k p) =
      tensor0SFiberNorm H.metric (T.cuspMap i p) (2 + k)
        (iteratedMetricCovariantDerivative H.metric 2
          (rawPullbackError_C4 g H.metric f) k (T.cuspMap i p)) := by
  classical
  have hrangeD : ∀ y ∈ (cuspDomainOpens_C4 : Set CuspHalfSpace), T.cuspMap i y ∈ Uo := hrange
  have hfe : ContMDiffOn halfCollarModel W.model ∞ (f ∘ T.cuspMap i) cuspDomainOpens_C4 :=
    hf.comp (T.cuspEmbedding i).contMDiff.contMDiffOn hrangeD
  have himme : ∀ y ∈ (cuspDomainOpens_C4 : Set CuspHalfSpace),
      Function.Injective (mfderiv halfCollarModel W.model (f ∘ T.cuspMap i) y) := by
    intro y hy v w h
    have hyU : T.cuspMap i y ∈ Uo := hrangeD y hy
    have hfd : MDifferentiableAt (𝓡 3) W.model f (T.cuspMap i y) :=
      (hf.contMDiffAt (Uo.isOpen.mem_nhds hyU)).mdifferentiableAt infty_ne_zero_C4
    have hφd : MDifferentiableAt halfCollarModel (𝓡 3) (T.cuspMap i) y :=
      (T.cuspEmbedding i).contMDiff.mdifferentiableAt infty_ne_zero_C4
    rw [mfderiv_comp y hfd hφd] at h
    exact cuspMap_immersion_C4 T i y (himm _ hyU h)
  have hcusp := fun x : cuspDomainOpens_C4 =>
    rawNorm_eq_metricDerivNorm_C4 g (T.cusp i).metric (f ∘ T.cuspMap i) cuspDomainOpens_C4 hfe
      himme k x
  have hH := fun y : Uo =>
    rawNorm_eq_metricDerivNorm_C4 g H.metric f Uo hf himm k y
  -- the two sides as continuous functions on `cuspDomainOpens_C4`
  let A : cuspDomainOpens_C4 → ℝ := fun x => metricDerivNorm k
    (g.pullbackOfImmersion (I := halfCollarModel) (fun z : cuspDomainOpens_C4 => (f ∘ T.cuspMap i) z)
      (contMDiff_restrict_C4 _ _ hfe) (fun z => by
        intro v w hvw
        exact himme z z.property
          ((mfderiv_comp_val_C4 _ _ hfe z v).symm.trans
            (hvw.trans (mfderiv_comp_val_C4 _ _ hfe z w)))))
    ((T.cusp i).metric.restrictOpen cuspDomainOpens_C4)
    ((T.cusp i).metric.restrictOpen cuspDomainOpens_C4) x
  let B : Uo → ℝ := fun y => metricDerivNorm k
    (g.pullbackOfImmersion (I := 𝓡 3) (fun z : Uo => f z) (contMDiff_restrict_C4 _ _ hf)
      (fun z => by
        intro v w hvw
        exact himm z z.property
          ((mfderiv_comp_val_C4 _ _ hf z v).symm.trans
            (hvw.trans (mfderiv_comp_val_C4 _ _ hf z w)))))
    (H.metric.restrictOpen Uo) (H.metric.restrictOpen Uo) y
  have hA : Continuous A := continuous_metricDerivNorm_C4 _ _ _ k
  have hB : Continuous B := continuous_metricDerivNorm_C4 _ _ _ k
  let ι : cuspDomainOpens_C4 → Uo := fun x => ⟨T.cuspMap i x, hrangeD _ x.2⟩
  have hι : Continuous ι :=
    Continuous.subtype_mk ((T.cuspEmbedding i).contMDiff.continuous.comp continuous_subtype_val) _
  have hAB : A = B ∘ ι := by
    have hcl : closure {y : cuspDomainOpens_C4 | 0 < (y : CuspHalfSpace).2.val 0} = univ :=
      eq_univ_of_forall dense_interior_cuspDomain_C4
    have hclosed : IsClosed {x : cuspDomainOpens_C4 | A x = (B ∘ ι) x} :=
      isClosed_eq hA (hB.comp hι)
    have hsub : {y : cuspDomainOpens_C4 | 0 < (y : CuspHalfSpace).2.val 0} ⊆
        {x : cuspDomainOpens_C4 | A x = (B ∘ ι) x} := by
      intro y hy
      have hyI : (y : CuspHalfSpace) ∈ cuspInterior_C4 :=
        ⟨hy, y.2⟩
      have h1 := interior_rawNorm_eq_C4 T i g f Uo hrange hf himm k ⟨y, hyI⟩
      have h2 := hcusp y
      have h3 := hH (ι y)
      change A y = B (ι y)
      change _ = _ at h2
      exact (h2.symm.trans (h1.trans h3)).symm.symm
    have := closure_minimal hsub hclosed
    rw [hcl] at this
    funext x
    exact this (mem_univ x)
  have := congrFun hAB ⟨p, hp⟩
  exact (hcusp ⟨p, hp⟩).trans (this.trans (hH (ι ⟨p, hp⟩)).symm)

/-- **`metric_error` from the `H`-side error.** If the raw `C^k` error `f^*g - H.metric`
(`k ≤ K`) is `≤ δ` at the points of `cuspMap '' cuspDomain`, then the cusp-coordinate error of
`f ∘ cuspMap` against `T.cusp i` is `≤ δ` on `cuspDomain`. -/
theorem cuspMetricErrorBound_of_H_C4 (g : SmoothRiemannianMetric W.model W.Carrier)
    (K : ℕ) (δ : ℝ) (f : H.Carrier → W.Carrier) (Uo : Opens H.Carrier)
    (hrange : ∀ p ∈ cuspDomain, T.cuspMap i p ∈ Uo)
    (hf : ContMDiffOn (𝓡 3) W.model ∞ f Uo)
    (himm : ∀ y ∈ Uo, Function.Injective (mfderiv (𝓡 3) W.model f y))
    (herr : ∀ k : ℕ, k ≤ K → ∀ p ∈ cuspDomain,
      tensor0SFiberNorm H.metric (T.cuspMap i p) (2 + k)
        (iteratedMetricCovariantDerivative H.metric 2
          (rawPullbackError_C4 g H.metric f) k (T.cuspMap i p)) ≤ δ) :
    cuspMetricErrorBound g K δ (T.cusp i) (f ∘ T.cuspMap i) := fun k hk p hp =>
  (rawNorm_eq_all_C4 T i g f Uo hrange hf himm k p hp).trans_le (herr k hk p hp)

end GC.LongTime.Ch12
