import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.PositiveSpaceForm


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

open Bundle Metric Manifold
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n + 1)] [NeZero n]

private def tangentOpenEquiv
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
    (U : TopologicalSpace.Opens Q) (x : U) :
    TangentSpace (𝓡 n) (x : Q) ≃L[ℝ] TangentSpace (𝓡 n) x :=
  (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q)).trans
    (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) x).symm

omit [NeZero n] in
private theorem mfderiv_subtype_val_tangentOpenEquiv
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
    (U : TopologicalSpace.Opens Q) (x : U) (v : TangentSpace (𝓡 n) (x : Q)) :
    mfderiv (𝓡 n) (𝓡 n) (Subtype.val : U → Q) x (tangentOpenEquiv U x v) = v := by
  rw [mfderiv_subtype_val_apply]
  apply (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q)).injective
  change tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q)
      ((tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) x).symm
        (tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q) v)) =
    tangentSpaceModelContinuousLinearEquiv (I := 𝓡 n) (x : Q) v
  rw [tangentSpaceModelContinuousLinearEquiv_symm_apply]
  exact tangentSpaceModelContinuousLinearEquiv_apply (I := 𝓡 n) (x : Q) v


theorem roundSphereQuotient_metric_eq_of_projection_inner
    (D : RoundSphereQuotient A n) (g : SmoothRiemannianMetric (𝓡 n) D.Q)
    (hproj : ∀ x (v w : TangentSpace (𝓡 n) x),
      g.inner (D.proj x) (mfderiv (𝓡 n) (𝓡 n) D.proj x v)
        (mfderiv (𝓡 n) (𝓡 n) D.proj x w) = (roundMetric (E := A) (n := n)).inner x v w) :
    D.gQuot = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  let S := D.sectionAt x
  let xW : S.baseNeighborhood := ⟨x, S.mem_baseNeighborhood⟩
  have hx : D.proj (S.toSphere xW) = x := S.toSphere_proj xW
  have hd (u : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 n) (𝓡 n) D.proj (S.toSphere xW)
        (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW
          (tangentOpenEquiv S.baseNeighborhood xW u)) = u := by
    have h := ContinuousLinearMap.ext_iff.mp (S.dproj_sec D.proj_smooth xW)
      (tangentOpenEquiv S.baseNeighborhood xW u)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [hx] at h
    rw [mfderiv_subtype_val_tangentOpenEquiv] at h
    exact h
  rw [D.gQuot_inner, D.gm_apply]
  rw [S.pullback_inner_eval S.mem_baseNeighborhood]
  change (roundMetric (E := A) (n := n)).inner (S.toSphere xW)
    (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW
      (tangentOpenEquiv S.baseNeighborhood xW v))
    (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW
      (tangentOpenEquiv S.baseNeighborhood xW w)) = _
  calc
    _ = g.inner (D.proj (S.toSphere xW))
        (mfderiv (𝓡 n) (𝓡 n) D.proj (S.toSphere xW)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW
            (tangentOpenEquiv S.baseNeighborhood xW v)))
        (mfderiv (𝓡 n) (𝓡 n) D.proj (S.toSphere xW)
          (mfderiv (𝓡 n) (𝓡 n) S.toSphere xW
            (tangentOpenEquiv S.baseNeighborhood xW w))) :=
      (hproj _ _ _).symm
    _ = g.inner (D.proj (S.toSphere xW)) v w :=
      congrArg₂ (fun a b => g.inner (D.proj (S.toSphere xW)) a b) (hd v) (hd w)
    _ = g.inner x v w := by rw [hx]


theorem roundSphereQuotientUC_metric
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace (EuclideanSpace ℝ (Fin n)) Q]
    [IsManifold (𝓡 n) ∞ Q] [T2Space Q] [SigmaCompactSpace Q]
    [BoundarylessManifold (𝓡 n) Q] [ConnectedSpace Q] [LocallyPathConnectedSpace Q]
    [SemilocallySimplyConnectedSpace Q] [Inhabited Q]
    (g : SmoothRiemannianMetric (𝓡 n) Q)
    (d : sphere (0 : A) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ UniversalCover Q)
    (hd : ∀ x (v w : TangentSpace (𝓡 n) x),
      (UniversalCover.liftedMetric (I := 𝓡 n) g).inner (d x)
        (mfderiv (𝓡 n) (𝓡 n) d x v) (mfderiv (𝓡 n) (𝓡 n) d x w) =
          (roundMetric (E := A) (n := n)).inner x v w) :
    (roundQuotientUC g d hd).gQuot = g := by
  apply roundSphereQuotient_metric_eq_of_projection_inner
  intro x v w
  change g.inner (UniversalCover.proj (d x))
    (mfderiv (𝓡 n) (𝓡 n) (UniversalCover.proj ∘ d) x v)
    (mfderiv (𝓡 n) (𝓡 n) (UniversalCover.proj ∘ d) x w) = _
  have hp := (UniversalCover.hasMFDerivAt_proj (I := 𝓡 n) (M := Q) (d x)).mfderiv
  rw [mfderiv_comp_apply x
      ((UniversalCover.proj_contMDiff (I := 𝓡 n) (M := Q)).mdifferentiableAt (by simp))
      (d.contMDiff.mdifferentiableAt (by simp)),
    mfderiv_comp_apply x
      ((UniversalCover.proj_contMDiff (I := 𝓡 n) (M := Q)).mdifferentiableAt (by simp))
      (d.contMDiff.mdifferentiableAt (by simp)), hp]
  exact hd x v w

private instance roundQuotientMetric_sphere4 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]


theorem exists_roundSphereQuotient_metric
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M) (hbdry : I.Boundaryless)
    (hdim : Module.finrank ℝ E = 3) (g : SmoothRiemannianMetric I M)
    (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StandardAt g x X Y Y X = c *
        (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)) :
    ∃ D : RoundSphereQuotient.{0, u} (EuclideanSpace ℝ (Fin 4)) 3,
      ∃ e : M ≃ₘ⟮I, 𝓡 3⟯ D.Q,
        ∀ x : M, ∀ v w : TangentSpace I x,
          D.gQuot.inner (e x) (mfderiv I (𝓡 3) e x v) (mfderiv I (𝓡 3) e x w) =
            c * g.inner x v w := by
  classical
  let _ : CompactSpace M := hcompact
  let _ : ConnectedSpace M := hconn
  let _ : I.Boundaryless := hbdry
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := ContinuousLinearEquiv.ofFinrankEq (by
    rw [hdim, finrank_euclideanSpace_fin])
  let S := DifferentialGeometry.Geometry.Topology.standardModelCopy (I := I) (M := M) e
  let _ : CompactSpace S.Q := S.equiv.toHomeomorph.compactSpace
  let _ : ConnectedSpace S.Q := S.equiv.surjective.connectedSpace S.equiv.continuous
  let _ : Inhabited S.Q := Classical.inhabited_of_nonempty inferInstance
  let _ : LocallyPathConnectedSpace S.Q :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) S.Q
  let _ : SemilocallySimplyConnectedSpace S.Q :=
    manifold_semilocallySimplyConnectedSpace (I := 𝓡 3) (M := S.Q)
  let gQ := Diffeomorph.pullbackMetricCross g S.equiv.symm
  have hsecQ : ∀ x : S.Q, ∀ X Y : TangentSpace (𝓡 3) x,
      metricRm04StandardAt gQ x X Y Y X = c *
        (gQ.inner x X X * gQ.inner x Y Y - gQ.inner x X Y * gQ.inner x X Y) := by
    intro x X Y
    rw [metricRm04Standard_pullbackCross g S.equiv.symm x X Y Y X, hsec,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x X X,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x Y Y,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x X Y]
  let p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := sphereBasisPt 0
  let q : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := sphereBasisPt 1
  have hpq : p ≠ q := by
    simpa only [p, q] using (sphereBasisPt_ne (by decide) :
      sphereBasisPt (0 : Fin 4) ≠ sphereBasisPt (1 : Fin 4))
  have hqneg : q ≠ -p := by
    simpa only [p, q] using (sphereBasisPt_ne_neg (by decide) :
      sphereBasisPt (1 : Fin 4) ≠ -sphereBasisPt (0 : Fin 4))
  obtain ⟨d, hd⟩ := sphereCover_one (A := EuclideanSpace ℝ (Fin 4)) (n := 3)
    (Q := S.Q) (by norm_num) gQ c hc hsecQ p q hpq hqneg
  let D := roundQuotientUC (scaleMetric c hc gQ) d hd
  have hD : D.gQuot = scaleMetric c hc gQ := roundSphereQuotientUC_metric _ d hd
  have hmetric (x : M) (v w : TangentSpace I x) :
      (scaleMetric c hc gQ).inner (S.equiv x)
        (mfderiv I (𝓡 3) S.equiv x v) (mfderiv I (𝓡 3) S.equiv x w) =
          c * g.inner x v w := by
    rw [scaleMetric_inner, Diffeomorph.pullbackMetricCross_inner]
    congr 1
    have hinv (u : TangentSpace I x) :
        mfderiv (𝓡 3) I S.equiv.symm (S.equiv x) (mfderiv I (𝓡 3) S.equiv x u) = u := by
      have h := mfderiv_comp_apply x (S.equiv.symm.contMDiff.mdifferentiableAt (by simp))
        (S.equiv.contMDiff.mdifferentiableAt (by simp)) u
      have hf : (S.equiv.symm : S.Q → M) ∘ S.equiv = id := by
        funext y
        exact S.equiv.symm_apply_apply y
      rw [hf, mfderiv_id] at h
      exact h.symm
    exact (congrArg₂ (fun a b => g.inner (S.equiv.symm (S.equiv x)) a b)
      (hinv v) (hinv w)).trans (by rw [S.equiv.symm_apply_apply])
  refine ⟨D, S.equiv, fun x v w => ?_⟩
  exact (congrArg (fun metric : SmoothRiemannianMetric (𝓡 3) S.Q =>
    metric.inner (S.equiv x) (mfderiv I (𝓡 3) S.equiv x v) (mfderiv I (𝓡 3) S.equiv x w))
      hD).trans (hmetric x v w)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
