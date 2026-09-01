import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import DifferentialGeometry.Geometry.Curvature.PullbackNaturalityCross
import DifferentialGeometry.Geometry.Metric.Sphere.CoverQuotient
import DifferentialGeometry.Geometry.Metric.Sphere.PositiveCover
import DifferentialGeometry.Topology.Covering.SemilocallySimplyConnected
import DifferentialGeometry.Topology.StandardModel
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Bundle Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry
namespace Geometry

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

private instance roundSphereFinFact (n : ℕ) :
    Fact (Module.finrank ℝ
      (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨by rw [finrank_euclideanSpace_fin]⟩

theorem exists_round_sphere_cover_of_constant_positive_sectional_curvature
    {n : ℕ} (hn : 1 < n)
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M)
    (hbdry : I.Boundaryless) (hdim : Module.finrank ℝ E = n)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∃ cover : sphere
        (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → M,
      ContMDiff (𝓡 n) I ∞ cover ∧
        Function.Surjective cover ∧
        IsCoveringMap cover ∧
        ∀ (x : sphere
            (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
          (v w : TangentSpace (𝓡 n) x),
          (scaleMetric c hc g).inner (cover x)
              (mfderiv (𝓡 n) I cover x v)
              (mfderiv (𝓡 n) I cover x w) =
            (roundMetric
              (E := EuclideanSpace ℝ (Fin (n + 1)))
              (n := n)).inner x v w := by
  classical
  let : CompactSpace M := hcompact
  let : ConnectedSpace M := hconn
  let : I.Boundaryless := hbdry
  let : NeZero (Module.finrank ℝ E) :=
    ⟨by rw [hdim]; omega⟩
  let : NeZero n := ⟨by omega⟩
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n) := by
    exact ContinuousLinearEquiv.ofFinrankEq (by
      rw [hdim, finrank_euclideanSpace_fin])
  let S := Topology.stdModelCopy (I := I) (M := M) e
  let : CompactSpace S.Q := S.equiv.toHomeomorph.compactSpace
  let : ConnectedSpace S.Q :=
    S.equiv.surjective.connectedSpace S.equiv.continuous
  let : Inhabited S.Q := Classical.inhabited_of_nonempty inferInstance
  let : LocallyPathConnectedSpace S.Q :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin n)) S.Q
  let : Riemannian.Topology.SemilocallySimplyConnectedSpace S.Q :=
    Riemannian.Topology.manifold_semilocallySimplyConnectedSpace
      (I := 𝓡 n) (M := S.Q)
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [finrank_euclideanSpace_fin]
    infer_instance
  let gQ : SmoothRiemannianMetric (𝓡 n) S.Q :=
    Diffeomorph.pullbackMetricCross (I := 𝓡 n) (J := I) g S.equiv.symm
  have hsecQ :
      ∀ x : S.Q, ∀ X Y : TangentSpace (𝓡 n) x,
        metricRm04StdAt (I := 𝓡 n) (M := S.Q) gQ x X Y Y X =
          c * (gQ.inner x X X * gQ.inner x Y Y -
            gQ.inner x X Y * gQ.inner x X Y) := by
    intro x X Y
    rw [metricRm04Std_pullbackCross g S.equiv.symm x X Y Y X,
      hsec,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x X X,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x Y Y,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x X Y]
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  let p : sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    sphereBasisPt i0
  let q : sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    sphereBasisPt i1
  have hi : i0 ≠ i1 := by
    intro hi
    have := congrArg Fin.val hi
    simp [i0, i1] at this
  have hpq : p ≠ q := by
    simpa only [p, q] using sphereBasisPt_ne hi
  have hqneg : q ≠ -p := by
    simpa only [p, q] using sphereBasisPt_ne_neg hi
  obtain ⟨d, hd⟩ := sphereCover_one
    (A := EuclideanSpace ℝ (Fin (n + 1))) (n := n) (Q := S.Q)
    hn gQ c hc hsecQ p q hpq hqneg
  let proj : sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → S.Q :=
    Riemannian.Topology.UniversalCover.proj ∘ d
  let cover : sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → M :=
    S.equiv.symm ∘ proj
  have hprojSurj : Function.Surjective
      (Riemannian.Topology.UniversalCover.proj :
        Riemannian.Topology.UniversalCover S.Q → S.Q) := by
    let : PathConnectedSpace S.Q :=
      PathConnectedSpace.of_locallyPathConnectedSpace
    intro x
    let gamma : Path (default : S.Q) x :=
      PathConnectedSpace.somePath default x
    exact ⟨⟨x, Path.Homotopic.Quotient.mk gamma⟩, rfl⟩
  have hprojCont : ContMDiff (𝓡 n) (𝓡 n) ∞ proj :=
    (Riemannian.Topology.UniversalCover.proj_contMDiff
      (I := 𝓡 n) (M := S.Q)).comp d.contMDiff
  have hprojLocal : IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ proj :=
    isLocalDiffeomorph_comp
      (Riemannian.Topology.UniversalCover.proj_localDiffeo
        (I := 𝓡 n) (M := S.Q)) d.isLocalDiffeomorph
  have hcoverLocal : IsLocalDiffeomorph (𝓡 n) I ∞ cover :=
    isLocalDiffeomorph_comp S.equiv.symm.isLocalDiffeomorph hprojLocal
  refine ⟨cover, S.equiv.symm.contMDiff.comp hprojCont,
    S.equiv.symm.surjective.comp (hprojSurj.comp d.surjective),
    hcoverLocal.isLocalHomeomorph.covering_compact, ?_⟩
  intro x v w
  have hprojDeriv (u : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 n) (𝓡 n) proj x u =
        mfderiv (𝓡 n) (𝓡 n) d x u := by
    rw [show proj = Riemannian.Topology.UniversalCover.proj ∘ d from rfl,
      mfderiv_comp_apply x
        ((Riemannian.Topology.UniversalCover.proj_contMDiff
          (I := 𝓡 n) (M := S.Q)).mdifferentiableAt (by simp))
        (d.contMDiff.mdifferentiableAt (by simp)),
      (Riemannian.Topology.UniversalCover.hasMFDerivAt_proj
        (I := 𝓡 n) (M := S.Q) (d x)).mfderiv]
    rfl
  have hcoverDeriv (u : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 n) I cover x u =
        mfderiv (𝓡 n) I S.equiv.symm (proj x)
          (mfderiv (𝓡 n) (𝓡 n) proj x u) := by
    rw [show cover = S.equiv.symm ∘ proj from rfl,
      mfderiv_comp_apply x
        (S.equiv.symm.contMDiff.mdifferentiableAt (by simp))
        (hprojCont.mdifferentiableAt (by simp))]
  rw [scaleMetric_inner, hcoverDeriv v, hcoverDeriv w]
  change c * g.inner (S.equiv.symm (proj x))
      (mfderiv (𝓡 n) I S.equiv.symm (proj x)
        (mfderiv (𝓡 n) (𝓡 n) proj x v))
      (mfderiv (𝓡 n) I S.equiv.symm (proj x)
        (mfderiv (𝓡 n) (𝓡 n) proj x w)) = _
  rw [← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm (proj x)]
  rw [hprojDeriv v, hprojDeriv w]
  change (Riemannian.Topology.UniversalCover.liftedMetric
      (I := 𝓡 n) (scaleMetric c hc gQ)).inner (d x)
        (mfderiv (𝓡 n) (𝓡 n) d x v)
        (mfderiv (𝓡 n) (𝓡 n) d x w) = _
  exact hd x v w

theorem exists_round_two_sphere_cover_of_constant_positive_sectional_curvature
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M)
    (hbdry : I.Boundaryless) (hdim : Module.finrank ℝ E = 2)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∃ cover : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M,
      ContMDiff (𝓡 2) I ∞ cover ∧
        Function.Surjective cover ∧
        IsCoveringMap cover ∧
        ∀ (x : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
          (v w : TangentSpace (𝓡 2) x),
          (scaleMetric c hc g).inner (cover x)
              (mfderiv (𝓡 2) I cover x v)
              (mfderiv (𝓡 2) I cover x w) =
            (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner x v w := by
  simpa only [Nat.reduceAdd] using
    exists_round_sphere_cover_of_constant_positive_sectional_curvature
      (I := I) (M := M) (n := 2) (by omega)
      hcompact hconn hbdry hdim g c hc hsec

theorem exists_round_three_sphere_cover_of_constant_positive_sectional_curvature
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M)
    (hbdry : I.Boundaryless) (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    ∃ cover : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      ContMDiff (𝓡 3) I ∞ cover ∧
        Function.Surjective cover ∧
        IsCoveringMap cover ∧
        ∀ (x : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
          (v w : TangentSpace (𝓡 3) x),
          (scaleMetric c hc g).inner (cover x)
              (mfderiv (𝓡 3) I cover x v)
              (mfderiv (𝓡 3) I cover x w) =
            (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)).inner x v w := by
  simpa only [Nat.reduceAdd] using
    exists_round_sphere_cover_of_constant_positive_sectional_curvature
      (I := I) (M := M) (n := 3) (by omega)
      hcompact hconn hbdry hdim g c hc hsec

noncomputable def constPosQuotientOfFinrank
    {n : ℕ} [NeZero n] (hn : 1 < n)
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M)
    (hbdry : I.Boundaryless) (hdim : Module.finrank ℝ E = n)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    Σ data : RoundQuotientData.{0, u}
        (EuclideanSpace ℝ (Fin (n + 1))) n,
      M ≃ₘ⟮I, 𝓡 n⟯ data.Q := by
  classical
  letI : CompactSpace M := hcompact
  letI : ConnectedSpace M := hconn
  letI : I.Boundaryless := hbdry
  letI : NeZero (Module.finrank ℝ E) :=
    ⟨by rw [hdim]; omega⟩
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin n) := by
    exact ContinuousLinearEquiv.ofFinrankEq (by
      rw [hdim, finrank_euclideanSpace_fin])
  let S := Topology.stdModelCopy (I := I) (M := M) e
  letI : CompactSpace S.Q := S.equiv.toHomeomorph.compactSpace
  letI : ConnectedSpace S.Q :=
    S.equiv.surjective.connectedSpace S.equiv.continuous
  letI : Inhabited S.Q :=
    Classical.inhabited_of_nonempty inferInstance
  letI : LocallyPathConnectedSpace S.Q :=
    ChartedSpace.locallyPathConnectedSpace
      (EuclideanSpace ℝ (Fin n)) S.Q
  letI : Riemannian.Topology.SemilocallySimplyConnectedSpace S.Q :=
    Riemannian.Topology.manifold_semilocallySimplyConnectedSpace
      (I := 𝓡 n) (M := S.Q)
  letI : NeZero
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [finrank_euclideanSpace_fin]
    infer_instance
  let gQ : SmoothRiemannianMetric (𝓡 n) S.Q :=
    Diffeomorph.pullbackMetricCross
      (I := 𝓡 n) (J := I) g S.equiv.symm
  have hsecQ :
      ∀ x : S.Q, ∀ X Y : TangentSpace (𝓡 n) x,
        metricRm04StdAt (I := 𝓡 n) (M := S.Q) gQ x X Y Y X =
          c * (gQ.inner x X X * gQ.inner x Y Y -
            gQ.inner x X Y * gQ.inner x X Y) := by
    intro x X Y
    rw [metricRm04Std_pullbackCross g S.equiv.symm x X Y Y X,
      hsec,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x X X,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x Y Y,
      ← Diffeomorph.pullbackMetricCross_inner g S.equiv.symm x X Y]
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  let p : sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    sphereBasisPt i0
  let q : sphere
      (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    sphereBasisPt i1
  have hi : i0 ≠ i1 := by
    intro hi
    have := congrArg Fin.val hi
    simp [i0, i1] at this
  have hpq : p ≠ q := by
    simpa only [p, q] using sphereBasisPt_ne hi
  have hqneg : q ≠ -p := by
    simpa only [p, q] using sphereBasisPt_ne_neg hi
  have hcover := sphereCover_one
    (A := EuclideanSpace ℝ (Fin (n + 1))) (n := n) (Q := S.Q)
    hn gQ c hc hsecQ p q hpq hqneg
  let d := Classical.choose hcover
  have hd := Classical.choose_spec hcover
  let g1 : SmoothRiemannianMetric (𝓡 n) S.Q :=
    scaleMetric (I := 𝓡 n) c hc gQ
  let data : RoundQuotientData.{0, u}
      (EuclideanSpace ℝ (Fin (n + 1))) n :=
    roundQuotientUC g1 d (by simpa only [g1] using hd)
  refine ⟨data, ?_⟩
  change M ≃ₘ⟮I, 𝓡 n⟯ S.Q
  exact S.equiv

noncomputable def constPosQuotient
    (hcompact : CompactSpace M) (hconn : ConnectedSpace M)
    (hbdry : I.Boundaryless) (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hsec : ∀ x : M, ∀ X Y : TangentSpace I x,
      metricRm04StdAt (I := I) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y -
          g.inner x X Y * g.inner x X Y)) :
    Σ data : RoundQuotientData.{0, u}
        (EuclideanSpace ℝ (Fin 4)) 3,
      M ≃ₘ⟮I, 𝓡 3⟯ data.Q := by
  simpa only [Nat.reduceAdd] using
    constPosQuotientOfFinrank
      (I := I) (M := M) (n := 3) (by omega)
      hcompact hconn hbdry hdim g c hc hsec

end Geometry
end DifferentialGeometry
