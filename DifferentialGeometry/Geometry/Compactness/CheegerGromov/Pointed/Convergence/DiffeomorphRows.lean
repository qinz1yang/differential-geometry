import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.OpenEmbedding
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCrossConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange
import DifferentialGeometry.Topology.Manifold.Diffeomorph.Preimage
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open Geometry.Curvature

universe u uN uE uH uF uG
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type uG} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type uN} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N] [T2Space N]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : CompleteSpace F := FiniteDimensional.complete ℝ F
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem exists_pointed_convergence_of_local_pullbacks_along_diffeomorph
    {X : PointedRiemannianSeq.{u, uE, uH} I} {P : PointedRiemannianManifold.{u, uE, uH} I}
    [PreconnectedSpace P.M] (e : P.M ≃ₘ⟮I, J⟯ N)
    (g : SmoothRiemannianMetric J N) (hmetric : P.metric = Diffeomorph.pullbackMetricCross g e)
    (f : ℕ → ℕ) (U : ℕ → TopologicalSpace.Opens N) (hp : ∀ i, e P.basepoint ∈ U i)
    (psi : ∀ i, U i → (X.obj (f i)).M)
    (hpsi : ∀ i, IsLocalDiffeomorph J I ∞ (psi i)) (hinj : ∀ i, Function.Injective (psi i))
    (hbase : ∀ i, psi i ⟨e P.basepoint, hp i⟩ = (X.obj (f i)).basepoint)
    (hexhaust : ∀ K : Set N, IsCompact K → ∀ᶠ i in atTop, K ⊆ U i)
    (hlocal : ∀ K : Set N, IsCompact K →
      ∃ W : TopologicalSpace.Opens N, K ⊆ W ∧
        ∃ Gm : ℕ → SmoothRiemannianMetric J W,
          MetricCInfConvergenceOnCompacts Gm (g.restrictOpen W) (g.restrictOpen W) ∧
          ∀ᶠ i in atTop, ∃ hWU : W ≤ U i,
            ∀ (x : W) (v w : TangentSpace J x),
              (Gm i).inner x v w = (X.obj (f i)).metric.inner
                (psi i (TopologicalSpace.Opens.inclusion hWU x))
                (mfderiv J I (fun y : W => psi i (TopologicalSpace.Opens.inclusion hWU y)) x v)
                (mfderiv J I (fun y : W => psi i (TopologicalSpace.Opens.inclusion hWU y)) x w)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ maps : PointedRiemannianConvergenceMaps X P (f ∘ k),
      (∀ i (z : U (k i)), maps.map i (e.symm z) = psi (k i) z) ∧
      (∀ i, maps.source i ⊆ e ⁻¹' U (k i)) ∧
      (∀ i, IsCompact (closure (maps.source i))) ∧ (∀ i, IsConnected (maps.source i)) ∧
      ∃ C : MetricConvergenceData maps,
        ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData maps i := by
  let V (i) : TopologicalSpace.Opens P.M := ⟨e ⁻¹' U i, (U i).isOpen.preimage e.continuous⟩
  let d (i) := DifferentialGeometry.Manifold.Diffeomorph.preimage e (U i)
  let psi' (i) : V i → (X.obj (f i)).M := fun x => psi i (d i x)
  have hlocal' : ∀ K : Set P.M, IsCompact K →
      ∃ W : TopologicalSpace.Opens P.M, K ⊆ W ∧
        ∃ Gm : ℕ → SmoothRiemannianMetric I W,
          MetricCInfConvergenceOnCompacts Gm (P.metric.restrictOpen W) (P.metric.restrictOpen W) ∧
          ∀ᶠ i in atTop, ∃ hWV : W ≤ V i,
            ∀ (x : W) (v w : TangentSpace I x),
              (Gm i).inner x v w = (X.obj (f i)).metric.inner
                (psi' i (TopologicalSpace.Opens.inclusion hWV x))
                (mfderiv I I (fun y : W => psi' i (TopologicalSpace.Opens.inclusion hWV y)) x v)
                (mfderiv I I (fun y : W => psi' i (TopologicalSpace.Opens.inclusion hWV y)) x w) := by
    intro K hK
    obtain ⟨W, hKW, Gm, hconv, hGm⟩ := hlocal (e '' K) (hK.image e.continuous)
    let W' : TopologicalSpace.Opens P.M := ⟨e ⁻¹' W, W.isOpen.preimage e.continuous⟩
    let dW := DifferentialGeometry.Manifold.Diffeomorph.preimage e W
    let _ : SigmaCompactSpace W' := isSigmaCompact_iff_sigmaCompactSpace.mp
      (Geometry.isSigmaCompact_of_isOpen I W'.isOpen)
    let _ : SigmaCompactSpace W := by
      apply (isSigmaCompact_univ_iff (X := W)).mp
      have hh := (isSigmaCompact_univ : IsSigmaCompact (univ : Set W')).image dW.continuous
      have heq : dW '' (univ : Set W') = (univ : Set W) := by
        ext y
        constructor
        · intro _
          trivial
        · intro _
          exact ⟨dW.symm y, mem_univ _, dW.apply_symm_apply y⟩
      exact heq ▸ hh
    let G' := fun i => Diffeomorph.pullbackMetricCross (Gm i) dW
    have hdW (x : W') (v : TangentSpace I x) : mfderiv I J dW x v = mfderiv I J e (x : P.M) v := by
      have hh := DifferentialGeometry.mfderiv_subtypeVal_comp (I := I) (J := J) dW x
      have he := DifferentialGeometry.mfderiv_restrict_open (I := I) (J := J) e W' x
      exact congrArg (fun D => D v) (hh.symm.trans he)
    have hlim : Diffeomorph.pullbackMetricCross (g.restrictOpen W) dW = P.metric.restrictOpen W' := by
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      have hl := (Diffeomorph.pullbackMetricCross_inner (g.restrictOpen W) dW x v w).trans
        (SmoothRiemannianMetric.restrictOpen_inner g W (dW x)
          (mfderiv I J dW x v) (mfderiv I J dW x w))
      have hr := SmoothRiemannianMetric.restrictOpen_inner P.metric W' x v w
      have hright : P.metric.inner (x : P.M) v w =
          g.inner (e (x : P.M)) (mfderiv I J e (x : P.M) v) (mfderiv I J e (x : P.M) w) := by
        rw [hmetric]
        exact Diffeomorph.pullbackMetricCross_inner g e (x : P.M) v w
      have hr' := hr.trans hright
      apply hl.trans
      apply Eq.trans _ hr'.symm
      exact congrArg₂ (fun v' w' => g.inner (e (x : P.M)) v' w') (hdW x v) (hdW x w)
    refine ⟨W', fun x hx => hKW ⟨x,hx,rfl⟩, G', ?_, ?_⟩
    · have hh := PDE.RicciFlow.Perelman.KappaSolutions.metricCInfConvOnCompacts_pullbackCross
        Gm (g.restrictOpen W) (g.restrictOpen W) dW hconv
      rwa [hlim] at hh
    filter_upwards [hGm] with i hi
    obtain ⟨hWU, hGi⟩ := hi
    have hWV : W' ≤ V i := fun x hx => hWU hx
    refine ⟨hWV, ?_⟩
    intro x v w
    let h : W → (X.obj (f i)).M := fun y => psi i (TopologicalSpace.Opens.inclusion hWU y)
    have heq : (fun y : W' => psi' i (TopologicalSpace.Opens.inclusion hWV y)) = h ∘ dW := rfl
    have hhd : MDifferentiableAt J I h (dW x) := by
      exact (hpsi i).mdifferentiable (by decide) _ |>.comp _
        ((contMDiff_inclusion (I := J) (n := ∞) hWU).mdifferentiable (by decide) _)
    have hd (z : TangentSpace I x) :
        mfderiv I I (fun y : W' => psi' i (TopologicalSpace.Opens.inclusion hWV y)) x z =
          mfderiv J I h (dW x) (mfderiv I J dW x z) := by
      rw [heq]
      exact mfderiv_comp_apply x hhd (dW.contMDiff.mdifferentiable (by decide) x) z
    rw [Diffeomorph.pullbackMetricCross_inner]
    have hh := hGi (dW x) (mfderiv I J dW x v) (mfderiv I J dW x w)
    exact hh.trans (by rw [hd, hd]; rfl)
  obtain ⟨k, hk, maps, hmap, hsrc, hcpt, hconn, C, hC⟩ :=
    exists_pointed_convergence_of_injective_local_diffeomorphs f V hp psi'
      (fun i => DifferentialGeometry.isLocalDiffeomorph_comp (hpsi i) (d i).isLocalDiffeomorph)
      (fun i => (hinj i).comp (d i).injective) hbase
      (fun K hK => (hexhaust (e '' K) (hK.image e.continuous)).mono fun i hi x hx => hi ⟨x,hx,rfl⟩)
      hlocal'
  refine ⟨k, hk, maps, ?_, hsrc, hcpt, hconn, C, hC⟩
  intro i z
  let y : V (k i) := ⟨e.symm z, by change e (e.symm z) ∈ U (k i); simpa only [e.apply_symm_apply] using z.property⟩
  have hh := hmap i y
  have hy : d (k i) y = z := by apply Subtype.ext; exact e.apply_symm_apply z
  simpa only [psi', hy] using hh

end DifferentialGeometry.CheegerGromovCompactness
