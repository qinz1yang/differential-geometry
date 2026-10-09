import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitnessTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.LocalPullback
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
private theorem rescaledMetric_congr_scale {D : RealTimeInterval}
    (S : SolutionOn (I := I3) (M := M) D) (t : ℝ) {Q Q' : ℝ} (hQ : 0 < Q) (hQ' : 0 < Q')
    (h : Q = Q') : rescaledMetric S t Q hQ = rescaledMetric S t Q' hQ' := by
  subst h
  rfl

def StrongNeck.castTime {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {eps t t' : ℝ} {x : M} (nk : StrongNeck S eps x t) (h : t = t') : StrongNeck S eps x t' :=
  h ▸ nk

def StrongNeck.ofMetricEq {D D' : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {S' : SolutionOn (I := I3) (M := M) D'} {eps t : ℝ} {x : M} (nk : StrongNeck S eps x t)
    (hmet : ∀ τ, S'.base.metric τ = S.base.metric τ)
    (hD : Icc (t - (S.scalar t x)⁻¹) t ⊆ D'.carrier) : StrongNeck S' eps x t := by
  have hQ : S'.scalar t x = S.scalar t x := by
    change metricScalarAt (S'.base.metric t) x = metricScalarAt (S.base.metric t) x
    rw [hmet]
  have hQpos : 0 < S'.scalar t x := hQ ▸ nk.Q_pos
  have hresc : rescaledMetric S' t (S'.scalar t x) hQpos =
      rescaledMetric S t (S.scalar t x) nk.Q_pos := by
    rw [rescaledMetric_congr_scale S' t hQpos nk.Q_pos hQ]
    funext τ
    simp only [rescaledMetric, hmet]
  refine
    { eps_pos := nk.eps_pos
      eps_small := nk.eps_small
      Q_pos := hQpos
      cylinder := nk.cylinder
      map := nk.map
      center := nk.center
      center_eq := nk.center_eq
      domain := nk.domain
      time_domain := by rw [hQ]; exact hD
      comparison := ?_ }
  rw [hresc]
  exact nk.comparison

variable {N : Type u} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold I3 ∞ N]
  [T2Space N] [SigmaCompactSpace N]

def StrongNeck.ofLocalPullback {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {ι : N → M} (hι : IsLocalDiffeomorph I3 I3 ∞ ι) (hinj : Function.Injective ι)
    {eps t : ℝ} {x : N} (nk : StrongNeck (S.localPullback ι hι) eps x t) :
    StrongNeck S eps (ι x) t := by
  have hex : ∃ e : PartialDiffeomorph I3 I3 N M ∞, e.source = univ ∧ (e : N → M) = ι := by
    obtain ⟨e, hs, -, hf'⟩ := IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_injOn
      (hι.isLocalDiffeomorphOn univ) isOpen_univ ⟨x, trivial⟩ hinj.injOn
    exact ⟨e, hs, hf'⟩
  let e := Classical.choose hex
  have hspec := Classical.choose_spec hex
  have hmem : ∀ y : N, y ∈ e.source := fun y => hspec.1 ▸ mem_univ y
  have he : ((e : PartialDiffeomorph I3 I3 N M ∞) : N → M) = ι := hspec.2
  have hQ : S.scalar t (ι x) = (S.localPullback ι hι).scalar t x := by
    change metricScalarAt (S.base.metric t) (ι x) =
      metricScalarAt (localPullMetric (S.base.metric t) ι hι) x
    rw [metricScalarAt_localPull]
  have hQpos : 0 < S.scalar t (ι x) := hQ ▸ nk.Q_pos
  have hiso : ∀ s, ∀ z ∈ e.source, ∀ v w : TangentSpace I3 z,
      (rescaledMetric S t (S.scalar t (ι x)) hQpos s).inner (e z) (mfderiv I3 I3 e z v)
          (mfderiv I3 I3 e z w) =
        (rescaledMetric (S.localPullback ι hι) t ((S.localPullback ι hι).scalar t x)
          nk.Q_pos s).inner z v w := by
    intro s z _ v w
    rw [rescaledMetric_congr_scale S t hQpos nk.Q_pos hQ]
    simp only [rescaledMetric, scaleMetric_inner, SolutionOn.localPullback_metric,
      localPullMetric_inner]
    rw [he]
  have hF : ∀ y ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹, MDifferentiableAt IC I3 nk.map y := fun y hy =>
    nk.map.mdifferentiableAt (by decide) (nk.domain hy)
  refine
    { eps_pos := nk.eps_pos
      eps_small := nk.eps_small
      Q_pos := hQpos
      cylinder := nk.cylinder
      map := nk.map.trans e
      center := nk.center
      center_eq := ?_
      domain := ?_
      time_domain := by rw [hQ]; exact nk.time_domain
      comparison := nk.comparison.mapIsometry e hiso hF (fun y _ => hmem _) }
  · rw [PartialDiffeomorph.trans_apply, nk.center_eq]
    exact congrFun he x
  · intro y hy
    rw [PartialDiffeomorph.trans_source]
    exact ⟨nk.domain hy, hmem _⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
