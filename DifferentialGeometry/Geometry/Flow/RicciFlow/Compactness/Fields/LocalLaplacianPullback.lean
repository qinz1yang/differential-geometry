import DifferentialGeometry.Geometry.Operator.Laplacian.LocalIsometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedPullbackExtensions


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped ContDiff _root_.Manifold _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

theorem eventually_laplacian_gSeqExt_comp_map
    (Phi : PointedCGHMaps X P phi) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi) (htgt : TargetIsSigmaCompact Phi)
    {K : Set P.M} (hK : IsCompact K) :
    ∀ᶠ k in atTop,
      letI : TopologicalSpace (X.term (phi k)).M := (X.term (phi k)).topology
      letI : ChartedSpace H (X.term (phi k)).M := (X.term (phi k)).charted
      letI : IsManifold I ∞ (X.term (phi k)).M := (X.term (phi k)).smooth
      ∀ (t : ℝ) (f : (X.term (phi k)).M → ℝ) (V : Set (X.term (phi k)).M),
        IsOpen V → ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f V → ∀ y ∈ K, Phi.map k y ∈ V →
          laplacian (Geometry.Connection.LeviCivita (gSeqExt Phi R bf hsrc htgt k t))
            (gSeqExt Phi R bf hsrc htgt k t) (f ∘ Phi.map k) y =
          laplacian (Geometry.Connection.LeviCivita ((X.term (phi k)).S.base.metric t))
            ((X.term (phi k)).S.base.metric t) f (Phi.map k y) := by
  filter_upwards [eventually_gSeqExt_eq_pullback Phi R bf hsrc htgt K hK] with k hk
  let : TopologicalSpace (X.term (phi k)).M := (X.term (phi k)).topology
  let : ChartedSpace H (X.term (phi k)).M := (X.term (phi k)).charted
  let : IsManifold I ∞ (X.term (phi k)).M := (X.term (phi k)).smooth
  let : T2Space (X.term (phi k)).M := (X.term (phi k)).t2
  let : SigmaCompactSpace (X.term (phi k)).M := (X.term (phi k)).sigmaCompact
  intro t f V hV hf y hy hyV
  obtain ⟨U, hU, hKU, hUs, hm⟩ := hk
  have hPhi : IsLocalDiffeomorphOn I I ∞ (Phi.map k) U := by
    intro z
    exact (Phi.partialDiffeomorph k).isLocalDiffeomorphAt I I ∞ (hUs z.2)
  exact laplacian_comp_of_local_isometry_on
    (gSeqExt Phi R bf hsrc htgt k t) ((X.term (phi k)).S.base.metric t)
    hU hPhi (hm t) hV hf (hKU hy) hyV

end DifferentialGeometry.CheegerGromovCompactness
