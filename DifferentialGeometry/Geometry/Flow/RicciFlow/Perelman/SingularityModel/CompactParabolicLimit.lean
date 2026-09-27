import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.HamiltonIvey
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CompactRankReduction

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]

theorem exists_gaussian_or_roundThreeSphere_solitonModelCovering_of_compact_parabolic_closed_flow_limit
    [I.Boundaryless] [CompactSpace M]
    {D₀ D : RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D₀)
    (hS : IsSolutionOn (I := I) S)
    (time scale : Nat → Real)
    (hscalePos : ∀ i, 0 < scale i)
    (htimeMem : ∀ i, time i ∈ D₀.carrier)
    (hcarrier : ∀ i,
      D.carrier ⊆ (parabolicInterval D₀ (time i) (scale i) (htimeMem i)).carrier)
    (hregular : ∀ i,
      D.regular ⊆ (parabolicInterval D₀ (time i) (scale i) (htimeMem i)).regular)
    (basepoint : Nat → M)
    {L : PointedFlowData.{u, uE, uH} (I := I) D}
    {subseq : Nat → Nat}
    (h : SmoothCGHConverges (I := I)
      (parabolicPointedFlowSeq (I := I) S hS time scale hscalePos htimeMem
        hcarrier hregular basepoint) L subseq)
    (hscale : Tendsto (fun k => scale (subseq k)) atTop atTop)
    {T t₀ : Real}
    (htime : Tendsto (fun k => time (subseq k)) atTop (nhds T))
    (ht₀T : t₀ < T)
    (hslab : ∀ u ∈ D₀.carrier, t₀ ≤ u → Set.Icc t₀ u ⊆ D₀.carrier)
    (hreg : ∀ u ∈ D₀.carrier, t₀ < u → Set.Ioo t₀ u ⊆ D₀.regular)
    (hdim : Module.finrank Real E = 3) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : IsManifold I 1 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 2 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 3 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : T2Space L.M := L.t2
    CompactSpace L.M → ConnectedSpace L.M →
    ∀ (t : D.carrier) (f : C^∞⟮I, L.M; Real⟯),
      normalizedGradientRicciSoliton (I := I) (L.S.family.metric t.1) f →
      (∃ cover : E → L.M,
        solitonModelCovering (euclideanMetric (E := E))
          (gaussianPotential (E := E)) (L.S.family.metric t.1) f cover) ∨
      (∃ cover : Metric.sphere (0 : EuclideanSpace Real (Fin 4)) 1 → L.M,
        solitonModelCovering roundThreeSphereShrinkerMetric
          roundThreeSphereShrinkerPotential (L.S.family.metric t.1) f cover) := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I 1 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 2 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 3 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  intro hcompact hconnected t f hshrinker
  let _ : CompactSpace L.M := hcompact
  let _ : ConnectedSpace L.M := hconnected
  have hcone :=
    CheegerGromovCompactness.SmoothCGHConverges.curvatureOperator_nonnegative_of_parabolic_closed_flow
      (I := I) S hS time scale hscalePos htimeMem hcarrier hregular basepoint h
        hscale htime ht₀T hslab hreg hdim
  exact
    exists_gaussian_or_roundThreeSphere_solitonModelCovering_of_compact_of_finrank_eq_three_of_nonnegative
      (I := I) (M := L.M) hshrinker hdim (hcone t.1 t.2)

end DifferentialGeometry.PDE.RicciFlow.Perelman
