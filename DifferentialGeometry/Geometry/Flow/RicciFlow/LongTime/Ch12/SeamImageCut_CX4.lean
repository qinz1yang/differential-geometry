import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeamImage_CX4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutPresentationMain

set_option autoImplicit false

/-!
# Worked cut-presentation instances of the seam-image adapter

The decomposition and seam equation are obtained from `cutAlongTori_C2a_S12`,
whose statement is frozen in `build-logs/ch12/DELIVERIES.md` at `4230848283`.
Only the equality between the transported input maps and the given collars is
assumed. In particular, neither a decomposition nor a seam-range equality is
assumed. All three clauses of the S12 cut theorem are retained in the output.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.Topology Set

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g}

/-- Worked instance for a whole collar family on one slice component. The S12
pointwise `torusInPrime` equation supplies the actual seam parametrisation. -/
theorem cutAlongTori_seamImage_CX4 (s : RegularSlice F.observation)
    (C : ConnectedComponents s.stage.Carrier)
    (A : CollaredTorusFamily_C2a (s.stage.toClosedOrientedManifold.component C).Carrier)
    (f : Fin A.count → Torus → (postStage F.observation s.time).Carrier)
    (reparam : Fin A.count → Torus ≃ Torus)
    (hcollar : ∀ i x, sliceCast_CX4 s (f i (reparam i x)) =
      (A.collar i (x, 0)).val) :
    ∃ (D : TorusDecomposition (s.stage.toClosedOrientedManifold.component C))
      (e : Fin A.count ≃ Fin D.boundary.count),
      D.carrier = cutCarrier_C2a A ∧
      (∀ i (x : Torus), D.reconstructionAtlas.torusInPrime D.reconstruction (e i) x =
        A.collar i (x, 0)) ∧
      (∀ i, ∀ p ∈ signedCollarSource,
        D.reconstructionAtlas.primeSeam D.reconstruction (e i) p = A.collar i p) ∧
      (∀ i, HEq (range (f i)) (range (fun x : Torus =>
        (D.reconstructionAtlas.torusInPrime D.reconstruction (e i) x).val))) := by
  obtain ⟨D, e, hcarrier, htorus, hseam⟩ :=
    cutAlongTori_C2a_S12 (s.stage.toClosedOrientedManifold.component C) A
  refine ⟨D, e, hcarrier, htorus, hseam, fun i => ?_⟩
  apply sliceRange_heq_of_pointwise_CX4 s (f i) _ (reparam i)
  intro x
  exact (hcollar i x).trans (congrArg Subtype.val (htorus i x)).symm

/-- The same worked instance with actual cusp maps, using the identity torus
reparametrisation. The port for each collar can come from a different core. -/
theorem cutAlongTori_cuspSeamImage_CX4 {K : ℕ}
    (cores : PersistentHyperbolicCores F K) (s : RegularSlice F.observation)
    (ht : cores.start ≤ s.time) (C : ConnectedComponents s.stage.Carrier)
    (A : CollaredTorusFamily_C2a (s.stage.toClosedOrientedManifold.component C).Carrier)
    (truncation : ∀ i : Fin cores.count, HyperbolicTruncation (cores.model i))
    (port : Fin A.count → Σ i : Fin cores.count, Fin (truncation i).count)
    (hcollar : ∀ i x, sliceCast_CX4 s
      (cores.map (port i).1 s.time ht
        ((truncation (port i).1).cuspMap (port i).2 (x, halfZero))) =
          (A.collar i (x, 0)).val) :
    ∃ (D : TorusDecomposition (s.stage.toClosedOrientedManifold.component C))
      (e : Fin A.count ≃ Fin D.boundary.count),
      D.carrier = cutCarrier_C2a A ∧
      (∀ i (x : Torus), D.reconstructionAtlas.torusInPrime D.reconstruction (e i) x =
        A.collar i (x, 0)) ∧
      (∀ i, ∀ p ∈ signedCollarSource,
        D.reconstructionAtlas.primeSeam D.reconstruction (e i) p = A.collar i p) ∧
      (∀ i, HEq (range (fun x : Torus => cores.map (port i).1 s.time ht
        ((truncation (port i).1).cuspMap (port i).2 (x, halfZero))))
        (range (fun x : Torus =>
          (D.reconstructionAtlas.torusInPrime D.reconstruction (e i) x).val))) := by
  obtain ⟨D, e, hcarrier, htorus, hseam⟩ :=
    cutAlongTori_C2a_S12 (s.stage.toClosedOrientedManifold.component C) A
  refine ⟨D, e, hcarrier, htorus, hseam, fun i => ?_⟩
  apply seamImage_of_pointwise_CX4 cores s ht (port i).1 (truncation (port i).1)
    (port i).2 C D (e i) (Equiv.refl Torus)
  intro x
  exact (hcollar i x).trans (congrArg Subtype.val (htorus i x)).symm

end GC.LongTime.Ch12
