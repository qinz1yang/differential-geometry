import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCap

set_option autoImplicit false
noncomputable section

open Set Function

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  {T : TubeSystem M} (K : Capping T N)
  (A : T.Boundary → ThreeBall ≃ₜ ThreeBall)
  (a : T.Boundary → Sphere 2 ≃ₜ Sphere 2)
  (hboundary : ∀ b y, A b (sphereToThreeBall y) = sphereToThreeBall (a b y))

def reparametrizeCaps : Capping T N where
  coreInclusion := K.coreInclusion
  coreEmbedding := K.coreEmbedding
  cap b := (K.cap b).comp ⟨A b, (A b).continuous⟩
  capEmbedding b := (K.capEmbedding b).comp (A b).isEmbedding
  attaching b := (a b).trans (K.attaching b)
  boundary_eq b y := by
    change K.cap b (A b (sphereToThreeBall y)) =
      K.coreInclusion (T.coreBoundarySphere b (K.attaching b (a b y)))
    rw [hboundary]
    exact K.boundary_eq b (a b y)
  exhaustive := by
    change range K.coreInclusion ∪ (⋃ b, range (K.cap b ∘ A b)) = univ
    simp only [Surjective.range_comp (A _).surjective]
    exact K.exhaustive
  core_cap_intersection b := by
    change range K.coreInclusion ∩ range (K.cap b ∘ A b) =
      range (K.coreInclusion.comp (T.coreBoundarySphere b))
    rw [(A b).surjective.range_comp]
    exact K.core_cap_intersection b
  cap_disjoint := by
    intro b c hbc
    change Disjoint (range (K.cap b ∘ A b)) (range (K.cap c ∘ A c))
    rw [(A b).surjective.range_comp, (A c).surjective.range_comp]
    exact K.cap_disjoint hbc

theorem reparametrizeCaps_coreInclusion :
    (K.reparametrizeCaps A a hboundary).coreInclusion = K.coreInclusion := rfl

theorem reparametrizeCaps_cap (b : T.Boundary) (x : ThreeBall) :
    (K.reparametrizeCaps A a hboundary).cap b x = K.cap b (A b x) := rfl

theorem reparametrizeCaps_attaching (b : T.Boundary) (y : Sphere 2) :
    (K.reparametrizeCaps A a hboundary).attaching b y = K.attaching b (a b y) := rfl

theorem range_cap_reparametrizeCaps (b : T.Boundary) :
    range ((K.reparametrizeCaps A a hboundary).cap b) = range (K.cap b) :=
  (A b).surjective.range_comp (K.cap b)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.Capping

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology

variable {M Q D N : Type*} [TopologicalSpace M] [TopologicalSpace Q]
  [TopologicalSpace D] [TopologicalSpace N] (E : CutCapTopology M Q D N)
  (A : E.tubes.Boundary → ThreeBall ≃ₜ ThreeBall)
  (a : E.tubes.Boundary → Sphere 2 ≃ₜ Sphere 2)
  (hboundary : ∀ b y, A b (sphereToThreeBall y) = sphereToThreeBall (a b y))

def reparametrizeCaps : CutCapTopology M Q D N where
  tubes := E.tubes
  capping := E.capping.reparametrizeCaps A a hboundary
  presentation := E.presentation
  nontrivial := E.nontrivial

theorem reparametrizeCaps_retainedCore :
    (E.reparametrizeCaps A a hboundary).retainedCore = E.retainedCore := rfl

theorem reparametrizeCaps_tubes : (E.reparametrizeCaps A a hboundary).tubes = E.tubes := rfl

theorem reparametrizeCaps_presentation :
    (E.reparametrizeCaps A a hboundary).presentation = E.presentation := rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.CutCapTopology
