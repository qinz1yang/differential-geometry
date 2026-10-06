import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCores

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal
universe u
namespace GC.LongTime.Ch12

variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- Restart persistent cores at a later time `T ≥ start`. -/
def restartCores_S30 (B : PersistentHyperbolicCores F K) (T : ℝ)
    (hT : B.start ≤ T) : PersistentHyperbolicCores F K where
  count := B.count
  model := B.model
  start := T
  start_pos := B.start_pos.trans_le hT
  accuracy := B.accuracy
  accuracy_pos := fun t ht => B.accuracy_pos t (hT.trans ht)
  accuracy_antitone := fun a ha b hb hab =>
    B.accuracy_antitone (hT.trans ha) (hT.trans hb) hab
  accuracy_decay := B.accuracy_decay
  domain := B.domain
  map := fun i t ht => B.map i t (hT.trans ht)
  smooth := fun i t ht => B.smooth i t (hT.trans ht)
  embedding := fun i t ht => B.embedding i t (hT.trans ht)
  advertised_ball := fun i t ht => B.advertised_ball i t (hT.trans ht)
  exhausts := B.exhausts
  disjoint := fun t ht => B.disjoint t (hT.trans ht)
  metric_error := fun i t ht => B.metric_error i t (hT.trans ht)
  thick_covered := fun t ht p r hr h1 h2 => B.thick_covered t (hT.trans ht) p r hr h1 h2
  static_patches := fun i t ht x hx => by
    obtain ⟨p⟩ := B.static_patches i t (hT.trans ht) x hx
    exact ⟨{
      n := p.n, first := p.first, last := p.last, ordered := p.ordered, a := p.a, b := p.b
      a_nonneg := p.a_nonneg, before := p.before, after := p.after, horizon := p.horizon
      neighborhood := p.neighborhood, mem_neighborhood := p.mem_neighborhood
      in_domain := fun s hs hTs => p.in_domain s hs (hT.trans hTs)
      stages := p.stages
      map := p.map
      smooth := p.smooth
      agrees := fun s hs hTs y hy => p.agrees s hs (hT.trans hTs) y hy
      speed := fun s hs hTs y hy => p.speed s hs (hT.trans hTs) y hy }⟩

/-- Restart buffered cores at a later time `T ≥ start`. -/
def BufferedPersistentCores.restart_S30 (B : BufferedPersistentCores F K) (T : ℝ)
    (hT : B.start ≤ T) : BufferedPersistentCores F K where
  toPersistentHyperbolicCores := restartCores_S30 B.toPersistentHyperbolicCores T hT
  buffer_domain := fun i t ht => B.buffer_domain i t (hT.trans ht)
  buffer_error := fun i t ht => B.buffer_error i t (hT.trans ht)

section simp
variable (B : BufferedPersistentCores F K) (T : ℝ) (hT : B.start ≤ T)

@[simp] theorem BufferedPersistentCores.restart_start_S30 :
    (B.restart_S30 T hT).start = T := rfl
@[simp] theorem BufferedPersistentCores.restart_count_S30 :
    (B.restart_S30 T hT).count = B.count := rfl
@[simp] theorem BufferedPersistentCores.restart_accuracy_S30 :
    (B.restart_S30 T hT).accuracy = B.accuracy := rfl
@[simp] theorem BufferedPersistentCores.restart_model_S30 (i : Fin B.count) :
    (B.restart_S30 T hT).model i = B.model i := rfl
@[simp] theorem BufferedPersistentCores.restart_domain_S30 (i : Fin B.count) :
    (B.restart_S30 T hT).domain i = B.domain i := rfl

theorem BufferedPersistentCores.restart_map_S30 (i : Fin B.count) (t : ℝ) (ht : T ≤ t) :
    (B.restart_S30 T hT).map i t ht = B.map i t (hT.trans ht) := rfl

theorem BufferedPersistentCores.restart_image_S30 (i : Fin B.count) (t : ℝ) (ht : T ≤ t)
    (S : Set (B.model i).Carrier) :
    (B.restart_S30 T hT).map i t ht '' S = B.map i t (hT.trans ht) '' S := rfl

end simp

end GC.LongTime.Ch12
