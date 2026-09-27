import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.LifetimeInterval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Metric
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Curvature.Metric.Defs

set_option autoImplicit false
noncomputable section
open Set Manifold DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

structure PartialStandardSolution where
  lifetime : ℝ≥0∞
  lifetime_pos : 0 < lifetime
  metric : ℝ → SmoothRiemannianMetric (𝓡 3) E3
  smooth : ContDiffOn ℝ ∞ (F := E3 →L[ℝ] E3 →L[ℝ] ℝ)
    (fun p : ℝ × E3 => by exact (metric p.1).inner p.2)
    ((lifetimeInterval lifetime lifetime_pos).carrier ×ˢ (univ : Set E3))
  equation : ∀ t ∈ (lifetimeInterval lifetime lifetime_pos).carrier,
    ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s => (metric s).inner x v w)
        (-2 * ricciTensor (metric t) x v w) (Ici 0) t
  initial : metric 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric
  complete : ∀ t ∈ (lifetimeInterval lifetime lifetime_pos).carrier,
    RiemannianMetricComplete (metric t)
  curvature_bound : ∀ θ : ℝ, 0 ≤ θ → ENNReal.ofReal θ < lifetime →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Icc 0 θ, ∀ x : E3,
      Real.sqrt (normSq0S (metric t) x 4 (metricRm04 (metric t) x)) ≤ K

namespace PartialStandardSolution

abbrev domain (S : PartialStandardSolution) : Set ℝ :=
  (lifetimeInterval S.lifetime S.lifetime_pos).carrier

def IsExtendedBy (S S' : PartialStandardSolution) : Prop :=
  S.lifetime ≤ S'.lifetime ∧ ∀ t ∈ S.domain, S'.metric t = S.metric t

theorem isExtendedBy_refl (S : PartialStandardSolution) : S.IsExtendedBy S :=
  ⟨le_rfl, fun _ _ => rfl⟩

theorem isExtendedBy_trans {S S' S'' : PartialStandardSolution}
    (h : S.IsExtendedBy S') (h' : S'.IsExtendedBy S'') : S.IsExtendedBy S'' := by
  refine ⟨h.1.trans h'.1, ?_⟩
  intro t ht
  exact (h'.2 t (lifetimeInterval_carrier_mono S.lifetime_pos S'.lifetime_pos h.1 ht)).trans
    (h.2 t ht)

theorem lifetime_eq_and_metric_eq_of_mutual_extension {S S' : PartialStandardSolution}
    (h : S.IsExtendedBy S') (h' : S'.IsExtendedBy S) :
    S.lifetime = S'.lifetime ∧ ∀ t ∈ S.domain, S'.metric t = S.metric t :=
  ⟨le_antisymm h.1 h'.1, h.2⟩

def IsMaximal (S : PartialStandardSolution) : Prop :=
  ∀ S' : PartialStandardSolution, S.IsExtendedBy S' → S'.IsExtendedBy S

theorem isMaximal_iff_no_strict_extension (S : PartialStandardSolution) :
    S.IsMaximal ↔ ¬ ∃ S' : PartialStandardSolution,
      S.IsExtendedBy S' ∧ S.lifetime < S'.lifetime := by
  constructor
  · intro h ⟨S', he, hlt⟩
    exact (not_le_of_gt hlt) (h S' he).1
  · intro h S' he
    have hle : S'.lifetime ≤ S.lifetime := by
      by_contra hn
      exact h ⟨S', he, lt_of_not_ge hn⟩
    refine ⟨hle, ?_⟩
    intro t ht
    exact (he.2 t (lifetimeInterval_carrier_mono S'.lifetime_pos S.lifetime_pos hle ht)).symm

def restrict (S : PartialStandardSolution) (T : ℝ≥0∞) (hT : 0 < T)
    (hTS : T ≤ S.lifetime) : PartialStandardSolution where
  lifetime := T
  lifetime_pos := hT
  metric := S.metric
  smooth := S.smooth.mono (prod_mono
    (lifetimeInterval_carrier_mono hT S.lifetime_pos hTS) Subset.rfl)
  equation := fun t ht => S.equation t
    (lifetimeInterval_carrier_mono hT S.lifetime_pos hTS ht)
  initial := S.initial
  complete := fun t ht => S.complete t
    (lifetimeInterval_carrier_mono hT S.lifetime_pos hTS ht)
  curvature_bound := fun θ hθ hθT => S.curvature_bound θ hθ (hθT.trans_le hTS)

theorem restrict_metric (S : PartialStandardSolution) (T : ℝ≥0∞) (hT : 0 < T)
    (hTS : T ≤ S.lifetime) : (S.restrict T hT hTS).metric = S.metric := rfl

theorem restrict_isExtendedBy (S : PartialStandardSolution) (T : ℝ≥0∞) (hT : 0 < T)
    (hTS : T ≤ S.lifetime) : (S.restrict T hT hTS).IsExtendedBy S :=
  ⟨hTS, fun _ _ => rfl⟩

theorem not_isMaximal_restrict (S : PartialStandardSolution) (T : ℝ≥0∞) (hT : 0 < T)
    (hTS : T < S.lifetime) : ¬ (S.restrict T hT hTS.le).IsMaximal := by
  intro hmax
  exact (not_le_of_gt hTS) (hmax S (S.restrict_isExtendedBy T hT hTS.le)).1

theorem initial_equation (S : PartialStandardSolution) (x : E3)
    (v w : TangentSpace (𝓡 3) x) :
    HasDerivWithinAt (fun t => (S.metric t).inner x v w)
      (-2 * ricciTensor DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x v w) (Ici 0) 0 := by
  have h := S.equation 0 ((mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos 0).mpr
    ⟨le_rfl, by simpa using S.lifetime_pos⟩) x v w
  simpa only [S.initial] using h
end PartialStandardSolution

def StandardSolution := {S : PartialStandardSolution // S.IsMaximal}
end DifferentialGeometry.PDE.RicciFlow
