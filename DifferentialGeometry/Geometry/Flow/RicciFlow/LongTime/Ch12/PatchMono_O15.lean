import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PersistentHyperbolicCores

set_option autoImplicit false

/-!
# Monotonicity of persistent model patches (CH12-O15 G3)

H5 (sheet-H3H5 §2) assembles finitely many single-model persistent families with one common
start time `T' = max Tᵢ` and one common accuracy `α' = max αᵢ`.  A static patch for the old data
remains a patch for the later start, the weaker accuracy and a larger domain.
-/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold GC.LongTime
open scoped Manifold ContDiff

universe u

namespace GC.LongTime.Ch12

theorem persistentModelPatch_mono_O15 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {H : FiniteVolumeHyperbolicModel.{u}} {T T' : ℝ}
    {α α' : ℝ → ℝ} {domain domain' : ℝ → TopologicalSpace.Opens H.Carrier}
    {f : (t : ℝ) → T ≤ t → H.Carrier → (postStage F.observation t).Carrier} {t₀ : ℝ}
    {x₀ : H.Carrier}
    (hp : Nonempty (PersistentModelPatch F H T α domain f t₀ x₀)) (hT : T ≤ T')
    (hα0 : ∀ t, T' ≤ t → 0 ≤ α t) (hα : ∀ t, T' ≤ t → α t ≤ α' t)
    (hdom : ∀ t, T' ≤ t → domain t ≤ domain' t) :
    Nonempty (PersistentModelPatch F H T' α' domain' (fun t ht => f t (hT.trans ht)) t₀ x₀) := by
  obtain ⟨p⟩ := hp
  refine ⟨{
    n := p.n, first := p.first, last := p.last, ordered := p.ordered, a := p.a, b := p.b
    a_nonneg := p.a_nonneg, before := p.before, after := p.after, horizon := p.horizon
    neighborhood := p.neighborhood, mem_neighborhood := p.mem_neighborhood
    in_domain := fun s hs hTs => (p.in_domain s hs (hT.trans hTs)).trans (hdom s hTs)
    stages := p.stages
    map := p.map
    smooth := p.smooth
    agrees := fun s hs hTs y hy => p.agrees s hs (hT.trans hTs) y hy
    speed := fun s hs hTs y hy => ?_ }⟩
  refine (p.speed s hs (hT.trans hTs) y hy).trans_le ?_
  have h0 : (0 : ℝ) ≤ (s : ℝ) := s.2.1
  have hsq : α s ^ 2 ≤ α' s ^ 2 :=
    pow_le_pow_left₀ (hα0 s hTs) (hα s hTs) 2
  exact div_le_div_of_nonneg_right hsq h0

end GC.LongTime.Ch12
