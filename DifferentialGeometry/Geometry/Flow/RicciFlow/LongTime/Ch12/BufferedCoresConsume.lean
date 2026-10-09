import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BufferedCores
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PortAdapterPersistent

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}

/-- Structural sanity (no flow dependence): `toCores` keeps map, accuracy, start, model. -/
theorem toCores_map_S11 (B : BufferedPersistentCores F K) : B.toCores.map = B.map := rfl
theorem toCores_accuracy_S11 (B : BufferedPersistentCores F K) :
    B.toCores.accuracy = B.accuracy := rfl
theorem toCores_start_S11 (B : BufferedPersistentCores F K) : B.toCores.start = B.start := rfl
theorem toCores_count_S11 (B : BufferedPersistentCores F K) : B.toCores.count = B.count := rfl
theorem toCores_domain_S11 (B : BufferedPersistentCores F K) : B.toCores.domain = B.domain := rfl

/-- The buffer enlarges the advertised ball: the (doubled) ball lies in the domain. -/
theorem advertised_ball_sub_buffer_S11 (B : BufferedPersistentCores F K) (i : Fin B.count) (t : ℝ)
    (ht : B.start ≤ t) :
    riemannianBallOf (B.model i).metric (B.model i).basepoint (B.accuracy t)⁻¹ ⊆
      riemannianBallOf (B.model i).metric (B.model i).basepoint (2 * (B.accuracy t)⁻¹) := by
  refine riemannianBallOf_mono _ _ ?_
  have : 0 < (B.accuracy t)⁻¹ := inv_pos.mpr (B.accuracy_pos t ht)
  linarith

/-- A09 field-table consumption check (CH12-R1 §1.3, `cores` row): a *fixed* truncation and start
time, whose image lies in the advertised ball at the start time, gives a `PersistentCuspExterior`
of `B.toCores`: the identical argument as `persistentExterior_CPE2`, using only
`accuracy_antitone`/`accuracy_pos` of the cores. -/
def persistentExterior_ofBuffered_S11 (B : BufferedPersistentCores F K)
    (trunc : (i : Fin B.toCores.count) → HyperbolicTruncation (B.toCores.model i))
    (t₀ : ℝ) (h₀ : B.start ≤ t₀)
    (hin : ∀ i, range (trunc i).inclusion ⊆
      riemannianBallOf (B.toCores.model i).metric (B.toCores.model i).basepoint
        (B.toCores.accuracy t₀)⁻¹) :
    PersistentCuspExterior B.toCores where
  truncation := trunc
  start := t₀
  after_cores := h₀
  in_ball := by
    intro i t ht
    refine (hin i).trans (riemannianBallOf_mono _ _ ?_)
    have h0 : 0 < B.toCores.accuracy t := B.toCores.accuracy_pos t (h₀.trans ht)
    exact inv_anti₀ h0 (B.toCores.accuracy_antitone h₀ (h₀.trans ht) ht)

/-- The consumer's `LateCutFamily.cores` slot (`PersistentHyperbolicCores F (K + 4)`) is exactly the
type of `toCores` of a buffered family at level `K + 4`; for any `L` filling that slot with
`B.toCores`, `persistentExterior_CPE2` (fix one truncation, later times stay in the advertised
ball) applies unchanged, and the advertised radius is `B`'s own accuracy. -/
theorem cpe2_applies_to_buffered_S11 {slices : ℕ → RegularSlice F.observation}
    (B : BufferedPersistentCores F (K + 4)) (L : GC.LongTime.LateCutFamily F K slices)
    (hL : L.cores = B.toCores) (j : ℕ) (hj : L.first ≤ j) :
    L.cores.accuracy = B.accuracy ∧
    ∀ i t, (slices j).time ≤ t →
      range (L.truncation j i).inclusion ⊆
        riemannianBallOf (L.cores.model i).metric (L.cores.model i).basepoint
          (L.cores.accuracy t)⁻¹ :=
  ⟨by rw [hL]; rfl, fun i t ht => (GC.LongTime.CuspP1.persistentExterior_CPE2 L j hj).in_ball i t ht⟩

end GC.LongTime.Ch12
