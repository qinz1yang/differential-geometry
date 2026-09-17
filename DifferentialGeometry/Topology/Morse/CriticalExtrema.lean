import DifferentialGeometry.Topology.Morse.Defs
import DifferentialGeometry.Topology.Manifold.LocalExtrema
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Set.Card

open Set
open scoped Manifold Topology

namespace DifferentialGeometry.Topology.Morse

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H}

theorem isCriticalPointAt_of_isLocalMin {f : M → ℝ} {x : M}
    (hmin : IsLocalMin f x) (hx : I.IsInteriorPoint x) : IsCriticalPointAt I f x := by
  ext v
  exact congrArg (fun A : E →L[ℝ] ℝ => A v) (hmin.mvfderiv_eq_zero hx)

theorem isCriticalPointAt_of_isLocalMax {f : M → ℝ} {x : M}
    (hmax : IsLocalMax f x) (hx : I.IsInteriorPoint x) : IsCriticalPointAt I f x := by
  ext v
  exact congrArg (fun A : E →L[ℝ] ℝ => A v) (hmax.mvfderiv_eq_zero hx)

variable [BoundarylessManifold I M]

theorem eq_of_isMin_of_injOn_criticalPoints {f : M → ℝ}
    (hinj : InjOn f {x | IsCriticalPointAt I f x}) {x y : M}
    (hx : ∀ z, f x ≤ f z) (hy : ∀ z, f y ≤ f z) : x = y := by
  have hc (p : M) (hp : ∀ z, f p ≤ f z) : IsCriticalPointAt I f p :=
    isCriticalPointAt_of_isLocalMin (Filter.Eventually.of_forall hp)
      BoundarylessManifold.isInteriorPoint
  exact hinj (hc x hx) (hc y hy) (le_antisymm (hx y) (hy x))

theorem eq_of_isMax_of_injOn_criticalPoints {f : M → ℝ}
    (hinj : InjOn f {x | IsCriticalPointAt I f x}) {x y : M}
    (hx : ∀ z, f z ≤ f x) (hy : ∀ z, f z ≤ f y) : x = y := by
  have hc (p : M) (hp : ∀ z, f z ≤ f p) : IsCriticalPointAt I f p :=
    isCriticalPointAt_of_isLocalMax (Filter.Eventually.of_forall hp)
      BoundarylessManifold.isInteriorPoint
  exact hinj (hc x hx) (hc y hy) (le_antisymm (hy x) (hx y))

theorem exists_unique_min_max_of_injOn_criticalPoints [CompactSpace M] [Nonempty M]
    {f : M → ℝ} (hf : Continuous f)
    (hinj : InjOn f {x | IsCriticalPointAt I f x}) :
    ∃ p q : M, (∀ x, f p ≤ f x ∧ f x ≤ f q) ∧
      (∀ x, f x = f p ↔ x = p) ∧ (∀ x, f x = f q ↔ x = q) ∧
      IsCriticalPointAt I f p ∧ IsCriticalPointAt I f q := by
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuousOn
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
  have hp' := fun x => hp (mem_univ x)
  have hq' := fun x => hq (mem_univ x)
  refine ⟨p, q, fun x => ⟨hp' x, hq' x⟩, ?_, ?_,
    isCriticalPointAt_of_isLocalMin (Filter.Eventually.of_forall hp')
      BoundarylessManifold.isInteriorPoint,
    isCriticalPointAt_of_isLocalMax (Filter.Eventually.of_forall hq')
      BoundarylessManifold.isInteriorPoint⟩
  · intro x
    refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
    exact eq_of_isMin_of_injOn_criticalPoints hinj (fun z => h ▸ hp' z) hp'
  · intro x
    refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
    exact eq_of_isMax_of_injOn_criticalPoints hinj (fun z => h ▸ hq' z) hq'

theorem injOn_criticalPoints_of_ncard_eq_two [CompactSpace M] [Infinite M]
    {f : M → ℝ} (hf : Continuous f)
    (hcard : {x | IsCriticalPointAt I f x}.ncard = 2) :
    InjOn f {x | IsCriticalPointAt I f x} := by
  obtain ⟨u, v, huv, hset⟩ := ncard_eq_two.mp hcard
  let : Nonempty M := ⟨u⟩
  have hfinite : {x | IsCriticalPointAt I f x}.Finite := hset.symm ▸ toFinite {u, v}
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hf.continuousOn
  obtain ⟨q, _, hq⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
  have hp' := fun x => hp (mem_univ x)
  have hq' := fun x => hq (mem_univ x)
  have hpc : IsCriticalPointAt I f p :=
    isCriticalPointAt_of_isLocalMin (Filter.Eventually.of_forall hp')
      BoundarylessManifold.isInteriorPoint
  have hqc : IsCriticalPointAt I f q :=
    isCriticalPointAt_of_isLocalMax (Filter.Eventually.of_forall hq')
      BoundarylessManifold.isInteriorPoint
  have hlt : f p < f q := by
    apply lt_of_le_of_ne (hp' q)
    intro heq
    have hc : {x | IsCriticalPointAt I f x} = univ := by
      apply eq_univ_of_forall
      intro x
      apply isCriticalPointAt_of_isLocalMin _ BoundarylessManifold.isInteriorPoint
      apply Filter.Eventually.of_forall
      intro y
      exact (hq' x).trans (heq.symm.le.trans (hp' y))
    rw [hc] at hfinite
    exact Set.infinite_univ hfinite
  have hpq : p ≠ q := fun h => hlt.ne (congrArg f h)
  have hsub : ({p, q} : Set M) ⊆ {x | IsCriticalPointAt I f x} := by
    rintro x (rfl | rfl)
    · exact hpc
    · exact hqc
  have heq : ({p, q} : Set M) = {x | IsCriticalPointAt I f x} :=
    eq_of_subset_of_ncard_le hsub (by rw [hcard, ncard_pair hpq]) hfinite
  rw [← heq]
  rintro x (rfl | rfl) y (rfl | rfl) hxy
  · rfl
  · exact (hlt.ne hxy).elim
  · exact (hlt.ne' hxy).elim
  · rfl


theorem exists_min_max_of_ncard_criticalPoints_eq_two [CompactSpace M]
    {f : M → ℝ} (hf : Continuous f)
    (hinj : InjOn f {x | IsCriticalPointAt I f x})
    (hcard : {x | IsCriticalPointAt I f x}.ncard = 2) :
    ∃ p q : M, f p < f q ∧ {x | IsCriticalPointAt I f x} = {p, q} ∧
      (∀ x, f p ≤ f x ∧ f x ≤ f q) ∧
      (∀ x, f x = f p ↔ x = p) ∧ (∀ x, f x = f q ↔ x = q) := by
  obtain ⟨u, v, huv, hset⟩ := ncard_eq_two.mp hcard
  let : Nonempty M := ⟨u⟩
  obtain ⟨p, q, hb, hp, hq, hpc, hqc⟩ := exists_unique_min_max_of_injOn_criticalPoints hf hinj
  have hu : u ∈ {x | IsCriticalPointAt I f x} := by rw [hset]; exact mem_insert u {v}
  have hv : v ∈ {x | IsCriticalPointAt I f x} := by
    rw [hset]
    exact mem_insert_of_mem u (mem_singleton v)
  have hlt : f p < f q := by
    apply lt_of_le_of_ne (hb q).1
    intro heq
    have he (x : M) : f x = f p := le_antisymm ((hb x).2.trans_eq heq.symm) (hb x).1
    exact huv (hinj hu hv ((he u).trans (he v).symm))
  have hpq : p ≠ q := fun h => hlt.ne (congrArg f h)
  have hsub : ({p, q} : Set M) ⊆ {x | IsCriticalPointAt I f x} := by
    intro x hx
    rcases hx with rfl | rfl
    · exact hpc
    · exact hqc
  have hfinite : {x | IsCriticalPointAt I f x}.Finite := hset.symm ▸ toFinite {u, v}
  have heq : ({p, q} : Set M) = {x | IsCriticalPointAt I f x} :=
    eq_of_subset_of_ncard_le hsub (by rw [hcard, ncard_pair hpq]) hfinite
  exact ⟨p, q, hlt, heq.symm, hb, hp, hq⟩

end DifferentialGeometry.Topology.Morse
