import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Order.Compact

namespace DifferentialGeometry.Topology.Engulfing

open Set Filter _root_.Topology

variable {X : Type*} [TopologicalSpace X]

noncomputable def lowerEnvelope (f : X → ℝ) (x : X) : ℝ := liminf f (𝓝 x)

theorem lowerEnvelope_le {f : X → ℝ} (hbelow : BddBelow (range f)) (x : X) :
    lowerEnvelope f x ≤ f x :=
  liminf_le_of_le hbelow.isBoundedUnder_of_range
    (fun a hb => show x ∈ {y | a ≤ f y} from mem_of_mem_nhds hb)

theorem lowerSemicontinuous_lowerEnvelope {f : X → ℝ}
    (hbelow : BddBelow (range f)) (habove : BddAbove (range f)) :
    LowerSemicontinuous (lowerEnvelope f) := by
  intro x a ha
  obtain ⟨b, hab, hbx⟩ := exists_between ha
  have hb : ∀ᶠ y in 𝓝 x, b < f y :=
    eventually_lt_of_lt_liminf hbx hbelow.isBoundedUnder_of_range
  filter_upwards [eventually_eventually_nhds.mpr hb] with y hy
  apply hab.trans_le
  exact le_liminf_of_le habove.isBoundedUnder_of_range.isCobounded_flip
    (hy.mono fun _ h => h.le)

theorem lowerEnvelope_eq_of_continuousAt {f : X → ℝ} {x : X} (hf : ContinuousAt f x) :
    lowerEnvelope f x = f x := hf.liminf_eq

theorem lowerEnvelope_eq_of_continuous {f : X → ℝ} (hf : Continuous f) : lowerEnvelope f = f :=
  funext (fun x => lowerEnvelope_eq_of_continuousAt (hf.continuousAt (x := x)))

theorem le_lowerEnvelope_of_lowerSemicontinuous {f g : X → ℝ}
    (habove : BddAbove (range f)) (hg : LowerSemicontinuous g) (hgf : ∀ x, g x ≤ f x) :
    ∀ x, g x ≤ lowerEnvelope f x := by
  intro x
  apply le_of_forall_lt
  intro a ha
  obtain ⟨b, hab, hbx⟩ := exists_between ha
  exact hab.trans_le (le_liminf_of_le habove.isBoundedUnder_of_range.isCobounded_flip
    ((hg x b hbx).mono fun y hy => hy.le.trans (hgf y)))

theorem lowerEnvelope_eq_of_lowerSemicontinuous {f : X → ℝ}
    (hbelow : BddBelow (range f)) (habove : BddAbove (range f))
    (hf : LowerSemicontinuous f) : lowerEnvelope f = f := by
  funext x
  exact le_antisymm (lowerEnvelope_le hbelow x)
    (le_lowerEnvelope_of_lowerSemicontinuous habove hf (fun _ => le_rfl) x)

def verticalHull (f : X → ℝ) : Set (X × ℝ) :=
  {p | lowerEnvelope f p.1 ≤ p.2 ∧ p.2 ≤ f p.1}

@[simp]
theorem mem_verticalHull {f : X → ℝ} {x : X} {t : ℝ} :
    (x, t) ∈ verticalHull f ↔ t ∈ Icc (lowerEnvelope f x) (f x) := Iff.rfl

theorem isClosed_verticalHull {f : X → ℝ} (hf : UpperSemicontinuous f)
    (hbelow : BddBelow (range f)) (habove : BddAbove (range f)) :
    IsClosed (verticalHull f) :=
  (lowerSemicontinuous_lowerEnvelope hbelow habove).isClosed_epigraph.inter hf.IsClosed_hypograph

theorem graph_subset_verticalHull {f : X → ℝ} (hbelow : BddBelow (range f)) :
    {p : X × ℝ | p.2 = f p.1} ⊆ verticalHull f := by
  intro p hp
  exact ⟨hp ▸ lowerEnvelope_le hbelow p.1, hp.le⟩

theorem bddBelow_range_lowerEnvelope {f : X → ℝ}
    (hbelow : BddBelow (range f)) (habove : BddAbove (range f)) :
    BddBelow (range (lowerEnvelope f)) := by
  obtain ⟨a, ha⟩ := hbelow
  refine ⟨a, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact le_liminf_of_le habove.isBoundedUnder_of_range.isCobounded_flip
    (Eventually.of_forall (fun y => ha (mem_range_self y)))

theorem isCompact_verticalHullBetween [CompactSpace X] {l g : X → ℝ}
    (hl : LowerSemicontinuous l) (hg : UpperSemicontinuous g)
    (hlower : BddBelow (range l)) (hupper : BddAbove (range g)) :
    IsCompact {p : X × ℝ | l p.1 ≤ p.2 ∧ p.2 ≤ g p.1} := by
  obtain ⟨a, ha⟩ := hlower
  obtain ⟨b, hb⟩ := hupper
  apply (isCompact_univ.prod (isCompact_Icc : IsCompact (Icc a b))).of_isClosed_subset
    (hl.isClosed_epigraph.inter hg.IsClosed_hypograph)
  intro p hp
  exact ⟨mem_univ _, (ha (mem_range_self p.1)).trans hp.1,
    hp.2.trans (hb (mem_range_self p.1))⟩

theorem isCompact_verticalHull [CompactSpace X] {f : X → ℝ}
    (hf : UpperSemicontinuous f) (hbelow : BddBelow (range f)) (habove : BddAbove (range f)) :
    IsCompact (verticalHull f) :=
  isCompact_verticalHullBetween (lowerSemicontinuous_lowerEnvelope hbelow habove) hf
    (bddBelow_range_lowerEnvelope hbelow habove) habove

theorem isCompact_lowerEnvelope_hull [CompactSpace X] {f g : X → ℝ}
    (hbelow : BddBelow (range f)) (habove : BddAbove (range f))
    (hg : UpperSemicontinuous g) (hgabove : BddAbove (range g)) :
    IsCompact {p : X × ℝ | lowerEnvelope f p.1 ≤ p.2 ∧ p.2 ≤ g p.1} :=
  isCompact_verticalHullBetween (lowerSemicontinuous_lowerEnvelope hbelow habove) hg
    (bddBelow_range_lowerEnvelope hbelow habove) hgabove

end DifferentialGeometry.Topology.Engulfing
