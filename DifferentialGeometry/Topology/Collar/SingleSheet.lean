import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# One sheet: local homeomorphisms separated by a height function

A local homeomorphism `p : X → Y` from a compact connected Hausdorff space into a Hausdorff
space is injective as soon as some continuous height `h : X → ℝ` separates the points of each
fibre, i.e. `x ↦ (p x, h x)` is injective. The proof shows that the set of points which are
highest in their fibre is clopen. This is the topological step of the "ordered sheets give one
graph" argument in BCP03 (foundation F-e). A local homeomorphism from a nonempty compact space
onto a connected Hausdorff space is surjective.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Topology

namespace DifferentialGeometry.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The pairs of distinct points with the same image form a closed set when `p` is locally
injective and the target is Hausdorff. -/
theorem isClosed_setOf_eq_ne_of_isLocallyInjective [T2Space Y] {p : X → Y}
    (hpc : Continuous p) (hp : IsLocallyInjective p) :
    IsClosed {q : X × X | p q.1 = p q.2 ∧ q.1 ≠ q.2} := by
  choose U hUo hxU hUi using hp
  let O : Set (X × X) := ⋃ x, U x ×ˢ U x
  have hO : IsOpen O := isOpen_iUnion fun x => (hUo x).prod (hUo x)
  have hR : IsClosed {q : X × X | p q.1 = p q.2} :=
    isClosed_eq (hpc.comp continuous_fst) (hpc.comp continuous_snd)
  have heq : {q : X × X | p q.1 = p q.2 ∧ q.1 ≠ q.2} = {q : X × X | p q.1 = p q.2} ∩ Oᶜ := by
    ext q
    simp only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff, O, mem_iUnion, mem_prod, not_exists,
      not_and]
    constructor
    · rintro ⟨hpq, hne⟩
      exact ⟨hpq, fun x h1 h2 => hne (hUi x h1 h2 hpq)⟩
    · rintro ⟨hpq, hno⟩
      refine ⟨hpq, fun hq => ?_⟩
      have h1 := hxU q.1
      exact hno q.1 h1 (hq ▸ h1)
  rw [heq]
  exact hR.inter hO.isClosed_compl

/-- Points that are strictly below some other point of their fibre form an open set. -/
theorem isOpen_setOf_exists_lt_of_isLocalHomeomorph {p : X → Y} (hp : IsLocalHomeomorph p)
    {h : X → ℝ} (hh : Continuous h) :
    IsOpen {x : X | ∃ y, p y = p x ∧ h x < h y} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨y, hyx, hlt⟩
  obtain ⟨e, hye, rfl⟩ := hp y
  have hxt : e x ∈ e.target := hyx ▸ e.map_source hye
  have hcont : ContinuousAt (fun x' => h (e.symm (e x'))) x :=
    hh.continuousAt.comp ((e.continuousAt_symm hxt).comp hp.continuous.continuousAt)
  have hval : h (e.symm (e x)) = h y := by rw [← hyx, e.left_inv hye]
  have hev1 : ∀ᶠ x' in 𝓝 x, h x' < h (e.symm (e x')) :=
    (hh.continuousAt).eventually_lt hcont (hval ▸ hlt)
  have hev2 : ∀ᶠ x' in 𝓝 x, e x' ∈ e.target :=
    hp.continuous.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds hxt)
  filter_upwards [hev1, hev2] with x' h1 h2
  exact ⟨e.symm (e x'), e.right_inv h2, h1⟩

/-- E1 (BCP03, one graph): a local homeomorphism from a compact connected Hausdorff space whose
fibres are separated by a continuous height is injective. -/
theorem injective_of_isLocalHomeomorph_of_injective_height
    [CompactSpace X] [T2Space X] [PreconnectedSpace X] [T2Space Y] {p : X → Y}
    (hp : IsLocalHomeomorph p) {h : X → ℝ} (hh : Continuous h)
    (hinj : Injective fun x => (p x, h x)) : Injective p := by
  let S : Set X := {x | ∀ y, p y = p x → h y ≤ h x}
  have hScompl : Sᶜ = {x : X | ∃ y, p y = p x ∧ h x < h y} := by
    ext x
    simp only [S, mem_compl_iff, mem_ofPred_eq, not_forall, not_le, exists_prop]
  -- the complement is the first projection of a compact set
  let A : Set (X × X) := {q | p q.1 = p q.2 ∧ q.1 ≠ q.2} ∩ {q | h q.1 ≤ h q.2}
  have hA : IsClosed A :=
    (isClosed_setOf_eq_ne_of_isLocallyInjective hp.continuous hp.isLocallyInjective).inter
      (isClosed_le (hh.comp continuous_fst) (hh.comp continuous_snd))
  have hfst : Prod.fst '' A = {x : X | ∃ y, p y = p x ∧ h x < h y} := by
    ext x
    simp only [A, mem_image, mem_inter_iff, mem_ofPred_eq, Prod.exists, exists_and_right,
      exists_eq_right]
    constructor
    · rintro ⟨y, ⟨hpxy, hne⟩, hle⟩
      refine ⟨y, hpxy.symm, lt_of_le_of_ne hle fun hhe => hne (hinj ?_)⟩
      simp only [hpxy, hhe]
    · rintro ⟨y, hpyx, hlt⟩
      exact ⟨y, ⟨hpyx.symm, fun hxy => hlt.ne (hxy ▸ rfl)⟩, hlt.le⟩
  have hSclosed : IsClosed Sᶜ := by
    rw [hScompl, ← hfst]
    exact (hA.isCompact.image continuous_fst).isClosed
  have hSopen : IsOpen Sᶜ := by
    rw [hScompl]
    exact isOpen_setOf_exists_lt_of_isLocalHomeomorph hp hh
  intro x y hxy
  -- `S` is nonempty: a highest point of the compact fibre through `x`
  have hfib : IsCompact {z : X | p z = p x} :=
    (isClosed_eq hp.continuous continuous_const).isCompact
  obtain ⟨z, hzf, hzmax⟩ := hfib.exists_isMaxOn ⟨x, rfl⟩ hh.continuousOn
  have hzS : z ∈ S := by
    intro w hw
    exact hzmax (show p w = p x from hw.trans hzf)
  have hSuniv : S = univ := by
    have hcl : IsClopen S := ⟨isOpen_compl_iff.mp hSopen, isClosed_compl_iff.mp hSclosed⟩
    exact hcl.eq_univ ⟨z, hzS⟩
  have hxS : x ∈ S := hSuniv ▸ mem_univ x
  have hyS : y ∈ S := hSuniv ▸ mem_univ y
  have hle1 : h y ≤ h x := hxS y hxy.symm
  have hle2 : h x ≤ h y := hyS x hxy
  apply hinj
  simp only [hxy, le_antisymm hle2 hle1]

/-- A local homeomorphism from a nonempty compact space to a connected Hausdorff space is
surjective. -/
theorem surjective_of_isLocalHomeomorph_of_compactSpace
    [CompactSpace X] [Nonempty X] [T2Space Y] [PreconnectedSpace Y] {p : X → Y}
    (hp : IsLocalHomeomorph p) : Surjective p := by
  have hcl : IsClopen (range p) :=
    ⟨(isCompact_range hp.continuous).isClosed, hp.isOpenMap.isOpen_range⟩
  have huniv := hcl.eq_univ (range_nonempty p)
  exact eq_univ_iff_forall.mp huniv

/-- A compact connected local homeomorphism with fibres separated by a height is a
homeomorphism onto a connected Hausdorff target. -/
theorem bijective_of_isLocalHomeomorph_of_injective_height
    [CompactSpace X] [T2Space X] [PreconnectedSpace X] [Nonempty X] [T2Space Y]
    [PreconnectedSpace Y] {p : X → Y} (hp : IsLocalHomeomorph p) {h : X → ℝ}
    (hh : Continuous h) (hinj : Injective fun x => (p x, h x)) : Bijective p :=
  ⟨injective_of_isLocalHomeomorph_of_injective_height hp hh hinj,
    surjective_of_isLocalHomeomorph_of_compactSpace hp⟩

end DifferentialGeometry.Topology
