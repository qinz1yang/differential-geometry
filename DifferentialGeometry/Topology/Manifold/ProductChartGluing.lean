import DifferentialGeometry.Topology.Diffeomorph.FiberwiseAffine
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphRange
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {N M : Type*}

def productChartMap (P : ℕ → N × ℝ → M) (z : N × ℝ) : M :=
  P ⌊z.2⌋₊ (z.1, z.2 - (⌊z.2⌋₊ : ℝ))

theorem productChartMap_eq_on_closed_strip
    (P : ℕ → N × ℝ → M) (hseam : ∀ n p, P (n + 1) (p, 0) = P n (p, 1))
    (n : ℕ) (p : N) (t : ℝ) (ht : t ∈ Icc (n : ℝ) ((n : ℝ) + 1)) :
    productChartMap P (p, t) = P n (p, t - n) := by
  by_cases hlt : t < (n : ℝ) + 1
  · have hfloor : ⌊t⌋₊ = n := Nat.floor_eq_on_Ico n t ⟨ht.1, hlt⟩
    simp only [productChartMap, hfloor]
  · have heq : t = (n : ℝ) + 1 := le_antisymm ht.2 (le_of_not_gt hlt)
    have hfloor : ⌊t⌋₊ = n + 1 := by rw [heq, ← Nat.cast_add_one, Nat.floor_natCast]
    simp only [productChartMap, hfloor]
    rw [heq, Nat.cast_add_one, sub_self, hseam]
    congr 1
    congr 1
    ring

theorem productChartMap_eventuallyEq_chart
    [TopologicalSpace N]
    (P : ℕ → N × ℝ → M)
    (hseam : ∀ n, ∃ V : Set (N × ℝ), IsOpen V ∧ univ ×ˢ ({0} : Set ℝ) ⊆ V ∧
      ∀ z ∈ V, P (n + 1) z = P n (z.1, z.2 + 1))
    (z : N × ℝ) (hz : 0 < z.2) :
    ∃ n : ℕ, z.2 - n ∈ Icc (0 : ℝ) 1 ∧
      productChartMap P =ᶠ[𝓝 z] (fun w => P n (w.1, w.2 - n)) := by
  let n := ⌊z.2⌋₊
  have hlo : (n : ℝ) ≤ z.2 := Nat.floor_le hz.le
  have hhi : z.2 < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmem : z.2 - n ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  refine ⟨n, hmem, ?_⟩
  by_cases hstrict : (n : ℝ) < z.2
  · have hnear : ∀ᶠ w : N × ℝ in 𝓝 z, w.2 ∈ Ioo (n : ℝ) ((n : ℝ) + 1) :=
      continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ⟨hstrict, hhi⟩)
    filter_upwards [hnear] with w hw
    have hfloor := Nat.floor_eq_on_Ico n w.2 ⟨hw.1.le, hw.2⟩
    simp only [productChartMap, hfloor]
  · have heq : z.2 = (n : ℝ) := le_antisymm (le_of_not_gt hstrict) hlo
    have hn0 : n ≠ 0 := by intro hn; rw [heq, hn, Nat.cast_zero] at hz; exact lt_irrefl _ hz
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have hzEq : z.2 = (k : ℝ) + 1 := by rw [heq, hk, Nat.cast_succ]
    obtain ⟨V, hVo, hVzero, hcompat⟩ := hseam k
    let shift : N × ℝ → N × ℝ := fun w => (w.1, w.2 - n)
    have hshift : Continuous shift := continuous_fst.prodMk (continuous_snd.sub continuous_const)
    have hzV : shift z ∈ V := by
      have hh : shift z = (z.1, 0) := by dsimp only [shift]; rw [heq, sub_self]
      rw [hh]
      exact hVzero ⟨mem_univ _, rfl⟩
    have hnearV : ∀ᶠ w : N × ℝ in 𝓝 z, shift w ∈ V :=
      hshift.continuousAt.preimage_mem_nhds (hVo.mem_nhds hzV)
    have hnearI : ∀ᶠ w : N × ℝ in 𝓝 z, w.2 ∈ Ioo (k : ℝ) ((k : ℝ) + 2) :=
      continuous_snd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by
        rw [hzEq]; constructor <;> linarith))
    filter_upwards [hnearV, hnearI] with w hwV hwI
    by_cases hw : w.2 < (k : ℝ) + 1
    · have hfloor := Nat.floor_eq_on_Ico k w.2 ⟨hwI.1.le, hw⟩
      simp only [productChartMap, hfloor]
      have hh := hcompat (shift w) hwV
      have hs : (shift w).1 = w.1 := rfl
      have ht : (shift w).2 + 1 = w.2 - k := by dsimp only [shift]; rw [hk, Nat.cast_succ]; ring
      rw [hs, ht] at hh
      simpa only [shift, hk, Nat.succ_eq_add_one] using hh.symm
    · have hfloor : ⌊w.2⌋₊ = n := by
        apply Nat.floor_eq_on_Ico n
        rw [hk, Nat.cast_succ]
        exact ⟨le_of_not_gt hw, by linarith [hwI.2]⟩
      simp only [productChartMap, hfloor]

end DifferentialGeometry.Topology.Manifold

end

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E H N F G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace M] [ChartedSpace G M]

theorem isLocalDiffeomorphAt_of_eventuallyEq_partialDiffeomorph
    (Q : PartialDiffeomorph I J N M ∞) {f : N → M} {x : N}
    (hx : x ∈ Q.source) (heq : f =ᶠ[𝓝 x] Q) :
    IsLocalDiffeomorphAt I J ∞ f x := by
  obtain ⟨U, hU, hUopen, hxU⟩ := eventually_nhds_iff.mp heq
  let P := DifferentialGeometry.Topology.PartialDiffeomorph.restrict Q U hUopen
  refine ⟨P, ⟨hx, hxU⟩, ?_⟩
  intro y hy
  exact hU y hy.2

theorem productChartMap_isLocalDiffeomorphOn
    (P : ℕ → PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M ∞)
    (hsource : ∀ n, (univ ×ˢ Icc (0 : ℝ) 1 : Set (N × ℝ)) ⊆ (P n).source)
    (hseam : ∀ n, ∃ V : Set (N × ℝ), IsOpen V ∧ univ ×ˢ ({0} : Set ℝ) ⊆ V ∧
      ∀ z ∈ V, P (n + 1) z = P n (z.1, z.2 + 1)) :
    IsLocalDiffeomorphOn (I.prod 𝓘(ℝ)) J ∞
      (productChartMap (fun n => P n)) (univ ×ˢ Ioi (0 : ℝ)) := by
  intro z
  have hz := z.property
  obtain ⟨n, hn, heq⟩ := productChartMap_eventuallyEq_chart (fun n => P n) hseam (z : N × ℝ) hz.2
  let shift : Diffeomorph (I.prod 𝓘(ℝ)) (I.prod 𝓘(ℝ)) (N × ℝ) (N × ℝ) ∞ :=
    Diffeomorph.fiberwiseAffine (fun _ => -(n : ℝ)) (fun _ => (1 : ℝ))
      contMDiff_const contMDiff_const (fun _ => one_ne_zero)
  have hshift (w : N × ℝ) : shift w = (w.1, w.2 - n) := by
    change (w.1, -(n : ℝ) + 1 * w.2) = _
    simp only [one_mul, sub_eq_add_neg, add_comm]
  let Q := shift.toPartialDiffeomorph.trans (P n)
  have hQ (w : N × ℝ) : Q w = P n (w.1, w.2 - n) := by
    change P n (shift w) = _
    rw [hshift]
  apply isLocalDiffeomorphAt_of_eventuallyEq_partialDiffeomorph Q
  · change (z : N × ℝ) ∈ (univ : Set (N × ℝ)) ∧ shift z ∈ (P n).source
    rw [hshift]
    exact ⟨mem_univ _, hsource n ⟨mem_univ _, hn⟩⟩
  · exact heq.trans (Eventually.of_forall fun w => (hQ w).symm)

end DifferentialGeometry.Topology.Manifold

end

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E H N F G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace M] [ChartedSpace G M]

theorem productChartMap_injOn
    (P : ℕ → PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M ∞)
    (hsource : ∀ n, (univ ×ˢ Icc (0 : ℝ) 1 : Set (N × ℝ)) ⊆ (P n).source)
    (hadjacent : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
      P (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1) = P n '' (univ ×ˢ ({1} : Set ℝ)))
    (hseparated : ∀ m n : ℕ, m + 1 < n →
      Disjoint (P m '' (univ ×ˢ Icc (0 : ℝ) 1)) (P n '' (univ ×ˢ Icc (0 : ℝ) 1))) :
    InjOn (productChartMap (fun n => P n)) (univ ×ˢ Ici (0 : ℝ)) := by
  have hnorm (z : N × ℝ) (hz : 0 ≤ z.2) :
      z.2 - (⌊z.2⌋₊ : ℝ) ∈ Ico (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (Nat.floor_le hz), by linarith [Nat.lt_floor_add_one z.2]⟩
  have ordered (z w : N × ℝ) (hz : 0 ≤ z.2) (hw : 0 ≤ w.2)
      (hij : ⌊z.2⌋₊ ≤ ⌊w.2⌋₊)
      (heq : productChartMap (fun n => P n) z = productChartMap (fun n => P n) w) :
      z = w := by
    let i := ⌊z.2⌋₊
    let j := ⌊w.2⌋₊
    let zv : N × ℝ := (z.1, z.2 - i)
    let wv : N × ℝ := (w.1, w.2 - j)
    have hzmem : zv ∈ univ ×ˢ Icc (0 : ℝ) 1 := ⟨mem_univ _, (hnorm z hz).1, (hnorm z hz).2.le⟩
    have hwmem : wv ∈ univ ×ˢ Icc (0 : ℝ) 1 := ⟨mem_univ _, (hnorm w hw).1, (hnorm w hw).2.le⟩
    change P i zv = P j wv at heq
    by_cases hsame : i = j
    · have hphase : zv = wv := (P i).injOn (hsource i hzmem)
        (by rw [hsame]; exact hsource j hwmem) (by rw [hsame] at heq ⊢; exact heq)
      have hfst := congrArg Prod.fst hphase
      have hsnd := congrArg Prod.snd hphase
      refine Prod.ext (show z.1 = w.1 from hfst) ?_
      change z.2 - (i : ℝ) = w.2 - (j : ℝ) at hsnd
      rw [hsame] at hsnd
      linarith
    · have hij' : i < j := lt_of_le_of_ne hij hsame
      by_cases hnext : j = i + 1
      · have hinter : P i zv ∈ P i '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
            P (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1) := by
          refine ⟨mem_image_of_mem _ hzmem, ?_⟩
          rw [heq, ← hnext]
          exact mem_image_of_mem _ hwmem
        rw [hadjacent] at hinter
        obtain ⟨v, hv, hveq⟩ := hinter
        have hvsrc := hsource i (show v ∈ univ ×ˢ Icc (0 : ℝ) 1 from
          ⟨hv.1, by rw [hv.2]; exact ⟨zero_le_one, le_rfl⟩⟩)
        have hph := (P i).injOn (hsource i hzmem) hvsrc hveq.symm
        have hh := congrArg Prod.snd hph
        have hh' : z.2 - (i : ℝ) = 1 := hh.trans hv.2
        exact False.elim ((ne_of_lt (hnorm z hz).2) hh')
      · have hfar : i + 1 < j := by omega
        have hm : P i zv ∈ P i '' (univ ×ˢ Icc (0 : ℝ) 1) := mem_image_of_mem _ hzmem
        have hn : P i zv ∈ P j '' (univ ×ˢ Icc (0 : ℝ) 1) := by rw [heq]; exact mem_image_of_mem _ hwmem
        exact False.elim (disjoint_left.mp (hseparated i j hfar) hm hn)
  intro z hz w hw heq
  rcases le_total ⌊z.2⌋₊ ⌊w.2⌋₊ with hij | hji
  · exact ordered z w hz.2 hw.2 hij heq
  · exact (ordered w z hw.2 hz.2 hji heq.symm).symm

theorem productChartMap_image_positive
    (P : ℕ → PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M ∞)
    (hseam : ∀ n p, P (n + 1) (p, 0) = P n (p, 1))
    (hinj : InjOn (productChartMap (fun n => P n)) (univ ×ˢ Ici (0 : ℝ))) :
    productChartMap (fun n => P n) '' (univ ×ˢ Ioi (0 : ℝ)) =
      (⋃ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1)) \
        (P 0 '' (univ ×ˢ ({0} : Set ℝ))) := by
  let f := productChartMap (fun n => P n)
  have hclosed (n : ℕ) (p : N) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      f (p, (n : ℝ) + t) = P n (p, t) := by
    have hh := productChartMap_eq_on_closed_strip (fun n => P n) hseam n p ((n : ℝ) + t)
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simpa only [add_sub_cancel_left] using hh
  have hzero (p : N) : f (p, 0) = P 0 (p, 0) := by
    simpa only [Nat.cast_zero, zero_add] using hclosed 0 p 0 ⟨le_rfl, zero_le_one⟩
  apply Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    have hzmem : (z.1, z.2 - (⌊z.2⌋₊ : ℝ)) ∈ univ ×ˢ Icc (0 : ℝ) 1 :=
      ⟨mem_univ _, sub_nonneg.mpr (Nat.floor_le hz.2.le),
        by linarith [Nat.lt_floor_add_one z.2]⟩
    refine ⟨mem_iUnion.mpr ⟨⌊z.2⌋₊, ⟨_, hzmem, rfl⟩⟩, ?_⟩
    rintro ⟨w, hw, hweq⟩
    have hwEq : w = (w.1, (0 : ℝ)) := Prod.ext rfl hw.2
    rw [hwEq, ← hzero] at hweq
    have hwmem : (w.1, (0 : ℝ)) ∈ univ ×ˢ Ici (0 : ℝ) := ⟨mem_univ _, show (0 : ℝ) ≤ 0 from le_rfl⟩
    have hzmem : z ∈ univ ×ˢ Ici (0 : ℝ) := ⟨hz.1, show (0 : ℝ) ≤ z.2 from hz.2.le⟩
    have he := hinj hwmem hzmem hweq
    have ht := congrArg Prod.snd he
    exact (ne_of_gt hz.2) ht.symm
  · rintro x ⟨hx, hnot⟩
    obtain ⟨n, z, hz, hzx⟩ := mem_iUnion.mp hx
    have hnonneg : 0 ≤ (n : ℝ) + z.2 := add_nonneg (Nat.cast_nonneg n) hz.2.1
    have hpos : 0 < (n : ℝ) + z.2 := by
      by_contra h
      have heq : (n : ℝ) + z.2 = 0 := le_antisymm (le_of_not_gt h) hnonneg
      apply hnot
      refine ⟨(z.1, 0), ⟨mem_univ _, rfl⟩, ?_⟩
      rw [← hzero, ← heq, hclosed n z.1 z.2 hz.2]
      exact hzx
    exact ⟨(z.1, (n : ℝ) + z.2), ⟨mem_univ _, hpos⟩, (hclosed n z.1 z.2 hz.2).trans hzx⟩

end DifferentialGeometry.Topology.Manifold

end

set_option autoImplicit false
noncomputable section
open Set Filter Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.Manifold

variable {E H N F G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]
  [Nonempty N] [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace M] [ChartedSpace G M]

theorem exists_global_product_chart_of_compatible_slabs
    (P : ℕ → PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M ∞)
    (hsource : ∀ n, (univ ×ˢ Icc (0 : ℝ) 1 : Set (N × ℝ)) ⊆ (P n).source)
    (hseam : ∀ n, ∃ V : Set (N × ℝ), IsOpen V ∧ univ ×ˢ ({0} : Set ℝ) ⊆ V ∧
      ∀ z ∈ V, P (n + 1) z = P n (z.1, z.2 + 1))
    (hadjacent : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
      P (n + 1) '' (univ ×ˢ Icc (0 : ℝ) 1) = P n '' (univ ×ˢ ({1} : Set ℝ)))
    (hseparated : ∀ m n : ℕ, m + 1 < n →
      Disjoint (P m '' (univ ×ˢ Icc (0 : ℝ) 1)) (P n '' (univ ×ˢ Icc (0 : ℝ) 1))) :
    ∃ Q : PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M ∞,
      Q.source = univ ×ˢ Ioi (0 : ℝ) ∧
      Q.target = (⋃ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1)) \
        (P 0 '' (univ ×ˢ ({0} : Set ℝ))) ∧
      EqOn Q (productChartMap (fun n => P n)) (univ ×ˢ Ioi (0 : ℝ)) ∧
      ∀ n : ℕ, ∀ p : N, ∀ t ∈ Icc (0 : ℝ) 1, 0 < (n : ℝ) + t →
        Q (p, (n : ℝ) + t) = P n (p, t) := by
  classical
  let U : TopologicalSpace.Opens (N × ℝ) := ⟨univ ×ˢ Ioi (0 : ℝ), isOpen_univ.prod isOpen_Ioi⟩
  let f := productChartMap (fun n => P n)
  have hlocal : IsLocalDiffeomorph (I.prod 𝓘(ℝ)) J ∞ (fun x : U => f x) :=
    DifferentialGeometry.isLocalDiffeomorph_restrict_open U
      (productChartMap_isLocalDiffeomorphOn P hsource hseam)
  have hinj0 : InjOn f (univ ×ˢ Ici (0 : ℝ)) :=
    productChartMap_injOn P hsource hadjacent hseparated
  have hinj : Function.Injective (fun x : U => f x) := by
    intro x y heq
    apply Subtype.ext
    exact hinj0 ⟨x.property.1, show (0 : ℝ) ≤ (x : N × ℝ).2 from x.property.2.le⟩
      ⟨y.property.1, show (0 : ℝ) ≤ (y : N × ℝ).2 from y.property.2.le⟩ heq
  let V : TopologicalSpace.Opens M := hlocal.image
  let e : Diffeomorph (I.prod 𝓘(ℝ)) J U V ∞ :=
    DifferentialGeometry.Topology.diffeomorphRangeOfInjective hlocal hinj
  let p0 : N := Classical.choice inferInstance
  let x0 : U := ⟨(p0, 1), mem_univ _, show (0 : ℝ) < 1 from zero_lt_one⟩
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (I.prod 𝓘(ℝ)) U ⟨x0⟩
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph J V ⟨e x0⟩
  let Q := (iU.symm.trans e.toPartialDiffeomorph).trans iV
  have hiU : iU.target = (U : Set (N × ℝ)) :=
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target _ _ _
  have hiV : iV.target = (V : Set M) :=
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target _ _ _
  have hQs : Q.source = (U : Set (N × ℝ)) := by
    ext x
    change ((x ∈ iU.target ∧ iU.symm x ∈ (univ : Set U)) ∧ e (iU.symm x) ∈ (univ : Set V)) ↔ x ∈ U
    simp only [mem_univ, and_true, hiU]
    rfl
  have hQt : Q.target = (V : Set M) := by
    ext y
    change (y ∈ iV.target ∧ (iV.symm y ∈ (univ : Set V) ∧ e.symm (iV.symm y) ∈ (univ : Set U))) ↔ y ∈ V
    simp only [mem_univ, and_self, and_true, hiV]
    rfl
  have hQeq : EqOn Q f U := by
    intro x hx
    have hi : iU.symm x = ⟨x, hx⟩ :=
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply _ _ _ hx
    change (e (iU.symm x) : M) = f x
    rw [hi]
    rfl
  have hboundary (n : ℕ) (p : N) : P (n + 1) (p, 0) = P n (p, 1) := by
    obtain ⟨W, _, hW, heq⟩ := hseam n
    simpa only [zero_add] using heq (p, 0) (hW ⟨mem_univ _, rfl⟩)
  have hVimage : (V : Set M) = f '' (U : Set (N × ℝ)) := by
    change range (fun x : U => f x) = f '' (U : Set (N × ℝ))
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨Q, hQs, hQt.trans (hVimage.trans (productChartMap_image_positive P hboundary hinj0)), hQeq, ?_⟩
  intro n p t ht hpos
  have hm : (p, (n : ℝ) + t) ∈ U := ⟨mem_univ _, hpos⟩
  rw [hQeq hm]
  have hh := productChartMap_eq_on_closed_strip (fun n => P n) hboundary n p ((n : ℝ) + t)
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simpa only [add_sub_cancel_left] using hh

end DifferentialGeometry.Topology.Manifold

end
