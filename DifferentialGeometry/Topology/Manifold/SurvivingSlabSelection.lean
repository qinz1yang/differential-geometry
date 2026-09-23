import DifferentialGeometry.Topology.Combinatorics.FiberEnumeration
import DifferentialGeometry.Topology.Combinatorics.BranchUpdates
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E H N F G M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace N] [ChartedSpace H N] [CompactSpace N]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace M] [ChartedSpace G M] [T2Space M]
  {r : ℕ∞ω}

theorem exists_surviving_slab_sequence_of_finite_updates
    (label : ℕ → ι) (hlabels : (range label).Finite)
    (sphere : ℕ → ι → N → M)
    (hunchanged : ∀ n i, label n ≠ i → sphere (n + 1) i = sphere n i)
    (P : ℕ → PartialDiffeomorph (I.prod 𝓘(ℝ)) J (N × ℝ) M r)
    (hsource : ∀ n, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (P n).source)
    (μ : ℕ → Diffeomorph I I N N r)
    (hlower : ∀ n z, P n (z, 0) = sphere n (label n) z)
    (hupper : ∀ n z, P n (z, 1) = sphere (n + 1) (label n) (μ n z))
    (W : ℕ → Set M) (hW : Monotone W)
    (hcontained : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ W (n + 1))
    (hinter : ∀ n, P n '' (univ ×ˢ Icc (0 : ℝ) 1) ∩ W n = range (sphere n (label n)))
    (hsphere_frontier : ∀ n, range (sphere n (label n)) ⊆ frontier (W n))
    (hfilled : ∀ n, range (sphere n (label n)) ⊆ interior (W (n + 1))) :
    ∃ i : ι, ∃ s : ℕ → ℕ, StrictMono s ∧ (∀ n, label (s n) = i) ∧
      (∀ z, P (s 0) (z, 0) = sphere 0 i z) ∧
      (∀ n, univ ×ˢ Icc (0 : ℝ) 1 ⊆ (P (s n)).source) ∧
      (∀ n z, P (s (n + 1)) (z, 0) = P (s n) ((μ (s n)).symm z, 1)) ∧
      (∀ n, P (s n) '' (univ ×ˢ Icc (0 : ℝ) 1) ∩
        P (s (n + 1)) '' (univ ×ˢ Icc (0 : ℝ) 1) =
        P (s n) '' (univ ×ˢ ({1} : Set ℝ))) ∧
      (∀ a b : ℕ, a + 1 < b →
        Disjoint (P (s a) '' (univ ×ˢ Icc (0 : ℝ) 1))
          (P (s b) '' (univ ×ˢ Icc (0 : ℝ) 1))) ∧
      (⋃ n, P (s n) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩ W 0 =
        range (sphere 0 i) ∩ W 0 := by
  obtain ⟨i, s, hmono, hlabel, _, hfirst, hgap⟩ := hlabels.exists_strictMono_enumeration_fiber
  have hstates (n : ℕ) : sphere (s (n + 1)) i = sphere (s n + 1) i :=
    DifferentialGeometry.Topology.state_succ_eq_of_consecutive_occurrences
      label sphere hunchanged i s hmono hgap n
  have hpair (n : ℕ) (z : N) : P (s (n + 1)) (z, 0) =
      P (s n) ((μ (s n)).symm z, 1) := by
    rw [hlower, hupper, hlabel, hlabel]
    have hs := congrFun (hstates n) z
    exact hs.trans (congrArg (sphere (s n + 1) i)
      (show z = μ (s n) ((μ (s n)).symm z) from ((μ (s n)).apply_symm_apply z).symm))
  have hupper_range (n : ℕ) : P (s n) '' (univ ×ˢ ({1} : Set ℝ)) =
      range (sphere (s (n + 1)) (label (s (n + 1)))) := by
    ext x
    constructor
    · rintro ⟨⟨z, t⟩, ⟨_, ht⟩, hz⟩
      have : t = 1 := ht
      subst t
      refine ⟨μ (s n) z, ?_⟩
      have he := hpair n (μ (s n) z)
      rw [hlower] at he
      have hmu : (μ (s n)).symm (μ (s n) z) = z := (μ (s n)).symm_apply_apply z
      exact he.trans ((congrArg (fun q => P (s n) (q, 1)) hmu).trans hz)
    · rintro ⟨z, hz⟩
      exact ⟨((μ (s n)).symm z, 1), ⟨mem_univ _, rfl⟩,
        (hpair n z).symm.trans ((hlower _ z).trans hz)⟩
  have hbase : sphere (s 0) i = sphere 0 i :=
    DifferentialGeometry.Topology.eq_of_no_update_between label sphere hunchanged i
      (Nat.zero_le _) (fun m hm hms hmi => (not_lt_of_ge (hfirst m hmi)) hms)
  have hinitial : (⋃ n, P (s n) '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩ W 0 =
      range (sphere 0 i) ∩ W 0 := by
    ext x
    constructor
    · rintro ⟨hx, hxW⟩
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      refine ⟨?_, hxW⟩
      cases n with
      | zero =>
        have hxlow : x ∈ range (sphere (s 0) (label (s 0))) :=
          hinter _ ▸ ⟨hn, hW (Nat.zero_le _) hxW⟩
        simpa only [hlabel, hbase] using hxlow
      | succ n =>
        have hxlow : x ∈ range (sphere (s (n + 1)) (label (s (n + 1)))) :=
          hinter _ ▸ ⟨hn, hW (Nat.zero_le _) hxW⟩
        have hxup : x ∈ P (s n) '' (univ ×ˢ ({1} : Set ℝ)) :=
          hupper_range n ▸ hxlow
        obtain ⟨⟨z, t⟩, ⟨_, ht⟩, hz⟩ := hxup
        have ht1 : t = 1 := ht
        subst t
        have hzsource := hsource (s n) (show (z, (1 : ℝ)) ∈
          univ ×ˢ Icc (0 : ℝ) 1 from ⟨mem_univ _, by norm_num⟩)
        have hxold : x ∈ range (sphere (s n) (label (s n))) :=
          hinter _ ▸ ⟨⟨(z, 1), ⟨mem_univ _, by norm_num⟩, hz⟩,
            hW (Nat.zero_le _) hxW⟩
        obtain ⟨w, hw⟩ := hxold
        have hwsource := hsource (s n) (show (w, (0 : ℝ)) ∈
          univ ×ˢ Icc (0 : ℝ) 1 from ⟨mem_univ _, by norm_num⟩)
        have hEq : (z, (1 : ℝ)) = (w, 0) := (P (s n)).injOn hzsource hwsource
          (hz.trans ((hlower _ w).trans hw).symm)
        have hfalse : (1 : ℝ) = 0 := congrArg Prod.snd hEq
        exact (one_ne_zero hfalse).elim
    · rintro ⟨⟨z, hz⟩, hxW⟩
      refine ⟨mem_iUnion.mpr ⟨0, ?_⟩, hxW⟩
      refine ⟨(z, 0), ⟨mem_univ _, by norm_num⟩, ?_⟩
      rw [hlower, hlabel, hbase]
      exact hz
  refine ⟨i, s, hmono, hlabel, ?_, fun n => hsource _, hpair, ?_, ?_, hinitial⟩
  · intro z
    rw [hlower, hlabel]
    exact congrFun hbase z
  · intro n
    rw [hupper_range]
    apply Subset.antisymm
    · intro x hx
      have hinW : x ∈ W (s (n + 1)) :=
        hW (Nat.succ_le_of_lt (hmono (Nat.lt_succ_self n))) (hcontained _ hx.1)
      exact hinter _ ▸ ⟨hx.2, hinW⟩
    · intro x hx
      obtain ⟨z, hz⟩ := hx
      have hp : P (s n) ((μ (s n)).symm z, 1) = x :=
        (hpair n z).symm.trans ((hlower _ z).trans hz)
      exact ⟨⟨((μ (s n)).symm z, 1), ⟨mem_univ _, by norm_num⟩, hp⟩,
        ⟨(z, 0), ⟨mem_univ _, by norm_num⟩, (hlower _ z).trans hz⟩⟩
  · intro a b hab
    apply disjoint_left.mpr
    intro x hxA hxB
    have hsak : s a < s (a + 1) := hmono (Nat.lt_succ_self a)
    have hskb : s (a + 1) < s b := hmono hab
    have hxW : x ∈ W (s b) := hW (Nat.succ_le_of_lt (lt_trans hsak hskb)) (hcontained _ hxA)
    have hxSphere : x ∈ range (sphere (s b) (label (s b))) := hinter _ ▸ ⟨hxB, hxW⟩
    have hxfront := hsphere_frontier (s b) hxSphere
    have hfirst : x ∈ P (s a) '' (univ ×ˢ Icc (0 : ℝ) 1) := hxA
    by_cases hxint : x ∈ interior (P (s a) '' (univ ×ˢ Icc (0 : ℝ) 1))
    · exact hxfront.2 (interior_mono ((hcontained _).trans
        (hW (Nat.succ_le_of_lt (lt_trans hsak hskb)))) hxint)
    · have hxBfront : x ∈ frontier (P (s a) '' (univ ×ˢ Icc (0 : ℝ) 1)) :=
        ⟨subset_closure hfirst, hxint⟩
      have hxsrc : ∃ q : N × ℝ, q ∈ univ ×ˢ ({0, 1} : Set ℝ) ∧ P (s a) q = x := by
        have hc : IsClosed (P (s a) '' (univ ×ˢ Icc (0 : ℝ) 1)) :=
          ((isCompact_univ.prod isCompact_Icc).image_of_continuousOn
            ((P (s a)).contMDiffOn_toFun.continuousOn.mono (hsource _))).isClosed
        have hf := (P (s a)).toOpenPartialHomeomorph.image_frontier_of_subset_source
          (hsource (s a)) (isClosed_univ.prod isClosed_Icc) hc
        change P (s a) '' frontier (univ ×ˢ Icc (0 : ℝ) 1) =
          frontier (P (s a) '' (univ ×ˢ Icc (0 : ℝ) 1)) at hf
        rw [frontier_univ_prod_eq, frontier_Icc zero_le_one] at hf
        have hximage : x ∈ P (s a) '' (univ ×ˢ ({0, 1} : Set ℝ)) := hf.symm ▸ hxBfront
        exact hximage
      obtain ⟨⟨z, t⟩, ⟨_, ht⟩, hzx⟩ := hxsrc
      rcases ht with ht | ht
      · have : t = 0 := ht
        subst t
        have hxlow : x ∈ range (sphere (s a) (label (s a))) :=
          ⟨z, (hlower _ z).symm.trans hzx⟩
        exact hxfront.2 (interior_mono (hW (Nat.succ_le_of_lt (lt_trans hsak hskb)))
          (hfilled _ hxlow))
      · have : t = 1 := ht
        subst t
        have hxup : x ∈ range (sphere (s (a + 1)) (label (s (a + 1)))) :=
          hupper_range a ▸ ⟨(z, 1), ⟨mem_univ _, rfl⟩, hzx⟩
        exact hxfront.2 (interior_mono (hW (Nat.succ_le_of_lt hskb)) (hfilled _ hxup))

end DifferentialGeometry.Topology.Manifold
