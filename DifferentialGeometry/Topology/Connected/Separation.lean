import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Subpath

open Set Topology

namespace DifferentialGeometry.Topology

variable {X : Type*} [TopologicalSpace X]

def Separates (C H K : Set X) : Prop :=
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ Disjoint U V ∧ U ∪ V = Cᶜ ∧ H ⊆ U ∧ K ⊆ V

theorem Separates.symm {C H K : Set X} (h : Separates C H K) : Separates C K H := by
  obtain ⟨U, V, hU, hV, hd, heq, hH, hK⟩ := h
  exact ⟨V, U, hV, hU, hd.symm, (union_comm V U).trans heq, hK, hH⟩

theorem Separates.left_subset_compl {C H K : Set X} (h : Separates C H K) : H ⊆ Cᶜ := by
  obtain ⟨U, V, _, _, _, heq, hH, _⟩ := h
  exact hH.trans (subset_union_left.trans heq.subset)

theorem Separates.right_subset_compl {C H K : Set X} (h : Separates C H K) : K ⊆ Cᶜ :=
  h.symm.left_subset_compl

theorem Separates.not_mem_connectedComponentIn {C H K : Set X} (h : Separates C H K)
    {x y : X} (hx : x ∈ H) (hy : y ∈ K) : y ∉ connectedComponentIn Cᶜ x := by
  obtain ⟨U, V, hU, hV, hd, heq, hH, hK⟩ := h
  intro hyx
  have hsub : connectedComponentIn Cᶜ x ⊆ U :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union hU hV hd
      ((connectedComponentIn_subset _ _).trans heq.symm.subset)
      ⟨x, mem_connectedComponentIn (heq ▸ Or.inl (hH hx)), hH hx⟩
  exact disjoint_left.mp hd (hsub hyx) (hK hy)

theorem separates_empty_left {C K : Set X} (hC : IsClosed C) (hK : K ⊆ Cᶜ) :
    Separates C ∅ K :=
  ⟨∅, Cᶜ, isOpen_empty, hC.isOpen_compl, by simp, empty_union _,
    empty_subset _, hK⟩

theorem separates_iff_not_mem_connectedComponentIn [LocallyConnectedSpace X]
    {C H K : Set X} (hC : IsClosed C) (hH : IsPreconnected H) (hK : IsPreconnected K)
    (hHC : H ⊆ Cᶜ) (hKC : K ⊆ Cᶜ) {x y : X} (hx : x ∈ H) (hy : y ∈ K) :
    Separates C H K ↔ y ∉ connectedComponentIn Cᶜ x := by
  refine ⟨fun h => h.not_mem_connectedComponentIn hx hy, fun hxy => ?_⟩
  let U := connectedComponentIn Cᶜ x
  have hHU : H ⊆ U := hH.subset_connectedComponentIn hx hHC
  have hKV : K ⊆ Cᶜ \ U := by
    intro z hz
    refine ⟨hKC hz, fun hzU => ?_⟩
    have hsub := hK.subset_connectedComponentIn hz hKC
    rw [← connectedComponentIn_eq hzU] at hsub
    exact hxy (hsub hy)
  have hV : IsOpen (Cᶜ \ U) := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    apply Filter.mem_of_superset
      (hC.isOpen_compl.connectedComponentIn.mem_nhds (mem_connectedComponentIn hz.1))
    intro w hw
    refine ⟨connectedComponentIn_subset _ _ hw, fun hwU => ?_⟩
    have heq := (connectedComponentIn_eq hw).trans (connectedComponentIn_eq hwU).symm
    exact hz.2 (show z ∈ connectedComponentIn Cᶜ x from heq ▸ mem_connectedComponentIn hz.1)
  refine ⟨U, Cᶜ \ U, hC.isOpen_compl.connectedComponentIn, hV,
    disjoint_sdiff_right, ?_, hHU, hKV⟩
  exact union_sdiff_cancel (connectedComponentIn_subset _ _)

theorem joinedIn_compl_of_not_separates [LocallyConnectedSpace X]
    (hpath : ∀ U : Set X, IsOpen U → IsConnected U → IsPathConnected U)
    {C H K : Set X} (hC : IsClosed C) (hH : IsPreconnected H) (hK : IsPreconnected K)
    (hHC : H ⊆ Cᶜ) (hKC : K ⊆ Cᶜ) (h : ¬ Separates C H K)
    {x y : X} (hx : x ∈ H) (hy : y ∈ K) : JoinedIn Cᶜ x y := by
  have hyU : y ∈ connectedComponentIn Cᶜ x := by
    by_contra hn
    exact h ((separates_iff_not_mem_connectedComponentIn hC hH hK hHC hKC hx hy).mpr hn)
  exact ((hpath _ hC.isOpen_compl.connectedComponentIn
    (isConnected_connectedComponentIn_iff.mpr (hHC hx))).joinedIn x
      (mem_connectedComponentIn (hHC hx)) y hyU).mono (connectedComponentIn_subset _ _)

theorem JoinedIn.compl_of_frontier_replacement
    {C C' N : Set X} {x y : X} (h : JoinedIn C'ᶜ x y)
    (hN : IsClosed N) (hout : C \ N = C' \ N)
    (hfrontier : frontier N \ C' ⊆ Cᶜ) (hpath : IsPathConnected (frontier N \ C'))
    (hxN : x ∈ Nᶜ) (hyN : y ∈ Nᶜ) :
    JoinedIn Cᶜ x y := by
  let γ := h.somePath
  let T : Set unitInterval := γ ⁻¹' N
  have hγ (t : unitInterval) : γ t ∈ C'ᶜ := h.somePath_mem t
  have houtside {z : X} (hzC' : z ∈ C'ᶜ) (hzN : z ∈ Nᶜ) : z ∈ Cᶜ := by
    intro hzC
    have hz : z ∈ C \ N := ⟨hzC, hzN⟩
    rw [hout] at hz
    exact hzC' hz.1
  by_cases hTne : T.Nonempty
  · have hTclosed : IsClosed T := hN.preimage γ.continuous
    obtain ⟨a, haT, hamin⟩ :=
      hTclosed.isCompact.exists_isMinOn hTne continuous_subtype_val.continuousOn
    obtain ⟨b, hbT, hbmax⟩ :=
      hTclosed.isCompact.exists_isMaxOn hTne continuous_subtype_val.continuousOn
    have haN : γ a ∈ N := haT
    have hbN : γ b ∈ N := hbT
    have hab : a ≤ b := hamin hbT
    have ha0 : (a : ℝ) ≠ 0 := by
      intro ha
      apply hxN
      simpa only [show a = 0 from Subtype.ext ha, γ, Path.source] using haN
    have hb1 : (b : ℝ) ≠ 1 := by
      intro hb
      apply hyN
      simpa only [show b = 1 from Subtype.ext hb, γ, Path.target] using hbN
    have haPos : (0 : ℝ) < a := lt_of_le_of_ne a.property.1 (Ne.symm ha0)
    have hbLt : (b : ℝ) < 1 := lt_of_le_of_ne b.property.2 hb1
    have hbefore : ∀ s ∈ Ico (0 : ℝ) a, γ.extend s ∈ Nᶜ := by
      intro s hs
      have hsI : s ∈ Icc (0 : ℝ) 1 :=
        ⟨hs.1, (le_of_lt hs.2).trans a.property.2⟩
      rw [Path.extend_apply γ hsI]
      intro hsN
      let sI : unitInterval := ⟨s, hsI⟩
      exact (not_le_of_gt hs.2) (hamin (show sI ∈ T from hsN))
    have hafter : ∀ s ∈ Ioc (b : ℝ) 1, γ.extend s ∈ Nᶜ := by
      intro s hs
      have hsI : s ∈ Icc (0 : ℝ) 1 :=
        ⟨b.property.1.trans (le_of_lt hs.1), hs.2⟩
      rw [Path.extend_apply γ hsI]
      intro hsN
      let sI : unitInterval := ⟨s, hsI⟩
      exact (not_le_of_gt hs.1) (hbmax (show sI ∈ T from hsN))
    have haTimeClosure : (a : ℝ) ∈ closure (Ico (0 : ℝ) a) := by
      rw [closure_Ico (Ne.symm ha0)]
      exact ⟨haPos.le, le_rfl⟩
    have hbTimeClosure : (b : ℝ) ∈ closure (Ioc (b : ℝ) 1) := by
      rw [closure_Ioc hb1]
      exact ⟨le_rfl, hbLt.le⟩
    have haClosure : γ a ∈ closure Nᶜ := by
      have ha := γ.continuous_extend.continuousAt.continuousWithinAt.mem_closure
        haTimeClosure hbefore
      rw [Path.extend_apply γ a.property] at ha
      exact ha
    have hbClosure : γ b ∈ closure Nᶜ := by
      have hb := γ.continuous_extend.continuousAt.continuousWithinAt.mem_closure
        hbTimeClosure hafter
      rw [Path.extend_apply γ b.property] at hb
      exact hb
    have haNotInterior : γ a ∉ interior N := by
      simpa only [← mem_compl_iff, ← closure_compl] using haClosure
    have hbNotInterior : γ b ∉ interior N := by
      simpa only [← mem_compl_iff, ← closure_compl] using hbClosure
    have haFrontier : γ a ∈ frontier N :=
      (mem_frontier_iff_notMem_interior haN).2 haNotInterior
    have hbFrontier : γ b ∈ frontier N :=
      (mem_frontier_iff_notMem_interior hbN).2 hbNotInterior
    have haSafe : γ a ∈ frontier N \ C' := ⟨haFrontier, hγ a⟩
    have hbSafe : γ b ∈ frontier N \ C' := ⟨hbFrontier, hγ b⟩
    have hprefix : JoinedIn Cᶜ x (γ a) := by
      have hp : JoinedIn Cᶜ (γ 0) (γ a) := by
        refine ⟨γ.subpath 0 a, fun t => ?_⟩
        have ht : γ.subpath 0 a t ∈ range (γ.subpath 0 a) := mem_range_self t
        rw [Path.range_subpath_of_le γ 0 a bot_le] at ht
        obtain ⟨s, hs, hst⟩ := ht
        rw [← hst]
        by_cases hsa : s = a
        · simpa only [hsa] using hfrontier haSafe
        · apply houtside (hγ s)
          intro hsN
          exact (not_le_of_gt (lt_of_le_of_ne hs.2 hsa))
            (hamin (show s ∈ T from hsN))
      simpa only [γ, Path.source] using hp
    have hsuffix : JoinedIn Cᶜ (γ b) y := by
      have hp : JoinedIn Cᶜ (γ b) (γ 1) := by
        refine ⟨γ.subpath b 1, fun t => ?_⟩
        have ht : γ.subpath b 1 t ∈ range (γ.subpath b 1) := mem_range_self t
        rw [Path.range_subpath_of_le γ b 1 le_top] at ht
        obtain ⟨s, hs, hst⟩ := ht
        rw [← hst]
        by_cases hsb : s = b
        · simpa only [hsb] using hfrontier hbSafe
        · apply houtside (hγ s)
          intro hsN
          exact (not_le_of_gt (lt_of_le_of_ne hs.1 fun hsb' => hsb hsb'.symm))
            (hbmax (show s ∈ T from hsN))
      simpa only [γ, Path.target] using hp
    have hmiddle : JoinedIn Cᶜ (γ a) (γ b) :=
      (hpath.joinedIn (γ a) haSafe (γ b) hbSafe).mono hfrontier
    exact (hprefix.trans hmiddle).trans hsuffix
  · refine ⟨γ, fun t => houtside (hγ t) ?_⟩
    intro htN
    exact hTne ⟨t, htN⟩

theorem Separates.of_frontier_replacement [LocallyConnectedSpace X]
    (hopenPath : ∀ U : Set X, IsOpen U → IsConnected U → IsPathConnected U)
    {C C' H K N : Set X} (h : Separates C H K) (hC' : IsClosed C')
    (hN : IsClosed N) (hout : C \ N = C' \ N)
    (hfrontier : frontier N \ C' ⊆ Cᶜ) (hpath : IsPathConnected (frontier N \ C'))
    (hH : IsPreconnected H) (hK : IsPreconnected K)
    (hHN : H ⊆ Nᶜ) (hKN : K ⊆ Nᶜ) :
    Separates C' H K := by
  have hHC' : H ⊆ C'ᶜ := by
    intro x hxH hxC'
    have hx : x ∈ C' \ N := ⟨hxC', hHN hxH⟩
    rw [← hout] at hx
    exact h.left_subset_compl hxH hx.1
  have hKC' : K ⊆ C'ᶜ := by
    intro x hxK hxC'
    have hx : x ∈ C' \ N := ⟨hxC', hKN hxK⟩
    rw [← hout] at hx
    exact h.right_subset_compl hxK hx.1
  by_cases hHne : H.Nonempty
  · by_cases hKne : K.Nonempty
    · obtain ⟨x, hx⟩ := hHne
      obtain ⟨y, hy⟩ := hKne
      by_contra hsep
      have hjoined := joinedIn_compl_of_not_separates hopenPath hC' hH hK hHC' hKC'
        hsep hx hy
      have hjoined' := JoinedIn.compl_of_frontier_replacement hjoined hN hout hfrontier hpath
        (hHN hx) (hKN hy)
      exact h.not_mem_connectedComponentIn hx hy
        ((isConnected_range hjoined'.somePath.continuous).isPreconnected.subset_connectedComponentIn
          ⟨0, hjoined'.somePath.source⟩
          (range_subset_iff.mpr hjoined'.somePath_mem)
          ⟨1, hjoined'.somePath.target⟩)
    · rw [not_nonempty_iff_eq_empty.mp hKne]
      exact (separates_empty_left hC' hHC').symm
  · rw [not_nonempty_iff_eq_empty.mp hHne]
    exact separates_empty_left hC' hKC'

end DifferentialGeometry.Topology
