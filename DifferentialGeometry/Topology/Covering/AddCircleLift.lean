import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Calculus.ContDiff.Operations

noncomputable section

open Set Filter Topology
open scoped ContDiff Topology

namespace DifferentialGeometry.Topology

theorem eventually_apply_of_mem_nhdsWithin {α : Type*} [TopologicalSpace α] {s : Set α} {x : α}
    (hx : x ∈ s) {p : α → Prop} (h : ∀ᶠ y in 𝓝[s] x, p y) : p x := by
  obtain ⟨u, -, hxu, hu⟩ := mem_nhdsWithin.mp h
  exact hu ⟨hxu, hx⟩

theorem exists_contDiffOn_addCircle_lift_of_periodic {s : Set ℝ} (hs : Convex ℝ s)
    (hne : s.Nonempty) (f : ℝ × ℝ → AddCircle (1 : ℝ))
    (hper : ∀ p : ℝ × ℝ, f (p.1 + 1, p.2) = f p)
    (hloc : ∀ q ∈ (univ : Set ℝ) ×ˢ s, ∃ φ : ℝ × ℝ → ℝ,
      ContDiffWithinAt ℝ ∞ φ ((univ : Set ℝ) ×ˢ s) q ∧
      (fun p => (φ p : AddCircle (1 : ℝ))) =ᶠ[𝓝[(univ : Set ℝ) ×ˢ s] q] f) :
    ∃ (g : ℝ × ℝ → ℝ) (d : ℤ), ContDiffOn ℝ ∞ g ((univ : Set ℝ) ×ˢ s) ∧
      (∀ q ∈ (univ : Set ℝ) ×ˢ s, (g q : AddCircle (1 : ℝ)) = f q) ∧
      (∀ q ∈ (univ : Set ℝ) ×ˢ s, g (q.1 + 1, q.2) = g q + d) := by
  classical
  let U : Set (ℝ × ℝ) := (univ : Set ℝ) ×ˢ s
  have hUconv : Convex ℝ U := convex_univ.prod hs
  have hUne : U.Nonempty := ⟨(0, hne.some), ⟨trivial, hne.some_mem⟩⟩
  have hUpre : IsPreconnected U := hUconv.isPreconnected
  have : LocallyPathConnectedSpace U := hUconv.locallyPathConnectedSpace
  have : ContractibleSpace U := hUconv.contractibleSpace hUne
  have : SimplyConnectedSpace U := inferInstance
  have hshift_maps : MapsTo (fun p : ℝ × ℝ => (p.1 + 1, p.2)) U U :=
    fun p hp => ⟨trivial, hp.2⟩
  have hshift_cont : ContinuousOn (fun p : ℝ × ℝ => (p.1 + 1, p.2)) U :=
    ((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn
  have hfcont : ContinuousOn f U := by
    intro q hq
    obtain ⟨φ, hφ, hφeq⟩ := hloc q hq
    have hcoe : ContinuousWithinAt (fun p : ℝ × ℝ => (φ p : AddCircle (1 : ℝ))) U q :=
      (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.comp_continuousWithinAt
        hφ.continuousWithinAt
    exact hcoe.congr_of_eventuallyEq (Filter.EventuallyEq.symm hφeq)
      ((Filter.EventuallyEq.eq_of_nhdsWithin hφeq hq).symm)
  let F : C(U, AddCircle (1 : ℝ)) :=
    ⟨U.domRestrict f, continuousOn_iff_continuous_domRestrict.mp hfcont⟩
  let q₀ : U := ⟨hUne.some, hUne.some_mem⟩
  obtain ⟨φ₀, -, hφ₀eq⟩ := hloc hUne.some hUne.some_mem
  let e₀ : ℝ := φ₀ hUne.some
  have he₀ : ((e₀ : ℝ) : AddCircle (1 : ℝ)) = F q₀ :=
    eventually_apply_of_mem_nhdsWithin hUne.some_mem hφ₀eq
  obtain ⟨Y, ⟨hY₀, hYπ⟩, -⟩ :=
    (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts F q₀ e₀ he₀
  let g : ℝ × ℝ → ℝ := fun q => if hq : q ∈ U then Y ⟨q, hq⟩ else 0
  have hg_apply : ∀ q (hq : q ∈ U), g q = Y ⟨q, hq⟩ := by
    intro q hq
    simp only [g, dif_pos hq]
  have hg_lift : ∀ q ∈ U, (g q : AddCircle (1 : ℝ)) = f q := by
    intro q hq
    rw [hg_apply q hq]
    have := congrFun hYπ ⟨q, hq⟩
    simpa [F] using this
  have hg_cont : ContinuousOn g U := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine Y.continuous.congr fun x => ?_
    exact (hg_apply x.1 x.2).symm
  have hg_smooth : ContDiffOn ℝ ∞ g U := by
    intro q hq
    obtain ⟨φ, hφ, hφeq⟩ := hloc q hq
    obtain ⟨u₁, hu₁open, hqu₁, hu₁⟩ := mem_nhdsWithin.mp hφeq
    obtain ⟨u₂, hu₂mem, hu₂⟩ :=
      (contDiffWithinAt_iff_contDiffOn_nhds (n := (1 : ℕ∞ω)) (by decide)).mp
        (hφ.of_le (by simp))
    rw [Set.insert_eq_of_mem hq] at hu₂mem
    obtain ⟨u₃, hu₃open, hqu₃, hu₃⟩ := mem_nhdsWithin.mp hu₂mem
    have hmem : u₁ ∩ u₃ ∈ 𝓝 q :=
      Filter.inter_mem (hu₁open.mem_nhds hqu₁) (hu₃open.mem_nhds hqu₃)
    obtain ⟨r, hrpos, hr⟩ := Metric.mem_nhds_iff.mp hmem
    let t : Set (ℝ × ℝ) := U ∩ Metric.ball q r
    have ht_sub_U : t ⊆ U := inter_subset_left
    have ht_mem : t ∈ 𝓝[U] q :=
      Filter.inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds q hrpos))
    have ht_pre : IsPreconnected t := hUconv.inter (convex_ball q r) |>.isPreconnected
    have ht_sub_u₂ : t ⊆ u₂ := fun p hp => hu₃ ⟨(hr hp.2).2, hp.1⟩
    have hφt : ContinuousOn φ t := hu₂.continuousOn.mono ht_sub_u₂
    have ht_eq : ∀ p ∈ t, (φ p : AddCircle (1 : ℝ)) = f p := fun p hp => hu₁ ⟨(hr hp.2).1, hp.1⟩
    have hψ_cont : ContinuousOn (fun p : ℝ × ℝ => g p - φ p) t :=
      (hg_cont.mono ht_sub_U).sub hφt
    have hψ_mem : ∀ p ∈ t, g p - φ p ∈ AddSubgroup.zmultiples (1 : ℝ) := by
      intro p hp
      rw [← QuotientAddGroup.eq_iff_sub_mem]
      change ((g p : ℝ) : AddCircle (1 : ℝ)) = ((φ p : ℝ) : AddCircle (1 : ℝ))
      rw [hg_lift p (ht_sub_U hp), ht_eq p hp]
    let Ψ : ℝ × ℝ → AddSubgroup.zmultiples (1 : ℝ) :=
      fun p => if hp : p ∈ t then ⟨g p - φ p, hψ_mem p hp⟩ else 0
    have hΨcont : ContinuousOn Ψ t := by
      rw [continuousOn_iff_continuous_domRestrict]
      have h1 : Continuous (t.domRestrict (fun p : ℝ × ℝ => g p - φ p)) :=
        continuousOn_iff_continuous_domRestrict.mp hψ_cont
      refine (Continuous.subtype_mk h1 fun x => hψ_mem x.1 x.2).congr fun x => ?_
      change (⟨g x.1 - φ x.1, hψ_mem x.1 x.2⟩ : AddSubgroup.zmultiples (1 : ℝ)) = Ψ x.1
      simp only [Ψ, dif_pos x.2]
    have hq_t : q ∈ t := ⟨hq, Metric.mem_ball_self hrpos⟩
    have hval : ∀ p (hp : p ∈ t), (Ψ p).val = g p - φ p := by
      intro p hp
      simp only [Ψ, dif_pos hp]
    have hconst : ∀ p ∈ t, g p - φ p = g q - φ q := by
      intro p hp
      have hc := congrArg Subtype.val (IsPreconnected.constant ht_pre hΨcont hq_t hp)
      rw [hval q hq_t, hval p hp] at hc
      exact hc.symm
    have hgq : ContDiffWithinAt ℝ ∞ (fun p : ℝ × ℝ => φ p + (g q - φ q)) U q :=
      hφ.add contDiffWithinAt_const
    refine hgq.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [ht_mem] with p hp
      have := hconst p hp
      linarith
    · have := hconst q hq_t
      linarith
  have hψd_cont : ContinuousOn (fun p : ℝ × ℝ => g (p.1 + 1, p.2) - g p) U :=
    (hg_cont.comp hshift_cont hshift_maps).sub hg_cont
  have hψd_mem : ∀ p ∈ U, g (p.1 + 1, p.2) - g p ∈ AddSubgroup.zmultiples (1 : ℝ) := by
    intro p hp
    rw [← QuotientAddGroup.eq_iff_sub_mem]
    change ((g (p.1 + 1, p.2) : ℝ) : AddCircle (1 : ℝ)) = ((g p : ℝ) : AddCircle (1 : ℝ))
    rw [hg_lift (p.1 + 1, p.2) (hshift_maps hp), hper p, hg_lift p hp]
  let Ψd : ℝ × ℝ → AddSubgroup.zmultiples (1 : ℝ) :=
    fun p => if hp : p ∈ U then ⟨g (p.1 + 1, p.2) - g p, hψd_mem p hp⟩ else 0
  have hΨd_cont : ContinuousOn Ψd U := by
    rw [continuousOn_iff_continuous_domRestrict] at hψd_cont ⊢
    refine (Continuous.subtype_mk hψd_cont fun x => hψd_mem x.1 x.2).congr fun x => ?_
    change (⟨g (x.1.1 + 1, x.1.2) - g x.1, hψd_mem x.1 x.2⟩ :
      AddSubgroup.zmultiples (1 : ℝ)) = Ψd x.1
    simp only [Ψd, dif_pos x.2]
  obtain ⟨d, hd⟩ := AddSubgroup.mem_zmultiples_iff.mp (hψd_mem hUne.some hUne.some_mem)
  have hd' : g (hUne.some.1 + 1, hUne.some.2) - g hUne.some = (d : ℝ) := by
    rw [← hd, zsmul_one]
  refine ⟨g, d, hg_smooth, hg_lift, ?_⟩
  intro q hq
  have hval : ∀ p (hp : p ∈ U), (Ψd p).val = g (p.1 + 1, p.2) - g p := by
    intro p hp
    simp only [Ψd, dif_pos hp]
  have hc := congrArg Subtype.val (IsPreconnected.constant hUpre hΨd_cont hUne.some_mem hq)
  rw [hval hUne.some hUne.some_mem, hval q hq] at hc
  linarith

end DifferentialGeometry.Topology
