import DifferentialGeometry.Topology.Engulfing.Prism.TransverseSemicontinuousPrism

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Topology

theorem upperSemicontinuous_piecewise_raise {X : Type*} [TopologicalSpace X]
    {f g : X → ℝ} (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
    (hfg : ∀ x, f x ≤ g x) {J : Set X} (hJ : IsClosed J) [DecidablePred (· ∈ J)] :
    UpperSemicontinuous (J.piecewise g f) := by
  apply upperSemicontinuous_iff_IsClosed_hypograph.mpr
  have heq : {p : X × ℝ | p.2 ≤ J.piecewise g f p.1} =
      {p : X × ℝ | p.2 ≤ f p.1} ∪
        ((J ×ˢ (univ : Set ℝ)) ∩ {p : X × ℝ | p.2 ≤ g p.1}) := by
    ext p
    by_cases hp : p.1 ∈ J
    · simp only [piecewise_eq_of_mem _ _ _ hp, mem_ofPred_eq, mem_union, mem_inter_iff,
        mem_prod, mem_univ, and_true, hp, true_and]
      exact ⟨Or.inr, fun h => h.elim (fun h => h.trans (hfg p.1)) id⟩
    · simp only [piecewise_eq_of_notMem _ _ _ hp, mem_ofPred_eq, mem_union, mem_inter_iff,
        mem_prod, mem_univ, and_true, hp, false_and, or_false]
  rw [heq]
  exact hf.IsClosed_hypograph.union ((hJ.prod isClosed_univ).inter hg.IsClosed_hypograph)

theorem exists_prism_engulfing_relative_columns {Y Z : Type*}
    [MetricSpace Y] [MetricSpace Z] (o : Y) {F : Set Z} (hF : IsClosed F)
    {f g : F → ℝ} (hf : Continuous f) (hg : Continuous g) (hfg : ∀ z, f z ≤ g z)
    (hboundary : ∀ z : F, z.1 ∈ frontier F → f z = g z)
    {J : Set F} (hJ : IsClosed J) {U W A : Set ((Y × Z) × ℝ)}
    (hU : IsOpen U) (hW : IsOpen W) (hA : IsClosed A) (hAU : A ⊆ U)
    (hgraph : ∀ z : F, ((o, z.1), f z) ∈ U)
    (hcolumns : ∀ z ∈ J, ∀ t ∈ Icc (f z) (g z), ((o, z.1), t) ∈ U)
    (hmoving : ∀ z ∉ J, ∀ t ∈ Ioc (f z) (g z), ((o, z.1), t) ∈ W)
    (havoid : ∀ z ∉ J, ∀ t ∈ Ioc (f z) (g z), ((o, z.1), t) ∉ A) :
    ∃ H : ((Y × Z) × ℝ) ≃ₜ ((Y × Z) × ℝ),
      (∀ p, (H p).1 = p.1) ∧ (∀ p ∉ W, H p = p) ∧
      (∀ p ∈ A, H p = p) ∧ (∀ p, p.1.2 ∉ interior F → H p = p) ∧
      A ⊆ H '' U ∧
      ∀ (z : F) t, t ∈ Icc (f z) (g z) → ((o, z.1), t) ∈ H '' U := by
  classical
  let r : F → ℝ := J.piecewise g f
  have hr : UpperSemicontinuous r :=
    upperSemicontinuous_piecewise_raise hf.upperSemicontinuous hg.upperSemicontinuous hfg hJ
  have hfr (z : F) : f z ≤ r z := by
    dsimp [r]
    by_cases hz : z ∈ J
    · rw [piecewise_eq_of_mem _ _ _ hz]
      exact hfg z
    · rw [piecewise_eq_of_notMem _ _ _ hz]
  have hrg (z : F) : r z ≤ g z := by
    dsimp [r]
    by_cases hz : z ∈ J
    · rw [piecewise_eq_of_mem _ _ _ hz]
    · rw [piecewise_eq_of_notMem _ _ _ hz]
      exact hfg z
  have hrboundary (z : F) (hz : z.1 ∈ frontier F) : r z = g z :=
    le_antisymm (hrg z) ((hboundary z hz) ▸ hfr z)
  apply exists_transverse_semicontinuous_prism_engulfing_keeping o hF
    hf.lowerSemicontinuous hr hg hfr hrg hrboundary hU hW hA hAU
  · intro z t ht
    by_cases hz : z ∈ J
    · exact hcolumns z hz t ⟨ht.1, ht.2.trans (hrg z)⟩
    · have he : r z = f z := piecewise_eq_of_notMem _ _ _ hz
      have htf : t = f z := le_antisymm (he ▸ ht.2) ht.1
      simpa only [htf] using hgraph z
  · intro z t ht
    by_cases hz : z ∈ J
    · have he : r z = g z := piecewise_eq_of_mem _ _ _ hz
      exact False.elim (not_lt_of_ge ht.2 (he ▸ ht.1))
    · exact hmoving z hz t ⟨(hfr z).trans_lt ht.1, ht.2⟩
  · intro z t ht
    by_cases hz : z ∈ J
    · have he : r z = g z := piecewise_eq_of_mem _ _ _ hz
      exact False.elim (not_lt_of_ge ht.2 (he ▸ ht.1))
    · exact havoid z hz t ⟨(hfr z).trans_lt ht.1, ht.2⟩

end DifferentialGeometry.Topology.Engulfing
