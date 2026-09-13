import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.Comparison



noncomputable section

open Set Bundle Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianCurveLength_le_of_quad (g h : SmoothRiemannianMetric I M) {c : ℝ}
    (hc : 0 < c) (hgh : ∀ x v, h.inner x v v ≤ c * g.inner x v v)
    (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveLength h γ a b ≤
      ENNReal.ofReal (Real.sqrt c) * riemannianCurveLength g γ a b := by
  unfold riemannianCurveLength
  rw [ENNReal.mul_iSup]
  refine iSup_le fun p => ?_
  calc ∑ i ∈ Finset.range p.1,
        riemannianEDistOf h (γ (p.2.1 (i + 1))) (γ (p.2.1 i))
      ≤ ∑ i ∈ Finset.range p.1, ENNReal.ofReal (Real.sqrt c) *
          riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
        Finset.sum_le_sum fun i _ => edistOf_le_of_quad g h hc hgh _ _
    _ = ENNReal.ofReal (Real.sqrt c) * ∑ i ∈ Finset.range p.1,
          riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
        (Finset.mul_sum ..).symm
    _ ≤ ⨆ q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
          ENNReal.ofReal (Real.sqrt c) * ∑ i ∈ Finset.range q.1,
            riemannianEDistOf g (γ (q.2.1 (i + 1))) (γ (q.2.1 i)) := le_iSup (f := fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b} => ENNReal.ofReal (Real.sqrt c) * ∑ i ∈ Finset.range q.1, riemannianEDistOf g (γ (q.2.1 (i + 1))) (γ (q.2.1 i))) p

theorem le_riemannianCurveLength_of_quad (g h : SmoothRiemannianMetric I M) {c : ℝ}
    (hc : 0 < c) (hl : ∀ x v, c * g.inner x v v ≤ h.inner x v v)
    (γ : ℝ → M) (a b : ℝ) :
    ENNReal.ofReal (Real.sqrt c) * riemannianCurveLength g γ a b ≤
      riemannianCurveLength h γ a b := by
  unfold riemannianCurveLength
  rw [ENNReal.mul_iSup]
  refine iSup_le fun p => ?_
  calc ENNReal.ofReal (Real.sqrt c) * ∑ i ∈ Finset.range p.1,
        riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i))
      = ∑ i ∈ Finset.range p.1, ENNReal.ofReal (Real.sqrt c) *
          riemannianEDistOf g (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) := Finset.mul_sum ..
    _ ≤ ∑ i ∈ Finset.range p.1,
          riemannianEDistOf h (γ (p.2.1 (i + 1))) (γ (p.2.1 i)) :=
        Finset.sum_le_sum fun i _ => le_edistOf_of_quad g h hc hl _ _
    _ ≤ ⨆ q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
          ∑ i ∈ Finset.range q.1,
            riemannianEDistOf h (γ (q.2.1 (i + 1))) (γ (q.2.1 i)) := le_iSup (f := fun q : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b} => ∑ i ∈ Finset.range q.1, riemannianEDistOf h (γ (q.2.1 (i + 1))) (γ (q.2.1 i))) p

theorem riemannianCurveLength_scaleMetric (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) :
    riemannianCurveLength (scaleMetric (I := I) c hc g) γ a b =
      ENNReal.ofReal (Real.sqrt c) * riemannianCurveLength g γ a b := by
  refine le_antisymm ?_ ?_
  · refine riemannianCurveLength_le_of_quad g (scaleMetric (I := I) c hc g) hc ?_ γ a b
    intro x v
    simp
  · exact le_riemannianCurveLength_of_quad g (scaleMetric (I := I) c hc g) hc
      (fun x v => by simp) γ a b

namespace GeometricCutoffRecord

variable {H : ObservedHistory.{u}} {i : Fin H.eventCount} {parameters : CutoffParameters}
  (G : GeometricCutoffRecord H i parameters)

def LocalLengthComparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c) : Prop :=
  ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
    (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
    Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
    ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x ∈ (Kc c).support.region,
      ∃ U ∈ 𝓝 x, ∀ (a b : ℝ) (γ : ℝ → (G.Parent c).Carrier),
        a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
        riemannianCurveLength ((H.stage i.castSucc).componentMetric
          ((H.event i).incoming.flow.base.metric s)
          (G.transition.childParent c)) γ a b ≠ ⊤ →
        riemannianCurveLength
          ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
          (fun t => (Kc c).rfs_whole_parent_map (γ t)) a b ≤
        ENNReal.ofReal (ell s) * riemannianCurveLength
          ((H.stage i.castSucc).componentMetric
            ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) γ a b

theorem rfs_child_comparison_metric_of_local_length_comparison
    (Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c)
    (hlocal : G.LocalLengthComparison Kc) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, f c = (Kc c).rfs_whole_parent_map) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨s₀, hs₀, ell, hell, htend, hloc⟩ := hlocal
  refine ⟨fun c => (Kc c).rfs_whole_parent_map, fun c => rfl, s₀, hs₀, ell, hell, htend, ?_⟩
  intro c s hs x y
  let gs : SmoothRiemannianMetric ThreeModel (G.Parent c).Carrier :=
    (H.stage i.castSucc).componentMetric ((H.event i).incoming.flow.base.metric s)
      (G.transition.childParent c)
  let hc : SmoothRiemannianMetric ThreeModel (G.Child c).Carrier :=
    (H.stage i.succ).componentMetric (H.event i).outputMetric c
  have hL : (0 : ℝ) ≤ ell s := le_trans zero_le_one (hell s hs)
  have hlocFull : ∀ x : (G.Parent c).Carrier, ∃ U ∈ 𝓝 x,
      ∀ (a b : ℝ) (γ : ℝ → (G.Parent c).Carrier),
        a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
        riemannianCurveLength gs γ a b ≠ ⊤ →
        riemannianCurveLength hc (fun t => (Kc c).rfs_whole_parent_map (γ t)) a b ≤
          ENNReal.ofReal (ell s) * riemannianCurveLength gs γ a b := by
    intro x
    by_cases hx : x ∈ (Kc c).support.region
    · obtain ⟨U, hU, hU'⟩ := hloc c s hs x hx
      exact ⟨U, hU, hU'⟩
    · obtain ⟨U, hU, hconst⟩ := (Kc c).rfs_whole_parent_map_locallyConstant_of_notMem hx
      refine ⟨U, hU, fun a b γ hab hγ hmap hfin => ?_⟩
      have hone : ∀ t ∈ Icc a b, (fun t => (Kc c).rfs_whole_parent_map (γ t)) t =
          (Kc c).rfs_whole_parent_map x :=
        fun t ht => hconst (γ t) (hmap ht)
      have hzero := riemannianCurveLength_eq_zero_of_apply_eq_const (g := hc)
        (γ := fun t => (Kc c).rfs_whole_parent_map (γ t))
        (a := a) (b := b) (q := (Kc c).rfs_whole_parent_map x) hone
      rw [hzero]
      exact bot_le
  let : SecondCountableTopology (G.Parent c).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (G.Parent c).Carrier
  let : SecondCountableTopology (G.Child c).Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace (G.Child c).Carrier
  by_cases hfin : riemannianEDistOf gs x y = ⊤
  · rw [hfin, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr
      (lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) (hell s hs))))]
    exact le_top
  · have hlocCoe : ∀ x : (G.Parent c).Carrier, ∃ U ∈ 𝓝 x,
        ∀ (a b : ℝ) (γ : ℝ → (G.Parent c).Carrier),
          a ≤ b → ContinuousOn γ (Icc a b) → MapsTo γ (Icc a b) U →
          riemannianCurveLength gs γ a b ≠ ⊤ →
          riemannianCurveLength hc (fun t => (Kc c).rfs_whole_parent_map (γ t)) a b ≤
            ↑(NNReal.mk (ell s) hL) * riemannianCurveLength gs γ a b :=
      fun x => by
        obtain ⟨U, hU, hU'⟩ := hlocFull x
        exact ⟨U, hU, fun a b γ hab hγ hmap hfin => by
          simpa only [ENNReal.ofReal_eq_coe_nnreal hL] using hU' a b γ hab hγ hmap hfin⟩
    have h := rfs_local_to_global_length_of_ne_top gs hc
      ((Kc c).rfs_whole_parent_map) (NNReal.mk (ell s) hL) hlocCoe hfin
    rwa [ENNReal.ofReal_eq_coe_nnreal hL]

theorem rfs_child_comparison_metric_of_exists_local_length_comparison
    (h : ∃ Kc : (c : ConnectedComponents (H.stage i.succ).Carrier) → G.ComparisonSupport c,
      G.LocalLengthComparison Kc) :
    ∃ f : (c : ConnectedComponents (H.stage i.succ).Carrier) →
        C((G.Parent c).Carrier, (G.Child c).Carrier),
      (∀ c, ∃ K : G.ComparisonSupport c, f c = K.rfs_whole_parent_map) ∧
      ∃ s₀ ∈ Ico (H.time i.castSucc) (H.time i.succ), ∃ ell : ℝ → ℝ,
        (∀ s ∈ Ioo s₀ (H.time i.succ), 1 ≤ ell s) ∧
        Filter.Tendsto ell (𝓝[<] (H.time i.succ)) (𝓝 1) ∧
        ∀ c, ∀ s ∈ Ioo s₀ (H.time i.succ), ∀ x y : (G.Parent c).Carrier,
          riemannianEDistOf ((H.stage i.succ).componentMetric (H.event i).outputMetric c)
            (f c x) (f c y) ≤ ENNReal.ofReal (ell s) *
            riemannianEDistOf ((H.stage i.castSucc).componentMetric
              ((H.event i).incoming.flow.base.metric s) (G.transition.childParent c)) x y := by
  obtain ⟨Kc, hKc⟩ := h
  obtain ⟨f, hf, hrest⟩ := rfs_child_comparison_metric_of_local_length_comparison G Kc hKc
  exact ⟨f, fun c => ⟨Kc c, hf c⟩, hrest⟩

end GeometricCutoffRecord

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
