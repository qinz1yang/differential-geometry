import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.NodeSplicing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.C1Integrability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Attainment

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Filter Function Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {D : RealTimeInterval}

section Prefix

variable {M : Type u} [UniformSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M]

omit [CompactSpace M] in
theorem lReg_prefix_min
    (S : SolutionOn (I := I) (M := M) D)
    (hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric)
    (hSc : ScalarSTContOn (I := I) (M := M) S)
    (T a c b : Real) (hac : a < c) (hcb : c < b)
    (gamma : Real → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc a b))
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegAction S T gamma a b ≤ lRegAction S T delta a b) :
    ∀ delta : Real → M,
      ContMDiffOn (modelWithCornersSelf Real Real) I 1 delta (Icc a c) →
      delta a = gamma a → delta c = gamma c →
      lRegAction S T gamma a c ≤ lRegAction S T delta a c := by
  intro delta hdelta hda hdc
  have hgammaTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc c b) := hgamma.mono (by
    intro s hs
    exact ⟨hac.le.trans hs.1, hs.2⟩)
  obtain ⟨eta, m, t, p, u, hetaDelta, hetaGamma, htmono, ht0, htlast,
      _hc, hsrc, hrep⟩ :=
    exists_chartH1_join (I := I) a c b hac hcb delta gamma
      hdelta hgammaTail hdc
  obtain ⟨alpha, _w, halpha, halphaa, halphab, _hsrcAlpha, _hrepAlpha,
      _hw, _hunif, haction⟩ :=
    lAction_c1_dense (I := I) S hMet hSc T a b t htmono ht0 htlast p eta u
      hsrc hrep hreg
  have hetaA : eta a = gamma a :=
    (hetaDelta ⟨le_rfl, hac.le⟩).trans hda
  have hetaB : eta b = gamma b := hetaGamma ⟨hcb.le, le_rfl⟩
  have hwhole : lRegAction S T gamma a b ≤ lRegAction S T eta a b := by
    apply ge_of_tendsto haction
    exact Eventually.of_forall fun n ↦
      hmin (alpha n) (halpha n) ((halphaa n).trans hetaA)
        ((halphab n).trans hetaB)
  have hregAC : ∀ s ∈ Icc a c, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hs.1, hs.2.trans hcb.le⟩
  have hregCB : ∀ s ∈ Icc c b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact hreg s ⟨hac.le.trans hs.1, hs.2⟩
  have hgammaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc a c) := hgamma.mono (by
    intro s hs
    exact ⟨hs.1, hs.2.trans hcb.le⟩)
  have hetaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
      (Icc a c) := hdelta.congr fun s hs ↦ hetaDelta hs
  have hetaTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 eta
      (Icc c b) := hgammaTail.congr fun s hs ↦ hetaGamma hs
  have hgammaIntAC :=
    lRegLag_int_c1 (I := I) S hMet hSc T a c hac.le gamma hgammaHead hregAC
  have hgammaIntCB :=
    lRegLag_int_c1 (I := I) S hMet hSc T c b hcb.le gamma hgammaTail hregCB
  have hetaIntAC :=
    lRegLag_int_c1 (I := I) S hMet hSc T a c hac.le eta hetaHead hregAC
  have hetaIntCB :=
    lRegLag_int_c1 (I := I) S hMet hSc T c b hcb.le eta hetaTail hregCB
  have hgammaAdd :=
    lRegAction_add (I := I) S T gamma a c b hgammaIntAC hgammaIntCB
  have hetaAdd := lRegAction_add (I := I) S T eta a c b hetaIntAC hetaIntCB
  have hetaAC : lRegAction S T eta a c = lRegAction S T delta a c := by
    apply lRegAction_congr (I := I) S T
    intro s hs
    have hs' : s ∈ Ioo a c := by
      simpa only [uIoo_of_le hac.le] using hs
    exact hetaDelta ⟨hs'.1.le, hs'.2.le⟩
  have hetaCB : lRegAction S T eta c b = lRegAction S T gamma c b := by
    apply lRegAction_congr (I := I) S T
    intro s hs
    have hs' : s ∈ Ioo c b := by
      simpa only [uIoo_of_le hcb.le] using hs
    exact hetaGamma ⟨hs'.1.le, hs'.2.le⟩
  rw [← hgammaAdd, ← hetaAdd, hetaAC, hetaCB] at hwhole
  linarith

end Prefix

section Compact

variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

theorem lRegCostC1_eq_on
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T t0 t1 a b : Real) (hab : a < b)
    (htime : Icc t0 t1 ⊆ D.carrier)
    (hback : ∀ s ∈ Icc a b, T - s ^ 2 ∈ Icc t0 t1)
    (x y : M) (gamma : Real → M)
    (hgamma : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc a b))
    (hga : gamma a = x) (hgb : gamma b = y)
    (hreg : ∀ s ∈ Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = x → delta b = y →
      lRegAction S T gamma a b ≤ lRegAction S T delta a b) :
    lRegAction S T gamma a b = lRegCostC1 S T a b x y := by
  let c : Real := (a + b) / 2
  have hac : a < c := by
    simp only [c]
    linarith
  have hcb : c < b := by
    simp only [c]
    linarith
  have hgammaHead : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc a c) := hgamma.mono (by
    intro s hs
    exact ⟨hs.1, hs.2.trans hcb.le⟩)
  have hgammaTail : ContMDiffOn (modelWithCornersSelf Real Real) I 1 gamma
      (Icc c b) := hgamma.mono (by
    intro s hs
    exact ⟨hac.le.trans hs.1, hs.2⟩)
  obtain ⟨eta, m, t, p, u, hetaHead, hetaTail, htmono, ht0, htlast,
      _hc, hsrc, hrep⟩ :=
    exists_chartH1_join (I := I) a c b hac hcb gamma gamma
      hgammaHead hgammaTail rfl
  have hMet : MetricFamilySmoothOn (I := I) (M := M) D S.family.metric :=
    hS.smoothMetric
  have hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  obtain ⟨alpha, _w, halpha, halphaa, halphab, _hsrcAlpha, _hrepAlpha,
      _hw, _hunif, haction⟩ :=
    lAction_c1_dense (I := I) S hMet hSc T a b t htmono ht0 htlast p eta u
      hsrc hrep hreg
  have hetaA : eta a = x := (hetaHead ⟨le_rfl, hac.le⟩).trans hga
  have hetaB : eta b = y := (hetaTail ⟨hcb.le, le_rfl⟩).trans hgb
  have hetaEq : lRegAction S T eta a b = lRegAction S T gamma a b := by
    apply lRegAction_congr (I := I) S T
    intro s hs
    have hs' : s ∈ Ioo a b := by
      simpa only [uIoo_of_le hab.le] using hs
    by_cases hsc : s ≤ c
    · exact hetaHead ⟨hs'.1.le, hsc⟩
    · exact hetaTail ⟨(lt_of_not_ge hsc).le, hs'.2.le⟩
  have hcostGamma : lRegCostC1 S T a b x y ≤ lRegAction S T gamma a b := by
    rw [← hetaEq]
    apply ge_of_tendsto haction
    exact Eventually.of_forall fun n ↦
      lRegCostC1_le (I := I) S hS T t0 t1 a b hab.le htime hback x y
        (alpha n) (halpha n) ((halphaa n).trans hetaA)
        ((halphab n).trans hetaB) hreg
  have hcosts : {r : Real | ∃ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta ∧
        delta a = x ∧ delta b = y ∧ lRegAction S T delta a b = r}.Nonempty := by
    refine ⟨lRegAction S T (alpha 0) a b, alpha 0, halpha 0,
      (halphaa 0).trans hetaA, (halphab 0).trans hetaB, rfl⟩
  have hgammaCost : lRegAction S T gamma a b ≤ lRegCostC1 S T a b x y := by
    change lRegAction S T gamma a b ≤ sInf {r : Real | ∃ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta ∧
        delta a = x ∧ delta b = y ∧ lRegAction S T delta a b = r}
    apply le_csInf hcosts
    intro r hr
    obtain ⟨delta, hdelta, hda, hdb, rfl⟩ := hr
    exact hmin delta hdelta hda hdb
  exact le_antisymm hgammaCost hcostGamma

end Compact

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
