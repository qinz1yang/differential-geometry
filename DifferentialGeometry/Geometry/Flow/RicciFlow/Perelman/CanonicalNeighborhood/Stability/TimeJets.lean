import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessComparisonConstruction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.IntrinsicTimeJetConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TimeJets
import DifferentialGeometry.Geometry.Metric.Convergence.Time.Lipschitz

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

private theorem exists_identity_metricComparisonOn_of_timeJets
    (h g : ℝ → SmoothRiemannianMetric I3 M) (U : Set M) {c b : ℝ} (hcb : c < b)
    (order : ℕ) (eps : ℝ) (A B : ℕ → ℝ → Tensor0SField (I := I3) (M := M) (n := ∞) 2)
    (hA₀ : ∀ s, A 0 s = metricTensorField (g s))
    (hB₀ : ∀ s, B 0 s = metricTensorField (h s))
    (hA : ∀ q s, s ∈ Icc c b → ∀ y,
      HasDerivWithinAt (fun r => A q r y) (A (q + 1) s y) (Icc c b) s)
    (hB : ∀ q s, s ∈ Icc c b → ∀ y,
      HasDerivWithinAt (fun r => B q r y) (B (q + 1) s y) (Icc c b) s)
    (hbound : ∀ i j, i + 2 * j ≤ order → ∀ s ∈ Icc c b, ∀ y ∈ U,
      tensor02CovDerivNormWith i (A j s - B j s) (h s) (h s) y ≤ eps) :
    ∃ cmp : MetricComparisonOn h g (PartialDiffeomorph.refl (I := I3) M : M → M) U
        (Icc c b) order eps,
      ∀ j s, s ∈ Icc c b → ∀ y (v : Fin 2 → TangentSpace I3 y),
        HasDerivWithinAt (fun r => cmp.jet j r y v) (cmp.jet (j + 1) s y v) (Icc c b) s := by
  refine ⟨metricComparisonOnOfGenuineTimeTowers h g _ U (Icc c b) (uniqueDiffOn_Icc hcb)
    order eps A B ?_ ?_ (fun q s hs y _ => hA q s hs y) (fun q s hs y _ => hB q s hs y)
    hbound, ?_⟩
  · intro s y _ v
    rw [hA₀, metricTensorField_apply]
    change _ = (g s).inner y (mfderiv I3 I3 (id : M → M) y (v 0))
      (mfderiv I3 I3 (id : M → M) y (v 1))
    rw [mfderiv_id]
    rfl
  · intro s y v
    rw [hB₀, metricTensorField_apply]
  · intro j s hs y v
    exact ((tensor0SEvalCLM (I := I3) (M := M) (x := y) v).hasFDerivAt.comp_hasDerivWithinAt
      s (hA j s hs y)).sub
      ((tensor0SEvalCLM (I := I3) (M := M) (x := y) v).hasFDerivAt.comp_hasDerivWithinAt
        s (hB j s hs y))

theorem exists_metricComparisonOn_of_uniform_metricDerivNorm_lt
    {D : RealTimeInterval} (S₀ : SolutionOn (I := I3) (M := M) D) (hS₀ : IsSolutionOn S₀)
    {a c b : ℝ} (hac : a < c) (hcb : c < b) (hcarrier : D.carrier = Icc a b)
    (hregular : Ioo a b ⊆ D.regular) (R : SmoothRiemannianMetric I3 M) {K : Set M}
    (hK : IsCompact K) (order : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ p : ℕ, ∀ S : SolutionOn (I := I3) (M := M) D, IsSolutionOn S →
      (∀ t ∈ Icc c b, ∀ q ≤ p, ∀ x : M,
        metricDerivNorm q (S.base.metric t) (S₀.base.metric t) R x < δ) →
      ∃ cmp : MetricComparisonOn S₀.base.metric S.base.metric
          (PartialDiffeomorph.refl (I := I3) M : M → M) K (Icc c b) order eps,
        ∀ j s, s ∈ Icc c b → ∀ y (v : Fin 2 → TangentSpace I3 y),
          HasDerivWithinAt (fun r => cmp.jet j r y v) (cmp.jet (j + 1) s y v) (Icc c b) s := by
  classical
  obtain ⟨C, hCzero, hC⟩ :=
    Perelman.KappaSolutions.exists_ordinary_metric_time_jets_on_closed_interval S₀ hS₀ hac hcb
      hcarrier hregular
  by_contra hcon
  have key : ∀ n : ℕ, ∃ S : SolutionOn (I := I3) (M := M) D, IsSolutionOn S ∧
      (∀ t ∈ Icc c b, ∀ q ≤ n, ∀ x : M,
        metricDerivNorm q (S.base.metric t) (S₀.base.metric t) R x < 1 / ((n : ℝ) + 1)) ∧
      ¬ ∃ cmp : MetricComparisonOn S₀.base.metric S.base.metric
          (PartialDiffeomorph.refl (I := I3) M : M → M) K (Icc c b) order eps,
        ∀ j s, s ∈ Icc c b → ∀ y (v : Fin 2 → TangentSpace I3 y),
          HasDerivWithinAt (fun r => cmp.jet j r y v) (cmp.jet (j + 1) s y v) (Icc c b) s := by
    intro n
    by_contra hn
    exact hcon ⟨1 / ((n : ℝ) + 1), by positivity, n, fun S hS hclose => by
      by_contra hS'
      exact hn ⟨S, hS, hclose, hS'⟩⟩
  choose S hS hclose hfail using key
  choose B hBzero hB using fun n =>
    Perelman.KappaSolutions.exists_ordinary_metric_time_jets_on_closed_interval (S n) (hS n)
      hac hcb hcarrier hregular
  have hconv : ∀ L : Set M, IsCompact L → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc c b,
        metricDerivNormSupOn L r ((S n).base.metric t) (S₀.base.metric t) R < ε := by
    intro L _ r ε hε
    obtain ⟨N₀, hN₀⟩ := exists_nat_one_div_lt hε
    refine ⟨max r N₀, fun n hn t ht => ?_⟩
    have hle : metricDerivNormSupOn L r ((S n).base.metric t) (S₀.base.metric t) R ≤
        1 / ((n : ℝ) + 1) :=
      metricDerivNormSupOn_le_of_forall L r _ _ R _ (by positivity) fun q hq x _ =>
        (hclose n t ht q (hq.trans ((le_max_left r N₀).trans hn)) x).le
    have hn₀ : (N₀ : ℝ) ≤ n := by exact_mod_cast (le_max_right r N₀).trans hn
    have hmono : 1 / ((n : ℝ) + 1) ≤ 1 / ((N₀ : ℝ) + 1) := by
      gcongr
    linarith
  have hbound (i j : ℕ) : ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc c b, ∀ x ∈ K,
      tensor02CovDerivNormWith i (B n j t - C j t) (S₀.base.metric t) (S₀.base.metric t) x ≤
        eps :=
    Perelman.KappaSolutions.metric_time_jet_errors_uniform_on_compacts_of_closed_interval
      S hS S₀ hS₀ hac hcb hcarrier hregular R hconv B C hBzero hCzero
      (fun n q t ht x => (hB n q t ht x).2) (fun q t ht x => (hC q t ht x).2) hK i j eps heps
  choose N hN using hbound
  let n := (Finset.range (order + 1)).sup fun i => (Finset.range (order + 1)).sup (N i)
  refine hfail n (exists_identity_metricComparisonOn_of_timeJets S₀.base.metric
    (S n).base.metric K hcb order eps (B n) C (hBzero n) hCzero
    (fun q s hs y => (hB n q s hs y).2) (fun q s hs y => (hC q s hs y).2) ?_)
  intro i j hij s hs y hy
  apply hN i j n ?_ s hs y hy
  exact le_trans
    (Finset.le_sup (f := N i) (Finset.mem_range.mpr (by omega)))
    (Finset.le_sup (f := fun i => (Finset.range (order + 1)).sup (N i))
      (Finset.mem_range.mpr (by omega)))

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
