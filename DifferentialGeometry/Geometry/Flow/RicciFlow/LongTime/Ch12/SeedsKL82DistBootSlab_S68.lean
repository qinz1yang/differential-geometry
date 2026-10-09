import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL82ComponentDistance_CX11

/-!
# CH12-S68, Group G1: the slab distance estimate with a Ricci bound on a fixed ball only

CX11's `dist_le_of_ricci_inv_time_component_CX11` needs `Ric ≤ C/(v−a)` around both `x` and `y`
on balls of radius `√(3(v−a)/C)`.  Claim (C) of KL 82.1 only controls a fixed ball `B_v(x, R0)`
around the centre trace `x`.  Here the Ricci bound is assumed on `B_v(x, R0)` only, together with
the margin `d_{v1}(x,y) + 16√(C/3)√(v1−a) + √(3(v1−a)/C) < R0`; the second point `y` then stays
inside by a first-exit (continuous induction downwards in `v`) argument:

* `downward_bootstrap_S68`: abstract downward continuous induction on `[v0, v1]`;
* `dist_boot_slab_S68`: the good set `{u : the slab inequality holds on [u, v1]}` is closed
  (continuity of `d_v(x,y)`) and open downwards (the margin is strict, and CX11's slab inequality
  on `[u − δ, v1]`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold TopologicalSpace DifferentialGeometry
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Metric DifferentialGeometry.CheegerGromovCompactness
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch12

universe u

/-- Downward continuous induction: if `Q` is closed on `[v0, v1]`, holds at `v1`, and propagates
a little to the left of every `u` such that it holds on `[u, v1]`, then it holds on `[v0, v1]`. -/
theorem downward_bootstrap_S68 {v0 v1 : ℝ} (hv01 : v0 ≤ v1) (Q : ℝ → Prop)
    (hclosed : IsClosed (Icc v0 v1 ∩ {v | Q v})) (h1 : Q v1)
    (hstep : ∀ u ∈ Ioc v0 v1, (∀ v ∈ Icc u v1, Q v) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ Icc v0 v1, u - δ ≤ v → Q v) :
    ∀ v ∈ Icc v0 v1, Q v := by
  let G : Set ℝ := {u | v0 ≤ u ∧ ∀ v ∈ Icc u v1, Q v}
  have hv1G : v1 ∈ G := ⟨hv01, fun v hv => by rwa [le_antisymm hv.2 hv.1]⟩
  have hne : G.Nonempty := ⟨v1, hv1G⟩
  have hbdd : BddBelow G := ⟨v0, fun u hu => hu.1⟩
  have hu0v0 : v0 ≤ sInf G := le_csInf hne (fun u hu => hu.1)
  have hu0v1 : sInf G ≤ v1 := csInf_le hbdd hv1G
  have hQgt : ∀ v, sInf G < v → v ≤ v1 → Q v := by
    intro v hv hv1
    obtain ⟨u, huG, hu⟩ := exists_lt_of_csInf_lt hne hv
    exact huG.2 v ⟨hu.le, hv1⟩
  have hQu0 : Q (sInf G) := by
    rcases eq_or_lt_of_le hu0v1 with h | h
    · rw [h]; exact h1
    · have hcl : sInf G ∈ closure (Ioc (sInf G) v1) := by
        rw [closure_Ioc h.ne]; exact ⟨le_rfl, h.le⟩
      have hsub : Ioc (sInf G) v1 ⊆ Icc v0 v1 ∩ {v | Q v} := fun v hv =>
        ⟨⟨hu0v0.trans hv.1.le, hv.2⟩, hQgt v hv.1 hv.2⟩
      exact (hclosed.closure_subset_iff.mpr hsub hcl).2
  have hu0G : sInf G ∈ G := ⟨hu0v0, fun v hv => by
    rcases eq_or_lt_of_le hv.1 with h | h
    · rw [← h]; exact hQu0
    · exact hQgt v h hv.2⟩
  have hv0 : sInf G = v0 := by
    by_contra hne'
    have hlt : v0 < sInf G := lt_of_le_of_ne hu0v0 (Ne.symm hne')
    obtain ⟨δ, hδ, hstep'⟩ := hstep (sInf G) ⟨hlt, hu0v1⟩ hu0G.2
    have hu1G : max v0 (sInf G - δ) ∈ G := ⟨le_max_left _ _, fun v hv =>
      hstep' v ⟨(le_max_left _ _).trans hv.1, hv.2⟩ ((le_max_right _ _).trans hv.1)⟩
    have h1' := csInf_le hbdd hu1G
    have h2' : max v0 (sInf G - δ) < sInf G := max_lt hlt (by linarith)
    linarith
  intro v hv
  exact hu0G.2 v ⟨hv0 ▸ hv.1, hv.2⟩

/-- Two points in the same connected component are at finite Riemannian distance. -/
theorem edist_ne_top_component_S68 {M : Type u} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (x y : M) (hy : y ∈ connectedComponent x) :
    riemannianEDistOf g x y ≠ ⊤ := by
  let U := connectedComponentOpen (I := ThreeModel) x
  let : ConnectedSpace U := connectedComponentOpen_connectedSpace (I := ThreeModel) x
  let xU : U := ⟨x, mem_connectedComponent⟩
  let yU : U := ⟨y, hy⟩
  have h := riemannianEDistOf_ne_top (g.restrictOpen U) xU yU
  rwa [edistOf_restrictOpen_connCompOpen g x xU yU] at h

/-- Continuity of `v ↦ d_v(x, y)` on one component of a possibly disconnected manifold
(derived from the solution and completeness, as in CX11's component slab). -/
theorem continuousOn_dist_component_S68
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := M) D)
    (hS : IsSolutionOn S) {v0 v1 : ℝ} (hcar : Icc v0 v1 ⊆ D.carrier)
    (hcomplete : ∀ v ∈ Icc v0 v1, RiemannianMetricComplete (S.base.metric v))
    (x y : M) (hy : y ∈ connectedComponent x) :
    ContinuousOn (fun v => (riemannianEDistOf (S.base.metric v) x y).toReal) (Icc v0 v1) := by
  let U := connectedComponentOpen (I := ThreeModel) x
  let : ConnectedSpace U := connectedComponentOpen_connectedSpace (I := ThreeModel) x
  let : SigmaCompactSpace U :=
    (show IsClosed (U : Set M) from isClosed_connectedComponent).sigmaCompactSpace
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let xU : U := ⟨x, mem_connectedComponent⟩
  let yU : U := ⟨y, hy⟩
  let S' := solutionOnRestrictOpen S U
  have hS' : IsSolutionOn S' := isSolutionOn_restrictOpen S hS U
  have hcomp (v : ℝ) (hv : v ∈ Icc v0 v1) : RiemannianMetricComplete (S'.base.metric v) :=
    riemannianMetricComplete_restrictOpen_connCompOpen (S.base.metric v) x (hcomplete v hv)
  have hd (v : ℝ) (p q : U) :
      riemannianEDistOf (S'.base.metric v) p q = riemannianEDistOf (S.base.metric v) p.val q.val :=
    edistOf_restrictOpen_connCompOpen (S.base.metric v) x p q
  have hc := continuousOn_riemannianEDistOf S'.base.metric ordConnected_Icc
    (hS'.smoothMetric.metricTensor_cont.mono hcar) hcomp xU
  have hc' : ContinuousOn (fun v => riemannianEDistOf (S'.base.metric v) xU yU) (Icc v0 v1) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ hv => ⟨hv, mem_univ _⟩)
  have hcR : ContinuousOn (fun v => (riemannianEDistOf (S'.base.metric v) xU yU).toReal)
      (Icc v0 v1) := by
    intro v hv
    exact (ENNReal.continuousAt_toReal (riemannianEDistOf_ne_top (S'.base.metric v) xU yU)).comp_continuousWithinAt
      (f := fun r => riemannianEDistOf (S'.base.metric r) xU yU) (hc' v hv)
  simpa only [hd] using hcR

/-- **G1 (slab, ball form).**  CX11's component slab estimate with the Ricci bound
`Ric ≤ C/(v−a)` assumed only on `B_v(x, R0)`; the margin keeps `y`'s `√(3(v−a)/C)`-ball inside it.
The conclusion holds for every `v ∈ [v0, v1]`. -/
theorem dist_boot_slab_S68
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] [SigmaCompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := ThreeModel) (M := M) D)
    (hS : IsSolutionOn S) {a v0 v1 C R0 : ℝ} (hC : 0 < C) (hav0 : a ≤ v0)
    (hv01 : v0 ≤ v1) (hcar : Icc v0 v1 ⊆ D.carrier) (hreg : Ioc v0 v1 ⊆ D.regular)
    (hcomplete : ∀ v ∈ Icc v0 v1, RiemannianMetricComplete (S.base.metric v))
    (x y : M) (hy : y ∈ connectedComponent x)
    (hmargin : (riemannianEDistOf (S.base.metric v1) x y).toReal +
      16 * Real.sqrt (C / 3) * Real.sqrt (v1 - a) + Real.sqrt (3 * (v1 - a) / C) < R0)
    (hRic : ∀ v ∈ Ioc v0 v1, ∀ z : M, ∀ w : TangentSpace ThreeModel z,
      riemannianEDistOf (S.base.metric v) x z < ENNReal.ofReal R0 →
      ricciTensor (S.base.metric v) z w w ≤ C / (v - a) * (S.base.metric v).inner z w w) :
    ∀ v ∈ Icc v0 v1,
      (riemannianEDistOf (S.base.metric v) x y).toReal +
          16 * Real.sqrt (C / 3) * Real.sqrt (v - a) ≤
        (riemannianEDistOf (S.base.metric v1) x y).toReal +
          16 * Real.sqrt (C / 3) * Real.sqrt (v1 - a) := by
  let d : ℝ → ℝ := fun v => (riemannianEDistOf (S.base.metric v) x y).toReal
  let r : ℝ → ℝ := fun v => Real.sqrt (3 * (v - a) / C)
  let Q : ℝ → Prop := fun v =>
    d v + 16 * Real.sqrt (C / 3) * Real.sqrt (v - a) ≤
      d v1 + 16 * Real.sqrt (C / 3) * Real.sqrt (v1 - a)
  have hd0 : ∀ v, 0 ≤ d v := fun v => ENNReal.toReal_nonneg
  have hcont : ContinuousOn d (Icc v0 v1) :=
    continuousOn_dist_component_S68 S hS hcar hcomplete x y hy
  have hcQ : ContinuousOn (fun v => d v + 16 * Real.sqrt (C / 3) * Real.sqrt (v - a))
      (Icc v0 v1) := hcont.add (by fun_prop : Continuous
        fun v : ℝ => 16 * Real.sqrt (C / 3) * Real.sqrt (v - a)).continuousOn
  have hcg : ContinuousOn (fun v => d v + r v) (Icc v0 v1) :=
    hcont.add (by fun_prop : Continuous fun v : ℝ => r v).continuousOn
  have hrmono : ∀ v, v ≤ v1 → r v ≤ r v1 := fun v hv => by
    apply Real.sqrt_le_sqrt
    have := div_le_div_of_nonneg_right (by linarith : 3 * (v - a) ≤ 3 * (v1 - a)) hC.le
    exact this
  -- the Ricci bound on `x`'s `R0`-ball gives it on both balls of radius `r v`, if `d v + r v < R0`
  have hcover : ∀ v ∈ Ioc v0 v1, d v + r v < R0 → ∀ z : M, ∀ w : TangentSpace ThreeModel z,
      (riemannianEDistOf (S.base.metric v) x z < ENNReal.ofReal (r v) ∨
        riemannianEDistOf (S.base.metric v) y z < ENNReal.ofReal (r v)) →
      ricciTensor (S.base.metric v) z w w ≤ C / (v - a) * (S.base.metric v).inner z w w := by
    intro v hv hlt z w hz
    have hr0 : 0 ≤ r v := Real.sqrt_nonneg _
    have hR0 : 0 < R0 := by linarith [hd0 v]
    apply hRic v hv z w
    rcases hz with hz | hz
    · exact hz.trans_le (ENNReal.ofReal_le_ofReal (by linarith [hd0 v]))
    · have hfin := edist_ne_top_component_S68 (S.base.metric v) x y hy
      have h1 : riemannianEDistOf (S.base.metric v) x z ≤
          riemannianEDistOf (S.base.metric v) x y + riemannianEDistOf (S.base.metric v) y z :=
        riemannianEDistOf_triangle _ x y z
      have h2 : riemannianEDistOf (S.base.metric v) x y + riemannianEDistOf (S.base.metric v) y z <
          riemannianEDistOf (S.base.metric v) x y + ENNReal.ofReal (r v) :=
        ENNReal.add_lt_add_left hfin hz
      have h3 : riemannianEDistOf (S.base.metric v) x y + ENNReal.ofReal (r v) =
          ENNReal.ofReal (d v + r v) := by
        rw [ENNReal.ofReal_add (hd0 v) hr0]
        congr 1
        exact (ENNReal.ofReal_toReal hfin).symm
      rw [h3] at h2
      exact (h1.trans_lt h2).trans ((ENNReal.ofReal_lt_ofReal_iff hR0).mpr hlt)
  have hstep : ∀ u ∈ Ioc v0 v1, (∀ v ∈ Icc u v1, Q v) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ Icc v0 v1, u - δ ≤ v → Q v := by
    intro u hu hQ
    have hpt : ∀ v ∈ Icc u v1, d v + r v < R0 := by
      intro v hv
      have h1 := hQ v hv
      have h2 := hrmono v hv.2
      have h3 : 0 ≤ 16 * Real.sqrt (C / 3) * Real.sqrt (v - a) := by positivity
      simp only [Q] at h1
      have : d v + r v ≤ d v1 + 16 * Real.sqrt (C / 3) * Real.sqrt (v1 - a) + r v1 := by
        linarith
      exact this.trans_lt hmargin
    have humem : u ∈ Icc v0 v1 := ⟨hu.1.le, hu.2⟩
    have hev : ∀ᶠ v in 𝓝[Icc v0 v1] u, d v + r v < R0 :=
      (hcg u humem).eventually (Iio_mem_nhds (hpt u ⟨le_rfl, hu.2⟩))
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hev
    refine ⟨ε, hε, ?_⟩
    intro v hv hvu
    rcases le_or_gt u v with huv | huv
    · exact hQ v ⟨huv, hv.2⟩
    · have hall : ∀ v' ∈ Ioc v v1, d v' + r v' < R0 := by
        intro v' hv'
        rcases le_or_gt u v' with h | h
        · exact hpt v' ⟨h, hv'.2⟩
        · have hmem : v' ∈ Metric.ball u ε ∩ Icc v0 v1 := by
            refine ⟨?_, ⟨hv.1.trans hv'.1.le, hv'.2⟩⟩
            rw [Metric.mem_ball, Real.dist_eq, abs_lt]
            constructor <;> linarith [hv'.1]
          exact hsub hmem
      have hav : a ≤ v := hav0.trans hv.1
      exact dist_le_of_ricci_inv_time_component_CX11 S hS hC hav hv.2
        (fun z hz => hcar ⟨hv.1.trans hz.1, hz.2⟩) (fun z hz => hreg ⟨hv.1.trans_lt hz.1, hz.2⟩)
        (fun z hz => hcomplete z ⟨hv.1.trans hz.1, hz.2⟩) x y hy
        (fun v' hv' z w hz => hcover v' ⟨hv.1.trans_lt hv'.1, hv'.2⟩ (hall v' hv') z w hz)
  exact downward_bootstrap_S68 hv01 Q
    (hcQ.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic) le_rfl hstep

end GC.LongTime.Ch12
