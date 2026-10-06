import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicDeepTruncation

set_option autoImplicit false
noncomputable section
open Set Function Filter Manifold GC.Endpoint DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff Topology
universe u
namespace GC.LongTime.CuspP1

/-- A compact subset of a finite-volume hyperbolic model lies in a Riemannian ball. -/
theorem exists_ball_of_isCompact_CPA2 {H : FiniteVolumeHyperbolicModel.{u}} {S : Set H.Carrier}
    (hS : IsCompact S) : ∃ R : ℝ, 0 < R ∧ S ⊆ riemannianBallOf H.metric H.basepoint R := by
  let B : ℕ → Set H.Carrier := fun n => riemannianBallOf H.metric H.basepoint (n : ℝ)
  have hcover : S ⊆ ⋃ n, B n := by
    intro x _
    have hfin : riemannianEDistOf H.metric H.basepoint x ≠ ⊤ :=
      riemannianEDistOf_ne_top H.metric H.basepoint x
    obtain ⟨n, hn⟩ := exists_nat_gt (riemannianEDistOf H.metric H.basepoint x).toReal
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change riemannianEDistOf H.metric H.basepoint x < ENNReal.ofReal (n : ℝ)
    have hq : (0 : ℝ) < n := lt_of_le_of_lt ENNReal.toReal_nonneg hn
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hq).mpr hn
  have hmono : Monotone B := fun m n h =>
    riemannianBallOf_mono _ _ (Nat.cast_le.mpr h)
  obtain ⟨n, hn⟩ := hS.elim_directed_cover B
    (fun n => isOpen_riemannianBallOf H.metric H.basepoint (n : ℝ)) hcover hmono.directed_le
  refine ⟨(n : ℝ) + 1, by positivity, hn.trans ?_⟩
  exact riemannianBallOf_mono _ _ (by linarith)

open GC.LongTime in
/-- The start time after which the deepened cores sit inside the advertised balls. -/
theorem exists_deepStart_CPA2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}
    (E : PersistentCuspExterior cores)
    (hclosed : ∀ i (q : Fin (E.truncation i).count), IsClosed (range ((E.truncation i).cuspMap q)))
    {b : ℝ} (hb : 2 ≤ b) :
    ∃ s : ℝ, E.start ≤ s ∧ ∀ i t, s ≤ t →
      range (deepenTruncation_CPA2 (E.truncation i) (hclosed i) hb).inclusion ⊆
        riemannianBallOf (cores.model i).metric (cores.model i).basepoint (cores.accuracy t)⁻¹ := by
  classical
  let D : (i : Fin cores.count) → HyperbolicTruncation (cores.model i) := fun i =>
    deepenTruncation_CPA2 (E.truncation i) (hclosed i) hb
  have hball : ∀ i, ∃ R : ℝ, 0 < R ∧ range (D i).inclusion ⊆
      riemannianBallOf (cores.model i).metric (cores.model i).basepoint R := fun i =>
    exists_ball_of_isCompact_CPA2 (isCompact_range (D i).inclusion.continuous)
  choose R hRpos hRball using hball
  let R₀ : ℝ := ∑ i, R i
  have hR₀ : ∀ i, R i ≤ R₀ := fun i =>
    Finset.single_le_sum (f := R) (fun j _ => (hRpos j).le) (Finset.mem_univ i)
  have hR0 : 0 ≤ R₀ := Finset.sum_nonneg fun j _ => (hRpos j).le
  obtain ⟨T₁, hT₁⟩ := cores.accuracy_decay (R₀ + 1)⁻¹ (inv_pos.mpr (by linarith))
  refine ⟨max E.start T₁, le_max_left _ _, fun i t ht => ?_⟩
  have hts : cores.start ≤ t := E.after_cores.trans ((le_max_left _ _).trans ht)
  have hpos := cores.accuracy_pos t hts
  have hlt := hT₁ t ((le_max_right _ _).trans ht)
  have hinv : R₀ + 1 < (cores.accuracy t)⁻¹ := by
    rw [lt_inv_comm₀ (show (0 : ℝ) < R₀ + 1 by linarith) hpos]
    exact hlt
  exact (hRball i).trans (riemannianBallOf_mono _ _ (by linarith [hR₀ i]))

open GC.LongTime in
/-- **Deeper exterior.** Every truncation of the exterior is replaced by its deepening. -/
def deepExterior_CPA2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}
    (E : PersistentCuspExterior cores)
    (hclosed : ∀ i (q : Fin (E.truncation i).count), IsClosed (range ((E.truncation i).cuspMap q)))
    {b : ℝ} (hb : 2 ≤ b) : PersistentCuspExterior cores where
  truncation := fun i => deepenTruncation_CPA2 (E.truncation i) (hclosed i) hb
  start := Classical.choose (exists_deepStart_CPA2 E hclosed hb)
  after_cores := E.after_cores.trans (Classical.choose_spec (exists_deepStart_CPA2 E hclosed hb)).1
  in_ball := fun i t ht =>
    (Classical.choose_spec (exists_deepStart_CPA2 E hclosed hb)).2 i t ht

open GC.LongTime in
theorem deepExterior_start_CPA2 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {K : ℕ} {cores : PersistentHyperbolicCores F K}
    (E : PersistentCuspExterior cores)
    (hclosed : ∀ i (q : Fin (E.truncation i).count), IsClosed (range ((E.truncation i).cuspMap q)))
    {b : ℝ} (hb : 2 ≤ b) : E.start ≤ (deepExterior_CPA2 E hclosed hb).start :=
  (Classical.choose_spec (exists_deepStart_CPA2 E hclosed hb)).1

end GC.LongTime.CuspP1
