import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalNeckRecentering
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCurvatureEscape

noncomputable section
open Set Filter Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem same_component_of_finite_terminal_distance
    {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}
    (g : SmoothRiemannianMetric ThreeModel G.terminalRegularOpen)
    (x y : G.terminalRegularOpen) (hfinite : riemannianEDistOf g x y ≠ ⊤) :
    x.val ∈ connectedComponent y.val := by
  obtain ⟨γ, hγ0, hγ1, hγ, _⟩ := DifferentialGeometry.exists_lt_of_edistOf_lt g
    (lt_top_iff_ne_top.mpr hfinite)
  have hconn := isPreconnected_Icc.image γ hγ.continuousOn
  have hy : y ∈ connectedComponent x := hconn.subset_connectedComponent
    ⟨0, by norm_num, hγ0⟩ ⟨1, by norm_num, hγ1⟩
  have hxy : x ∈ connectedComponent y := (connectedComponent_eq hy) ▸ mem_connectedComponent
  exact continuous_subtype_val.mapsTo_connectedComponent y hxy

theorem exists_terminal_scalar_escape_spatial_necks
    (P : ℕ → OrientedThreeStage.{u}) (a s : ℕ → ℝ)
    (G : ∀ n, (P n).IncomingSlab (a n) (s n))
    (L : ∀ n, (G n).TerminalLimitMetric)
    (x : ∀ n, (G n).terminalRegularOpen)
    (Q : ℕ → ℝ) (hQ : ∀ n, 0 < Q n)
    {eps δ C1 : ℝ} (C : ℝ≥0) (hδ : 0 < δ) (hδsmall : δ < 1 / 20000)
    (hepsδ : eps < δ) (hfit : δ⁻¹ + 1 ≤ eps⁻¹)
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n) (hqQ : ∀ n, q n ≤ Q n)
    (hcanonical : ∀ n, ∀ y : (P n).Carrier, ∀ t ∈ Ioo (a n) (s n),
      q n < (G n).flow.scalar t y →
      ∃ W : CanonicalWitness (G n).flow eps C1 C y t, W.capTubeHasNeckChart eps)
    (hx : ∀ n, metricScalarAt (L n).metric (x n) ≤ Q n)
    (hfail : ∃ r : ℝ, 0 < r ∧ ¬ ∃ A : ℝ,
      ∀ᶠ n in atTop, ∀ y : (G n).terminalRegularOpen,
        riemannianEDistOf (scaleMetric (Q n) (hQ n) (L n).metric) (x n) y < ENNReal.ofReal r →
          metricScalarAt (L n).metric y / Q n ≤ A) :
    ∃ (R : ℝ) (ind : ℕ → ℕ), 0 < R ∧ StrictMono ind ∧
      (∀ r : ℝ, 0 < r → r < R → ∃ A : ℝ,
        ∀ᶠ n in atTop,
          IsCompact (riemannianClosedBallOf
            (scaleMetric (Q n) (hQ n) (L n).metric) (x n) r) ∧
          ∀ y : (G n).terminalRegularOpen,
            y ∈ riemannianClosedBallOf
              (scaleMetric (Q n) (hQ n) (L n).metric) (x n) r →
              metricScalarAt (L n).metric y / Q n ≤ A) ∧
      ∃ v : ∀ n, (G (ind n)).terminalRegularOpen,
        (∀ n, Nonempty (SpatialNeck (L (ind n)).metric δ (v n))) ∧
        (∀ n, riemannianEDistOf
          (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric) (x (ind n)) (v n) ≠ ⊤) ∧
        Tendsto (fun n => (riemannianEDistOf
          (scaleMetric (Q (ind n)) (hQ (ind n)) (L (ind n)).metric) (x (ind n)) (v n)).toReal)
          atTop (𝓝 R) ∧
        Tendsto (fun n => metricScalarAt (L (ind n)).metric (v n) / Q (ind n)) atTop atTop := by
  classical
  obtain ⟨R, ind, hR, hind, hinner, y, hfinite, hdist, hlarge⟩ :=
    exists_terminal_scalar_escape_radius P a s G L x Q hQ C q hqQ
      (fun n y t ht hy => ⟨(hcanonical n y t ht hy).choose⟩) hx hfail
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlarge.eventually_gt_atTop (max (1 : ℝ) C))
  let f : ℕ → ℕ := fun n => ind (n + N)
  have hf : StrictMono f := hind.comp (fun _ _ h => Nat.add_lt_add_right h N)
  have hratio (n) : max (1 : ℝ) C < metricScalarAt (L (f n)).metric (y (n + N)) / Q (f n) :=
    hN (n + N) (Nat.le_add_left N n)
  have hhigh (n) : q (f n) < metricScalarAt (L (f n)).metric (y (n + N)) := by
    have h := (lt_div_iff₀ (hQ (f n))).mp ((le_max_left 1 (C : ℝ)).trans_lt (hratio n))
    exact (hqQ (f n)).trans_lt (by simpa only [one_mul] using h)
  have hgap (n) : (C : ℝ) * metricScalarAt (L (f n)).metric (x (f n)) <
      metricScalarAt (L (f n)).metric (y (n + N)) := by
    have h := (lt_div_iff₀ (hQ (f n))).mp ((le_max_right 1 (C : ℝ)).trans_lt (hratio n))
    exact (mul_le_mul_of_nonneg_left (hx (f n)) C.coe_nonneg).trans_lt h
  have hcomp (n) : (x (f n)).val ∈ connectedComponent (y (n + N)).val :=
    same_component_of_finite_terminal_distance
      (scaleMetric (Q (f n)) (hQ (f n)) (L (f n)).metric)
      (x (f n)) (y (n + N)) (hfinite (n + N))
  obtain ⟨v, nk, _, hblow, hfinite', hdist'⟩ :=
    OrientedThreeStage.IncomingSlab.exists_spatial_neck_centers_at_escape_radius
      (fun n => P (f n)) (fun n => a (f n)) (fun n => s (f n))
      (fun n => G (f n)) (fun n => L (f n)) (fun n => y (n + N)) (fun n => x (f n))
      hδ hδsmall hepsδ hfit (fun n => q (f n)) (fun n => Q (f n))
      (fun n => hq (f n)) (fun n => hQ (f n))
      (fun n t ht hy => hcanonical (f n) (y (n + N)).val t ht hy)
      hhigh hcomp hgap (hlarge.comp (tendsto_add_atTop_nat N))
      (fun n => x (f n)) (fun n => hfinite (n + N)) (hdist.comp (tendsto_add_atTop_nat N))
  exact ⟨R, f, hR, hf, hinner, v, fun n => ⟨nk n⟩, hfinite', hdist', hblow⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
