import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.PairwiseApproximation.PrescribedRadii
import DifferentialGeometry.Analysis.Calculus.Compactness.DiagonalSubsequence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.PointedBallImage
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Chain

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff _root_.Topology

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_subsequence_metric_approximation_maps_on_radii
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    (r R ε : ℕ → ℝ) (p : ℕ → ℕ)
    (hr : ∀ n, 0 ≤ r n) (hrR : ∀ n, r n < R n)
    (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n < 1)
    (hjets : ∀ n p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint (R n) p C)
    (hinj : ∀ n, ∃ η : ℝ, 0 < η ∧
      ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
        riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
          ENNReal.ofReal (r n) → HasInjRadiusAt (I := I) (X.obj k) x η) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ Ψ : ∀ n, PartialDiffeomorph I I (X.obj (σ n)).M (X.obj (σ (n + 1))).M ∞,
        ∀ n, Ψ n (X.obj (σ n)).basepoint = (X.obj (σ (n + 1))).basepoint ∧
          Nonempty (PartialDiffeomorphMetricApproximation
            (riemannianClosedBallOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint (r n))
            (ε n) (p n) (Ψ n) (X.obj (σ n)).metric (X.obj (σ (n + 1))).metric) := by
  classical
  obtain ⟨phi, hphi, hpair⟩ :=
    exists_subsequence_pairwise_metric_approximation_on_radii X hcomplete hconn r R hr hrR
      hjets hinj
  choose N hN using fun n => hpair n (ε n) (hε n) (hε1 n) (p n)
  obtain ⟨tau, htau, hNtau⟩ := exists_strictMono_ge N
  have hmaps : ∀ n, ∃ Ψ : PartialDiffeomorph I I (X.obj (phi (tau n))).M
      (X.obj (phi (tau (n + 1)))).M ∞,
      Ψ (X.obj (phi (tau n))).basepoint = (X.obj (phi (tau (n + 1)))).basepoint ∧
        Nonempty (PartialDiffeomorphMetricApproximation
          (riemannianClosedBallOf (X.obj (phi (tau n))).metric
            (X.obj (phi (tau n))).basepoint (r n))
          (ε n) (p n) Ψ (X.obj (phi (tau n))).metric
            (X.obj (phi (tau (n + 1)))).metric) := by
    intro n
    exact hN n (tau n) (tau (n + 1)) (hNtau n)
      ((hNtau n).trans (htau.monotone (Nat.le_succ n)))
  choose Ψ hbase hdata using hmaps
  exact ⟨phi ∘ tau, hphi.comp htau, Ψ, fun n => ⟨hbase n, hdata n⟩⟩

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem exists_radius_error {r R ε : ℝ} (hr : 0 < r) (hrR : r < R)
    (hε : 0 < ε) (n : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ ≤ ε ∧ δ ≤ (1 / 2 : ℝ) ^ (n + 1) ∧
      Real.sqrt (1 + δ) * r < R := by
  let δ := min ε (min ((1 / 2 : ℝ) ^ (n + 1)) ((R - r) / (2 * r)))
  have hδpos : 0 < δ := lt_min hε (lt_min (by positivity)
    (div_pos (sub_pos.mpr hrR) (by positivity)))
  have hδpow : δ ≤ (1 / 2 : ℝ) ^ (n + 1) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ < 1 := hδpow.trans_lt
    (pow_lt_one₀ (by norm_num) (by norm_num) (by omega))
  have hδgap : δ ≤ (R - r) / (2 * r) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hprod : δ * (2 * r) ≤ R - r := (le_div_iff₀ (by positivity)).mp hδgap
  have hsqrt : Real.sqrt (1 + δ) ≤ 1 + δ := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by linarith, by nlinarith [sq_nonneg δ]⟩
  refine ⟨δ, hδpos, hδ1, min_le_left _ _, hδpow, ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hsqrt hr.le
  nlinarith

theorem exists_subsequence_metric_approximation_chain_on_radii
    (X : PointedRiemannianSeq.{u, uE, uH} (I := I))
    (hcomplete : SeqMetricComplete (I := I) X)
    (hconn : ∀ k, ConnectedSpace (X.obj k).M)
    (s r R ε : ℕ → ℝ) (hs : ∀ n, 0 < s n) (hmono : StrictMono s)
    (hsr : ∀ n, s n < r n) (hrR : ∀ n, r n < R n) (hε : ∀ n, 0 < ε n)
    (hjets : ∀ n p : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in atTop, HasLocalCurvDerivBound (I := I)
        (X.obj k) (X.obj k).basepoint (R n) p C)
    (hinj : ∀ n, ∃ η : ℝ, 0 < η ∧
      ∀ᶠ k in atTop, ∀ x : (X.obj k).M,
        riemannianEDistOf (I := I) (X.obj k).metric (X.obj k).basepoint x ≤
          ENNReal.ofReal (r n) → HasInjRadiusAt (I := I) (X.obj k) x η) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ δ : ℕ → ℝ,
      (∀ n, 0 < δ n ∧ δ n ≤ ε n ∧ δ n ≤ (1 / 2 : ℝ) ^ (n + 1)) ∧
      ∃ Ψ : ∀ n, PartialDiffeomorph I I (X.obj (σ n)).M (X.obj (σ (n + 1))).M ∞,
        (∀ n, Ψ n (X.obj (σ n)).basepoint = (X.obj (σ (n + 1))).basepoint) ∧
        (∀ n, Nonempty (PartialDiffeomorphMetricApproximation
          (riemannianClosedBallOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint (r n))
          (δ n) n (Ψ n) (X.obj (σ n)).metric (X.obj (σ (n + 1))).metric)) ∧
        (∀ n, Set.MapsTo (Ψ n)
          (riemannianClosedBallOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint (s n))
          (riemannianBallOf (X.obj (σ (n + 1))).metric
            (X.obj (σ (n + 1))).basepoint (s (n + 1)))) ∧
        ∀ j k, riemannianClosedBallOf (X.obj (σ j)).metric
            (X.obj (σ j)).basepoint (s j) ⊆ (chainComp Ψ j k).source := by
  classical
  let m : ℕ → ℝ := fun n => min (r n) ((s n + s (n + 1)) / 2)
  have hsm : ∀ n, s n < m n := by
    intro n
    apply lt_min (hsr n)
    have hlt := hmono (Nat.lt_succ_self n)
    linarith
  have hmpos : ∀ n, 0 < m n := fun n => (hs n).trans (hsm n)
  have hmnext : ∀ n, m n < s (n + 1) := by
    intro n
    have hle : m n ≤ (s n + s (n + 1)) / 2 := min_le_right _ _
    have hlt := hmono (Nat.lt_succ_self n)
    linarith
  choose δ hδpos hδlt hδe hδpow hδrad using fun n =>
    exists_radius_error (hmpos n) (hmnext n) (hε n) n
  obtain ⟨σ, hσ, Ψ, hΨ⟩ := exists_subsequence_metric_approximation_maps_on_radii
    X hcomplete hconn r R δ id (fun n => ((hs n).trans (hsr n)).le)
      hrR hδpos hδlt hjets hinj
  let K : ∀ n, Set (X.obj (σ n)).M := fun n =>
    riemannianClosedBallOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint (s n)
  have himage : ∀ n, Set.MapsTo (Ψ n) (K n)
      (riemannianBallOf (X.obj (σ (n + 1))).metric
        (X.obj (σ (n + 1))).basepoint (s (n + 1))) := by
    intro n x hx
    apply (hΨ n).2.some.mapsTo_riemannianBallOf (hmpos n) (min_le_left _ _)
      (hδrad n) (hΨ n).1
    change riemannianEDistOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint x < _
    change riemannianEDistOf (X.obj (σ n)).metric (X.obj (σ n)).basepoint x ≤ _ at hx
    exact hx.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hmpos n)).mpr (hsm n))
  have hmaps : ∀ n, Set.MapsTo (Ψ n) (K n) (K (n + 1)) := by
    intro n x hx
    have h := himage n hx
    change riemannianEDistOf (X.obj (σ (n + 1))).metric
      (X.obj (σ (n + 1))).basepoint (Ψ n x) ≤ _
    exact h.le
  have hsource : ∀ n, K n ⊆ (Ψ n).source := fun n x hx =>
    (hΨ n).2.some.source_sub
      (riemannianClosedBallOf_mono _ _ (hsr n).le hx)
  exact ⟨σ, hσ, δ, fun n => ⟨hδpos n, hδe n, hδpow n⟩,
    Ψ, fun n => (hΨ n).1, fun n => (hΨ n).2, himage,
    subset_chainComp_source Ψ K hsource hmaps⟩

end DifferentialGeometry.CheegerGromovCompactness
