import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessNormalizedTimeJets
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessCaptureReserve
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedIntrinsicTimeJets


set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M]

private local instance comparisonConstructionC1 : IsManifold I 1 N :=
  IsManifold.of_le (n := ∞) (by decide)


def metricComparisonOnOfGenuineTimeTowers
    (h : ℝ → SmoothRiemannianMetric I N) (g : ℝ → SmoothRiemannianMetric I3 M)
    (F : N → M) (U : Set N) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J) (order : ℕ) (eps : ℝ)
    (A B : ℕ → ℝ → Tensor0SField (I := I) (M := N) (n := ∞) 2)
    (hA₀ : ∀ s, ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace I y,
      A 0 s y v = (g s).inner (F y) (mfderiv I I3 F y (v 0)) (mfderiv I I3 F y (v 1)))
    (hB₀ : ∀ s y, ∀ v : Fin 2 → TangentSpace I y, B 0 s y v = (h s).inner y (v 0) (v 1))
    (hA : ∀ q s, s ∈ J → ∀ y ∈ U,
      HasDerivWithinAt (fun r => A q r y) (A (q + 1) s y) J s)
    (hB : ∀ q s, s ∈ J → ∀ y ∈ U,
      HasDerivWithinAt (fun r => B q r y) (B (q + 1) s y) J s)
    (hbound : ∀ a b, a + 2 * b ≤ order → ∀ s ∈ J, ∀ y ∈ U,
      tensor02CovDerivNormWith a (A b s - B b s) (h s) (h s) y ≤ eps) :
    MetricComparisonOn h g F U J order eps where
  pullback s := A 0 s
  pullback_eq := hA₀
  jet q s := A q s - B q s
  jet_zero := by
    intro s y v
    change A 0 s y v - B 0 s y v = _
    rw [hB₀]
  jet_succ := by
    intro q s hs y hy v
    have hd := ((tensor0SEvalCLM (I := I) (M := N) (x := y) v).hasFDerivAt.comp_hasDerivWithinAt
      s (hA q s hs y hy)).sub
      ((tensor0SEvalCLM (I := I) (M := N) (x := y) v).hasFDerivAt.comp_hasDerivWithinAt
        s (hB q s hs y hy))
    exact (hd.derivWithin (hJ s hs)).symm
  equivalence := by
    intro s hs y hy v
    apply quadratic_comparison_of_error_norm (h s) (A 0 s) (A 0 s - B 0 s) y ?_
      (hbound 0 0 (by simp) s hs y hy) v
    intro w
    change A 0 s y w - B 0 s y w = _
    rw [hB₀]
  close := hbound


theorem MetricComparisonOn.exists_source_capture_reserve
    (h : ℝ → SmoothRiemannianMetric I N) (g : ℝ → SmoothRiemannianMetric I3 M)
    (F : PartialDiffeomorph I I3 N M ∞) (p : N)
    {J : Set ℝ} (hzero : (0 : ℝ) ∈ J) {order : ℕ} {eps : ℝ}
    (heps : 0 < eps) (heps1 : eps < 1)
    (C : MetricComparisonOn h g F (riemannianClosedBallOf (h 0) p (modelRadius eps)) J order eps)
    (hcompact : IsCompact (riemannianClosedBallOf (h 0) p (modelRadius eps)))
    (hsource : riemannianClosedBallOf (h 0) p (modelRadius eps) ⊆ F.source) :
    ∃ eta : ℝ, 0 < eta ∧
      riemannianClosedBallOf (g 0) (F p) (modelRadius eps - 1 + eta) ⊆
        F '' riemannianClosedBallOf (h 0) p (modelRadius eps) := by
  let R := modelRadius eps
  let L := (Real.sqrt (1 - eps))⁻¹
  have hR : 0 < R := inv_pos.mpr (Real.sqrt_pos.mpr heps)
  have hL : 0 < L := inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hgap : R - 1 < R / L := by
    simpa only [R, L, div_inv_eq_mul] using modelRadius_sub_one_lt_captureRadius heps heps1
  let eta := (R / L - (R - 1)) / 2
  have heta : 0 < eta := by dsimp only [eta]; linarith
  have hr : R - 1 + eta < R / L := by dsimp only [eta]; linarith
  have hlower : ∀ y ∈ riemannianClosedBallOf (h 0) p R, ∀ v : TangentSpace I y,
      (h 0).inner y v v ≤ L ^ 2 * (g 0).inner (F y)
        (mfderiv I I3 F y v) (mfderiv I I3 F y v) := by
    intro y hy v
    have hh := (C.equivalence 0 hzero y hy v).1
    rw [C.pullback_eq 0 y hy (fun _ => v)] at hh
    have hfactor : L ^ 2 * (1 - eps) = 1 := by
      dsimp only [L]
      rw [inv_pow, Real.sq_sqrt (by linarith)]
      exact inv_mul_cancel₀ (by linarith)
    calc
      _ = L ^ 2 * ((1 - eps) * (h 0).inner y v v) := by
        rw [← mul_assoc, hfactor, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hh (sq_nonneg L)
  exact ⟨eta, heta, closedBall_subset_image_of_metric_lower_crossModel
    (h 0) (g 0) F p hR hL hr hcompact hsource hlower⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Filter Set
open DifferentialGeometry.Tensor.Coordinates DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff _root_.Topology

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem eventually_pointed_metric_comparison_on_strict_closedWindow
    {X : PointedFlowSeq.{u, 0, 0} (I := I3)}
    {P : PointedRiemannianManifold.{u, 0, 0} (I := I3)} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I3) X P phi)
    {D₀ : RealTimeInterval} (L : SolutionOn (I := I3) (M := P.M) D₀) (hL : IsSolutionOn L)
    {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hslab : Icc a b ⊆ X.D.carrier) (hregular : Ioo a b ⊆ X.D.regular)
    (hslab₀ : Icc a b ⊆ D₀.carrier) (hregular₀ : Ioo a b ⊆ D₀.regular)
    (G : ℕ → ℝ → SmoothRiemannianMetric I3 P.M)
    (hG : ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop,
      ∃ U : Set P.M, IsOpen U ∧ K ⊆ U ∧ U ⊆ Phi.source i ∧
      ∀ t : ℝ, ∀ x ∈ U, ∀ v w : TangentSpace I3 x,
        (G i t).inner x v w = ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
          (mfderiv I3 I3 (Phi.map i) x v) (mfderiv I3 I3 (Phi.map i) x w))
    (B : ℕ → ℕ → ℝ → Tensor0SField (I := I3) (M := P.M) (n := ∞) 2)
    (C : ℕ → ℝ → Tensor0SField (I := I3) (M := P.M) (n := ∞) 2)
    (hBzero : ∀ n s, B n 0 s = metricTensorField (G n s))
    (hCzero : ∀ s, C 0 s = metricTensorField (L.base.metric s))
    (hB : ∀ n q s, s ∈ Icc c b → ∀ x : P.M,
      HasDerivWithinAt (fun t => B n q t x) (B n (q + 1) s x) (Icc c b) s)
    (hC : ∀ q s, s ∈ Icc c b → ∀ x : P.M,
      HasDerivWithinAt (fun t => C q t x) (C (q + 1) s x) (Icc c b) s)
    {u v : ℝ} (huv : u < v) (hJb : Icc u v ⊆ Icc c b)
    (hgram : ∀ (p : P.M) (i j : Fin (Module.finrank ℝ ThreeSpace)), ∀ Q : Set ThreeSpace,
      IsCompact Q → Q ⊆ (extChartAt I3 p).target → ∀ r : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc u v, ∀ y ∈ Q,
        ‖iteratedFDeriv ℝ r (chartGramOnE (I := I3) (G n t) p i j) y -
          iteratedFDeriv ℝ r (chartGramOnE (I := I3) (L.base.metric t) p i j) y‖ ≤ ε)
    (K : Set P.M) (hK : IsCompact K) (order : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ i in atTop, Nonempty (MetricComparisonOn L.base.metric
      (fun t => (X.term (phi i)).S.base.metric t) (Phi.map i) K (Icc u v) order ε) := by
  classical
  have hclose : ∀ᶠ i in atTop, ∀ p q : Fin (order + 1), ∀ t ∈ Icc u v, ∀ x ∈ K,
      tensor02CovDerivNormWith (I := I3) (p : ℕ) (B i (q : ℕ) t - C (q : ℕ) t)
        (L.base.metric t) (L.base.metric t) x ≤ ε := by
    rw [Filter.eventually_all]
    intro p
    rw [Filter.eventually_all]
    intro q
    exact eventually_atTop.2 (pointed_error_jets_uniform_on_compact_closedWindow Phi L hL
      hac hcb hslab hregular hslab₀ hregular₀ G hG B C hBzero hCzero hB hC
      isCompact_Icc hJb hgram K hK p q ε hε)
  filter_upwards [hclose, hG K hK] with i hi hGi
  obtain ⟨U, _hU, hKU, _hUsource, hpair⟩ := hGi
  refine ⟨metricComparisonOnOfGenuineTimeTowers L.base.metric
    (fun t => (X.term (phi i)).S.base.metric t) (Phi.map i) K (Icc u v)
    (uniqueDiffOn_Icc huv) order ε (B i) C ?_ ?_ ?_ ?_ ?_⟩
  · intro s y hy w
    rw [hBzero i s, metricTensorField_apply]
    exact hpair s y (hKU hy) (w 0) (w 1)
  · intro s y w
    rw [hCzero s, metricTensorField_apply]
  · intro q s hs y _hy
    exact (hB i q s (hJb hs) y).mono hJb
  · intro q s hs y _hy
    exact (hC q s (hJb hs) y).mono hJb
  · intro r q hrq s hs y hy
    exact hi ⟨r, by omega⟩ ⟨q, by omega⟩ s hs y hy

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

noncomputable section
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Set Filter DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff

variable {E H N M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N] [T2Space N] [SigmaCompactSpace N]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M]

def MetricComparisonOn.singleton
    {h : ℝ → SmoothRiemannianMetric I N} {g : ℝ → SmoothRiemannianMetric I3 M}
    {F : N → M} {U : Set N} {J : Set ℝ} {order : ℕ} {eps : ℝ}
    (C : MetricComparisonOn h g F U J order eps) {t : ℝ} (ht : t ∈ J) :
    MetricComparisonOn h g F U {t} order eps := by
  let jet := fun q s => if q = 0 then C.jet 0 s else 0
  refine {
    pullback := C.pullback
    pullback_eq := C.pullback_eq
    jet := jet
    jet_zero := ?_
    jet_succ := ?_
    equivalence := ?_
    close := ?_ }
  · intro s y v
    exact C.jet_zero s y v
  · intro q s hs y _hy v
    obtain rfl := mem_singleton_iff.mp hs
    simp only [jet, if_neg (Nat.add_one_ne_zero q)]
    change 0 = derivWithin (fun a => (if q = 0 then C.jet 0 a else 0) y v) {s} s
    symm
    apply derivWithin_zero_of_not_accPt
    rw [accPt_iff_clusterPt, inf_principal]
    simp [ClusterPt]
  · intro s hs y hy v
    obtain rfl := mem_singleton_iff.mp hs
    exact C.equivalence _ ht y hy v
  · intro a b hab s hs y hy
    obtain rfl := mem_singleton_iff.mp hs
    by_cases hb : b = 0
    · simpa only [jet, if_pos hb] using C.close a 0 (by omega) _ ht y hy
    · have heps : 0 ≤ eps :=
        (Real.sqrt_nonneg _).trans (C.close 0 0 (by omega) _ ht y hy)
      simp only [jet, if_neg hb]
      rw [tensor02CovDerivNormWith, tensor02_cov_deriv_eq_cov_deriv_of_field,
        covDerivOfField_zero_tensor]
      simpa only [ContMDiffSection.coe_zero, Pi.zero_apply, normSq0S, inner0S,
        MetricFiberData.inner, map_zero, Real.sqrt_zero] using heps

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
