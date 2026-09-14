import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtensionTerminalInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelDistanceTransfer
import DifferentialGeometry.Geometry.Metric.Distance.Finiteness
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem recenteredScalarBoundBeyondRadius_of_pos
    {kappa sigma c c' : ℝ} {Phi : ℝ → ℝ}
    (hc : 0 < c) (hc' : 0 < c')
    (h : RecenteredScalarBoundBeyondRadius.{u} kappa sigma Phi c') :
    RecenteredScalarBoundBeyondRadius.{u} kappa sigma Phi c := by
  obtain ⟨epsStar, hepsStar, hmain⟩ := h
  refine ⟨epsStar, hepsStar, fun eps heps hle A D hA hD hrad => ?_⟩
  have hsqrtpos : 0 < Real.sqrt (1 + max A (6 * Phi 0)) :=
    Real.sqrt_pos.mpr (by linarith [le_max_left A (6 * Phi 0)])
  have hDpos : 0 < D := lt_of_lt_of_le (div_pos hc hsqrtpos) hrad.le
  have hsqpos : 0 < c' / D := div_pos hc' hDpos
  have hA'le : (c' / D) ^ 2 ≤ max (max A ((c' / D) ^ 2)) (6 * Phi 0) :=
    le_trans (le_max_right A ((c' / D) ^ 2)) (le_max_left _ _)
  have hsqrt : c' / D < Real.sqrt (1 + max (max A ((c' / D) ^ 2)) (6 * Phi 0)) := by
    have hlt : (c' / D) ^ 2 < 1 + max (max A ((c' / D) ^ 2)) (6 * Phi 0) := by linarith
    have h := Real.sqrt_lt_sqrt (sq_nonneg (c' / D)) hlt
    rwa [Real.sqrt_sq_eq_abs, abs_of_pos hsqpos] at h
  have hrad' : c' / Real.sqrt (1 + max (max A ((c' / D) ^ 2)) (6 * Phi 0)) < D := by
    have h := div_lt_div_of_pos_left hc' hsqpos hsqrt
    rwa [div_div_cancel₀ (ne_of_gt hc')] at h
  obtain ⟨C, hC⟩ := hmain eps heps hle (max A ((c' / D) ^ 2)) D
    (lt_of_lt_of_le hA (le_max_left _ _)) hD hrad'
  exact ⟨C, fun X => by
    filter_upwards [hC X] with i hi
    intro s hs z y hz hd
    exact hi s hs z y (le_trans hz (le_max_left A ((c' / D) ^ 2))) hd⟩

theorem recenteredScalarBoundBeyondRadius_iff_of_pos {kappa sigma c c' : ℝ} {Phi : ℝ → ℝ}
    (hc : 0 < c) (hc' : 0 < c') :
    RecenteredScalarBoundBeyondRadius.{u} kappa sigma Phi c ↔
      RecenteredScalarBoundBeyondRadius.{u} kappa sigma Phi c' :=
  ⟨recenteredScalarBoundBeyondRadius_of_pos hc' hc,
    recenteredScalarBoundBeyondRadius_of_pos hc hc'⟩

theorem recenteredScalarBoundBeyondRadius_iff_one {kappa sigma c : ℝ} {Phi : ℝ → ℝ}
    (hc : 0 < c) :
    RecenteredScalarBoundBeyondRadius.{u} kappa sigma Phi c ↔
      RecenteredScalarBoundBeyondRadius.{u} kappa sigma Phi 1 :=
  recenteredScalarBoundBeyondRadius_iff_of_pos hc one_pos

def RecenteredSourceBound (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ᶠ i in Filter.atTop,
        ∀ s ∈ Set.Icc (-(X.depth i / 2)) 0, ∀ z y : (X.term i).M,
          (X.term i).S.scalar s z ≤ A →
          metricDistance ((X.term i).S.base.metric s) z y ≤ D →
            (X.term i).S.scalar s y ≤ C

theorem recentered_source_bound_of_canonical_beyondRadius {kappa sigma c : ℝ} {Phi : ℝ → ℝ}
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) (hc : 0 < c)
    (hlocal : TerminalLocalPropagationBound.{u} kappa c)
    (hfar : RecenteredScalarBoundBeyondRadius.{u} kappa sigma Phi 1) :
    RecenteredSourceBound.{u} kappa sigma Phi :=
  recentered_source_bound_of_beyondRadius hsigma hPhi hc hlocal
    ((recenteredScalarBoundBeyondRadius_iff_one hc).mpr hfar)

def TerminalSliceScalarTransfer (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∃ eta : ℝ, 0 ≤ eta ∧ eta ≤ 1 / 4 ∧
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
        (J : RealTimeInterval) (B : BackwardExtension L J),
        ∀ s : ℝ, s ∈ J.carrier → ∀ K : Set L.space.M, IsCompact K →
          ∀ᶠ i in Filter.atTop, ∀ y ∈ K,
            |B.solution.scalar s y -
              (X.term (L.subseq (B.subseq i))).S.scalar s
                (L.maps.partialDiffeomorph (B.subseq i) y)| ≤ eta

theorem eventually_mem_backwardWindow {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) {s : ℝ} (hs : s ∈ J.carrier) :
    ∀ᶠ i in Filter.atTop,
      s ∈ Set.Icc (-(X.depth (L.subseq (B.subseq i)) / 2)) 0 := by
  have hcomp := B.convergence (∅ : Set L.space.M) isCompact_empty s s le_rfl
    (by simpa only [Set.Icc_self, Set.singleton_subset_iff] using hs) 0 1 one_pos
  have hsle : s ≤ 0 := by
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hcomp
    have hwin := (hN N le_rfl).1 (Set.left_mem_Icc.mpr le_rfl)
    simp only [Function.comp_apply] at hwin
    rw [X.carrier_eq (L.subseq (B.subseq N))] at hwin
    exact hwin.2
  have hσ : Filter.Tendsto (fun i => X.depth (L.subseq (B.subseq i)))
      Filter.atTop Filter.atTop :=
    X.depth_tendsto.comp (L.strictMono.tendsto_atTop.comp B.strictMono.tendsto_atTop)
  filter_upwards [hσ.eventually (Filter.eventually_ge_atTop (-(2 * s)))] with i hi
  exact ⟨by linarith, hsle⟩

theorem metricDistance_slice_transfer {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} {L : TerminalLimit X}
    {J : RealTimeInterval} (B : BackwardExtension L J) {s : ℝ} (hs : s ∈ J.carrier)
    {eps₀ rho : ℝ} (he₀ : 0 < eps₀) (he₁ : eps₀ ≤ 1 / 2) (hrho : 0 ≤ rho)
    {z y : L.space.M}
    (hd : metricDistance (B.solution.base.metric s) z y ≤ rho) :
    ∀ᶠ i in Filter.atTop,
      metricDistance ((X.term (L.subseq (B.subseq i))).S.base.metric s)
          (L.maps.partialDiffeomorph (B.subseq i) z)
          (L.maps.partialDiffeomorph (B.subseq i) y) ≤
        Real.sqrt (1 + eps₀) * rho := by
  have hR : 0 < 12 * (rho + 1) := by linarith
  have hrs : RiemannianMetricComplete (I := I3) (B.solution.base.metric s) :=
    ⟨MetricComplete.complete { L.space with metric := B.solution.base.metric s }
      (B.complete s hs)⟩
  have hK : IsCompact
      (riemannianClosedBallOf (I := I3) (B.solution.base.metric s) z (12 * (rho + 1))) :=
    RiemannianMetricComplete.closedEBall_isCompact hrs z (12 * (rho + 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (B.convergence (riemannianClosedBallOf (I := I3) (B.solution.base.metric s) z
        (12 * (rho + 1))) hK s s le_rfl
      (by simpa only [Set.Icc_self, Set.singleton_subset_iff] using hs) 4 eps₀ he₀)
  filter_upwards [Filter.eventually_ge_atTop N] with i hi
  obtain ⟨-, hsrc, hne⟩ := hN i hi
  obtain ⟨C⟩ := hne
  have hequiv : ∀ y' ∈ riemannianClosedBallOf (I := I3) (B.solution.base.metric s) z
      (12 * (rho + 1)), ∀ v : TangentSpace I3 y',
      (1 - eps₀) * (B.solution.base.metric s).inner y' v v ≤
          ((X.term (L.subseq (B.subseq i))).S.base.metric s).inner
            (L.maps.partialDiffeomorph (B.subseq i) y')
            (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq i)) y' v)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq i)) y' v) ∧
        ((X.term (L.subseq (B.subseq i))).S.base.metric s).inner
            (L.maps.partialDiffeomorph (B.subseq i) y')
            (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq i)) y' v)
            (mfderiv I3 I3 (L.maps.partialDiffeomorph (B.subseq i)) y' v) ≤
          (1 + eps₀) * (B.solution.base.metric s).inner y' v v := by
    intro y' hy' v
    have heq := C.pullback_eq s y' hy' (fun _ => v)
    have hcm := C.equivalence s (Set.left_mem_Icc.mpr le_rfl) y' hy' v
    exact ⟨hcm.1.trans (le_of_eq heq), (le_of_eq heq.symm).trans hcm.2⟩
  have hroom : Real.sqrt (1 + eps₀) * (3 * rho) <
      Real.sqrt (1 - eps₀) * (12 * (rho + 1)) := by
    have h1 : Real.sqrt (1 + eps₀) ≤ 3 / 2 := by
      have hs1 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + eps₀ by linarith)
      nlinarith [Real.sqrt_nonneg (1 + eps₀)]
    have h2 : (1 / 2 : ℝ) ≤ Real.sqrt (1 - eps₀) := by
      have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - eps₀ by linarith)
      nlinarith [Real.sqrt_nonneg (1 - eps₀)]
    have hL : Real.sqrt (1 + eps₀) * (3 * rho) ≤ (3 / 2) * (3 * rho) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have hRu : (1 / 2 : ℝ) * (12 * (rho + 1)) ≤
        Real.sqrt (1 - eps₀) * (12 * (rho + 1)) :=
      mul_le_mul_of_nonneg_right h2 (by linarith)
    linarith
  have : PreconnectedSpace L.space.M := L.connected.toPreconnectedSpace
  have hfin : riemannianEDistOf (I := I3) (B.solution.base.metric s) z y ≠ ⊤ :=
    riemannianEDistOf_ne_top (I := I3) (B.solution.base.metric s) z y
  have hymem : y ∈ riemannianClosedBallOf (I := I3) (B.solution.base.metric s) z rho :=
    (ENNReal.le_ofReal_iff_toReal_le hfin hrho).mpr hd
  have hzmem : z ∈ riemannianClosedBallOf (I := I3) (B.solution.base.metric s) z rho :=
    (ENNReal.le_ofReal_iff_toReal_le (riemannianEDistOf_ne_top (I := I3)
      (B.solution.base.metric s) z z) hrho).mpr (by rw [riemannianEDistOf_self]; simpa using hrho)
  have hmain := (crossModel_toReal_transfer (h := B.solution.base.metric s)
    (g := (X.term (L.subseq (B.subseq i))).S.base.metric s)
    (F := L.maps.partialDiffeomorph (B.subseq i)) z hR he₀.le (by linarith) hrho hK hsrc
    hequiv hroom z hzmem y hymem).2
  exact hmain.trans (mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _))

theorem uniform_moving_slice_propagation_of_recenteredSourceBound_and_scalarTransfer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hsrc : RecenteredSourceBound.{u} kappa sigma Phi)
    (htr : TerminalSliceScalarTransfer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (J : RealTimeInterval) (B : BackwardExtension L J),
          ∀ s ∈ J.carrier, ∀ z y : L.space.M,
            B.solution.scalar s z ≤ A →
            metricDistance (B.solution.base.metric s) z y ≤ D →
              B.solution.scalar s y ≤ C := by
  obtain ⟨e₁, he₁, hsrc⟩ := hsrc
  obtain ⟨e₂, he₂, htr⟩ := htr
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps heps hle A D hD => ?_⟩
  have hle₁ : eps ≤ e₁ := le_trans hle (min_le_left _ _)
  have hle₂ : eps ≤ e₂ := le_trans hle (min_le_right _ _)
  obtain ⟨C₀, hC₀⟩ := hsrc eps heps hle₁ (A + 1) (D + 1) (by linarith)
  obtain ⟨eta, heta0, heta, htr⟩ := htr eps heps hle₂
  refine ⟨C₀ + 1, fun X L J B s hs z y hz hd => ?_⟩
  have he₀ : 0 < min (1 / 2 : ℝ) (1 / (D + 1) ^ 2) :=
    lt_min (by norm_num) (by positivity)
  have he₁' : min (1 / 2 : ℝ) (1 / (D + 1) ^ 2) ≤ 1 / 2 := min_le_left _ _
  have hsq : Real.sqrt (1 + min (1 / 2 : ℝ) (1 / (D + 1) ^ 2)) * D ≤ D + 1 := by
    have hle : min (1 / 2 : ℝ) (1 / (D + 1) ^ 2) ≤ 1 / (D + 1) ^ 2 := min_le_right _ _
    have hroot : Real.sqrt (1 + min (1 / 2 : ℝ) (1 / (D + 1) ^ 2)) ≤
        1 + 1 / (D + 1) ^ 2 := by
      have hs1 := Real.sq_sqrt
        (show (0 : ℝ) ≤ 1 + min (1 / 2 : ℝ) (1 / (D + 1) ^ 2) by positivity)
      nlinarith [Real.sqrt_nonneg (1 + min (1 / 2 : ℝ) (1 / (D + 1) ^ 2)), hle,
        sq_nonneg (1 / (D + 1) ^ 2)]
    have hpos : 0 < (D + 1) ^ 2 := by positivity
    have hkey : 1 / (D + 1) ^ 2 * D ≤ 1 := by
      have h1 : 1 / (D + 1) ^ 2 * D = D / (D + 1) ^ 2 := by ring
      rw [h1, div_le_one hpos]
      nlinarith
    calc Real.sqrt (1 + min (1 / 2 : ℝ) (1 / (D + 1) ^ 2)) * D
        ≤ (1 + 1 / (D + 1) ^ 2) * D := mul_le_mul_of_nonneg_right hroot hD
      _ = D + 1 / (D + 1) ^ 2 * D := by ring
      _ ≤ D + 1 := by linarith
  have hK : IsCompact ({z, y} : Set L.space.M) :=
    ((Set.finite_singleton y).insert z).isCompact
  have hdiag : Filter.Tendsto (fun i => L.subseq (B.subseq i)) Filter.atTop Filter.atTop :=
    L.strictMono.tendsto_atTop.comp B.strictMono.tendsto_atTop
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (((htr X L J B s hs {z, y} hK).and
        (metricDistance_slice_transfer B hs he₀ he₁' hD hd)).and
      ((hdiag.eventually (hC₀ X)).and (eventually_mem_backwardWindow B hs)))
  obtain ⟨⟨hscal, hdist⟩, hsrcAt, hwin⟩ := hN N le_rfl
  have hzK : z ∈ ({z, y} : Set L.space.M) := by simp
  have hyK : y ∈ ({z, y} : Set L.space.M) := by simp
  have hzabs := hscal z hzK
  have hyabs := hscal y hyK
  have hsrcz : (X.term (L.subseq (B.subseq N))).S.scalar s
      (L.maps.partialDiffeomorph (B.subseq N) z) ≤ A + 1 := by
    have h1 : (X.term (L.subseq (B.subseq N))).S.scalar s
        (L.maps.partialDiffeomorph (B.subseq N) z) ≤ B.solution.scalar s z + eta := by
      linarith [(abs_le.mp hzabs).1]
    linarith
  have hsrcd : metricDistance ((X.term (L.subseq (B.subseq N))).S.base.metric s)
      (L.maps.partialDiffeomorph (B.subseq N) z)
      (L.maps.partialDiffeomorph (B.subseq N) y) ≤ D + 1 :=
    le_trans hdist hsq
  have hbound := hsrcAt s hwin (L.maps.partialDiffeomorph (B.subseq N) z)
    (L.maps.partialDiffeomorph (B.subseq N) y) hsrcz hsrcd
  have hyup : B.solution.scalar s y ≤
      (X.term (L.subseq (B.subseq N))).S.scalar s
        (L.maps.partialDiffeomorph (B.subseq N) y) + eta := by
    linarith [(abs_le.mp hyabs).2]
  linarith

theorem uniform_moving_slice_propagation_of_canonical_beyondRadius_and_scalarTransfer
    {kappa sigma c : ℝ} {Phi : ℝ → ℝ}
    (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi) (hc : 0 < c)
    (hlocal : TerminalLocalPropagationBound.{u} kappa c)
    (hfar : RecenteredScalarBoundBeyondRadius.{u} kappa sigma Phi 1)
    (htr : TerminalSliceScalarTransfer.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ A D : ℝ, 0 ≤ D → ∃ C : ℝ,
        ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X)
          (J : RealTimeInterval) (B : BackwardExtension L J),
          ∀ s ∈ J.carrier, ∀ z y : L.space.M,
            B.solution.scalar s z ≤ A →
            metricDistance (B.solution.base.metric s) z y ≤ D →
              B.solution.scalar s y ≤ C :=
  uniform_moving_slice_propagation_of_recenteredSourceBound_and_scalarTransfer
    (recentered_source_bound_of_canonical_beyondRadius hsigma hPhi hc hlocal hfar) htr


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
