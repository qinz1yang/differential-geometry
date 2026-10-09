import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalWitnessComparisonTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalToleranceMonotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelDistanceTransfer

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

section Restriction

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]

def MetricComparisonOn.restrictTimes {h : ℝ → SmoothRiemannianMetric J N}
    {g : ℝ → SmoothRiemannianMetric I3 M} {F : N → M} {U : Set N} {times times' : Set ℝ}
    {order : ℕ} {eps : ℝ} (C : MetricComparisonOn h g F U times order eps)
    (hsub : times' ⊆ times) (huniq : UniqueDiffOn ℝ times')
    (hdiff : ∀ b, ∀ s ∈ times', ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace J y,
      DifferentiableWithinAt ℝ (fun a => C.jet b a y v) times s) :
    MetricComparisonOn h g F U times' order eps where
  pullback := C.pullback
  pullback_eq := C.pullback_eq
  jet := C.jet
  jet_zero := C.jet_zero
  jet_succ b s hs y hy v := (C.jet_succ b s (hsub hs) y hy v).trans
    (derivWithin_subset hsub (huniq s hs) (hdiff b s hs y hy v)).symm
  equivalence s hs := C.equivalence s (hsub hs)
  close a b hab s hs := C.close a b hab s (hsub hs)

end Restriction

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P] [IsManifold I3 ∞ P]
  [T2Space P] [SigmaCompactSpace P]

theorem LocalCap.exists_transport_tolerance_of_metricComparisonOn
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P) D} (hS : IsSolutionOn S)
    {alpha eps a b t : ℝ} {x : P} {W : Set P} (L : LocalCap S eps x t W)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) (heps : eps ≤ neckModelTolerance alpha)
    (hab : a < b) (hwindow : ∀ i, b ≤ t - 2 * (S.scalar t (L.chain.centers i))⁻¹)
    (hslab : Icc a t ⊆ D.carrier) (hreg : Ioo a t ⊆ D.regular)
    (V : TopologicalSpace.Opens P) (hVcompact : IsCompact (closure (V : Set P)))
    {K : Set P} (hK : IsCompact K) (hKV : K ⊆ V) (hWK : W ⊆ K)
    (houter : ∀ i, ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, (L.chain.necks i).map y ∈ K) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N]
        [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N],
      ∀ {D' : RealTimeInterval} (S' : SolutionOn (I := I3) (M := N) D'), IsSolutionOn S' →
      Icc a t ⊆ D'.carrier → Ioo a t ⊆ D'.regular →
      ∀ F : PartialDiffeomorph I3 I3 P N ∞, (V : Set P) ⊆ F.source →
      MetricComparisonOn S.base.metric S'.base.metric F V (Icc b t) ⌈(2 * alpha)⁻¹⌉₊ delta →
      ∃ L' : LocalCap S' (2 * alpha) (F x) t (F '' W),
        L'.tubeMap = L.tubeMap.trans F ∧ L'.tube = F '' L.tube ∧
          L'.core.carrier = F '' L.core.carrier := by
  have hmodel : neckModelTolerance alpha < 1 / 11 :=
    (neckModelTolerance_le alpha).trans_lt (by linarith)
  have heps2 : eps ≤ 2 * alpha := heps.trans ((neckModelTolerance_le alpha).trans (by linarith))
  let L₁ := L.monoEps heps hmodel
  let L₂ := L.monoEps heps2 hsmall
  have hbuffer : ∀ i, a < t - 2 * (S.scalar t (L.chain.centers i))⁻¹ :=
    fun i => hab.trans_le (hwindow i)
  have htransport := fun i : Fin L.chain.count =>
    (L₁.chain.necks i).exists_transport_tolerance_of_metricComparisonOn hS ha hsmall
      (hbuffer i) hslab hreg V hVcompact hK hKV (houter i)
  choose delta hdelta htr using htransport
  have hne : (Finset.univ : Finset (Fin L.chain.count)).Nonempty :=
    ⟨⟨0, L.chain.count_pos⟩, Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne delta, (Finset.lt_inf'_iff hne).mpr fun i _ => hdelta i, ?_⟩
  intro N _ _ _ _ _ D' S' hS' hslab' hreg' F hF C
  have hbt : b < t := by
    have hQ := (L.chain.necks ⟨0, L.chain.count_pos⟩).Q_pos
    have h0 := hwindow ⟨0, L.chain.count_pos⟩
    have := inv_pos.mpr hQ
    linarith
  have hjet : ∀ q, ∀ y ∈ (V : Set P), ∀ v : Fin 2 → TangentSpace I3 y,
      ContDiffOn ℝ ∞ (fun s => C.jet q s y v) (Icc b t) := fun q y hy v =>
    C.jet_contDiffOn_of_solutions S hS S' hS' hab hab hbt hslab hreg hslab' hreg' q y hy v
  have hneck : ∀ i, ∃ nk' : StrongNeck S' (2 * alpha) (F (L.chain.centers i)) t,
      nk'.map = partialDiffeomorphTransMixed (L₁.chain.necks i).map F := by
    intro i
    have hQ := (L.chain.necks i).Q_pos
    have hlt : t - 2 * (S.scalar t (L.chain.centers i))⁻¹ < t := by
      have := inv_pos.mpr hQ
      linarith
    have hsub : Icc (t - 2 * (S.scalar t (L.chain.centers i))⁻¹) t ⊆ Icc b t :=
      Icc_subset_Icc_left (hwindow i)
    exact htr i N S' hS' hslab' hreg' F hF
      ((C.restrictTimes hsub (uniqueDiffOn_Icc hlt) fun q s hs y hy v =>
        ((hjet q y hy v).differentiableOn (by simp) s (hsub hs))).mono (subset_refl _) le_rfl
        (Finset.inf'_le _ (Finset.mem_univ i)))
  choose necks hmap using hneck
  have hW : W ⊆ F.source := hWK.trans (hKV.trans hF)
  have htube : L₂.tube ⊆ F.source :=
    subset_union_right.trans (L₂.union_eq.ge.trans hW)
  exact ⟨LocalCap.map L₂ F hW (orderedNeckChainTransport L₂.chain F htube necks hmap),
    rfl, rfl, rfl⟩

theorem exists_tolerance_depth_image_of_metricComparisonOn
    (h : ℝ → SmoothRiemannianMetric I3 P) (s : ℝ) (x : P) {A : Set P}
    {rho R margin : ℝ} (hmargin : 0 < margin) (hQ : 0 < metricScalarAt (h s) x)
    (hrho : 0 ≤ rho) (hroom : 3 * rho < R)
    (hcpt : IsCompact (riemannianClosedBallOf (I := I3) (h s) x R))
    (hA : A ⊆ riemannianClosedBallOf (I := I3) (h s) x rho)
    (hdeep : ∀ y ∈ A,
      10000 / Real.sqrt (metricScalarAt (h s) x) + margin ≤ metricDistance (h s) x y) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N]
        [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N]
        {g : ℝ → SmoothRiemannianMetric I3 N} {F : PartialDiffeomorph I3 I3 P N ∞}
        {U : TopologicalSpace.Opens P} {times : Set ℝ} {order : ℕ},
        MetricComparisonOn h g F U times order delta →
        riemannianClosedBallOf (I := I3) (h s) x R ⊆ U → (U : Set P) ⊆ F.source →
        s ∈ times → 2 ≤ order →
        ∀ y ∈ F '' A,
          10000 / Real.sqrt (metricScalarAt (g s) (F x)) ≤ metricDistance (g s) (F x) y := by
  set Q := metricScalarAt (h s) x
  set A₀ := 10000 / Real.sqrt Q
  set X := A₀ + margin / 2
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hA₀ : 0 < A₀ := div_pos (by norm_num) hsQ
  have hX : 0 < X := by positivity
  have hAX : A₀ < X := by
    change A₀ < A₀ + margin / 2
    linarith
  have hRpos : 0 < R := by linarith
  set Rlow := (10000 / X) ^ 2
  have hsqrtQ : Real.sqrt Q = 10000 / A₀ := by
    rw [div_div_cancel₀ (by norm_num : (10000 : ℝ) ≠ 0)]
  have hXl : 10000 / X < Real.sqrt Q := by
    rw [hsqrtQ]
    exact div_lt_div_of_pos_left (by norm_num) hA₀ hAX
  have hlowQ : Rlow < Q := by
    have h0 : 0 ≤ 10000 / X := by positivity
    calc Rlow = (10000 / X) ^ 2 := rfl
      _ < Real.sqrt Q ^ 2 := pow_lt_pow_left₀ hXl h0 (by norm_num)
      _ = Q := Real.sq_sqrt hQ.le
  obtain ⟨delta₁, hdelta₁, hscalar⟩ :=
    exists_tolerance_abs_metricScalarAt_sub_lt h s x (sub_pos.mpr hlowQ)
  have hc₁ : Continuous fun e : ℝ =>
      Real.sqrt (1 - e) * R - Real.sqrt (1 + e) * (3 * rho) := by fun_prop
  have hc₂ : Continuous fun e : ℝ => Real.sqrt (1 - e) * (A₀ + margin) - X := by fun_prop
  have h₁ : ∀ᶠ e in 𝓝 (0 : ℝ), 0 < Real.sqrt (1 - e) * R - Real.sqrt (1 + e) * (3 * rho) := by
    apply (hc₁.tendsto 0).eventually (lt_mem_nhds _)
    simp only [sub_zero, add_zero, Real.sqrt_one, one_mul]
    linarith
  have h₂ : ∀ᶠ e in 𝓝 (0 : ℝ), 0 < Real.sqrt (1 - e) * (A₀ + margin) - X := by
    apply (hc₂.tendsto 0).eventually (lt_mem_nhds _)
    simp only [sub_zero, Real.sqrt_one, one_mul, X]
    linarith
  have h0 : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < e := self_mem_nhdsWithin
  have h3 : ∀ᶠ e in 𝓝[>] (0 : ℝ), e < 1 := nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)
  have h₁' : ∀ᶠ e in 𝓝[>] (0 : ℝ),
      0 < Real.sqrt (1 - e) * R - Real.sqrt (1 + e) * (3 * rho) := nhdsWithin_le_nhds h₁
  have h₂' : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < Real.sqrt (1 - e) * (A₀ + margin) - X :=
    nhdsWithin_le_nhds h₂
  obtain ⟨e, hepos, hone, he₁, he₂⟩ := (h0.and (h3.and (h₁'.and h₂'))).exists
  refine ⟨min delta₁ e, lt_min hdelta₁ hepos, ?_⟩
  intro N _ _ _ _ _ g F U times order C hball hsource hs horder y hy
  obtain ⟨z, hz, rfl⟩ := hy
  set d := min delta₁ e
  have hd0 : 0 ≤ d := (lt_min hdelta₁ hepos).le
  have hde : d ≤ e := min_le_right _ _
  have hd1 : d < 1 := hde.trans_lt hone
  have hxball : x ∈ riemannianClosedBallOf (I := I3) (h s) x R := by
    change riemannianEDistOf (I := I3) (h s) x x ≤ ENNReal.ofReal R
    rw [riemannianEDistOf_self]
    exact zero_le
  have hclose := hscalar N (C.mono (subset_refl _) le_rfl (min_le_left _ _)) U hsource
    (subset_refl _) hs horder (hball hxball)
  have hRlow : Rlow < metricScalarAt (g s) (F x) := by
    have := (abs_lt.mp hclose).1
    linarith
  have hRlow0 : 0 < Rlow := by positivity
  have hsqrt : 10000 / X < Real.sqrt (metricScalarAt (g s) (F x)) := by
    have hh := Real.sqrt_lt_sqrt hRlow0.le hRlow
    rwa [Real.sqrt_sq (by positivity)] at hh
  have hleft : 10000 / Real.sqrt (metricScalarAt (g s) (F x)) < X := by
    have hh := div_lt_div_of_pos_left (by norm_num : (0 : ℝ) < 10000) (by positivity) hsqrt
    rwa [div_div_cancel₀ (by norm_num : (10000 : ℝ) ≠ 0)] at hh
  have hsqrt_le : Real.sqrt (1 - e) ≤ Real.sqrt (1 - d) := Real.sqrt_le_sqrt (by linarith)
  have hsqrt_le' : Real.sqrt (1 + d) ≤ Real.sqrt (1 + e) := Real.sqrt_le_sqrt (by linarith)
  have hroom' : Real.sqrt (1 + d) * (3 * rho) < Real.sqrt (1 - d) * R := by
    have h3r : 0 ≤ 3 * rho := by linarith
    calc Real.sqrt (1 + d) * (3 * rho) ≤ Real.sqrt (1 + e) * (3 * rho) :=
          mul_le_mul_of_nonneg_right hsqrt_le' h3r
      _ < Real.sqrt (1 - e) * R := by linarith
      _ ≤ Real.sqrt (1 - d) * R := mul_le_mul_of_nonneg_right hsqrt_le hRpos.le
  have hequiv : ∀ w ∈ riemannianClosedBallOf (I := I3) (h s) x R, ∀ v : TangentSpace I3 w,
      (1 - d) * (h s).inner w v v ≤
          (g s).inner (F w) (mfderiv I3 I3 (F : P → N) w v) (mfderiv I3 I3 (F : P → N) w v) ∧
        (g s).inner (F w) (mfderiv I3 I3 (F : P → N) w v) (mfderiv I3 I3 (F : P → N) w v) ≤
          (1 + d) * (h s).inner w v v := by
    intro w hw v
    have hmem := hball hw
    have hh := C.equivalence s hs w hmem v
    rwa [C.pullback_eq s w hmem (fun _ => v)] at hh
  have hxrho : x ∈ riemannianClosedBallOf (I := I3) (h s) x rho := by
    change riemannianEDistOf (I := I3) (h s) x x ≤ ENNReal.ofReal rho
    rw [riemannianEDistOf_self]
    exact zero_le
  have htransfer := (crossModel_metricDistance_transfer (h s) (g s) F x hRpos hd0 hd1 hrho hcpt
    (hball.trans hsource) hequiv hroom' x hxrho z (hA hz)).1
  have hmid : X ≤ Real.sqrt (1 - d) * (A₀ + margin) := by
    have hh : X ≤ Real.sqrt (1 - e) * (A₀ + margin) := by linarith
    exact hh.trans (mul_le_mul_of_nonneg_right hsqrt_le (by linarith))
  have hdz := hdeep z hz
  have hfin : Real.sqrt (1 - d) * (A₀ + margin) ≤ Real.sqrt (1 - d) * metricDistance (h s) x z :=
    mul_le_mul_of_nonneg_left hdz (Real.sqrt_nonneg _)
  linarith

theorem LocalCap.exists_deep_transport_tolerance_of_metricComparisonOn
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := P) D} (hS : IsSolutionOn S)
    {alpha eps a b t rho R margin : ℝ} {x : P} {W : Set P} (L : LocalCap S eps x t W)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11) (heps : eps ≤ neckModelTolerance alpha)
    (hab : a < b) (hwindow : ∀ i, b ≤ t - 2 * (S.scalar t (L.chain.centers i))⁻¹)
    (hslab : Icc a t ⊆ D.carrier) (hreg : Ioo a t ⊆ D.regular)
    (V : TopologicalSpace.Opens P) (hVcompact : IsCompact (closure (V : Set P)))
    {K : Set P} (hK : IsCompact K) (hKV : K ⊆ V) (hWK : W ⊆ K)
    (houter : ∀ i, ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, (L.chain.necks i).map y ∈ K)
    (hQ : 0 < S.scalar t x) (hmargin : 0 < margin) (hrho : 0 ≤ rho) (hroom : 3 * rho < R)
    (hball : riemannianClosedBallOf (I := I3) (S.base.metric t) x R ⊆ K)
    (htube : L.tube ⊆ riemannianClosedBallOf (I := I3) (S.base.metric t) x rho)
    (hdeep : ∀ y ∈ L.tube,
      10000 / Real.sqrt (S.scalar t x) + margin ≤ metricDistance (S.base.metric t) x y) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (N : Type u) [TopologicalSpace N] [ChartedSpace ThreeSpace N]
        [IsManifold I3 ∞ N] [T2Space N] [SigmaCompactSpace N],
      ∀ {D' : RealTimeInterval} (S' : SolutionOn (I := I3) (M := N) D'), IsSolutionOn S' →
      Icc a t ⊆ D'.carrier → Ioo a t ⊆ D'.regular →
      ∀ F : PartialDiffeomorph I3 I3 P N ∞, (V : Set P) ⊆ F.source →
      MetricComparisonOn S.base.metric S'.base.metric F V (Icc b t) ⌈(2 * alpha)⁻¹⌉₊ delta →
      ∃ L' : LocalCap S' (2 * alpha) (F x) t (F '' W),
        L'.tubeMap = L.tubeMap.trans F ∧ L'.tube = F '' L.tube ∧
          L'.core.carrier = F '' L.core.carrier ∧
          ∀ y ∈ L'.tube,
            10000 / Real.sqrt (S'.scalar t (F x)) ≤ metricDistance (S'.base.metric t) (F x) y := by
  obtain ⟨delta₁, hdelta₁, hcap⟩ := L.exists_transport_tolerance_of_metricComparisonOn hS ha
    hsmall heps hab hwindow hslab hreg V hVcompact hK hKV hWK houter
  have hcpt : IsCompact (riemannianClosedBallOf (I := I3) (S.base.metric t) x R) :=
    hK.of_isClosed_subset
      (DifferentialGeometry.Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _) hball
  obtain ⟨delta₂, hdelta₂, hdepth⟩ := exists_tolerance_depth_image_of_metricComparisonOn
    S.base.metric t x hmargin hQ hrho hroom hcpt htube hdeep
  refine ⟨min delta₁ delta₂, lt_min hdelta₁ hdelta₂, ?_⟩
  intro N _ _ _ _ _ D' S' hS' hslab' hreg' F hF C
  obtain ⟨L', htm, ht, hc⟩ := hcap N S' hS' hslab' hreg' F hF
    (C.mono (subset_refl _) le_rfl (min_le_left _ _))
  have hbt : b < t := by
    have hQi := (L.chain.necks ⟨0, L.chain.count_pos⟩).Q_pos
    have h0 := hwindow ⟨0, L.chain.count_pos⟩
    have := inv_pos.mpr hQi
    linarith
  have horder2 : 2 ≤ ⌈(2 * alpha)⁻¹⌉₊ := by
    have h1 : (1 : ℝ) < (2 * alpha)⁻¹ := (one_lt_inv₀ (by linarith)).mpr (by linarith)
    have h2 : 1 < ⌈(2 * alpha)⁻¹⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast h1)
    omega
  refine ⟨L', htm, ht, hc, ?_⟩
  rw [ht]
  exact hdepth N (C.mono (subset_refl _) le_rfl (min_le_right _ _)) (hball.trans hKV)
    hF ⟨hbt.le, le_rfl⟩ horder2

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
