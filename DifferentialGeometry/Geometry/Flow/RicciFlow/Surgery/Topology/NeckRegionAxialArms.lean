import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornNeckImprovement
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderAxialDistance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CylinderBallCapture
import DifferentialGeometry.Geometry.Comparison.MetricDistanceTransfer
import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle
import DifferentialGeometry.Geometry.Geodesic.MinimizingArm
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

noncomputable section

open Set
open DifferentialGeometry.Geometry.Comparison.Toponogov
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem exists_minimizingArm_of_edist_ne_top (g : SmoothRiemannianMetric I3 M)
    (hg : RiemannianMetricComplete g) {x y : M} (hxy : x ≠ y)
    (hfin : riemannianEDistOf g x y ≠ ⊤) :
    ∃ a : MinimizingArm g x, a.length = metricDistance g x y ∧ a.point a.length = y := by
  let C := connectedComponentOpen (I := I3) x
  have hyC : y ∈ (C : Set M) := by
    apply Geometry.Metric.edistOf_ball_subset_connCompOpen g x
      ((riemannianEDistOf g x y).toReal + 1)
    change riemannianEDistOf g x y < ENNReal.ofReal _
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg zero_le_one, ENNReal.ofReal_toReal hfin,
      ENNReal.ofReal_one]
    exact ENNReal.lt_add_right hfin one_ne_zero
  let _ : ConnectedSpace C := connectedComponentOpen_connectedSpace (I := I3) x
  let _ : SigmaCompactSpace C := (isClosed_connectedComponent (x := x)).sigmaCompactSpace
  have hC := Geometry.Metric.riemannianMetricComplete_restrictOpen_connCompOpen g x hg
  let xC : C := ⟨x, mem_connectedComponent⟩
  let yC : C := ⟨y, hyC⟩
  have hne : xC ≠ yC := fun h => hxy (congrArg Subtype.val h)
  obtain ⟨a, hlen, hend⟩ := exists_minimizingArm_of_complete (g.restrictOpen C) hC xC yC hne
  have hdist : ∀ p q : C, metricDistance (g.restrictOpen C) p q = metricDistance g p q := by
    intro p q
    unfold metricDistance
    rw [Geometry.Metric.edistOf_restrictOpen_connCompOpen]
  refine ⟨{ length := a.length
            length_pos := a.length_pos
            point := fun s => (a.point s : M)
            start := by rw [a.start]
            minimizing := fun s hs t ht => by rw [← hdist]; exact a.minimizing s hs t ht },
    ?_, ?_⟩
  · change a.length = _
    rw [hlen, hdist]
  · change ((a.point a.length : C) : M) = y
    rw [hend]

private theorem toReal_bounds_of_ofReal_mul {E : ℝ≥0∞} {c lo hi : ℝ} (hc : 0 < c)
    (hhi : 0 ≤ hi) (h1 : ENNReal.ofReal lo ≤ ENNReal.ofReal c * E)
    (h2 : ENNReal.ofReal c * E ≤ ENNReal.ofReal hi) :
    E ≠ ⊤ ∧ lo ≤ c * E.toReal ∧ c * E.toReal ≤ hi := by
  have hfin : ENNReal.ofReal c * E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h2
  have e : (ENNReal.ofReal c * E).toReal = c * E.toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
  refine ⟨fun hE => ?_, ?_, ?_⟩
  · rw [hE, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc).ne'] at hfin
    exact hfin rfl
  · rw [← e]
    exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp h1
  · rw [← e]
    exact ENNReal.toReal_le_of_le_ofReal hhi h2

omit [SigmaCompactSpace M] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem SpatialNeck.axial_metricDistance_bounds {g : SmoothRiemannianMetric I3 M} {eps : ℝ}
    {x : M} (nk : SpatialNeck g eps x) (z : Sphere 2) {H : ℝ} (hH : 0 < H)
    (hHeps : 6 * H < eps⁻¹) {a b : ℝ} (ha : |a| ≤ H) (hb : |b| ≤ H) :
    riemannianEDistOf g (nk.map (z, a)) (nk.map (z, b)) ≠ ⊤ ∧
      Real.sqrt (1 - eps) * |a - b| ≤
        Real.sqrt (metricScalarAt g x) * metricDistance g (nk.map (z, a)) (nk.map (z, b)) ∧
      Real.sqrt (metricScalarAt g x) * metricDistance g (nk.map (z, a)) (nk.map (z, b)) ≤
        Real.sqrt (1 + eps) * |a - b| := by
  have heps0 : 0 ≤ eps := nk.eps_pos.le
  have heps1 : eps < 1 := by linarith [nk.eps_small]
  have hR : 0 < 6 * H := by linarith
  have hslab : riemannianClosedBallOf (nk.cylinder.metric 0) ((z, 0) : Cylinder) (6 * H) ⊆
      (univ : Set (Sphere 2)) ×ˢ Ioo (-eps⁻¹) eps⁻¹ := by
    intro y hy
    have h1 := (nk.cylinder.closedBall_subset_slab ((z, 0) : Cylinder) hR.le hy).2
    have h2 : ((z, 0) : Cylinder).2 = 0 := rfl
    exact ⟨mem_univ _, by constructor <;> linarith [h1.1, h1.2]⟩
  have hequiv : ∀ y ∈ riemannianClosedBallOf (nk.cylinder.metric 0) ((z, 0) : Cylinder) (6 * H),
      ∀ v : TangentSpace IC y,
      (1 - eps) * (nk.cylinder.metric 0).inner y v v ≤
          (DifferentialGeometry.scaleMetric (metricScalarAt g x) nk.Q_pos g).inner (nk.map y)
            (mfderiv IC I3 (nk.map : Cylinder → M) y v)
            (mfderiv IC I3 (nk.map : Cylinder → M) y v) ∧
        (DifferentialGeometry.scaleMetric (metricScalarAt g x) nk.Q_pos g).inner (nk.map y)
            (mfderiv IC I3 (nk.map : Cylinder → M) y v)
            (mfderiv IC I3 (nk.map : Cylinder → M) y v) ≤
          (1 + eps) * (nk.cylinder.metric 0).inner y v v := by
    intro y hy v
    have hyU := hslab hy
    have heq := nk.comparison.pullback_eq 0 y hyU (fun _ => v)
    have hcmp := nk.comparison.equivalence 0 rfl y hyU v
    refine ⟨?_, ?_⟩
    · have h1 := hcmp.1
      rwa [heq] at h1
    · have h2 := hcmp.2
      rwa [heq] at h2
  have hroom : Real.sqrt (1 + eps) * (3 * H) < Real.sqrt (1 - eps) * (6 * H) := by
    have hp := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + eps by linarith)
    have hm := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - eps by linarith)
    have hs : Real.sqrt (1 + eps) < 2 * Real.sqrt (1 - eps) := by
      nlinarith [Real.sqrt_nonneg (1 + eps), Real.sqrt_nonneg (1 - eps), nk.eps_small]
    nlinarith
  have hball : ∀ c : ℝ, |c| ≤ H →
      ((z, c) : Cylinder) ∈
        riemannianClosedBallOf (nk.cylinder.metric 0) ((z, 0) : Cylinder) H := by
    intro c hc
    change riemannianEDistOf (nk.cylinder.metric 0) ((z, 0) : Cylinder) (z, c) ≤ ENNReal.ofReal H
    refine (nk.cylinder.axial_edist_le z 0 c).trans (ENNReal.ofReal_le_ofReal ?_)
    simpa only [zero_sub, abs_neg] using hc
  obtain ⟨hlo, hhi⟩ := crossModel_edist_transfer (nk.cylinder.metric 0)
    (DifferentialGeometry.scaleMetric (metricScalarAt g x) nk.Q_pos g) nk.map ((z, 0) : Cylinder)
    hR heps0 heps1 hH.le (nk.cylinder.isCompact_closedBall _ hR.le) (hslab.trans nk.domain)
    hequiv hroom (z, a) (hball a ha) (z, b) (hball b hb)
  have hcyl : riemannianEDistOf (nk.cylinder.metric 0) ((z, a) : Cylinder) (z, b) =
      ENNReal.ofReal |a - b| :=
    le_antisymm (nk.cylinder.axial_edist_le z a b) (nk.cylinder.height_edist_le (z, a) (z, b))
  rw [hcyl, edistOf_scale, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hlo
  rw [hcyl, edistOf_scale, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hhi
  exact toReal_bounds_of_ofReal_mul (Real.sqrt_pos.mpr nk.Q_pos) (by positivity) hlo hhi

private theorem pi_div_two_le_arccos_neck_cosine {eps : ℝ} (heps0 : 0 ≤ eps)
    (heps : eps ≤ 1 / 3) :
    Real.pi / 2 ≤ Real.arccos ((3 * eps - 1) / (1 + eps)) := by
  refine le_of_not_gt fun hlt => ?_
  have hpos := Real.arccos_lt_pi_div_two.mp hlt
  have hnonpos : (3 * eps - 1) / (1 + eps) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  linarith

theorem SpatialNeck.exists_axial_minimizingArms {g : SmoothRiemannianMetric I3 M}
    (hg : RiemannianMetricComplete g) {eps : ℝ} {x : M} (nk : SpatialNeck g eps x)
    {D : ℝ} (hD : 0 < D) (hDeps : 9 * D < eps⁻¹) :
    ∃ (arms : Fin 2 → MinimizingArm g x) (ell : Fin 2 → ℝ),
      (∀ j, ell j ∈ Ioc 0 (arms j).length) ∧
      (∀ j, Real.sqrt (metricScalarAt g x) * ell j ∈ Icc D (2 * D)) ∧
      Real.arccos ((3 * eps - 1) / (1 + eps)) ≤ comparisonAngle (ell 0) (ell 1)
        (metricDistance g ((arms 0).point (ell 0)) ((arms 1).point (ell 1))) := by
  have heps0 : 0 < eps := nk.eps_pos
  have heps1 : eps < 1 / 11 := nk.eps_small
  have hH : 0 < 3 * D / 2 := by positivity
  have hHeps : 6 * (3 * D / 2) < eps⁻¹ := by linarith
  have hsQ : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr nk.Q_pos
  have hsm2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - eps by linarith)
  have hsp2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + eps by linarith)
  have hsm0 := Real.sqrt_nonneg (1 - eps)
  have hsp0 := Real.sqrt_nonneg (1 + eps)
  have hsmlo : 2 / 3 ≤ Real.sqrt (1 - eps) := by nlinarith
  have hsphi : Real.sqrt (1 + eps) ≤ 4 / 3 := by nlinarith
  let hgt : Fin 2 → ℝ := ![3 * D / 2, -(3 * D / 2)]
  have habs : ∀ j, |hgt j| = 3 * D / 2 := by
    intro j
    fin_cases j <;> simp [hgt, abs_of_pos hH]
  have habs0 : ∀ j, |0 - hgt j| = 3 * D / 2 := by
    intro j
    rw [zero_sub, abs_neg, habs]
  have hne : ∀ j, hgt j ≠ 0 := by
    intro j h
    have := habs j
    rw [h, abs_zero] at this
    linarith
  have hbd := fun a b (ha : |a| ≤ 3 * D / 2) (hb : |b| ≤ 3 * D / 2) =>
    nk.axial_metricDistance_bounds nk.center hH hHeps ha hb
  have hsrc : ∀ c : ℝ, |c| ≤ 3 * D / 2 → ((nk.center, c) : Cylinder) ∈ nk.map.source := by
    intro c hc
    refine nk.domain ⟨mem_univ _, abs_lt.mp (lt_of_le_of_lt hc ?_)⟩
    linarith
  have hzero : |(0 : ℝ)| ≤ 3 * D / 2 := by rw [abs_zero]; exact hH.le
  have harm : ∀ j, ∃ a : MinimizingArm g x,
      a.length = metricDistance g x (nk.map (nk.center, hgt j)) ∧
        a.point a.length = nk.map (nk.center, hgt j) := by
    intro j
    have hxy : x ≠ nk.map (nk.center, hgt j) := by
      intro h
      have h0 : nk.map (nk.center, 0) = nk.map (nk.center, hgt j) := nk.center_eq.trans h
      have h1 := nk.map.left_inv' (hsrc 0 hzero)
      have h2 := nk.map.left_inv' (hsrc (hgt j) (habs j).le)
      rw [h0] at h1
      have h3 := h1.symm.trans h2
      exact hne j (congrArg Prod.snd h3).symm
    have hfin := (hbd 0 (hgt j) hzero (habs j).le).1
    rw [nk.center_eq] at hfin
    exact exists_minimizingArm_of_edist_ne_top g hg hxy hfin
  choose arms hlen hend using harm
  refine ⟨arms, fun j => (arms j).length, fun j => ⟨(arms j).length_pos, le_rfl⟩, ?_, ?_⟩
  · intro j
    obtain ⟨-, hlo, hhi⟩ := hbd 0 (hgt j) hzero (habs j).le
    rw [nk.center_eq, habs0] at hlo hhi
    change Real.sqrt (metricScalarAt g x) * (arms j).length ∈ Icc D (2 * D)
    rw [hlen j]
    constructor <;> nlinarith
  · change Real.arccos ((3 * eps - 1) / (1 + eps)) ≤ comparisonAngle (arms 0).length
      (arms 1).length (metricDistance g ((arms 0).point (arms 0).length)
        ((arms 1).point (arms 1).length))
    rw [hend 0, hend 1, ← comparisonAngle_scale _ _ _ hsQ]
    obtain ⟨-, hlo0, hhi0⟩ := hbd 0 (hgt 0) hzero (habs 0).le
    obtain ⟨-, hlo1, hhi1⟩ := hbd 0 (hgt 1) hzero (habs 1).le
    obtain ⟨-, hlo2, -⟩ := hbd (hgt 0) (hgt 1) (habs 0).le (habs 1).le
    rw [nk.center_eq, habs0] at hlo0 hhi0 hlo1 hhi1
    rw [← hlen 0] at hlo0 hhi0
    rw [← hlen 1] at hlo1 hhi1
    have h01 : |hgt 0 - hgt 1| = 2 * (3 * D / 2) := by
      simp only [hgt, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [sub_neg_eq_add, abs_of_pos (by positivity)]
      ring
    rw [h01] at hlo2
    set u0 := Real.sqrt (metricScalarAt g x) * (arms 0).length
    set u1 := Real.sqrt (metricScalarAt g x) * (arms 1).length
    set w := Real.sqrt (metricScalarAt g x) *
      metricDistance g (nk.map (nk.center, hgt 0)) (nk.map (nk.center, hgt 1))
    set H := 3 * D / 2
    unfold comparisonAngle comparisonCosine
    apply Real.arccos_le_arccos
    have hu0 : 0 < u0 := by nlinarith
    have hu1 : 0 < u1 := by nlinarith
    have ep : Real.sqrt (1 + eps) * H * (Real.sqrt (1 + eps) * H) = (1 + eps) * H ^ 2 := by
      rw [show Real.sqrt (1 + eps) * H * (Real.sqrt (1 + eps) * H) =
        Real.sqrt (1 + eps) ^ 2 * H ^ 2 by ring, hsp2]
    have em : Real.sqrt (1 - eps) * (2 * H) * (Real.sqrt (1 - eps) * (2 * H)) =
        4 * (1 - eps) * H ^ 2 := by
      rw [show Real.sqrt (1 - eps) * (2 * H) * (Real.sqrt (1 - eps) * (2 * H)) =
        4 * Real.sqrt (1 - eps) ^ 2 * H ^ 2 by ring, hsm2]
    have hu0sq : u0 ^ 2 ≤ (1 + eps) * H ^ 2 := by
      have h := mul_self_le_mul_self hu0.le hhi0
      nlinarith
    have hu1sq : u1 ^ 2 ≤ (1 + eps) * H ^ 2 := by
      have h := mul_self_le_mul_self hu1.le hhi1
      nlinarith
    have hwsq : 4 * (1 - eps) * H ^ 2 ≤ w ^ 2 := by
      have h := mul_self_le_mul_self (by positivity) hlo2
      nlinarith
    have hprod : u0 * u1 ≤ (1 + eps) * H ^ 2 := by
      have h := mul_le_mul hhi0 hhi1 hu1.le (by positivity)
      nlinarith
    rw [div_le_div_iff₀ (by positivity) (by linarith)]
    have hA : (u0 ^ 2 + u1 ^ 2 - w ^ 2) * (1 + eps) ≤
        (2 * (1 + eps) * H ^ 2 - 4 * (1 - eps) * H ^ 2) * (1 + eps) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have hB : (3 * eps - 1) * (2 * ((1 + eps) * H ^ 2)) ≤ (3 * eps - 1) * (2 * (u0 * u1)) :=
      mul_le_mul_of_nonpos_left (by linarith) (by linarith)
    calc (u0 ^ 2 + u1 ^ 2 - w ^ 2) * (1 + eps)
        ≤ (2 * (1 + eps) * H ^ 2 - 4 * (1 - eps) * H ^ 2) * (1 + eps) := hA
      _ = (3 * eps - 1) * (2 * ((1 + eps) * H ^ 2)) := by ring
      _ ≤ (3 * eps - 1) * (2 * (u0 * u1)) := hB
      _ = (3 * eps - 1) * (2 * u0 * u1) := by ring

theorem StrongNeck.exists_axial_minimizingArms {J : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) J} {eps : ℝ} {x : M} {t : ℝ} (nk : StrongNeck S eps x t)
    (hg : RiemannianMetricComplete (S.base.metric t)) {D : ℝ} (hD : 0 < D)
    (hDeps : 9 * D < eps⁻¹) :
    ∃ (arms : Fin 2 → MinimizingArm (S.base.metric t) x) (ell : Fin 2 → ℝ),
      (∀ j, ell j ∈ Ioc 0 (arms j).length) ∧
      (∀ j, Real.sqrt (S.scalar t x) * ell j ∈ Icc D (2 * D)) ∧
      Real.arccos ((3 * eps - 1) / (1 + eps)) ≤ comparisonAngle (ell 0) (ell 1)
        (metricDistance (S.base.metric t) ((arms 0).point (ell 0)) ((arms 1).point (ell 1))) :=
  nk.toSpatialNeck.exists_axial_minimizingArms hg hD hDeps

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

theorem exists_strongNeck_threshold_of_spatialNeck
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1 / 11)
    {kappa : ℝ} (hkappa : 0 < kappa) {rho : ℝ} (hrho : 0 < rho) {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi) :
    ∃ eps Q₀ theta : ℝ, 0 < eps ∧ 0 < Q₀ ∧ 0 < theta ∧
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s)
        (x : P.Carrier) (t : ℝ), t < s → Q₀ ≤ G.flow.scalar t x →
        a ≤ t - theta / G.flow.scalar t x →
        Perelman.PhiAlmostNonnegative G.flow (Icc (t - theta / G.flow.scalar t x) t) Phi →
        (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
          (B : Perelman.FlowMetricBall G.flow τ),
          t - theta / G.flow.scalar t x ≤ τ → (τ : ℝ) ≤ t → B.radius ≤ rho →
            B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed kappa) →
        SpatialNeck (G.flow.base.metric t) eps x →
        Nonempty (StrongNeck G.flow delta x t) := by
  obtain ⟨D, Q₀, theta, hD, hQ₀, htheta, hthr⟩ :=
    exists_strongNeck_threshold_of_minimizing_arms.{u} hdelta hdelta1 Real.pi_div_two_pos
      hkappa hrho hPhi
  refine ⟨(9 * D + 11)⁻¹, Q₀, theta, by positivity, hQ₀, htheta, ?_⟩
  intro P a s G x t hts hQ hwin hpinch hnc nk
  have hDeps : 9 * D < ((9 * D + 11)⁻¹)⁻¹ := by
    rw [inv_inv]
    linarith
  obtain ⟨arms, ell, hell, hlen, hang⟩ :=
    nk.exists_axial_minimizingArms (RiemannianMetricComplete.of_compact _) hD hDeps
  exact hthr P a s G x t hts hQ hwin hpinch hnc arms ell hell hlen
    ((pi_div_two_le_arccos_neck_cosine nk.eps_pos.le (by linarith [nk.eps_small])).trans hang)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
