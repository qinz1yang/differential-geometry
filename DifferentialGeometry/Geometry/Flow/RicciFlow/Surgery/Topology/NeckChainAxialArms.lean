import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckRegionAxialArms
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckLocalTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TransverseCrossingPath
import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngle
import DifferentialGeometry.Geometry.Geodesic.MinimizingArm
import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance

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
private theorem exists_chain_minimizingArm (g : SmoothRiemannianMetric I3 M)
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

omit [SigmaCompactSpace M] [T2Space M] in
private theorem chain_dist_triangle (g : SmoothRiemannianMetric I3 M) {x y z : M}
    (hxy : riemannianEDistOf g x y ≠ ⊤) (hyz : riemannianEDistOf g y z ≠ ⊤) :
    metricDistance g x z ≤ metricDistance g x y + metricDistance g y z :=
  DifferentialGeometry.riemannianEDistOf_toReal_triangle g x y z hxy hyz

omit [SigmaCompactSpace M] [T2Space M] in
private theorem chain_dist_comm (g : SmoothRiemannianMetric I3 M) (x y : M) :
    metricDistance g x y = metricDistance g y x := by
  unfold metricDistance
  rw [DifferentialGeometry.riemannianEDistOf_comm]

omit [SigmaCompactSpace M] [T2Space M] in
private theorem chain_edist_comm_ne_top (g : SmoothRiemannianMetric I3 M) {x y : M}
    (h : riemannianEDistOf g x y ≠ ⊤) : riemannianEDistOf g y x ≠ ⊤ := by
  rwa [DifferentialGeometry.riemannianEDistOf_comm]

omit [SigmaCompactSpace M] [T2Space M] in
private theorem chain_edist_ne_top_trans (g : SmoothRiemannianMetric I3 M) {x y z : M}
    (hxy : riemannianEDistOf g x y ≠ ⊤) (hyz : riemannianEDistOf g y z ≠ ⊤) :
    riemannianEDistOf g x z ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hxy, hyz⟩)
    (DifferentialGeometry.riemannianEDistOf_triangle g x y z)

omit [SigmaCompactSpace M] [T2Space M] in
private theorem chain_dist_self (g : SmoothRiemannianMetric I3 M) (x : M) :
    metricDistance g x x = 0 := by
  unfold metricDistance
  rw [DifferentialGeometry.riemannianEDistOf_self, ENNReal.toReal_zero]

private theorem exists_slice_point_on_minimizer {g : SmoothRiemannianMetric I3 M}
    (hg : RiemannianMetricComplete g) {p y : M} {S : Set M}
    (hfin : riemannianEDistOf g p y ≠ ⊤)
    (hsep : y ∉ connectedComponentIn Sᶜ p) :
    ∃ z ∈ S, riemannianEDistOf g p z ≠ ⊤ ∧ riemannianEDistOf g z y ≠ ⊤ ∧
      metricDistance g p y = metricDistance g p z + metricDistance g z y := by
  by_cases hp : p ∈ S
  · refine ⟨p, hp, ?_, hfin, by rw [chain_dist_self, zero_add]⟩
    rw [DifferentialGeometry.riemannianEDistOf_self]
    exact ENNReal.zero_ne_top
  by_cases hpy : p = y
  · exact absurd (hpy ▸ mem_connectedComponentIn hp) hsep
  obtain ⟨a, hlen, hend⟩ := exists_chain_minimizingArm g hg hpy hfin
  have hmeet : ∃ s ∈ Icc 0 a.length, a.point s ∈ S := by
    by_contra hno
    simp only [not_exists, not_and] at hno
    have hsub : a.point '' Icc 0 a.length ⊆ Sᶜ := by
      rintro _ ⟨s, hs, rfl⟩
      exact hno s hs
    have hpre : IsPreconnected (a.point '' Icc 0 a.length) :=
      isPreconnected_Icc.image _ a.continuousOn_point
    have h0 : p ∈ a.point '' Icc 0 a.length := ⟨0, ⟨le_rfl, a.length_pos.le⟩, a.start⟩
    have hL : y ∈ a.point '' Icc 0 a.length := ⟨a.length, ⟨a.length_pos.le, le_rfl⟩, hend⟩
    exact hsep (hpre.subset_connectedComponentIn h0 hsub hL)
  obtain ⟨s, hs, hsS⟩ := hmeet
  have h0 : (0 : ℝ) ∈ Icc 0 a.length := ⟨le_rfl, a.length_pos.le⟩
  have hL : a.length ∈ Icc 0 a.length := ⟨a.length_pos.le, le_rfl⟩
  have e1 := a.edistOf_eq h0 hs
  have e2 := a.edistOf_eq hs hL
  rw [a.start] at e1
  rw [hend] at e2
  have d1 := a.minimizing 0 h0 s hs
  have d2 := a.minimizing s hs a.length hL
  rw [a.start] at d1
  rw [hend] at d2
  refine ⟨a.point s, hsS, by rw [e1]; exact ENNReal.ofReal_ne_top,
    by rw [e2]; exact ENNReal.ofReal_ne_top, ?_⟩
  rw [d1, d2, ← hlen, zero_sub, abs_neg, abs_of_nonneg hs.1,
    abs_of_nonpos (by linarith [hs.2])]
  ring

theorem metricDistance_ge_of_separating_slices {g : SmoothRiemannianMetric I3 M}
    (hg : RiemannianMetricComplete g) (c : ℕ → M) (slice : ℕ → Set M) (e : ℕ → ℝ)
    {i m : ℕ} (him : i < m) (he : ∀ k, 0 ≤ e k)
    (hmem : ∀ k, i < k → k ≤ m → c k ∈ slice k)
    (hnear : ∀ k, i < k → k ≤ m → ∀ y ∈ slice k,
      riemannianEDistOf g (c k) y ≤ ENNReal.ofReal (e k))
    (hstep : ∀ k, i ≤ k → k < m → riemannianEDistOf g (c k) (c (k + 1)) ≠ ⊤)
    (hsep : ∀ k, i < k → k < m →
      Disjoint (slice (k + 1)) (connectedComponentIn (slice k)ᶜ (c i))) :
    ∑ j ∈ Finset.Ico i m, metricDistance g (c j) (c (j + 1)) -
        2 * ∑ j ∈ Finset.Ico (i + 1) m, e j ≤ metricDistance g (c i) (c m) := by
  have hnear' : ∀ k, i < k → k ≤ m → ∀ y ∈ slice k,
      riemannianEDistOf g (c k) y ≠ ⊤ ∧ metricDistance g (c k) y ≤ e k :=
    fun k h1 h2 y hy =>
    ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hnear k h1 h2 y hy),
      ENNReal.toReal_le_of_le_ofReal (he k) (hnear k h1 h2 y hy)⟩
  have key : ∀ k, i + 1 ≤ k → k ≤ m → ∀ y ∈ slice k,
      riemannianEDistOf g (c i) y ≠ ⊤ ∧
      ∑ j ∈ Finset.Ico i k, metricDistance g (c j) (c (j + 1)) -
        2 * ∑ j ∈ Finset.Ico (i + 1) k, e j - metricDistance g (c k) y ≤
        metricDistance g (c i) y := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro hm y hy
      have h1 := hstep i le_rfl (by omega)
      obtain ⟨h2, -⟩ := hnear' (i + 1) (by omega) hm y hy
      have hiy := chain_edist_ne_top_trans g h1 h2
      refine ⟨hiy, ?_⟩
      have htri := chain_dist_triangle g hiy (chain_edist_comm_ne_top g h2)
      rw [chain_dist_comm g y] at htri
      rw [Finset.sum_Ico_succ_top le_rfl, Finset.Ico_self, Finset.sum_empty, Finset.Ico_self,
        Finset.sum_empty]
      linarith
    | succ k hk ih =>
      intro hm y hy
      have hk' : i < k := by omega
      obtain ⟨hik, -⟩ := ih (by omega) (c k) (hmem k hk' (by omega))
      have hstepk := hstep k (by omega) (by omega)
      obtain ⟨hy1, hy2⟩ := hnear' (k + 1) (by omega) hm y hy
      have hiy : riemannianEDistOf g (c i) y ≠ ⊤ :=
        chain_edist_ne_top_trans g (chain_edist_ne_top_trans g hik hstepk) hy1
      have hnot : y ∉ connectedComponentIn (slice k)ᶜ (c i) := fun h =>
        Set.disjoint_left.mp (hsep k hk' (by omega)) hy h
      obtain ⟨z, hzS, hiz, hzy, hsplit⟩ := exists_slice_point_on_minimizer hg hiy hnot
      obtain ⟨-, hih⟩ := ih (by omega) z hzS
      obtain ⟨hkz, hkze⟩ := hnear' k hk' (by omega) z hzS
      have t1 := chain_dist_triangle g hkz hzy
      have t2 := chain_dist_triangle g (chain_edist_ne_top_trans g hkz hzy)
        (chain_edist_comm_ne_top g hy1)
      rw [chain_dist_comm g y (c (k + 1))] at t2
      refine ⟨hiy, ?_⟩
      rw [Finset.sum_Ico_succ_top (by omega : i ≤ k),
        Finset.sum_Ico_succ_top (by omega : i + 1 ≤ k)]
      linarith
  obtain ⟨-, h⟩ := key m (by omega) le_rfl (c m) (hmem m him le_rfl)
  rw [chain_dist_self, sub_zero] at h
  exact h


omit [SigmaCompactSpace M] in
theorem SpatialNeck.metricDistance_center_axial_bounds {g : SmoothRiemannianMetric I3 M}
    {eps : ℝ} {x : M} (nk : SpatialNeck g eps x) {L : ℝ} (hL : 0 < L) (hLeps : L < eps⁻¹) :
    riemannianEDistOf g x (nk.map (nk.center, L)) ≠ ⊤ ∧
      Real.sqrt (1 - eps) * L / Real.sqrt (metricScalarAt g x) ≤
        metricDistance g x (nk.map (nk.center, L)) ∧
      metricDistance g x (nk.map (nk.center, L)) ≤
        Real.sqrt (1 + eps) * L / Real.sqrt (metricScalarAt g x) := by
  have hi : 0 < eps⁻¹ := inv_pos.mpr nk.eps_pos
  have h0 : (0 : ℝ) ∈ Ioo (-eps⁻¹) eps⁻¹ := ⟨by linarith, hi⟩
  have hLm : L ∈ Ioo (-eps⁻¹) eps⁻¹ := ⟨by linarith, hLeps⟩
  have hup := nk.edist_same_fiber_le nk.center h0 hLm
  rw [nk.center_eq, zero_sub, abs_neg, abs_of_pos hL] at hup
  have hfin : riemannianEDistOf g x (nk.map (nk.center, L)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hup
  refine ⟨hfin, ?_, ENNReal.toReal_le_of_le_ofReal (by positivity) hup⟩
  have hsQ : 0 < Real.sqrt (metricScalarAt g x) := Real.sqrt_pos.mpr nk.Q_pos
  have hm : 0 < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr (by linarith [nk.eps_small])
  by_contra hlt
  rw [not_le] at hlt
  have hd0 : 0 ≤ metricDistance g x (nk.map (nk.center, L)) := ENNReal.toReal_nonneg
  set d := metricDistance g x (nk.map (nk.center, L)) with hd
  set sQ := Real.sqrt (metricScalarAt g x)
  set sm := Real.sqrt (1 - eps)
  have hdsm : d * sQ < sm * L := by
    have := (lt_div_iff₀ hsQ).mp hlt
    linarith
  set r := (d * sQ / sm + L) / 2 with hr
  have hq : d * sQ / sm < L := by
    rw [div_lt_iff₀ hm]
    linarith
  have hq0 : 0 ≤ d * sQ / sm := by positivity
  have hrL : r < L := by linarith
  have hr0 : 0 < r := by linarith
  have hdr : d < r * sm / sQ := by
    rw [lt_div_iff₀ hsQ]
    have h1 : d * sQ / sm < r := by linarith
    have h2 := (div_lt_iff₀ hm).mp h1
    linarith
  have hmem : nk.map (nk.center, L) ∈ riemannianBallOf g x (r * sm / sQ) := by
    change riemannianEDistOf g x _ < ENNReal.ofReal _
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hdr
  obtain ⟨⟨w, h⟩, ⟨-, hh⟩, heq⟩ := nk.ball_subset_image_slab hr0 (hrL.trans hLeps) hmem
  have hsrc1 : ((w, h) : Cylinder) ∈ nk.map.source :=
    nk.domain ⟨mem_univ _, by constructor <;> linarith [hh.1, hh.2]⟩
  have hsrc2 : ((nk.center, L) : Cylinder) ∈ nk.map.source := nk.domain ⟨mem_univ _, hLm⟩
  have hpair := (nk.map.left_inv' hsrc1).symm.trans
    ((congrArg nk.map.symm heq).trans (nk.map.left_inv' hsrc2))
  have hhL : h = L := congrArg Prod.snd hpair
  linarith [hh.2]

private theorem necklace_angle_cosine {u v w δ : ℝ} (hu : 0 < u) (hv : 0 < v)
    (huv : u ≤ 2 * v) (hvu : v ≤ 2 * u) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hw : (1 - δ) * (u + v) ≤ w) :
    Real.arccos (9 / 2 * δ - 1) ≤ comparisonAngle u v w := by
  unfold comparisonAngle comparisonCosine
  apply Real.arccos_le_arccos
  rw [div_le_iff₀ (by positivity)]
  have hs : 0 ≤ (1 - δ) * (u + v) := mul_nonneg (by linarith) (by linarith)
  have hw2 := mul_self_le_mul_self hs hw
  have hsq : (1 - 2 * δ) * (u + v) ^ 2 ≤ ((1 - δ) * (u + v)) * ((1 - δ) * (u + v)) := by
    nlinarith [sq_nonneg δ, sq_nonneg (u + v)]
  have hprod : 0 ≤ δ * ((2 * u - v) * (2 * v - u)) :=
    mul_nonneg hδ0 (mul_nonneg (by linarith) (by linarith))
  nlinarith

theorem exists_minimizingArms_of_neckNecklace {g : SmoothRiemannianMetric I3 M}
    (hg : RiemannianMetricComplete g) {eps L D : ℝ} (hL : 0 < L) (hLeps : L < eps⁻¹)
    (hLD : 3 * L ≤ D) (c : ℕ → M) (nk : ∀ k, SpatialNeck g eps (c k)) {i₀ m : ℕ}
    (hi₀ : i₀ ≤ m) (hstep : ∀ k < m, c (k + 1) = (nk k).map ((nk k).center, L))
    (hscalar : ∀ k ≤ m, metricScalarAt g (c i₀) ≤ 4 * metricScalarAt g (c k))
    (hsep : ∀ i k, i < k → k < m →
      Disjoint ((nk (k + 1)).map '' (univ ×ˢ ({0} : Set ℝ)))
        (connectedComponentIn ((nk k).map '' (univ ×ˢ ({0} : Set ℝ)))ᶜ (c i)))
    (hlow : D ≤ Real.sqrt (metricScalarAt g (c i₀)) * metricDistance g (c i₀) (c 0))
    (hhigh : D ≤ Real.sqrt (metricScalarAt g (c i₀)) * metricDistance g (c i₀) (c m)) :
    ∃ (arms : Fin 2 → MinimizingArm g (c i₀)) (ell : Fin 2 → ℝ),
      (∀ j, ell j ∈ Ioc 0 (arms j).length) ∧
      (∀ j, Real.sqrt (metricScalarAt g (c i₀)) * ell j ∈ Icc D (2 * D)) ∧
      Real.arccos (9 / 2 * (14 / (Real.sqrt (1 - eps) * L)) - 1) ≤
        comparisonAngle (ell 0) (ell 1)
          (metricDistance g ((arms 0).point (ell 0)) ((arms 1).point (ell 1))) := by
  classical
  have heps0 : 0 < eps := (nk 0).eps_pos
  have heps1 : eps < 1 / 11 := (nk 0).eps_small
  set sQ := Real.sqrt (metricScalarAt g (c i₀)) with hsQdef
  have hsQ : 0 < sQ := Real.sqrt_pos.mpr (nk i₀).Q_pos
  have hsm : 0 < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr (by linarith)
  have hsp : Real.sqrt (1 + eps) ≤ 3 / 2 := by
    have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + eps by linarith)
    nlinarith [Real.sqrt_nonneg (1 + eps)]
  have hD : 0 < D := by linarith
  set δ := 14 / (Real.sqrt (1 - eps) * L) with hδdef
  have hδ0 : 0 ≤ δ := by positivity
  let ell' : ℕ → ℝ := fun k => metricDistance g (c k) (c (k + 1))
  let e : ℕ → ℝ := fun k => 7 / Real.sqrt (metricScalarAt g (c k))
  have he : ∀ k, 0 ≤ e k := fun k => div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hstepb : ∀ k < m, riemannianEDistOf g (c k) (c (k + 1)) ≠ ⊤ ∧
      Real.sqrt (1 - eps) * L / Real.sqrt (metricScalarAt g (c k)) ≤ ell' k ∧
      ell' k ≤ Real.sqrt (1 + eps) * L / Real.sqrt (metricScalarAt g (c k)) := by
    intro k hk
    simp only [ell']
    rw [hstep k hk]
    exact (nk k).metricDistance_center_axial_bounds hL hLeps
  have hell0 : ∀ k < m, 0 ≤ ell' k := fun k _ => ENNReal.toReal_nonneg
  have heδ : ∀ k < m, 2 * e k ≤ δ * ell' k := by
    intro k hk
    have hQk := Real.sqrt_pos.mpr (nk k).Q_pos
    have h1 : δ * (Real.sqrt (1 - eps) * L / Real.sqrt (metricScalarAt g (c k))) =
        2 * e k := by
      simp only [δ, e]
      field_simp
      ring
    rw [← h1]
    exact mul_le_mul_of_nonneg_left (hstepb k hk).2.1 hδ0
  have hbig : ∀ k < m, sQ * ell' k ≤ D := by
    intro k hk
    have hQk := Real.sqrt_pos.mpr (nk k).Q_pos
    have hle : sQ ≤ 2 * Real.sqrt (metricScalarAt g (c k)) := by
      have h := Real.sqrt_le_sqrt (hscalar k hk.le)
      rwa [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    have h2 := (hstepb k hk).2.2
    have h3 : sQ * ell' k ≤ 2 * Real.sqrt (metricScalarAt g (c k)) *
        (Real.sqrt (1 + eps) * L / Real.sqrt (metricScalarAt g (c k))) :=
      mul_le_mul hle h2 (hell0 k hk) (by linarith)
    have h4 : 2 * Real.sqrt (metricScalarAt g (c k)) *
        (Real.sqrt (1 + eps) * L / Real.sqrt (metricScalarAt g (c k))) =
        2 * Real.sqrt (1 + eps) * L := by
      field_simp
    nlinarith
  have hfin0 : ∀ k ≤ m, riemannianEDistOf g (c 0) (c k) ≠ ⊤ := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [DifferentialGeometry.riemannianEDistOf_self]
      exact ENNReal.zero_ne_top
    | succ k ih =>
      intro hk
      exact chain_edist_ne_top_trans g (ih (by omega)) (hstepb k (by omega)).1
  have hfin : ∀ a b, a ≤ m → b ≤ m → riemannianEDistOf g (c a) (c b) ≠ ⊤ :=
    fun a b ha hb => chain_edist_ne_top_trans g (chain_edist_comm_ne_top g (hfin0 a ha))
      (hfin0 b hb)
  have hup : ∀ a b, a ≤ b → b ≤ m →
      metricDistance g (c a) (c b) ≤ ∑ j ∈ Finset.Ico a b, ell' j := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base =>
      intro _
      rw [chain_dist_self, Finset.Ico_self, Finset.sum_empty]
    | succ b hab ih =>
      intro hb
      rw [Finset.sum_Ico_succ_top hab]
      have ht := chain_dist_triangle g (hfin a b (by omega) (by omega))
        (hstepb b (by omega)).1
      have := ih (by omega)
      linarith
  have hexp : ∃ k, i₀ ≤ k ∧ k ≤ m ∧ D ≤ sQ * metricDistance g (c i₀) (c k) :=
    ⟨m, hi₀, le_rfl, hhigh⟩
  obtain ⟨kp, ⟨hkp1, hkp2, hkp3⟩, hkpmin⟩ :
      ∃ k, (i₀ ≤ k ∧ k ≤ m ∧ D ≤ sQ * metricDistance g (c i₀) (c k)) ∧
        ∀ k' < k, ¬ (i₀ ≤ k' ∧ k' ≤ m ∧ D ≤ sQ * metricDistance g (c i₀) (c k')) :=
    ⟨Nat.find hexp, Nat.find_spec hexp, fun k' hk' => Nat.find_min hexp hk'⟩
  have hkp0 : i₀ < kp := by
    rcases eq_or_lt_of_le hkp1 with h | h
    · rw [← h, chain_dist_self, mul_zero] at hkp3
      linarith
    · exact h
  obtain ⟨q, rfl⟩ : ∃ q, kp = q + 1 := ⟨kp - 1, by omega⟩
  have hq : sQ * metricDistance g (c i₀) (c q) < D := by
    have h := hkpmin q (by omega)
    simp only [not_and, not_le] at h
    exact h (by omega) (by omega)
  have hkpup : sQ * metricDistance g (c i₀) (c (q + 1)) ≤ 2 * D := by
    have ht := chain_dist_triangle g (hfin i₀ q hi₀ (by omega)) (hstepb q (by omega)).1
    have := hbig q (by omega)
    nlinarith
  have hexm : ∃ j, j ≤ i₀ ∧ D ≤ sQ * metricDistance g (c i₀) (c (i₀ - j)) :=
    ⟨i₀, le_rfl, by rw [Nat.sub_self]; exact hlow⟩
  obtain ⟨jm, ⟨hjm1, hjm2⟩, hjmmin⟩ :
      ∃ j, (j ≤ i₀ ∧ D ≤ sQ * metricDistance g (c i₀) (c (i₀ - j))) ∧
        ∀ j' < j, ¬ (j' ≤ i₀ ∧ D ≤ sQ * metricDistance g (c i₀) (c (i₀ - j'))) :=
    ⟨Nat.find hexm, Nat.find_spec hexm, fun j' hj' => Nat.find_min hexm hj'⟩
  have hjm0 : jm ≠ 0 := by
    rintro rfl
    rw [Nat.sub_zero, chain_dist_self, mul_zero] at hjm2
    linarith
  obtain ⟨q', rfl⟩ : ∃ q', jm = q' + 1 := ⟨jm - 1, by omega⟩
  set km := i₀ - (q' + 1) with hkm
  have hkm1 : i₀ - q' = km + 1 := by omega
  have hq' : sQ * metricDistance g (c i₀) (c (km + 1)) < D := by
    have h := hjmmin q' (by omega)
    simp only [not_and, not_le] at h
    rw [← hkm1]
    exact h (by omega)
  have hkmup : sQ * metricDistance g (c i₀) (c km) ≤ 2 * D := by
    have ht := chain_dist_triangle g (hfin i₀ (km + 1) hi₀ (by omega))
      (chain_edist_comm_ne_top g (hstepb km (by omega)).1)
    rw [chain_dist_comm g (c (km + 1))] at ht
    have := hbig km (by omega)
    nlinarith
  have hne_p : c i₀ ≠ c (q + 1) := by
    intro h
    rw [← h, chain_dist_self, mul_zero] at hkp3
    linarith
  have hne_m : c i₀ ≠ c km := by
    intro h
    rw [← h, chain_dist_self, mul_zero] at hjm2
    linarith
  obtain ⟨ap, hlenp, hendp⟩ :=
    exists_chain_minimizingArm g hg hne_p (hfin i₀ (q + 1) hi₀ hkp2)
  obtain ⟨am, hlenm, hendm⟩ :=
    exists_chain_minimizingArm g hg hne_m (hfin i₀ km hi₀ (by omega))
  have hlow' := metricDistance_ge_of_separating_slices hg c
    (fun k => (nk k).map '' (univ ×ˢ ({0} : Set ℝ))) e (i := km) (m := q + 1)
    (by omega) he
    (fun k _ _ => ⟨((nk k).center, 0), ⟨mem_univ _, mem_singleton 0⟩, (nk k).center_eq⟩)
    (fun k _ _ y hy => (nk k).central_sphere_subset_closedBall hy)
    (fun k _ hk => (hstepb k (by omega)).1)
    (fun k hk1 hk2 => hsep km k hk1 (by omega))
  have hsube : 2 * ∑ j ∈ Finset.Ico (km + 1) (q + 1), e j ≤
      δ * ∑ j ∈ Finset.Ico km (q + 1), ell' j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    calc ∑ j ∈ Finset.Ico (km + 1) (q + 1), 2 * e j
        ≤ ∑ j ∈ Finset.Ico km (q + 1), 2 * e j :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_left (by omega))
            (fun j _ _ => by linarith [he j])
      _ ≤ ∑ j ∈ Finset.Ico km (q + 1), δ * ell' j :=
          Finset.sum_le_sum fun j hj => heδ j (by
            have := (Finset.mem_Ico.mp hj).2
            omega)
  have hsplit := Finset.sum_Ico_consecutive ell' (show km ≤ i₀ by omega)
    (show i₀ ≤ q + 1 by omega)
  have hupm := hup km i₀ (by omega) hi₀
  have hupp := hup i₀ (q + 1) (by omega) hkp2
  rw [chain_dist_comm g (c km)] at hupm
  set u := metricDistance g (c i₀) (c (q + 1)) with hu
  set v := metricDistance g (c i₀) (c km) with hv
  set w := metricDistance g (c km) (c (q + 1)) with hw
  have hT : (1 - δ) * ∑ j ∈ Finset.Ico km (q + 1), ell' j ≤ w := by linarith
  have hupos : 0 < u := by
    by_contra h
    have : u = 0 := le_antisymm (not_lt.mp h) ENNReal.toReal_nonneg
    rw [this, mul_zero] at hkp3
    linarith
  have hvpos : 0 < v := by
    by_contra h
    have : v = 0 := le_antisymm (not_lt.mp h) ENNReal.toReal_nonneg
    rw [this, mul_zero] at hjm2
    linarith
  refine ⟨![ap, am], ![ap.length, am.length], ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact ⟨ap.length_pos, le_rfl⟩
    · exact ⟨am.length_pos, le_rfl⟩
  · intro j
    fin_cases j
    · change sQ * ap.length ∈ Icc D (2 * D)
      rw [hlenp]
      exact ⟨hkp3, hkpup⟩
    · change sQ * am.length ∈ Icc D (2 * D)
      rw [hlenm]
      exact ⟨hjm2, hkmup⟩
  · change Real.arccos (9 / 2 * δ - 1) ≤ comparisonAngle ap.length am.length
      (metricDistance g (ap.point ap.length) (am.point am.length))
    rw [hendp, hendm, hlenp, hlenm, chain_dist_comm g (c (q + 1))]
    rcases le_or_gt δ 1 with hδ1 | hδ1
    · have hum : u ≤ 2 * v := by
        have : sQ * u ≤ sQ * (2 * v) := by nlinarith
        exact le_of_mul_le_mul_left this hsQ
      have hvm : v ≤ 2 * u := by
        have : sQ * v ≤ sQ * (2 * u) := by nlinarith
        exact le_of_mul_le_mul_left this hsQ
      refine necklace_angle_cosine hupos hvpos hum hvm hδ0 hδ1 ?_
      have h1 : (1 - δ) * (u + v) ≤ (1 - δ) * ∑ j ∈ Finset.Ico km (q + 1), ell' j :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    · rw [Real.arccos_eq_zero.mpr (by linarith)]
      exact Real.arccos_nonneg _

theorem exists_minimizingArms_of_strongNeckNecklace {J : RealTimeInterval}
    {S : SolutionOn (I := I3) (M := M) J} {eps L D t : ℝ}
    (hg : RiemannianMetricComplete (S.base.metric t)) (hL : 0 < L) (hLeps : L < eps⁻¹)
    (hLD : 3 * L ≤ D) (c : ℕ → M) (nk : ∀ k, StrongNeck S eps (c k) t) {i₀ m : ℕ}
    (hi₀ : i₀ ≤ m) (hstep : ∀ k < m, c (k + 1) = (nk k).map ((nk k).center, L))
    (hscalar : ∀ k ≤ m, S.scalar t (c i₀) ≤ 4 * S.scalar t (c k))
    (hsep : ∀ i k, i < k → k < m →
      Disjoint ((nk (k + 1)).map '' (univ ×ˢ ({0} : Set ℝ)))
        (connectedComponentIn ((nk k).map '' (univ ×ˢ ({0} : Set ℝ)))ᶜ (c i)))
    (hlow : D ≤ Real.sqrt (S.scalar t (c i₀)) *
      metricDistance (S.base.metric t) (c i₀) (c 0))
    (hhigh : D ≤ Real.sqrt (S.scalar t (c i₀)) *
      metricDistance (S.base.metric t) (c i₀) (c m)) :
    ∃ (arms : Fin 2 → MinimizingArm (S.base.metric t) (c i₀)) (ell : Fin 2 → ℝ),
      (∀ j, ell j ∈ Ioc 0 (arms j).length) ∧
      (∀ j, Real.sqrt (S.scalar t (c i₀)) * ell j ∈ Icc D (2 * D)) ∧
      Real.arccos (9 / 2 * (14 / (Real.sqrt (1 - eps) * L)) - 1) ≤
        comparisonAngle (ell 0) (ell 1)
          (metricDistance (S.base.metric t) ((arms 0).point (ell 0)) ((arms 1).point (ell 1))) :=
  exists_minimizingArms_of_neckNecklace hg hL hLeps hLD c (fun k => (nk k).toSpatialNeck) hi₀
    hstep hscalar hsep hlow hhigh

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u

private theorem pi_div_two_le_arccos_of_nonpos {z : ℝ} (hz : z ≤ 0) :
    Real.pi / 2 ≤ Real.arccos z := by
  refine le_of_not_gt fun hlt => ?_
  have hpos := Real.arccos_lt_pi_div_two.mp hlt
  linarith

theorem exists_strongNeck_threshold_of_neckNecklace
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1 / 11)
    {kappa : ℝ} (hkappa : 0 < kappa) {rho : ℝ} (hrho : 0 < rho) {Phi : ℝ → ℝ}
    (hPhi : Perelman.AdmissiblePinchingFunction Phi) :
    ∃ D Q₀ theta : ℝ, 0 < D ∧ 0 < Q₀ ∧ 0 < theta ∧
      ∀ (P : OrientedThreeStage.{u}) (a s : ℝ) (G : P.IncomingSlab a s) (t : ℝ)
        (c : ℕ → P.Carrier) (nk : ∀ k, SpatialNeck (G.flow.base.metric t) (3000)⁻¹ (c k))
        (i₀ m : ℕ), i₀ ≤ m →
        (∀ k < m, c (k + 1) = (nk k).map ((nk k).center, 100)) →
        (∀ k ≤ m, G.flow.scalar t (c i₀) ≤ 4 * G.flow.scalar t (c k)) →
        (∀ i k, i < k → k < m →
          Disjoint ((nk (k + 1)).map '' (Set.univ ×ˢ ({0} : Set ℝ)))
            (connectedComponentIn ((nk k).map '' (Set.univ ×ˢ ({0} : Set ℝ)))ᶜ (c i))) →
        D ≤ Real.sqrt (G.flow.scalar t (c i₀)) *
          metricDistance (G.flow.base.metric t) (c i₀) (c 0) →
        D ≤ Real.sqrt (G.flow.scalar t (c i₀)) *
          metricDistance (G.flow.base.metric t) (c i₀) (c m) →
        t < s → Q₀ ≤ G.flow.scalar t (c i₀) →
        a ≤ t - theta / G.flow.scalar t (c i₀) →
        Perelman.PhiAlmostNonnegative G.flow
          (Set.Icc (t - theta / G.flow.scalar t (c i₀)) t) Phi →
        (∀ (τ : (RealTimeInterval.closedOpen a s G.lt).FlowTime)
          (B : Perelman.FlowMetricBall G.flow τ),
          t - theta / G.flow.scalar t (c i₀) ≤ τ → (τ : ℝ) ≤ t → B.radius ≤ rho →
            B.IsParabolicallyRmControlled → B.IsKappaNoncollapsed kappa) →
        Nonempty (StrongNeck G.flow delta (c i₀) t) := by
  obtain ⟨D, Q₀, theta, hD, hQ₀, htheta, hthr⟩ :=
    exists_strongNeck_threshold_of_minimizing_arms.{u} hdelta hdelta1 Real.pi_div_two_pos
      hkappa hrho hPhi
  refine ⟨D, Q₀, theta, hD, hQ₀, htheta, ?_⟩
  intro P a s G t c nk i₀ m hi₀ hstep hscalar hsep hlow hhigh hts hQ hwin hpinch hnc
  have hcomplete := RiemannianMetricComplete.of_compact (G.flow.base.metric t)
  rcases lt_or_ge (9 * D) ((3000 : ℝ)⁻¹)⁻¹ with hsmall | hlarge
  · obtain ⟨arms, ell, hell, hlen, hang⟩ :=
      (nk i₀).exists_axial_minimizingArms hcomplete hD hsmall
    refine hthr P a s G (c i₀) t hts hQ hwin hpinch hnc arms ell hell hlen
      ((pi_div_two_le_arccos_of_nonpos ?_).trans hang)
    apply div_nonpos_of_nonpos_of_nonneg <;> norm_num
  · have hLD : 3 * (100 : ℝ) ≤ D := by
      rw [inv_inv] at hlarge
      linarith
    obtain ⟨arms, ell, hell, hlen, hang⟩ :=
      exists_minimizingArms_of_neckNecklace hcomplete (by norm_num : (0 : ℝ) < 100)
        (by norm_num : (100 : ℝ) < ((3000 : ℝ)⁻¹)⁻¹) hLD c nk hi₀ hstep hscalar hsep hlow
        hhigh
    refine hthr P a s G (c i₀) t hts hQ hwin hpinch hnc arms ell hell hlen
      ((pi_div_two_le_arccos_of_nonpos ?_).trans hang)
    have hs2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - (3000 : ℝ)⁻¹ by norm_num)
    have hs0 := Real.sqrt_nonneg (1 - (3000 : ℝ)⁻¹)
    have hs : (63 : ℝ) / 100 ≤ Real.sqrt (1 - (3000 : ℝ)⁻¹) := by nlinarith
    have hpos : 0 < Real.sqrt (1 - (3000 : ℝ)⁻¹) * 100 := by positivity
    have hle : 14 / (Real.sqrt (1 - (3000 : ℝ)⁻¹) * 100) ≤ 2 / 9 := by
      rw [div_le_div_iff₀ hpos (by norm_num)]
      nlinarith
    linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
