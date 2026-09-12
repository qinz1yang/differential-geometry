import DifferentialGeometry.Geometry.Comparison.Toponogov.ComparisonAngleOrder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornEndAngle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Toponogov

universe u

variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

theorem totallyBounded_univ_iff_finset_net {α : Type*} [PseudoMetricSpace α] :
    TotallyBounded (univ : Set α) ↔
      ∀ ε > 0, ∃ t : Finset α, ∀ x : α, ∃ y ∈ t, dist x y < ε := by
  constructor
  · intro h ε hε
    obtain ⟨t, ht, hcov⟩ := Metric.totallyBounded_iff.mp h (ε / 2) (half_pos hε)
    refine ⟨ht.toFinset, fun x => ?_⟩
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hcov (mem_univ x))
    obtain ⟨hyt, hxy⟩ := mem_iUnion.mp hy
    exact ⟨y, ht.mem_toFinset.mpr hyt, by
      rw [Metric.mem_ball] at hxy
      linarith⟩
  · intro h
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨t, ht⟩ := h ε hε
    refine ⟨(t : Set α), t.finite_toSet, fun x _ => ?_⟩
    obtain ⟨y, hyt, hxy⟩ := ht x
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨by simpa using hyt,
      by rw [Metric.mem_ball]; exact hxy⟩⟩

theorem compactSpace_completion_of_totallyBounded {α : Type*} [PseudoMetricSpace α]
    (h : TotallyBounded (univ : Set α)) :
    CompactSpace (UniformSpace.Completion α) := by
  have htb : TotallyBounded (univ : Set (UniformSpace.Completion α)) := by
    rw [Metric.totallyBounded_iff] at h ⊢
    intro ε hε
    obtain ⟨t, ht, hcov⟩ := h (ε / 2) (half_pos hε)
    refine ⟨(fun x : α => (x : UniformSpace.Completion α)) '' t, ht.image _, ?_⟩
    intro z _
    obtain ⟨x, hx⟩ :=
      (UniformSpace.Completion.denseRange_coe (α := α)).exists_dist_lt z (half_pos hε)
    obtain ⟨y, hy⟩ := mem_iUnion.mp (hcov (mem_univ x))
    obtain ⟨hyt, hxy⟩ := mem_iUnion.mp hy
    refine mem_iUnion.mpr ⟨(y : UniformSpace.Completion α), mem_iUnion.mpr
      ⟨⟨y, hyt, rfl⟩, ?_⟩⟩
    rw [Metric.mem_ball] at hxy ⊢
    have htri := dist_triangle z (x : UniformSpace.Completion α)
      (y : UniformSpace.Completion α)
    rw [UniformSpace.Completion.dist_eq] at htri
    linarith
  exact isCompact_univ_iff.mp
    (isCompact_iff_totallyBounded_isComplete.mpr ⟨htb, isComplete_univ⟩)

variable {g : SmoothRiemannianMetric I3 W}

attribute [local instance] EndAngles.metric

structure ScaleDirectionNet (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) : Prop where
  net : ∀ eta > 0, ∃ A : Finset (EndRay H.endpoint), ∃ d > 0, ∀ b : EndRay H.endpoint,
    ∃ a ∈ A, ∀ s ∈ Ioc (0 : ℝ) (min d (min b.length a.length)),
      dist (a.point s) (b.point s) < eta * s

structure ScaleSeparatedEndRays (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) : Prop where
  separated : ∃ a b : EndRay H.endpoint, ∃ c > 0, ∃ d > 0,
    ∀ s ∈ Ioc (0 : ℝ) (min d (min a.length b.length)),
      c * s ≤ dist (a.point s) (b.point s)

structure SeparatedEndRays (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g)
    (angles : EndAngles H) : Prop where
  separated : ∃ a b : EndRay H.endpoint, ∃ beta > 0, ∃ d > 0,
    ∀ s ∈ Ioc (0 : ℝ) (min d (min a.length b.length)), beta ≤ endComparisonAngle a b s s

theorem comparisonAngle_self_le_of_dist_le {s gamma D : ℝ} (hs : 0 < s) (hgamma : 0 < gamma)
    (hgamma1 : gamma ≤ 1) (hD0 : 0 ≤ D) (hD : D ≤ gamma / Real.pi * s) :
    comparisonAngle s s D ≤ gamma := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hquarter : 0 ≤ gamma / 4 := by positivity
  have hquarterpi : gamma / 4 ≤ Real.pi / 2 := by
    have := Real.pi_gt_three
    linarith
  have hsin := Real.mul_le_sin hquarter hquarterpi
  have hkey : gamma / Real.pi * s ≤ 2 * s * Real.sin (gamma / 4) := by
    have h2 : 2 * s * (2 / Real.pi * (gamma / 4)) ≤ 2 * s * Real.sin (gamma / 4) :=
      mul_le_mul_of_nonneg_left hsin (by positivity)
    have h3 : 2 * s * (2 / Real.pi * (gamma / 4)) = gamma / Real.pi * s := by
      field_simp
      ring
    rwa [h3] at h2
  have hD' : D ≤ 2 * s * Real.sin (gamma / 4) := hD.trans hkey
  have hsq : D ^ 2 ≤ 4 * s ^ 2 * Real.sin (gamma / 4) ^ 2 := by
    nlinarith [hD', hD0]
  have hcosid : Real.cos (gamma / 2) = 1 - 2 * Real.sin (gamma / 4) ^ 2 := by
    rw [show gamma / 2 = 2 * (gamma / 4) by ring, Real.cos_two_mul_eq_one_sub]
  have htheta0 : 0 ≤ gamma / 2 := by positivity
  have hthetapi : gamma / 2 ≤ Real.pi := by linarith
  have hhalf : comparisonAngle s s D ≤ gamma / 2 :=
    comparisonAngle_le_of_sq_le_cos (θ := gamma / 2) hs hs htheta0 hthetapi (by
      rw [hcosid]
      nlinarith)
  linarith

theorem quotient_totallyBounded_iff_finset_angle_net (H : FiniteHorn g) (angles : EndAngles H) :
    TotallyBounded (univ : Set angles.quotient) ↔
      ∀ ε > 0, ∃ A : Finset (EndRay H.endpoint), ∀ b : EndRay H.endpoint,
        ∃ a ∈ A, angles.angle a b < ε := by
  classical
  rw [totallyBounded_univ_iff_finset_net]
  have honto : ∀ q : angles.quotient, ∃ a : EndRay H.endpoint, angles.classOf a = q :=
    fun q => angles.onto q
  choose rep hrep using honto
  constructor
  · intro h ε hε
    obtain ⟨t, ht⟩ := h ε hε
    refine ⟨t.image rep, fun b => ?_⟩
    obtain ⟨q, hqt, hqb⟩ := ht (angles.classOf b)
    refine ⟨rep q, Finset.mem_image_of_mem _ hqt, ?_⟩
    calc angles.angle (rep q) b
        = dist (angles.classOf (rep q)) (angles.classOf b) :=
          (angles.distance (rep q) b).symm
      _ = dist q (angles.classOf b) := by rw [hrep q]
      _ = dist (angles.classOf b) q := dist_comm _ _
      _ < ε := hqb
  · intro h ε hε
    obtain ⟨A, hA⟩ := h ε hε
    refine ⟨A.image angles.classOf, fun q => ?_⟩
    obtain ⟨b, rfl⟩ := angles.onto q
    obtain ⟨a, haA, hab⟩ := hA b
    exact ⟨angles.classOf a, Finset.mem_image_of_mem _ haA,
      calc dist (angles.classOf b) (angles.classOf a) = angles.angle a b := by
            rw [dist_comm, angles.distance a b]
        _ < ε := hab⟩

theorem totallyBounded_quotient_of_scaleDirectionNet (H : FiniteHorn g) (angles : EndAngles H)
    (hnet : ScaleDirectionNet g H) :
    TotallyBounded (univ : Set angles.quotient) := by
  classical
  rw [quotient_totallyBounded_iff_finset_angle_net H angles]
  intro eps heps
  have heta : 0 < min (eps / 2) 1 := lt_min (by linarith) one_pos
  have heta1 : min (eps / 2) 1 ≤ 1 := min_le_right _ _
  have hetaeps : min (eps / 2) 1 ≤ eps / 2 := min_le_left _ _
  have hdel : 0 < min (eps / 2) 1 / Real.pi := div_pos heta Real.pi_pos
  obtain ⟨A, d, hd, hA⟩ := hnet.net (min (eps / 2) 1 / Real.pi) hdel
  refine ⟨A, fun b => ?_⟩
  obtain ⟨a, haA, ha⟩ := hA b
  obtain ⟨dl, hdlpos, hdlle, hdl⟩ := angles.limit a b (min (eps / 2) 1) heta
  have hminpos : 0 < min d dl := lt_min hd hdlpos
  have hspos : 0 < min d dl / 2 := by linarith
  have hsd : min d dl / 2 ≤ d := by have := min_le_left d dl; linarith
  have hsdl : min d dl / 2 ≤ dl := by have := min_le_right d dl; linarith
  have hmem : min d dl / 2 ∈ Ioc (0 : ℝ) (min d (min b.length a.length)) :=
    ⟨hspos, le_min hsd (le_min (hsdl.trans (hdlle.trans (min_le_right _ _)))
      (hsdl.trans (hdlle.trans (min_le_left _ _))))⟩
  have hmemdl : min d dl / 2 ∈ Ioc (0 : ℝ) dl := ⟨hspos, hsdl⟩
  have hclose : dist (a.point (min d dl / 2)) (b.point (min d dl / 2)) <
      (min (eps / 2) 1 / Real.pi) * (min d dl / 2) := ha (min d dl / 2) hmem
  have hcmp : endComparisonAngle a b (min d dl / 2) (min d dl / 2) ≤ min (eps / 2) 1 :=
    comparisonAngle_self_le_of_dist_le hspos heta heta1 (dist_nonneg) hclose.le
  have hangle : angles.angle a b < min (eps / 2) 1 + min (eps / 2) 1 := by
    have h := (abs_lt.mp (hdl (min d dl / 2) hmemdl (min d dl / 2) hmemdl)).1
    linarith
  have h2m : min (eps / 2) 1 + min (eps / 2) 1 ≤ eps :=
    (add_le_add hetaeps hetaeps).trans_eq (by ring)
  exact ⟨a, haA, lt_of_lt_of_le hangle h2m⟩

theorem separatedEndRays_of_scaleSeparated (H : FiniteHorn g) (angles : EndAngles H)
    (h : ScaleSeparatedEndRays g H) : SeparatedEndRays g H angles := by
  obtain ⟨a, b, c, hc, d, hd, hsep⟩ := h.separated
  have hgamma : 0 < min c 2 := lt_min hc (by norm_num)
  have hgamma2 : min c 2 ≤ 2 := min_le_right _ _
  have hbeta : 0 < Real.arccos (1 - (min c 2) ^ 2 / 2) := by
    rw [Real.arccos_pos]
    nlinarith [hgamma]
  have hbetapi : Real.arccos (1 - (min c 2) ^ 2 / 2) ≤ Real.pi := Real.arccos_le_pi _
  refine ⟨a, b, Real.arccos (1 - (min c 2) ^ 2 / 2), hbeta, d, hd, ?_⟩
  intro s hs
  have hslen : s ≤ min a.length b.length := hs.2.trans (min_le_right _ _)
  have hsa : s ≤ a.length := hslen.trans (min_le_left _ _)
  have hsb : s ≤ b.length := hslen.trans (min_le_right _ _)
  have hms : min c 2 * s ≤ dist (a.point s) (b.point s) :=
    (mul_le_mul_of_nonneg_right (min_le_left c 2) hs.1.le).trans (hsep s hs)
  have hD0 : 0 ≤ dist (a.point s) (b.point s) := dist_nonneg
  have hD2s : dist (a.point s) (b.point s) ≤ s + s := by
    have h := dist_triangle (a.point s : UniformSpace.Completion W) H.endpoint
      (b.point s : UniformSpace.Completion W)
    rw [UniformSpace.Completion.dist_eq, a.radial s ⟨hs.1, hsa⟩] at h
    rw [dist_comm H.endpoint (b.point s : UniformSpace.Completion W),
      b.radial s ⟨hs.1, hsb⟩] at h
    linarith
  have hcos : Real.cos (endComparisonAngle a b s s) ≤
      Real.cos (Real.arccos (1 - (min c 2) ^ 2 / 2)) := by
    change Real.cos (comparisonAngle s s (dist (a.point s) (b.point s))) ≤
      Real.cos (Real.arccos (1 - (min c 2) ^ 2 / 2))
    rw [Real.cos_arccos (by nlinarith [hgamma2])
      (by nlinarith [hgamma]), cos_comparisonAngle hs.1 hs.1 (by rw [sub_self, abs_zero]; exact hD0) hD2s]
    have hsq : ((min c 2) * s) ^ 2 ≤ dist (a.point s) (b.point s) ^ 2 :=
      sq_le_sq' (by nlinarith [hD0, hms]) hms
    have hden : 0 < 2 * (s * s) := by nlinarith [hs.1]
    rw [comparisonCosine]
    rw [show 2 * s * s = 2 * (s * s) by ring]
    rw [div_le_iff₀ hden]
    nlinarith [hsq, hs.1, hgamma]
  by_contra hcon
  have hlt : endComparisonAngle a b s s < Real.arccos (1 - (min c 2) ^ 2 / 2) :=
    lt_of_not_ge hcon
  have hmono := Real.cos_lt_cos_of_nonneg_of_le_pi
    (x := endComparisonAngle a b s s) (y := Real.arccos (1 - (min c 2) ^ 2 / 2))
    (comparisonAngle_mem_Icc s s (dist (a.point s) (b.point s))).1 hbetapi hlt
  linarith [hcos, hmono]

theorem exists_pos_angle_of_separatedEndRays (H : FiniteHorn g) (angles : EndAngles H)
    (hsep : SeparatedEndRays g H angles) :
    ∃ a b : EndRay H.endpoint, 0 < angles.angle a b := by
  obtain ⟨a, b, beta, hbeta, d, hd, hsep'⟩ := hsep.separated
  obtain ⟨d', hd'pos, hd'le, hd'⟩ := angles.limit a b (beta / 2) (half_pos hbeta)
  have hminpos : 0 < min d d' := lt_min hd hd'pos
  have hspos : 0 < min d d' / 2 := by linarith
  have hsd : min d d' / 2 ≤ d := by have := min_le_left d d'; linarith
  have hsdd' : min d d' / 2 ≤ d' := by have := min_le_right d d'; linarith
  have hmem : min d d' / 2 ∈ Ioc (0 : ℝ) (min d (min a.length b.length)) :=
    ⟨hspos, le_min hsd (le_min (hsdd'.trans (hd'le.trans (min_le_left _ _)))
      (hsdd'.trans (hd'le.trans (min_le_right _ _))))⟩
  have hmemd' : min d d' / 2 ∈ Ioc (0 : ℝ) d' := ⟨hspos, hsdd'⟩
  have hlow := hsep' (min d d' / 2) hmem
  have hdist := (abs_lt.mp (hd' (min d d' / 2) hmemd' (min d d' / 2) hmemd')).2
  exact ⟨a, b, by linarith⟩

theorem separatedEndRays_of_exists_pos_angle (H : FiniteHorn g) (angles : EndAngles H)
    (h : ∃ a b : EndRay H.endpoint, 0 < angles.angle a b) :
    SeparatedEndRays g H angles := by
  obtain ⟨a, b, hab⟩ := h
  obtain ⟨dm, hdm, hdmle, hmono⟩ := angles.monotone a b
  obtain ⟨dl, hdl, hdlle, hlim⟩ := angles.limit a b (angles.angle a b / 2) (half_pos hab)
  have hdlmem : min dm dl ∈ Ioc (0 : ℝ) dl := ⟨lt_min hdm hdl, min_le_right _ _⟩
  have hlow : angles.angle a b / 2 < endComparisonAngle a b (min dm dl) (min dm dl) := by
    have h := (abs_lt.mp (hlim (min dm dl) hdlmem (min dm dl) hdlmem)).1
    linarith
  refine ⟨a, b, angles.angle a b / 2, half_pos hab, min dm dl, lt_min hdm hdl, ?_⟩
  intro s hs
  have hsd : s ≤ min dm dl := hs.2.trans (min_le_left _ _)
  have hslen : s ≤ min a.length b.length := hs.2.trans (min_le_right _ _)
  have hsdm : s ≤ dm := hsd.trans (min_le_left _ _)
  have hdle : min dm dl ≤ dm := min_le_left _ _
  have hmono' := hmono s (min dm dl) s (min dm dl) hs.1 hsd hdle hs.1 hsd hdle
  exact hlow.le.trans hmono'

theorem finite_horn_direction_compactness_of_inputs
    (hnet : ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ScaleDirectionNet g H)
    (hsep : ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ angles : EndAngles H, SeparatedEndRays g H angles) :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ angles : EndAngles H, letI := angles.metric;
        TotallyBounded (Set.univ : Set angles.quotient) ∧
          CompactSpace (UniformSpace.Completion angles.quotient) ∧
          ∃ a b : EndRay H.endpoint, 0 < angles.angle a b := by
  obtain ⟨H₁, hH₁, hnet'⟩ := hnet
  obtain ⟨H₂, hH₂, hsep'⟩ := hsep
  refine ⟨max H₁ H₂, lt_max_of_lt_left hH₁, ?_⟩
  intro g H hdepth angles
  have hnet'' := hnet' g H ((le_max_left H₁ H₂).trans hdepth)
  have hsep'' := hsep' g H ((le_max_right H₁ H₂).trans hdepth) angles
  have htb := totallyBounded_quotient_of_scaleDirectionNet H angles hnet''
  exact ⟨htb, compactSpace_completion_of_totallyBounded htb,
    exists_pos_angle_of_separatedEndRays H angles hsep''⟩

theorem separatedEndRays_iff_exists_pos_angle (H : FiniteHorn g) (angles : EndAngles H) :
    SeparatedEndRays g H angles ↔ ∃ a b : EndRay H.endpoint, 0 < angles.angle a b :=
  ⟨exists_pos_angle_of_separatedEndRays H angles, separatedEndRays_of_exists_pos_angle H angles⟩

theorem finite_horn_direction_compactness_of_geometric_inputs
    (hnet : ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ScaleDirectionNet g H)
    (hsep : ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ScaleSeparatedEndRays g H) :
    ∃ H₀ : ℝ, 0 < H₀ ∧ ∀ (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g),
      H₀ ≤ H.collar_depth → ∀ angles : EndAngles H, letI := angles.metric;
        TotallyBounded (Set.univ : Set angles.quotient) ∧
          CompactSpace (UniformSpace.Completion angles.quotient) ∧
          ∃ a b : EndRay H.endpoint, 0 < angles.angle a b := by
  obtain ⟨H₂, hH₂, hsep'⟩ := hsep
  exact finite_horn_direction_compactness_of_inputs hnet
    ⟨H₂, hH₂, fun g H hdepth angles => separatedEndRays_of_scaleSeparated H angles
      (hsep' g H hdepth)⟩


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
