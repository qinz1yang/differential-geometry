import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornTransverseControl
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
noncomputable section
open Filter Manifold Set
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u
variable {W : Type u} [MetricSpace W] [ChartedSpace ThreeSpace W]
  [IsManifold I3 ∞ W]

omit [ChartedSpace ThreeSpace W] [IsManifold I3 ∞ W] in
private theorem endRay_continuousOn {E : UniformSpace.Completion W} (a : EndRay E) :
    ContinuousOn a.point (Ioc (0 : ℝ) a.length) := by
  have hlip : LipschitzOnWith 1 a.point (Ioc (0 : ℝ) a.length) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simpa only [a.minimizing s hs t ht, NNReal.coe_one, one_mul, Real.dist_eq]
      using (le_rfl : |s - t| ≤ |s - t|)
  exact hlip.continuousOn

theorem finiteHorn_subend_separated_from_compact (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) {K : Set W} (hK : IsCompact K) :
    ∃ i, ∃ delta : ℝ, 0 < delta ∧
      ∀ x ∈ H.subend i, ∀ y ∈ K, delta ≤ dist x y := by
  by_cases hne : K.Nonempty
  · obtain ⟨y₀, _hy₀, hmin⟩ := hK.exists_isMinOn hne H.tube.continuous_height.continuousOn
    have hypos : 0 < H.tube.height y₀ := (H.tube.height_mem y₀).1
    let U : Set W := {x | H.tube.height y₀ / 2 < H.tube.height x}
    have hUopen : IsOpen U := isOpen_lt continuous_const H.tube.continuous_height
    have hKU : K ⊆ U := by
      intro y hy
      have hlow : H.tube.height y₀ ≤ H.tube.height y := hmin hy
      change H.tube.height y₀ / 2 < H.tube.height y
      linarith
    obtain ⟨delta, hdelta, hthick⟩ := hK.exists_thickening_subset_open hUopen hKU
    obtain ⟨i, hi⟩ := ((tendsto_order.mp H.cut_height_zero).2
      (H.tube.height y₀ / 2) (by positivity)).exists
    refine ⟨i, delta, hdelta, ?_⟩
    intro x hx y hy
    apply le_of_not_gt
    intro hdist
    have hxU : x ∈ U := hthick (Metric.mem_thickening_iff.mpr ⟨y, hy, hdist⟩)
    rw [H.subend_eq i] at hx
    change H.tube.height x < H.cut_height i at hx
    change H.tube.height y₀ / 2 < H.tube.height x at hxU
    linarith
  · refine ⟨0, 1, by norm_num, ?_⟩
    intro _x _hx y hy
    exact (hne ⟨y, hy⟩).elim

theorem finiteHorn_subend_radial_small (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) {eta : ℝ} (heta : 0 < eta) :
    ∃ i, ∀ x ∈ H.subend i, dist (x : UniformSpace.Completion W) H.endpoint < eta := by
  let r : ℝ := min (eta / 2) (H.axial.length / 2)
  have hr : 0 < r := lt_min (half_pos heta) (half_pos H.axial.length_pos)
  let K : Set W := H.axial.point '' Icc r H.axial.length
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn
    ((endRay_continuousOn H.axial).mono (fun s hs => ⟨hr.trans_le hs.1, hs.2⟩))
  obtain ⟨i, delta, hdelta, hseparate⟩ := finiteHorn_subend_separated_from_compact g H hK
  obtain ⟨j, hnear⟩ := finiteHorn_subend_near_axis g H
    (lt_min (half_pos heta) hdelta)
  have hmono : Antitone H.subend := antitone_nat_of_succ_le H.nested
  refine ⟨max i j, ?_⟩
  intro x hx
  obtain ⟨s, hs, hxs⟩ := hnear x (hmono (le_max_right i j) hx)
  have hsr : s < r := by
    by_contra hnot
    have hyK : H.axial.point s ∈ K := ⟨s, ⟨le_of_not_gt hnot, hs.2⟩, rfl⟩
    have hlow := hseparate x (hmono (le_max_left i j) hx) _ hyK
    exact (not_lt_of_ge hlow) (hxs.trans_le (min_le_right _ _))
  calc
    dist (x : UniformSpace.Completion W) H.endpoint ≤
        dist (x : UniformSpace.Completion W) (H.axial.point s : UniformSpace.Completion W) +
          dist (H.axial.point s : UniformSpace.Completion W) H.endpoint := dist_triangle _ _ _
    _ = dist x (H.axial.point s) + s := by
      rw [UniformSpace.Completion.dist_eq, H.axial.radial s hs]
    _ < eta := by
      have hxhalf := hxs.trans_le (min_le_left _ _)
      have hrhalf : r ≤ eta / 2 := min_le_left _ _
      linarith

theorem finiteHorn_endpoint_mem_closure_subend (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (i : ℕ) :
    H.endpoint ∈ closure ((fun x : W => (x : UniformSpace.Completion W)) '' H.subend i) := by
  obtain ⟨d, hd, hdL, htail⟩ := H.cofinal_axial i
  apply Metric.mem_closure_iff.mpr
  intro eta heta
  let s : ℝ := min d eta / 2
  have hs : 0 < s := half_pos (lt_min hd heta)
  have hsd : s ≤ d := by
    have h := min_le_left d eta
    dsimp [s]
    linarith
  have hseta : s < eta := by
    have h := min_le_right d eta
    dsimp [s]
    linarith
  refine ⟨(H.axial.point s : UniformSpace.Completion W),
    ⟨H.axial.point s, htail s ⟨hs, hsd⟩, rfl⟩, ?_⟩
  rw [dist_comm, H.axial.radial s ⟨hs, hsd.trans hdL⟩]
  exact hseta

theorem finiteHorn_unique_endpoint (g : SmoothRiemannianMetric I3 W) (H : FiniteHorn g) :
    (⋂ i, closure ((fun x : W => (x : UniformSpace.Completion W)) '' H.subend i)) =
      {H.endpoint} := by
  ext z
  constructor
  · intro hz
    apply mem_singleton_iff.mpr
    by_contra hne
    have hpos : 0 < dist z H.endpoint := dist_pos.mpr hne
    obtain ⟨i, hi⟩ := finiteHorn_subend_radial_small g H (half_pos hpos)
    have hsub : (fun x : W => (x : UniformSpace.Completion W)) '' H.subend i ⊆
        Metric.closedBall H.endpoint (dist z H.endpoint / 2) := by
      rintro _ ⟨x, hx, rfl⟩
      exact (hi x hx).le
    have hclosed := closure_minimal hsub Metric.isClosed_closedBall
    have hzdist : dist z H.endpoint ≤ dist z H.endpoint / 2 :=
      hclosed (mem_iInter.mp hz i)
    linarith
  · intro hz
    rcases mem_singleton_iff.mp hz with rfl
    exact mem_iInter.mpr (finiteHorn_endpoint_mem_closure_subend g H)

theorem finiteHorn_isCompact_closure_subend (g : SmoothRiemannianMetric I3 W)
    (H : FiniteHorn g) (i : ℕ) :
    IsCompact (closure ((fun x : W => (x : UniformSpace.Completion W)) '' H.subend i)) := by
  have htb : TotallyBounded ((fun x : W => (x : UniformSpace.Completion W)) '' H.subend i) := by
    apply Metric.totallyBounded_iff.mpr
    intro eta heta
    obtain ⟨j, hsmall⟩ := finiteHorn_subend_radial_small g H heta
    let K : Set W := H.tube.map '' (univ ×ˢ Icc (H.cut_height j) (H.cut_height i))
    have hK : IsCompact K := H.tube.isCompact_slab (H.cut_height_mem j).1 (H.cut_height_mem i).2
    have hKC : IsCompact ((fun x : W => (x : UniformSpace.Completion W)) '' K) :=
      hK.image (UniformSpace.Completion.continuous_coe W)
    obtain ⟨T, hT, hcover⟩ := Metric.totallyBounded_iff.mp hKC.totallyBounded eta heta
    refine ⟨insert H.endpoint T, hT.insert _, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    by_cases hxj : x ∈ H.subend j
    · exact mem_iUnion.mpr ⟨H.endpoint,
        mem_iUnion.mpr ⟨mem_insert H.endpoint T, hsmall x hxj⟩⟩
    · have hxK : x ∈ K := by
        have hxlow : H.cut_height j ≤ H.tube.height x := by
          apply le_of_not_gt
          intro hlt
          apply hxj
          rw [H.subend_eq j]
          exact hlt
        have hxhigh : H.tube.height x ≤ H.cut_height i := by
          rw [H.subend_eq i] at hx
          exact hx.le
        refine ⟨H.tube.map.symm x, ⟨mem_univ _, hxlow, hxhigh⟩, ?_⟩
        exact H.tube.map.right_inv' (by rw [H.tube.target_eq]; trivial)
      obtain ⟨y, hy⟩ := mem_iUnion.mp (hcover ⟨x, hxK, rfl⟩)
      obtain ⟨hyT, hxy⟩ := mem_iUnion.mp hy
      exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨mem_insert_of_mem _ hyT, hxy⟩⟩
  exact isCompact_iff_totallyBounded_isComplete.mpr ⟨htb.closure, isClosed_closure.isComplete⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
