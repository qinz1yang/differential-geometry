import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelTheorem

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

noncomputable section

universe u uE uH

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

section PerFlow

variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] {D : RealTimeInterval}

structure OrientedBadPointSelected (orient : OrientationDatum I) (eps kappa : Real)
    (S : SolutionOn (I := I) (M := M) D)
    (T depth : Real) (xhat : M) (that : Real) (x : M) (t : Real) : Prop where
  bad : ¬ IsOrientedGoodPoint (I := I) orient eps kappa S x t
  scalar_pos : 0 < S.scalar t x
  scalar_ge : S.scalar that xhat ≤ S.scalar t x
  time_le : t ≤ that
  displacement : that - 2 * depth / S.scalar that xhat ≤ t
  time_ge : 1 / 2 ≤ t
  depth_ratio : depth / S.scalar t x ≤ 1 / 4
  window_subset : Set.Icc (t - depth / S.scalar t x) t ⊆ Set.Icc (0 : Real) T
  higher_curvature_good : ∀ (y : M) (s : Real),
    s ∈ Set.Icc (t - depth / S.scalar t x) t → 2 * S.scalar t x ≤ S.scalar s y →
      IsOrientedGoodPoint (I := I) orient eps kappa S y s

theorem OrientedBadPointSelected.higher_curvature_isGoodPoint
    {orient : OrientationDatum I} {eps kappa T depth that t : Real}
    {S : SolutionOn (I := I) (M := M) D} {xhat x : M}
    (h : OrientedBadPointSelected orient eps kappa S T depth xhat that x t)
    {y : M} {s : Real} (hs : s ∈ Set.Icc (t - depth / S.scalar t x) t)
    (hR : 2 * S.scalar t x ≤ S.scalar s y) :
    IsGoodPoint.{u, uE, uH} (I := I) eps kappa S y s :=
  isGoodPoint_of_isOrientedGoodPoint (h.higher_curvature_good y s hs hR)

theorem orientedBadPointSelected_trivial_iff
    {eps kappa T depth that t : Real} {S : SolutionOn (I := I) (M := M) D} {xhat x : M} :
    OrientedBadPointSelected (trivialOrientationDatum I) eps kappa S T depth xhat that x t ↔
      BadPointSelected (I := I) eps kappa S T depth xhat that x t := by
  constructor
  · intro h
    exact ⟨fun hg => h.bad (isOrientedGoodPoint_trivialOrientationDatum_iff.2 hg),
      h.scalar_pos, h.scalar_ge, h.time_le, h.displacement, h.time_ge, h.depth_ratio,
      h.window_subset, fun y s hs hR => h.higher_curvature_isGoodPoint hs hR⟩
  · intro h
    exact ⟨fun hg => h.bad (isOrientedGoodPoint_trivialOrientationDatum_iff.1 hg),
      h.scalar_pos, h.scalar_ge, h.time_le, h.displacement, h.time_ge, h.depth_ratio,
      h.window_subset, fun y s hs hR =>
        isOrientedGoodPoint_trivialOrientationDatum_iff.2 (h.higher_curvature_good y s hs hR)⟩

private theorem exists_orientedBadPoint_of_floor_weight
    {orient : OrientationDatum I} {S : SolutionOn (I := I) (M := M) D}
    {eps kappa T K depth : Real} (hdepth : 0 ≤ depth)
    (hK : ∀ (y : M) (s : Real), s ∈ Set.Icc (0 : Real) T → S.scalar s y ≤ K) :
    ∀ (n : ℕ) (y : M) (s : Real), ⌊K / S.scalar s y⌋₊ = n →
      (¬ IsOrientedGoodPoint (I := I) orient eps kappa S y s) →
      0 < S.scalar s y → s ≤ T → 0 ≤ s - 2 * depth / S.scalar s y →
      ∃ (x : M) (t : Real),
        (¬ IsOrientedGoodPoint (I := I) orient eps kappa S x t) ∧ 0 < S.scalar t x ∧
          S.scalar s y ≤ S.scalar t x ∧ t ≤ s ∧
          s - 2 * depth / S.scalar s y ≤ t - depth / S.scalar t x ∧
          ∀ (y' : M) (s' : Real), s' ∈ Set.Icc (t - depth / S.scalar t x) t →
            2 * S.scalar t x ≤ S.scalar s' y' →
              IsOrientedGoodPoint (I := I) orient eps kappa S y' s' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y s hn hbad hR hsT hs0
  have hnn : (0 : Real) ≤ depth / S.scalar s y := div_nonneg hdepth hR.le
  have hdouble : 2 * depth / S.scalar s y = 2 * (depth / S.scalar s y) := by ring
  by_cases hex : ∃ (y' : M) (s' : Real), s' ∈ Set.Icc (s - depth / S.scalar s y) s ∧
      2 * S.scalar s y ≤ S.scalar s' y' ∧
      ¬ IsOrientedGoodPoint (I := I) orient eps kappa S y' s'
  · obtain ⟨y', s', hs'mem, hR2, hbad'⟩ := hex
    have hR' : 0 < S.scalar s' y' := lt_of_lt_of_le (by linarith) hR2
    have hnn' : (0 : Real) ≤ 2 * depth / S.scalar s' y' :=
      div_nonneg (by linarith) hR'.le
    have hhalf : 2 * depth / S.scalar s' y' ≤ depth / S.scalar s y := by
      have h1 : 2 * depth / S.scalar s' y' ≤ 2 * depth / (2 * S.scalar s y) :=
        div_le_div_of_nonneg_left (by linarith) (by linarith) hR2
      have h2 : 2 * depth / (2 * S.scalar s y) = depth / S.scalar s y :=
        mul_div_mul_left depth (S.scalar s y) (by norm_num : (2 : Real) ≠ 0)
      rw [h2] at h1
      exact h1
    have hchain : s - 2 * depth / S.scalar s y ≤ s' - 2 * depth / S.scalar s' y' := by
      have h1 : s - depth / S.scalar s y ≤ s' := hs'mem.1
      linarith
    have hs'0 : 0 ≤ s' - 2 * depth / S.scalar s' y' := le_trans hs0 hchain
    have hs'T : s' ≤ T := le_trans hs'mem.2 hsT
    have hKbound : S.scalar s' y' ≤ K := hK y' s' ⟨by linarith, hs'T⟩
    have hlt : ⌊K / S.scalar s' y'⌋₊ < ⌊K / S.scalar s y⌋₊ :=
      floor_div_lt_floor_div_of_two_mul_le hR hR2 hKbound
    rw [hn] at hlt
    obtain ⟨x, t, hbadx, hRx, hRle, htle, hwin, hgood⟩ :=
      ih _ hlt y' s' rfl hbad' hR' hs'T hs'0
    exact ⟨x, t, hbadx, hRx, by linarith, le_trans htle hs'mem.2, by linarith, hgood⟩
  · refine ⟨y, s, hbad, hR, le_rfl, le_rfl, by linarith, ?_⟩
    intro y' s' hs' hRy'
    by_contra hcon
    exact hex ⟨y', s', hs', hRy', hcon⟩

theorem exists_orientedBadPointSelected
    {orient : OrientationDatum I} {S : SolutionOn (I := I) (M := M) D}
    {eps kappa T K depth : Real} (hdepth : 0 ≤ depth)
    (hK : ∀ (y : M) (s : Real), s ∈ Set.Icc (0 : Real) T → S.scalar s y ≤ K)
    {xhat : M} {that : Real} (hthat : 1 ≤ that) (hthatT : that ≤ T)
    (hQhat : 0 < S.scalar that xhat) (hdepthQ : depth ≤ S.scalar that xhat / 4)
    (hbad : ¬ IsOrientedGoodPoint (I := I) orient eps kappa S xhat that) :
    ∃ (x : M) (t : Real),
      OrientedBadPointSelected orient eps kappa S T depth xhat that x t := by
  have hhalf : 2 * depth / S.scalar that xhat ≤ 1 / 2 := by
    rw [div_le_iff₀ hQhat]
    linarith
  have hs0 : 0 ≤ that - 2 * depth / S.scalar that xhat := by linarith
  obtain ⟨x, t, hbadx, hRx, hRle, htle, hwin, hgood⟩ :=
    exists_orientedBadPoint_of_floor_weight (I := I) (S := S) (orient := orient)
      (eps := eps) (kappa := kappa) (T := T) (K := K)
      hdepth hK _ xhat that rfl hbad hQhat hthatT hs0
  have hdepthRx : 0 ≤ depth / S.scalar t x := div_nonneg hdepth hRx.le
  have hratio : depth / S.scalar t x ≤ 1 / 4 := by
    have h1 : depth / S.scalar t x ≤ depth / S.scalar that xhat :=
      div_le_div_of_nonneg_left hdepth hQhat hRle
    have h2 : depth / S.scalar that xhat ≤ 1 / 4 := by
      rw [div_le_iff₀ hQhat]
      linarith
    linarith
  exact ⟨x, t,
    { bad := hbadx
      scalar_pos := hRx
      scalar_ge := hRle
      time_le := htle
      displacement := by linarith
      time_ge := by linarith
      depth_ratio := hratio
      window_subset := Set.Icc_subset_Icc (by linarith) (le_trans htle hthatT)
      higher_curvature_good := hgood }⟩

end PerFlow

theorem eventually_exists_orientedBadPointSelected
    {Mi : ℕ → Type u} [∀ i, TopologicalSpace (Mi i)] [∀ i, ChartedSpace H (Mi i)]
    [∀ i, IsManifold I ∞ (Mi i)] [∀ i, IsManifold I 1 (Mi i)]
    {Di : ℕ → RealTimeInterval} {S : ∀ i, SolutionOn (I := I) (M := Mi i) (Di i)}
    {orient : OrientationDatum I} {eps kappa : Real} {T K : ℕ → Real}
    (hK : ∀ (i : ℕ) (y : Mi i) (s : Real),
      s ∈ Set.Icc (0 : Real) (T i) → (S i).scalar s y ≤ K i)
    {xhat : ∀ i, Mi i} {that : ℕ → Real}
    (hthat : ∀ i, 1 ≤ that i) (hthatT : ∀ i, that i ≤ T i)
    (hbad : ∀ i, ¬ IsOrientedGoodPoint (I := I) orient eps kappa (S i) (xhat i) (that i))
    (hQhat : Filter.Tendsto (fun i => (S i).scalar (that i) (xhat i))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun i => selectionDepth ((S i).scalar (that i) (xhat i)))
        Filter.atTop Filter.atTop ∧
      ∀ᶠ i in Filter.atTop, ∃ (x : Mi i) (t : Real),
        OrientedBadPointSelected orient eps kappa (S i) (T i)
          (selectionDepth ((S i).scalar (that i) (xhat i))) (xhat i) (that i) x t := by
  refine ⟨tendsto_selectionDepth hQhat, ?_⟩
  filter_upwards [hQhat.eventually_gt_atTop 0] with i hi
  exact exists_orientedBadPointSelected (I := I) (selectionDepth_nonneg hi.le) (hK i)
    (hthat i) (hthatT i) hi (selectionDepth_le_div_four _) (hbad i)

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
