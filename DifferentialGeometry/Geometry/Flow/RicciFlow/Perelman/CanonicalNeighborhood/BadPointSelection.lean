import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

noncomputable section

universe u uE uH

open scoped Manifold ContDiff



theorem floor_div_lt_floor_div_of_two_mul_le {K R R' : Real}
    (hR : 0 < R) (hRR : 2 * R ≤ R') (hRK : R' ≤ K) :
    ⌊K / R'⌋₊ < ⌊K / R⌋₊ := by
  have hR2 : (0 : Real) < 2 * R := by linarith
  have hR' : (0 : Real) < R' := lt_of_lt_of_le hR2 hRR
  have hK : (0 : Real) ≤ K := le_trans hR'.le hRK
  have hKR : (2 : Real) ≤ K / R := by
    rw [le_div_iff₀ hR]
    linarith
  have hstep : K / R' ≤ K / R / 2 := by
    have h1 : K / R' ≤ K / (2 * R) := div_le_div_of_nonneg_left hK hR2 hRR
    have h2 : K / R / 2 = K / (2 * R) := by
      rw [div_div, mul_comm]
    rw [h2]
    exact h1
  have hhalf : (0 : Real) ≤ K / R / 2 := by linarith
  have hfloor1 : ⌊K / R'⌋₊ ≤ ⌊K / R / 2⌋₊ := Nat.floor_le_floor hstep
  have hfloor2 : ⌊K / R / 2⌋₊ + 1 ≤ ⌊K / R⌋₊ := by
    refine Nat.le_floor ?_
    have hle : ((⌊K / R / 2⌋₊ : ℕ) : Real) ≤ K / R / 2 := Nat.floor_le hhalf
    push_cast
    linarith
  omega



section PerFlow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

structure BadPointSelected (eps kappa : Real) (S : SolutionOn (I := I) (M := M) D)
    (T depth : Real) (xhat : M) (that : Real) (x : M) (t : Real) : Prop where
  bad : IsBadPoint.{u, uE, uH} (I := I) eps kappa S x t
  scalar_pos : 0 < S.scalar t x
  scalar_ge : S.scalar that xhat ≤ S.scalar t x
  time_le : t ≤ that
  displacement : that - 2 * depth / S.scalar that xhat ≤ t
  time_ge : 1 / 2 ≤ t
  depth_ratio : depth / S.scalar t x ≤ 1 / 4
  window_subset : Set.Icc (t - depth / S.scalar t x) t ⊆ Set.Icc (0 : Real) T
  higher_curvature_good : ∀ (y : M) (s : Real),
    s ∈ Set.Icc (t - depth / S.scalar t x) t → 2 * S.scalar t x ≤ S.scalar s y →
      IsGoodPoint.{u, uE, uH} (I := I) eps kappa S y s

theorem exists_isBadPoint_of_floor_weight
    {S : SolutionOn (I := I) (M := M) D} {eps kappa T K depth : Real}
    (hdepth : 0 ≤ depth)
    (hK : ∀ (y : M) (s : Real), s ∈ Set.Icc (0 : Real) T → S.scalar s y ≤ K) :
    ∀ (n : ℕ) (y : M) (s : Real), ⌊K / S.scalar s y⌋₊ = n →
      IsBadPoint.{u, uE, uH} (I := I) eps kappa S y s → 0 < S.scalar s y → s ≤ T →
        0 ≤ s - 2 * depth / S.scalar s y →
        ∃ (x : M) (t : Real),
          IsBadPoint.{u, uE, uH} (I := I) eps kappa S x t ∧ 0 < S.scalar t x ∧
            S.scalar s y ≤ S.scalar t x ∧ t ≤ s ∧
            s - 2 * depth / S.scalar s y ≤ t - depth / S.scalar t x ∧
            ∀ (y' : M) (s' : Real), s' ∈ Set.Icc (t - depth / S.scalar t x) t →
              2 * S.scalar t x ≤ S.scalar s' y' →
                IsGoodPoint.{u, uE, uH} (I := I) eps kappa S y' s' := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y s hn hbad hR hsT hs0
  have hnn : (0 : Real) ≤ depth / S.scalar s y := div_nonneg hdepth hR.le
  have hdouble : 2 * depth / S.scalar s y = 2 * (depth / S.scalar s y) := by ring
  by_cases hex : ∃ (y' : M) (s' : Real), s' ∈ Set.Icc (s - depth / S.scalar s y) s ∧
      2 * S.scalar s y ≤ S.scalar s' y' ∧
      IsBadPoint.{u, uE, uH} (I := I) eps kappa S y' s'
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
    refine ⟨x, t, hbadx, hRx, by linarith, le_trans htle hs'mem.2, by linarith, hgood⟩
  · refine ⟨y, s, hbad, hR, le_rfl, le_rfl, by linarith, ?_⟩
    intro y' s' hs' hRy'
    by_contra hcon
    have hcon' : IsBadPoint.{u, uE, uH} (I := I) eps kappa S y' s' := hcon
    exact hex ⟨y', s', hs', hRy', hcon'⟩

theorem exists_badPointSelected
    {S : SolutionOn (I := I) (M := M) D} {eps kappa T K depth : Real}
    (hdepth : 0 ≤ depth)
    (hK : ∀ (y : M) (s : Real), s ∈ Set.Icc (0 : Real) T → S.scalar s y ≤ K)
    {xhat : M} {that : Real}
    (hthat : 1 ≤ that) (hthatT : that ≤ T)
    (hQhat : 0 < S.scalar that xhat)
    (hdepthQ : depth ≤ S.scalar that xhat / 4)
    (hbad : IsBadPoint.{u, uE, uH} (I := I) eps kappa S xhat that) :
    ∃ (x : M) (t : Real),
      BadPointSelected (I := I) eps kappa S T depth xhat that x t := by
  have hhalf : 2 * depth / S.scalar that xhat ≤ 1 / 2 := by
    rw [div_le_iff₀ hQhat]
    linarith
  have hs0 : 0 ≤ that - 2 * depth / S.scalar that xhat := by linarith
  obtain ⟨x, t, hbadx, hRx, hRle, htle, hwin, hgood⟩ :=
    exists_isBadPoint_of_floor_weight (I := I) (S := S) (eps := eps) (kappa := kappa)
      (T := T) (K := K) hdepth hK _ xhat that rfl hbad hQhat hthatT hs0
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

theorem window_subset_carrier_of_two_mul_scalar_le
    {S : SolutionOn (I := I) (M := M) D} {eps T depth Q t : Real}
    (heps : 0 < eps) (hQ : 2 / eps ≤ Q) (hratio : depth / Q ≤ 1 / 4)
    (ht : 1 / 2 ≤ t) (htT : t ≤ T)
    (hslab : Set.Icc (0 : Real) T ⊆ D.carrier)
    {y : M} {s : Real} (hs : s ∈ Set.Icc (t - depth / Q) t)
    (hR : 2 * Q ≤ S.scalar s y) :
    Set.Icc (s - (eps * S.scalar s y)⁻¹) s ⊆ D.carrier := by
  have hQpos : 0 < Q := lt_of_lt_of_le (div_pos (by norm_num) heps) hQ
  have hs4 : 1 / 4 ≤ s := by
    have := hs.1
    linarith
  have hR4 : 4 / eps ≤ S.scalar s y := by
    have h2 : 2 * (2 / eps) = 4 / eps := by ring
    linarith
  have hRe : (4 : Real) ≤ eps * S.scalar s y := by
    have h1 : (4 : Real) ≤ S.scalar s y * eps := (div_le_iff₀ heps).1 hR4
    linarith [mul_comm eps (S.scalar s y)]
  have hinv : (eps * S.scalar s y)⁻¹ ≤ 1 / 4 := by
    have h1 : 1 / (eps * S.scalar s y) ≤ 1 / 4 :=
      div_le_div_of_nonneg_left zero_le_one (by norm_num) hRe
    rw [inv_eq_one_div]
    exact h1
  refine Set.Subset.trans (Set.Icc_subset_Icc (by linarith) (le_trans hs.2 htT)) hslab

end PerFlow



def selectionDepth (Q : Real) : Real := min (Real.sqrt Q) (Q / 4)

theorem selectionDepth_le_div_four (Q : Real) : selectionDepth Q ≤ Q / 4 := min_le_right _ _

theorem selectionDepth_nonneg {Q : Real} (hQ : 0 ≤ Q) : 0 ≤ selectionDepth Q :=
  le_min (Real.sqrt_nonneg Q) (by linarith)

theorem tendsto_selectionDepth {iota : Type*} {l : Filter iota} {Q : iota → Real}
    (hQ : Filter.Tendsto Q l Filter.atTop) :
    Filter.Tendsto (fun i => selectionDepth (Q i)) l Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun b => ?_
  have h1 : ∀ᶠ i in l, b ≤ Real.sqrt (Q i) :=
    Filter.tendsto_atTop.1 (Real.tendsto_sqrt_atTop.comp hQ) b
  have h2 : ∀ᶠ i in l, b ≤ Q i / 4 :=
    Filter.tendsto_atTop.1 (Filter.Tendsto.atTop_div_const (by norm_num) hQ) b
  filter_upwards [h1, h2] with i hi1 hi2
  exact le_min hi1 hi2

section Sequence

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

theorem eventually_exists_badPointSelected
    {Mi : ℕ → Type u} [∀ i, TopologicalSpace (Mi i)] [∀ i, ChartedSpace H (Mi i)]
    [∀ i, IsManifold I ∞ (Mi i)] [∀ i, IsManifold I 1 (Mi i)]
    {Di : ℕ → DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {S : ∀ i, SolutionOn (I := I) (M := Mi i) (Di i)}
    {eps kappa : Real} {T K : ℕ → Real}
    (hK : ∀ (i : ℕ) (y : Mi i) (s : Real),
      s ∈ Set.Icc (0 : Real) (T i) → (S i).scalar s y ≤ K i)
    {xhat : ∀ i, Mi i} {that : ℕ → Real}
    (hthat : ∀ i, 1 ≤ that i) (hthatT : ∀ i, that i ≤ T i)
    (hbad : ∀ i, IsBadPoint.{u, uE, uH} (I := I) eps kappa (S i) (xhat i) (that i))
    (hQhat : Filter.Tendsto (fun i => (S i).scalar (that i) (xhat i))
      Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun i => selectionDepth ((S i).scalar (that i) (xhat i)))
        Filter.atTop Filter.atTop ∧
      ∀ᶠ i in Filter.atTop, ∃ (x : Mi i) (t : Real),
        BadPointSelected (I := I) eps kappa (S i) (T i)
          (selectionDepth ((S i).scalar (that i) (xhat i))) (xhat i) (that i) x t := by
  refine ⟨tendsto_selectionDepth hQhat, ?_⟩
  filter_upwards [hQhat.eventually_gt_atTop 0] with i hi
  exact exists_badPointSelected (I := I) (selectionDepth_nonneg hi.le) (hK i)
    (hthat i) (hthatT i) hi (selectionDepth_le_div_four _) (hbad i)

end Sequence

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
