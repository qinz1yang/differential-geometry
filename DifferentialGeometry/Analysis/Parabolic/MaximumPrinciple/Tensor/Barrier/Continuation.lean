import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.Tensor.Barrier.Basic
open DifferentialGeometry.Tensor.RicciIdentity
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow

noncomputable section

open Bundle DifferentialGeometry.Tensor0SBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I 2 M]

def tensorBarrierUniformOnSlab
    (G : Real -> SmoothRiemannianMetric I M)
    (S : TwoTensorFamily (I := I) (M := M))
    (delta t0 : Real) : Prop :=
  ∀ epsilon : Real, SmallBarrierEps epsilon ->
    TwoTensorFamilyNonnegativeOn (I := I) (M := M)
      (tensorBarrierFamily (I := I) (M := M) G S epsilon delta t0)
      (Set.Icc t0 (t0 + delta))

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem tensor_nonnegative_on_fixed_slab_of_barrier
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {delta t0 : Real}
    (hdelta : 0 < delta)
    (hbarrier : tensorBarrierUniformOnSlab (I := I) (M := M) G S delta t0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S
      (Set.Icc t0 (t0 + delta)) := by
  intro t ht x v
  let q : Real := S t x v v
  let c : Real := (delta + t - t0) * (G t).inner x v v
  have htime_nonneg : 0 ≤ delta + t - t0 := by
    have ht_sub : 0 ≤ t - t0 := sub_nonneg.mpr ht.1
    have hsum : 0 ≤ delta + (t - t0) :=
      add_nonneg (le_of_lt hdelta) ht_sub
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsum
  have hmetric_nonneg : 0 ≤ (G t).inner x v v := by
    by_cases hv : v = 0
    · subst v
      simp
    · exact le_of_lt ((G t).pos x v hv)
  have hc_nonneg : 0 ≤ c := by
    simpa [c] using mul_nonneg htime_nonneg hmetric_nonneg
  have hforall : ∀ e : Real, 0 < e -> 0 ≤ q + e := by
    intro e he
    let eta : Real := min 1 (e / (c + 1))
    have hden_pos : 0 < c + 1 :=
      add_pos_of_nonneg_of_pos hc_nonneg zero_lt_one
    have hdiv_pos : 0 < e / (c + 1) :=
      div_pos he hden_pos
    have heta_pos : 0 < eta := by
      dsimp [eta]
      exact lt_min zero_lt_one hdiv_pos
    have heta_le_one : eta ≤ 1 := by
      dsimp [eta]
      exact min_le_left 1 (e / (c + 1))
    have heta_le_div : eta ≤ e / (c + 1) := by
      dsimp [eta]
      exact min_le_right 1 (e / (c + 1))
    have heta_small : SmallBarrierEps eta := ⟨heta_pos, heta_le_one⟩
    have hbar_eta :
        0 ≤
          tensorBarrierFamily (I := I) (M := M) G S eta delta t0 t x v v :=
      hbarrier eta heta_small t ht x v
    have hbar_q : 0 ≤ q + eta * c := by
      simpa [tensorBarrierFamily, q, c, mul_assoc] using hbar_eta
    have heta_nonneg : 0 ≤ eta := le_of_lt heta_pos
    have hcoeff_le : c ≤ c + 1 := le_add_of_nonneg_right zero_le_one
    have hprod_le : eta * c ≤ eta * (c + 1) :=
      mul_le_mul_of_nonneg_left hcoeff_le heta_nonneg
    have hden_ne : c + 1 ≠ 0 := ne_of_gt hden_pos
    have heta_mul_den_le : eta * (c + 1) ≤ e := by
      have hmul_le : eta * (c + 1) ≤ (e / (c + 1)) * (c + 1) :=
        mul_le_mul_of_nonneg_right heta_le_div (le_of_lt hden_pos)
      have hdiv_mul : (e / (c + 1)) * (c + 1) = e := by
        field_simp [hden_ne]
      simpa [hdiv_mul] using hmul_le
    have heta_c_le : eta * c ≤ e := by
      exact le_trans hprod_le heta_mul_den_le
    exact le_trans hbar_q (by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left heta_c_le q)
  have hq_nonneg : 0 ≤ q := le_of_forall_pos_le_add hforall
  simpa [q] using hq_nonneg

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [IsManifold I 2 M] in
private theorem nonnegative_time_isClosed
    {S : TwoTensorFamily (I := I) (M := M)}
    {T : Real}
    (hcont : ∀ x, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : Real => S t x v w) (Set.Icc 0 T)) :
    IsClosed ({t : Real | TwoTensorFamilyNonnegativeAtTime (I := I) (M := M)
      S t} ∩ Set.Icc 0 T) := by
  rw [show
      {t : Real | TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t} ∩
          Set.Icc 0 T =
        Set.Icc 0 T ∩ ⋂ x : M, ⋂ v : TangentSpace I x,
          (Set.Icc 0 T ∩ (fun t : Real => S t x v v) ⁻¹' Set.Ici 0) by
    ext t
    constructor
    · intro ht
      refine ⟨ht.2, ?_⟩
      rw [Set.mem_iInter]
      intro x
      rw [Set.mem_iInter]
      intro v
      exact ⟨ht.2, ht.1 x v⟩
    · intro ht
      refine ⟨?_, ht.1⟩
      intro x v
      exact ((Set.mem_iInter.mp (Set.mem_iInter.mp ht.2 x) v)).2]
  exact isClosed_Icc.inter
    (isClosed_iInter fun x =>
      isClosed_iInter fun v =>
        (hcont x v v).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici)

omit [FiniteDimensional ℝ E] [IsManifold I 1 M] [IsManifold I 2 M] in
theorem tensor_nonnegative_on_of_barrier_continuation
    {G : Real -> SmoothRiemannianMetric I M}
    {S : TwoTensorFamily (I := I) (M := M)}
    {T : Real}
    (hcont : ∀ x, ∀ v w : TangentSpace I x,
      ContinuousOn (fun t : Real => S t x v w) (Set.Icc 0 T))
    (hinit : TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S 0)
    (hstep : ∀ t0 : Real, t0 ∈ Set.Icc 0 T -> t0 < T ->
      TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t0 ->
      ∃ delta : Real, 0 < delta ∧ t0 + delta ≤ T ∧
        tensorBarrierUniformOnSlab (I := I) (M := M) G S delta t0) :
    TwoTensorFamilyNonnegativeOn (I := I) (M := M) S (Set.Icc 0 T) := by
  let P : Set Real := {t : Real | TwoTensorFamilyNonnegativeAtTime (I := I) (M := M) S t}
  have hclosed : IsClosed (P ∩ Set.Icc 0 T) := by
    simpa [P] using nonnegative_time_isClosed (I := I) (M := M) (S := S) hcont
  have hP : Set.Icc 0 T ⊆ P := by
    refine hclosed.Icc_subset_of_forall_exists_gt (a := 0) (b := T) ?_ ?_
    · simpa [P] using hinit
    · intro t ht y hy
      have htIcc : t ∈ Set.Icc 0 T := ⟨ht.2.1, le_of_lt ht.2.2⟩
      obtain ⟨delta, hdelta, _hdeltaT, hbarrier⟩ :=
        hstep t htIcc ht.2.2 ht.1
      have hslab : TwoTensorFamilyNonnegativeOn (I := I) (M := M) S
          (Set.Icc t (t + delta)) :=
        tensor_nonnegative_on_fixed_slab_of_barrier (I := I) (M := M)
          (G := G) (S := S) hdelta hbarrier
      let z : Real := min y (t + delta)
      have htz : t < z := by
        dsimp [z]
        exact lt_min hy (by linarith)
      have hz_le_delta : z ≤ t + delta := by
        dsimp [z]
        exact min_le_right y (t + delta)
      have hz_le_y : z ≤ y := by
        dsimp [z]
        exact min_le_left y (t + delta)
      have hzP : P z :=
        hslab z ⟨le_of_lt htz, hz_le_delta⟩
      exact ⟨z, hzP, htz, hz_le_y⟩
  intro t ht
  exact hP ht


end

end DifferentialGeometry.PDE.RicciFlow
