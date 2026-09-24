import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureSequence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

theorem exists_lt_apply_of_strictMono {f : ℕ → ℕ} (hf : StrictMono f) (m : ℕ) :
    ∃ j : ℕ, m < f j := by
  refine ⟨m + 1, ?_⟩
  have h0 : f 0 + m ≤ f m := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hlt : f m < f (m + 1) := hf (Nat.lt_succ_self m)
      omega
  have h1 : f 0 + (m + 1) ≤ f (m + 1) := by
    have hlt : f m < f (m + 1) := hf (Nat.lt_succ_self m)
    omega
  omega

theorem le_apply_self_of_strictMono {f : ℕ → ℕ} (hf : StrictMono f) (n : ℕ) :
    n ≤ f n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hlt : f n < f (n + 1) := hf (Nat.lt_succ_self n)
    omega

theorem exists_strictMono_forall_shift_of_forall_exists_subseq
    (P : ℕ → (ℕ → ℕ) → Prop)
    (hsub : ∀ n (φ ψ : ℕ → ℕ), P n φ → StrictMono ψ → P n (φ ∘ ψ))
    (hstep : ∀ n (φ : ℕ → ℕ), StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P n (φ ∘ ψ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n : ℕ, P n (fun k => φ (n + k)) := by
  classical
  let step : (n : ℕ) → {f : ℕ → ℕ // StrictMono f ∧ ∀ j ≤ n, P j f} →
      {f : ℕ → ℕ // StrictMono f ∧ ∀ j ≤ n + 1, P j f} := fun n Fn =>
    ⟨Fn.1 ∘ (hstep (n + 1) Fn.1 Fn.2.1).choose,
      Fn.2.1.comp (hstep (n + 1) Fn.1 Fn.2.1).choose_spec.1,
      by
        intro j hj
        rcases lt_or_eq_of_le hj with hlt | heq
        · exact hsub j Fn.1 _ (Fn.2.2 j (Nat.lt_succ_iff.mp hlt))
            (hstep (n + 1) Fn.1 Fn.2.1).choose_spec.1
        · subst heq
          exact (hstep (n + 1) Fn.1 Fn.2.1).choose_spec.2⟩
  let base : {f : ℕ → ℕ // StrictMono f ∧ ∀ j ≤ 0, P j f} :=
    ⟨(hstep 0 id strictMono_id).choose,
      (hstep 0 id strictMono_id).choose_spec.1,
      by
        intro j hj
        obtain rfl : j = 0 := Nat.le_zero.mp hj
        simpa using (hstep 0 id strictMono_id).choose_spec.2⟩
  let F : (n : ℕ) → {f : ℕ → ℕ // StrictMono f ∧ ∀ j ≤ n, P j f} := fun n =>
    Nat.rec (motive := fun n => {f : ℕ → ℕ // StrictMono f ∧ ∀ j ≤ n, P j f})
      base step n
  have Fstep : ∀ n : ℕ,
      (F (n + 1)).1 = (F n).1 ∘ (hstep (n + 1) (F n).1 (F n).2.1).choose := by
    intro n
    rfl
  let b : ℕ → ℕ := fun k =>
    Nat.rec ((F 0).1 0)
      (fun k prev => (F (k + 1)).1
        (Classical.choose (exists_lt_apply_of_strictMono (F (k + 1)).2.1 prev))) k
  have bmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro k
    exact Classical.choose_spec (exists_lt_apply_of_strictMono (F (k + 1)).2.1 (b k))
  have bmem : ∀ k : ℕ, b k ∈ Set.range (F k).1 := by
    intro k
    cases k with
    | zero => exact ⟨0, rfl⟩
    | succ k => exact ⟨_, rfl⟩
  have hnest : ∀ n m : ℕ, n ≤ m → Set.range (F m).1 ⊆ Set.range (F n).1 := by
    intro n m hnm
    revert hnm
    induction m with
    | zero =>
      intro hnm
      have hn : n = 0 := Nat.le_zero.mp hnm
      subst hn
      exact fun _ hx => hx
    | succ m ih =>
      intro hnm
      rcases lt_or_eq_of_le hnm with hlt | heq
      · intro x hx
        rw [Fstep m] at hx
        exact ih (Nat.lt_succ_iff.mp hlt) (Set.range_comp_subset_range _ _ hx)
      · subst heq
        exact fun _ hx => hx
  refine ⟨b, bmono, fun n => ?_⟩
  have hmem : ∀ k : ℕ, b (n + k) ∈ Set.range (F n).1 :=
    fun k => hnest n (n + k) (Nat.le_add_right n k) (bmem (n + k))
  let τ : ℕ → ℕ := fun k => Classical.choose (hmem k)
  have hτspec : ∀ k : ℕ, (F n).1 (τ k) = b (n + k) :=
    fun k => Classical.choose_spec (hmem k)
  have hτmono : StrictMono τ := by
    intro a c hac
    have h1 : b (n + a) < b (n + c) := bmono (Nat.add_lt_add_left hac n)
    have h2 : (F n).1 (τ a) < (F n).1 (τ c) := by
      rw [hτspec a, hτspec c]
      exact h1
    exact (F n).2.1.lt_iff_lt.mp h2
  have htail : (fun k => b (n + k)) = (F n).1 ∘ τ := by
    funext k
    exact (hτspec k).symm
  rw [htail]
  exact hsub n (F n).1 τ ((F n).2.2 n le_rfl) hτmono

theorem exists_diag_subseq_of_tail
    (P : ℕ → (ℕ → ℕ) → Prop)
    (hstep : ∀ n (φ : ℕ → ℕ), StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ P n (φ ∘ ψ))
    (hsub : ∀ n (φ ψ : ℕ → ℕ), StrictMono ψ → P n φ → P n (φ ∘ ψ))
    (hextend : ∀ n (φ : ℕ → ℕ) (m : ℕ), P n (fun k => φ (k + m)) → P n φ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n : ℕ, P n φ := by
  obtain ⟨φ, hφ, htail⟩ := exists_strictMono_forall_shift_of_forall_exists_subseq P
    (fun n φ ψ h hψ => hsub n φ ψ hψ h) hstep
  exact ⟨φ, hφ, fun n => hextend n φ n (by simpa [Nat.add_comm] using htail n)⟩

theorem exists_strictMono_forall_shift_ne :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n k : ℕ, φ (n + k) ≠ n := by
  refine exists_strictMono_forall_shift_of_forall_exists_subseq
    (fun n φ => ∀ k : ℕ, φ k ≠ n) ?_ ?_
  · intro n φ ψ hφ _ k
    exact hφ (ψ k)
  · intro n φ hφ
    refine ⟨fun k => n + 1 + k, strictMono_nat_of_lt_succ fun k => by omega, ?_⟩
    intro k
    change φ (n + 1 + k) ≠ n
    have h := le_apply_self_of_strictMono hφ (n + 1 + k)
    omega

def windowInterval (n : ℕ) : RealTimeInterval :=
  RealTimeInterval.closed (-(n : ℝ)) 0 (neg_nonpos.mpr (Nat.cast_nonneg n))

@[simp] theorem windowInterval_carrier (n : ℕ) :
    (windowInterval n).carrier = Set.Icc (-(n : ℝ)) 0 := rfl

@[simp] theorem windowInterval_regular (n : ℕ) :
    (windowInterval n).regular = Set.Ioo (-(n : ℝ)) 0 := rfl

theorem windowInterval_carrier_mono {n m : ℕ} (h : n ≤ m) :
    (windowInterval n).carrier ⊆ (windowInterval m).carrier := by
  intro t ht
  rw [windowInterval_carrier] at ht ⊢
  exact ⟨by linarith [ht.1, Nat.cast_le (α := ℝ).mpr h], ht.2⟩

theorem windowInterval_carrier_subset_closed_iff {n : ℕ} {B : ℝ} (hB : 0 ≤ B) :
    (windowInterval n).carrier ⊆
      (RealTimeInterval.closed (-B) 0 (neg_nonpos.mpr hB)).carrier ↔ (n : ℝ) ≤ B := by
  constructor
  · intro h
    have hmem : -(n : ℝ) ∈ (windowInterval n).carrier := by
      rw [windowInterval_carrier]
      exact ⟨le_rfl, neg_nonpos.mpr (Nat.cast_nonneg n)⟩
    exact neg_le_neg_iff.mp (h hmem).1
  · intro h t ht
    rw [windowInterval_carrier] at ht
    exact ⟨by linarith [ht.1], ht.2⟩

theorem exists_mem_windowInterval_carrier_iff {t : ℝ} :
    (∃ n : ℕ, t ∈ (windowInterval n).carrier) ↔ t ≤ 0 := by
  constructor
  · rintro ⟨n, ht⟩
    rw [windowInterval_carrier] at ht
    exact ht.2
  · intro ht
    obtain ⟨n, hn⟩ := exists_nat_ge (-t)
    exact ⟨n, by rw [windowInterval_carrier]; exact ⟨by linarith, ht⟩⟩

theorem eventually_windowInterval_carrier_subset_closed
    (horizon : ℕ → ℝ) (hpos : ∀ i, 0 ≤ horizon i)
    (htendsto : Tendsto horizon atTop atTop) (n : ℕ) :
    ∀ᶠ i in atTop,
      (windowInterval n).carrier ⊆
        (RealTimeInterval.closed (-(horizon i)) 0 (neg_nonpos.mpr (hpos i))).carrier := by
  filter_upwards [htendsto.eventually_ge_atTop (n : ℝ)] with i hi
  exact (windowInterval_carrier_subset_closed_iff (hpos i)).mpr hi

theorem tendsto_mul_atTop_of_pos_le (theta : ℝ) (htheta : 0 < theta)
    (t Q : ℕ → ℝ) (ht : ∀ i, theta ≤ t i) (hQ : Tendsto Q atTop atTop) :
    Tendsto (fun i => t i * Q i) atTop atTop := by
  refine tendsto_atTop.2 fun B => ?_
  by_cases hB : B ≤ 0
  · filter_upwards [hQ.eventually_ge_atTop 0] with i hi
    have hti : 0 ≤ t i := htheta.le.trans (ht i)
    nlinarith [mul_nonneg hti hi]
  · have hB0 : 0 < B := lt_of_not_ge hB
    filter_upwards [hQ.eventually_ge_atTop (B / theta)] with i hi
    have hQ0 : 0 ≤ Q i := (div_nonneg hB0.le htheta.le).trans hi
    have h1 : B ≤ theta * Q i := by
      have hmul := mul_le_mul_of_nonneg_left hi htheta.le
      rwa [mul_div_cancel₀ B (ne_of_gt htheta)] at hmul
    have h2 : theta * Q i ≤ t i * Q i := mul_le_mul_of_nonneg_right (ht i) hQ0
    linarith

theorem iUnion_windowInterval_carrier :
    (⋃ n : ℕ, (windowInterval n).carrier) = Set.Iic 0 := by
  ext t
  rw [Set.mem_iUnion]
  exact exists_mem_windowInterval_carrier_iff

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
  (windowInterval windowInterval_carrier windowInterval_regular
    exists_strictMono_forall_shift_of_forall_exists_subseq)
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
  (ancientTimeInterval ancientTimeInterval_carrier ancientTimeInterval_regular)
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

universe u uE uH

namespace PointedFlowData

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {D : RealTimeInterval}

def restrictWindow (F : PointedFlowData.{u, uE, uH} (I := I) D) (n : ℕ)
    (hcar : (windowInterval n).carrier ⊆ D.carrier)
    (hreg : (windowInterval n).regular ⊆ D.regular) :
    PointedFlowData.{u, uE, uH} (I := I) (windowInterval n) :=
  F.timeRestrict _ hcar hreg

@[simp] theorem restrictWindow_atTime (F : PointedFlowData.{u, uE, uH} (I := I) D) (n : ℕ)
    (hcar : (windowInterval n).carrier ⊆ D.carrier)
    (hreg : (windowInterval n).regular ⊆ D.regular) (t : ℝ) :
    (F.restrictWindow n hcar hreg).atTime t = F.atTime t := rfl

@[simp] theorem restrictWindow_basepoint (F : PointedFlowData.{u, uE, uH} (I := I) D) (n : ℕ)
    (hcar : (windowInterval n).carrier ⊆ D.carrier)
    (hreg : (windowInterval n).regular ⊆ D.regular) :
    (F.restrictWindow n hcar hreg).basepoint = F.basepoint := rfl

end PointedFlowData

namespace PointedFlowSeq

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

def restrictWindow (X : PointedFlowSeq.{u, uE, uH} (I := I)) (n : ℕ)
    (hcar : (windowInterval n).carrier ⊆ X.D.carrier)
    (hreg : (windowInterval n).regular ⊆ X.D.regular) :
    PointedFlowSeq.{u, uE, uH} (I := I) where
  D := windowInterval n
  term i := (X.term i).restrictWindow n hcar hreg

@[simp] theorem restrictWindow_D (X : PointedFlowSeq.{u, uE, uH} (I := I)) (n : ℕ)
    (hcar : (windowInterval n).carrier ⊆ X.D.carrier)
    (hreg : (windowInterval n).regular ⊆ X.D.regular) :
    (X.restrictWindow n hcar hreg).D = windowInterval n := rfl

@[simp] theorem restrictWindow_atTime (X : PointedFlowSeq.{u, uE, uH} (I := I)) (n : ℕ)
    (hcar : (windowInterval n).carrier ⊆ X.D.carrier)
    (hreg : (windowInterval n).regular ⊆ X.D.regular) (t : ℝ) :
    (X.restrictWindow n hcar hreg).atTime t = X.atTime t := rfl

end PointedFlowSeq

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

theorem windowInterval_carrier_subset_of_eq_ancient {D : RealTimeInterval}
    (hD : D = ancientTimeInterval) (n : ℕ) :
    (windowInterval n).carrier ⊆ D.carrier := by
  rw [hD, ancientTimeInterval_carrier]
  intro t ht
  rw [windowInterval_carrier] at ht
  exact ht.2

theorem windowInterval_regular_subset_of_eq_ancient {D : RealTimeInterval}
    (hD : D = ancientTimeInterval) (n : ℕ) :
    (windowInterval n).regular ⊆ D.regular := by
  rw [hD, ancientTimeInterval_regular]
  intro t ht
  rw [windowInterval_regular] at ht
  exact ht.2

def WindowConverges (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D = ancientTimeInterval)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    (n : ℕ) (φ : ℕ → ℕ) : Prop :=
  Nonempty (SmoothCGHConverges (I := I)
    (X.restrictWindow n (windowInterval_carrier_subset_of_eq_ancient hD n)
      (windowInterval_regular_subset_of_eq_ancient hD n))
    (L.restrictWindow n (windowInterval_carrier_subset_of_eq_ancient rfl n)
      (windowInterval_regular_subset_of_eq_ancient rfl n))
    φ)

theorem exists_strictMono_forall_shift_of_windowConverges
    (X : PointedFlowSeq.{u, uE, uH} (I := I)) (hD : X.D = ancientTimeInterval)
    (L : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)
    (hsub : ∀ n (φ ψ : ℕ → ℕ), WindowConverges X hD L n φ → StrictMono ψ →
      WindowConverges X hD L n (φ ∘ ψ))
    (hstep : ∀ n (φ : ℕ → ℕ), StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ WindowConverges X hD L n (φ ∘ ψ)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n : ℕ, WindowConverges X hD L n (fun k => φ (n + k)) :=
  exists_strictMono_forall_shift_of_forall_exists_subseq
    (fun n φ => WindowConverges X hD L n φ) hsub hstep

end CheegerGromovCompactness
end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
  (windowInterval windowInterval_carrier windowInterval_carrier_subset_closed_iff
    eventually_windowInterval_carrier_subset_closed tendsto_mul_atTop_of_pos_le)
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
theorem highCurvatureInterval_window_carrier_subset_iff {T : ℝ} (hT : 0 < T)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (n i : ℕ) :
    (windowInterval n).carrier ⊆ (highCurvatureInterval hT S x t htpos hpos i).carrier ↔
      (n : ℝ) ≤ t i * S.scalar (t i) (x i) := by
  have hB : 0 ≤ t i * S.scalar (t i) (x i) :=
    (mul_pos (htpos i) (hpos i)).le
  rw [highCurvatureInterval_carrier]
  exact windowInterval_carrier_subset_closed_iff hB

omit [T2Space M] [SigmaCompactSpace M] in
theorem eventually_windowInterval_carrier_subset_highCurvatureInterval {T theta : ℝ}
    (hT : 0 < T) (htheta : 0 < theta)
    (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closedOpen 0 T hT))
    (x : ℕ → M) (t : ℕ → ℝ) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (htle : ∀ i, theta ≤ t i)
    (hscalar : Filter.Tendsto (fun i => S.scalar (t i) (x i)) Filter.atTop Filter.atTop)
    (n : ℕ) :
    ∀ᶠ i in Filter.atTop,
      (windowInterval n).carrier ⊆
        (highCurvatureInterval hT S x t htpos hpos i).carrier := by
  have hhorizon : Filter.Tendsto (fun i => t i * S.scalar (t i) (x i)) Filter.atTop
      Filter.atTop :=
    tendsto_mul_atTop_of_pos_le theta htheta t (fun i => S.scalar (t i) (x i)) htle hscalar
  have hpos' : ∀ i, 0 ≤ t i * S.scalar (t i) (x i) :=
    fun i => (mul_pos (htpos i) (hpos i)).le
  have hclosed := eventually_windowInterval_carrier_subset_closed
    (fun i => t i * S.scalar (t i) (x i)) hpos' hhorizon n
  filter_upwards [hclosed] with i hi
  rwa [highCurvatureInterval_carrier]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
