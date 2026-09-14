import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Hamilton
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Restriction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

def arcInterval (T : Real) : RealTimeInterval :=
  if hT : 0 < T then RealTimeInterval.closed (-T) 0 (by linarith) else
    RealTimeInterval.closed 0 0 le_rfl

theorem arcInterval_carrier {T : Real} (hT : 0 < T) :
    (arcInterval T).carrier = Set.Icc (-T) 0 := by
  simp only [arcInterval, dif_pos hT, RealTimeInterval.closed]

theorem arcInterval_regular {T : Real} (hT : 0 < T) :
    (arcInterval T).regular = Set.Ioo (-T) 0 := by
  simp only [arcInterval, dif_pos hT, RealTimeInterval.closed]

theorem arcInterval_carrier_subset_Iic (T : Real) (hT : 0 < T) :
    (arcInterval T).carrier ⊆ Set.Iic 0 := by
  rw [arcInterval_carrier hT]
  intro t ht
  exact Set.mem_Iic.mpr ht.2

theorem arcInterval_carrier_subset {A T : Real} (hA : 0 < A) (hAT : A ≤ T) :
    (arcInterval A).carrier ⊆ (arcInterval T).carrier := by
  have hT : 0 < T := lt_of_lt_of_le hA hAT
  rw [arcInterval_carrier hA, arcInterval_carrier hT]
  intro t ht
  exact ⟨by linarith [ht.1], ht.2⟩

theorem arcInterval_regular_subset {A T : Real} (hA : 0 < A) (hAT : A ≤ T) :
    (arcInterval A).regular ⊆ (arcInterval T).regular := by
  have hT : 0 < T := lt_of_lt_of_le hA hAT
  rw [arcInterval_regular hA, arcInterval_regular hT]
  intro t ht
  exact ⟨by linarith [ht.1], ht.2⟩

theorem realTimeInterval_ext {D D' : RealTimeInterval} (hc : D.carrier = D'.carrier)
    (hr : D.regular = D'.regular) (hi : D.initial = D'.initial) : D = D' := by
  cases D
  cases D'
  simp_all

theorem not_arcInterval_eq_ancient (A : Real) (hA : 0 < A) :
    arcInterval A ≠ CanonicalNeighborhood.ancientTimeInterval := by
  intro h
  have hmem : (-A - 1) ∈ (arcInterval A).carrier := by
    rw [congrArg RealTimeInterval.carrier h, CanonicalNeighborhood.ancientTimeInterval_carrier]
    exact Set.mem_Iic.mpr (by linarith)
  rw [arcInterval_carrier hA] at hmem
  have := hmem.1
  linarith

theorem arcInterval_initial (T : Real) (hT : 0 < T) : (arcInterval T).initial = -T := by
  simp only [arcInterval, dif_pos hT, RealTimeInterval.closed]

theorem not_openInterval_carrier_subset_ancient {α b : Real}
    (h0 : (0 : Real) ∈ Set.Ioo α b) :
    ¬ ((RealTimeInterval.openInterval α b 0 h0).carrier ⊆
      CanonicalNeighborhood.ancientTimeInterval.carrier) := by
  intro h
  have hb : 0 < b := h0.2
  have hmem : b / 2 ∈ (RealTimeInterval.openInterval α b 0 h0).carrier :=
    ⟨by linarith [h0.1], by linarith⟩
  have hanc := h hmem
  rw [CanonicalNeighborhood.ancientTimeInterval_carrier] at hanc
  have : b / 2 ≤ 0 := Set.mem_Iic.mp hanc
  linarith

theorem not_ancient_carrier_subset_openInterval {α b : Real}
    (h0 : (0 : Real) ∈ Set.Ioo α b) :
    ¬ (CanonicalNeighborhood.ancientTimeInterval.carrier ⊆
      (RealTimeInterval.openInterval α b 0 h0).carrier) := by
  intro h
  have hmem : α - 1 ∈ CanonicalNeighborhood.ancientTimeInterval.carrier := by
    rw [CanonicalNeighborhood.ancientTimeInterval_carrier]
    exact Set.mem_Iic.mpr (by linarith [h0.1])
  have hlow : α < α - 1 := (h hmem).1
  linarith

theorem ne_openInterval_of_carrier_subset_Iic {D : RealTimeInterval}
    (hD : D.carrier ⊆ Set.Iic 0) {α b : Real} (h0 : (0 : Real) ∈ Set.Ioo α b) :
    D ≠ RealTimeInterval.openInterval α b 0 h0 := by
  intro h
  have hcarrier : (RealTimeInterval.openInterval α b 0 h0).carrier = D.carrier :=
    (congrArg RealTimeInterval.carrier h).symm
  refine not_openInterval_carrier_subset_ancient h0 ?_
  rw [hcarrier]
  exact hD

theorem ne_openInterval_of_arcInterval (A : Real) (hA : 0 < A) {α b : Real}
    (h0 : (0 : Real) ∈ Set.Ioo α b) :
    arcInterval A ≠ RealTimeInterval.openInterval α b 0 h0 :=
  ne_openInterval_of_carrier_subset_Iic (arcInterval_carrier_subset_Iic A hA) h0

theorem carrier_subset_iInter_arcHorizon_subset_arcHorizon {T : Nat → Real}
    {D : RealTimeInterval} (h : D.carrier ⊆ ⋂ m : Nat, Set.Icc (-(T m)) 0) (n : Nat) :
    D.carrier ⊆ Set.Icc (-(T n)) 0 :=
  h.trans (Set.iInter_subset _ n)

theorem not_Icc_subset_carrier_of_carrier_subset_iInter_arcHorizon {T : Nat → Real}
    {D : RealTimeInterval} (h : D.carrier ⊆ ⋂ m : Nat, Set.Icc (-(T m)) 0) {A : Real}
    (hApos : 0 < A) (hA : T 0 < A) : ¬ (Set.Icc (-A) 0 ⊆ D.carrier) := by
  intro hsub
  have h0 : Set.Icc (-A) 0 ⊆ Set.Icc (-(T 0)) 0 :=
    hsub.trans (carrier_subset_iInter_arcHorizon_subset_arcHorizon h 0)
  have hmem : (-A) ∈ Set.Icc (-A) 0 := ⟨le_rfl, by linarith⟩
  have := (h0 hmem).1
  linarith

theorem eventually_arcInterval_carrier_subset_of_tendsto (T : Nat → Real)
    (hT : Tendsto T atTop atTop) (A : Real) (hA : 0 < A) :
    ∀ᶠ n in atTop, (arcInterval A).carrier ⊆ (arcInterval (T n)).carrier := by
  filter_upwards [hT.eventually_ge_atTop A] with n hn
  exact arcInterval_carrier_subset hA hn

theorem tendsto_mul_atTop_of_pos_le_scalar (θ : Real) (hθ : 0 < θ) (t Q : Nat → Real)
    (ht : ∀ i, θ ≤ t i) (hQ : Tendsto Q atTop atTop) :
    Tendsto (fun i => t i * Q i) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro B
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hQ.eventually_ge_atTop (max 1 (B / θ)))
  refine ⟨N, fun i hi => ?_⟩
  have h1 : (1 : Real) ≤ Q i := (le_max_left _ _).trans (hN i hi)
  have hQpos : 0 < Q i := lt_of_lt_of_le one_pos h1
  have hti : 0 < t i := lt_of_lt_of_le hθ (ht i)
  by_cases hB : B ≤ 0
  · have : 0 < t i * Q i := mul_pos hti hQpos
    linarith
  · have h2 : B / θ ≤ Q i := (le_max_right _ _).trans (hN i hi)
    have hprod : θ * (B / θ) ≤ t i * Q i :=
      mul_le_mul (ht i) h2 (le_of_lt (div_pos (lt_of_not_ge hB) hθ)) hti.le
    rwa [mul_div_cancel₀ B (ne_of_gt hθ)] at hprod

theorem iUnion_arcWindow_carrier :
    (⋃ m : Nat, (arcInterval ((m : Real) + 1)).carrier) = Set.Iic 0 := by
  ext t
  constructor
  · intro ht
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ht
    rw [arcInterval_carrier (by positivity : (0 : Real) < (m : Real) + 1)] at hm
    exact Set.mem_Iic.mpr hm.2
  · intro ht
    have ht0 : t ≤ 0 := Set.mem_Iic.mp ht
    obtain ⟨m, hm⟩ := exists_nat_ge (-t)
    refine Set.mem_iUnion.mpr ⟨m, ?_⟩
    rw [arcInterval_carrier (by positivity : (0 : Real) < (m : Real) + 1)]
    exact ⟨by linarith [hm], ht0⟩

theorem iInter_arcHorizon_of_const (c : Real) :
    (⋂ _n : Nat, Set.Icc (-c) 0) = Set.Icc (-c) 0 := by
  ext t
  simp

theorem exists_nondegenerate_carrier_subset_iInter_arcHorizon_of_const (c : Real) (hc : 0 < c) :
    ∃ D : RealTimeInterval, D.regular.Nonempty ∧
      D.carrier ⊆ ⋂ _n : Nat, Set.Icc (-c) 0 :=
  ⟨arcInterval c,
    ⟨-c / 2, by
      rw [arcInterval_regular hc]
      exact ⟨by linarith, by linarith⟩⟩,
    by rw [iInter_arcHorizon_of_const c, arcInterval_carrier hc]⟩

structure FiniteArcFlowSeq (I : ModelWithCorners Real E H) where
  horizon : Nat → Real
  horizon_pos : ∀ n : Nat, 0 < horizon n
  term : (n : Nat) → PointedFlowData.{u, uE, uH} (I := I) (arcInterval (horizon n))

namespace FiniteArcFlowSeq

variable (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))

def tail (N : Nat) : FiniteArcFlowSeq.{u, uE, uH} (I := I) where
  horizon n := X.horizon (n + N)
  horizon_pos n := X.horizon_pos (n + N)
  term n := X.term (n + N)

def window (A : Real) (hA : 0 < A) (hcov : ∀ k : Nat, A ≤ X.horizon k) :
    PointedFlowSeq.{u, uE, uH} (I := I) where
  D := arcInterval A
  term k := (X.term k).timeRestrict (arcInterval A)
    (arcInterval_carrier_subset hA (hcov k))
    (arcInterval_regular_subset hA (hcov k))

@[simp] theorem window_atTime (A : Real) (hA : 0 < A) (hcov : ∀ k : Nat, A ≤ X.horizon k)
    (k : Nat) (t : Real) :
    ((X.window A hA hcov).term k).atTime t = (X.term k).atTime t := rfl

@[simp] theorem window_rmNormSq (A : Real) (hA : 0 < A) (hcov : ∀ k : Nat, A ≤ X.horizon k)
    (k : Nat) (t : Real) (x : (X.term k).M) :
    ((X.window A hA hcov).term k).rmNormSq t x = (X.term k).rmNormSq t x :=
  rfl

end FiniteArcFlowSeq

def windowHorizon (m : Nat) : Real := (m : Real) + 1

theorem windowHorizon_pos (m : Nat) : 0 < windowHorizon m := by
  rw [windowHorizon]
  positivity

theorem windowHorizon_mono : StrictMono windowHorizon := by
  intro a b hab
  rw [windowHorizon, windowHorizon]
  exact_mod_cast Nat.add_lt_add_right hab 1

namespace FiniteArcFlowSeq

variable (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
variable (hT : Tendsto X.horizon atTop atTop)

noncomputable def windowShift (m : Nat) : Nat :=
  Classical.choose (eventually_atTop.mp (hT.eventually_ge_atTop (windowHorizon m)))

theorem le_horizon_add_windowShift (m : Nat) :
    ∀ k : Nat, windowHorizon m ≤ X.horizon (k + X.windowShift hT m) :=
  fun k =>
    Classical.choose_spec (eventually_atTop.mp (hT.eventually_ge_atTop (windowHorizon m)))
      (k + X.windowShift hT m) (Nat.le_add_left _ _)

noncomputable def windowSeq (m : Nat) : PointedFlowSeq.{u, uE, uH} (I := I) :=
  (X.tail (X.windowShift hT m)).window (windowHorizon m) (windowHorizon_pos m)
    fun k => X.le_horizon_add_windowShift hT m k

@[simp] theorem windowSeq_atTime (m : Nat) (k : Nat) (t : Real) :
    ((X.windowSeq hT m).term k).atTime t = (X.term (k + X.windowShift hT m)).atTime t := rfl

def WindowConverges (m : Nat) (φ : Nat → Nat) : Prop :=
  ∃ L : PointedFlowData.{u, uE, uH} (I := I) (arcInterval (windowHorizon m)),
    Nonempty (SmoothCGHConverges (I := I) (X.windowSeq hT m) L φ)

end FiniteArcFlowSeq

def FiniteArcWindowCompactnessInput (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (hT : Tendsto X.horizon atTop atTop) : Prop :=
  ∀ (m : Nat) (φ : Nat → Nat), StrictMono φ →
    ∃ ψ : Nat → Nat, StrictMono ψ ∧ X.WindowConverges hT m (φ ∘ ψ)

theorem exists_strictMono_forall_shift_windowConverges
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (hT : Tendsto X.horizon atTop atTop)
    (hinput : FiniteArcWindowCompactnessInput X hT)
    (hsub : ∀ (m : Nat) (φ ψ : Nat → Nat)
      (L : PointedFlowData.{u, uE, uH} (I := I) (arcInterval (windowHorizon m))),
      StrictMono ψ →
      Nonempty (SmoothCGHConverges (I := I) (X.windowSeq hT m) L φ) →
      Nonempty (SmoothCGHConverges (I := I) (X.windowSeq hT m) L (φ ∘ ψ))) :
    ∃ φ : Nat → Nat, StrictMono φ ∧
      ∀ m : Nat, X.WindowConverges hT m (fun k => φ (m + k)) := by
  classical
  let P : Nat → (Nat → Nat) → Prop := fun m ρ =>
    ∃ L : PointedFlowData.{u, uE, uH} (I := I) (arcInterval (windowHorizon m)),
      Nonempty (SmoothCGHConverges (I := I) (X.windowSeq hT m) L ρ)
  have hPstep : ∀ m (φ : Nat → Nat), StrictMono φ →
      ∃ ψ, StrictMono ψ ∧ P m (φ ∘ ψ) :=
    hinput
  have hPsub : ∀ m (φ ψ : Nat → Nat), StrictMono ψ → P m φ → P m (φ ∘ ψ) := by
    intro m φ ψ hψ hP
    exact ⟨hP.choose, hsub m φ ψ hP.choose hψ hP.choose_spec⟩
  let step : (m : Nat) → {f : Nat → Nat // StrictMono f ∧ ∀ j ≤ m, P j f} →
      {f : Nat → Nat // StrictMono f ∧ ∀ j ≤ m + 1, P j f} := fun m Fm =>
    ⟨Fm.1 ∘ (hPstep (m + 1) Fm.1 Fm.2.1).choose,
     Fm.2.1.comp (hPstep (m + 1) Fm.1 Fm.2.1).choose_spec.1,
     by
       intro j hj
       rcases lt_or_eq_of_le hj with hlt | heq
       · exact hPsub j Fm.1 _ (hPstep (m + 1) Fm.1 Fm.2.1).choose_spec.1
           (Fm.2.2 j (Nat.lt_succ_iff.mp hlt))
       · subst heq
         exact (hPstep (m + 1) Fm.1 Fm.2.1).choose_spec.2⟩
  let base : {f : Nat → Nat // StrictMono f ∧ ∀ j ≤ 0, P j f} :=
    ⟨(hPstep 0 id strictMono_id).choose,
     (hPstep 0 id strictMono_id).choose_spec.1,
     by
       intro j hj
       obtain rfl : j = 0 := Nat.le_zero.mp hj
       simpa using (hPstep 0 id strictMono_id).choose_spec.2⟩
  let F : (m : Nat) → {f : Nat → Nat // StrictMono f ∧ ∀ j ≤ m, P j f} := fun m =>
    Nat.rec (motive := fun m => {f : Nat → Nat // StrictMono f ∧ ∀ j ≤ m, P j f})
      base step m
  have Fstep : ∀ m : Nat,
      (F (m + 1)).1 = (F m).1 ∘ (hPstep (m + 1) (F m).1 (F m).2.1).choose := fun _ => rfl
  let b : Nat → Nat := fun k =>
    Nat.rec ((F 0).1 0) (fun k prev => (F (k + 1)).1 (prev + 1)) k
  have bmono : StrictMono b := by
    apply strictMono_nat_of_lt_succ
    intro k
    have h1 : b k + 1 ≤ (F (k + 1)).1 (b k + 1) := (F (k + 1)).2.1.id_le (b k + 1)
    have h2 : b (k + 1) = (F (k + 1)).1 (b k + 1) := rfl
    omega
  have bmem : ∀ k : Nat, b k ∈ Set.range (F k).1 := by
    intro k
    cases k with
    | zero => exact ⟨0, rfl⟩
    | succ k => exact ⟨_, rfl⟩
  have hnest : ∀ n m : Nat, n ≤ m → Set.range (F m).1 ⊆ Set.range (F n).1 := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact fun _ hx => hx
    | succ m hnm ih =>
      intro x hx
      rw [Fstep m] at hx
      exact ih (Set.range_comp_subset_range _ _ hx)
  refine ⟨b, bmono, fun n => ?_⟩
  have hmem : ∀ k : Nat, b (n + k) ∈ Set.range (F n).1 :=
    fun k => hnest n (n + k) (Nat.le_add_right n k) (bmem (n + k))
  let τ : Nat → Nat := fun k => Classical.choose (hmem k)
  have hτspec : ∀ k : Nat, (F n).1 (τ k) = b (n + k) :=
    fun k => Classical.choose_spec (hmem k)
  have hτmono : StrictMono τ := by
    intro a c hac
    have h1 : b (n + a) < b (n + c) := bmono (Nat.add_lt_add_left hac n)
    rw [← hτspec a, ← hτspec c] at h1
    exact (F n).2.1.lt_iff_lt.mp h1
  have htail : (fun k => b (n + k)) = (F n).1 ∘ τ := by
    funext k
    exact (hτspec k).symm
  rw [htail]
  exact hPsub n (F n).1 τ hτmono ((F n).2.2 n le_rfl)

structure FiniteArcEstimates (X : FiniteArcFlowSeq.{u, uE, uH} (I := I)) : Prop where
  complete : ∀ k : Nat, ∀ t : Real, t ∈ (arcInterval (X.horizon k)).carrier →
    MetricComplete (I := I) ((X.term k).atTime t)
  curvature : ∀ A : Real, 0 < A → ∃ C : Real, 0 ≤ C ∧ ∀ k : Nat,
    ∀ t : Real, t ∈ Set.Icc (-A) 0 → ∀ x : (X.term k).M,
      (X.term k).rmNormSq (I := I) t x ≤ C
  connected : ∀ k : Nat,
    letI : TopologicalSpace (X.term k).M := (X.term k).topology
    ConnectedSpace (X.term k).M

section Estimates

variable {E' : Type uE} [NormedAddCommGroup E'] [InnerProductSpace Real E']
variable [FiniteDimensional Real E'] [CompleteSpace E']
variable {H' : Type uH} [TopologicalSpace H']
variable {I' : ModelWithCorners Real E' H'} [I'.Boundaryless]
variable [NeZero (Module.finrank Real E')]

structure WindowCompactnessEstimates (X : FiniteArcFlowSeq.{u, uE, uH} (I := I'))
    (A : Real) (hA : 0 < A) (hcov : ∀ k : Nat, A ≤ X.horizon k) where
  complete : FlowMetricComplete (I := I') (X.window A hA hcov)
  curvature : FlowCurvatureBoundedOnCompactWindows (I := I') (X.window A hA hcov)
  injectivity : FlowScaleInjectivityBound (I := I') (X.window A hA hcov)
  connected : ∀ k : Nat,
    letI : TopologicalSpace ((X.window A hA hcov).term k).M :=
      ((X.window A hA hcov).term k).topology
    ConnectedSpace ((X.window A hA hcov).term k).M

omit [I'.Boundaryless] [NeZero (Module.finrank Real E')] in
theorem windowCompactnessEstimates_complete_of_finiteArcEstimates
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I')) (hes : FiniteArcEstimates X)
    (A : Real) (hA : 0 < A) (hcov : ∀ k : Nat, A ≤ X.horizon k) :
    FlowMetricComplete (I := I') (X.window A hA hcov) :=
  ⟨fun k t ht => by
    have ht' : t ∈ (arcInterval (X.horizon k)).carrier :=
      arcInterval_carrier_subset hA (hcov k) ht
    simpa using hes.complete k t ht'⟩

omit [I'.Boundaryless] [NeZero (Module.finrank Real E')] in
theorem windowCompactnessEstimates_curvature_of_finiteArcEstimates
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I')) (hes : FiniteArcEstimates X)
    (A : Real) (hA : 0 < A) (hcov : ∀ k : Nat, A ≤ X.horizon k) :
    FlowCurvatureBoundedOnCompactWindows (I := I') (X.window A hA hcov) :=
  ⟨fun a b hab => by
    obtain ⟨C, hC, hbound⟩ := hes.curvature A hA
    refine ⟨C, hC, fun i t ht x => ?_⟩
    have ht' : t ∈ (arcInterval A).carrier := hab ht
    rw [arcInterval_carrier hA] at ht'
    exact hbound i t ht' x⟩

omit [I'.Boundaryless] [NeZero (Module.finrank Real E')] in
theorem windowCompactnessEstimates_connected_of_finiteArcEstimates
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I')) (hes : FiniteArcEstimates X)
    (A : Real) (hA : 0 < A) (hcov : ∀ k : Nat, A ≤ X.horizon k) :
    ∀ k : Nat,
      letI : TopologicalSpace ((X.window A hA hcov).term k).M :=
        ((X.window A hA hcov).term k).topology
      ConnectedSpace ((X.window A hA hcov).term k).M :=
  fun k => hes.connected k

end Estimates

theorem window_D_ne_openInterval (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (A : Real) (hA : 0 < A) (hcov : ∀ k : Nat, A ≤ X.horizon k) {α b : Real}
    (h0 : (0 : Real) ∈ Set.Ioo α b) :
    (X.window A hA hcov).D ≠ RealTimeInterval.openInterval α b 0 h0 :=
  ne_openInterval_of_arcInterval A hA h0

theorem window_D_ne_ancient (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (A : Real) (hA : 0 < A) (hcov : ∀ k : Nat, A ≤ X.horizon k) :
    (X.window A hA hcov).D ≠ CanonicalNeighborhood.ancientTimeInterval :=
  not_arcInterval_eq_ancient A hA

section Blowup

variable {M : Type u}
variable [TopologicalSpace M] [ChartedSpace Surgery.Topology.ThreeSpace M]
variable [IsManifold CanonicalNeighborhood.FiniteHorn.I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
theorem highCurvatureInterval_eq_arcInterval {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := CanonicalNeighborhood.FiniteHorn.I3) (M := M)
      (RealTimeInterval.closedOpen 0 T hT))
    (x : Nat → M) (t : Nat → Real) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (i : Nat) :
    CanonicalNeighborhood.FiniteHorn.highCurvatureInterval hT S x t htpos hpos i =
      arcInterval (t i * S.scalar (t i) (x i)) := by
  have hc : 0 < t i * S.scalar (t i) (x i) := mul_pos (htpos i) (hpos i)
  refine realTimeInterval_ext ?_ ?_ ?_
  · rw [arcInterval_carrier hc,
      CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_carrier]
  · rw [arcInterval_regular hc,
      CanonicalNeighborhood.FiniteHorn.highCurvatureInterval_regular]
  · rw [arcInterval_initial _ hc]
    rfl

noncomputable def highCurvatureArcSeq {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := CanonicalNeighborhood.FiniteHorn.I3) (M := M)
      (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : Nat → M) (t : Nat → Real)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : Real) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) :
    FiniteArcFlowSeq.{u, 0, 0} (I := CanonicalNeighborhood.FiniteHorn.I3) where
  horizon i := t i * S.scalar (t i) (x i)
  horizon_pos i := mul_pos (htpos i) (hpos i)
  term i := (highCurvatureInterval_eq_arcInterval hT S x t htpos hpos i) ▸
    (CanonicalNeighborhood.FiniteHorn.highCurvatureFlowSequence hT S hS x t htmem htpos
      hpos).term i

theorem highCurvatureArcSeq_horizon {T : Real} (hT : 0 < T)
    (S : SolutionOn (I := CanonicalNeighborhood.FiniteHorn.I3) (M := M)
      (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : Nat → M) (t : Nat → Real)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : Real) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) :
    (highCurvatureArcSeq hT S hS x t htmem htpos hpos).horizon =
      fun i => t i * S.scalar (t i) (x i) := rfl

theorem highCurvatureArcSeq_horizon_tendsto {T theta : Real} (hT : 0 < T) (htheta : 0 < theta)
    (S : SolutionOn (I := CanonicalNeighborhood.FiniteHorn.I3) (M := M)
      (RealTimeInterval.closedOpen 0 T hT))
    (hS : IsSolutionOn S) (x : Nat → M) (t : Nat → Real)
    (htmem : ∀ i, t i ∈ Set.Ico (0 : Real) T) (htpos : ∀ i, 0 < t i)
    (hpos : ∀ i, 0 < S.scalar (t i) (x i)) (htle : ∀ i, theta ≤ t i)
    (hscalar : Tendsto (fun i => S.scalar (t i) (x i)) atTop atTop) :
    Tendsto (highCurvatureArcSeq hT S hS x t htmem htpos hpos).horizon atTop atTop := by
  simpa only [highCurvatureArcSeq_horizon] using
    tendsto_mul_atTop_of_pos_le_scalar theta htheta t (fun i => S.scalar (t i) (x i)) htle
      hscalar

end Blowup

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
