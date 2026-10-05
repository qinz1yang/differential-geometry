import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1StandardFacts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.CliffordCoordinates

/-!
# Chapter-14 assembly, item L1, G3b / T1′: the rim slices and the separated end heights

Lane ASM-L1e (the necks of a ball–handle cycle, T1′ of `build-logs/scratch/ASM-L1b/Shortcut.lean`).

* `BallHandleCycle.rimSlice k b`: the end disk `b` of handle `k` together with the outer rim annulus
  `rimChart k b (θ, x, 0)`, `0 ≤ x ≤ 1`, on the boundary of the ball. It is the image of the level
  `τ = 0` of the neck of rim `(k, b)`. The slices are compact (`isCompact_rimSlice`) and pairwise
  disjoint (`disjoint_rimSlice`: different handles are disjoint, the two end disks of one handle
  are disjoint, an end disk meets the rim chart of the other end of its handle nowhere by
  `rim_handle` and `rim_label`, and rim chart targets are disjoint).
* `exists_pairwise_disjoint_open_nhds`: finitely many pairwise disjoint compact sets in a Hausdorff
  space have pairwise disjoint open neighbourhoods.
* `BallHandleCycle.rimHeight_lt` (E1): when both rims of a handle are products in the handle's
  coordinates with height profiles `σ₀` (end `false`) and `σ₁` (end `true`), the two product
  heights are separated, `σ₀ y₀ < 1 - σ₁ y₁` on `[0, a₀) × [0, a₁)`: otherwise, by the
  intermediate value theorem, `σ₀ u = 1 - σ₁ v` for some product heights `u, v`, and the two rim
  charts would meet at the corresponding handle point (`rim_disjoint`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskCharts_ASML1e : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

/-! ## The rim slices -/

/-- The slice of rim `(k, b)`: the end disk and the outer rim annulus `0 ≤ x ≤ 1` on the ball's
boundary (the image of the level `τ = 0` of the neck). -/
def BallHandleCycle.rimSlice {W : CompactCarrier.{u}} (C : BallHandleCycle W) (k : Fin C.len)
    (b : Bool) : Set W.Carrier :=
  (C.handle k).endDisk b ∪ C.rimChart k b '' (univ ×ˢ (Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}))

theorem iccEnd_injective : Injective iccEnd := by
  intro b b' h
  have h' : ((iccEnd b : Icc (0 : ℝ) 1) : ℝ) = iccEnd b' := by rw [h]
  cases b <;> cases b' <;> simp [iccEnd] at h' ⊢

theorem BallHandleCycle.rimAnnulus_subset_source {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    (k : Fin C.len) (b : Bool) :
    univ ×ˢ (Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}) ⊆ (C.rimChart k b).source := by
  rintro p ⟨-, hx, hy⟩
  apply (C.rim_source k b).mpr
  have hy' : p.2.2 = 0 := hy
  refine ⟨?_, ?_⟩
  · rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  · rw [hy', abs_zero]
    norm_num

theorem BallHandleCycle.isCompact_rimSlice {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    (k : Fin C.len) (b : Bool) : IsCompact (C.rimSlice k b) := by
  refine IsCompact.union ?_ ?_
  · exact isCompact_range ((C.handle k).smooth.continuous.comp
      (continuous_id.prodMk continuous_const))
  · refine IsCompact.image_of_continuousOn
      (isCompact_univ.prod (isCompact_Icc.prod isCompact_singleton)) ?_
    exact (C.rimChart k b).toOpenPartialHomeomorph.continuousOn.mono (C.rimAnnulus_subset_source k b)

/-- An end disk meets the rim annulus of a different rim nowhere. -/
theorem BallHandleCycle.endDisk_disjoint_rimAnnulus {W : CompactCarrier.{u}}
    (C : BallHandleCycle W) {k k' : Fin C.len} {b b' : Bool} (h : (k, b) ≠ (k', b')) :
    Disjoint ((C.handle k).endDisk b)
      (C.rimChart k' b' '' (univ ×ˢ (Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}))) := by
  rw [Set.disjoint_left]
  rintro z ⟨x₀, rfl⟩ ⟨p, hp, hpz⟩
  have hps := C.rimAnnulus_subset_source k' b' hp
  by_cases hk : k = k'
  · subst hk
    have hbb : b ≠ b' := fun hbb => h (by rw [hbb])
    have hH : C.rimChart k b' p ∈ range (C.handle k).map := hpz ▸ ⟨_, rfl⟩
    have hx : p.2.1 ≤ 0 := ((C.rim_handle k b' hps).mp hH).2
    have hp0 : p.2 = (0, 0) := by
      apply Prod.ext
      · exact le_antisymm hx hp.2.1.1
      · exact hp.2.2
    have hlab : C.rimChart k b' p ∈ C.rimChart k b' '' {p | p.2 = (0, 0)} := ⟨p, hp0, rfl⟩
    rw [C.rim_label k b'] at hlab
    obtain ⟨x₁, -, hx₁⟩ := hlab
    rw [hpz] at hx₁
    have := congrArg Prod.snd ((C.handle k).injective hx₁)
    exact hbb (iccEnd_injective this).symm
  · exact Set.disjoint_left.mp (C.disjoint_handle_target k' b' k hk) ⟨_, rfl⟩
      (hpz ▸ C.mem_target_of_mem_source hps)

theorem BallHandleCycle.disjoint_rimSlice {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    {k k' : Fin C.len} {b b' : Bool} (h : (k, b) ≠ (k', b')) :
    Disjoint (C.rimSlice k b) (C.rimSlice k' b') := by
  refine Disjoint.union_left (Disjoint.union_right ?_ (C.endDisk_disjoint_rimAnnulus h))
    (Disjoint.union_right (C.endDisk_disjoint_rimAnnulus (Ne.symm h)).symm ?_)
  · rw [Set.disjoint_left]
    rintro z ⟨x₀, rfl⟩ ⟨x₁, hx₁⟩
    by_cases hk : k = k'
    · subst hk
      have := congrArg Prod.snd ((C.handle k).injective hx₁)
      exact h (by rw [iccEnd_injective this])
    · exact Set.disjoint_left.mp (C.handle_disjoint hk) ⟨_, rfl⟩ ⟨_, hx₁⟩
  · rw [Set.disjoint_left]
    rintro z ⟨p, hp, rfl⟩ ⟨p', hp', hpp'⟩
    exact Set.disjoint_left.mp (C.rim_disjoint k b k' b' h)
      (C.mem_target_of_mem_source (C.rimAnnulus_subset_source k b hp))
      (hpp' ▸ C.mem_target_of_mem_source (C.rimAnnulus_subset_source k' b' hp'))

/-- Finitely many pairwise disjoint compact sets of a Hausdorff space have pairwise disjoint open
neighbourhoods. -/
theorem exists_pairwise_disjoint_open_nhds {X ι : Type*} [TopologicalSpace X] [T2Space X]
    [Finite ι] {K : ι → Set X} (hK : ∀ i, IsCompact (K i)) (hd : Pairwise (Disjoint on K)) :
    ∃ O : ι → Set X, (∀ i, IsOpen (O i)) ∧ (∀ i, K i ⊆ O i) ∧ Pairwise (Disjoint on O) := by
  classical
  have hsep : ∀ i j, i ≠ j → ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ K i ⊆ U ∧ K j ⊆ V ∧
      Disjoint U V := fun i j hij =>
    SeparatedNhds.of_isCompact_isCompact (hK i) (hK j) (hd hij)
  choose! U V hU hV hKU hKV hUV using hsep
  refine ⟨fun i => ⋂ j, ⋂ (_ : j ≠ i), U i j ∩ V j i, ?_, ?_, ?_⟩
  · intro i
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun hji =>
      (hU i j (Ne.symm hji)).inter (hV j i hji)
  · intro i
    exact subset_iInter fun j => subset_iInter fun hji =>
      subset_inter (hKU i j (Ne.symm hji)) (hKV j i hji)
  · intro i j hij
    refine Disjoint.mono ?_ ?_ (hUV i j hij)
    · exact (iInter_subset _ j).trans ((iInter_subset _ (Ne.symm hij)).trans inter_subset_left)
    · exact (iInter_subset _ i).trans ((iInter_subset _ hij).trans inter_subset_right)

/-! ## E1: separated end heights -/

/-- A smooth function with positive derivative on `[0, a)` is nonnegative there if it vanishes
at `0`. -/
theorem nonneg_of_deriv_pos_Ico {σ : ℝ → ℝ} {a : ℝ} (hσ : ContDiff ℝ ∞ σ) (hσ0 : σ 0 = 0)
    (hσd : ∀ y ∈ Ico 0 a, 0 < deriv σ y) {y : ℝ} (hy : y ∈ Ico 0 a) : 0 ≤ σ y := by
  have hmono : StrictMonoOn σ (Icc 0 y) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 y) hσ.continuous.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    exact hσd x ⟨hx.1.le, hx.2.trans hy.2⟩
  rw [← hσ0]
  exact hmono.monotoneOn ⟨le_rfl, hy.1⟩ ⟨hy.1, le_rfl⟩ hy.1

/-- The circle point of a unit vector of the plane. -/
theorem exists_planeOfCircle_eq {v : EuclideanSpace ℝ (Fin 2)} (hv : ‖v‖ = 1) :
    ∃ θ : Circle, planeOfCircle θ = v := by
  refine ⟨unitOf (Complex.orthonormalBasisOneI.repr.symm v), ?_⟩
  have hne : Complex.orthonormalBasisOneI.repr.symm v ≠ 0 := by
    intro h0
    have := congrArg norm h0
    rw [LinearIsometryEquiv.norm_map, hv, norm_zero] at this
    exact one_ne_zero this
  rw [planeOfCircle, coe_unitOf hne, LinearIsometryEquiv.norm_map, hv, inv_one, one_smul,
    LinearIsometryEquiv.apply_symm_apply]

theorem norm_planeOfCircle_eq_one (θ : Circle) : ‖planeOfCircle θ‖ = 1 := by
  rw [planeOfCircle, LinearIsometryEquiv.norm_map, Circle.norm_coe]

/-- **E1.** The product heights of the two rims of one handle are separated. -/
theorem BallHandleCycle.rimHeight_lt {W : CompactCarrier.{u}} (C : BallHandleCycle W)
    (k : Fin C.len) {a₀ a₁ : ℝ} (ha₀ : 3 / 4 < a₀) (ha₀' : a₀ ≤ 2) (ha₁ : 3 / 4 < a₁)
    (ha₁' : a₁ ≤ 2)
    (A₀ A₁ : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {ρ₀ σ₀ ρ₁ σ₁ : ℝ → ℝ} (hσ₀ : ContDiff ℝ ∞ σ₀) (hσ₁ : ContDiff ℝ ∞ σ₁)
    (hρ₀0 : ρ₀ 0 = 1) (hρ₁0 : ρ₁ 0 = 1) (hσ₀0 : σ₀ 0 = 0) (hσ₁0 : σ₁ 0 = 0)
    (hσ₀d : ∀ y ∈ Ico 0 a₀, 0 < deriv σ₀ y) (hσ₁d : ∀ y ∈ Ico 0 a₁, 0 < deriv σ₁ y)
    (heq₀ : ∀ (θ : Circle) (x y : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      -a₀ < x → x ≤ 0 → 0 ≤ y → y < a₀ →
      (w : EuclideanSpace ℝ (Fin 2)) = ρ₀ x • A₀ (planeOfCircle θ) →
      (t : ℝ) = endCoord false (σ₀ y) → C.rimChart k false (θ, (x, y)) = (C.handle k).map (w, t))
    (heq₁ : ∀ (θ : Circle) (x y : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      -a₁ < x → x ≤ 0 → 0 ≤ y → y < a₁ →
      (w : EuclideanSpace ℝ (Fin 2)) = ρ₁ x • A₁ (planeOfCircle θ) →
      (t : ℝ) = endCoord true (σ₁ y) → C.rimChart k true (θ, (x, y)) = (C.handle k).map (w, t))
    {y₀ y₁ : ℝ} (hy₀ : y₀ ∈ Ico 0 a₀) (hy₁ : y₁ ∈ Ico 0 a₁) : σ₀ y₀ < 1 - σ₁ y₁ := by
  by_contra hcon
  -- the intermediate value theorem along the segment `s ↦ (s y₀, s y₁)`
  let h : ℝ → ℝ := fun s => σ₀ (s * y₀) + σ₁ (s * y₁)
  have hh : ContinuousOn h (Icc 0 1) :=
    ((hσ₀.continuous.comp (continuous_id.mul continuous_const)).add
      (hσ₁.continuous.comp (continuous_id.mul continuous_const))).continuousOn
  have h0 : h 0 = 0 := by simp [h, hσ₀0, hσ₁0]
  have h1 : 1 ≤ h 1 := by
    simp only [h, one_mul]
    linarith [not_lt.mp hcon]
  obtain ⟨s, hs, hs1⟩ := intermediate_value_Icc zero_le_one hh
    (show (1 : ℝ) ∈ Icc (h 0) (h 1) from ⟨by rw [h0]; norm_num, h1⟩)
  set u := s * y₀ with hu_def
  set v := s * y₁ with hv_def
  have hu : u ∈ Ico 0 a₀ := ⟨mul_nonneg hs.1 hy₀.1,
    lt_of_le_of_lt (mul_le_of_le_one_left hy₀.1 hs.2) hy₀.2⟩
  have hv : v ∈ Ico 0 a₁ := ⟨mul_nonneg hs.1 hy₁.1,
    lt_of_le_of_lt (mul_le_of_le_one_left hy₁.1 hs.2) hy₁.2⟩
  have huv : σ₀ u + σ₁ v = 1 := hs1
  have hu0 := nonneg_of_deriv_pos_Ico hσ₀ hσ₀0 hσ₀d hu
  have hv0 := nonneg_of_deriv_pos_Ico hσ₁ hσ₁0 hσ₁d hv
  -- the common handle point
  let θ₀ : Circle := 1
  have hw₀ : ‖A₀ (planeOfCircle θ₀)‖ = 1 := by
    rw [LinearIsometryEquiv.norm_map, norm_planeOfCircle_eq_one]
  let w : ClosedCell 2 := ⟨A₀ (planeOfCircle θ₀), hw₀.le⟩
  let t : Icc (0 : ℝ) 1 := ⟨σ₀ u, hu0, by linarith⟩
  obtain ⟨θ₁, hθ₁⟩ := exists_planeOfCircle_eq (v := A₁.symm (A₀ (planeOfCircle θ₀)))
    (by rw [LinearIsometryEquiv.norm_map, hw₀])
  have hz₀ : C.rimChart k false (θ₀, (0, u)) = (C.handle k).map (w, t) :=
    heq₀ θ₀ 0 u w t (by linarith) le_rfl hu.1 hu.2 (by simp [w, hρ₀0]) (by simp [t, endCoord])
  have hz₁ : C.rimChart k true (θ₁, (0, v)) = (C.handle k).map (w, t) :=
    heq₁ θ₁ 0 v w t (by linarith) le_rfl hv.1 hv.2 (by simp [w, hρ₁0, hθ₁])
      (by simp only [t, endCoord, ite_true]; linarith)
  have hsrc : ∀ (b : Bool) (θ : Circle) {y a : ℝ}, y ∈ Ico 0 a → a ≤ 2 →
      (θ, ((0 : ℝ), y)) ∈ (C.rimChart k b).source := by
    intro b θ y a hy ha
    apply (C.rim_source k b).mpr
    refine ⟨by simp, ?_⟩
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hT₀ := C.mem_target_of_mem_source (hsrc false θ₀ hu ha₀')
  have hT₁ := C.mem_target_of_mem_source (hsrc true θ₁ hv ha₁')
  rw [hz₀] at hT₀
  rw [hz₁] at hT₁
  exact Set.disjoint_left.mp (C.rim_disjoint k false k true (by simp)) hT₀ hT₁

end GC.GraphManifold.Assembly
