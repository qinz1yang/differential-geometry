import DifferentialGeometry.Analysis.Parabolic.MaximumPrinciple.KyFanBarrier
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

universe u

variable {X : Type u}

theorem rank_eq_at_positive_time_of_spreading
    {rank : Real → X → Nat} {T : Real}
    (hlower : ∀ t ∈ Ioc 0 T, ∀ x,
      ∀ᶠ s in 𝓝[Icc 0 T] t, rank t x ≤ rank s x)
    (hspread : ∀ {s t : Real}, 0 ≤ s → s < t → t ≤ T →
      ∀ x y, rank s x ≤ rank t y)
    {t : Real} (ht : t ∈ Ioc 0 T) (x y : X) :
    rank t x = rank t y := by
  have hsubset : Ioo 0 t ⊆ Icc 0 T := by
    intro s hs
    exact ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hxy : rank t x ≤ rank t y := by
    have hev : ∀ᶠ s in 𝓝[Ioo 0 t] t, rank t x ≤ rank s x :=
      (hlower t ht x).filter_mono (nhdsWithin_mono t hsubset)
    have hmem : ∀ᶠ s in 𝓝[Ioo 0 t] t, s ∈ Ioo 0 t := self_mem_nhdsWithin
    let _ : (𝓝[Ioo 0 t] t).NeBot := right_nhdsWithin_Ioo_neBot ht.1
    obtain ⟨s, hs_mem, hs_rank⟩ := (hmem.and hev).exists
    exact hs_rank.trans (hspread hs_mem.1.le hs_mem.2 ht.2 x y)
  have hyx : rank t y ≤ rank t x := by
    have hev : ∀ᶠ s in 𝓝[Ioo 0 t] t, rank t y ≤ rank s y :=
      (hlower t ht y).filter_mono (nhdsWithin_mono t hsubset)
    have hmem : ∀ᶠ s in 𝓝[Ioo 0 t] t, s ∈ Ioo 0 t := self_mem_nhdsWithin
    let _ : (𝓝[Ioo 0 t] t).NeBot := right_nhdsWithin_Ioo_neBot ht.1
    obtain ⟨s, hs_mem, hs_rank⟩ := (hmem.and hev).exists
    exact hs_rank.trans (hspread hs_mem.1.le hs_mem.2 ht.2 y x)
  exact le_antisymm hxy hyx

theorem rank_monotoneOn_of_spreading
    {rank : Real → X → Nat} {T : Real}
    (hspread : ∀ {s t : Real}, 0 ≤ s → s < t → t ≤ T →
      ∀ x y, rank s x ≤ rank t y)
    (x : X) : MonotoneOn (fun t => rank t x) (Ioc 0 T) := by
  intro s hs t ht hst
  rcases hst.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact hspread hs.1.le hlt ht.2 x x

theorem rank_eq_on_left_interval_of_spreading
    {rank : Real → X → Nat} {T : Real}
    (hlower : ∀ t ∈ Ioc 0 T, ∀ x,
      ∀ᶠ s in 𝓝[Icc 0 T] t, rank t x ≤ rank s x)
    (hspread : ∀ {s t : Real}, 0 ≤ s → s < t → t ≤ T →
      ∀ x y, rank s x ≤ rank t y)
    {t : Real} (ht : t ∈ Ioc 0 T) (x : X) :
    ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t, rank s x = rank t x := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp (hlower t ht x)
  let ε := min δ t
  have hεpos : 0 < ε := lt_min hδ ht.1
  have hεt : ε ≤ t := min_le_right δ t
  have hεδ : ε ≤ δ := min_le_left δ t
  refine ⟨ε, ⟨hεpos, hεt⟩, ?_⟩
  intro s hs
  have hs0 : 0 < s := by linarith [hs.1, hεt]
  have hsT : s ≤ T := hs.2.trans ht.2
  have hdist : dist s t < δ := by
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hs.2)]
    linarith [hs.1, hεδ]
  have hlowerst : rank t x ≤ rank s x :=
    hball ⟨Metric.mem_ball.mpr hdist, ⟨hs0.le, hsT⟩⟩
  have hupperst : rank s x ≤ rank t x := by
    rcases hs.2.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact hspread hs0.le hlt ht.2 x x
  exact le_antisymm hupperst hlowerst

theorem exists_rank_eq_on_initial_interval_of_spreading
    [Nonempty X] {rank : Real → X → Nat} {T : Real}
    (hT : 0 < T)
    (hspread : ∀ {s t : Real}, 0 ≤ s → s < t → t ≤ T →
      ∀ x y, rank s x ≤ rank t y) :
    ∃ δ ∈ Ioc 0 T, ∃ q : Nat, ∀ t ∈ Ioc 0 δ, ∀ x, rank t x = q := by
  let values : Set Nat := {q | ∃ t ∈ Ioc 0 T, ∃ x, rank t x = q}
  have hvalues : values.Nonempty := by
    exact ⟨rank T (Classical.choice inferInstance), T, ⟨hT, le_rfl⟩,
      Classical.choice inferInstance, rfl⟩
  let q := sInf values
  have hqmem : q ∈ values := Nat.sInf_mem hvalues
  obtain ⟨tstar, htstar, xstar, hxstar⟩ := hqmem
  refine ⟨tstar / 2,
    ⟨half_pos htstar.1, (half_le_self htstar.1.le).trans htstar.2⟩, q, ?_⟩
  intro t ht x
  have htT : t ∈ Ioc 0 T :=
    ⟨ht.1, ht.2.trans ((half_le_self htstar.1.le).trans htstar.2)⟩
  have hqle : q ≤ rank t x := Nat.sInf_le ⟨t, htT, x, rfl⟩
  have httstar : t < tstar := by linarith [ht.2, htstar.1]
  have hle : rank t x ≤ q := by
    rw [← hxstar]
    exact hspread ht.1.le httstar htstar.2 x xstar
  exact le_antisymm hle hqle

theorem rank_spatially_constant_and_locally_constant_from_left_of_spreading
    [Nonempty X] {rank : Real → X → Nat} {T : Real}
    (hT : 0 < T)
    (hlower : ∀ t ∈ Ioc 0 T, ∀ x,
      ∀ᶠ s in 𝓝[Icc 0 T] t, rank t x ≤ rank s x)
    (hspread : ∀ {s t : Real}, 0 ≤ s → s < t → t ≤ T →
      ∀ x y, rank s x ≤ rank t y) :
    (∀ t ∈ Ioc 0 T, ∀ x y, rank t x = rank t y) ∧
      (∀ x, MonotoneOn (fun t => rank t x) (Ioc 0 T)) ∧
      (∀ t ∈ Ioc 0 T, ∀ x,
        ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t, rank s x = rank t x) ∧
      ∃ δ ∈ Ioc 0 T, ∃ q : Nat,
        ∀ t ∈ Ioc 0 δ, ∀ x, rank t x = q := by
  refine ⟨?_, ?_, ?_, exists_rank_eq_on_initial_interval_of_spreading hT hspread⟩
  · intro t ht x y
    exact rank_eq_at_positive_time_of_spreading hlower hspread ht x y
  · intro x
    exact rank_monotoneOn_of_spreading hspread x
  · intro t ht x
    exact rank_eq_on_left_interval_of_spreading hlower hspread ht x

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

theorem finrank_range_eq_at_positive_time_of_spreading
    {A : ℝ → X → {B : E →L[ℝ] E // B.IsPositive}} {T : ℝ}
    (hcontinuous : ∀ x, ContinuousOn (fun t => A t x) (Icc 0 T))
    (hspread : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      Module.finrank ℝ (A s x).1.range ≤
        Module.finrank ℝ (A t y).1.range)
    {t : ℝ} (ht : t ∈ Ioc 0 T) (x y : X) :
    Module.finrank ℝ (A t x).1.range =
      Module.finrank ℝ (A t y).1.range := by
  apply rank_eq_at_positive_time_of_spreading
    (rank := fun s z => Module.finrank ℝ (A s z).1.range)
    (T := T) (t := t)
  · intro s hs z
    exact ContinuousLinearMap.IsPositive.eventually_finrank_range_ge_of_tendsto
      (hcontinuous z s ⟨hs.1.le, hs.2⟩)
  · exact hspread
  · exact ht

theorem finrank_range_le_of_lowerKyFanSum_pos_spreading
    {A : ℝ → X → {B : E →L[ℝ] E // B.IsPositive}} {T : ℝ}
    (hkyfan : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      ∀ k : ℕ, 1 ≤ k → k ≤ Module.finrank ℝ E →
        0 < ((A s x).2.toLinearMap.isSymmetric.lowerKyFanSum k) →
        0 < ((A t y).2.toLinearMap.isSymmetric.lowerKyFanSum k))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    (x y : X) :
    Module.finrank ℝ (A s x).1.range ≤
      Module.finrank ℝ (A t y).1.range := by
  exact LinearMap.IsPositive.finrank_range_le_of_lowerKyFanSum_pos
    (A s x).2.toLinearMap (A t y).2.toLinearMap
    (fun k hk₁ hkE hkpos => hkyfan hs hst ht x y k hk₁ hkE hkpos)

theorem finrank_range_le_of_lowerKyFanSum_pos_spreading_of_finrank_eq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    {A : E →L[ℝ] E} {B : F →L[ℝ] F}
    (hA : A.IsPositive) (hB : B.IsPositive)
    (hfinrank : Module.finrank ℝ E = Module.finrank ℝ F)
    (hkyfan : ∀ k : ℕ, 1 ≤ k → k ≤ Module.finrank ℝ E →
      0 < hA.toLinearMap.isSymmetric.lowerKyFanSum k →
      0 < hB.toLinearMap.isSymmetric.lowerKyFanSum k) :
    Module.finrank ℝ A.range ≤ Module.finrank ℝ B.range :=
  LinearMap.IsPositive.finrank_range_le_of_lowerKyFanSum_pos_of_finrank_eq
    hA.toLinearMap hB.toLinearMap hfinrank hkyfan

theorem finrank_range_spatially_constant_and_locally_constant_from_lowerKyFanSum_pos
    [Nonempty X]
    {A : ℝ → X → {B : E →L[ℝ] E // B.IsPositive}} {T : ℝ}
    (hT : 0 < T)
    (hcontinuous : ∀ x, ContinuousOn (fun t => A t x) (Icc 0 T))
    (hkyfan : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      ∀ k : ℕ, 1 ≤ k → k ≤ Module.finrank ℝ E →
        0 < ((A s x).2.toLinearMap.isSymmetric.lowerKyFanSum k) →
        0 < ((A t y).2.toLinearMap.isSymmetric.lowerKyFanSum k)) :
    (∀ t ∈ Ioc 0 T, ∀ x y,
      Module.finrank ℝ (A t x).1.range =
        Module.finrank ℝ (A t y).1.range) ∧
      (∀ x, MonotoneOn
        (fun t => Module.finrank ℝ (A t x).1.range) (Ioc 0 T)) ∧
      (∀ t ∈ Ioc 0 T, ∀ x,
        ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
          Module.finrank ℝ (A s x).1.range =
            Module.finrank ℝ (A t x).1.range) ∧
      ∃ δ ∈ Ioc 0 T, ∃ q : Nat, ∀ t ∈ Ioc 0 δ, ∀ x,
        Module.finrank ℝ (A t x).1.range = q := by
  refine rank_spatially_constant_and_locally_constant_from_left_of_spreading
    hT ?_ ?_
  · intro t ht x
    exact ContinuousLinearMap.IsPositive.eventually_finrank_range_ge_of_tendsto
      (hcontinuous x t ⟨ht.1.le, ht.2⟩)
  · intro s t hs hst ht x y
    exact finrank_range_le_of_lowerKyFanSum_pos_spreading
      hkyfan hs hst ht x y

theorem finrank_range_spatially_constant_and_locally_constant_from_left_of_spreading
    [Nonempty X]
    {A : ℝ → X → {B : E →L[ℝ] E // B.IsPositive}} {T : ℝ}
    (hT : 0 < T)
    (hcontinuous : ∀ x, ContinuousOn (fun t => A t x) (Icc 0 T))
    (hspread : ∀ {s t : ℝ}, 0 ≤ s → s < t → t ≤ T → ∀ x y,
      Module.finrank ℝ (A s x).1.range ≤
        Module.finrank ℝ (A t y).1.range) :
    (∀ t ∈ Ioc 0 T, ∀ x y,
      Module.finrank ℝ (A t x).1.range =
        Module.finrank ℝ (A t y).1.range) ∧
      (∀ x, MonotoneOn
        (fun t => Module.finrank ℝ (A t x).1.range) (Ioc 0 T)) ∧
      (∀ t ∈ Ioc 0 T, ∀ x,
        ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
          Module.finrank ℝ (A s x).1.range =
            Module.finrank ℝ (A t x).1.range) ∧
      ∃ δ ∈ Ioc 0 T, ∃ q : Nat, ∀ t ∈ Ioc 0 δ, ∀ x,
        Module.finrank ℝ (A t x).1.range = q := by
  apply rank_spatially_constant_and_locally_constant_from_left_of_spreading
    hT _ hspread
  intro t ht x
  exact ContinuousLinearMap.IsPositive.eventually_finrank_range_ge_of_tendsto
    (hcontinuous x t ⟨ht.1.le, ht.2⟩)

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

private theorem exists_smooth_bump_mul_le_of_pos_on
    {phi : M → ℝ} {K : Set M} {x : M} (hphi : ContinuousAt phi x)
    (hphiNonneg : ∀ y ∈ K, 0 ≤ phi y)
    (hx : 0 < phi x) {U : Set M} (hU : U ∈ 𝓝 x)
    {k : ℕ} (hk : 0 < k) :
    ∃ f : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
      (∀ y, 0 ≤ f y) ∧ HasCompactSupport f ∧
      tsupport f ⊆ U ∧ 0 < f x ∧
      ∀ y ∈ K, (k : ℝ) * f y ≤ phi y := by
  let U' : Set M := U ∩ phi ⁻¹' Ioi (phi x / 2)
  have hU' : U' ∈ 𝓝 x := by
    refine inter_mem hU (hphi.preimage_mem_nhds ?_)
    exact isOpen_Ioi.mem_nhds (half_lt_self hx)
  obtain ⟨chi, -, hchi⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp hU'
  let a : ℝ := phi x / (2 * (k : ℝ))
  let f : M → ℝ := fun y ↦ a * chi y
  have hkReal : 0 < (k : ℝ) := by exact_mod_cast hk
  have ha : 0 < a := div_pos hx (mul_pos zero_lt_two hkReal)
  refine ⟨f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contMDiff_const.mul chi.contMDiff
  · intro y
    exact mul_nonneg ha.le chi.nonneg
  · exact chi.hasCompactSupport.mul_left
  · exact tsupport_mul_subset_right.trans (hchi.trans inter_subset_left)
  · rw [show f x = a * chi x by rfl, chi.eq_one, mul_one]
    exact ha
  · intro y hyK
    by_cases hy : chi y = 0
    · simp only [f, hy, mul_zero, mul_zero]
      exact hphiNonneg y hyK
    · have hyU' : y ∈ U' := hchi (subset_tsupport _ hy)
      have hyphi : phi x / 2 < phi y := hyU'.2
      have hchile : chi y ≤ 1 := chi.le_one
      dsimp only [f, a]
      calc
        (k : ℝ) * (phi x / (2 * (k : ℝ)) * chi y) =
            phi x / 2 * chi y := by field_simp
        _ ≤ phi x / 2 := by
          exact mul_le_of_le_one_right (half_pos hx).le hchile
        _ ≤ phi y := hyphi.le

namespace PositiveSystem

open DifferentialGeometry
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem lowerKyFanSum_pos_at_of_local_dirichlet_solution_exists
    [NeZero (Module.finrank ℝ E)]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ z, FiniteDimensional ℝ (V z)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    {k : ℕ} (hkpos : 0 < k) (hk : k ≤ Module.finrank ℝ F)
    {Kset : Set M} (hKset : IsCompact Kset)
    (hKsetInterior : interior Kset ⊆ I.interior M)
    {x y : M} (hxKset : x ∈ interior Kset) (hyKset : y ∈ interior Kset)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc s t, ∀ z ∈ Kset, (A q z).IsPositive)
    (hphiCont : ContinuousOn (fun p : ℝ × M ↦
      (hAsymm p.1 p.2).lowerKyFanSum k) (Icc s t ×ˢ Kset))
    (hsource : 0 < (hAsymm s x).lowerKyFanSum k)
    {R : ℝ} (hR : ∀ q ∈ Icc s t, ∀ z ∈ Kset, ‖A q z‖ ≤ R)
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    {Klip : NNReal}
    (hreactionLip : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      LipschitzOnWith Klip (reaction q z)
        {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    (hdirichlet :
      ∀ (c : ℝ), 0 ≤ c → ∀ f₀ : M → ℝ,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ f₀ →
        (∀ z, 0 ≤ f₀ z) → HasCompactSupport f₀ →
        tsupport f₀ ⊆ interior Kset →
        (∃ z ∈ interior Kset, 0 < f₀ z) →
        ∃ f : ℝ → M → ℝ,
          ContinuousOn (fun p : ℝ × M ↦ f p.1 p.2)
              (Icc s t ×ˢ Kset) ∧
          (∀ z ∈ Kset, f s z = f₀ z) ∧
          (∀ q ∈ Icc s t, ∀ z ∈ frontier Kset, f q z = 0) ∧
          (∀ q ∈ Ioc s t, ∀ z ∈ interior Kset, 0 < f q z) ∧
          (∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
            DifferentiableAt ℝ (fun r ↦ f r z) q) ∧
          (∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
            MDifferentiableAt I 𝓘(ℝ, ℝ) (f q) z) ∧
          (∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
            MDiffAt (T% fun w : M ↦
              gradientFun (I := I) (G.metric q) (f q) w) z) ∧
          ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
            parabolicOperatorWithDrift (I := I) G T X f q z = -c * f q z)
    (hGconn : ∀ q ∈ Ioc s t,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      DifferentiableAt ℝ (fun r ↦ A r z) q)
    (hevolution : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      deriv (fun r ↦ A r z) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) :
    0 < (hAsymm t y).lowerKyFanSum k := by
  let phi : M → ℝ := fun z ↦ (hAsymm s z).lowerKyFanSum k
  have hsIcc : s ∈ Icc s t := ⟨le_rfl, hst.le⟩
  have hphiWithin : ContinuousWithinAt phi Kset x := by
    exact (hphiCont (s, x) ⟨hsIcc, interior_subset hxKset⟩).comp
      (continuousAt_const.prodMk continuousAt_id).continuousWithinAt
      (fun z hz ↦ ⟨hsIcc, hz⟩)
  have hKsetNhd : Kset ∈ 𝓝 x :=
    mem_of_superset (isOpen_interior.mem_nhds hxKset) interior_subset
  have hphiAt : ContinuousAt phi x := hphiWithin.continuousAt hKsetNhd
  have hphiNonneg : ∀ z ∈ Kset, 0 ≤ phi z := by
    intro z hz
    exact LinearMap.IsSymmetric.lowerKyFanSum_nonneg
      ((ContinuousLinearMap.isPositive_toLinearMap_iff (A s z)).mpr
        (hApos s hsIcc z hz)) k
  obtain ⟨f₀, hf₀Smooth, hf₀Nonneg, hf₀Compact, hf₀Support,
      hf₀x, hf₀Le⟩ :=
    exists_smooth_bump_mul_le_of_pos_on (I := I) (K := Kset)
      hphiAt hphiNonneg hsource
      (isOpen_interior.mem_nhds hxKset) hkpos
  let c : ℝ := (Klip : ℝ) + 1
  have hcNonneg : 0 ≤ c := by
    dsimp only [c]
    positivity
  obtain ⟨f, hfCont, hfInitialEq, hfBoundary, hfPos, hfTime,
      hfSpace, hfGrad, hfEquation⟩ :=
    hdirichlet c hcNonneg f₀ hf₀Smooth hf₀Nonneg hf₀Compact hf₀Support
      ⟨x, hxKset, hf₀x⟩
  have hc : (Klip : ℝ) < c := by
    dsimp only [c]
    linarith
  have hfInitial : ∀ z ∈ Kset,
      (k : ℝ) * f s z ≤ (hAsymm s z).lowerKyFanSum k := by
    intro z hz
    rw [hfInitialEq z hz]
    exact hf₀Le z hz
  exact lowerKyFanSum_pos_on_compact_set_of_dirichlet_solution
    (I := I) G cov hcov hT hs ht hkpos hk hKset hKsetInterior
      A hAsymm hApos hphiCont hR X reaction hreactionNull hreactionLip
      f hfCont hfInitial hfBoundary hfPos hfTime hfSpace hfGrad hc
      hfEquation hGconn hAt hevolution t ⟨hst, le_rfl⟩ y hyKset

theorem finrank_range_le_at_of_local_dirichlet_solution_exists
    [NeZero (Module.finrank ℝ E)]
    [VectorBundle ℝ E (TangentSpace I : M → Type _)]
    [fiberFinite : ∀ z, FiniteDimensional ℝ (V z)]
    (G : MetricConnectionFamily (I := I) (M := M) ℝ)
    (cov : ℝ → CovariantDerivative I F V)
    [∀ q, ContMDiffCovariantDerivative (cov q) ∞]
    (hcov : ∀ q, (cov q).IsMetricCompatible)
    {T : ℝ} (hT : 0 < T) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ T)
    {Kset : Set M} (hKset : IsCompact Kset)
    (hKsetInterior : interior Kset ⊆ I.interior M)
    {x y : M} (hxKset : x ∈ interior Kset) (hyKset : y ∈ interior Kset)
    (A : ℝ → Cₛ^∞⟮I; F →L[ℝ] F, (fun z : M ↦ V z →L[ℝ] V z)⟯)
    (hAsymm : ∀ q z,
      ((A q z : V z →L[ℝ] V z) : V z →ₗ[ℝ] V z).IsSymmetric)
    (hApos : ∀ q ∈ Icc s t, ∀ z ∈ Kset, (A q z).IsPositive)
    (hphiCont : ∀ k, k ≤ Module.finrank ℝ F →
      ContinuousOn (fun p : ℝ × M ↦
        (hAsymm p.1 p.2).lowerKyFanSum k) (Icc s t ×ˢ Kset))
    {R : ℝ} (hR : ∀ q ∈ Icc s t, ∀ z ∈ Kset, ‖A q z‖ ≤ R)
    (X : ℝ → (z : M) → TangentSpace I z)
    (reaction : ℝ → (z : M) →
      (V z →L[ℝ] V z) → V z →L[ℝ] V z)
    (hreactionNull : ∀ q z,
      satisfiesNullEigenvectorCondition (reaction q z))
    {Klip : NNReal}
    (hreactionLip : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      LipschitzOnWith Klip (reaction q z)
        {B : V z →L[ℝ] V z | B.IsPositive ∧ ‖B‖ ≤ 2 * R})
    (hdirichlet :
      ∀ (c : ℝ), 0 ≤ c → ∀ f₀ : M → ℝ,
        ContMDiff I 𝓘(ℝ, ℝ) ∞ f₀ →
        (∀ z, 0 ≤ f₀ z) → HasCompactSupport f₀ →
        tsupport f₀ ⊆ interior Kset →
        (∃ z ∈ interior Kset, 0 < f₀ z) →
        ∃ f : ℝ → M → ℝ,
          ContinuousOn (fun p : ℝ × M ↦ f p.1 p.2)
              (Icc s t ×ˢ Kset) ∧
          (∀ z ∈ Kset, f s z = f₀ z) ∧
          (∀ q ∈ Icc s t, ∀ z ∈ frontier Kset, f q z = 0) ∧
          (∀ q ∈ Ioc s t, ∀ z ∈ interior Kset, 0 < f q z) ∧
          (∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
            DifferentiableAt ℝ (fun r ↦ f r z) q) ∧
          (∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
            MDifferentiableAt I 𝓘(ℝ, ℝ) (f q) z) ∧
          (∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
            MDiffAt (T% fun w : M ↦
              gradientFun (I := I) (G.metric q) (f q) w) z) ∧
          ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
            parabolicOperatorWithDrift (I := I) G T X f q z = -c * f q z)
    (hGconn : ∀ q ∈ Ioc s t,
      G.connection q = LeviCivita (I := I) (G.metric q))
    (hAt : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      DifferentiableAt ℝ (fun r ↦ A r z) q)
    (hevolution : ∀ q ∈ Ioc s t, ∀ z ∈ interior Kset,
      deriv (fun r ↦ A r z) q =
        rawBundleEndomorphismConnLap (I := I) (G.metric q) (cov q)
            (fun w ↦ A q w) z +
          HomConnectionGen.homBundleCovariantDerivativeGen
            I M F V F V (cov q) (cov q) (fun w ↦ A q w) z (X q z) +
          reaction q z (A q z)) :
    Module.finrank ℝ (A s x).range ≤ Module.finrank ℝ (A t y).range := by
  have hsIcc : s ∈ Icc s t := ⟨le_rfl, hst.le⟩
  have htIcc : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  let ex := (trivializationAt F V x).linearEquivAt ℝ x
    (mem_baseSet_trivializationAt F V x)
  let ey := (trivializationAt F V y).linearEquivAt ℝ y
    (mem_baseSet_trivializationAt F V y)
  have hfinrank : Module.finrank ℝ (V x) = Module.finrank ℝ (V y) :=
    ex.finrank_eq.trans ey.finrank_eq.symm
  apply finrank_range_le_of_lowerKyFanSum_pos_spreading_of_finrank_eq
    (hApos s hsIcc x (interior_subset hxKset))
    (hApos t htIcc y (interior_subset hyKset)) hfinrank
  intro k hkpos hkx hsource
  have hkF : k ≤ Module.finrank ℝ F := by
    rw [← ex.finrank_eq]
    exact hkx
  exact lowerKyFanSum_pos_at_of_local_dirichlet_solution_exists
    (I := I) G cov hcov hT hs hst ht hkpos hkF hKset hKsetInterior
      hxKset hyKset A hAsymm hApos (hphiCont k hkF) hsource hR X
      reaction hreactionNull hreactionLip hdirichlet hGconn hAt hevolution

end PositiveSystem
