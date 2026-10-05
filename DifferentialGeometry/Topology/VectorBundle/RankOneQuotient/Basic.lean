import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Rank-one bundles as quotients of `S(V) × ℝ`

Lane LFR54-QUOT (chapter 13, LFR51/LFR52 → LFR54 → chapter-14 `ZeroModel`). For a vector bundle
`V → B` with one-dimensional fibres and an inner product on each fibre, the unit sphere bundle meets
every fibre in exactly two antipodal points. Suppose `ν : Σ → TotalSpace F V` is injective, takes unit
values, hits every unit vector, and intertwines an involution `τ` of `Σ` with `v ↦ -v`. Then the map
`Φ (p, t) = t • ν p` (`rankOneParam`) from `Σ × ℝ` onto the total space is surjective
(`rankOneParam_surjective`) and identifies exactly `(p, t)` with `(τ p, -t)`
(`rankOneParam_eq_iff`). This is the set-level form of `V ≅ (S(V) × ℝ) / ((u, t) ∼ (-u, -t))`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Module

namespace DifferentialGeometry.Topology.VectorBundle.RankOneQuotient

section Fibre

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- In a one-dimensional inner product space every vector is its component along a unit vector. -/
theorem eq_inner_smul_of_finrank_eq_one (hW : finrank ℝ W = 1) (x u : W) (hu : ‖u‖ = 1) :
    x = inner ℝ x u • u := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact zero_ne_one hu
  obtain ⟨c, rfl⟩ := (finrank_eq_one_iff_of_nonzero' u hu0).mp hW x
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hu, one_pow, mul_one]

/-- Two unit vectors of a one-dimensional inner product space agree up to sign. -/
theorem eq_or_eq_neg_of_finrank_eq_one (hW : finrank ℝ W = 1) {u v : W} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) : v = u ∨ v = -u := by
  have hv' := eq_inner_smul_of_finrank_eq_one hW v u hu
  have hc : |inner ℝ v u| = 1 := by
    have h := congrArg norm hv'
    rw [norm_smul, hu, mul_one, hv, Real.norm_eq_abs] at h
    exact h.symm
  rcases abs_eq (zero_le_one' ℝ) |>.mp hc with h | h
  · left
    rw [hv', h, one_smul]
  · right
    rw [hv', h, neg_one_smul]

/-- A one-dimensional inner product space contains a unit vector. -/
theorem exists_norm_eq_one_of_finrank_eq_one (hW : finrank ℝ W = 1) : ∃ u : W, ‖u‖ = 1 := by
  obtain ⟨v, hv⟩ : ∃ v : W, v ≠ 0 := by
    by_contra h
    have h' : ∀ v : W, v = 0 := fun v => not_not.mp fun hv => h ⟨v, hv⟩
    have : Subsingleton W := ⟨fun a b => (h' a).trans (h' b).symm⟩
    rw [finrank_zero_of_subsingleton] at hW
    exact zero_ne_one hW
  refine ⟨‖v‖⁻¹ • v, ?_⟩
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

end Fibre

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {B : Type*} [TopologicalSpace B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- The fibres of a vector bundle have the dimension of the model fibre. -/
theorem finrank_fiber (b : B) : finrank ℝ (V b) = finrank ℝ F :=
  ((trivializationAt F V b).continuousLinearEquivAt ℝ b
    (FiberBundle.mem_baseSet_trivializationAt' b)).toLinearEquiv.finrank_eq

/-- The parametrisation `(p, t) ↦ t • ν p` of the total space by `Σ × ℝ`. -/
def rankOneParam {S : Type*} (ν : S → TotalSpace F V) (q : S × ℝ) : TotalSpace F V :=
  ⟨(ν q.1).proj, q.2 • (ν q.1).2⟩

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
@[simp] theorem rankOneParam_proj {S : Type*} (ν : S → TotalSpace F V) (q : S × ℝ) :
    (rankOneParam ν q).proj = (ν q.1).proj := rfl

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
theorem norm_rankOneParam {S : Type*} (ν : S → TotalSpace F V) (hνS : ∀ p, ‖(ν p).2‖ = 1)
    (q : S × ℝ) : ‖(rankOneParam ν q).2‖ = |q.2| := by
  change ‖q.2 • (ν q.1).2‖ = |q.2|
  rw [norm_smul, hνS, mul_one, Real.norm_eq_abs]

variable {S : Type*} (ν : S → TotalSpace F V) (τ : S → S)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace B]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V] in
/-- `Φ (τ p, -t) = Φ (p, t)`. -/
theorem rankOneParam_deck (hνneg : ∀ p, ν (τ p) = ⟨(ν p).proj, -(ν p).2⟩) (p : S) (t : ℝ) :
    rankOneParam ν (τ p, -t) = rankOneParam ν (p, t) := by
  change (⟨(ν (τ p)).proj, (-t) • (ν (τ p)).2⟩ : TotalSpace F V) = ⟨(ν p).proj, t • (ν p).2⟩
  rw [hνneg p, neg_smul, smul_neg, neg_neg]

/-- Two parameters over the same base point agree or differ by the involution. -/
theorem eq_or_eq_of_proj_eq (hF : finrank ℝ F = 1) (hνS : ∀ p, ‖(ν p).2‖ = 1)
    (hνinj : Function.Injective ν) (hνneg : ∀ p, ν (τ p) = ⟨(ν p).proj, -(ν p).2⟩) {p q : S}
    (h : (ν q).proj = (ν p).proj) : q = p ∨ q = τ p := by
  have hq := hνS q
  have hp := hνS p
  have hτ := hνneg p
  generalize hQ : ν q = Q at hq h
  generalize hP : ν p = P at hp h hτ
  obtain ⟨b, v⟩ := Q
  obtain ⟨b', v'⟩ := P
  change b = b' at h
  subst h
  have hv : v = v' ∨ v = -v' :=
    eq_or_eq_neg_of_finrank_eq_one ((finrank_fiber (F := F) (V := V) b).trans hF) hp hq
  rcases hv with rfl | rfl
  · left
    apply hνinj
    rw [hQ, hP]
  · right
    apply hνinj
    rw [hQ, hτ]

/-- `Φ` is onto the total space. -/
theorem rankOneParam_surjective (hF : finrank ℝ F = 1)
    (hνsurj : ∀ z : TotalSpace F V, ‖z.2‖ = 1 → ∃ p, ν p = z) :
    Function.Surjective (rankOneParam ν) := by
  intro z
  have hb := (finrank_fiber (F := F) (V := V) z.proj).trans hF
  by_cases hz : z.2 = 0
  · obtain ⟨u, hu⟩ := exists_norm_eq_one_of_finrank_eq_one hb
    obtain ⟨p, hp⟩ := hνsurj ⟨z.proj, u⟩ hu
    refine ⟨(p, 0), ?_⟩
    change (⟨(ν p).proj, (0 : ℝ) • (ν p).2⟩ : TotalSpace F V) = z
    rw [hp, zero_smul]
    change (⟨z.proj, 0⟩ : TotalSpace F V) = ⟨z.proj, z.2⟩
    rw [hz]
  · have hn : ‖z.2‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    obtain ⟨p, hp⟩ := hνsurj ⟨z.proj, ‖z.2‖⁻¹ • z.2⟩ (by
      change ‖‖z.2‖⁻¹ • z.2‖ = 1
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn])
    refine ⟨(p, ‖z.2‖), ?_⟩
    change (⟨(ν p).proj, ‖z.2‖ • (ν p).2⟩ : TotalSpace F V) = z
    rw [hp]
    change (⟨z.proj, ‖z.2‖ • ‖z.2‖⁻¹ • z.2⟩ : TotalSpace F V) = ⟨z.proj, z.2⟩
    rw [smul_smul, mul_inv_cancel₀ hn, one_smul]

/-- `Φ` identifies exactly `(p, t)` with `(τ p, -t)`. -/
theorem rankOneParam_eq_iff (hF : finrank ℝ F = 1) (hνS : ∀ p, ‖(ν p).2‖ = 1)
    (hνinj : Function.Injective ν) (hνneg : ∀ p, ν (τ p) = ⟨(ν p).proj, -(ν p).2⟩)
    {q q' : S × ℝ} (h : rankOneParam ν q' = rankOneParam ν q) :
    q' = q ∨ q' = (τ q.1, -q.2) := by
  obtain ⟨p, t⟩ := q
  obtain ⟨p', t'⟩ := q'
  have hproj := congrArg TotalSpace.proj h
  change (ν p').proj = (ν p).proj at hproj
  have hp := hνS p
  rcases eq_or_eq_of_proj_eq ν τ hF hνS hνinj hνneg hproj with rfl | rfl
  · left
    have h2 : t' • (ν p').2 = t • (ν p').2 := by
      have := h
      simp only [rankOneParam] at this
      exact eq_of_heq (TotalSpace.mk.inj this).2
    have h3 := congrArg (fun v => inner ℝ v (ν p').2) h2
    simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, hp, one_pow, mul_one] at h3
    rw [h3]
  · right
    have h1 : rankOneParam ν (τ p, t') = ⟨(ν p).proj, (-t') • (ν p).2⟩ := by
      change (⟨(ν (τ p)).proj, t' • (ν (τ p)).2⟩ : TotalSpace F V) = _
      rw [hνneg p, neg_smul, smul_neg]
    rw [h1] at h
    have h2 : (-t') • (ν p).2 = t • (ν p).2 := by
      simp only [rankOneParam] at h
      exact eq_of_heq (TotalSpace.mk.inj h).2
    have h3 := congrArg (fun v => inner ℝ v (ν p).2) h2
    simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, hp, one_pow, mul_one] at h3
    simp only [Prod.mk.injEq, true_and]
    linarith

end DifferentialGeometry.Topology.VectorBundle.RankOneQuotient
