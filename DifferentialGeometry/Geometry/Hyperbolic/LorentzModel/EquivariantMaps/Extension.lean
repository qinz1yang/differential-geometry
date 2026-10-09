/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Cusps.CrossSections
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.TimelikeAveraging
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.Uniformizable

noncomputable section

open Set Filter
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.EquivariantExtension

open Hyperbolic HyperbolicAction HyperbolicFaithful LorentzAveraging

variable {n : ℕ}

def ofSpatial (x : Fin n → ℝ) : HUpper n where
  val := Sum.elim x (fun _ => Real.sqrt (1 + ∑ i, x i ^ 2))
  is_unit := by
    have hs : 0 ≤ 1 + ∑ i, x i ^ 2 := by positivity
    simp only [lorB, sdot, tc, Sum.elim_inl, Sum.elim_inr, ← pow_two,
      Real.sq_sqrt hs]
    ring
  future := Real.sqrt_pos.mpr (by positivity)

theorem ofSpatial_val (p : HUpper n) : ofSpatial (fun i => p.val (Sum.inl i)) = p := by
  apply HUpper.ext
  funext a
  rcases a with i | j
  · rfl
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change Real.sqrt (1 + ∑ i, p.val (Sum.inl i) ^ 2) = tc p.val
    have he : 1 + ∑ i, p.val (Sum.inl i) ^ 2 = tc p.val ^ 2 := by
      simpa only [sdot, pow_two] using p.tc_sq.symm
    rw [he, Real.sqrt_sq p.future.le]

theorem continuous_ofSpatial : Continuous (ofSpatial (n := n)) := by
  apply StratumDeformation.continuous_of_val
  apply continuous_pi
  intro a
  rcases a with i | j
  · exact continuous_apply i
  · change Continuous (fun x : Fin n → ℝ => Real.sqrt (1 + ∑ i, x i ^ 2))
    fun_prop

theorem exists_continuous_extension {A : Set (HUpper n)} (hA : IsClosed A)
    (h : HUpper n → HUpper n) (hc : ContinuousOn h A) :
    ∃ u : HUpper n → HUpper n, Continuous u ∧ EqOn u h A := by
  let v : C(A, Fin n → ℝ) :=
    ⟨fun x i => (h x.val).val (Sum.inl i), continuous_pi fun i =>
      (continuous_apply (Sum.inl i)).comp (LorentzExtremal.continuous_val.comp
        (continuousOn_iff_continuous_domRestrict.mp hc))⟩
  obtain ⟨w, hw⟩ := v.exists_restrict_eq hA
  refine ⟨fun x => ofSpatial (w x), continuous_ofSpatial.comp w.continuous, ?_⟩
  intro x hx
  have he : w x = fun i => (h x).val (Sum.inl i) :=
    congrArg (fun z : C(A, Fin n → ℝ) => z ⟨x, hx⟩) hw
  change ofSpatial (w x) = h x
  rw [he, ofSpatial_val]

def weight (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (a : HUpper n → ℝ) (γ : Γ) (x : HUpper n) : ℝ :=
  a ((poMulAction hn).smul (γ : PO n 1)⁻¹ x)

theorem locallyFinite_weight (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (a : HUpper n → ℝ) (ha : HasCompactSupport a) :
    LocallyFinite (fun γ : Γ => Function.support (weight hn Γ a γ)) := by
  let := poMulAction hn
  obtain ⟨R, hR⟩ := ha.isCompact.isBounded.subset_closedBall (basepointH : HUpper n)
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), ?_⟩
  apply (DirichletDomain.finite_setOf_coe_le hn Γ hΓ (R + 1 + dist x basepointH)).subset
  rintro γ ⟨y, hy, hyx⟩
  have hy' : (γ : PO n 1)⁻¹ • y ∈ tsupport a := subset_tsupport _ (show
    a ((γ : PO n 1)⁻¹ • y) ≠ 0 from hy)
  have hdR : dist basepointH ((γ : PO n 1)⁻¹ • y) ≤ R := by
    simpa only [Metric.mem_closedBall, dist_comm] using hR hy'
  have he : dist ((γ : PO n 1) • basepointH) y =
      dist basepointH ((γ : PO n 1)⁻¹ • y) := by
    simpa only [smul_inv_smul] using
      po_dist_smul hn (γ : PO n 1) basepointH ((γ : PO n 1)⁻¹ • y)
  have hd := dist_triangle ((γ : PO n 1) • basepointH) y basepointH
  have hd' := dist_triangle y x basepointH
  rw [he] at hd
  have hyx' : dist y x < 1 := hyx
  change dist ((γ : PO n 1) • basepointH) basepointH ≤ _
  linarith

theorem weight_support_finite (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) (a : HUpper n → ℝ) (ha : HasCompactSupport a)
    (x : HUpper n) : (Function.support (fun γ : Γ => weight hn Γ a γ x)).Finite :=
  (locallyFinite_weight hn Γ hΓ a ha).point_finite x

theorem continuous_weight (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    {a : HUpper n → ℝ} (ha : Continuous a) (γ : Γ) :
    Continuous (weight hn Γ a γ) :=
  ha.comp (CuspCrossSections.interiorHomeomorph hn (γ : PO n 1)⁻¹).continuous

def totalWeight (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (a : HUpper n → ℝ) (x : HUpper n) : ℝ :=
  ∑ᶠ γ : Γ, weight hn Γ a γ x

def orbitVector (hn : 1 ≤ n) {Γ Λ : Subgroup (PO n 1)} (f : Γ ≃* Λ)
    (a : HUpper n → ℝ) (u : HUpper n → HUpper n) (x : HUpper n) : LorVec n :=
  ∑ᶠ γ : Γ, weight hn Γ a γ x •
    ((poMulAction hn).smul (f γ : PO n 1) (u ((poMulAction hn).smul (γ : PO n 1)⁻¹ x))).val

theorem continuous_totalWeight (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) {a : HUpper n → ℝ}
    (ha : Continuous a) (hca : HasCompactSupport a) :
    Continuous (totalWeight hn Γ a) :=
  continuous_finsum (continuous_weight hn Γ ha) (locallyFinite_weight hn Γ hΓ a hca)

theorem continuous_orbitVector (hn : 1 ≤ n) {Γ Λ : Subgroup (PO n 1)}
    (hΓ : IsDiscrete (SetLike.coe Γ)) (f : Γ ≃* Λ)
    {a : HUpper n → ℝ} (ha : Continuous a) (hca : HasCompactSupport a)
    {u : HUpper n → HUpper n} (hu : Continuous u) :
    Continuous (orbitVector hn f a u) := by
  apply continuous_finsum
  · intro γ
    exact (continuous_weight hn Γ ha γ).smul (LorentzExtremal.continuous_val.comp
      ((CuspCrossSections.interiorHomeomorph hn (f γ : PO n 1)).continuous.comp
        (hu.comp (CuspCrossSections.interiorHomeomorph hn (γ : PO n 1)⁻¹).continuous)))
  · apply (locallyFinite_weight hn Γ hΓ a hca).subset
    intro γ x hx
    change weight hn Γ a γ x ≠ 0
    intro he
    exact hx (by simp only [he, zero_smul])

theorem weight_smul (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (a : HUpper n → ℝ) (δ γ : Γ) (x : HUpper n) :
    weight hn Γ a (δ * γ) ((poMulAction hn).smul (δ : PO n 1) x) = weight hn Γ a γ x := by
  let := poMulAction hn
  change a (((δ * γ : Γ) : PO n 1)⁻¹ • ((δ : PO n 1) • x)) =
    a ((γ : PO n 1)⁻¹ • x)
  simp only [Subgroup.coe_mul, mul_inv_rev, mul_smul, inv_smul_smul]

theorem totalWeight_smul (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (a : HUpper n → ℝ) (δ : Γ) (x : HUpper n) :
    totalWeight hn Γ a ((poMulAction hn).smul (δ : PO n 1) x) = totalWeight hn Γ a x := by
  unfold totalWeight
  rw [← finsum_comp_equiv (Equiv.mulLeft δ)]
  exact finsum_congr fun γ => weight_smul hn Γ a δ γ x

theorem orbitVector_smul (hn : 1 ≤ n) {Γ Λ : Subgroup (PO n 1)}
    (hΓ : IsDiscrete (SetLike.coe Γ)) (f : Γ ≃* Λ)
    (a : HUpper n → ℝ) (hca : HasCompactSupport a) (u : HUpper n → HUpper n)
    (δ : Γ) (L : LorVec n →ₗ[ℝ] LorVec n)
    (hL : ∀ p : HUpper n, L p.val = ((poMulAction hn).smul (f δ : PO n 1) p).val)
    (x : HUpper n) :
    orbitVector hn f a u ((poMulAction hn).smul (δ : PO n 1) x) = L (orbitVector hn f a u x) := by
  let := poMulAction hn
  have hfin : (Function.support (fun γ : Γ => weight hn Γ a γ x •
      ((f γ : PO n 1) • u ((γ : PO n 1)⁻¹ • x)).val)).Finite :=
    (weight_support_finite hn Γ hΓ a hca x).subset
      (fun γ hγ he => hγ (by simp only [he, zero_smul]))
  unfold orbitVector
  change (∑ᶠ γ : Γ, weight hn Γ a γ ((δ : PO n 1) • x) •
    ((f γ : PO n 1) • u ((γ : PO n 1)⁻¹ • ((δ : PO n 1) • x))).val) =
    L.toAddMonoidHom (∑ᶠ γ : Γ, weight hn Γ a γ x •
      ((f γ : PO n 1) • u ((γ : PO n 1)⁻¹ • x)).val)
  rw [L.toAddMonoidHom.map_finsum hfin, ← finsum_comp_equiv (Equiv.mulLeft δ)]
  apply finsum_congr
  intro γ
  change weight hn Γ a (δ * γ) ((δ : PO n 1) • x) •
      ((f (δ * γ) : PO n 1) • u (((δ * γ : Γ) : PO n 1)⁻¹ • ((δ : PO n 1) • x))).val =
    L (weight hn Γ a γ x • ((f γ : PO n 1) • u ((γ : PO n 1)⁻¹ • x)).val)
  have hL' (p : HUpper n) : L p.val = ((f δ : PO n 1) • p).val := hL p
  have hw : weight hn Γ a (δ * γ) ((δ : PO n 1) • x) = weight hn Γ a γ x :=
    weight_smul hn Γ a δ γ x
  rw [hw, map_smul, hL']
  simp only [map_mul, Subgroup.coe_mul, mul_inv_rev, mul_smul, inv_smul_smul]

theorem orbitVector_eq_on (hn : 1 ≤ n) {Γ Λ : Subgroup (PO n 1)}
    (hΓ : IsDiscrete (SetLike.coe Γ)) (f : Γ ≃* Λ)
    (a : HUpper n → ℝ) (hca : HasCompactSupport a)
    {A : Set (HUpper n)} (hA : ∀ (γ : Γ) (x : HUpper n), x ∈ A →
      (poMulAction hn).smul (γ : PO n 1) x ∈ A)
    (h u : HUpper n → HUpper n) (hu : EqOn u h A)
    (heq : ∀ (γ : Γ) (x : HUpper n), x ∈ A →
      h ((poMulAction hn).smul (γ : PO n 1) x) = (poMulAction hn).smul (f γ : PO n 1) (h x))
    {x : HUpper n} (hx : x ∈ A) :
    orbitVector hn f a u x = totalWeight hn Γ a x • (h x).val := by
  let := poMulAction hn
  have heq' (γ : Γ) (x : HUpper n) (hx : x ∈ A) :
      h ((γ : PO n 1) • x) = (f γ : PO n 1) • h x := heq γ x hx
  have hterm (γ : Γ) : (f γ : PO n 1) • u ((γ : PO n 1)⁻¹ • x) = h x := by
    have hx' : (γ : PO n 1)⁻¹ • x ∈ A := hA γ⁻¹ x hx
    rw [hu hx', ← heq' γ _ hx', smul_inv_smul]
  change (∑ᶠ γ : Γ, weight hn Γ a γ x •
    ((f γ : PO n 1) • u ((γ : PO n 1)⁻¹ • x)).val) = _
  simp only [hterm]
  exact (finsum_smul' (weight_support_finite hn Γ hΓ a hca x) (h x).val).symm

theorem exists_continuous_equivariant_extension (hn : 1 ≤ n)
    (Γ Λ : Subgroup (PO n 1)) (hΓ : IsDiscrete (SetLike.coe Γ)) (f : Γ ≃* Λ)
    {A K : Set (HUpper n)} (hclosed : IsClosed A) (hK : IsCompact K)
    (hA : ∀ (γ : Γ) (x : HUpper n), x ∈ A →
      (poMulAction hn).smul (γ : PO n 1) x ∈ A)
    (hcover : ∀ x : HUpper n, x ∉ interior A → ∃ γ : Γ,
      (poMulAction hn).smul (γ : PO n 1) x ∈ K)
    (h : HUpper n → HUpper n) (hc : ContinuousOn h A)
    (heq : ∀ (γ : Γ) (x : HUpper n), x ∈ A →
      h ((poMulAction hn).smul (γ : PO n 1) x) = (poMulAction hn).smul (f γ : PO n 1) (h x)) :
    ∃ Φ : HUpper n → HUpper n, Continuous Φ ∧
      PseudoIsometry.IsFEquivariant f hn Φ ∧ EqOn Φ h A := by
  classical
  let := poMulAction hn
  obtain ⟨u, huc, hueq⟩ := exists_continuous_extension hclosed h hc
  obtain ⟨a, haK, hac, _, ha01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
  have has : HasCompactSupport a := hac
  let W := totalWeight hn Γ a
  let V := orbitVector hn f a u
  have hW := continuous_totalWeight hn Γ hΓ a.continuous has
  have hV := continuous_orbitVector hn hΓ f a.continuous has huc
  have hWpos {x : HUpper n} (hx : x ∉ interior A) : 0 < W x := by
    obtain ⟨γ, hγ⟩ := hcover x hx
    apply finsum_pos (fun δ => (ha01 _).1) _ (weight_support_finite hn Γ hΓ a has x)
    refine ⟨γ⁻¹, ?_⟩
    change 0 < a ((γ : PO n 1)⁻¹⁻¹ • x)
    have he : a ((γ : PO n 1) • x) = 1 := haK hγ
    rw [inv_inv, he]
    norm_num
  have hVtime {x : HUpper n} (hx : 0 < W x) : V x ∈ timelikeCone :=
    finsum_mem_timelikeCone _ _ (weight_support_finite hn Γ hΓ a has x)
      (fun γ => (ha01 _).1) hx
  let Φ : HUpper n → HUpper n := fun x =>
    if 0 < W x then normalizeOrBase (V x) else u x
  have hΦA : EqOn Φ h A := by
    intro x hx
    dsimp only [Φ]
    split_ifs with hw
    · change normalizeOrBase (orbitVector hn f a u x) = h x
      rw [orbitVector_eq_on hn hΓ f a has hA h u hueq heq hx]
      exact normalizeOrBase_smul_val (h x) hw
    · exact hueq hx
  refine ⟨Φ, ?_, ?_, hΦA⟩
  · apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hw : 0 < W x
    · have he : Φ =ᶠ[𝓝 x] fun y => normalizeOrBase (V y) := by
        filter_upwards [hW.continuousAt.eventually (Ioi_mem_nhds hw)] with y hy
        exact ite_eq_left hy
      exact ((continuousAt_normalizeOrBase (hVtime hw)).comp hV.continuousAt).congr he.symm
    · have hx : x ∈ interior A := by
        by_contra hx
        exact hw (hWpos hx)
      have he : Φ =ᶠ[𝓝 x] u := by
        filter_upwards [isOpen_interior.mem_nhds hx] with y hy
        exact (hΦA (interior_subset hy)).trans (hueq (interior_subset hy)).symm
      exact huc.continuousAt.congr he.symm
  · intro δ x
    have hWδ : W ((δ : PO n 1) • x) = W x := totalWeight_smul hn Γ a δ x
    by_cases hw : 0 < W x
    · change (if 0 < W ((δ : PO n 1) • x) then _ else _) =
        (f δ : PO n 1) •
          (if 0 < W x then normalizeOrBase (V x) else u x)
      simp only [hWδ, ite_eq_left hw]
      obtain ⟨L, hL, _⟩ := exists_linear_lift hn (f δ : PO n 1)
      change normalizeOrBase (V ((δ : PO n 1) • x)) =
        (f δ : PO n 1) • normalizeOrBase (V x)
      rw [show V ((δ : PO n 1) • x) = L (V x) from
        orbitVector_smul hn hΓ f a has u δ L hL x]
      exact normalizeOrBase_linear_lift hn (f δ : PO n 1) L hL (hVtime hw)
    · have hx : x ∈ A := interior_subset (by
        by_contra hx
        exact hw (hWpos hx))
      rw [hΦA (hA δ x hx), hΦA hx]
      exact heq δ x hx

end DifferentialGeometry.EquivariantExtension
