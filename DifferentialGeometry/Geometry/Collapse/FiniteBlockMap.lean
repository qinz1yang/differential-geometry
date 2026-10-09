import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.SMul
import DifferentialGeometry.Geometry.Metric.MarkerRecovery

set_option autoImplicit false

/-!
# The finite block map (FC01), marker recovery on it (FC03) and the exact first scale (FC04)

Blueprint 207B, `def:fibration-block-map` (FC01, B:81), `lem:fibration-marker-recovery`
(FC03, B:180) and `lem:fibration-image-scale` (FC04, B:211).

Every tag `i` of a finite index type carries a coordinate space `V i`, a radius function `R i`,
a coordinate `η i` (only its values on the open domain `U i` matter) and a cutoff `ζ i` whose
CLOSED support lies in `U i`. The block is `(R ζ η, R ζ) ∈ V i ⊕ ℝ` and the map lands in the
orthogonal `ℓ²` sum. The scale tag `ρ` of the blueprint is the block with `V = ℝ⁰`, `ζ ≡ 1`,
`R = ρ` (value `(0, ρ)`), and the `E'` tag is a block with `R = ρ`; the others have constant
radius. The orthogonal projections `π_{a,b}` are the block restrictions to finite tag sets.
-/

open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

variable {κ : Type*} {V : κ → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℝ (V i)]

/-- The block target `H = ⊕ᵢ (V i ⊕ ℝ)` with orthogonal `ℓ²` norms. -/
abbrev BlockSpace (V : κ → Type*) : Type _ :=
  PiLp 2 fun i => WithLp 2 (V i × ℝ)

/-- **FC01**: the finite block map `p ↦ ((R ζ η)(p), (R ζ)(p))ᵢ`; the scalar last component of
each block is its marker. -/
noncomputable def blockMap {M : Type*} (R ζ : κ → M → ℝ) (η : ∀ i, M → V i) (p : M) :
    BlockSpace V :=
  WithLp.toLp 2 fun i => WithLp.toLp 2 ((R i p * ζ i p) • η i p, R i p * ζ i p)

section Basic

variable {M : Type*} (R ζ : κ → M → ℝ) (η : ∀ i, M → V i)

theorem blockMap_apply (p : M) (i : κ) :
    blockMap R ζ η p i = WithLp.toLp 2 ((R i p * ζ i p) • η i p, R i p * ζ i p) := rfl

theorem blockMap_apply_fst (p : M) (i : κ) :
    (blockMap R ζ η p i).fst = (R i p * ζ i p) • η i p := rfl

theorem blockMap_apply_snd (p : M) (i : κ) :
    (blockMap R ζ η p i).snd = R i p * ζ i p := rfl

/-- The zero extension is well defined: only the values of `η i` on `U i` enter. -/
theorem blockMap_congr_of_eqOn [TopologicalSpace M] {U : κ → Set M} {η' : ∀ i, M → V i}
    (hsupp : ∀ i, tsupport (ζ i) ⊆ U i) (hη : ∀ i, EqOn (η i) (η' i) (U i)) :
    blockMap R ζ η = blockMap R ζ η' := by
  funext p
  refine congrArg (WithLp.toLp 2) (funext fun i => ?_)
  by_cases hp : p ∈ U i
  · simp only [hη i hp]
  · have hz : ζ i p = 0 := image_eq_zero_of_notMem_tsupport fun h => hp (hsupp i h)
    simp [hz]

/-- FC01's image bounds: the marker lies in `[0, R]`. -/
theorem blockMap_marker_mem_Icc {p : M} {i : κ} (hR : 0 ≤ R i p) (hζ : ζ i p ∈ Icc 0 1) :
    (blockMap R ζ η p i).snd ∈ Icc 0 (R i p) := by
  rw [blockMap_apply_snd]
  exact ⟨mul_nonneg hR hζ.1, mul_le_of_le_one_right hR hζ.2⟩

/-- FC01's image bounds: `|x'ᵢ| ≤ Cᵢ x''ᵢ` whenever `|ηᵢ| ≤ Cᵢ` where the cutoff is nonzero. -/
theorem norm_blockMap_fst_le {p : M} {i : κ} {C : ℝ} (hR : 0 ≤ R i p) (hζ : 0 ≤ ζ i p)
    (hC : ζ i p ≠ 0 → ‖η i p‖ ≤ C) :
    ‖(blockMap R ζ η p i).fst‖ ≤ C * (blockMap R ζ η p i).snd := by
  rw [blockMap_apply_fst, blockMap_apply_snd, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hR hζ)]
  by_cases h0 : ζ i p = 0
  · simp [h0]
  · rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC h0) (mul_nonneg hR hζ)

end Basic

section Smooth

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*}
  [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M]
  [ChartedSpace HM M]

/-- FC01's construction check: with cutoffs whose CLOSED supports lie in open coordinate
domains, the zero-extended block map is smooth. -/
theorem contMDiff_blockMap [Fintype κ] {n : WithTop ℕ∞} {R ζ : κ → M → ℝ} {η : ∀ i, M → V i}
    {U : κ → Set M} (hU : ∀ i, IsOpen (U i)) (hη : ∀ i, ContMDiffOn I 𝓘(ℝ, V i) n (η i) (U i))
    (hζ : ∀ i, ContMDiff I 𝓘(ℝ) n (ζ i)) (hR : ∀ i, ContMDiff I 𝓘(ℝ) n (R i))
    (hsupp : ∀ i, tsupport (ζ i) ⊆ U i) :
    ContMDiff I 𝓘(ℝ, BlockSpace V) n (blockMap R ζ η) := by
  have hpi : ContMDiff I 𝓘(ℝ, ∀ i, WithLp 2 (V i × ℝ)) n
      (fun p i => WithLp.toLp 2 ((R i p * ζ i p) • η i p, R i p * ζ i p)) := by
    refine contMDiff_pi_space.2 fun i => ?_
    have hmark : ContMDiff I 𝓘(ℝ) n fun p => R i p * ζ i p := by
      have h := (hR i).smul (hζ i)
      exact h
    have hvec : ContMDiff I 𝓘(ℝ, V i) n fun p => (R i p * ζ i p) • η i p := by
      intro p
      by_cases hp : p ∈ tsupport (ζ i)
      · have hηp : ContMDiffAt I 𝓘(ℝ, V i) n (η i) p :=
          (hη i).contMDiffAt ((hU i).mem_nhds (hsupp i hp))
        exact ContMDiffAt.smul (hmark p) hηp
      · have hev : (fun q => (R i q * ζ i q) • η i q) =ᶠ[𝓝 p] fun _ => (0 : V i) := by
          filter_upwards [(isClosed_tsupport (ζ i)).isOpen_compl.mem_nhds hp] with q hq
          rw [image_eq_zero_of_notMem_tsupport hq, mul_zero, zero_smul]
        exact (contMDiffAt_const).congr_of_eventuallyEq hev
    have hprod : ContMDiff I 𝓘(ℝ, V i × ℝ) n
        fun p => ((R i p * ζ i p) • η i p, R i p * ζ i p) := hvec.prodMk_space hmark
    exact ((WithLp.prodContinuousLinearEquiv 2 ℝ (V i) ℝ).symm :
      (V i × ℝ) →L[ℝ] WithLp 2 (V i × ℝ)).contMDiff.comp hprod
  exact ((PiLp.continuousLinearEquiv 2 ℝ fun i => WithLp 2 (V i × ℝ)).symm :
    (∀ i, WithLp 2 (V i × ℝ)) →L[ℝ] BlockSpace V).contMDiff.comp hpi

end Smooth

section Restrict

variable [DecidableEq κ]

/-- The orthogonal projection `π_s` onto the blocks with tags in `s` (the subspaces `Q_a`). -/
noncomputable def blockRestrict (s : Finset κ) : BlockSpace V →L[ℝ] BlockSpace V :=
  ((PiLp.continuousLinearEquiv 2 ℝ fun i => WithLp 2 (V i × ℝ)).symm :
      (∀ i, WithLp 2 (V i × ℝ)) →L[ℝ] BlockSpace V).comp
    ((ContinuousLinearMap.pi fun i =>
        if i ∈ s then ContinuousLinearMap.proj i else 0).comp
      (PiLp.continuousLinearEquiv 2 ℝ fun i => WithLp 2 (V i × ℝ) :
        BlockSpace V →L[ℝ] ∀ i, WithLp 2 (V i × ℝ)))

theorem blockRestrict_apply (s : Finset κ) (x : BlockSpace V) (i : κ) :
    blockRestrict s x i = if i ∈ s then x i else 0 := by
  by_cases h : i ∈ s <;> simp [blockRestrict, h]

/-- `π_{b,c} ∘ π_{a,b} = π_{a,c}`: restricting twice restricts to the intersection. -/
theorem blockRestrict_comp (s t : Finset κ) :
    (blockRestrict (V := V) t).comp (blockRestrict s) = blockRestrict (s ∩ t) := by
  ext x i
  simp only [ContinuousLinearMap.comp_apply, blockRestrict_apply, Finset.mem_inter]
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [hs, ht]

theorem norm_blockRestrict_apply_le [Fintype κ] (s : Finset κ) (x : BlockSpace V) :
    ‖blockRestrict s x‖ ≤ ‖x‖ := by
  have h : ‖blockRestrict s x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [blockRestrict_apply]
    split_ifs <;> simp
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

theorem norm_blockRestrict_le [Fintype κ] (s : Finset κ) : ‖blockRestrict (V := V) s‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact norm_blockRestrict_apply_le s x

theorem blockRestrict_univ [Fintype κ] :
    blockRestrict (V := V) Finset.univ = ContinuousLinearMap.id ℝ _ := by
  ext x i
  simp [blockRestrict_apply]

end Restrict

section Marker

variable {M : Type*} {R ζ : κ → M → ℝ} {η : ∀ i, M → V i}

private theorem blockMap_apply_sub_eq_smul {p q : M} {i : κ} {r : ℝ} (hRi : ∀ y, R i y = r)
    (hp : ζ i p = 1) :
    blockMap R ζ η q i - blockMap R ζ η p i =
      r • (WithLp.toLp 2 (ζ i q • η i q, ζ i q) - WithLp.toLp 2 (η i p, (1 : ℝ))) := by
  rw [blockMap_apply, blockMap_apply, hRi, hRi, hp, smul_sub, ← WithLp.toLp_smul,
    ← WithLp.toLp_smul, Prod.smul_mk, Prod.smul_mk, smul_smul, smul_eq_mul, smul_eq_mul, mul_one]

variable [TopologicalSpace M] [Fintype κ] [DecidableEq κ]

/-- **FC03**: a full marker recovers its own coordinate from image distance alone, also after
any orthogonal projection `π_s` that retains the WHOLE `i`th block (`s = univ`: the unprojected
map). No prior local-distance assumption on `q` is used. -/
theorem marker_recovery_of_blockMap_dist {U : κ → Set M} (s : Finset κ) {i : κ} (hi : i ∈ s)
    {r A e : ℝ} (hr : 0 < r) (hRi : ∀ y, R i y = r) (hsupp : tsupport (ζ i) ⊆ U i) {p q : M}
    (hp : ζ i p = 1) (hA : ‖η i p‖ ≤ A) (he : 0 < e) (he1 : e < 1)
    (hq : ‖blockRestrict s (blockMap R ζ η q) - blockRestrict s (blockMap R ζ η p)‖ < e * r) :
    1 - e < ζ i q ∧ q ∈ U i ∧ ‖η i q - η i p‖ < (1 + A) * e / (1 - e) := by
  have hblock : ‖blockMap R ζ η q i - blockMap R ζ η p i‖ < e * r := by
    refine lt_of_le_of_lt ?_ hq
    have := PiLp.norm_apply_le
      (blockRestrict s (blockMap R ζ η q) - blockRestrict s (blockMap R ζ η p)) i
    simpa [blockRestrict_apply, hi] using this
  rw [blockMap_apply_sub_eq_smul hRi hp, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    mul_comm e r] at hblock
  have hdist : dist (WithLp.toLp 2 (ζ i q • η i q, ζ i q)) (WithLp.toLp 2 (η i p, (1 : ℝ))) < e := by
    rw [dist_eq_norm]; exact lt_of_mul_lt_mul_left hblock hr.le
  obtain ⟨hζq, hη⟩ := GC.MetricGeometry.norm_coordinate_sub_lt_of_block_dist he he1 hA hdist
  refine ⟨hζq, hsupp (subset_tsupport _ ?_), hη⟩
  rw [mem_support]
  linarith

end Marker

section Scale

variable {M : Type*}

/-- The FC04 radius `r₁(x) = σ x_ρ`, read from the retained scale block `iρ`. -/
noncomputable def scaleRadius (iρ : κ) (σ : ℝ) (x : BlockSpace V) : ℝ := σ * (x iρ).snd

/-- **FC04**: on the image of the block map the radius is the exact scale `σ ρ(p)`. -/
theorem scaleRadius_blockMap {R ζ : κ → M → ℝ} {η : ∀ i, M → V i} {iρ : κ} {ρ : M → ℝ}
    (hR : ∀ p, R iρ p = ρ p) (hζ : ∀ p, ζ iρ p = 1) (σ : ℝ) (p : M) :
    scaleRadius iρ σ (blockMap R ζ η p) = σ * ρ p := by
  rw [scaleRadius, blockMap_apply_snd, hR, hζ, mul_one]

/-- **FC04**: the radius is independent of the chosen preimage. -/
theorem scale_eq_of_blockMap_eq {R ζ : κ → M → ℝ} {η : ∀ i, M → V i} {iρ : κ} {ρ : M → ℝ}
    (hR : ∀ p, R iρ p = ρ p) (hζ : ∀ p, ζ iρ p = 1) {p q : M}
    (hpq : blockMap R ζ η p = blockMap R ζ η q) : ρ p = ρ q := by
  have := scaleRadius_blockMap (η := η) hR hζ 1 p
  rw [hpq, scaleRadius_blockMap hR hζ, one_mul, one_mul] at this
  exact this.symm

omit [∀ i, InnerProductSpace ℝ (V i)] in
/-- **FC04**: the radius is `σ`-Lipschitz for the ambient (restricted) Euclidean distance. -/
theorem abs_scaleRadius_sub_le [Fintype κ] (iρ : κ) {σ : ℝ} (hσ : 0 ≤ σ) (x y : BlockSpace V) :
    |scaleRadius iρ σ x - scaleRadius iρ σ y| ≤ σ * ‖x - y‖ := by
  rw [scaleRadius, scaleRadius, ← mul_sub, abs_mul, abs_of_nonneg hσ]
  refine mul_le_mul_of_nonneg_left ?_ hσ
  calc |(x iρ).snd - (y iρ).snd| = ‖((x - y) iρ).snd‖ := by
        rw [PiLp.sub_apply, Real.norm_eq_abs]; rfl
    _ ≤ ‖(x - y) iρ‖ := by apply WithLp.norm_snd_le
    _ ≤ ‖x - y‖ := PiLp.norm_apply_le _ _

/-- **FC04**: on a compact carrier the radius on the image is bounded above and away from
zero. -/
theorem exists_scaleRadius_bounds [TopologicalSpace M] [CompactSpace M] [Nonempty M]
    {R ζ : κ → M → ℝ} {η : ∀ i, M → V i} {iρ : κ} {ρ : M → ℝ} (hR : ∀ p, R iρ p = ρ p)
    (hζ : ∀ p, ζ iρ p = 1) (hρc : Continuous ρ) (hρ : ∀ p, 0 < ρ p) {σ : ℝ} (hσ : 0 < σ) :
    ∃ m Mx : ℝ, 0 < m ∧ ∀ p, m ≤ scaleRadius iρ σ (blockMap R ζ η p) ∧
      scaleRadius iρ σ (blockMap R ζ η p) ≤ Mx := by
  obtain ⟨p₀, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hρc.continuousOn
  obtain ⟨p₁, -, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hρc.continuousOn
  refine ⟨σ * ρ p₀, σ * ρ p₁, mul_pos hσ (hρ p₀), fun p => ?_⟩
  rw [scaleRadius_blockMap hR hζ]
  exact ⟨mul_le_mul_of_nonneg_left (hmin (mem_univ p)) hσ.le,
    mul_le_mul_of_nonneg_left (hmax (mem_univ p)) hσ.le⟩

end Scale

end DifferentialGeometry.Geometry.Collapse
