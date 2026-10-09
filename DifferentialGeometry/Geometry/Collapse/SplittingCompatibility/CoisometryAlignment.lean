import DifferentialGeometry.Geometry.Metric.Approximation.CompatibilityRecentering
import DifferentialGeometry.Analysis.InnerProductSpace.AnchorAlignment
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# One coisometry from AC76's compatibility witness, at every rank (FC21 for AC76/AC79)

Blueprint `master207A.tex`: AC71 (`def:alexandrov-directed-compatibility`, A:5745), AC76
(`thm:alexandrov-uniform-compatibility`, A:5986; Lean `exists_splitting_compatibility_parameter`),
AC79/AC80 (`cor:alexandrov-splitting-recenter`, A:6141; `thm:alexandrov-compatibility-recenter`,
A:6164; Lean `KleinerLottApprox.recenterEuclidean`, `SplittingCompatible.recenterEuclidean`).
Blueprint `master207B.tex`: FC19 (B:1293, binding paragraph B:1363–1371), FC20/FC21 (B:1397–1449),
FC23 item 3 (B:1518).

FC19 and FC23 consume the AC76/AC79 compatibility data as ONE constant coisometry `Λ : ℝᵏ → ℝʲ`
(`Λ ∘ Λ† = id`) and a translation `c` with `‖φ₁ − Λ ψ₁ − c‖` small, "as in KL 4.31". This file
supplies that form for every pair of ranks `j ≤ k` (the existing alignments cover only `(1,k)`,
`exists_unit_row_alignment_of_splittingCompatible`, and `(n,n)`,
`exists_orthogonal_alignment_of_splittingCompatible_equal_rank`).

* `splittingFirstBlock Q`: the first block `Q₁` of AC71's orthogonal map `Q : ℝᵏ ≃ ℝʲ × ℝᵏ⁻ʲ`, a
  coisometry (`splittingFirstBlock_comp_adjoint`).
* `exists_coisometry_alignment_of_splittingCompatible` (FC20 + FC21 with AC76's witness):
  `‖φ₁ x − Λ ψ₁ x − c‖ ≤ (1 + 24 j) τ` wherever `x ∈ B(p, τ⁻¹)` and `‖ψ₁ x‖ ≤ a`, for any
  `20 j τ ≤ a`, `2a ≤ τ⁻¹`.
* `KleinerLottApprox.norm_euclidean_fst_le`, `product_distortion_le`, `product_cover`: a normalized
  Euclidean-product KL approximation in FC19's distortion / cover-to-error-`δ` form (`δ ≥ 3ε`).
* `exists_recentered_coisometry_alignment` (AC79/AC80 + FC21): the ORIGINAL coordinates are aligned
  by one coisometry on the ball of radius `δ⁻¹` about a new centre `c`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace GC.MetricGeometry

/-- The first block `Q₁` of an orthogonal splitting `Q : ℝᵏ ≃ₗᵢ ℝʲ × ℝᵏ⁻ʲ` (AC71's witness). -/
def splittingFirstBlock {j k : ℕ}
    (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j)))) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin j) :=
  LinearMap.toContinuousLinearMap ((LinearMap.fst ℝ _ _).comp
    ((WithLp.linearEquiv 2 ℝ _).toLinearMap.comp Q.toLinearEquiv.toLinearMap))

theorem splittingFirstBlock_apply {j k : ℕ}
    (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))))
    (v : EuclideanSpace ℝ (Fin k)) : splittingFirstBlock Q v = (Q v).fst := rfl

/-- The adjoint of `Q₁`: `y ↦ Q⁻¹ (y, 0)`. -/
private def splittingFirstBlockAdjoint {j k : ℕ}
    (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j)))) :
    EuclideanSpace ℝ (Fin j) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
  LinearMap.toContinuousLinearMap (Q.symm.toLinearEquiv.toLinearMap.comp
    ((WithLp.linearEquiv 2 ℝ _).symm.toLinearMap.comp (LinearMap.inl ℝ _ _)))

private theorem splittingFirstBlockAdjoint_apply {j k : ℕ}
    (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))))
    (y : EuclideanSpace ℝ (Fin j)) :
    splittingFirstBlockAdjoint Q y = Q.symm (WithLp.toLp 2 (y, 0)) := rfl

private theorem adjoint_splittingFirstBlock {j k : ℕ}
    (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j)))) :
    ContinuousLinearMap.adjoint (splittingFirstBlock Q) = splittingFirstBlockAdjoint Q := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro y v
  rw [splittingFirstBlockAdjoint_apply, splittingFirstBlock_apply,
    ← Q.inner_map_map (Q.symm (WithLp.toLp 2 (y, 0))) v, LinearIsometryEquiv.apply_symm_apply,
    WithLp.prod_inner_apply]
  change ⟪y, (Q v).fst⟫_ℝ + ⟪(0 : EuclideanSpace ℝ (Fin (k - j))), (Q v).snd⟫_ℝ = ⟪y, (Q v).fst⟫_ℝ
  rw [inner_zero_left, add_zero]

/-- `Q₁` is a coisometry: `Q₁ Q₁† = id`. -/
theorem splittingFirstBlock_comp_adjoint {j k : ℕ}
    (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j)))) :
    (splittingFirstBlock Q).comp (ContinuousLinearMap.adjoint (splittingFirstBlock Q)) =
      ContinuousLinearMap.id ℝ _ := by
  rw [adjoint_splittingFirstBlock]
  ext1 y
  rw [ContinuousLinearMap.comp_apply, splittingFirstBlockAdjoint_apply, splittingFirstBlock_apply,
    LinearIsometryEquiv.apply_symm_apply, WithLp.toLp_fst, ContinuousLinearMap.id_apply]

theorem norm_splittingFirstBlock_apply_le {j k : ℕ}
    (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))))
    (v : EuclideanSpace ℝ (Fin k)) : ‖splittingFirstBlock Q v‖ ≤ ‖v‖ := by
  rw [splittingFirstBlock_apply, ← Q.norm_map v]
  exact WithLp.norm_fst_le _ (Q v)

variable {X A B : Type*} [MetricSpace X] [MetricSpace A] [MetricSpace B]

/-- **FC21 for AC76's witness, all ranks `j ≤ k`.** If `φ` (rank `j`) is `τ`-compatible with `ψ`
(rank `k`) at `p`, one constant coisometry `Λ : ℝᵏ → ℝʲ` and one translation `c` satisfy
`‖φ₁ − Λ ψ₁ − c‖ ≤ (1 + 24 j) τ` wherever `x ∈ B(p, τ⁻¹)` and `‖ψ₁ x‖ ≤ a`. -/
theorem exists_coisometry_alignment_of_splittingCompatible {p : X} {a₀ : A} {b₀ : B}
    {j k : ℕ} {δ ε τ a : ℝ}
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a₀)) δ)
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)) ε)
    (hcomp : SplittingCompatible φ ψ τ) (ha0 : 0 < a) (ha : 20 * (j : ℝ) * τ ≤ a)
    (ha2 : 2 * a ≤ τ⁻¹) :
    ∃ Λ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin j), ∃ c,
      Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
      ∀ x ∈ ball p τ⁻¹, ‖(ψ.toFun x).fst‖ ≤ a →
        ‖(φ.toFun x).fst - Λ (ψ.toFun x).fst - c‖ ≤ (1 + 24 * j) * τ := by
  obtain ⟨-, Q, E, F, hQ⟩ := hcomp
  have hτ : 0 < τ := E.error_pos
  let S : Type _ := {x : X // x ∈ ball p τ⁻¹ ∧ ‖(ψ.toFun x).fst‖ ≤ a}
  have hdist (v w : EuclideanSpace ℝ (Fin j)) (hv : ‖v‖ < 2 * a) (hw : ‖w‖ < 2 * a) :
      |‖E.toFun v - E.toFun w‖ - ‖v - w‖| ≤ τ := by
    have hv' : v ∈ ball (0 : EuclideanSpace ℝ (Fin j)) τ⁻¹ := by
      rw [mem_ball_zero_iff]; linarith
    have hw' : w ∈ ball (0 : EuclideanSpace ℝ (Fin j)) τ⁻¹ := by
      rw [mem_ball_zero_iff]; linarith
    have h := E.distortion v hv' w hw'
    rwa [dist_eq_norm, dist_eq_norm] at h
  obtain ⟨Λ, c, hΛ, hval⟩ := InnerProductSpace.exists_coisometry_raw_factor_alignment
    (fun x : S => (ψ.toFun x.1).fst) (fun x : S => (φ.toFun x.1).fst) (splittingFirstBlock Q)
    (splittingFirstBlock_comp_adjoint Q) 0 0 ha0 hτ.le
    (by rwa [finrank_euclideanSpace_fin]) E.toFun E.basepoint hdist
    (fun x => by
      have h := (WithLp.dist_fst_le _ _).trans (hQ x.1 x.2.1)
      rw [WithLp.toLp_fst, dist_comm, dist_eq_norm] at h
      simpa only [sub_zero, splittingFirstBlock_apply] using h)
    (fun x => by
      rw [sub_zero]
      exact (norm_splittingFirstBlock_apply_le Q _).trans x.2.2)
  rw [finrank_euclideanSpace_fin] at hval
  refine ⟨Λ, c, hΛ, fun x hx hxa => ?_⟩
  have h := hval ⟨x, hx, hxa⟩
  calc ‖(φ.toFun x).fst - Λ (ψ.toFun x).fst - c‖ ≤ τ + 24 * j * τ := h
    _ = (1 + 24 * j) * τ := by ring

namespace KleinerLottApprox

/-- A KL `σ`-approximation is a KL `τ`-approximation with the SAME map once `3σ ≤ τ < 1`
(the coverage witness of radius `< τ⁻¹ − τ + 3σ` stays in the smaller source ball). -/
def weaken {Y : Type*} [MetricSpace Y] {p : X} {q : Y} {σ τ : ℝ}
    (f : KleinerLottApprox p q σ) (hστ : 3 * σ ≤ τ) (hτone : τ < 1) :
    KleinerLottApprox p q τ where
  error_pos := by linarith [f.error_pos]
  error_lt_one := hτone
  toFun := f.toFun
  basepoint := f.basepoint
  distortion x hx x' hx' := by
    have hσ := f.error_pos
    have hball : ball p τ⁻¹ ⊆ ball p σ⁻¹ :=
      ball_subset_ball (inv_anti₀ hσ (by linarith))
    exact (f.distortion x (hball hx) x' (hball hx')).trans (by linarith)
  coverage y hy := by
    have hσ := f.error_pos
    have hτ : 0 < τ := by linarith
    have hinv : τ⁻¹ ≤ σ⁻¹ := inv_anti₀ hσ (by linarith)
    obtain ⟨x, hx, hxy⟩ := f.coverage_witness y (by linarith)
    have hrad := (abs_le.mp (f.radial_error x hx)).1
    have htri := dist_triangle (f.toFun x) y q
    rw [dist_comm (f.toFun x) y] at htri
    have hxp : x ∈ ball p τ⁻¹ := by rw [mem_ball]; linarith
    have hmem : f.toFun x ∈ f.toFun '' ball p τ⁻¹ := ⟨x, hxp, rfl⟩
    exact (infDist_le_dist_of_mem hmem).trans (by linarith)

theorem weaken_toFun {Y : Type*} [MetricSpace Y] {p : X} {q : Y} {σ τ : ℝ}
    (f : KleinerLottApprox p q σ) (hστ : 3 * σ ≤ τ) (hτone : τ < 1) :
    (f.weaken hστ hτone).toFun = f.toFun := rfl

/-- A normalized Euclidean-product KL approximation has `‖ψ₁ x‖ ≤ d(x,p) + ε` on its ball. -/
theorem norm_euclidean_fst_le {p : X} {b₀ : B} {k : ℕ} {ε : ℝ}
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)) ε)
    {x : X} (hx : x ∈ ball p ε⁻¹) : ‖(ψ.toFun x).fst‖ ≤ dist x p + ε := by
  have h1 := WithLp.dist_fst_le (ψ.toFun x) (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀))
  have h0 : (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)).fst = 0 := rfl
  rw [h0, dist_zero_right] at h1
  have h2 := (abs_le.mp (ψ.radial_error x hx)).2
  linarith

/-- FC19's `hdist` for a normalized Euclidean-product KL approximation (`δ = ε`, `H ≤ ε⁻¹`). -/
theorem product_distortion_le {p : X} {b₀ : B} {k : ℕ} {ε H : ℝ}
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)) ε)
    (hH : H ≤ ε⁻¹) :
    ∀ x ∈ ball p H, ∀ y ∈ ball p H,
      |dist (WithLp.toLp 2 ((ψ.toFun x).fst, (ψ.toFun x).snd) :
          WithLp 2 (EuclideanSpace ℝ (Fin k) × B))
        (WithLp.toLp 2 ((ψ.toFun y).fst, (ψ.toFun y).snd)) - dist x y| ≤ ε := fun x hx y hy =>
  ψ.distortion x (ball_subset_ball hH hx) y (ball_subset_ball hH hy)

/-- FC19's `hcover` for a normalized Euclidean-product KL approximation: every target point of
radius `< H − δ` has a preimage in `B(p,H)` within `δ`, for `H ≤ ε⁻¹` and `3ε ≤ δ`. -/
theorem product_cover {p : X} {b₀ : B} {k : ℕ} {ε H δ : ℝ}
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)) ε)
    (hH : H ≤ ε⁻¹) (hδ : 3 * ε ≤ δ) :
    ∀ q : WithLp 2 (EuclideanSpace ℝ (Fin k) × B),
      dist q (WithLp.toLp 2 (0, b₀)) < H - δ →
        ∃ y ∈ ball p H, dist (WithLp.toLp 2 ((ψ.toFun y).fst, (ψ.toFun y).snd)) q ≤ δ := by
  intro q hq
  have hε := ψ.error_pos
  obtain ⟨y, hy, hqy⟩ := ψ.coverage_witness q (by linarith)
  have hrad := (abs_le.mp (ψ.radial_error y hy)).1
  have htri := dist_triangle (ψ.toFun y) q (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀))
  rw [dist_comm (ψ.toFun y) q] at htri
  refine ⟨y, ?_, ?_⟩
  · rw [mem_ball]; linarith
  · change dist (ψ.toFun y) q ≤ δ
    rw [dist_comm]; linarith

end KleinerLottApprox

/-- **AC79/AC80 + FC21**: compatibility at `p` (error `ε ≤ ϑ(δ, C+1)`) gives, at every new centre
`c` with `d(p,c) ≤ C`, one constant coisometry `Λ` and translation `b` aligning the ORIGINAL
coordinates on `B(c, δ⁻¹)` wherever `‖ψ₁ x − ψ₁ c‖ ≤ r`. -/
theorem exists_recentered_coisometry_alignment {p : X} {a₀ : A} {b₀ : B} {j k : ℕ}
    {ε δ C r : ℝ}
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a₀)) ε)
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)) ε)
    (hcomp : SplittingCompatible φ ψ ε) (c : X) (hδ : 0 < δ) (hδone : δ < 1) (hC : 0 ≤ C)
    (hε : ε ≤ recenterTolerance δ (C + 1)) (hc : dist p c ≤ C)
    (hr0 : 0 < r) (hr : 20 * (j : ℝ) * δ ≤ r) (hr2 : 2 * r ≤ δ⁻¹) :
    ∃ Λ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin j), ∃ b,
      Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
      ∀ x ∈ ball c δ⁻¹, ‖(ψ.toFun x).fst - (ψ.toFun c).fst‖ ≤ r →
        ‖(φ.toFun x).fst - Λ (ψ.toFun x).fst - b‖ ≤ (1 + 24 * j) * δ := by
  obtain ⟨Λ, b', hΛ, hal⟩ := exists_coisometry_alignment_of_splittingCompatible _ _
    (hcomp.recenterEuclidean c hδ hδone hC hε hc) hr0 hr hr2
  refine ⟨Λ, b' + (φ.toFun c).fst - Λ (ψ.toFun c).fst, hΛ, fun x hx hxr => ?_⟩
  have h := hal x hx (by simpa only [KleinerLottApprox.recenterEuclidean_apply,
    WithLp.toLp_fst] using hxr)
  simp only [KleinerLottApprox.recenterEuclidean_apply, WithLp.toLp_fst, map_sub] at h
  convert h using 2
  abel

end GC.MetricGeometry
