import DifferentialGeometry.Geometry.Collapse.SplittingCompatibility.CoisometryAlignment
import DifferentialGeometry.Analysis.InnerProductSpace.OverlapComparisonChain
import DifferentialGeometry.Geometry.Metric.Approximation.CommonEndpointTests

/-!
# AC76/AC79 compatibility data bound to the FC19 and FC23 kernels

Blueprint `master207B.tex`: FC19 (`lem:fibration-common-endpoints`, B:1293; binding paragraph
B:1349–1371) and FC23 (`found:fibration-original-binding`, B:1505, item 3: "the AC76/AC79
compatibility data on the SHORT buffer, FC21's single coisometry, and explicit error budgets").

The two kernels take the compatibility data as raw hypotheses. Here they are discharged from AC76's
output `SplittingCompatible φ ψ τ` (rank `j` map `φ`, rank `k` map `ψ`, both normalized at `p`):

* `exists_raw_factor_data_of_splittingCompatible`: AC71's witness gives FC21's raw data — the
  coisometry `Q₁ = splittingFirstBlock Q`, the pointed Euclidean factor map `E` with distortion `τ`
  on the radius-`2a` ball (`2a ≤ τ⁻¹`), and `‖φ₁ − E(Q₁ ψ₁)‖ ≤ τ` on `B(p, τ⁻¹)`.
* `exists_coisometry_overlap_comparison_of_splittingCompatible` (FC23): the kernel
  `InnerProductSpace.exists_coisometry_overlap_comparison` with `hraw`, `hball`, `hdist` discharged;
  `e_c = δ_f = τ`.
* `norm_sub_comp_le_of_splittingCompatible_common_endpoints` (FC19, derivative step): the kernel
  `GC.MetricGeometry.norm_sub_comp_le_of_common_endpoints` with `hdist`, `hcover`, `hup`, `hzp`
  (from the larger map `ψ` itself, `δ := 3ε`) and `hΨ` (all-rank FC21 alignment,
  `E := (1 + 24 j) τ`) discharged on `B(p,H)`, `H ≤ min τ⁻¹ ε⁻¹`, `H + ε ≤ a`.

The original derivative tests and the long-endpoint geometry remain the rows' own hypotheses.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped InnerProductSpace

namespace GC.MetricGeometry

variable {X A B : Type*} [MetricSpace X] [MetricSpace A] [MetricSpace B]

/-- AC71's witness as FC21's raw factor data: one coisometry block `Q₁`, one pointed factor map
`f` with distortion `τ` on the radius-`2a` ball, and `‖φ₁ − f(Q₁ ψ₁ − 0) − 0‖ ≤ τ` on `B(p, τ⁻¹)`. -/
theorem exists_raw_factor_data_of_splittingCompatible {p : X} {a₀ : A} {b₀ : B}
    {j k : ℕ} {δ ε τ a : ℝ}
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a₀)) δ)
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)) ε)
    (hcomp : SplittingCompatible φ ψ τ) (ha2 : 2 * a ≤ τ⁻¹) :
    ∃ Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
        WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))),
      ∃ f : EuclideanSpace ℝ (Fin j) → EuclideanSpace ℝ (Fin j), f 0 = 0 ∧
        (∀ v w, ‖v‖ < 2 * a → ‖w‖ < 2 * a → |‖f v - f w‖ - ‖v - w‖| ≤ τ) ∧
        ∀ x ∈ ball p τ⁻¹,
          ‖(φ.toFun x).fst - f (splittingFirstBlock Q (ψ.toFun x).fst - 0) - 0‖ ≤ τ := by
  obtain ⟨-, Q, E, F, hQ⟩ := hcomp
  refine ⟨Q, E.toFun, E.basepoint, fun v w hv hw => ?_, fun x hx => ?_⟩
  · have hv' : v ∈ ball (0 : EuclideanSpace ℝ (Fin j)) τ⁻¹ := by
      rw [mem_ball_zero_iff]; linarith
    have hw' : w ∈ ball (0 : EuclideanSpace ℝ (Fin j)) τ⁻¹ := by
      rw [mem_ball_zero_iff]; linarith
    have h := E.distortion v hv' w hw'
    rwa [dist_eq_norm, dist_eq_norm] at h
  · have h := (WithLp.dist_fst_le _ _).trans (hQ x hx)
    rw [WithLp.toLp_fst, dist_comm, dist_eq_norm] at h
    simpa only [sub_zero, splittingFirstBlock_apply] using h

/-- **FC23 binding.** AC76's compatibility witness on the short buffer `S ⊆ B(p, τ⁻¹)` (with
`‖ψ₁‖ ≤ a` there) and the asymmetric long/short tests on `D ⊆ S` give ONE coisometry `Λ` and
translation `b` with value error `τ + 24 j τ` on `S` and the FC22 derivative comparison on `D`. -/
theorem exists_coisometry_overlap_comparison_of_splittingCompatible
    {T : X → Type*} [∀ x, NormedAddCommGroup (T x)] [∀ x, InnerProductSpace ℝ (T x)]
    [∀ x, CompleteSpace (T x)] {p : X} {a₀ : A} {b₀ : B} {j k : ℕ} {δ₁ ε τ a : ℝ}
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a₀)) δ₁)
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)) ε)
    (hcomp : SplittingCompatible φ ψ τ) (S D : Set X) (ha0 : 0 < a)
    (ha : 20 * (j : ℝ) * τ ≤ a) (ha2 : 2 * a ≤ τ⁻¹) (hS : S ⊆ ball p τ⁻¹)
    (hSa : ∀ x ∈ S, ‖(ψ.toFun x).fst‖ ≤ a)
    (dF : ∀ x, T x →L[ℝ] EuclideanSpace ℝ (Fin j)) (dG : ∀ x, T x →L[ℝ] EuclideanSpace ℝ (Fin k))
    {αF αG ℓ₀ t β δ : ℝ} (hαF : 0 ≤ αF) (hℓ₀ : 0 < ℓ₀) (ht : 0 < t) (hβ : 0 ≤ β) (hδ : 0 ≤ δ)
    (hF : ∀ x ∈ D, ∀ i, ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp (dF x)‖ ≤ 1 + αF)
    (hG : ∀ x ∈ D, ‖dG x‖ ≤ 1 + αG) (hDS : D ⊆ S)
    (htests : ∀ x ∈ D, ∀ i : Fin j, ∃ w : T x, ‖w‖ = 1 ∧ ∃ y z : X, ∃ ℓ : ℝ, ℓ₀ ≤ ℓ ∧ z ∈ S ∧
      ℓ - β ≤ (φ.toFun y).fst i - (φ.toFun x).fst i ∧
      (φ.toFun y).fst i - (φ.toFun z).fst i ≤ ℓ - t + δ ∧
      |dF x w i - ((φ.toFun y).fst i - (φ.toFun x).fst i) / ℓ| ≤ αF ∧
      ‖dG x w - t⁻¹ • ((ψ.toFun z).fst - (ψ.toFun x).fst)‖ ≤ αG) :
    ∃ Λ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin j), ∃ b,
      Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
      (∀ x ∈ S, ‖(φ.toFun x).fst - Λ (ψ.toFun x).fst - b‖ ≤ τ + 24 * j * τ) ∧
      ∀ x ∈ D, ‖dF x - Λ.comp (dG x)‖ ≤ 2 * Real.sqrt (j * (4 * max (αF + β / ℓ₀)
        (αG + (β + δ + 2 * (τ + 24 * j * τ)) / t) +
          max (αF + β / ℓ₀) (αG + (β + δ + 2 * (τ + 24 * j * τ)) / t) ^ 2)) := by
  have hτ : 0 < τ := by
    obtain ⟨-, -, E, -, -⟩ := hcomp
    exact E.error_pos
  obtain ⟨Q, f, hf0, hfdist, hraw⟩ := exists_raw_factor_data_of_splittingCompatible φ ψ hcomp ha2
  exact InnerProductSpace.exists_coisometry_overlap_comparison
    (fun x => (ψ.toFun x).fst) (fun x => (φ.toFun x).fst) S D (splittingFirstBlock Q)
    (splittingFirstBlock_comp_adjoint Q) 0 0 ha0 hτ.le ha hτ.le f hf0 hfdist
    (fun x hx => hraw x (hS hx))
    (fun x hx => by
      rw [sub_zero]
      exact (norm_splittingFirstBlock_apply_le Q _).trans (hSa x hx))
    dF dG hαF hℓ₀ ht hβ hδ hF hG hDS htests

/-- **FC19 binding (derivative step).** AC76's compatibility witness and the larger map `ψ` itself
supply all metric data of FC19 on `B(p,H)`: `ψ`'s distortion and cover-to-error `3ε`, and ONE
coisometry `Λ` with `‖φ₁ − Λ ψ₁ − b‖ ≤ (1 + 24 j) τ`. With the original adapted tests along every
minimizing direction, `‖dF − Λ dG‖ ≤ 2 √(j (4ε' + ε'²))`,
`ε' = α + (9ε + 2(1 + 24 j)τ)/(s − 6ε)`, at every point of `B(p,L)`. -/
theorem norm_sub_comp_le_of_splittingCompatible_common_endpoints
    {TX : X → Type*} [∀ x, NormedAddCommGroup (TX x)] [∀ x, InnerProductSpace ℝ (TX x)]
    [∀ x, CompleteSpace (TX x)] {p : X} {a₀ : A} {b₀ : B} {j k : ℕ} {δ₁ ε τ a L T s H α : ℝ}
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), a₀)) δ₁)
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), b₀)) ε)
    (hcomp : SplittingCompatible φ ψ τ) (ha0 : 0 < a) (ha : 20 * (j : ℝ) * τ ≤ a)
    (ha2 : 2 * a ≤ τ⁻¹) (hHτ : H ≤ τ⁻¹) (hHε : H ≤ ε⁻¹) (hHa : H + ε ≤ a)
    (hT : 0 ≤ T) (hα : 0 ≤ α) (hs : T + 2 * (3 * ε) < s) (hH : L + s + 3 * (3 * ε) < H)
    (W : ∀ x : X, X → Set (TX x)) (hW : ∀ x y, x ≠ y → (W x y).Nonempty)
    (hWunit : ∀ x y, ∀ w ∈ W x y, ‖w‖ = 1)
    (dF : ∀ x, TX x →L[ℝ] EuclideanSpace ℝ (Fin j)) (dG : ∀ x, TX x →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hF : ∀ x ∈ ball p L, ∀ i, ‖(EuclideanSpace.proj i : StrongDual ℝ _).comp (dF x)‖ ≤ 1 + α)
    (hG : ∀ x ∈ ball p L, ‖dG x‖ ≤ 1 + α)
    (htestF : ∀ x ∈ ball p L, ∀ y ∈ ball p H, T < dist x y → ∀ w ∈ W x y,
      ‖dF x w - (dist x y)⁻¹ • ((φ.toFun y).fst - (φ.toFun x).fst)‖ ≤ α)
    (htestG : ∀ x ∈ ball p L, ∀ y ∈ ball p H, T < dist x y → ∀ w ∈ W x y,
      ‖dG x w - (dist x y)⁻¹ • ((ψ.toFun y).fst - (ψ.toFun x).fst)‖ ≤ α) :
    ∃ Λ : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin j), ∃ b,
      Λ.comp (ContinuousLinearMap.adjoint Λ) = ContinuousLinearMap.id ℝ _ ∧
      (∀ x ∈ ball p H, ‖(φ.toFun x).fst - Λ (ψ.toFun x).fst - b‖ ≤ (1 + 24 * j) * τ) ∧
      ∀ x ∈ ball p L, ‖dF x - Λ.comp (dG x)‖ ≤
        2 * Real.sqrt (j * (4 * (α + (3 * (3 * ε) + 2 * ((1 + 24 * j) * τ)) / (s - 2 * (3 * ε))) +
          (α + (3 * (3 * ε) + 2 * ((1 + 24 * j) * τ)) / (s - 2 * (3 * ε))) ^ 2)) := by
  have hτ : 0 < τ := by
    obtain ⟨-, -, E, -, -⟩ := hcomp
    exact E.error_pos
  have hε := ψ.error_pos
  obtain ⟨Λ, b, hΛ, hal⟩ := exists_coisometry_alignment_of_splittingCompatible φ ψ hcomp ha0 ha ha2
  have hΨ : ∀ x ∈ ball p H, ‖(φ.toFun x).fst - Λ (ψ.toFun x).fst - b‖ ≤ (1 + 24 * j) * τ :=
    fun x hx => hal x (ball_subset_ball hHτ hx)
      ((ψ.norm_euclidean_fst_le (ball_subset_ball hHε hx)).trans
        (by linarith [mem_ball.mp hx]))
  refine ⟨Λ, b, hΛ, hΨ, ?_⟩
  have hup : (ψ.toFun p).fst = 0 := by rw [ψ.basepoint]; rfl
  have hzp : (ψ.toFun p).snd = b₀ := by rw [ψ.basepoint]; rfl
  exact norm_sub_comp_le_of_common_endpoints (fun x => (ψ.toFun x).fst)
    (fun x => (ψ.toFun x).snd) (fun x => (φ.toFun x).fst) Λ hΛ b (δ := 3 * ε)
    (E := (1 + 24 * j) * τ) hT (by linarith) (by positivity) hα hs hH hup hzp
    (fun x hx y hy => (ψ.product_distortion_le hHε x hx y hy).trans (by linarith))
    (ψ.product_cover hHε le_rfl) hΨ W hW hWunit dF dG hF hG htestF htestG

end GC.MetricGeometry
