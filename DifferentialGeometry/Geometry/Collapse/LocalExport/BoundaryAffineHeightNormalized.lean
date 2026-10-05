import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightWitness

/-!
# BCG02's differential clause at normalized scale (lane BCG-7, G4)

Blueprint 207B, BCG02 (`B:8889–8958`), the direct check of the differential conclusion, on ONE
complete Riemannian carrier at the normalized metric (the reference scale `R_a = 1`; the circle /
edge / slim `test` fields are stated in this form after `mX.rescale`, `radialScaledBundle`, …):
the axis witness `y` (coverage and distortion of the reference splitting `ψ`), a minimizing unit
direction `w` from `x` to `y` (Hopf–Rinow), the reference adapted test at `(x, y, w)`, the raw
alignment `|U − (Aψ₁)₀| < E` at both endpoints, BCG02.b for `U` along the geodesic, the two norm
bounds, and FC15 with the budget `θ²/10⁵`.

* `exists_unit_geodesic_eq_BCG7`: on a complete Riemannian manifold, for `x ≠ z` a unit `w` with
  `intrinsicGeodesic x w (d(x, z)) = z` (`minExp_of_ne_top`);
* `bcg02_differential_normalized_BCG7`: for a reference splitting `ψ` (`β`-approximation into
  `ℝᵐ ×₂ Y` at `p`), a unit row `A`, a reference coordinate `φ_c` with its adapted test on
  `B(p, r_x) × B(p, r_far)`, separation `> sep` (quality `γ`) and `‖Dφ_c‖ ≤ 1 + γ` on `B(p, r)`, a
  function `U` with `|U − (Aψ₁)₀| < E` on `B(p, L + r + 1)`, `‖DU‖ ≤ 1 + δ_N` and the Taylor bound
  `|DU(w) − (U(γ_w(ℓ)) − U(x))/ℓ| ≤ Rℓ` (`ℓ ≤ L + 1`) on `B(p, r)`, and the budget
  `δ_N + 2γ + R(L + 1) + 2E + 5β ≤ θ²/10⁵`: at every `x ∈ B(p, r)`, `‖DU − (A Dφ_c)₀‖ < θ`;
* consumer `bcg02_differential_normalized_circle_BCG7`: the circle case (`L = 400`, `r = 10`, test
  radii `200`, `201·10⁴`, separation `201`, rank `m = 2`) with the requests `γ, E, β, δ_N ≤ θ²/10⁷`,
  `R ≤ θ²/10¹⁰`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Normalized

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- **Hopf–Rinow, unit form**: on a complete Riemannian manifold, for `x ≠ z` there is a unit vector
`w` at `x` with `intrinsicGeodesic x w (d(x, z)) = z`. -/
theorem exists_unit_geodesic_eq_BCG7 (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (x z : M) (hxz : x ≠ z) :
    ∃ w : TangentSpace I x, g.inner x w w = 1 ∧ intrinsicGeodesic g hEnorm x w (dist x z) = z := by
  obtain ⟨v, hv, hlen⟩ := minExp_of_ne_top g hEnorm x z (by
    rw [← IsRiemannianManifold.out (I := I)]
    exact edist_ne_top x z)
  rw [← IsRiemannianManifold.out (I := I), edist_dist, ENNReal.toReal_ofReal dist_nonneg] at hlen
  have hdpos : 0 < dist x z := dist_pos.mpr hxz
  have hvv : g.inner x v v = dist x z ^ 2 := by
    rw [← hlen, Real.sq_sqrt (metric_inner_self_nonneg g x v)]
  refine ⟨(dist x z)⁻¹ • v, ?_, ?_⟩
  · have h1 : g.inner x ((dist x z)⁻¹ • v) ((dist x z)⁻¹ • v) =
        (dist x z)⁻¹ * ((dist x z)⁻¹ * g.inner x v v) := by
      simp only [map_smul, smul_apply, smul_eq_mul]
    rw [h1, hvv]
    field_simp
  · rw [← intrinsicGeodesic_smul g hEnorm x ((dist x z)⁻¹ • v) (dist x z), smul_smul,
      mul_inv_cancel₀ hdpos.ne', one_smul]
    exact hv

/-- **BCG02's differential clause at normalized scale** (see the module docstring). -/
theorem bcg02_differential_normalized_BCG7 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {m : ℕ} {Y : Type*} [MetricSpace Y] {p : M} {a : Y} {β : ℝ}
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin m)), a)) β)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (φc : M → EuclideanSpace ℝ (Fin m)) (U : M → ℝ)
    {θ L r rx rfar sep γ E δN R : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hβ : β ≤ 1 / 10000)
    (hL : 2 ≤ L) (hLr : L + r + 1 ≤ β⁻¹ / 2) (hrx : r ≤ rx) (hfar : L + r + 1 ≤ rfar)
    (hsep : sep + 1 ≤ L) (hγ : 0 ≤ γ) (hE : 0 ≤ E) (hδN : 0 ≤ δN) (hR : 0 ≤ R)
    (hbud : δN + γ + R * (L + 1) + γ + 2 * E + 5 * β ≤ θ ^ 2 / 100000)
    (hraw : ∀ y, dist y p < L + r + 1 → |U y - A (ψ.toFun y).fst 0| < E)
    (htest : ∀ x ∈ ball p rx, ∀ z ∈ ball p rfar, sep < dist x z →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x z) = z →
      ‖mvfderiv I φc x w - (dist x z)⁻¹ • ((ψ.toFun z).fst - (ψ.toFun x).fst)‖ < γ)
    (hnc : ∀ x ∈ ball p r, ∀ u : TangentSpace I x,
      ‖mvfderiv I φc x u‖ ≤ (1 + γ) * Real.sqrt (g.inner x u u))
    (hnU : ∀ x ∈ ball p r, ∀ u : TangentSpace I x,
      |mvfderiv I U x u| ≤ (1 + δN) * Real.sqrt (g.inner x u u))
    (htay : ∀ x ∈ ball p r, ∀ w : TangentSpace I x, g.inner x w w = 1 →
      ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ L + 1 →
      |mvfderiv I U x w - (U (intrinsicGeodesic g hEnorm x w ℓ) - U x) / ℓ| ≤ R * ℓ)
    (x : M) (hx : x ∈ ball p r) :
    ∃ θ' < θ, ∀ u : TangentSpace I x,
      |mvfderiv I U x u - A (mvfderiv I φc x u) 0| ≤ θ' * Real.sqrt (g.inner x u u) := by
  have hβpos := ψ.error_pos
  obtain ⟨y, hy, hxy, hAy, hΔ⟩ := exists_axis_witness_raw_BCG7 ψ hβ A hA (by linarith) hLr U hraw x
    (mem_ball.mp hx)
  have hℓ := abs_le.mp hxy
  have hℓ1 : 1 ≤ dist x y := by linarith
  have hℓpos : 0 < dist x y := by linarith
  have hxy' : x ≠ y := fun h => by rw [h, dist_self] at hℓpos; exact lt_irrefl 0 hℓpos
  obtain ⟨w, hw, hgeo⟩ := exists_unit_geodesic_eq_BCG7 g hEnorm x y hxy'
  have hrxx : x ∈ ball p rx := mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hx) hrx)
  have hyfar : y ∈ ball p rfar := mem_ball.mpr (by linarith)
  have hsepxy : sep < dist x y := by linarith
  have ht := htest x hrxx y hyfar hsepxy w hw hgeo
  have hAn := ContinuousLinearMap.norm_le_one_of_comp_adjoint_BCG1 A hA
  have hrow := abs_row_sub_div_le_BCG7 A hAn (mvfderiv I φc x w) (ψ.toFun x).fst (ψ.toFun y).fst
    (dist x y)
  have htay' := htay x hx w hw (dist x y) hℓpos (by linarith)
  rw [hgeo] at htay'
  let h : TangentSpace I x →L[ℝ] ℝ :=
    (EuclideanSpace.proj (0 : Fin 1)).comp (A.comp (mvfderiv I φc x))
  have hh : ∀ u : TangentSpace I x, h u = A (mvfderiv I φc x u) 0 := fun u => rfl
  have hΔa : A ((ψ.toFun y).fst - (ψ.toFun x).fst) 0 =
      A (ψ.toFun y).fst 0 - A (ψ.toFun x).fst 0 := by
    simp only [map_sub, PiLp.sub_apply]
  obtain ⟨θ', hθ', hle⟩ := bcg02_differential_of_witness_BCG7 g x (mvfderiv I U x) h
    (δ₀ := δN + γ) (δ₁ := R * dist x y) (β := β) (L := L) hθ hθ1 (by positivity)
    (by positivity) hγ hE hβpos.le (by
      have : R * dist x y ≤ R * (L + 1) := mul_le_mul_of_nonneg_left (by linarith) hR
      linarith)
    (fun u => (hnU x hx u).trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.sqrt_nonneg _)))
    (fun u => by
      rw [hh]
      exact (abs_row_apply_le_BCG7 A hAn _).trans ((hnc x hx u).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))))
    w hw hℓ1 hxy htay' (by rw [hh, hΔa]; exact le_of_lt (lt_of_le_of_lt hrow ht)) hΔ hAy.le
  exact ⟨θ', hθ', fun u => by rw [← hh]; exact hle u⟩

/-- **Consumer: the circle case at normalized scale** (`L = 400`, `r = 10`, the circle test radii
`200`, `201·10⁴` and separation `201`), with the requests `γ, E, β, δ_N ≤ θ²/10⁷`, `R ≤ θ²/10¹⁰`. -/
theorem bcg02_differential_normalized_circle_BCG7 (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm g) {Y : Type*} [MetricSpace Y] {p : M} {a : Y} {β : ℝ}
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin 2)), a)) β)
    (A : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 1))
    (hA : A.comp (ContinuousLinearMap.adjoint A) = ContinuousLinearMap.id ℝ _)
    (φc : M → EuclideanSpace ℝ (Fin 2)) (U : M → ℝ) {θ γ E δN R : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hγ : 0 ≤ γ) (hE : 0 ≤ E) (hδN : 0 ≤ δN) (hR : 0 ≤ R) (hγθ : γ ≤ θ ^ 2 / 10000000)
    (hEθ : E ≤ θ ^ 2 / 10000000) (hβθ : β ≤ θ ^ 2 / 10000000) (hδNθ : δN ≤ θ ^ 2 / 10000000)
    (hRθ : R ≤ θ ^ 2 / 10000000000)
    (hraw : ∀ y, dist y p < 411 → |U y - A (ψ.toFun y).fst 0| < E)
    (htest : ∀ x ∈ ball p 200, ∀ z ∈ ball p (201 * 10000), 201 < dist x z →
      ∀ w : TangentSpace I x, g.inner x w w = 1 →
      intrinsicGeodesic g hEnorm x w (dist x z) = z →
      ‖mvfderiv I φc x w - (dist x z)⁻¹ • ((ψ.toFun z).fst - (ψ.toFun x).fst)‖ < γ)
    (hnc : ∀ x ∈ ball p 10, ∀ u : TangentSpace I x,
      ‖mvfderiv I φc x u‖ ≤ (1 + γ) * Real.sqrt (g.inner x u u))
    (hnU : ∀ x ∈ ball p 10, ∀ u : TangentSpace I x,
      |mvfderiv I U x u| ≤ (1 + δN) * Real.sqrt (g.inner x u u))
    (htay : ∀ x ∈ ball p 10, ∀ w : TangentSpace I x, g.inner x w w = 1 →
      ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 401 →
      |mvfderiv I U x w - (U (intrinsicGeodesic g hEnorm x w ℓ) - U x) / ℓ| ≤ R * ℓ)
    (x : M) (hx : x ∈ ball p 10) :
    ∃ θ' < θ, ∀ u : TangentSpace I x,
      |mvfderiv I U x u - A (mvfderiv I φc x u) 0| ≤ θ' * Real.sqrt (g.inner x u u) := by
  have hβpos := ψ.error_pos
  have hθ2 : θ ^ 2 < 1 := by nlinarith
  have hβs : β ≤ 1 / 10000 := by linarith
  have hβi : 10000000 ≤ β⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hβpos]
    linarith
  refine bcg02_differential_normalized_BCG7 g hEnorm ψ A hA φc U (L := 400) (r := 10) (rx := 200)
    (rfar := 201 * 10000) (sep := 201) hθ hθ1 hβs (by norm_num) (by linarith) (by norm_num)
    (by norm_num) (by norm_num) hγ hE hδN hR ?_ (fun y hy => hraw y (by linarith)) htest hnc hnU
    (fun x hx w hw ℓ hℓ hℓ' => htay x hx w hw ℓ hℓ (by linarith)) x hx
  have hθ0 : 0 ≤ θ ^ 2 := sq_nonneg θ
  nlinarith

end Normalized

end DifferentialGeometry.Geometry.Collapse
