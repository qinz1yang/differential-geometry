import DifferentialGeometry.Geometry.Collapse.SublevelCore.FiniteScaledMinimizingDirections

/-!
# LFR28 R2: the rescaled carrier `(S, Δ⁻¹ d, Δ⁻² κ)` (lane LFR28-R12)

For a complete surface `S` whose distance is the Riemannian distance of a metric `κ` of finite
order (`C^{r+1}`) with `sec_κ ≥ 0`, and `Δ > 0`, the metric `κΔ = Δ⁻² κ`
(`DifferentialGeometry.finiteScaleMetric`) has, for the rescaled distance `Δ⁻¹ d`
(`MetricSpace.rescale`, same topology and charts), the full instance package of LFR24
(`exists_rescaled_carrier_metric`).

Kernels (all new; the smooth twins are `sectionalCurvature_scaleMetric` and `edistOf_scale`):
* `inv_smul_matrix_of_ne_zero`, `jetChristoffel_smul`, `jetChristoffelDeriv_smul`,
  `jetRiemann_smul`, `jetRm04_smul`, `jet2_const_smul`, `coefficientRm04_const_smul`,
  `coefficientSectional_const_smul`: the coordinate curvature of `c • b` (Christoffel symbols and
  `R^l_{ijk}` scale invariant, `Rm04` scales by `c`, sectional curvature by `c⁻¹`);
* `sectionalCurvature_finiteScaleMetric`: `sec_{c • G} = c⁻¹ sec_G` for a metric of any order;
* `riemannianEDist_eq_mul_of_enorm_eq_mul`: scaling every tangent extended norm by `a` scales the
  Riemannian extended distance by `a`;
* `mem_finiteMinimizingDirectionsTo_finiteScaleMetric_iff`: the minimizing directions to an
  arbitrary set `Y` (the singleton case is `finiteMinimizingDirectionsTo_scaleMetric`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric Manifold MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Analysis

section JetScaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}

/-- `(c • A)⁻¹ = c⁻¹ • A⁻¹` for every real square matrix and `c ≠ 0` (no invertibility needed). -/
theorem inv_smul_matrix_of_ne_zero {c : ℝ} (hc : c ≠ 0) (A : Matrix (Fin n) (Fin n) ℝ) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases h : IsUnit A.det
  · let invertible_LFR28R12 : Invertible c := invertibleOfNonzero hc
    rw [Matrix.inv_smul A c h, invOf_eq_inv]
  · have h' : ¬IsUnit (c • A).det := by
      rw [Matrix.det_smul, isUnit_iff_ne_zero, mul_ne_zero_iff, not_and_or, not_not, not_not]
      exact Or.inr (by simpa only [isUnit_iff_ne_zero, not_not] using h)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      smul_zero]

theorem matrixOf_inv_smul_jet {c : ℝ} (hc : c ≠ 0) (p : MatJet E n) :
    (Matrix.of (c • p.1))⁻¹ = c⁻¹ • (Matrix.of p.1)⁻¹ :=
  inv_smul_matrix_of_ne_zero hc (Matrix.of p.1)

/-- The jet Christoffel symbols are invariant under a constant rescaling of the metric jet. -/
theorem jetChristoffel_smul (b : Fin n → E) {c : ℝ} (hc : c ≠ 0) (p : MatJet E n)
    (i j k : Fin n) : jetChristoffel b (c • p) i j k = jetChristoffel b p i j k := by
  simp only [jetChristoffel, matrixOf_inv_smul_jet hc, Matrix.smul_apply, Prod.smul_snd,
    Prod.smul_fst, smul_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  field_simp

/-- The derivative part of the jet Christoffel symbols is scale invariant. -/
theorem jetChristoffelDeriv_smul (b : Fin n → E) {c : ℝ} (hc : c ≠ 0) (p : MatJet E n)
    (m i j k : Fin n) : jetChristoffelDeriv b (c • p) m i j k = jetChristoffelDeriv b p m i j k := by
  have hS : ∀ l : Fin n, (∑ a : Fin n, ∑ d : Fin n,
      c⁻¹ * (Matrix.of p.1)⁻¹ k a * (c⁻¹ * (Matrix.of p.1)⁻¹ d l) * (c * (p.2.1 (b m)) a d)) =
      c⁻¹ * ∑ a : Fin n, ∑ d : Fin n,
        (Matrix.of p.1)⁻¹ k a * (Matrix.of p.1)⁻¹ d l * (p.2.1 (b m)) a d := by
    intro l
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    field_simp
  simp only [jetChristoffelDeriv, matrixOf_inv_smul_jet hc, Matrix.smul_apply, Prod.smul_snd,
    Prod.smul_fst, smul_apply, Pi.smul_apply, smul_eq_mul, hS]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  field_simp

/-- The jet curvature tensor `R^l_{ijk}` is scale invariant. -/
theorem jetRiemann_smul (b : Fin n → E) {c : ℝ} (hc : c ≠ 0) (p : MatJet E n)
    (i j k l : Fin n) : jetRiemann b (c • p) i j k l = jetRiemann b p i j k l := by
  simp only [jetRiemann, jetChristoffel_smul b hc, jetChristoffelDeriv_smul b hc]

end JetScaling

section CoefficientScaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The jet `Rm04` scales linearly with the metric jet. -/
theorem jetRm04_smul [FiniteDimensional ℝ E] {c : ℝ} (hc : c ≠ 0) (p : MatJet E (Module.finrank ℝ E)) (X Y Z W : E) :
    jetRm04 (c • p) X Y Z W = c * jetRm04 p X Y Z W := by
  simp only [jetRm04, jetRiemann_smul _ hc, Prod.smul_fst, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  refine Finset.sum_congr rfl fun l' _ => ?_
  ring

/-- The second jet of `c • g` is `c` times the second jet of `g`. -/
theorem jet2_const_smul {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] (g : E → F')
    (c : ℝ) (w : E) : jet2 (fun y => c • g y) w = c • jet2 g w := by
  have h1 : fderiv ℝ (fun y => c • g y) = c • fderiv ℝ g := fderiv_const_smul_field c
  have h2 : fderiv ℝ (fun y => c • fderiv ℝ g y) = c • fderiv ℝ (fun y => fderiv ℝ g y) :=
    fderiv_const_smul_field (f := fun y => fderiv ℝ g y) c
  simp only [jet2, h1, Pi.smul_apply, h2, Prod.smul_mk]

/-- The coefficient numerator `Rm04` of `c • b` is `c` times that of `b`. -/
theorem coefficientRm04_const_smul [FiniteDimensional ℝ E] (b : E → E →L[ℝ] E →L[ℝ] ℝ) {c : ℝ} (hc : c ≠ 0)
    (w X Y Z W : E) :
    coefficientRm04 (fun y => c • b y) w X Y Z W = c * coefficientRm04 b w X Y Z W := by
  have hG : coefficientGram (fun y => c • b y) = fun y => c • coefficientGram b y :=
    funext fun y => map_smul (coefficientGramCLM E) c (b y)
  unfold coefficientRm04
  rw [hG, jet2_const_smul, jetRm04_smul hc]

/-- The coefficient sectional curvature of `c • b` is `c⁻¹` times that of `b`. -/
theorem coefficientSectional_const_smul [FiniteDimensional ℝ E] (b : E → E →L[ℝ] E →L[ℝ] ℝ) {c : ℝ} (hc : c ≠ 0)
    (x v u : E) :
    coefficientSectional (fun y => c • b y) x v u = c⁻¹ * coefficientSectional b x v u := by
  rw [coefficientSectional_def, coefficientSectional_def, coefficientRm04_const_smul b hc]
  simp only [smul_apply, smul_eq_mul]
  rw [show c * (b x v v) * (c * (b x u u)) - (c * (b x v u)) ^ 2 =
      c ^ 2 * (b x v v * b x u u - (b x v u) ^ 2) by ring, mul_div_mul_comm,
    show c / c ^ 2 = c⁻¹ by field_simp]

end CoefficientScaling

end DifferentialGeometry.Analysis

namespace Bundle.ContMDiffRiemannianMetric

open private pullbackCoefficients from DifferentialGeometry.Geometry.Curvature.Riemann.FiniteMetric

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Sectional curvature of `c • G`** (any order): `sec_{c • G} = c⁻¹ · sec_G` (finite-order twin
of `sectionalCurvature_scaleMetric`). -/
theorem sectionalCurvature_finiteScaleMetric {n : ℕ∞ω} (c : ℝ) (hc : 0 < c)
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (p : M)
    (v w : TangentSpace I p) :
    (DifferentialGeometry.finiteScaleMetric c hc G).sectionalCurvature p v w =
      c⁻¹ * G.sectionalCurvature p v w := by
  have hcoef : pullbackCoefficients (DifferentialGeometry.finiteScaleMetric c hc G)
      (extChartAt I p).symm = fun x => c • pullbackCoefficients G (extChartAt I p).symm x := by
    funext x
    rfl
  unfold sectionalCurvature
  rw [hcoef]
  exact DifferentialGeometry.Analysis.coefficientSectional_const_smul _ hc.ne' _ _ _

end Bundle.ContMDiffRiemannianMetric

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

section Distance

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

/-- **Scaling the tangent norms scales the Riemannian distance.** If every tangent extended norm of
`n₂` is `a` times that of `n₁` (`0 < a < ⊤`), the Riemannian extended distances satisfy
`d₂ = a d₁`. -/
theorem riemannianEDist_eq_mul_of_enorm_eq_mul [TopologicalSpace M] [ChartedSpace H M]
    (n₁ n₂ : ∀ x : M, ENorm (TangentSpace I x))
    {a : ℝ≥0∞} (ha0 : a ≠ 0) (hatop : a ≠ ⊤)
    (h : ∀ (x : M) (v : TangentSpace I x), @enorm _ (n₂ x) v = a * @enorm _ (n₁ x) v)
    (x y : M) :
    (letI := n₂; riemannianEDist I x y) = a * (letI := n₁; riemannianEDist I x y) := by
  simp only [Manifold.riemannianEDist]
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_congr fun γ => ?_
  rw [ENNReal.mul_iInf_of_ne ha0 hatop]
  refine iInf_congr fun _ => ?_
  rw [← lintegral_const_mul' a _ hatop]
  exact lintegral_congr fun t => h _ _

variable [mM : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The rescaled Riemannian structure.** If the tangent norms of a Riemannian bundle `b` are those
of a metric `G` (any order) and `(M, d, b)` is a Riemannian manifold, then `(M, c d)` with the
bundle of `c² G` is a Riemannian manifold, and its tangent norms are those of `c² G`. -/
theorem isRiemannianManifold_rescale_finiteScaleMetric {n : ℕ∞ω}
    (b : RiemannianBundle (fun x : M => TangentSpace I x))
    (G : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    (hGnorm : letI := b
      ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (hM : letI := b; IsRiemannianManifold I M) {c : ℝ} (hc : 0 < c) :
    letI := mM.rescale c hc
    letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨(finiteScaleMetric (c ^ 2) (pow_pos hc 2) G).toRiemannianMetric⟩
    IsRiemannianManifold I M ∧ ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt ((finiteScaleMetric (c ^ 2) (pow_pos hc 2) G).inner x w w)) := by
  set Gc := finiteScaleMetric (c ^ 2) (pow_pos hc 2) G with hGc
  have hnew : ∀ (x : M) (w : TangentSpace I x),
      (letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨Gc.toRiemannianMetric⟩;
        ‖w‖ₑ) = ENNReal.ofReal (Real.sqrt (Gc.inner x w w)) := by
    intro x w
    let bundle_LFR28R12 : RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨Gc.toRiemannianMetric⟩
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hscale : ∀ (x : M) (w : TangentSpace I x),
      (letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨Gc.toRiemannianMetric⟩;
        ‖w‖ₑ) = ENNReal.ofReal c * (letI := b; ‖w‖ₑ) := by
    intro x w
    rw [hnew x w, show (letI := b; ‖w‖ₑ) = ENNReal.ofReal (Real.sqrt (G.inner x w w)) from
      hGnorm x w, ← ENNReal.ofReal_mul hc.le]
    congr 1
    change Real.sqrt (c ^ 2 * G.inner x w w) = _
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc.le]
  have ha0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have key : ∀ x y : M, _ := fun x y => riemannianEDist_eq_mul_of_enorm_eq_mul
    (fun _ => (letI := b; inferInstance))
    (fun _ => (letI : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨Gc.toRiemannianMetric⟩;
      inferInstance)) ha0 ENNReal.ofReal_ne_top hscale x y
  let D : M → M → ℝ := fun x y => dist x y
  have hold : ∀ x y : M, ENNReal.ofReal (D x y) = (letI := b; riemannianEDist I x y) := by
    intro x y
    rw [← edist_dist]
    exact (letI := b; hM).out x y
  let metric_LFR28R12 := mM.rescale c hc
  let bundle_LFR28R12 : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨Gc.toRiemannianMetric⟩
  refine ⟨⟨fun x y => ?_⟩, hnew⟩
  calc edist x y = ENNReal.ofReal (c * D x y) := by
        rw [edist_dist]
        rfl
    _ = ENNReal.ofReal c * (letI := b; riemannianEDist I x y) := by
        rw [ENNReal.ofReal_mul hc.le, hold]
    _ = riemannianEDist I x y := (key x y).symm

end Distance

section Directions

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Minimizing directions to an arbitrary set under rescaling** (the singleton case is
`finiteMinimizingDirectionsTo_scaleMetric`): `R⁻¹ • v` is a minimizing unit direction of `G` from
`q` to `Y` iff `v` is one of `R⁻² • G` in the rescaled metric space `(M, R⁻¹ d)`. -/
theorem mem_finiteMinimizingDirectionsTo_finiteScaleMetric_iff {n : ℕ∞ω}
    {G : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)} {R : ℝ} (hR : 0 < R)
    {Y : Set M} {q : M} {v : TangentSpace I q} :
    R⁻¹ • v ∈ G.finiteMinimizingDirectionsTo Y q ↔
      (letI := m.rescale R⁻¹ (inv_pos.mpr hR)
      v ∈ (finiteScaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) G).finiteMinimizingDirectionsTo
        Y q) := by
  have hinf : @Metric.infDist M (m.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace q Y =
      R⁻¹ * Metric.infDist q Y := by
    rw [@infDist_eq_iInf M (m.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace,
      infDist_eq_iInf, Real.mul_iInf_of_nonneg (inv_pos.mpr hR).le]
    rfl
  have hinner : G.inner q (R⁻¹ • v) (R⁻¹ • v) = R⁻¹ ^ 2 * G.inner q v v := by
    simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hexp : (finiteScaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) G).expMap = G.expMap :=
    Bundle.ContMDiffRiemannianMetric.expMap_finiteScaleMetric _ _ G
  change (G.inner q (R⁻¹ • v) (R⁻¹ • v) = 1 ∧
      G.expMap (⟨q, Metric.infDist q Y • R⁻¹ • v⟩ : TangentBundle I M) ∈ Y) ↔
    (R⁻¹ ^ 2 * G.inner q v v = 1 ∧
      (finiteScaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) G).expMap
        (⟨q, @Metric.infDist M (m.rescale R⁻¹ (inv_pos.mpr hR)).toPseudoMetricSpace q Y • v⟩ :
          TangentBundle I M) ∈ Y)
  rw [hexp, hinf, hinner, smul_smul, mul_comm (Metric.infDist q Y) R⁻¹]

end Directions

local notation "E2" => EuclideanSpace ℝ (Fin 2)

/-- **R2 (LFR28).** For a complete surface `S` whose distance is the Riemannian distance of a
`C^{r+1}` metric `κ` with `sec ≥ 0`, and every `Δ > 0`, the metric `κΔ = Δ⁻² κ` (same order) has
`sec ≥ 0`, its minimizing directions for the rescaled distance `Δ⁻¹ d` correspond to those of `κ`
(`u ↔ Δ • u`), and with the bundle `⟨κΔ⟩` on `(S, Δ⁻¹ d)`: `IsRiemannianManifold`,
`CompleteSpace` and the norm identity — the package LFR24 takes.

Strengthening of the frozen statement: the order hypothesis `2 ≤ r` is not needed (the frozen form
is the `example` below). -/
theorem exists_rescaled_carrier_metric {S : Type} [mS : MetricSpace S] [ChartedSpace E2 S]
    [IsManifold (𝓡 2) ∞ S] [hcS : CompleteSpace S]
    [RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) S]
    {r : ℕ∞} (κ : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2
      (TangentSpace (𝓡 2) : S → Type _))
    (hκnorm : ∀ (x : S) (w : TangentSpace (𝓡 2) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w)))
    (hκsec : ∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ κΔ : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2
        (TangentSpace (𝓡 2) : S → Type _),
      (∀ (x : S) (v w : TangentSpace (𝓡 2) x), κΔ.inner x v w = Δ⁻¹ ^ 2 * κ.inner x v w) ∧
      (∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κΔ.sectionalCurvature x v w) ∧
      (∀ (Y : Set S) (s : S) (u : TangentSpace (𝓡 2) s),
        u ∈ κ.finiteMinimizingDirectionsTo Y s →
          letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
          Δ • u ∈ κΔ.finiteMinimizingDirectionsTo Y s) ∧
      (∀ (Y : Set S) (s : S) (u : TangentSpace (𝓡 2) s),
        (letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
         u ∈ κΔ.finiteMinimizingDirectionsTo Y s) →
          Δ⁻¹ • u ∈ κ.finiteMinimizingDirectionsTo Y s) ∧
      (letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
       letI : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) := ⟨κΔ.toRiemannianMetric⟩
       IsRiemannianManifold (𝓡 2) S ∧ CompleteSpace S ∧
         ∀ (x : S) (w : TangentSpace (𝓡 2) x),
           ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κΔ.inner x w w))) := by
  have hΔi : 0 < Δ⁻¹ := inv_pos.mpr hΔ
  have hc : 0 < Δ⁻¹ ^ 2 := pow_pos hΔi 2
  set κΔ := finiteScaleMetric (Δ⁻¹ ^ 2) hc κ with hκΔ
  refine ⟨κΔ, fun x v w => rfl, fun x v w => ?_, fun Y s u hu => ?_, fun Y s u hu => ?_, ?_⟩
  · rw [hκΔ, Bundle.ContMDiffRiemannianMetric.sectionalCurvature_finiteScaleMetric]
    exact mul_nonneg (inv_nonneg.mpr hc.le) (hκsec x v w)
  · refine (mem_finiteMinimizingDirectionsTo_finiteScaleMetric_iff (G := κ) (Y := Y) hΔ).mp ?_
    rwa [smul_smul, inv_mul_cancel₀ hΔ.ne', one_smul]
  · exact (mem_finiteMinimizingDirectionsTo_finiteScaleMetric_iff (G := κ) (Y := Y) hΔ).mpr hu
  · exact isRiemannianManifold_rescale_finiteScaleMetric inferInstance κ hκnorm inferInstance hΔi |>.imp_right
      fun h => ⟨(MetricSpace.rescale_completeSpace_iff mS Δ⁻¹ hΔi).mpr hcS, h⟩

/-- The frozen form of R2 (with the unused hypothesis `2 ≤ r`). -/
example {S : Type} [mS : MetricSpace S] [ChartedSpace E2 S]
    [IsManifold (𝓡 2) ∞ S] [hcS : CompleteSpace S]
    [RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x)] [IsRiemannianManifold (𝓡 2) S]
    {r : ℕ∞} (κ : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2
      (TangentSpace (𝓡 2) : S → Type _)) (_hr : 2 ≤ r)
    (hκnorm : ∀ (x : S) (w : TangentSpace (𝓡 2) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κ.inner x w w)))
    (hκsec : ∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κ.sectionalCurvature x v w)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ κΔ : ContMDiffRiemannianMetric (𝓡 2) ((r : ℕ∞ω) + 1) E2
        (TangentSpace (𝓡 2) : S → Type _),
      (∀ (x : S) (v w : TangentSpace (𝓡 2) x), κΔ.inner x v w = Δ⁻¹ ^ 2 * κ.inner x v w) ∧
      (∀ (x : S) (v w : TangentSpace (𝓡 2) x), 0 ≤ κΔ.sectionalCurvature x v w) ∧
      (∀ (Y : Set S) (s : S) (u : TangentSpace (𝓡 2) s),
        u ∈ κ.finiteMinimizingDirectionsTo Y s →
          letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
          Δ • u ∈ κΔ.finiteMinimizingDirectionsTo Y s) ∧
      (∀ (Y : Set S) (s : S) (u : TangentSpace (𝓡 2) s),
        (letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
         u ∈ κΔ.finiteMinimizingDirectionsTo Y s) →
          Δ⁻¹ • u ∈ κ.finiteMinimizingDirectionsTo Y s) ∧
      (letI := mS.rescale Δ⁻¹ (inv_pos.mpr hΔ)
       letI : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) := ⟨κΔ.toRiemannianMetric⟩
       IsRiemannianManifold (𝓡 2) S ∧ CompleteSpace S ∧
         ∀ (x : S) (w : TangentSpace (𝓡 2) x),
           ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (κΔ.inner x w w))) :=
  exists_rescaled_carrier_metric κ hκnorm hκsec hΔ

end DifferentialGeometry.Geometry.Collapse
