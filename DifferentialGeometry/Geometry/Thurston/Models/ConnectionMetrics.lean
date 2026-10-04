import DifferentialGeometry.Geometry.Thurston.Atlas

/-!
# Connection metrics in coordinates and the fixed Thurston models (GM03, local form)

On `ModelCoordinates` with coordinates `(x, y, z)`, a diagonal base coframe `σ = (a dx, b dy)`
and a connection one-form `α = A dx + B dy` (coefficients depending on `(x, y)` only) give the
connection metric `a² dx² + b² dy² + (dz + α)²` (`connectionInner`). `BaseCoframe.gaussCurvature`
is the Gauss curvature of the base and `FibreConnection.HasCurvature α σ c` says `dα = c dA_σ`.

Normal forms per model, with constants `(κ, c)` proved: `flat` (κ = 0), `hyperbolic`
`e^{-2y} dx² + dy²` (κ = -1), `round R` the stereographic chart of the sphere of radius `R`
(κ = 1 / R²); `nil = -x dy` over `flat` (c = -1), `universalSL2 = e^{-y} dx` over `hyperbolic`
(c = 1), `hopf = (x dy - y dx) / (1 + x² + y²)` over `round (1/2)` (c = 2). The coframes are
literally `coordinateCoframe .hyperbolicProduct`, `.nil`, `.universalSL2`; `flat` with `α = 0`
is the Euclidean inner product, and `round 1` with `α = 0` is the pullback of
`unitCylinderMetric` along inverse stereographic projection times the identity
(`stereoCylinderChart`). Hence a chart in which a metric is literally one of these expressions is
a model chart: `ConnectionAtlas.hasThurstonAtlas` for the six models of `ConnectionModel`.

S³: `hopfParam (x, y, z) = (e^{iz}, (x + iy) e^{iz}) / √(1 + x² + y²)` maps `ModelCoordinates`
to the round unit three-sphere, `2π`-periodically in `z` (`hopfParam_periodic`, fibre length
`2π`), and pulls `sphericalModelMetric` back to the connection metric of `(round (1/2), hopf)`,
curvature 4 and `c = 2` (`sphericalModelMetric_hopfParam`); `hopfChart a` is its inverse on
`a - π < z < a + π` (an `arg` branch), giving the model charts for S³.

Scaling: `FibreScaledAtlas g σ α ℓ` (metric `h + ℓ² (dz + α)²`) is `ConnectionAtlas g σ (ℓ • α)`;
the reflections `y ↦ -y`, `x ↦ -x` flip the sign of `c`; so `h_κ + ℓ² (dz + c α_m)²` is modelled
on model `m` as soon as `ℓ c = ±1` (`FibreScaledAtlas.hasThurstonAtlas`). A homothety by `λ²`
is the connection metric of `(λ σ, λ α)` with constants `(κ / λ², c / λ)`
(`connectionInner_homothety`, `gaussCurvature_smul`, `HasCurvature.homothety`).
Global realizability of the constants by block parameters is not addressed here.
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

namespace GC.Geometry

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

structure BaseCoframe where
  xScale : ℝ → ℝ → ℝ
  yScale : ℝ → ℝ → ℝ

@[ext] structure FibreConnection where
  dxCoeff : ℝ → ℝ → ℝ
  dyCoeff : ℝ → ℝ → ℝ

def connectionCoframe (σ : BaseCoframe) (α : FibreConnection) (p v : ModelCoordinates) :
    Fin 3 → ℝ :=
  ![σ.xScale (p 0) (p 1) * v 0, σ.yScale (p 0) (p 1) * v 1,
    v 2 + α.dxCoeff (p 0) (p 1) * v 0 + α.dyCoeff (p 0) (p 1) * v 1]

def connectionInner (σ : BaseCoframe) (α : FibreConnection) (p v w : ModelCoordinates) : ℝ :=
  ∑ i : Fin 3, connectionCoframe σ α p v i * connectionCoframe σ α p w i

namespace BaseCoframe

def flat : BaseCoframe := ⟨fun _ _ => 1, fun _ _ => 1⟩

def hyperbolic : BaseCoframe := ⟨fun _ y => Real.exp (-y), fun _ _ => 1⟩

def round (R : ℝ) : BaseCoframe :=
  ⟨fun x y => 2 * R / (1 + x ^ 2 + y ^ 2), fun x y => 2 * R / (1 + x ^ 2 + y ^ 2)⟩

instance : SMul ℝ BaseCoframe := ⟨fun l σ => ⟨l • σ.xScale, l • σ.yScale⟩⟩

@[simp] theorem smul_xScale (l : ℝ) (σ : BaseCoframe) (x y : ℝ) :
    (l • σ).xScale x y = l * σ.xScale x y := rfl

@[simp] theorem smul_yScale (l : ℝ) (σ : BaseCoframe) (x y : ℝ) :
    (l • σ).yScale x y = l * σ.yScale x y := rfl

def area (σ : BaseCoframe) (x y : ℝ) : ℝ := σ.xScale x y * σ.yScale x y

def gaussCurvature (σ : BaseCoframe) (x y : ℝ) : ℝ :=
  -(deriv (fun s => deriv (fun s' => σ.yScale s' y) s / σ.xScale s y) x +
      deriv (fun t => deriv (fun t' => σ.xScale x t') t / σ.yScale x t) y) / σ.area x y

theorem gaussCurvature_flat (x y : ℝ) : flat.gaussCurvature x y = 0 := by
  simp [gaussCurvature, flat]

theorem gaussCurvature_hyperbolic (x y : ℝ) : hyperbolic.gaussCurvature x y = -1 := by
  have h1 (t : ℝ) : deriv (fun t' => Real.exp (-t')) t = -Real.exp (-t) := by
    simpa using ((hasDerivAt_neg t).exp).deriv
  have h2 : deriv (fun t => deriv (fun t' => Real.exp (-t')) t / 1) y = Real.exp (-y) := by
    simp only [h1, div_one]
    simpa using ((hasDerivAt_neg y).exp.neg).deriv
  simp only [gaussCurvature, hyperbolic, area, h2]
  simp

theorem gaussCurvature_round {R : ℝ} (hR : R ≠ 0) (x y : ℝ) :
    (round R).gaussCurvature x y = 1 / R ^ 2 := by
  have hD (a b : ℝ) : 1 + a ^ 2 + b ^ 2 ≠ 0 := by positivity
  have hs (s t : ℝ) : deriv (fun s' => 2 * R / (1 + s' ^ 2 + t ^ 2)) s =
      -(2 * R * (2 * s)) / (1 + s ^ 2 + t ^ 2) ^ 2 := by
    have h : HasDerivAt (fun s' => 2 * R / (1 + s' ^ 2 + t ^ 2)) _ s :=
      (hasDerivAt_const s (2 * R)).div (((hasDerivAt_pow 2 s).const_add 1).add_const (t ^ 2))
        (hD s t)
    rw [h.deriv]
    simp
  have ht (s t : ℝ) : deriv (fun t' => 2 * R / (1 + s ^ 2 + t' ^ 2)) t =
      -(2 * R * (2 * t)) / (1 + s ^ 2 + t ^ 2) ^ 2 := by
    have h : HasDerivAt (fun t' => 2 * R / (1 + s ^ 2 + t' ^ 2)) _ t :=
      (hasDerivAt_const t (2 * R)).div ((hasDerivAt_pow 2 t).const_add (1 + s ^ 2)) (hD s t)
    rw [h.deriv]
    simp
  have hfs : (fun s => deriv (fun s' => 2 * R / (1 + s' ^ 2 + y ^ 2)) s /
      (2 * R / (1 + s ^ 2 + y ^ 2))) = fun s => -(2 * s) / (1 + s ^ 2 + y ^ 2) := by
    funext s
    rw [hs]
    have := hD s y
    field_simp
  have hft : (fun t => deriv (fun t' => 2 * R / (1 + x ^ 2 + t' ^ 2)) t /
      (2 * R / (1 + x ^ 2 + t ^ 2))) = fun t => -(2 * t) / (1 + x ^ 2 + t ^ 2) := by
    funext t
    rw [ht]
    have := hD x t
    field_simp
  have hx : deriv (fun s => -(2 * s) / (1 + s ^ 2 + y ^ 2)) x =
      (-2 * (1 + x ^ 2 + y ^ 2) + 2 * x * (2 * x)) / (1 + x ^ 2 + y ^ 2) ^ 2 := by
    have h : HasDerivAt (fun s => -(2 * s) / (1 + s ^ 2 + y ^ 2)) _ x :=
      ((hasDerivAt_id x).const_mul 2).neg.div
        (((hasDerivAt_pow 2 x).const_add 1).add_const (y ^ 2)) (hD x y)
    rw [h.deriv]
    simp
  have hy : deriv (fun t => -(2 * t) / (1 + x ^ 2 + t ^ 2)) y =
      (-2 * (1 + x ^ 2 + y ^ 2) + 2 * y * (2 * y)) / (1 + x ^ 2 + y ^ 2) ^ 2 := by
    have h : HasDerivAt (fun t => -(2 * t) / (1 + x ^ 2 + t ^ 2)) _ y :=
      ((hasDerivAt_id y).const_mul 2).neg.div
        ((hasDerivAt_pow 2 y).const_add (1 + x ^ 2)) (hD x y)
    rw [h.deriv]
    simp
  simp only [gaussCurvature, round, area, hfs, hft, hx, hy]
  have := hD x y
  field_simp
  ring


theorem gaussCurvature_smul {l : ℝ} (hl : l ≠ 0) (σ : BaseCoframe) (x y : ℝ) :
    (l • σ).gaussCurvature x y = σ.gaussCurvature x y / l ^ 2 := by
  have hs : (fun s => deriv (fun s' => (l • σ).yScale s' y) s / (l • σ).xScale s y) =
      fun s => deriv (fun s' => σ.yScale s' y) s / σ.xScale s y := by
    funext s
    simp only [smul_yScale, smul_xScale, deriv_const_mul_field']
    exact mul_div_mul_left _ _ hl
  have ht : (fun t => deriv (fun t' => (l • σ).xScale x t') t / (l • σ).yScale x t) =
      fun t => deriv (fun t' => σ.xScale x t') t / σ.yScale x t := by
    funext t
    simp only [smul_yScale, smul_xScale, deriv_const_mul_field']
    exact mul_div_mul_left _ _ hl
  unfold gaussCurvature
  rw [hs, ht]
  simp only [area, smul_xScale, smul_yScale]
  rw [div_div]
  congr 1
  ring

end BaseCoframe

namespace FibreConnection

instance : Zero FibreConnection := ⟨⟨fun _ _ => 0, fun _ _ => 0⟩⟩

instance : SMul ℝ FibreConnection := ⟨fun l α => ⟨l • α.dxCoeff, l • α.dyCoeff⟩⟩

@[simp] theorem zero_dxCoeff (x y : ℝ) : (0 : FibreConnection).dxCoeff x y = 0 := rfl

@[simp] theorem zero_dyCoeff (x y : ℝ) : (0 : FibreConnection).dyCoeff x y = 0 := rfl

@[simp] theorem smul_dxCoeff (l : ℝ) (α : FibreConnection) (x y : ℝ) :
    (l • α).dxCoeff x y = l * α.dxCoeff x y := rfl

@[simp] theorem smul_dyCoeff (l : ℝ) (α : FibreConnection) (x y : ℝ) :
    (l • α).dyCoeff x y = l * α.dyCoeff x y := rfl

theorem smul_smul' (a b : ℝ) (α : FibreConnection) : a • b • α = (a * b) • α := by
  ext x y <;> simp [mul_assoc]

theorem one_smul' (α : FibreConnection) : (1 : ℝ) • α = α := by
  ext x y <;> simp

theorem smul_zero' (a : ℝ) : a • (0 : FibreConnection) = 0 := by
  ext x y <;> simp

def nil : FibreConnection := ⟨fun _ _ => 0, fun x _ => -x⟩

def universalSL2 : FibreConnection := ⟨fun _ y => Real.exp (-y), fun _ _ => 0⟩

def hopf : FibreConnection :=
  ⟨fun x y => -y / (1 + x ^ 2 + y ^ 2), fun x y => x / (1 + x ^ 2 + y ^ 2)⟩

def curvature (α : FibreConnection) (x y : ℝ) : ℝ :=
  deriv (fun s => α.dyCoeff s y) x - deriv (fun t => α.dxCoeff x t) y

def HasCurvature (α : FibreConnection) (σ : BaseCoframe) (c : ℝ) : Prop :=
  ∀ x y, α.curvature x y = c * σ.area x y

theorem hasCurvature_zero (σ : BaseCoframe) : (0 : FibreConnection).HasCurvature σ 0 := by
  intro x y
  simp [curvature]

theorem hasCurvature_nil : nil.HasCurvature .flat (-1) := by
  intro x y
  simp [curvature, nil, BaseCoframe.area, BaseCoframe.flat]

theorem hasCurvature_universalSL2 : universalSL2.HasCurvature .hyperbolic 1 := by
  intro x y
  have h : deriv (fun t => Real.exp (-t)) y = -Real.exp (-y) := by
    simpa using ((hasDerivAt_neg y).exp).deriv
  simp [curvature, universalSL2, BaseCoframe.area, BaseCoframe.hyperbolic, h]

theorem hasCurvature_hopf : hopf.HasCurvature (.round (1 / 2)) 2 := by
  intro x y
  have hD (a b : ℝ) : 1 + a ^ 2 + b ^ 2 ≠ 0 := by positivity
  have h1 : deriv (fun s => s / (1 + s ^ 2 + y ^ 2)) x =
      (1 * (1 + x ^ 2 + y ^ 2) - x * (2 * x)) / (1 + x ^ 2 + y ^ 2) ^ 2 := by
    have h : HasDerivAt (fun s => s / (1 + s ^ 2 + y ^ 2)) _ x :=
      (hasDerivAt_id x).div (((hasDerivAt_pow 2 x).const_add 1).add_const (y ^ 2)) (hD x y)
    rw [h.deriv]
    simp
  have h2 : deriv (fun t => -t / (1 + x ^ 2 + t ^ 2)) y =
      (-1 * (1 + x ^ 2 + y ^ 2) - (-y) * (2 * y)) / (1 + x ^ 2 + y ^ 2) ^ 2 := by
    have h : HasDerivAt (fun t => -t / (1 + x ^ 2 + t ^ 2)) _ y :=
      (hasDerivAt_neg y).div (((hasDerivAt_pow 2 y).const_add (1 + x ^ 2))) (hD x y)
    rw [h.deriv]
    simp
  simp only [curvature, hopf, BaseCoframe.area, BaseCoframe.round, h1, h2]
  field_simp
  ring


theorem HasCurvature.smul {α : FibreConnection} {σ : BaseCoframe} {c : ℝ}
    (h : α.HasCurvature σ c) (l : ℝ) : (l • α).HasCurvature σ (l * c) := by
  intro x y
  simp only [curvature, smul_dyCoeff, smul_dxCoeff, deriv_const_mul_field']
  rw [← mul_sub]
  exact (congrArg (l * ·) (h x y)).trans (mul_assoc _ _ _).symm

theorem HasCurvature.homothety {α : FibreConnection} {σ : BaseCoframe} {c l : ℝ}
    (h : α.HasCurvature σ c) (hl : l ≠ 0) : (l • α).HasCurvature (l • σ) (c / l) := by
  intro x y
  simp only [curvature, smul_dyCoeff, smul_dxCoeff, deriv_const_mul_field',
    BaseCoframe.area, BaseCoframe.smul_xScale, BaseCoframe.smul_yScale]
  rw [← mul_sub]
  have hxy := h x y
  simp only [curvature, BaseCoframe.area] at hxy
  rw [hxy]
  field_simp

end FibreConnection

theorem connectionCoframe_hyperbolicProduct (p v : ModelCoordinates) :
    connectionCoframe .hyperbolic 0 p v = coordinateCoframe .hyperbolicProduct p v := by
  ext i; fin_cases i <;> simp [connectionCoframe, coordinateCoframe, BaseCoframe.hyperbolic]

theorem connectionCoframe_nil (p v : ModelCoordinates) :
    connectionCoframe .flat .nil p v = coordinateCoframe .nil p v := by
  ext i; fin_cases i <;>
    simp [connectionCoframe, coordinateCoframe, BaseCoframe.flat, FibreConnection.nil]
  ring

theorem connectionCoframe_universalSL2 (p v : ModelCoordinates) :
    connectionCoframe .hyperbolic .universalSL2 p v = coordinateCoframe .universalSL2 p v := by
  ext i; fin_cases i <;>
    simp [connectionCoframe, coordinateCoframe, BaseCoframe.hyperbolic,
      FibreConnection.universalSL2]

theorem connectionInner_euclidean (p v w : ModelCoordinates) :
    connectionInner .flat 0 p v w = euclideanModelMetric.inner p v w := by
  change connectionInner .flat 0 p v w = inner ℝ v w
  simp [connectionInner, connectionCoframe, BaseCoframe.flat, Fin.sum_univ_three,
    PiLp.inner_apply]
  ring

def stereoDenom (p : ModelCoordinates) : ℝ := 1 + p 0 ^ 2 + p 1 ^ 2

theorem stereoDenom_pos (p : ModelCoordinates) : 0 < stereoDenom p := by
  unfold stereoDenom; positivity

def inverseStereoAmbient (p : ModelCoordinates) : EuclideanSpace ℝ (Fin 3) :=
  !₂[2 * p 0 / stereoDenom p, 2 * p 1 / stereoDenom p,
    (p 0 ^ 2 + p 1 ^ 2 - 1) / stereoDenom p]

theorem inverseStereoAmbient_mem (p : ModelCoordinates) :
    inverseStereoAmbient p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have hD := (stereoDenom_pos p).ne'
  rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp only [inverseStereoAmbient, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp
  field_simp
  unfold stereoDenom
  ring

private abbrev coordL (i : Fin 3) : ModelCoordinates →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

private theorem hasFDerivAt_coord (p : ModelCoordinates) (i : Fin 3) :
    HasFDerivAt (fun q : ModelCoordinates => q i) (coordL i) p :=
  PiLp.hasFDerivAt_apply 2 p i

private theorem hasFDerivAt_stereoDenom (p : ModelCoordinates) :
    HasFDerivAt stereoDenom ((2 * p 0) • coordL 0 +
      (2 * p 1) • coordL 1) p := by
  have h := (((hasFDerivAt_coord p 0).pow 2).const_add 1).add ((hasFDerivAt_coord p 1).pow 2)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp

private theorem hasFDerivAt_stereoDenom_inv (p : ModelCoordinates) :
    HasFDerivAt (fun q => (stereoDenom q)⁻¹)
      ((-(stereoDenom p ^ 2)⁻¹) • ((2 * p 0) • coordL 0 +
        (2 * p 1) • coordL 1)) p := by
  have h := (hasFDerivAt_inv (stereoDenom_pos p).ne').comp p (hasFDerivAt_stereoDenom p)
  refine h.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
  simp
  ring

theorem contDiff_inverseStereoAmbient : ContDiff ℝ ∞ inverseStereoAmbient := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : ModelCoordinates => q j) := (coordL j).contDiff
  have hD : ContDiff ℝ ∞ stereoDenom := by unfold stereoDenom; fun_prop
  have hne : ∀ q, stereoDenom q ≠ 0 := fun q => (stereoDenom_pos q).ne'
  refine contDiff_euclidean.2 fun i => ?_
  fin_cases i
  · change ContDiff ℝ ∞ (fun q : ModelCoordinates => 2 * q 0 / stereoDenom q)
    exact ContDiff.div (by fun_prop) hD hne
  · change ContDiff ℝ ∞ (fun q : ModelCoordinates => 2 * q 1 / stereoDenom q)
    exact ContDiff.div (by fun_prop) hD hne
  · change ContDiff ℝ ∞ (fun q : ModelCoordinates => (q 0 ^ 2 + q 1 ^ 2 - 1) / stereoDenom q)
    exact ContDiff.div (by fun_prop) hD hne

theorem fderiv_inverseStereoAmbient_apply (p v : ModelCoordinates) :
    fderiv ℝ inverseStereoAmbient p v =
      !₂[(2 * v 0 * stereoDenom p - 2 * p 0 * (2 * p 0 * v 0 + 2 * p 1 * v 1)) /
          stereoDenom p ^ 2,
        (2 * v 1 * stereoDenom p - 2 * p 1 * (2 * p 0 * v 0 + 2 * p 1 * v 1)) /
          stereoDenom p ^ 2,
        2 * (2 * p 0 * v 0 + 2 * p 1 * v 1) / stereoDenom p ^ 2] := by
  have hψ := contDiff_inverseStereoAmbient
  have hcomp (i : Fin 3) : (fderiv ℝ inverseStereoAmbient p v) i =
      fderiv ℝ (fun q => inverseStereoAmbient q i) p v := by
    have h := ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp p
      ((hψ.differentiable (by decide)) p).hasFDerivAt).fderiv
    rw [show (fun q => inverseStereoAmbient q i) =
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) ∘ inverseStereoAmbient from rfl, h]
    rfl
  have hinv := hasFDerivAt_stereoDenom_inv p
  have hpos := (stereoDenom_pos p).ne'
  have e0 : (fderiv ℝ inverseStereoAmbient p v) 0 =
      (2 * v 0 * stereoDenom p - 2 * p 0 * (2 * p 0 * v 0 + 2 * p 1 * v 1)) /
        stereoDenom p ^ 2 := by
    have h : HasFDerivAt (fun q => 2 * q 0 * (stereoDenom q)⁻¹) _ p :=
      ((hasFDerivAt_coord p 0).const_mul 2).mul hinv
    have hf : (fun q => inverseStereoAmbient q 0) = fun q => 2 * q 0 * (stereoDenom q)⁻¹ := by
      funext q; simp [inverseStereoAmbient, div_eq_mul_inv]
    rw [hcomp, hf, h.fderiv]
    simp
    field_simp
    ring
  have e1 : (fderiv ℝ inverseStereoAmbient p v) 1 =
      (2 * v 1 * stereoDenom p - 2 * p 1 * (2 * p 0 * v 0 + 2 * p 1 * v 1)) /
        stereoDenom p ^ 2 := by
    have h : HasFDerivAt (fun q => 2 * q 1 * (stereoDenom q)⁻¹) _ p :=
      ((hasFDerivAt_coord p 1).const_mul 2).mul hinv
    have hf : (fun q => inverseStereoAmbient q 1) = fun q => 2 * q 1 * (stereoDenom q)⁻¹ := by
      funext q; simp [inverseStereoAmbient, div_eq_mul_inv]
    rw [hcomp, hf, h.fderiv]
    simp
    field_simp
    ring
  have e2 : (fderiv ℝ inverseStereoAmbient p v) 2 =
      2 * (2 * p 0 * v 0 + 2 * p 1 * v 1) / stereoDenom p ^ 2 := by
    have h : HasFDerivAt (fun q => (q 0 ^ 2 + q 1 ^ 2 - 1) * (stereoDenom q)⁻¹) _ p :=
      ((((hasFDerivAt_coord p 0).pow 2).add ((hasFDerivAt_coord p 1).pow 2)).sub_const
        1).mul hinv
    have hf : (fun q => inverseStereoAmbient q 2) =
        fun q => (q 0 ^ 2 + q 1 ^ 2 - 1) * (stereoDenom q)⁻¹ := by
      funext q; simp [inverseStereoAmbient, div_eq_mul_inv]
    rw [hcomp, hf, h.fderiv]
    simp
    field_simp
    unfold stereoDenom
    ring
  ext i
  fin_cases i
  exacts [e0, e1, e2]

def inverseStereo (p : ModelCoordinates) : SpatialNeckSphere :=
  ⟨inverseStereoAmbient p, inverseStereoAmbient_mem p⟩

theorem contMDiff_inverseStereo : ContMDiff (𝓡 3) (𝓡 2) ∞ inverseStereo :=
  contDiff_inverseStereoAmbient.contMDiff.codRestrict_sphere inverseStereoAmbient_mem

theorem dIncl_mfderiv_inverseStereo (p v : ModelCoordinates) :
    dIncl (n := 2) (inverseStereo p) (mfderiv (𝓡 3) (𝓡 2) inverseStereo p v) =
      fderiv ℝ inverseStereoAmbient p v := by
  have hd : MDifferentiableAt (𝓡 3) (𝓡 2) inverseStereo p :=
    contMDiff_inverseStereo.contMDiffAt.mdifferentiableAt (by decide)
  have hι : MDifferentiableAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      ((↑) : SpatialNeckSphere → EuclideanSpace ℝ (Fin 3)) (inverseStereo p) :=
    (contMDiff_coe_sphere (n := 2)).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hcomp := mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 2)
    (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))) (f := inverseStereo)
    (g := ((↑) : SpatialNeckSphere → EuclideanSpace ℝ (Fin 3))) p hι hd v
  have hfun : ((↑) : SpatialNeckSphere → EuclideanSpace ℝ (Fin 3)) ∘ inverseStereo =
      inverseStereoAmbient := rfl
  rw [hfun, mfderiv_eq_fderiv] at hcomp
  have hkey : dIncl (n := 2) (inverseStereo p) (mfderiv (𝓡 3) (𝓡 2) inverseStereo p v) =
      mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        ((↑) : SpatialNeckSphere → EuclideanSpace ℝ (Fin 3)) (inverseStereo p)
        (mfderiv (𝓡 3) (𝓡 2) inverseStereo p v) := by
    with_unfolding_all rfl
  exact hkey.trans hcomp.symm

theorem roundMetric_inverseStereo (p v w : ModelCoordinates) :
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner (inverseStereo p)
        (mfderiv (𝓡 3) (𝓡 2) inverseStereo p v) (mfderiv (𝓡 3) (𝓡 2) inverseStereo p w) =
      (2 / stereoDenom p) ^ 2 * (v 0 * w 0 + v 1 * w 1) := by
  rw [roundMetric_inner, dIncl_mfderiv_inverseStereo, dIncl_mfderiv_inverseStereo,
    fderiv_inverseStereoAmbient_apply, fderiv_inverseStereoAmbient_apply]
  have hD := (stereoDenom_pos p).ne'
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  field_simp
  unfold stereoDenom
  ring

theorem unitCylinderMetric_inner_apply (y : SpatialNeckCylinder)
    (V W : TangentSpace SpatialNeckCylinderModel y) :
    unitCylinderMetric.inner y V W =
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y.1 V.1 W.1 + V.2 * W.2 :=
  rfl

def cylinderParam (p : ModelCoordinates) : SpatialNeckCylinder := (inverseStereo p, p 2)

theorem contMDiff_cylinderParam :
    ContMDiff (𝓡 3) SpatialNeckCylinderModel ∞ cylinderParam :=
  contMDiff_inverseStereo.prodMk (coordL 2).contDiff.contMDiff

theorem unitCylinderMetric_cylinderParam (p v w : ModelCoordinates) :
    unitCylinderMetric.inner (cylinderParam p)
        (mfderiv (𝓡 3) SpatialNeckCylinderModel cylinderParam p v)
        (mfderiv (𝓡 3) SpatialNeckCylinderModel cylinderParam p w) =
      (2 / stereoDenom p) ^ 2 * (v 0 * w 0 + v 1 * w 1) + v 2 * w 2 := by
  have hd : MDifferentiableAt (𝓡 3) (𝓡 2) inverseStereo p :=
    contMDiff_inverseStereo.contMDiffAt.mdifferentiableAt (by decide)
  have h2 : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) (fun q : ModelCoordinates => q 2) p :=
    ((coordL 2).contDiff (n := ∞)).contMDiff.contMDiffAt.mdifferentiableAt (by decide)
  have hprod : mfderiv (𝓡 3) SpatialNeckCylinderModel cylinderParam p =
      (mfderiv (𝓡 3) (𝓡 2) inverseStereo p).prod
        (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun q : ModelCoordinates => q 2) p) :=
    mfderiv_prodMk hd h2
  have hlin (u : ModelCoordinates) :
      mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun q : ModelCoordinates => q 2) p u = u 2 := by
    rw [mfderiv_eq_fderiv]
    exact congrArg (fun L : ModelCoordinates →L[ℝ] ℝ => L u) (coordL 2).fderiv
  have h1 (u : ModelCoordinates) :
      (mfderiv (𝓡 3) SpatialNeckCylinderModel cylinderParam p u).1 =
        mfderiv (𝓡 3) (𝓡 2) inverseStereo p u := by
    rw [hprod]; rfl
  have h2' (u : ModelCoordinates) :
      (mfderiv (𝓡 3) SpatialNeckCylinderModel cylinderParam p u).2 = u 2 := by
    rw [hprod]; exact hlin u
  rw [unitCylinderMetric_inner_apply, h1, h1, h2', h2']
  exact congrArg (· + v 2 * w 2) (roundMetric_inverseStereo p v w)

def stereoProjAmbient (u : EuclideanSpace ℝ (Fin 3)) (t : ℝ) : ModelCoordinates :=
  !₂[u 0 / (1 - u 2), u 1 / (1 - u 2), t]

theorem inverseStereoAmbient_two_ne (p : ModelCoordinates) : inverseStereoAmbient p 2 ≠ 1 := by
  have hD := (stereoDenom_pos p).ne'
  change (p 0 ^ 2 + p 1 ^ 2 - 1) / stereoDenom p ≠ 1
  intro h
  rw [div_eq_one_iff_eq hD] at h
  unfold stereoDenom at h
  linarith

theorem stereoProjAmbient_cylinderParam (p : ModelCoordinates) :
    stereoProjAmbient ((cylinderParam p).1 : EuclideanSpace ℝ (Fin 3)) (cylinderParam p).2 =
      p := by
  have hD := (stereoDenom_pos p).ne'
  have ha : 1 - (p 0 ^ 2 + p 1 ^ 2 - 1) / stereoDenom p = 2 / stereoDenom p := by
    field_simp; unfold stereoDenom; ring
  ext i
  fin_cases i <;>
    simp [stereoProjAmbient, cylinderParam, inverseStereo, inverseStereoAmbient, ha] <;>
    field_simp

theorem cylinderParam_stereoProjAmbient (y : SpatialNeckCylinder)
    (hy : (y.1 : EuclideanSpace ℝ (Fin 3)) 2 ≠ 1) :
    cylinderParam (stereoProjAmbient (y.1 : EuclideanSpace ℝ (Fin 3)) y.2) = y := by
  obtain ⟨⟨s, hs⟩, t⟩ := y
  have hn : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq s
    rw [mem_sphere_zero_iff_norm.mp hs] at h
    simpa [Fin.sum_univ_three] using h.symm
  have ha : 1 - s 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have hD : stereoDenom (stereoProjAmbient s t) = 2 / (1 - s 2) := by
    simp [stereoDenom, stereoProjAmbient]
    field_simp
    linear_combination hn
  refine Prod.ext (Subtype.ext ?_) rfl
  ext i
  fin_cases i <;>
    simp [cylinderParam, inverseStereo, inverseStereoAmbient, hD] <;>
    simp [stereoProjAmbient] <;>
    field_simp
  linear_combination hn

theorem contMDiffOn_stereoProj :
    ContMDiffOn SpatialNeckCylinderModel (𝓡 3) ∞
      (fun y : SpatialNeckCylinder => stereoProjAmbient (y.1 : EuclideanSpace ℝ (Fin 3)) y.2)
      {y | (y.1 : EuclideanSpace ℝ (Fin 3)) 2 ≠ 1} := by
  intro y hy
  have hinner : ContMDiff SpatialNeckCylinderModel 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × ℝ) ∞
      (fun y : SpatialNeckCylinder => ((y.1 : EuclideanSpace ℝ (Fin 3)), y.2)) :=
    ((contMDiff_coe_sphere (n := 2)).comp contMDiff_fst).prodMk_space contMDiff_snd
  have hG : ContDiffAt ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 3) × ℝ => stereoProjAmbient z.1 z.2)
      ((y.1 : EuclideanSpace ℝ (Fin 3)), y.2) := by
    have hc (j : Fin 3) : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 3) × ℝ => z.1 j) :=
      (coordL j).contDiff.comp contDiff_fst
    have hne : (1 : ℝ) - (y.1 : EuclideanSpace ℝ (Fin 3)) 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    refine contDiffAt_euclidean.2 fun i => ?_
    fin_cases i
    · exact ((hc 0).contDiffAt).div (contDiffAt_const.sub (hc 2).contDiffAt) hne
    · exact ((hc 1).contDiffAt).div (contDiffAt_const.sub (hc 2).contDiffAt) hne
    · exact contDiff_snd.contDiffAt
  have hcomp := hG.comp_contMDiffAt
    (f := fun y : SpatialNeckCylinder => ((y.1 : EuclideanSpace ℝ (Fin 3)), y.2)) (x := y)
    hinner.contMDiffAt
  exact hcomp.contMDiffWithinAt

def stereoCylinderChart :
    PartialDiffeomorph SpatialNeckCylinderModel (𝓡 3) SpatialNeckCylinder ModelCoordinates ∞ where
  toFun y := stereoProjAmbient (y.1 : EuclideanSpace ℝ (Fin 3)) y.2
  invFun := cylinderParam
  source := {y | (y.1 : EuclideanSpace ℝ (Fin 3)) 2 ≠ 1}
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' p _ := inverseStereoAmbient_two_ne p
  left_inv' y hy := cylinderParam_stereoProjAmbient y hy
  right_inv' p _ := stereoProjAmbient_cylinderParam p
  open_source := isOpen_ne_fun
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).continuous.comp
      (continuous_subtype_val.comp continuous_fst)) continuous_const
  open_target := isOpen_univ
  contMDiffOn_toFun := contMDiffOn_stereoProj
  contMDiffOn_invFun := contMDiff_cylinderParam.contMDiffOn


theorem connectionInner_round_zero (R : ℝ) (p v w : ModelCoordinates) :
    connectionInner (.round R) 0 p v w =
      (2 * R / stereoDenom p) ^ 2 * (v 0 * w 0 + v 1 * w 1) + v 2 * w 2 := by
  simp [connectionInner, connectionCoframe, BaseCoframe.round, stereoDenom, Fin.sum_univ_three]
  ring

theorem stereoCylinderChart_inner (y : SpatialNeckCylinder) (hy : y ∈ stereoCylinderChart.source)
    (v w : TangentSpace SpatialNeckCylinderModel y) :
    connectionInner (.round 1) 0 (stereoCylinderChart y)
        (mfderiv SpatialNeckCylinderModel (𝓡 3) stereoCylinderChart y v)
        (mfderiv SpatialNeckCylinderModel (𝓡 3) stereoCylinderChart y w) =
      unitCylinderMetric.inner y v w := by
  have hpt : cylinderParam (stereoCylinderChart y) = y := stereoCylinderChart.left_inv' hy
  have hΘ : MDifferentiableAt SpatialNeckCylinderModel (𝓡 3) stereoCylinderChart y :=
    stereoCylinderChart.mdifferentiableAt (by decide) hy
  have hC : MDifferentiableAt (𝓡 3) SpatialNeckCylinderModel cylinderParam
      (stereoCylinderChart y) :=
    contMDiff_cylinderParam.contMDiffAt.mdifferentiableAt (by decide)
  have hev : cylinderParam ∘ stereoCylinderChart =ᶠ[nhds y] id := by
    filter_upwards [stereoCylinderChart.open_source.mem_nhds hy] with z hz
    exact stereoCylinderChart.left_inv' hz
  have hid (u : TangentSpace SpatialNeckCylinderModel y) :
      mfderiv (𝓡 3) SpatialNeckCylinderModel cylinderParam (stereoCylinderChart y)
        (mfderiv SpatialNeckCylinderModel (𝓡 3) stereoCylinderChart y u) = u := by
    rw [← mfderiv_comp_apply y hC hΘ u, hev.mfderiv_eq, mfderiv_id]
    rfl
  have h := unitCylinderMetric_cylinderParam (stereoCylinderChart y)
    (mfderiv SpatialNeckCylinderModel (𝓡 3) stereoCylinderChart y v)
    (mfderiv SpatialNeckCylinderModel (𝓡 3) stereoCylinderChart y w)
  rw [hid, hid, hpt] at h
  rw [h]
  exact (connectionInner_round_zero 1 _ _ _).trans (by rw [mul_one])


def hopfFrame (p : ModelCoordinates) : EuclideanSpace ℝ (Fin 4) :=
  !₂[Real.cos (p 2), Real.sin (p 2), p 0 * Real.cos (p 2) - p 1 * Real.sin (p 2),
    p 0 * Real.sin (p 2) + p 1 * Real.cos (p 2)]

def hopfAmbient (p : ModelCoordinates) : EuclideanSpace ℝ (Fin 4) :=
  (Real.sqrt (stereoDenom p))⁻¹ • hopfFrame p

theorem inner_hopfFrame_self (p : ModelCoordinates) :
    inner ℝ (hopfFrame p) (hopfFrame p) = stereoDenom p := by
  rw [PiLp.inner_apply]
  simp [hopfFrame, Fin.sum_univ_four, stereoDenom]
  linear_combination (p 0 ^ 2 + p 1 ^ 2) * Real.sin_sq_add_cos_sq (p 2)

theorem hopfAmbient_mem (p : ModelCoordinates) :
    hopfAmbient p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 := by
  have hD := stereoDenom_pos p
  rw [mem_sphere_zero_iff_norm]
  have h2 : ‖hopfAmbient p‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq, hopfAmbient, real_inner_smul_left, real_inner_smul_right,
      inner_hopfFrame_self, ← mul_assoc, ← sq, inv_pow, Real.sq_sqrt hD.le, inv_mul_cancel₀ hD.ne']
  nlinarith [norm_nonneg (hopfAmbient p)]

theorem contDiff_hopfFrame : ContDiff ℝ ∞ hopfFrame := by
  have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : ModelCoordinates => q j) := (coordL j).contDiff
  refine contDiff_euclidean.2 fun i => ?_
  fin_cases i
  · change ContDiff ℝ ∞ (fun q : ModelCoordinates => Real.cos (q 2))
    fun_prop
  · change ContDiff ℝ ∞ (fun q : ModelCoordinates => Real.sin (q 2))
    fun_prop
  · change ContDiff ℝ ∞ (fun q : ModelCoordinates =>
      q 0 * Real.cos (q 2) - q 1 * Real.sin (q 2))
    fun_prop
  · change ContDiff ℝ ∞ (fun q : ModelCoordinates =>
      q 0 * Real.sin (q 2) + q 1 * Real.cos (q 2))
    fun_prop

theorem contDiff_hopfAmbient : ContDiff ℝ ∞ hopfAmbient := by
  have hD : ContDiff ℝ ∞ stereoDenom := by
    have hc (j : Fin 3) : ContDiff ℝ ∞ (fun q : ModelCoordinates => q j) :=
      (coordL j).contDiff
    unfold stereoDenom; fun_prop
  have hs : ContDiff ℝ ∞ (fun q => Real.sqrt (stereoDenom q)) :=
    hD.sqrt fun q => (stereoDenom_pos q).ne'
  exact (hs.inv fun q => (Real.sqrt_pos.2 (stereoDenom_pos q)).ne').smul contDiff_hopfFrame

theorem fderiv_hopfFrame_apply (p v : ModelCoordinates) :
    fderiv ℝ hopfFrame p v =
      !₂[-Real.sin (p 2) * v 2, Real.cos (p 2) * v 2,
        v 0 * Real.cos (p 2) - v 1 * Real.sin (p 2) -
          (p 0 * Real.sin (p 2) + p 1 * Real.cos (p 2)) * v 2,
        v 0 * Real.sin (p 2) + v 1 * Real.cos (p 2) +
          (p 0 * Real.cos (p 2) - p 1 * Real.sin (p 2)) * v 2] := by
  have hcomp (i : Fin 4) : (fderiv ℝ hopfFrame p v) i =
      fderiv ℝ (fun q => hopfFrame q i) p v := by
    have h := ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) i).hasFDerivAt.comp p
      ((contDiff_hopfFrame.differentiable (by decide)) p).hasFDerivAt).fderiv
    rw [show (fun q => hopfFrame q i) =
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) i) ∘ hopfFrame from rfl, h]
    rfl
  have hx := hasFDerivAt_coord p 0
  have hy := hasFDerivAt_coord p 1
  have hc : HasFDerivAt (fun q : ModelCoordinates => Real.cos (q 2)) _ p :=
    (hasFDerivAt_coord p 2).cos
  have hs : HasFDerivAt (fun q : ModelCoordinates => Real.sin (q 2)) _ p :=
    (hasFDerivAt_coord p 2).sin
  have e0 : (fderiv ℝ hopfFrame p v) 0 = -Real.sin (p 2) * v 2 := by
    rw [hcomp]
    change fderiv ℝ (fun q : ModelCoordinates => Real.cos (q 2)) p v = _
    rw [hc.fderiv]
    simp
  have e1 : (fderiv ℝ hopfFrame p v) 1 = Real.cos (p 2) * v 2 := by
    rw [hcomp]
    change fderiv ℝ (fun q : ModelCoordinates => Real.sin (q 2)) p v = _
    rw [hs.fderiv]
    simp
  have e2 : (fderiv ℝ hopfFrame p v) 2 = v 0 * Real.cos (p 2) - v 1 * Real.sin (p 2) -
      (p 0 * Real.sin (p 2) + p 1 * Real.cos (p 2)) * v 2 := by
    rw [hcomp]
    have h : HasFDerivAt (fun q : ModelCoordinates =>
        q 0 * Real.cos (q 2) - q 1 * Real.sin (q 2)) _ p := (hx.mul hc).sub (hy.mul hs)
    change fderiv ℝ (fun q : ModelCoordinates =>
        q 0 * Real.cos (q 2) - q 1 * Real.sin (q 2)) p v = _
    rw [h.fderiv]
    simp
    ring
  have e3 : (fderiv ℝ hopfFrame p v) 3 = v 0 * Real.sin (p 2) + v 1 * Real.cos (p 2) +
      (p 0 * Real.cos (p 2) - p 1 * Real.sin (p 2)) * v 2 := by
    rw [hcomp]
    have h : HasFDerivAt (fun q : ModelCoordinates =>
        q 0 * Real.sin (q 2) + q 1 * Real.cos (q 2)) _ p := (hx.mul hs).add (hy.mul hc)
    change fderiv ℝ (fun q : ModelCoordinates =>
        q 0 * Real.sin (q 2) + q 1 * Real.cos (q 2)) p v = _
    rw [h.fderiv]
    simp
    ring
  ext i
  fin_cases i
  exacts [e0, e1, e2, e3]

theorem inner_fderiv_hopfFrame (p v w : ModelCoordinates) :
    inner ℝ (fderiv ℝ hopfFrame p v) (fderiv ℝ hopfFrame p w) =
      v 0 * w 0 + v 1 * w 1 + (p 0 * v 1 - p 1 * v 0) * w 2 +
        (p 0 * w 1 - p 1 * w 0) * v 2 + stereoDenom p * (v 2 * w 2) := by
  rw [fderiv_hopfFrame_apply, fderiv_hopfFrame_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_four, stereoDenom]
  simp
  linear_combination (v 0 * w 0 + v 1 * w 1 + (p 0 * v 1 - p 1 * v 0) * w 2 +
    (p 0 * w 1 - p 1 * w 0) * v 2 + (1 + p 0 ^ 2 + p 1 ^ 2) * (v 2 * w 2)) *
      Real.sin_sq_add_cos_sq (p 2)

theorem inner_fderiv_hopfFrame_self (p v : ModelCoordinates) :
    inner ℝ (fderiv ℝ hopfFrame p v) (hopfFrame p) = p 0 * v 0 + p 1 * v 1 := by
  rw [fderiv_hopfFrame_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_four, hopfFrame]
  simp
  linear_combination (p 0 * v 0 + p 1 * v 1) * Real.sin_sq_add_cos_sq (p 2)

theorem fderiv_hopfAmbient_apply (p v : ModelCoordinates) :
    fderiv ℝ hopfAmbient p v =
      (Real.sqrt (stereoDenom p))⁻¹ • fderiv ℝ hopfFrame p v +
        (-((Real.sqrt (stereoDenom p))⁻¹ * ((p 0 * v 0 + p 1 * v 1) / stereoDenom p))) •
          hopfFrame p := by
  have hD := stereoDenom_pos p
  have hsq : Real.sqrt (stereoDenom p) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hr := (hasFDerivAt_inv hsq).comp p ((hasFDerivAt_stereoDenom p).sqrt hD.ne')
  have hU := ((contDiff_hopfFrame.differentiable (by decide)) p).hasFDerivAt
  have h : HasFDerivAt hopfAmbient _ p := hr.smul hU
  rw [h.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, Function.comp_apply]
  congr 2
  simp
  field_simp
  rw [Real.sq_sqrt hD.le]
  ring

theorem inner_fderiv_hopfAmbient (p v w : ModelCoordinates) :
    inner ℝ (fderiv ℝ hopfAmbient p v) (fderiv ℝ hopfAmbient p w) =
      connectionInner (.round (1 / 2)) .hopf p v w := by
  have hD := stereoDenom_pos p
  rw [fderiv_hopfAmbient_apply, fderiv_hopfAmbient_apply]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    inner_fderiv_hopfFrame, inner_fderiv_hopfFrame_self, inner_hopfFrame_self]
  rw [real_inner_comm _ (hopfFrame p), inner_fderiv_hopfFrame_self]
  have hr2 : (Real.sqrt (stereoDenom p))⁻¹ * (Real.sqrt (stereoDenom p))⁻¹ =
      (stereoDenom p)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hD.le]
  simp only [connectionInner, connectionCoframe, BaseCoframe.round, FibreConnection.hopf,
    Fin.sum_univ_three]
  simp only [Fin.isValue, neg_mul, mul_neg, neg_neg, one_div, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, mul_inv_cancel₀, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  linear_combination (norm := skip) (v 0 * w 0 + v 1 * w 1 + (p 0 * v 1 - p 1 * v 0) * w 2 +
    (p 0 * w 1 - p 1 * w 0) * v 2 + stereoDenom p * (v 2 * w 2) -
      (p 0 * v 0 + p 1 * v 1) * (p 0 * w 0 + p 1 * w 1) / stereoDenom p) * hr2
  have hD' : 1 + p 0 ^ 2 + p 1 ^ 2 ≠ 0 := by positivity
  unfold stereoDenom
  field_simp
  ring

def hopfParam (p : ModelCoordinates) : RoundThree := ⟨hopfAmbient p, hopfAmbient_mem p⟩

theorem contMDiff_hopfParam : ContMDiff (𝓡 3) (𝓡 3) ∞ hopfParam :=
  contDiff_hopfAmbient.contMDiff.codRestrict_sphere hopfAmbient_mem

theorem dIncl_mfderiv_hopfParam (p v : ModelCoordinates) :
    dIncl (n := 3) (hopfParam p) (mfderiv (𝓡 3) (𝓡 3) hopfParam p v) =
      fderiv ℝ hopfAmbient p v := by
  have hd : MDifferentiableAt (𝓡 3) (𝓡 3) hopfParam p :=
    contMDiff_hopfParam.contMDiffAt.mdifferentiableAt (by decide)
  have hι : MDifferentiableAt (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4))
      ((↑) : RoundThree → EuclideanSpace ℝ (Fin 4)) (hopfParam p) :=
    (contMDiff_coe_sphere (n := 3)).contMDiffAt.mdifferentiableAt
      (by decide : (∞ : ℕ∞ω) ≠ 0)
  have hcomp := mfderiv_comp_apply (I := 𝓡 3) (I' := 𝓡 3)
    (I'' := 𝓘(ℝ, EuclideanSpace ℝ (Fin 4))) (f := hopfParam)
    (g := ((↑) : RoundThree → EuclideanSpace ℝ (Fin 4))) p hι hd v
  have hfun : ((↑) : RoundThree → EuclideanSpace ℝ (Fin 4)) ∘ hopfParam = hopfAmbient := rfl
  rw [hfun, mfderiv_eq_fderiv] at hcomp
  have hkey : dIncl (n := 3) (hopfParam p) (mfderiv (𝓡 3) (𝓡 3) hopfParam p v) =
      mfderiv (𝓡 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4))
        ((↑) : RoundThree → EuclideanSpace ℝ (Fin 4)) (hopfParam p)
        (mfderiv (𝓡 3) (𝓡 3) hopfParam p v) := by
    with_unfolding_all rfl
  exact hkey.trans hcomp.symm

theorem sphericalModelMetric_hopfParam (p v w : ModelCoordinates) :
    sphericalModelMetric.inner (hopfParam p) (mfderiv (𝓡 3) (𝓡 3) hopfParam p v)
        (mfderiv (𝓡 3) (𝓡 3) hopfParam p w) =
      connectionInner (.round (1 / 2)) .hopf p v w := by
  unfold sphericalModelMetric
  rw [roundMetric_inner, dIncl_mfderiv_hopfParam, dIncl_mfderiv_hopfParam]
  exact inner_fderiv_hopfAmbient p v w

theorem hopfParam_periodic (p q : ModelCoordinates) (h0 : q 0 = p 0) (h1 : q 1 = p 1)
    (h2 : q 2 = p 2 + 2 * Real.pi) : hopfParam q = hopfParam p := by
  apply Subtype.ext
  simp only [hopfParam, hopfAmbient, hopfFrame, stereoDenom, h0, h1, h2, Real.cos_add_two_pi,
    Real.sin_add_two_pi]


def hopfAngleCoord (a : ℝ) (u : EuclideanSpace ℝ (Fin 4)) : ℂ :=
  ((u 0 * Real.cos a + u 1 * Real.sin a : ℝ) : ℂ) +
    ((u 1 * Real.cos a - u 0 * Real.sin a : ℝ) : ℂ) * Complex.I

@[simp] theorem hopfAngleCoord_re (a : ℝ) (u : EuclideanSpace ℝ (Fin 4)) :
    (hopfAngleCoord a u).re = u 0 * Real.cos a + u 1 * Real.sin a := by
  simp [hopfAngleCoord, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

@[simp] theorem hopfAngleCoord_im (a : ℝ) (u : EuclideanSpace ℝ (Fin 4)) :
    (hopfAngleCoord a u).im = u 1 * Real.cos a - u 0 * Real.sin a := by
  simp [hopfAngleCoord, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem contDiff_hopfAngleCoord (a : ℝ) : ContDiff ℝ ∞ (hopfAngleCoord a) := by
  have hc (j : Fin 4) : ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) => u j) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) j).contDiff
  have h1 : ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) =>
      u 0 * Real.cos a + u 1 * Real.sin a) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) =>
      u 1 * Real.cos a - u 0 * Real.sin a) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp h1).add
    ((Complex.ofRealCLM.contDiff.comp h2).mul contDiff_const)

theorem normSq_hopfAngleCoord (a : ℝ) (u : EuclideanSpace ℝ (Fin 4)) :
    Complex.normSq (hopfAngleCoord a u) = u 0 ^ 2 + u 1 ^ 2 := by
  rw [Complex.normSq_apply, hopfAngleCoord_re, hopfAngleCoord_im]
  linear_combination (u 0 ^ 2 + u 1 ^ 2) * Real.sin_sq_add_cos_sq a

theorem contDiffAt_arg {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ Complex.arg z := by
  have hlog := (Complex.contDiffAt_log hz (n := ∞)).restrict_scalars ℝ
  have h := Complex.imCLM.contDiff.contDiffAt.comp z hlog
  have hfun : (Complex.imCLM ∘ Complex.log) = Complex.arg := by
    funext w
    exact Complex.log_im w
  rwa [hfun] at h

def hopfChartAmbient (a : ℝ) (u : EuclideanSpace ℝ (Fin 4)) : ModelCoordinates :=
  !₂[(u 2 * u 0 + u 3 * u 1) / (u 0 ^ 2 + u 1 ^ 2),
    (u 3 * u 0 - u 2 * u 1) / (u 0 ^ 2 + u 1 ^ 2), a + Complex.arg (hopfAngleCoord a u)]

theorem contDiffAt_hopfChartAmbient (a : ℝ) {u : EuclideanSpace ℝ (Fin 4)}
    (hu : hopfAngleCoord a u ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ (hopfChartAmbient a) u := by
  have hc (j : Fin 4) : ContDiff ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) => u j) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) j).contDiff
  have hn : u 0 ^ 2 + u 1 ^ 2 ≠ 0 := by
    rw [← normSq_hopfAngleCoord a u]
    exact (Complex.normSq_pos.2 (Complex.slitPlane_ne_zero hu)).ne'
  have hden : ContDiffAt ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) => u 0 ^ 2 + u 1 ^ 2) u :=
    by fun_prop
  refine contDiffAt_euclidean.2 fun i => ?_
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) =>
      (u 2 * u 0 + u 3 * u 1) / (u 0 ^ 2 + u 1 ^ 2)) u
    exact ContDiffAt.div (by fun_prop) hden hn
  · change ContDiffAt ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) =>
      (u 3 * u 0 - u 2 * u 1) / (u 0 ^ 2 + u 1 ^ 2)) u
    exact ContDiffAt.div (by fun_prop) hden hn
  · change ContDiffAt ℝ ∞ (fun u : EuclideanSpace ℝ (Fin 4) =>
      a + Complex.arg (hopfAngleCoord a u)) u
    exact contDiffAt_const.add
      ((contDiffAt_arg hu).comp u (contDiff_hopfAngleCoord a).contDiffAt)

theorem hopfAngleCoord_hopfAmbient (a : ℝ) (q : ModelCoordinates) :
    hopfAngleCoord a (hopfAmbient q) = ((Real.sqrt (stereoDenom q))⁻¹ : ℝ) *
      (((Real.cos (q 2 - a) : ℝ) : ℂ) + ((Real.sin (q 2 - a) : ℝ) : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp only [hopfAngleCoord_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, Complex.mul_im]
    simp [hopfAmbient, hopfFrame, Real.cos_sub]
    ring
  · simp only [hopfAngleCoord_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, Complex.mul_im]
    simp [hopfAmbient, hopfFrame, Real.sin_sub]
    ring

theorem hopfChartAmbient_hopfAmbient (a : ℝ) (q : ModelCoordinates) (h1 : a - Real.pi < q 2)
    (h2 : q 2 < a + Real.pi) : hopfChartAmbient a (hopfAmbient q) = q := by
  have hD := stereoDenom_pos q
  have hρ : 0 < Real.sqrt (stereoDenom q) := Real.sqrt_pos.2 hD
  have hζ := hopfAngleCoord_hopfAmbient a q
  have harg : Complex.arg (hopfAngleCoord a (hopfAmbient q)) = q 2 - a := by
    rw [hζ, Complex.arg_real_mul _ (inv_pos.2 hρ), Complex.ofReal_cos, Complex.ofReal_sin,
      Complex.arg_cos_add_sin_mul_I]
    constructor <;> linarith
  ext i
  fin_cases i
  · change (hopfAmbient q 2 * hopfAmbient q 0 + hopfAmbient q 3 * hopfAmbient q 1) /
      (hopfAmbient q 0 ^ 2 + hopfAmbient q 1 ^ 2) = q 0
    simp [hopfAmbient, hopfFrame]
    field_simp
    ring
  · change (hopfAmbient q 3 * hopfAmbient q 0 - hopfAmbient q 2 * hopfAmbient q 1) /
      (hopfAmbient q 0 ^ 2 + hopfAmbient q 1 ^ 2) = q 1
    simp [hopfAmbient, hopfFrame]
    field_simp
    ring
  · change a + Complex.arg (hopfAngleCoord a (hopfAmbient q)) = q 2
    rw [harg]
    ring

theorem hopfAmbient_hopfChartAmbient (a : ℝ) (u : EuclideanSpace ℝ (Fin 4))
    (hu : hopfAngleCoord a u ∈ Complex.slitPlane)
    (hs : u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 = 1) :
    hopfAmbient (hopfChartAmbient a u) = u := by
  have hn : 0 < u 0 ^ 2 + u 1 ^ 2 := by
    rw [← normSq_hopfAngleCoord a u]
    exact Complex.normSq_pos.2 (Complex.slitPlane_ne_zero hu)
  have hr : 0 < Real.sqrt (u 0 ^ 2 + u 1 ^ 2) := Real.sqrt_pos.2 hn
  have hnorm : ‖hopfAngleCoord a u‖ = Real.sqrt (u 0 ^ 2 + u 1 ^ 2) := by
    rw [Complex.norm_def, normSq_hopfAngleCoord]
  have hsc := Real.sin_sq_add_cos_sq a
  have hcos : Real.cos (a + Complex.arg (hopfAngleCoord a u)) =
      u 0 / Real.sqrt (u 0 ^ 2 + u 1 ^ 2) := by
    rw [Real.cos_add, Complex.cos_arg (Complex.slitPlane_ne_zero hu), Complex.sin_arg, hnorm,
      hopfAngleCoord_re, hopfAngleCoord_im]
    field_simp
    linear_combination u 0 * hsc
  have hsin : Real.sin (a + Complex.arg (hopfAngleCoord a u)) =
      u 1 / Real.sqrt (u 0 ^ 2 + u 1 ^ 2) := by
    rw [Real.sin_add, Complex.cos_arg (Complex.slitPlane_ne_zero hu), Complex.sin_arg, hnorm,
      hopfAngleCoord_re, hopfAngleCoord_im]
    field_simp
    linear_combination u 1 * hsc
  have hD : stereoDenom (hopfChartAmbient a u) = (u 0 ^ 2 + u 1 ^ 2)⁻¹ := by
    simp only [stereoDenom, hopfChartAmbient]
    simp
    field_simp
    linear_combination (u 0 ^ 2 + u 1 ^ 2) * hs
  have hρ : (Real.sqrt (stereoDenom (hopfChartAmbient a u)))⁻¹ =
      Real.sqrt (u 0 ^ 2 + u 1 ^ 2) := by
    rw [hD, Real.sqrt_inv, inv_inv]
  have hsq : Real.sqrt (u 0 ^ 2 + u 1 ^ 2) ^ 2 = u 0 ^ 2 + u 1 ^ 2 := Real.sq_sqrt hn.le
  ext i
  fin_cases i
  · change (Real.sqrt (stereoDenom (hopfChartAmbient a u)))⁻¹ *
      Real.cos (a + Complex.arg (hopfAngleCoord a u)) = u 0
    rw [hρ, hcos]
    field_simp
  · change (Real.sqrt (stereoDenom (hopfChartAmbient a u)))⁻¹ *
      Real.sin (a + Complex.arg (hopfAngleCoord a u)) = u 1
    rw [hρ, hsin]
    field_simp
  · change (Real.sqrt (stereoDenom (hopfChartAmbient a u)))⁻¹ *
      ((u 2 * u 0 + u 3 * u 1) / (u 0 ^ 2 + u 1 ^ 2) *
          Real.cos (a + Complex.arg (hopfAngleCoord a u)) -
        (u 3 * u 0 - u 2 * u 1) / (u 0 ^ 2 + u 1 ^ 2) *
          Real.sin (a + Complex.arg (hopfAngleCoord a u))) = u 2
    rw [hρ, hcos, hsin]
    field_simp
    ring
  · change (Real.sqrt (stereoDenom (hopfChartAmbient a u)))⁻¹ *
      ((u 2 * u 0 + u 3 * u 1) / (u 0 ^ 2 + u 1 ^ 2) *
          Real.sin (a + Complex.arg (hopfAngleCoord a u)) +
        (u 3 * u 0 - u 2 * u 1) / (u 0 ^ 2 + u 1 ^ 2) *
          Real.cos (a + Complex.arg (hopfAngleCoord a u))) = u 3
    rw [hρ, hcos, hsin]
    field_simp
    ring

theorem hopfAngleCoord_hopfAmbient_mem (a : ℝ) (q : ModelCoordinates) (h1 : a - Real.pi < q 2)
    (h2 : q 2 < a + Real.pi) : hopfAngleCoord a (hopfAmbient q) ∈ Complex.slitPlane := by
  have hρ : 0 < (Real.sqrt (stereoDenom q))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (stereoDenom_pos q))
  rw [hopfAngleCoord_hopfAmbient, Complex.mem_slitPlane_iff]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    Complex.add_im, Complex.I_re, Complex.I_im, Complex.mul_im]
  by_cases hθ : Real.sin (q 2 - a) = 0
  · rw [Real.sin_eq_zero_iff_of_lt_of_lt (by linarith) (by linarith)] at hθ
    left
    simp [hθ, hρ]
  · right
    simp [hθ, hρ.ne']

def hopfChart (a : ℝ) : PartialDiffeomorph (𝓡 3) (𝓡 3) RoundThree ModelCoordinates ∞ where
  toFun s := hopfChartAmbient a (s : EuclideanSpace ℝ (Fin 4))
  invFun := hopfParam
  source := {s | hopfAngleCoord a (s : EuclideanSpace ℝ (Fin 4)) ∈ Complex.slitPlane}
  target := {q | a - Real.pi < q 2 ∧ q 2 < a + Real.pi}
  map_source' s hs := by
    have h1 := Complex.neg_pi_lt_arg (hopfAngleCoord a (s : EuclideanSpace ℝ (Fin 4)))
    have h2 := Complex.arg_lt_pi_iff.2 ((Complex.mem_slitPlane_iff.1 hs).imp le_of_lt id)
    change a - Real.pi < a + Complex.arg _ ∧ a + Complex.arg _ < a + Real.pi
    constructor <;> linarith
  map_target' q hq := hopfAngleCoord_hopfAmbient_mem a q hq.1 hq.2
  left_inv' s hs := by
    apply Subtype.ext
    have hn := EuclideanSpace.norm_sq_eq (s : EuclideanSpace ℝ (Fin 4))
    rw [mem_sphere_zero_iff_norm.mp s.2] at hn
    simp only [Fin.sum_univ_four, Real.norm_eq_abs, sq_abs, one_pow] at hn
    exact hopfAmbient_hopfChartAmbient a _ hs (by linarith)
  right_inv' q hq := hopfChartAmbient_hopfAmbient a q hq.1 hq.2
  open_source := Complex.isOpen_slitPlane.preimage
    ((contDiff_hopfAngleCoord a).continuous.comp continuous_subtype_val)
  open_target := by
    have hc : Continuous (fun q : ModelCoordinates => q 2) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 2).continuous
    exact (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  contMDiffOn_toFun := by
    intro s hs
    have hcomp := (contDiffAt_hopfChartAmbient a hs).comp_contMDiffAt
      (f := ((↑) : RoundThree → EuclideanSpace ℝ (Fin 4))) (x := s)
      (contMDiff_coe_sphere (n := 3)).contMDiffAt
    exact hcomp.contMDiffWithinAt
  contMDiffOn_invFun := contMDiff_hopfParam.contMDiffOn

theorem hopfChart_inner (a : ℝ) (y : RoundThree) (hy : y ∈ (hopfChart a).source)
    (v w : TangentSpace (𝓡 3) y) :
    connectionInner (.round (1 / 2)) .hopf (hopfChart a y)
        (mfderiv (𝓡 3) (𝓡 3) (hopfChart a) y v) (mfderiv (𝓡 3) (𝓡 3) (hopfChart a) y w) =
      sphericalModelMetric.inner y v w := by
  have hpt : hopfParam (hopfChart a y) = y := (hopfChart a).left_inv' hy
  have hΘ : MDifferentiableAt (𝓡 3) (𝓡 3) (hopfChart a) y :=
    (hopfChart a).mdifferentiableAt (by decide) hy
  have hC : MDifferentiableAt (𝓡 3) (𝓡 3) hopfParam (hopfChart a y) :=
    contMDiff_hopfParam.contMDiffAt.mdifferentiableAt (by decide)
  have hev : hopfParam ∘ hopfChart a =ᶠ[nhds y] id := by
    filter_upwards [(hopfChart a).open_source.mem_nhds hy] with z hz
    exact (hopfChart a).left_inv' hz
  have hid (u : TangentSpace (𝓡 3) y) :
      mfderiv (𝓡 3) (𝓡 3) hopfParam (hopfChart a y)
        (mfderiv (𝓡 3) (𝓡 3) (hopfChart a) y u) = u := by
    rw [← mfderiv_comp_apply y hC hΘ u, hev.mfderiv_eq, mfderiv_id]
    rfl
  have h := sphericalModelMetric_hopfParam (hopfChart a y)
    (mfderiv (𝓡 3) (𝓡 3) (hopfChart a) y v) (mfderiv (𝓡 3) (𝓡 3) (hopfChart a) y w)
  rw [hid, hid, hpt] at h
  exact h.symm

def diagonalEquiv (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    ModelCoordinates ≃L[ℝ] ModelCoordinates :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun v => !₂[a * v 0, b * v 1, c * v 2]
      invFun := fun v => !₂[a⁻¹ * v 0, b⁻¹ * v 1, c⁻¹ * v 2]
      map_add' := fun v w => by ext i; fin_cases i <;> simp <;> ring
      map_smul' := fun r v => by ext i; fin_cases i <;> simp <;> ring
      left_inv := fun v => by ext i; fin_cases i <;> simp [ha, hb, hc]
      right_inv := fun v => by ext i; fin_cases i <;> simp [ha, hb, hc] }

@[simp] theorem diagonalEquiv_apply (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (v : ModelCoordinates) :
    diagonalEquiv a b c ha hb hc v = !₂[a * v 0, b * v 1, c * v 2] := rfl

def linearChart (L : ModelCoordinates ≃L[ℝ] ModelCoordinates) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) ModelCoordinates ModelCoordinates ∞ where
  toPartialEquiv := L.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := L.contDiff.contMDiff.contMDiffOn
  contMDiffOn_invFun := L.symm.contDiff.contMDiff.contMDiffOn

theorem mfderiv_linearChart (L : ModelCoordinates ≃L[ℝ] ModelCoordinates)
    (p : ModelCoordinates) (v : TangentSpace (𝓡 3) p) :
    mfderiv (𝓡 3) (𝓡 3) (linearChart L) p v = L v := by
  rw [mfderiv_eq_fderiv]
  exact congrArg (fun T : ModelCoordinates →L[ℝ] ModelCoordinates => T v)
    (L : ModelCoordinates →L[ℝ] ModelCoordinates).fderiv

section Atlas

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def CoordinateInnerAtlas (g : SmoothRiemannianMetric I M)
    (q : ModelCoordinates → ModelCoordinates → ModelCoordinates → ℝ) : Prop :=
  ∀ x : M, ∃ e : PartialDiffeomorph (𝓡 3) I ModelCoordinates M ∞,
    x ∈ e.target ∧ ∀ p ∈ e.source, ∀ v w : TangentSpace (𝓡 3) p,
      g.inner (e p) (mfderiv (𝓡 3) I e p v) (mfderiv (𝓡 3) I e p w) = q p v w

def ConnectionAtlas (g : SmoothRiemannianMetric I M) (σ : BaseCoframe) (α : FibreConnection) :
    Prop :=
  CoordinateInnerAtlas g (connectionInner σ α)

theorem inner_trans_of_inner {F G K₁ K₂ N P : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace K₁] [TopologicalSpace K₂] {J : ModelWithCorners ℝ F K₁}
    {L : ModelWithCorners ℝ G K₂} [TopologicalSpace N] [ChartedSpace K₁ N]
    [TopologicalSpace P] [ChartedSpace K₂ P] (g : SmoothRiemannianMetric I M)
    (e : PartialDiffeomorph J I N M ∞) (Θ : PartialDiffeomorph L J P N ∞)
    (q : N → F → F → ℝ) (r : P → G → G → ℝ)
    (he : ∀ y ∈ e.source, ∀ v w : TangentSpace J y,
      g.inner (e y) (mfderiv J I e y v) (mfderiv J I e y w) = q y v w)
    (hΘ : ∀ y ∈ Θ.source, ∀ v w : TangentSpace L y,
      q (Θ y) (mfderiv L J Θ y v) (mfderiv L J Θ y w) = r y v w)
    (y : P) (hy : y ∈ (Θ.trans e).source) (v w : TangentSpace L y) :
    g.inner ((Θ.trans e) y) (mfderiv L I (Θ.trans e) y v) (mfderiv L I (Θ.trans e) y w) =
      r y v w := by
  have hyΘ : y ∈ Θ.source := hy.1
  have hye : Θ y ∈ e.source := hy.2
  have hΘd : MDifferentiableAt L J Θ y := Θ.mdifferentiableAt (by decide) hyΘ
  have hed : MDifferentiableAt J I e (Θ y) := e.mdifferentiableAt (by decide) hye
  have hcomp (u : TangentSpace L y) :
      mfderiv L I (Θ.trans e) y u = mfderiv J I e (Θ y) (mfderiv L J Θ y u) :=
    mfderiv_comp_apply y hed hΘd u
  rw [hcomp, hcomp]
  exact (he (Θ y) hye _ _).trans (hΘ y hyΘ v w)

theorem CoordinateInnerAtlas.of_linearEquiv {g : SmoothRiemannianMetric I M}
    {q r : ModelCoordinates → ModelCoordinates → ModelCoordinates → ℝ}
    (L : ModelCoordinates ≃L[ℝ] ModelCoordinates)
    (hL : ∀ p v w, q (L p) (L v) (L w) = r p v w) (h : CoordinateInnerAtlas g q) :
    CoordinateInnerAtlas g r := by
  intro x
  obtain ⟨e, hx, he⟩ := h x
  refine ⟨(linearChart L).trans e, ⟨hx, Set.mem_univ _⟩, fun p hp v w => ?_⟩
  refine inner_trans_of_inner g e (linearChart L) q r he (fun y _ v w => ?_) p hp v w
  rw [mfderiv_linearChart, mfderiv_linearChart]
  exact hL y v w

theorem ConnectionAtlas.coordinateModelAtlas {g : SmoothRiemannianMetric I M}
    {σ : BaseCoframe} {α : FibreConnection} (h : ConnectionAtlas g σ α) (k : CoordinateModel)
    (hk : ∀ p v, connectionCoframe σ α p v = coordinateCoframe k p v) :
    CoordinateModelAtlas g k := by
  intro x
  obtain ⟨e, hx, he⟩ := h x
  refine ⟨e, hx, fun p hp v w => (he p hp v w).trans ?_⟩
  simp only [connectionInner, coordinateInner]
  rw [hk p v, hk p w]

theorem ConnectionAtlas.modelAtlas_euclidean {g : SmoothRiemannianMetric I M}
    (h : ConnectionAtlas g .flat 0) : ModelAtlas g euclideanModelMetric := by
  intro x
  obtain ⟨e, hx, he⟩ := h x
  exact ⟨e, hx, fun p hp v w => (he p hp v w).trans (connectionInner_euclidean p v w)⟩

theorem ConnectionAtlas.modelAtlas_sphericalProduct {g : SmoothRiemannianMetric I M}
    (h : ConnectionAtlas g (.round 1) 0) : ModelAtlas g sphericalProductModelMetric := by
  intro x
  obtain ⟨e, hx, he⟩ := h x
  refine ⟨stereoCylinderChart.trans e, ⟨hx, Set.mem_univ _⟩, ?_⟩
  intro y hy v w
  exact inner_trans_of_inner g e stereoCylinderChart (connectionInner (.round 1) 0)
    (fun y v w => unitCylinderMetric.inner y v w) he
    (fun y hy v w => stereoCylinderChart_inner y hy v w) y hy v w

theorem ConnectionAtlas.modelAtlas_spherical {g : SmoothRiemannianMetric I M}
    (h : ConnectionAtlas g (.round (1 / 2)) .hopf) : ModelAtlas g sphericalModelMetric := by
  intro x
  obtain ⟨e, hx, he⟩ := h x
  refine ⟨(hopfChart (e.symm x 2)).trans e, ⟨hx, ?_⟩, ?_⟩
  · change e.symm x 2 - Real.pi < e.symm x 2 ∧ e.symm x 2 < e.symm x 2 + Real.pi
    constructor <;> linarith [Real.pi_pos]
  · intro y hy v w
    exact inner_trans_of_inner g e (hopfChart (e.symm x 2))
      (connectionInner (.round (1 / 2)) .hopf) (fun y v w => sphericalModelMetric.inner y v w) he
      (fun y hy v w => hopfChart_inner _ y hy v w) y hy v w

end Atlas

inductive ConnectionModel
  | euclidean | sphericalProduct | hyperbolicProduct | nil | universalSL2 | spherical
  deriving DecidableEq

namespace ConnectionModel

def base : ConnectionModel → BaseCoframe
  | .euclidean => .flat
  | .sphericalProduct => .round 1
  | .hyperbolicProduct => .hyperbolic
  | .nil => .flat
  | .universalSL2 => .hyperbolic
  | .spherical => .round (1 / 2)

def form : ConnectionModel → FibreConnection
  | .nil => .nil
  | .universalSL2 => .universalSL2
  | .spherical => .hopf
  | _ => 0

def baseCurvature : ConnectionModel → ℝ
  | .euclidean => 0
  | .sphericalProduct => 1
  | .hyperbolicProduct => -1
  | .nil => 0
  | .universalSL2 => -1
  | .spherical => 4

def connectionCurvature : ConnectionModel → ℝ
  | .nil => -1
  | .universalSL2 => 1
  | .spherical => 2
  | _ => 0

def thurston : ConnectionModel → ThurstonModel
  | .euclidean => .euclidean
  | .sphericalProduct => .sphericalProduct
  | .hyperbolicProduct => .hyperbolicProduct
  | .nil => .nil
  | .universalSL2 => .universalSL2
  | .spherical => .spherical

theorem gaussCurvature_base (m : ConnectionModel) (x y : ℝ) :
    m.base.gaussCurvature x y = m.baseCurvature := by
  cases m
  · exact BaseCoframe.gaussCurvature_flat x y
  · exact (BaseCoframe.gaussCurvature_round one_ne_zero x y).trans (by norm_num [baseCurvature])
  · exact BaseCoframe.gaussCurvature_hyperbolic x y
  · exact BaseCoframe.gaussCurvature_flat x y
  · exact BaseCoframe.gaussCurvature_hyperbolic x y
  · exact (BaseCoframe.gaussCurvature_round (by norm_num) x y).trans
      (by norm_num [baseCurvature])

theorem hasCurvature_form (m : ConnectionModel) :
    m.form.HasCurvature m.base m.connectionCurvature := by
  cases m
  · exact FibreConnection.hasCurvature_zero _
  · exact FibreConnection.hasCurvature_zero _
  · exact FibreConnection.hasCurvature_zero _
  · exact FibreConnection.hasCurvature_nil
  · exact FibreConnection.hasCurvature_universalSL2
  · exact FibreConnection.hasCurvature_hopf

end ConnectionModel

section Normal

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem ConnectionAtlas.hasThurstonAtlas {g : SmoothRiemannianMetric I M}
    (m : ConnectionModel) (h : ConnectionAtlas g m.base m.form) :
    HasThurstonAtlas g m.thurston := by
  cases m
  · exact h.modelAtlas_euclidean
  · exact h.modelAtlas_sphericalProduct
  · exact h.coordinateModelAtlas _ connectionCoframe_hyperbolicProduct
  · exact h.coordinateModelAtlas _ connectionCoframe_nil
  · exact h.coordinateModelAtlas _ connectionCoframe_universalSL2
  · exact h.modelAtlas_spherical

theorem connectionInner_reflect (m : ConnectionModel) :
    ∃ L : ModelCoordinates ≃L[ℝ] ModelCoordinates, ∀ p v w : ModelCoordinates,
      connectionInner m.base ((-1 : ℝ) • m.form) (L p) (L v) (L w) =
        connectionInner m.base m.form p v w := by
  cases m
  all_goals first
    | exact ⟨ContinuousLinearEquiv.refl ℝ _, fun p v w => by
        simp only [ConnectionModel.form, FibreConnection.smul_zero']; rfl⟩
    | skip
  · refine ⟨diagonalEquiv 1 (-1) 1 one_ne_zero (by norm_num) one_ne_zero, fun p v w => ?_⟩
    simp [connectionInner, connectionCoframe, ConnectionModel.base, ConnectionModel.form,
      BaseCoframe.flat, FibreConnection.nil, Fin.sum_univ_three]
  · refine ⟨diagonalEquiv (-1) 1 1 (by norm_num) one_ne_zero one_ne_zero, fun p v w => ?_⟩
    simp [connectionInner, connectionCoframe, ConnectionModel.base, ConnectionModel.form,
      BaseCoframe.hyperbolic, FibreConnection.universalSL2, Fin.sum_univ_three]
  · refine ⟨diagonalEquiv 1 (-1) 1 one_ne_zero (by norm_num) one_ne_zero, fun p v w => ?_⟩
    simp [connectionInner, connectionCoframe, ConnectionModel.base, ConnectionModel.form,
      BaseCoframe.round, FibreConnection.hopf, Fin.sum_univ_three]
    ring

theorem ConnectionAtlas.reflect {g : SmoothRiemannianMetric I M} (m : ConnectionModel)
    (h : ConnectionAtlas g m.base ((-1 : ℝ) • m.form)) : ConnectionAtlas g m.base m.form := by
  obtain ⟨L, hL⟩ := connectionInner_reflect m
  exact CoordinateInnerAtlas.of_linearEquiv L hL h

def fibreScaledInner (σ : BaseCoframe) (α : FibreConnection) (l : ℝ)
    (p v w : ModelCoordinates) : ℝ :=
  connectionCoframe σ α p v 0 * connectionCoframe σ α p w 0 +
    connectionCoframe σ α p v 1 * connectionCoframe σ α p w 1 +
      l ^ 2 * (connectionCoframe σ α p v 2 * connectionCoframe σ α p w 2)

def FibreScaledAtlas (g : SmoothRiemannianMetric I M) (σ : BaseCoframe) (α : FibreConnection)
    (l : ℝ) : Prop :=
  CoordinateInnerAtlas g (fibreScaledInner σ α l)

theorem fibreScaledInner_diagonal (σ : BaseCoframe) (α : FibreConnection) {l : ℝ} (hl : l ≠ 0)
    (p v w : ModelCoordinates) :
    fibreScaledInner σ α l (diagonalEquiv 1 1 l⁻¹ one_ne_zero one_ne_zero (inv_ne_zero hl) p)
        (diagonalEquiv 1 1 l⁻¹ one_ne_zero one_ne_zero (inv_ne_zero hl) v)
        (diagonalEquiv 1 1 l⁻¹ one_ne_zero one_ne_zero (inv_ne_zero hl) w) =
      connectionInner σ (l • α) p v w := by
  simp [fibreScaledInner, connectionInner, connectionCoframe, Fin.sum_univ_three]
  field_simp

theorem FibreScaledAtlas.connectionAtlas {g : SmoothRiemannianMetric I M} {σ : BaseCoframe}
    {α : FibreConnection} {l : ℝ} (hl : l ≠ 0) (h : FibreScaledAtlas g σ α l) :
    ConnectionAtlas g σ (l • α) :=
  CoordinateInnerAtlas.of_linearEquiv _ (fibreScaledInner_diagonal σ α hl) h

theorem FibreScaledAtlas.hasThurstonAtlas {g : SmoothRiemannianMetric I M}
    (m : ConnectionModel) {c l : ℝ} (hc : l * c = 1 ∨ l * c = -1)
    (h : FibreScaledAtlas g m.base (c • m.form) l) : HasThurstonAtlas g m.thurston := by
  have hl : l ≠ 0 := by
    rintro rfl
    norm_num at hc
  have h' := h.connectionAtlas hl
  rw [FibreConnection.smul_smul'] at h'
  rcases hc with hc | hc <;> rw [hc] at h'
  · rw [FibreConnection.one_smul'] at h'
    exact h'.hasThurstonAtlas m
  · exact (h'.reflect m).hasThurstonAtlas m

end Normal

theorem connectionInner_homothety (σ : BaseCoframe) (α : FibreConnection) {l : ℝ} (hl : l ≠ 0)
    (p v w : ModelCoordinates) :
    connectionInner (l • σ) (l • α) (diagonalEquiv 1 1 l one_ne_zero one_ne_zero hl p)
        (diagonalEquiv 1 1 l one_ne_zero one_ne_zero hl v)
        (diagonalEquiv 1 1 l one_ne_zero one_ne_zero hl w) =
      l ^ 2 * connectionInner σ α p v w := by
  simp [connectionInner, connectionCoframe, Fin.sum_univ_three]
  ring

end GC.Geometry
