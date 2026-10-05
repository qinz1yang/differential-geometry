import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryTransport
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorAtlasMetric
import DifferentialGeometry.Geometry.Geodesic.Naturality.MetricLocality
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarSplittingBCP02Taylor
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.AffineHeightDual
import DifferentialGeometry.Analysis.Calculus.Derivative.Curve
import DifferentialGeometry.Geometry.Collapse.SublevelCore.ScaledMinimizingDirections
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Smoothness

/-!
# BCG02's differential clause: transport between the completion `W°` and the carrier `W` (BCG-7, G2)

Blueprint 207B, BCG02 (`B:8889–8935`): the reference tests live on the completed interior
`(W°, ĝ)` at the normalized metric `R_a⁻²ĝ` (circle/edge/slim `test` fields: the intrinsic geodesic of
`gR = R⁻²ĝ` from `x` with unit initial vector `w` reaching the witness at time `ℓ`), while the boundary
height's Hessian and Taylor certificates (BCUSP-1, review 51 item B4) live on the carrier `(W, g)`.
"Choose `r∂` smaller … so the larger physical balls and all intervening segments stay in
`5 < η_b < 95`. In reference units `‖∇²U_b‖ ≤ 2R_a`. Writing `ℓ = d(x, y)` in those units, Taylor
integration yields `|DU_b(v) − (U_b(y) − U_b(x))/ℓ| ≤ R_aℓ` (BCG02.b)." Since `ĝ = g°` on the open set
`{D > 4}` (`g° = pieceInteriorMetric W g ⊤`, the pull-back of `g` by the inclusion `val` in the interior
atlas), a `ĝ`-geodesic segment inside `{D > 4}` is, through `val`, a `g`-geodesic of `W`; the
differential of `U_b ∘ val` on `W°` is `DU_b ∘ dval`; and `g(dval u, dval u) = ĝ(u, u)` there.

* `pieceInteriorMetric_eq_pullback_BCG7`, `hasGeodesicEquationAt_val_BCG7`: the geodesic equation of
  `g°` on `W°` maps to that of `g` on `W` (the interior-atlas argument of
  `boundaryInteriorAtlas_geodesicEquation`, for the open set `W.pieceInterior ⊤`);
* `hasGeodesicEquationAt_val_of_completion_BCG7`: the same for `ĝ` at points with `D > 4`
  (metric locality of the geodesic equation);
* `mdifferentiableAt_val_BCG7`, `mvfderiv_comp_val_BCG7`, `inner_mfderiv_val_BCG7`,
  `deriv_comp_eq_mvfderiv_BCG7`: chain rule through `val`, `g(dval ·, dval ·) = ĝ` on `{D ≥ 4}`, and
  `(f ∘ γ)'(t) = Df(γ'(t))`;
* `abs_mvfderiv_height_completion_le_BCG7`, `abs_mvfderiv_affineHeight_completion_le_BCG7`: B4's norm
  certificate on `W°`: `|D(η_i ∘ val)(u)| ≤ (1 + 2(ε + w₀))|u|_ĝ`, hence
  `|DU_b(u)| ≤ (1 + 2(ε + w₀))|u|_{R⁻²ĝ}` for `U_b = (η_i ∘ val − a)/R`;
* `cusp_taylor_completion_BCG7`: B4's Taylor certificate (`cusp_taylor_BCUSP1`) for a `ĝ`-geodesic
  segment of `W°` with `ĝ`-speed `≤ R` inside `{D > 4}`, starting at a collar point of height in
  `[2 + 2Rℓ, 98 − 2Rℓ]`;
* `lt_distanceToBoundary_of_consumer_BCG7`: points of the consumer ball `B_ĝ(j, 4Cρ(j))` have `D > 4`
  when `D(j) > 5`, `4Cρ(j) ≤ 1` (T2's consumer-domain clause, `consumer_domain_completion_BDRY5`);
* `radialScaled_geodesic_facts_BCG7`: the intrinsic geodesic of `R⁻²g` with a unit initial vector (the
  geodesic of the `test` fields, rescaled instance stack) is smooth, a geodesic of `g`, starts at `x`
  with velocity `w`, has `g`-speed `R`, and `d(x, Γ t) ≤ R t`;
* `bcg02_taylor_test_BCG7` (consumer): BCG02.b on `W°` along the geodesic of a reference test:
  `|DU_b(w) − (U_b(Γ ℓ) − U_b(x))/ℓ| ≤ Rℓ` when `d(x, j) + Rℓ < 4Cρ(j)` and `x` is a collar point of
  height in `[2 + 2Rℓ, 98 − 2Rℓ]`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Manifold Bundle Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable (W : CompactCarrier.{0}) (g : SmoothRiemannianMetric W.model W.Carrier)

/-- The metric `g°` of the interior `W°` (interior atlas) is the cross pull-back of the restriction
of `g` to the open set `W°` by the inverse of the interior-atlas diffeomorphism. -/
theorem pieceInteriorMetric_eq_pullback_BCG7 :
    pieceInteriorMetric W g ⊤ = Diffeomorph.pullbackMetricCross
      (g.restrictOpen (W.pieceInterior ⊤))
      (Manifold.interiorAtlasDiffeomorph W.model ∞ (M := W.pieceInterior ⊤)).symm := by
  let U := W.pieceInterior ⊤
  let Φ := Manifold.interiorAtlasDiffeomorph W.model ∞ (M := U)
  ext x v w
  have hΦ := (Φ.symm.contMDiff.contMDiffAt (x := x)).mdifferentiableAt (by simp)
  have hval : MDifferentiableAt W.model W.model (Subtype.val : U → W.Carrier) (Φ.symm x) :=
    (DifferentialGeometry.hasMFDerivAt_subtype_val (I := W.model) U (Φ.symm x)).mdifferentiableAt
  have hcomp := mfderiv_comp x hval hΦ
  have hfun : (Subtype.val : U → W.Carrier) ∘ (Φ.symm : U → U) = Subtype.val := by
    funext z
    rfl
  rw [hfun] at hcomp
  rw [DifferentialGeometry.mfderiv_subtype_val (I := W.model) U (Φ.symm x)] at hcomp
  have hcompV := congrArg (fun B : TangentSpace (𝓡 3) x →L[ℝ]
    TangentSpace W.model (x : W.Carrier) => B v) hcomp
  have hcompW := congrArg (fun B : TangentSpace (𝓡 3) x →L[ℝ]
    TangentSpace W.model (x : W.Carrier) => B w) hcomp
  change mfderiv (𝓡 3) W.model (Subtype.val : U → W.Carrier) x v =
    mfderiv (𝓡 3) W.model Φ.symm x v at hcompV
  change mfderiv (𝓡 3) W.model (Subtype.val : U → W.Carrier) x w =
    mfderiv (𝓡 3) W.model Φ.symm x w at hcompW
  have hpull := Diffeomorph.pullbackMetricCross_inner (g.restrictOpen U) Φ.symm x v w
  rw [SmoothRiemannianMetric.restrictOpen_inner] at hpull
  rw [pieceInteriorMetric_inner W g ⊤ x v w, hpull]
  change g.inner (x : W.Carrier) (mfderiv (𝓡 3) W.model Subtype.val x v)
    (mfderiv (𝓡 3) W.model Subtype.val x w) = g.inner (x : W.Carrier)
      (mfderiv (𝓡 3) W.model Φ.symm x v) (mfderiv (𝓡 3) W.model Φ.symm x w)
  rw [hcompV, hcompW]

/-- **Geodesics of `g°` are geodesics of `g`.** A curve of `W°`, smooth at `t`, satisfying the geodesic
equation of `g° = pieceInteriorMetric W g ⊤` at `t` maps by `val` to a curve satisfying the geodesic
equation of `g` on the carrier `W` at `t`. -/
theorem hasGeodesicEquationAt_val_BCG7 (γ : ℝ → W.pieceInterior ⊤) (t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ γ t)
    (hgeo : HasGeodesicEquationAt (pieceInteriorMetric W g ⊤) γ t) :
    HasGeodesicEquationAt g (fun s => (γ s).val) t := by
  let U := W.pieceInterior ⊤
  let Φ := Manifold.interiorAtlasDiffeomorph W.model ∞ (M := U)
  rw [pieceInteriorMetric_eq_pullback_BCG7] at hgeo
  have hmapped := geoEq_mapCrossAt (g.restrictOpen U) Φ.symm γ t hγ hgeo
  change HasGeodesicEquationAt (g.restrictOpen U) γ t at hmapped
  exact (VolumeComparison.boundaryOpen_geodesicEquation_iff (g := g) (U := U)
    (γ := γ) (t := t) (W.model.isInteriorPoint_iff_isInteriorPoint_val.mp
      BoundarylessManifold.isInteriorPoint)).mp hmapped

variable (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤))

/-- **Geodesics of the completion `ĝ` in `{D > 4}` are geodesics of `g`** (`ĝ = g°` on `{D ≥ 4}`). -/
theorem hasGeodesicEquationAt_val_of_completion_BCG7
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (γ : ℝ → W.pieceInterior ⊤) (t : ℝ) (hγ : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ γ t)
    (hgeo : HasGeodesicEquationAt ĝ γ t)
    (hD : ENNReal.ofReal 4 < distanceToBoundary W g (γ t)) :
    HasGeodesicEquationAt g (fun s => (γ s).val) t := by
  have hO : IsOpen {x : W.pieceInterior ⊤ | ENNReal.ofReal 4 < distanceToBoundary W g x} :=
    (isOpen_lt_distanceToBoundary_BDRY1 W g 4).preimage continuous_subtype_val
  have hev : ∀ᶠ x in 𝓝 (γ t), ∀ v w : TangentSpace (𝓡 3) x,
      ĝ.inner x v w = (pieceInteriorMetric W g ⊤).inner x v w := by
    filter_upwards [hO.mem_nhds hD] with x hx v w
    rw [heq x (le_of_lt hx)]
  exact hasGeodesicEquationAt_val_BCG7 W g γ t hγ
    ((hasGeodesicEquationAt_iff_of_metric_eventuallyEq ĝ (pieceInteriorMetric W g ⊤) hev).mp hgeo)

omit g in
/-- The inclusion `val : W° → W` (interior atlas) is differentiable. -/
theorem mdifferentiableAt_val_BCG7 (x : W.pieceInterior ⊤) :
    MDifferentiableAt (𝓡 3) W.model (Subtype.val : W.pieceInterior ⊤ → W.Carrier) x :=
  ((isLocalDiffeomorph_pieceInterior_val W ⊤).contMDiff x).mdifferentiableAt (by simp)

omit g in
/-- **Chain rule through `val`**: `D(f ∘ val)(u) = Df(dval u)`. -/
theorem mvfderiv_comp_val_BCG7 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : W.Carrier → F) (x : W.pieceInterior ⊤) (hf : MDifferentiableAt W.model 𝓘(ℝ, F) f x)
    (u : TangentSpace (𝓡 3) x) :
    mvfderiv (𝓡 3) (fun y : W.pieceInterior ⊤ => f y) x u =
      mvfderiv W.model f x (mfderiv (𝓡 3) W.model Subtype.val x u) := by
  have hcomp := mfderiv_comp x hf (mdifferentiableAt_val_BCG7 W x)
  change (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap
      (mfderiv (𝓡 3) 𝓘(ℝ, F) (f ∘ Subtype.val) x u) =
    (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap
      (mfderiv W.model 𝓘(ℝ, F) f x (mfderiv (𝓡 3) W.model Subtype.val x u))
  rw [hcomp]
  rfl

/-- On `{D ≥ 4}`: `g(dval u, dval w) = ĝ(u, w)`. -/
theorem inner_mfderiv_val_BCG7
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (x : W.pieceInterior ⊤) (hx : ENNReal.ofReal 4 ≤ distanceToBoundary W g x)
    (u w : TangentSpace (𝓡 3) x) :
    g.inner x (mfderiv (𝓡 3) W.model Subtype.val x u) (mfderiv (𝓡 3) W.model Subtype.val x w) =
      ĝ.inner x u w := by
  rw [heq x hx, pieceInteriorMetric_inner W g ⊤ x u w]

/-- `(f ∘ γ)'(t) = Df_{γ(t)}(γ'(t))` for a real function `f` and a curve `γ`. -/
theorem deriv_comp_eq_mvfderiv_BCG7 {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    (f : M → ℝ) (γ : ℝ → M) (t : ℝ) (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f (γ t))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    deriv (fun s => f (γ s)) t = mvfderiv I f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) :=
  (DifferentialGeometry.Analysis.Calculus.hasDerivAt_comp_mfderiv_along I f γ t hf hγ).deriv

variable {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- **B4's norm certificate on `W°`**: at a point `x` of `W°` with `D(x) ≥ 4` which is a band point
`e_i p` (`2 ≤ z(p) ≤ 98`), `|D(η_i ∘ val)(u)| ≤ (1 + 2(ε + w₀))|u|_ĝ`. -/
theorem abs_mvfderiv_height_completion_le_BCG7 (P : BoundaryCollarPacket W g K A w₀ ε)
    (hK : 1 ≤ K) (hε : ε ≤ 1 / 1000)
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (i : Fin P.cusp.count) {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (h2 : 2 ≤ p.2.val 0)
    (h98 : p.2.val 0 ≤ 98) (x : W.pieceInterior ⊤) (hx : x.val = (P.cusp.collar i).toFun p)
    (hD : ENNReal.ofReal 4 ≤ distanceToBoundary W g x) (u : TangentSpace (𝓡 3) x) :
    |mvfderiv (𝓡 3) (fun y : W.pieceInterior ⊤ => P.height i y) x u| ≤
      (1 + 2 * (ε + w₀)) * Real.sqrt (ĝ.inner x u u) := by
  have h := (P.cusp_norm_hessian_BCUSP1 hK hε i hp h2 h98).2.1
  rw [← hx] at h
  have hη : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (P.height i) x :=
    ((P.contMDiff_height i) _).mdifferentiableAt (by simp)
  rw [mvfderiv_comp_val_BCG7 W (P.height i) x hη u, ← inner_mfderiv_val_BCG7 W g ĝ heq x hD]
  exact h _

/-- **B4's norm certificate in the reference normalization**: under the hypotheses of
`abs_mvfderiv_height_completion_le_BCG7`, `U_b = (η_i ∘ val − a)/R` has
`|DU_b(u)| ≤ (1 + 2(ε + w₀))|u|_{R⁻²ĝ}`. -/
theorem abs_mvfderiv_affineHeight_completion_le_BCG7 (P : BoundaryCollarPacket W g K A w₀ ε)
    (hK : 1 ≤ K) (hε : ε ≤ 1 / 1000)
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (i : Fin P.cusp.count) {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (h2 : 2 ≤ p.2.val 0)
    (h98 : p.2.val 0 ≤ 98) (x : W.pieceInterior ⊤) (hx : x.val = (P.cusp.collar i).toFun p)
    (hD : ENNReal.ofReal 4 ≤ distanceToBoundary W g x) (a : ℝ) {R : ℝ} (hR : 0 < R)
    (u : TangentSpace (𝓡 3) x) :
    |mvfderiv (𝓡 3) (fun y : W.pieceInterior ⊤ => (P.height i y - a) / R) x u| ≤
      (1 + 2 * (ε + w₀)) *
        Real.sqrt ((scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) ĝ).inner x u u) := by
  have hη : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (P.height i) x :=
    ((P.contMDiff_height i) _).mdifferentiableAt (by simp)
  have hηv : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) (fun y : W.pieceInterior ⊤ => P.height i y) x :=
    hη.comp x (mdifferentiableAt_val_BCG7 W x)
  exact abs_mvfderiv_affineHeight_le_BCG7 ĝ hηv a hR
    (abs_mvfderiv_height_completion_le_BCG7 W g ĝ P hK hε heq i hp h2 h98 x hx hD) u

/-- **B4's Taylor certificate on `W°` (BCG02.b).** A `ĝ`-geodesic segment `c` of `W°` on `[0, ℓ]`
inside `{D > 4}` with `ĝ`-speed `≤ R`, starting at `x = c 0 = e_i p` with velocity `v` and
`2 + 2Rℓ ≤ z(p) ≤ 98 − 2Rℓ`: `|DU(v) − (U(c ℓ) − U(x))/ℓ| ≤ Rℓ` for `U = (η_i ∘ val − a)/R`. -/
theorem cusp_taylor_completion_BCG7 (P : BoundaryCollarPacket W g K A w₀ ε) (hK : 1 ≤ K)
    (hε : ε ≤ 1 / 1000)
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (i : Fin P.cusp.count) {R a : ℝ} (hR : 0 < R) (c : ℝ → W.pieceInterior ⊤) (ℓ : ℝ)
    (hℓ : 0 < ℓ) (hc : ∀ t ∈ Icc 0 ℓ, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 3) ∞ c t)
    (hgeo : ∀ t ∈ Icc 0 ℓ, HasGeodesicEquationAt ĝ c t)
    (hD : ∀ t ∈ Icc 0 ℓ, ENNReal.ofReal 4 < distanceToBoundary W g (c t))
    (hspeed : ∀ t ∈ Icc 0 ℓ,
      ĝ.inner (c t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c t 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c t 1) ≤ R ^ 2)
    (x : W.pieceInterior ⊤) (hx0 : c 0 = x) (v : TangentSpace (𝓡 3) x)
    (hv : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c 0 1 = v)
    {p : CuspHalfSpace} (hp : (P.cusp.collar i).toFun p = x.val)
    (h2 : 2 + 2 * R * ℓ ≤ p.2.val 0) (h98 : p.2.val 0 + 2 * R * ℓ ≤ 98) :
    |mvfderiv (𝓡 3) (fun y : W.pieceInterior ⊤ => (P.height i y - a) / R) x v -
      ((P.height i (c ℓ) - a) / R - (P.height i x - a) / R) / ℓ| ≤ R * ℓ := by
  subst hx0
  subst hv
  have hIcc : ∀ t ∈ Icc (0 : ℝ) (0 + ℓ), t ∈ Icc 0 ℓ := fun t ht => by rwa [zero_add] at ht
  have hvalc : ContMDiff (𝓡 3) W.model ∞ (Subtype.val : W.pieceInterior ⊤ → W.Carrier) :=
    (isLocalDiffeomorph_pieceInterior_val W ⊤).contMDiff
  have hc' : ∀ t ∈ Icc (0 : ℝ) (0 + ℓ),
      ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 (fun s => (c s).val) t := fun t ht =>
    ((hvalc (c t)).comp t (hc t (hIcc t ht))).of_le (by simp)
  have hgeo' : ∀ t ∈ Icc (0 : ℝ) (0 + ℓ), HasGeodesicEquationAt g (fun s => (c s).val) t :=
    fun t ht => hasGeodesicEquationAt_val_of_completion_BCG7 W g ĝ heq c t (hc t (hIcc t ht))
      (hgeo t (hIcc t ht)) (hD t (hIcc t ht))
  have hvel : ∀ t ∈ Icc (0 : ℝ) ℓ,
      mfderiv 𝓘(ℝ, ℝ) W.model (fun s => (c s).val) t ((NormedSpace.fromTangentSpace t).symm 1) =
        mfderiv (𝓡 3) W.model Subtype.val (c t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) c t 1) := by
    intro t ht
    have hcd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 3) c t := (hc t ht).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp t (mdifferentiableAt_val_BCG7 W (c t)) hcd
    change mfderiv 𝓘(ℝ, ℝ) W.model (Subtype.val ∘ c) t 1 = _
    rw [hcomp]
    rfl
  have hspeed' : ∀ t ∈ Icc (0 : ℝ) (0 + ℓ), g.inner ((fun s => (c s).val) t)
      (mfderiv 𝓘(ℝ, ℝ) W.model (fun s => (c s).val) t ((NormedSpace.fromTangentSpace t).symm 1))
      (mfderiv 𝓘(ℝ, ℝ) W.model (fun s => (c s).val) t ((NormedSpace.fromTangentSpace t).symm 1)) ≤
        R ^ 2 := by
    intro t ht
    have ht' := hIcc t ht
    rw [hvel t ht']
    change g.inner (c t).val _ _ ≤ R ^ 2
    rw [inner_mfderiv_val_BCG7 W g ĝ heq (c t) (le_of_lt (hD t ht'))]
    exact hspeed t ht'
  obtain ⟨-, htay⟩ := P.cusp_taylor_BCUSP1 hK hε i (a := a) hR (fun s => (c s).val) 0 ℓ hℓ hc'
    hgeo' hspeed' hp h2 h98
  have h0 : (0 : ℝ) ∈ Icc 0 ℓ := ⟨le_rfl, hℓ.le⟩
  have hU : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ)
      (fun y : W.pieceInterior ⊤ => (P.height i y - a) / R) (c 0) := by
    have hη : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (P.height i) (c 0) :=
      ((P.contMDiff_height i) _).mdifferentiableAt (by simp)
    have hηv : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ)
        (fun y : W.pieceInterior ⊤ => P.height i y) (c 0) :=
      hη.comp (c 0) (mdifferentiableAt_val_BCG7 W (c 0))
    have hφ : DifferentiableAt ℝ (fun t : ℝ => (t - a) / R) (P.height i (c 0)) :=
      (differentiableAt_id.sub_const a).div_const R
    exact DifferentiableAt.comp_mdifferentiableAt (f := fun y : W.pieceInterior ⊤ => P.height i y)
      hφ hηv
  have hderiv := deriv_comp_eq_mvfderiv_BCG7 (fun y : W.pieceInterior ⊤ => (P.height i y - a) / R)
    c 0 hU ((hc 0 h0).mdifferentiableAt (by simp))
  rw [← hderiv]
  rw [zero_add] at htay
  exact htay

/-- **Test domains stay in `{D > 4}`**: with T2's consumer-domain clause (BCP04.a, `32C ≤ n`), every
point of `B_ĝ(j, 4Cρ(j))` has `D > 4` when `D(j) > 5` and `4Cρ(j) ≤ 1`. -/
theorem lt_distanceToBoundary_of_consumer_BCG7 [ConnectedSpace W.Carrier]
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n C : ℝ} (hC : 0 ≤ C)
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    (hn : 32 * C ≤ n) :
    letI := inducedMetricSpace ĝ
    ∀ j : W.pieceInterior ⊤, ENNReal.ofReal 5 < distanceToBoundary W g j →
      4 * C * ρ j ≤ 1 → ∀ y : W.pieceInterior ⊤, dist y j < 4 * C * ρ j →
        ENNReal.ofReal 4 < distanceToBoundary W g y := by
  intro j hj hCρ y hy
  obtain ⟨himg, -⟩ := consumer_domain_completion_BDRY5 W g ĝ heq ρ hρ hC hbcp hn j hj
  have hyb : y.val ∈ riemannianBallOf g j.val (4 * C * ρ j) := by
    rw [← himg]
    exact ⟨y, hy, rfl⟩
  have hr : 0 ≤ 4 * C * ρ j := by have := hρ j; positivity
  have hp : ENNReal.ofReal (4 * C * ρ j + 4) ≤ distanceToBoundary W g j :=
    le_of_lt (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith)) hj)
  exact riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 W g hr (by norm_num) hp hyb

section Rescaled

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X]

/-- **The geodesic of a reference test.** On a complete carrier with `hmetric`, the intrinsic geodesic
`Γ` of `gR = R⁻²g` (rescaled instance stack, as in the `test` fields) with a `gR`-unit initial vector
`w` at `x` is smooth, satisfies the geodesic equation of `g`, has `Γ 0 = x`, `Γ'(0) = w`, `g`-speed
`R`, and `d(x, Γ t) ≤ R t` for `t ≥ 0`. -/
theorem radialScaled_geodesic_facts_BCG7 (g : SmoothRiemannianMetric 𝓘(ℝ, E3) X)
    (hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) {R : ℝ}
    (hR : 0 < R) (x : X) (w : TangentSpace 𝓘(ℝ, E3) x)
    (hw : (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g).inner x w w = 1)
    (Γ : ℝ → X)
    (hΓ : Γ = (let hMc : CompleteSpace X := ‹CompleteSpace X›
      letI := mX.rescale R⁻¹ (inv_pos.mpr hR)
      letI := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
      letI : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
        radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
      letI : IsRiemannianManifold 𝓘(ℝ, E3) X :=
        radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
      letI : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
      let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
        scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
      have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
      intrinsicGeodesic gR hnR x w)) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) ∞ Γ ∧ (∀ t, HasGeodesicEquationAt g Γ t) ∧ Γ 0 = x ∧
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) Γ 0 1 = w ∧
      (∀ t, g.inner (Γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) Γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) Γ t 1) = R ^ 2) ∧
      ∀ t, 0 ≤ t → dist x (Γ t) ≤ R * t := by
  have hMc : CompleteSpace X := ‹CompleteSpace X›
  let mR := mX.rescale R⁻¹ (inv_pos.mpr hR)
  let _ := radialScaledBundle g R⁻¹ (inv_pos.mpr hR)
  let _ : IsContinuousRiemannianBundle E3 (fun x : X => TangentSpace 𝓘(ℝ, E3) x) :=
    radialScaledContinuous g R⁻¹ (inv_pos.mpr hR)
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) X :=
    radialScaledManifold (m := mX) g hmetric R⁻¹ (inv_pos.mpr hR)
  let _ : CompleteSpace X := (mX.rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
  let gR : SmoothRiemannianMetric 𝓘(ℝ, E3) X :=
    scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) g
  have hnR : IsMetricNorm (I := 𝓘(ℝ, E3)) (M := X) gR := isMetricNorm_of_riemannianBundle gR
  have hΓ' : Γ = intrinsicGeodesic gR hnR x w := hΓ
  rw [hΓ']
  have hRi : 0 < R⁻¹ := inv_pos.mpr hR
  refine ⟨intrinsicGeodesic_contMDiff gR hnR x w, fun t => ?_, intrinsicGeodesic_zero gR hnR x w,
    intrinsicGeodesic_mfderiv_zero gR hnR x w, fun t => ?_, fun t ht => ?_⟩
  · exact (isGeodesic_scaleMetric_iff (R⁻¹ ^ 2) (pow_pos hRi 2)).mp
      (intrinsicGeodesic_isGeodesic gR hnR x w) t
  · have h := intrinsicGeodesic_speedSq_eq gR hnR x w t
    change R⁻¹ ^ 2 * g.inner _ _ _ = R⁻¹ ^ 2 * g.inner x w w at h
    have hw' : R⁻¹ ^ 2 * g.inner x w w = 1 := hw
    rw [hw'] at h
    have hR2 : R ^ 2 * R⁻¹ ^ 2 = 1 := by field_simp
    calc _ = R ^ 2 * (R⁻¹ ^ 2 * g.inner (intrinsicGeodesic gR hnR x w t)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) (intrinsicGeodesic gR hnR x w) t 1)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E3) (intrinsicGeodesic gR hnR x w) t 1)) := by
            rw [← mul_assoc, hR2, one_mul]
      _ = R ^ 2 := by rw [h, mul_one]
  · have h := intrinsicGeodesic_riemannianEDist_le gR hnR x w ht
    rw [intrinsicGeodesic_zero, ← IsRiemannianManifold.out, hw, Real.sqrt_one, one_mul,
      sub_zero, @edist_dist X mR.toPseudoMetricSpace] at h
    have h' := (ENNReal.ofReal_le_ofReal_iff ht).mp h
    rw [MetricSpace.rescale_dist] at h'
    rw [inv_mul_le_iff₀ hR] at h'
    exact h'

end Rescaled

/-- **Consumer: BCG02.b on `W°` along the geodesic of a reference test.** For a `gR`-unit vector `w`
at `x` (`gR = R⁻²ĝ`) and the intrinsic geodesic `Γ` of `gR` from `(x, w)`, if `d(x, j) + Rℓ < 4Cρ(j)`
for a point `j` with `D(j) > 5`, `4Cρ(j) ≤ 1` and `x = e_i p` with `2 + 2Rℓ ≤ z(p) ≤ 98 − 2Rℓ`, then
`|DU(w) − (U(Γ ℓ) − U(x))/ℓ| ≤ Rℓ`, `U = (η_i ∘ val − a)/R`. -/
theorem bcg02_taylor_test_BCG7 [ConnectedSpace W.Carrier] (P : BoundaryCollarPacket W g K A w₀ ε)
    (hK : 1 ≤ K) (hε : ε ≤ 1 / 1000)
    (heq : ∀ x : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g x →
      ĝ.inner x = (pieceInteriorMetric W g ⊤).inner x)
    (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n C : ℝ} (hC : 0 ≤ C)
    (hbcp : ∀ p, 0 < distanceToBoundary W g p →
      n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
        (distanceToBoundary W g p).toReal / ρ p)
    (hn : 32 * C ≤ n) (i : Fin P.cusp.count) {R a : ℝ} (hR : 0 < R) :
    letI := inducedMetricSpace ĝ
    ∀ (_ : CompleteSpace (W.pieceInterior ⊤)) (j : W.pieceInterior ⊤),
      ENNReal.ofReal 5 < distanceToBoundary W g j → 4 * C * ρ j ≤ 1 →
      ∀ (x : W.pieceInterior ⊤) (w : TangentSpace (𝓡 3) x),
      (scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) ĝ).inner x w w = 1 →
      ∀ (Γ : ℝ → W.pieceInterior ⊤), Γ = (let hMc : CompleteSpace (W.pieceInterior ⊤) := ‹_›
        letI := (inducedMetricSpace ĝ).rescale R⁻¹ (inv_pos.mpr hR)
        letI := radialScaledBundle ĝ R⁻¹ (inv_pos.mpr hR)
        letI : IsContinuousRiemannianBundle E3
            (fun x : W.pieceInterior ⊤ => TangentSpace (𝓡 3) x) :=
          radialScaledContinuous ĝ R⁻¹ (inv_pos.mpr hR)
        letI : IsRiemannianManifold (𝓡 3) (W.pieceInterior ⊤) :=
          radialScaledManifold (m := inducedMetricSpace ĝ) ĝ (inducedMetricSpace_hmetric ĝ) R⁻¹
            (inv_pos.mpr hR)
        letI : CompleteSpace (W.pieceInterior ⊤) :=
          ((inducedMetricSpace ĝ).rescale_completeSpace_iff R⁻¹ (inv_pos.mpr hR)).mpr hMc
        let gR : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤) :=
          scaleMetric (R⁻¹ ^ 2) (pow_pos (inv_pos.mpr hR) 2) ĝ
        have hnR : IsMetricNorm (I := 𝓡 3) (M := W.pieceInterior ⊤) gR :=
          isMetricNorm_of_riemannianBundle gR
        intrinsicGeodesic gR hnR x w) →
      ∀ ℓ : ℝ, 0 < ℓ → dist x j + R * ℓ < 4 * C * ρ j →
      ∀ p : CuspHalfSpace, (P.cusp.collar i).toFun p = x.val →
      2 + 2 * R * ℓ ≤ p.2.val 0 → p.2.val 0 + 2 * R * ℓ ≤ 98 →
      |mvfderiv (𝓡 3) (fun y : W.pieceInterior ⊤ => (P.height i y - a) / R) x w -
        ((P.height i (Γ ℓ) - a) / R - (P.height i x - a) / R) / ℓ| ≤ R * ℓ := by
  intro hc j hj hCρ x w hw Γ hΓ ℓ hℓ hdist p hp h2 h98
  let instM : MetricSpace (W.pieceInterior ⊤) := inducedMetricSpace ĝ
  obtain ⟨hsm, hgeo, h0, hvel, hsp, hd⟩ :=
    @radialScaled_geodesic_facts_BCG7 (W.pieceInterior ⊤) instM _ _ hc _ ĝ
      (inducedMetricSpace_hmetric ĝ) R hR x w hw Γ hΓ
  have hD : ∀ t ∈ Icc 0 ℓ, ENNReal.ofReal 4 < distanceToBoundary W g (Γ t) := by
    intro t ht
    refine lt_distanceToBoundary_of_consumer_BCG7 W g ĝ heq ρ hρ hC hbcp hn j hj hCρ (Γ t) ?_
    have h1 := hd t ht.1
    have h2' : R * t ≤ R * ℓ := mul_le_mul_of_nonneg_left ht.2 hR.le
    have h3 := dist_triangle (Γ t) x j
    rw [dist_comm] at h1
    linarith
  exact cusp_taylor_completion_BCG7 W g ĝ P hK hε heq i hR Γ ℓ hℓ (fun t _ => hsm t)
    (fun t _ => hgeo t) hD (fun t _ => le_of_eq (hsp t)) x h0 w hvel hp h2 h98

end DifferentialGeometry.Geometry.Collapse
