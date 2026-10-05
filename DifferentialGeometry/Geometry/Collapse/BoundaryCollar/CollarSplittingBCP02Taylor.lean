import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarSplittingBCP02Contract
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.SupportListsCollar
import DifferentialGeometry.Geometry.Metric.CurveSpeed

/-!
# B4: cusp norm error, Hessian `≤ 2R` and Taylor error `R·ℓ` on the physical height (lane BCUSP-1, G3)

Review 51, item B4; blueprint BCG02's differential check (`B:8922–8935`): "Choose `r∂` smaller, after
these fixed radii, so the larger physical balls and all intervening segments stay in `5 < η_b < 95`.
In reference units `‖∇²U_b‖ ≤ 2R_a`. Writing `ℓ = d(x, y)` in those units, Taylor integration yields
`|DU_b(v) − (U_b(y) − U_b(x))/ℓ| ≤ R_a ℓ` (BCG02.b)"; and the cusp norm error ("their norms are at most
one plus their prescribed small errors").

Units: `U = (η − a)/R`, reference metric `R⁻²g`. Then `dU = R⁻¹dη`, `∇²U = R⁻¹∇²η` (the Levi-Civita
connection of `R⁻²g` is that of `g`), `|u|_{R⁻²g} = R⁻¹|u|_g`; a geodesic of `g` with `g`-speed `≤ R`
has `R⁻²g`-speed `≤ 1`, and its parameter length `ℓ` is its reference length.

* `CuspEmbedding.abs_deriv_sub_chord_le_BCUSP1`: Taylor for ANY parameter length `ℓ > 0` (the delivered
  `CuspEmbedding.bcp02_chord` needs `ℓ ≤ 1 + γ⁻¹`): `|(U ∘ c)'(x₀) − chord| ≤ (3/4) R ℓ`;
* `CuspEmbedding.exists_height_of_geodesic_BCUSP1`: a curve of `g`-speed `≤ R` on `[x₀, x₀ + ℓ]`
  from `e p` stays at heights `|z − z(p)| < s` when `R ℓ < √(1 − δ) s` (first exit);
* `BoundaryCollarPacket.cusp_norm_hessian_BCUSP1`: at a band point of the packet's own height
  `η_i`: `|d(η_i − z)| ≤ 2ε`, `|dη_i| ≤ 1 + 2(ε + w₀)` and, for every `R > 0`,
  `R⁻¹|∇²η_i(u, w)| ≤ 2R · (R⁻¹|u|_g)(R⁻¹|w|_g)` — i.e. `|∇²U| ≤ 2R` in `R⁻²g`;
* `BoundaryCollarPacket.cusp_taylor_BCUSP1` (BCG02.b): a geodesic segment of `g`-speed `≤ R` and
  parameter length `ℓ` starting at a collar point of height in `[2 + 2Rℓ, 98 − 2Rℓ]` stays in the band
  `2 ≤ z ≤ 98` (where the Z contract holds), and the Taylor error of `U = (η_i − a)/R` is `≤ R ℓ`.

Deviation (as in `CuspEmbedding.bcp02_chord`): the Taylor clause is stated for every geodesic segment of
`g` with the speed bound; the blueprint's minimizing segments are among them.
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint GC.MetricGeometry
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Connection
  DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped Manifold ENNReal ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- **Taylor along a geodesic, any length.** For a smooth `η` with the Hessian bound `3/2` on the
band, a geodesic segment `c` of `g` in the band with `|c'|_g ≤ R` and parameter length `ℓ > 0`:
`|(Φ ∘ c)'(x₀) − (Φ(c(x₀+ℓ)) − Φ(c x₀))/ℓ| ≤ (3/4) R ℓ` for `Φ = (η − a)/R`. -/
theorem CuspEmbedding.abs_deriv_sub_chord_le_BCUSP1 (e : CuspEmbedding W g K δ X)
    {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η)
    (hH : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
      ∀ u w : TangentSpace W.model (e.toFun p),
        |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) η
            (e.toFun p) u w| ≤
          3 / 2 * Real.sqrt (g.inner (e.toFun p) u u) * Real.sqrt (g.inner (e.toFun p) w w))
    {R a : ℝ} (hR : 0 < R) (c : ℝ → W.Carrier) (x₀ ℓ : ℝ) (hℓ : 0 < ℓ)
    (hc : ∀ t ∈ Icc x₀ (x₀ + ℓ), ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 c t)
    (hgeo : ∀ t ∈ Icc x₀ (x₀ + ℓ), HasGeodesicEquationAt g c t)
    (hband : ∀ t ∈ Icc x₀ (x₀ + ℓ), ∃ p ∈ cuspDomain, 2 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 98 ∧
      e.toFun p = c t)
    (hspeed : ∀ t ∈ Icc x₀ (x₀ + ℓ), g.inner (c t)
      (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1))
      (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1)) ≤ R ^ 2) :
    |deriv (fun t => (η (c t) - a) / R) x₀ -
      ((η (c (x₀ + ℓ)) - a) / R - (η (c x₀) - a) / R) / ℓ| ≤ 3 / 4 * R * ℓ := by
  have hf : ∀ t ∈ Icc x₀ (x₀ + ℓ), ContDiffAt ℝ 2 (η ∘ c) t := fun t ht =>
    contMDiffAt_iff_contDiffAt.mp (((hη _).of_le (by simp)).comp t (hc t ht))
  have hM : ∀ t ∈ Icc x₀ (x₀ + ℓ), ‖iteratedFDeriv ℝ 2 (η ∘ c) t‖ ≤ 3 / 2 * R ^ 2 := by
    intro t ht
    obtain ⟨p, hp, h2, h98, hpt⟩ := hband t ht
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact e.abs_iteratedDeriv_two_comp_geodesic_le hη (hc t ht) (hgeo t ht) hp (by linarith) hpt
      (hH p hp h2 h98) (hspeed t ht)
  have h := DifferentialGeometry.Analysis.abs_deriv_sub_chord_le hℓ hf hM
  have hderiv : deriv (fun t => (η (c t) - a) / R) x₀ = deriv (η ∘ c) x₀ / R := by
    rw [deriv_div_const, deriv_sub_const]
    rfl
  have hchord : ((η (c (x₀ + ℓ)) - a) / R - (η (c x₀) - a) / R) / ℓ =
      ((η ∘ c) (x₀ + ℓ) - (η ∘ c) x₀) / ℓ / R := by
    simp only [Function.comp]
    field_simp
    ring
  rw [hderiv, hchord, ← sub_div, abs_div, abs_of_pos hR, div_le_iff₀ hR]
  calc |deriv (η ∘ c) x₀ - ((η ∘ c) (x₀ + ℓ) - (η ∘ c) x₀) / ℓ| ≤ 3 / 2 * R ^ 2 / 2 * ℓ := h
    _ = 3 / 4 * R * ℓ * R := by ring

/-- **Segments stay in the band (first exit).** A curve `c`, `C²` at the points of `[x₀, x₀ + ℓ]`
with `g`-speed `≤ R`, starting at the collar point `e p`, stays at collar heights `|z − z(p)| < s`
when `R ℓ < √(1 − δ) s` and `z(p) + s < 100`. -/
theorem CuspEmbedding.exists_height_of_geodesic_BCUSP1 (e : CuspEmbedding W g K δ X) {R : ℝ}
    (hR : 0 ≤ R) (c : ℝ → W.Carrier) (x₀ ℓ : ℝ)
    (hc : ∀ t ∈ Icc x₀ (x₀ + ℓ), ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 c t)
    (hspeed : ∀ t ∈ Icc x₀ (x₀ + ℓ), g.inner (c t)
      (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1))
      (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1)) ≤ R ^ 2)
    {p : CuspHalfSpace} (hp : e.toFun p = c x₀) {s : ℝ} (hs : 0 < s)
    (hps : p.2.val 0 + s < cuspDepth) (hRs : R * ℓ < Real.sqrt (1 - δ) * s) :
    ∀ t ∈ Icc x₀ (x₀ + ℓ), ∃ q ∈ cuspDomain, e.toFun q = c t ∧ |q.2.val 0 - p.2.val 0| < s := by
  intro t ht
  have hsub : Icc x₀ t ⊆ Icc x₀ (x₀ + ℓ) := Icc_subset_Icc le_rfl ht.2
  have hcon : ContMDiffOn 𝓘(ℝ, ℝ) W.model 1 c (Icc x₀ t) := fun τ hτ =>
    ((hc τ (hsub hτ)).of_le (by norm_num)).contMDiffWithinAt
  have hd := riemannianEDistOf_le_of_curve_speed_bound g ht.1 hcon (C := R) (fun τ hτ => by
    have h := hspeed τ (hsub (Ioo_subset_Icc_self hτ))
    calc Real.sqrt _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt h
      _ = R := Real.sqrt_sq hR)
  have hℓ0 : 0 ≤ ℓ := by linarith [ht.1, ht.2]
  have hRt : R * (t - x₀) ≤ R * ℓ := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hR
  refine e.exists_abs_height_sub_lt_of_edist_lt hs hps ?_
  rw [hp]
  refine hd.trans_lt ?_
  rw [← ENNReal.ofReal_mul hR]
  exact (ENNReal.ofReal_lt_ofReal_iff (by nlinarith)).mpr (by linarith)

namespace BoundaryCollarPacket

variable {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- **B4, norm error and Hessian at a band point of the packet's own height** (`1 ≤ K`, tolerance
`ε ≤ 1/1000`, `2 ≤ z(p) ≤ 98`): `|d(η_i − z)(u)| ≤ 2ε|u|_g`, `|dη_i(u)| ≤ (1 + 2(ε + w₀))|u|_g`, and for
every `R > 0`, `R⁻¹|∇²η_i(u, w)| ≤ 2R (R⁻¹|u|_g)(R⁻¹|w|_g)`: with `U = (η_i − a)/R` this is
`|∇²U| ≤ 2R` in the normalization `R⁻²g` (`dU = R⁻¹dη_i`, `∇²U = R⁻¹∇²η_i`). -/
theorem cusp_norm_hessian_BCUSP1 (P : BoundaryCollarPacket W g K A w₀ ε) (hK : 1 ≤ K)
    (hε : ε ≤ 1 / 1000) (i : Fin P.cusp.count) {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (h2 : 2 ≤ p.2.val 0) (h98 : p.2.val 0 ≤ 98) :
    (∀ u : TangentSpace W.model ((P.cusp.collar i).toFun p),
      |mvfderiv W.model (fun y => P.height i y -
          (invFunOn (P.cusp.collar i).toFun cuspDomain y).2.val 0) ((P.cusp.collar i).toFun p) u| ≤
        2 * ε * Real.sqrt (g.inner ((P.cusp.collar i).toFun p) u u)) ∧
    (∀ u : TangentSpace W.model ((P.cusp.collar i).toFun p),
      |mvfderiv W.model (P.height i) ((P.cusp.collar i).toFun p) u| ≤
        (1 + 2 * (ε + w₀)) * Real.sqrt (g.inner ((P.cusp.collar i).toFun p) u u)) ∧
    ∀ (R : ℝ), 0 < R → ∀ u w : TangentSpace W.model ((P.cusp.collar i).toFun p),
      R⁻¹ * |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
          (P.height i) ((P.cusp.collar i).toFun p) u w| ≤
        2 * R * (R⁻¹ * Real.sqrt (g.inner ((P.cusp.collar i).toFun p) u u)) *
          (R⁻¹ * Real.sqrt (g.inner ((P.cusp.collar i).toFun p) w w)) := by
  set e := P.cusp.collar i with he
  have hw : w₀ ≤ 1 / 6408 := P.threshold
  have hδ0 : 0 ≤ w₀ := e.delta_nonneg
  have hεpos : 0 < ε := P.tolerance_pos
  obtain ⟨-, hdiff, -, -, -, hH, -⟩ := e.bcp01_band_of_contract hK hδ0 (by linarith) hεpos hε
    (P.contMDiff_height i) (P.height_contract i) hp h2 h98
  have hs : (1 : ℝ) - w₀ ≤ Real.sqrt (1 - w₀) := by
    have h0 : 0 ≤ 1 - w₀ := by linarith
    have h1 : 1 - w₀ ≤ 1 := by linarith
    calc 1 - w₀ = Real.sqrt ((1 - w₀) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ Real.sqrt (1 - w₀) := Real.sqrt_le_sqrt (by nlinarith)
  have hs0 : 0 < Real.sqrt (1 - w₀) := lt_of_lt_of_le (by linarith) hs
  refine ⟨fun u => ?_, fun u => ?_, fun R hR u w => ?_⟩
  · have h := hdiff u
    have hg := Real.sqrt_nonneg (g.inner (e.toFun p) u u)
    have hinv : (1 - w₀)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    calc _ ≤ ε * (1 - w₀)⁻¹ * Real.sqrt (g.inner (e.toFun p) u u) := h
      _ ≤ 2 * ε * Real.sqrt (g.inner (e.toFun p) u u) := by
          refine mul_le_mul_of_nonneg_right ?_ hg
          nlinarith
  · have hηd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (P.height i) (e.toFun p) :=
      ((P.contMDiff_height i) _).mdifferentiableAt (by simp)
    have hζd : MDifferentiableAt W.model 𝓘(ℝ, ℝ)
        (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) :=
      (e.contMDiffOn_height_invFunOn.contMDiffAt
        (e.isOpen_image_cuspDomain.mem_nhds (mem_image_of_mem _ hp))).mdifferentiableAt
          one_ne_zero
    have hsplit : mvfderiv W.model (P.height i) (e.toFun p) u =
        mvfderiv W.model (fun y => P.height i y - (invFunOn e.toFun cuspDomain y).2.val 0)
          (e.toFun p) u +
        mvfderiv W.model (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) u := by
      rw [mvfderiv_fun_sub hηd hζd, sub_apply]
      ring
    have h1 := e.abs_mvfderiv_sub_height_le (by linarith) (P.contMDiff_height i) hεpos.le hp
      (fun v => (P.height_contract i p hp h2 h98).2.1 v) u
    have h2' := e.abs_mfderiv_height_invFunOn_le (by linarith) hp u
    change |mvfderiv W.model (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) u| ≤
      _ at h2'
    have hg := Real.sqrt_nonneg (g.inner (e.toFun p) u u)
    have hi0 : 0 ≤ (Real.sqrt (1 - w₀))⁻¹ := inv_nonneg.mpr hs0.le
    have hkey : (ε + 1) * (Real.sqrt (1 - w₀))⁻¹ ≤ 1 + 2 * (ε + w₀) := by
      rw [← div_eq_mul_inv, div_le_iff₀ hs0]
      have hmul : (1 + 2 * (ε + w₀)) * (1 - w₀) ≤ (1 + 2 * (ε + w₀)) * Real.sqrt (1 - w₀) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      nlinarith
    rw [hsplit]
    calc _ ≤ |mvfderiv W.model (fun y => P.height i y - (invFunOn e.toFun cuspDomain y).2.val 0)
          (e.toFun p) u| +
          |mvfderiv W.model (fun y => (invFunOn e.toFun cuspDomain y).2.val 0) (e.toFun p) u| :=
          abs_add_le _ _
      _ ≤ (ε + 1) * (Real.sqrt (1 - w₀))⁻¹ * Real.sqrt (g.inner (e.toFun p) u u) := by nlinarith
      _ ≤ (1 + 2 * (ε + w₀)) * Real.sqrt (g.inner (e.toFun p) u u) :=
          mul_le_mul_of_nonneg_right hkey hg
  · have h := hH u w
    have hRi : 0 < R⁻¹ := inv_pos.mpr hR
    have hu := Real.sqrt_nonneg (g.inner (e.toFun p) u u)
    have hw' := Real.sqrt_nonneg (g.inner (e.toFun p) w w)
    have heq : 2 * R * (R⁻¹ * Real.sqrt (g.inner (e.toFun p) u u)) *
        (R⁻¹ * Real.sqrt (g.inner (e.toFun p) w w)) =
        R⁻¹ * (2 * Real.sqrt (g.inner (e.toFun p) u u) * Real.sqrt (g.inner (e.toFun p) w w)) := by
      field_simp
    rw [heq]
    refine mul_le_mul_of_nonneg_left (h.trans ?_) hRi.le
    have := mul_nonneg hu hw'
    nlinarith

/-- **B4, BCG02.b on the packet's own height.** For a geodesic segment `c` of `g` with `g`-speed
`≤ R` and parameter length `ℓ > 0`, starting at the collar point `e_i p` of height in
`[2 + 2Rℓ, 98 − 2Rℓ]` (`1 ≤ K`, tolerance `ε ≤ 1/1000`): the whole segment stays in the band
`2 ≤ z ≤ 98`, and `U = (η_i − a)/R` has Taylor error `|(U ∘ c)'(x₀) − chord| ≤ R ℓ`. -/
theorem cusp_taylor_BCUSP1 (P : BoundaryCollarPacket W g K A w₀ ε) (hK : 1 ≤ K)
    (hε : ε ≤ 1 / 1000) (i : Fin P.cusp.count) {R a : ℝ} (hR : 0 < R) (c : ℝ → W.Carrier)
    (x₀ ℓ : ℝ) (hℓ : 0 < ℓ)
    (hc : ∀ t ∈ Icc x₀ (x₀ + ℓ), ContMDiffAt 𝓘(ℝ, ℝ) W.model 2 c t)
    (hgeo : ∀ t ∈ Icc x₀ (x₀ + ℓ), HasGeodesicEquationAt g c t)
    (hspeed : ∀ t ∈ Icc x₀ (x₀ + ℓ), g.inner (c t)
      (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1))
      (mfderiv 𝓘(ℝ, ℝ) W.model c t ((NormedSpace.fromTangentSpace t).symm 1)) ≤ R ^ 2)
    {p : CuspHalfSpace} (hp : (P.cusp.collar i).toFun p = c x₀)
    (h2 : 2 + 2 * R * ℓ ≤ p.2.val 0) (h98 : p.2.val 0 + 2 * R * ℓ ≤ 98) :
    (∀ t ∈ Icc x₀ (x₀ + ℓ), ∃ q ∈ cuspDomain, (P.cusp.collar i).toFun q = c t ∧
      2 ≤ q.2.val 0 ∧ q.2.val 0 ≤ 98) ∧
    |deriv (fun t => (P.height i (c t) - a) / R) x₀ -
      ((P.height i (c (x₀ + ℓ)) - a) / R - (P.height i (c x₀) - a) / R) / ℓ| ≤ R * ℓ := by
  set e := P.cusp.collar i with he
  have hw : w₀ ≤ 1 / 6408 := P.threshold
  have hδ0 : 0 ≤ w₀ := e.delta_nonneg
  have hRℓ : 0 < R * ℓ := mul_pos hR hℓ
  have hhalf : (1 / 2 : ℝ) < Real.sqrt (1 - w₀) := by
    rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hseg := e.exists_height_of_geodesic_BCUSP1 hR.le c x₀ ℓ hc hspeed hp (s := 2 * R * ℓ)
    (by positivity) (by simp only [cuspDepth]; linarith) (by nlinarith)
  have hband : ∀ t ∈ Icc x₀ (x₀ + ℓ), ∃ q ∈ cuspDomain, 2 ≤ q.2.val 0 ∧ q.2.val 0 ≤ 98 ∧
      e.toFun q = c t := by
    intro t ht
    obtain ⟨q, hq, hqt, hqz⟩ := hseg t ht
    have := abs_lt.mp hqz
    exact ⟨q, hq, by linarith, by linarith, hqt⟩
  refine ⟨fun t ht => ?_, ?_⟩
  · obtain ⟨q, hq, h2q, h98q, hqt⟩ := hband t ht
    exact ⟨q, hq, hqt, h2q, h98q⟩
  · have hH : ∀ q ∈ cuspDomain, 2 ≤ q.2.val 0 → q.2.val 0 ≤ 98 →
        ∀ u w : TangentSpace W.model (e.toFun q),
          |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) (P.height i)
              (e.toFun q) u w| ≤
            3 / 2 * Real.sqrt (g.inner (e.toFun q) u u) * Real.sqrt (g.inner (e.toFun q) w w) :=
      fun q hq h2q h98q => (e.bcp01_band_of_contract hK hδ0 (by linarith) P.tolerance_pos hε
        (P.contMDiff_height i) (P.height_contract i) hq h2q h98q).2.2.2.2.2.1
    have h := e.abs_deriv_sub_chord_le_BCUSP1 (P.contMDiff_height i) hH (a := a) hR c x₀ ℓ hℓ hc
      hgeo hband hspeed
    linarith

end BoundaryCollarPacket

end DifferentialGeometry.Geometry.Collapse
