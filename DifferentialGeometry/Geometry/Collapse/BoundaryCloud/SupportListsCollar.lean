import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCollarPacket
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarOverlap
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightGeometry

/-!
# BCG01 on actual data: the boundary support lists of the LC88 collar blocks

Blueprint 207B, BCG01 (`B:8727–8820`), bound to the actual boundary blocks. The block of
component `b` is BCG.0's `F_b = 𝓑(η_b)` extended by zero off the original collar band, i.e. the
LC88 collar block `BoundaryCollarPacket.block` (F9-C), with `η_b` the packet's smoothed depth
coordinate. Here the boundary data are closed (BCP01, BCP03, BSA05), so the clauses of BCG01
that only involve boundary supports are proved for these blocks:

* `CuspEmbedding.exists_abs_height_sub_lt_of_edist_lt` (first exit, two-sided band form): a point
  within `√(1 - δ) s` of `e p` is a collar point whose height differs from `z(p)` by `< s`.
* `BoundaryCollarPacket.one_le_edist_of_mem_tsupport_block` (separation, from BCP03.b): in the
  nonproduct case, distinct closed boundary supports are at distance `≥ 1` (tolerance `ε ≤ 1/2`).
* `BoundaryCollarPacket.subsingleton_supports_of_edist_lt_one`: at most ONE closed boundary support
  meets a set of diameter `< 1`.
* `BoundaryCollarPacket.band_of_mem_tsupport_of_edist_lt` (first exit): every point within
  `1/250` of the `b`th support lies in `e_b{19 < z < 91}` and in `{19 < η_b < 91}`
  (tolerance `ε ≤ 1/4`).
* `BoundaryCollarPacket.bcg01_reference_domain` (BCG01.b): for a positive `Λ`-Lipschitz scale `ρ`
  that is `< r_∂` on the collar regions `z ≤ 96` (BSA05), every original reference domain
  `D_a = B(p_a, C_a ρ(p_a))` (`C_a ≤ .95L`, `Λ C_a ≤ 1/2`, `r_∂ < 1/(1000L)`) meeting the `b`th
  support has `ρ(p_a) < 2 r_∂` and lies in `{19 < η_b < 91}`; in the nonproduct case no other
  support meets it (`subsingleton_supports_meeting_reference_domain`).
* `BoundaryCollarPacket.norm_mvfderiv_block_le`, `sum_norm_mvfderiv_block_le`: each block has
  `‖dF_b(u)‖ ≤ (1 + 1/200) P |u|_g` (`‖𝓑'‖ ≤ P`, `ε ≤ 1/1000`), and in the nonproduct case the
  SUM over all boundary components obeys the same bound, independent of their number.

Not bound here (the inputs are other rows): the exclusion of zero supports from `D_a` (BCP05,
which needs the BCP04 zero family), the four-family cover on `d ≥ 35` and the edge collar
assertions (LFR38/LFR44 selections with BCP04.a; LPA06), and the interior blocks in the global
`‖DF‖` bound (CGP02).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Bundle Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Analysis
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

section FirstExit

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **First exit, two-sided band form.** A point within `√(1 - δ) s` of the collar point `e p`
(`z(p) + s < 100`) is a collar point `e q` with `|z(q) - z(p)| < s`. -/
theorem CuspEmbedding.exists_abs_height_sub_lt_of_edist_lt (e : CuspEmbedding W g K δ X)
    {p : CuspHalfSpace} {s : ℝ} (hs : 0 < s) (hps : p.2.val 0 + s < cuspDepth) {y : W.Carrier}
    (hy : riemannianEDistOf g (e.toFun p) y < ENNReal.ofReal (Real.sqrt (1 - δ) * s)) :
    ∃ q ∈ cuspDomain, e.toFun q = y ∧ |q.2.val 0 - p.2.val 0| < s := by
  let : RiemannianBundle (fun x : W.Carrier => TangentSpace W.model x) := ⟨g.toRiemannianMetric⟩
  by_contra hcon
  have hy' : y ∉ e.toFun '' {q : CuspHalfSpace | p.2.val 0 - s < q.2.val 0 ∧
      q.2.val 0 < p.2.val 0 + s} := by
    rintro ⟨q, hq, rfl⟩
    exact hcon ⟨q, lt_trans hq.2 hps, rfl, abs_lt.mpr ⟨by linarith [hq.1], by linarith [hq.2]⟩⟩
  change Manifold.riemannianEDist W.model (e.toFun p) y < _ at hy
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hy
  have hy'' : γ 1 ∉ e.toFun '' {q : CuspHalfSpace | p.2.val 0 - s < q.2.val 0 ∧
      q.2.val 0 < p.2.val 0 + s} := by
    rw [hγ1]
    exact hy'
  obtain ⟨q, -, hqside, hq⟩ := e.exists_exit_le_pathELength hγ hps (by linarith) (by linarith)
    hγ0 hy''
  have hqs : |q.2.val 0 - p.2.val 0| = s := by
    rcases hqside with h | h
    · rw [h, show p.2.val 0 - s - p.2.val 0 = -s by ring, abs_neg, abs_of_pos hs]
    · rw [h, show p.2.val 0 + s - p.2.val 0 = s by ring, abs_of_pos hs]
  rw [hqs] at hq
  exact absurd (lt_of_le_of_lt hq hlen) (lt_irrefl _)

end FirstExit

namespace BoundaryCollarPacket

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- A point of the `b`th closed boundary support is a collar point of height in
`[20 - ε, 90 + ε]`. -/
theorem exists_of_mem_tsupport_block (P : BoundaryCollarPacket W g K A w₀ ε)
    {b : Fin P.cusp.count} {x : W.Carrier} (hx : x ∈ tsupport (P.block b)) :
    ∃ p ∈ cuspDomain, (P.cusp.collar b).toFun p = x ∧ 20 - ε ≤ p.2.val 0 ∧
      p.2.val 0 ≤ 90 + ε := by
  obtain ⟨p, hp, rfl⟩ := P.tsupport_block_subset b hx
  have hp98 : p.2.val 0 ≤ 98 := by linarith [hp.2, P.tolerance_le_one]
  exact ⟨p, cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp98, rfl, hp.1, hp.2⟩

/-- **BCG01, separation (BCP03.b).** In the nonproduct case (disjoint enlarged collars), the
closed supports of two boundary blocks are at distance `≥ 1` (tolerance `ε ≤ 1/2`). -/
theorem one_le_edist_of_mem_tsupport_block (P : BoundaryCollarPacket W g K A w₀ ε)
    (hε : ε ≤ 1 / 2) {i j : Fin P.cusp.count}
    (hdisj : Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
      ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    {x y : W.Carrier} (hx : x ∈ tsupport (P.block i)) (hy : y ∈ tsupport (P.block j)) :
    ENNReal.ofReal 1 ≤ riemannianEDistOf g x y := by
  obtain ⟨p, -, rfl, -, hp⟩ := P.exists_of_mem_tsupport_block hx
  obtain ⟨q, -, rfl, -, hq⟩ := P.exists_of_mem_tsupport_block hy
  exact P.cusp.bcp03b_heights (by linarith [P.threshold]) hdisj
    ⟨p, show p.2.val 0 ≤ 181 / 2 by linarith, rfl⟩ ⟨q, show q.2.val 0 < 92 by linarith, rfl⟩

/-- **BCG01, one support per small set.** In the nonproduct case, at most one closed boundary
support meets a set of diameter `< 1`. -/
theorem subsingleton_supports_of_edist_lt_one (P : BoundaryCollarPacket W g K A w₀ ε)
    (hε : ε ≤ 1 / 2)
    (hdisj : ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    {D : Set W.Carrier} (hD : ∀ x ∈ D, ∀ y ∈ D, riemannianEDistOf g x y < ENNReal.ofReal 1) :
    {b : Fin P.cusp.count | (tsupport (P.block b) ∩ D).Nonempty}.Subsingleton := by
  intro i hi j hj
  by_contra hij
  obtain ⟨x, hxS, hxD⟩ := hi
  obtain ⟨y, hyS, hyD⟩ := hj
  exact absurd (hD x hxD y hyD)
    (not_lt.mpr (P.one_le_edist_of_mem_tsupport_block hε (hdisj i j hij) hxS hyS))

/-- **BCG01, band containment (first exit).** Every point within `1/250` of the `b`th closed
boundary support lies in the collar band `19 < z_b < 91` and has `19 < η_b < 91`
(tolerance `ε ≤ 1/4`). -/
theorem band_of_mem_tsupport_of_edist_lt (P : BoundaryCollarPacket W g K A w₀ ε)
    (hε : ε ≤ 1 / 4) {b : Fin P.cusp.count} {x y : W.Carrier} (hx : x ∈ tsupport (P.block b))
    (hxy : riemannianEDistOf g x y < ENNReal.ofReal (1 / 250)) :
    ∃ q ∈ cuspDomain, (P.cusp.collar b).toFun q = y ∧ 19 < q.2.val 0 ∧ q.2.val 0 < 91 ∧
      19 < P.height b y ∧ P.height b y < 91 := by
  obtain ⟨p, -, rfl, hp20, hp90⟩ := P.exists_of_mem_tsupport_block hx
  have hw : 0 ≤ w₀ := (P.cusp.collar b).delta_nonneg
  have hs : (4 / 5 : ℝ) ≤ Real.sqrt (1 - w₀) := by
    rw [show (4 / 5 : ℝ) = Real.sqrt ((4 / 5) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by linarith [P.threshold])
  have hxy' : riemannianEDistOf g ((P.cusp.collar b).toFun p) y <
      ENNReal.ofReal (Real.sqrt (1 - w₀) * (1 / 200)) :=
    hxy.trans_le (ENNReal.ofReal_le_ofReal (by nlinarith))
  obtain ⟨q, hq, rfl, hqp⟩ := (P.cusp.collar b).exists_abs_height_sub_lt_of_edist_lt
    (s := 1 / 200) (by norm_num) (by norm_num [cuspDepth]; linarith) hxy'
  obtain ⟨hqp1, hqp2⟩ := abs_lt.mp hqp
  have hη := abs_lt.mp (P.height_contract b q hq (by linarith) (by linarith)).1
  refine ⟨q, hq, rfl, by linarith, by linarith, by linarith, by linarith⟩

/-- **BCG01.b on the original reference domains.** Let `ρ > 0` be `Λ`-Lipschitz for `d_g` and
`< r` on every collar region `z ≤ 96` (BSA05). If the reference domain
`D = {y | d(p, y) < C ρ(p)}` (`C ≤ .95L`, `Λ C ≤ 1/2`, `r < 1/(1000L)`) meets the `b`th closed
boundary support, then `ρ(p) < 2r` and every point of `D` lies in `e_b{19 < z < 91}` and in
`{19 < η_b < 91}` (tolerance `ε ≤ 1/4`). -/
theorem bcg01_reference_domain (P : BoundaryCollarPacket W g K A w₀ ε) (hε : ε ≤ 1 / 4)
    {ρ : W.Carrier → ℝ} (hρ : ∀ x, 0 < ρ x) {Λ r C L : ℝ} (hΛ : 0 ≤ Λ)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hsmall : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) < r)
    (hL : 0 < L) (hC : C ≤ 95 / 100 * L) (hΛC : Λ * C ≤ 1 / 2) (hr : r * (1000 * L) < 1)
    {p : W.Carrier} {b : Fin P.cusp.count}
    (hmeet : ∃ x ∈ tsupport (P.block b), riemannianEDistOf g p x < ENNReal.ofReal (C * ρ p)) :
    ρ p < 2 * r ∧ ∀ y, riemannianEDistOf g p y < ENNReal.ofReal (C * ρ p) →
      ∃ q ∈ cuspDomain, (P.cusp.collar b).toFun q = y ∧ 19 < q.2.val 0 ∧ q.2.val 0 < 91 ∧
        19 < P.height b y ∧ P.height b y < 91 := by
  obtain ⟨x, hx, hpx⟩ := hmeet
  have hρp := hρ p
  have hCρ : 0 < C * ρ p := by
    by_contra hle
    push Not at hle
    rw [ENNReal.ofReal_of_nonpos hle] at hpx
    exact absurd hpx (not_lt.mpr bot_le)
  have hC0 : 0 < C := pos_of_mul_pos_left hCρ hρp.le
  -- `R_a < 2 r_∂` by slow variation
  have hρx : ρ x < r := by
    obtain ⟨q, -, rfl, -, hq⟩ := P.exists_of_mem_tsupport_block hx
    exact hsmall b q (by linarith [P.tolerance_le_one])
  have hdiff : |ρ p - ρ x| ≤ Λ * (C * ρ p) := by
    have h1 : ENNReal.ofReal |ρ p - ρ x| ≤ ENNReal.ofReal (Λ * (C * ρ p)) := by
      rw [ENNReal.ofReal_mul hΛ]
      exact (hlip p x).trans (by gcongr)
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h1
  have hρ2 : ρ p < 2 * r := by
    have h2 : Λ * (C * ρ p) ≤ 1 / 2 * ρ p := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hΛC hρp.le
    have h3 := (abs_le.mp hdiff).2
    linarith
  refine ⟨hρ2, fun y hy => P.band_of_mem_tsupport_of_edist_lt hε hx ?_⟩
  -- the reference domain has diameter `< 1/250`
  have htri : riemannianEDistOf g x y ≤ riemannianEDistOf g p x + riemannianEDistOf g p y := by
    rw [riemannianEDistOf_comm g p x]
    exact riemannianEDistOf_triangle g x p y
  have hsum : riemannianEDistOf g p x + riemannianEDistOf g p y <
      ENNReal.ofReal (C * ρ p) + ENNReal.ofReal (C * ρ p) :=
    ENNReal.add_lt_add hpx hy
  rw [← ENNReal.ofReal_add hCρ.le hCρ.le] at hsum
  refine htri.trans_lt (hsum.trans_le (ENNReal.ofReal_le_ofReal ?_))
  have h4 : C * ρ p ≤ 95 / 100 * L * ρ p := mul_le_mul_of_nonneg_right hC hρp.le
  have h5 : L * ρ p ≤ L * (2 * r) := mul_le_mul_of_nonneg_left hρ2.le hL.le
  nlinarith

/-- **BCG01, at most one support per reference domain.** In the nonproduct case, under the
hypotheses of `bcg01_reference_domain`, at most one closed boundary support meets the reference
domain `{y | d(p, y) < C ρ(p)}`. -/
theorem subsingleton_supports_meeting_reference_domain (P : BoundaryCollarPacket W g K A w₀ ε)
    (hε : ε ≤ 1 / 4)
    (hdisj : ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    {ρ : W.Carrier → ℝ} (hρ : ∀ x, 0 < ρ x) {Λ r C L : ℝ} (hΛ : 0 ≤ Λ)
    (hlip : ∀ x y, ENNReal.ofReal |ρ x - ρ y| ≤ ENNReal.ofReal Λ * riemannianEDistOf g x y)
    (hsmall : ∀ (i : Fin P.cusp.count) (q : CuspHalfSpace), q.2.val 0 ≤ 96 →
      ρ ((P.cusp.collar i).toFun q) < r)
    (hL : 0 < L) (hC : C ≤ 95 / 100 * L) (hΛC : Λ * C ≤ 1 / 2) (hr : r * (1000 * L) < 1)
    (p : W.Carrier) :
    {b : Fin P.cusp.count | ∃ x ∈ tsupport (P.block b),
      riemannianEDistOf g p x < ENNReal.ofReal (C * ρ p)}.Subsingleton := by
  intro i hi j hj
  by_contra hij
  obtain ⟨x, hxS, hxD⟩ := hi
  obtain ⟨y, hyS, hyD⟩ := hj
  -- the reference domain has diameter `< 1`, so the two supports are at distance `< 1`
  have hsep := P.one_le_edist_of_mem_tsupport_block (by linarith) (hdisj i j hij) hxS hyS
  have hρ2 := (P.bcg01_reference_domain hε hρ hΛ hlip hsmall hL hC hΛC hr ⟨x, hxS, hxD⟩).1
  have hCρ : 0 < C * ρ p := by
    by_contra hle
    push Not at hle
    rw [ENNReal.ofReal_of_nonpos hle] at hxD
    exact absurd hxD (not_lt.mpr bot_le)
  have htri : riemannianEDistOf g x y ≤
      riemannianEDistOf g p x + riemannianEDistOf g p y := by
    rw [riemannianEDistOf_comm g p x]
    exact riemannianEDistOf_triangle g x p _
  have hsum := ENNReal.add_lt_add hxD hyD
  rw [← ENNReal.ofReal_add hCρ.le hCρ.le] at hsum
  have hlt : 2 * (C * ρ p) < 1 := by
    have h4 : C * ρ p ≤ 95 / 100 * L * ρ p := mul_le_mul_of_nonneg_right hC (hρ p).le
    have h5 : L * ρ p ≤ L * (2 * r) := mul_le_mul_of_nonneg_left hρ2.le hL.le
    nlinarith
  have hfin := htri.trans_lt (hsum.trans_le (ENNReal.ofReal_le_ofReal (by linarith :
    C * ρ p + C * ρ p ≤ 1)))
  exact absurd (hsep.trans_lt hfin) (lt_irrefl _)

/-- `mvfderiv` of a vector-valued function only depends on its germ. -/
theorem mvfderiv_congr_of_eventuallyEq {F G : W.Carrier → ℝ × ℝ} {x : W.Carrier}
    (h : F =ᶠ[𝓝 x] G) (u : TangentSpace W.model x) :
    mvfderiv W.model F x u = mvfderiv W.model G x u := by
  have hmf := Filter.EventuallyEq.mfderiv_eq (I := W.model) (I' := 𝓘(ℝ, ℝ × ℝ)) h
  have hx : F x = G x := h.eq_of_nhds
  unfold mvfderiv
  rw [hmf, hx]
  rfl

/-- `mvfderiv` of a function that vanishes near `x` is zero. -/
theorem mvfderiv_eq_zero_of_not_mem_tsupport {F : W.Carrier → ℝ × ℝ} {x : W.Carrier}
    (hx : x ∉ tsupport F) (u : TangentSpace W.model x) : mvfderiv W.model F x u = 0 := by
  have hev : F =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  rw [mvfderiv_congr_of_eventuallyEq hev u, mvfderiv_const]
  rfl

/-- **BCG01, one-block derivative bound.** With `‖𝓑'‖ ≤ P₀` and tolerance `ε ≤ 1/1000`, the
`b`th boundary block has `‖dF_b(u)‖ ≤ (1 + 1/200) P₀ |u|_g` at every point. -/
theorem norm_mvfderiv_block_le (P : BoundaryCollarPacket W g K A w₀ ε) (hε : ε ≤ 1 / 1000)
    {P₀ : ℝ} (hP₀ : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P₀) (b : Fin P.cusp.count)
    (x : W.Carrier) (u : TangentSpace W.model x) :
    ‖mvfderiv W.model (P.block b) x u‖ ≤ (1 + 1 / 200) * P₀ * Real.sqrt (g.inner x u u) := by
  have hP0 : 0 ≤ P₀ := (norm_nonneg _).trans (hP₀ 0)
  by_cases hx : x ∈ tsupport (P.block b)
  · obtain ⟨p, hp, rfl, hp20, hp90⟩ := P.exists_of_mem_tsupport_block hx
    have hO : IsOpen ((P.cusp.collar b).toFun '' {q : CuspHalfSpace | 2 < q.2.val 0 ∧ q.2.val 0 < 98}) :=
      (P.cusp.collar b).isOpen_image ((isOpen_lt continuous_const continuous_cusp_height).inter
        (isOpen_lt continuous_cusp_height continuous_const))
        fun q hq => cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hq.2.le
    have hmem : (P.cusp.collar b).toFun p ∈ (P.cusp.collar b).toFun '' {q : CuspHalfSpace | 2 < q.2.val 0 ∧ q.2.val 0 < 98} :=
      ⟨p, ⟨by linarith [P.tolerance_le_one], by linarith [P.tolerance_le_one]⟩, rfl⟩
    have hev : P.block b =ᶠ[𝓝 ((P.cusp.collar b).toFun p)] fun y => boundaryBlock (P.height b y) := by
      filter_upwards [hO.mem_nhds hmem] with y hy
      exact indicator_of_mem hy _
    have hηd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (P.height b) ((P.cusp.collar b).toFun p) :=
      (P.contMDiff_height b _).mdifferentiableAt (by simp)
    have hBd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) boundaryBlock (P.height b ((P.cusp.collar b).toFun p)) :=
      ((contDiff_boundaryBlock.differentiable (by simp)) _).mdifferentiableAt
    have hval : mvfderiv W.model (P.block b) ((P.cusp.collar b).toFun p) u =
        fderiv ℝ boundaryBlock (P.height b ((P.cusp.collar b).toFun p))
          (mvfderiv W.model (P.height b) ((P.cusp.collar b).toFun p) u) := by
      have h2 : mvfderiv W.model (boundaryBlock ∘ P.height b) ((P.cusp.collar b).toFun p) u =
          mvfderiv 𝓘(ℝ, ℝ) boundaryBlock (P.height b ((P.cusp.collar b).toFun p))
            (mfderiv W.model 𝓘(ℝ, ℝ) (P.height b) ((P.cusp.collar b).toFun p) u) :=
        mvfderiv_comp_apply _ hBd hηd u
      rw [mvfderiv_eq_fderiv] at h2
      rw [mvfderiv_congr_of_eventuallyEq hev u]
      exact h2
    rw [hval]
    have hd := ((P.cusp.collar b).bcp01b_differential_of_contract (by linarith [P.threshold])
      (P.contMDiff_height b) P.tolerance_pos.le hε hp
      (P.height_contract b p hp (by linarith) (by linarith)).2.1).1 u
    calc ‖fderiv ℝ boundaryBlock (P.height b ((P.cusp.collar b).toFun p))
            (mvfderiv W.model (P.height b) ((P.cusp.collar b).toFun p) u)‖
        ≤ ‖fderiv ℝ boundaryBlock (P.height b ((P.cusp.collar b).toFun p))‖ *
            ‖mvfderiv W.model (P.height b) ((P.cusp.collar b).toFun p) u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ P₀ * ((1 + 1 / 200) * Real.sqrt (g.inner ((P.cusp.collar b).toFun p) u u)) := by
          rw [Real.norm_eq_abs]
          exact mul_le_mul (hP₀ _) hd (abs_nonneg _) hP0
      _ = (1 + 1 / 200) * P₀ * Real.sqrt (g.inner ((P.cusp.collar b).toFun p) u u) := by ring
  · rw [mvfderiv_eq_zero_of_not_mem_tsupport hx, norm_zero]
    positivity

/-- **BCG01, the boundary part of the global derivative bound.** In the nonproduct case, the sum
over ALL boundary components of `‖dF_b(u)‖` is at most `(1 + 1/200) P₀ |u|_g`: at most one block
is nonzero near any point, so the bound does not depend on the number of components. -/
theorem sum_norm_mvfderiv_block_le (P : BoundaryCollarPacket W g K A w₀ ε) (hε : ε ≤ 1 / 1000)
    (hdisj : ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    {P₀ : ℝ} (hP₀ : ∀ t, ‖fderiv ℝ boundaryBlock t‖ ≤ P₀) (x : W.Carrier)
    (u : TangentSpace W.model x) :
    ∑ b, ‖mvfderiv W.model (P.block b) x u‖ ≤ (1 + 1 / 200) * P₀ * Real.sqrt (g.inner x u u) := by
  classical
  have hP0 : 0 ≤ P₀ := (norm_nonneg _).trans (hP₀ 0)
  by_cases h : ∃ b₀, x ∈ tsupport (P.block b₀)
  · obtain ⟨b₀, hb₀⟩ := h
    rw [Finset.sum_eq_single b₀]
    · exact P.norm_mvfderiv_block_le hε hP₀ b₀ x u
    · intro b _ hb
      have hxb : x ∉ tsupport (P.block b) := by
        intro hxb
        have h1 := P.one_le_edist_of_mem_tsupport_block (by linarith) (hdisj b b₀ hb) hxb hb₀
        rw [riemannianEDistOf_self] at h1
        exact absurd h1 (not_le.mpr (by norm_num))
      rw [mvfderiv_eq_zero_of_not_mem_tsupport hxb, norm_zero]
    · intro hb
      exact absurd (Finset.mem_univ b₀) hb
  · push Not at h
    rw [Finset.sum_eq_zero fun b _ => by rw [mvfderiv_eq_zero_of_not_mem_tsupport (h b), norm_zero]]
    positivity

end BoundaryCollarPacket

end DifferentialGeometry.Geometry.Collapse
