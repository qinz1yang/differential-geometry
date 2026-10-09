import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreSpec
import DifferentialGeometry.Topology.Manifold.FiniteOrderFlow.RegularSublevelIsotopy
import DifferentialGeometry.Topology.Manifold.MFDeriv.Interior

/-!
# BCG06, G4b: the relative supported move of the inner collar (lane BCG6-K, review 65 M3)

Review 65 (D65-4): E6 gives the labelled pair `(C_b, ∂_b W) ≅ (T² × [a, 40], T² × {a})` but not a
move supported away from `∂_b W`. Here the original level-40 inner collar `{level_b ≤ 40}` (the
retained certificate's sublevel) is carried onto the core by an ambient diffeomorphism of the
interior `W° = W.pieceInterior ⊤` (interior atlas `interiorCharted_BDRY1`) which is the identity off
a compact set lying in the strip `band ∩ {38 < η_b < 42}` — in particular near `∂W`.

Construction: the moving level `G_τ = level_b + τ Q` (`coreLevelT_BCG6K`, `Q` the strip correction
of G3), `τ = s(t)` with `s = Real.smoothTransition`, is regular on its level `40` for every
`τ ∈ [0, 1]` under (R) (`mfderiv_coreLevelT_ne_zero_BCG6K`), and all these levels lie in the compact
`e(37 ≤ z ≤ 43) ∩ {39.9 ≤ η_b ≤ 40.1}` (`coreLevelT_eq_forty_mem_BCG6K`). The tree's compactly
supported isotopy of a moving regular level (`exists_isotopy_regularSublevel_smooth`, defining pair
`Ψ(t, x) = G_{s(t)}(x) - 40`, `B ≡ 1`) carries `{level_b = 40}` onto `H_b`; the sides follow from the
connectedness of `{level_b < 40} ∩ W°` and `{G < 40} ∩ W°` (the two product certificates) and from a
fixed point near `∂_b W`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ}

namespace BoundaryCollarPacket

variable (P : BoundaryCollarPacket W g K A w₀ ε) (b : Fin P.cusp.count)

/-- The moving level `G_τ = level_b + τ Q`. -/
def coreLevelT_BCG6K (u : W.Carrier → ℝ) (τ : ℝ) (x : W.Carrier) : ℝ :=
  P.level b x + τ * P.coreCorrection_BCG6K b u x

theorem coreLevelT_one_BCG6K (u : W.Carrier → ℝ) :
    P.coreLevelT_BCG6K b u 1 = P.coreLevel_BCG6K b u := by
  funext x
  rw [coreLevelT_BCG6K, coreLevel_BCG6K, one_mul]

theorem coreLevelT_zero_BCG6K (u : W.Carrier → ℝ) : P.coreLevelT_BCG6K b u 0 = P.level b := by
  funext x
  rw [coreLevelT_BCG6K, zero_mul, add_zero]

theorem contMDiff_coreCorrection_BCG6K {u : W.Carrier → ℝ}
    (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u) :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (P.coreCorrection_BCG6K b u) := by
  have h := (P.contMDiff_coreLevel_BCG6K b hu).sub (P.contMDiff_level b)
  convert h using 1
  funext x
  simp [coreLevel_BCG6K]

/-- On the strip, `G_τ = η_b + τ κ(η_b) (u - η_b)`. -/
theorem coreLevelT_eq_on_strip_BCG6K (u : W.Carrier → ℝ) (τ : ℝ) {x : W.Carrier}
    (hx : x ∈ P.coreStrip_BCG6K b) :
    P.coreLevelT_BCG6K b u τ x =
      P.height b x + τ * (coreCutoff_BCG6K (P.height b x) * (u x - P.height b x)) := by
  have hband := P.coreStrip_subset_band_BCG6K b hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [coreLevelT_BCG6K, coreCorrection_BCG6K, indicator_of_mem hband,
    P.level_eq_height b p hp.1.le hp.2.le]

variable {b}

/-- **Where the moving level equals `40`** (`τ ∈ [0, 1]`): only at strip points of height
`37 ≤ z ≤ 43` with `|η_b - 40| ≤ 1/10`. -/
theorem coreLevelT_eq_forty_mem_BCG6K {u : W.Carrier → ℝ} {εd : ℝ} (hεd : εd < 1 / 10)
    (hBIu : ∀ x ∈ P.safeBand_BAUGA b, |u x - (P.block b x).1| < εd) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ1 : τ ≤ 1) {x : W.Carrier} (hx : P.coreLevelT_BCG6K b u τ x = 40) :
    x ∈ (P.cusp.collar b).toFun '' {p : CuspHalfSpace | 37 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 43} ∩
      {y | 399 / 10 ≤ P.height b y ∧ P.height b y ≤ 401 / 10} := by
  have hε1 := P.tolerance_le_one
  by_cases hband : x ∈ P.collarBand_BAUGA b
  · have hband' := hband
    obtain ⟨p, hp, rfl⟩ := hband'
    have hpd : p ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
    have hc := abs_lt.mp (P.height_contract b p hpd hp.1.le hp.2.le).1
    have hQ : P.coreCorrection_BCG6K b u ((P.cusp.collar b).toFun p) =
        coreCutoff_BCG6K (P.height b ((P.cusp.collar b).toFun p)) *
          (u ((P.cusp.collar b).toFun p) - P.height b ((P.cusp.collar b).toFun p)) :=
      indicator_of_mem hband _
    set η := P.height b ((P.cusp.collar b).toFun p) with hη
    by_cases hz95 : p.2.val 0 ≤ 95
    · have hG : P.coreLevelT_BCG6K b u τ ((P.cusp.collar b).toFun p) =
          η + τ * (coreCutoff_BCG6K η * (u ((P.cusp.collar b).toFun p) - η)) := by
        rw [coreLevelT_BCG6K, hQ, P.level_eq_height b p hp.1.le hz95]
      by_cases hκ : coreCutoff_BCG6K η = 0
      · rw [hG, hκ, zero_mul, mul_zero, add_zero] at hx
        rw [hx] at hκ
        rw [coreCutoff_eq_one_BCG6K (by norm_num) (by norm_num)] at hκ
        norm_num at hκ
      · have hs := coreCutoff_mem_strip_BCG6K hκ
        have hsafe : (P.cusp.collar b).toFun p ∈ P.safeBand_BAUGA b :=
          ⟨hband, by linarith, by linarith⟩
        have hu := hBIu _ hsafe
        rw [P.block_eq_of_mem_safeBand_BAUGA b hsafe] at hu
        have hu' := abs_lt.mp (show |u ((P.cusp.collar b).toFun p) - η| < εd from hu)
        have hκ0 := coreCutoff_nonneg_BCG6K η
        have hκ1 := coreCutoff_le_one_BCG6K η
        rw [hG] at hx
        have h1 : |τ * (coreCutoff_BCG6K η * (u ((P.cusp.collar b).toFun p) - η))| ≤ εd := by
          rw [abs_mul, abs_mul, abs_of_nonneg hτ0, abs_of_nonneg hκ0]
          have := abs_lt.mpr hu'
          calc τ * (coreCutoff_BCG6K η * |u ((P.cusp.collar b).toFun p) - η|)
              ≤ 1 * (1 * |u ((P.cusp.collar b).toFun p) - η|) := by
                apply mul_le_mul hτ1 (mul_le_mul_of_nonneg_right hκ1 (abs_nonneg _))
                  (by positivity) zero_le_one
            _ ≤ εd := by linarith
        have h2 := abs_le.mp h1
        refine ⟨⟨p, ⟨by linarith, by linarith⟩, rfl⟩, by linarith, by linarith⟩
    · exfalso
      have h95 : 95 < p.2.val 0 := not_le.mp hz95
      have hκ : coreCutoff_BCG6K η = 0 := coreCutoff_eq_zero_of_ge_BCG6K (by linarith)
      have hlev := P.level_gt_ninety_of_height_gt_BCG6K b hpd h95 hp.2
      rw [coreLevelT_BCG6K, hQ, hκ, zero_mul, mul_zero, add_zero] at hx
      linarith
  · exfalso
    have hQ0 : P.coreCorrection_BCG6K b u x = 0 := indicator_of_notMem hband _
    rw [coreLevelT_BCG6K, hQ0, mul_zero, add_zero] at hx
    by_cases hlow : ∃ p ∈ cuspDomain, p.2.val 0 ≤ 2 ∧ (P.cusp.collar b).toFun p = x
    · obtain ⟨p, hpd, hz2, rfl⟩ := hlow
      linarith [P.level_lt_of_height_le_two_BCG6K b hpd hz2]
    · linarith [P.level_gt_ninety_of_notMem_BCG6K b hband hlow]

/-- **Regularity of the moving level on its level `40`** (`τ ∈ [0, 1]`, condition (R)). -/
theorem mfderiv_coreLevelT_ne_zero_BCG6K (hε : ε ≤ 1 / 1000) {u : W.Carrier → ℝ}
    (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u) {εd c₃ : ℝ} (hc₃ : 0 ≤ c₃)
    (hR : 80 * εd + 102 / 100 * c₃ < 1)
    (hBIu : ∀ x ∈ P.safeBand_BAUGA b, |u x - (P.block b x).1| < εd)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w))
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) {x : W.Carrier}
    (hx : P.coreLevelT_BCG6K b u τ x ≤ 40) :
    mfderiv W.model 𝓘(ℝ, ℝ) (P.coreLevelT_BCG6K b u τ) x ≠ 0 := by
  by_cases hxT : x ∈ tsupport (P.coreCorrection_BCG6K b u)
  · obtain ⟨hxK, h1, h2⟩ := P.tsupport_coreCorrection_subset_BCG6K b u hxT
    have hxS : x ∈ P.coreStrip_BCG6K b := P.closedStrip_subset_coreStrip_BCG6K b hxK
    have hband := P.coreStrip_subset_band_BCG6K b hxS
    have hsafe : x ∈ P.safeBand_BAUGA b := ⟨hband, by linarith, by linarith⟩
    have hux := hBIu x hsafe
    rw [P.block_eq_of_mem_safeBand_BAUGA b hsafe] at hux
    have hux' : |u x - P.height b x| < εd := hux
    have heq : P.coreLevelT_BCG6K b u τ =ᶠ[𝓝 x] fun y =>
        P.height b y + τ * (coreCutoff_BCG6K (P.height b y) * (u y - P.height b y)) := by
      filter_upwards [(P.isOpen_coreStrip_BCG6K b).mem_nhds hxS] with y hy
      exact P.coreLevelT_eq_on_strip_BCG6K b u τ hy
    obtain ⟨w, hw1, hw2⟩ := P.exists_heightUnit_BCG6K b hε hband
    apply mfderiv_ne_zero_of_mvfderiv_BCG6K (w := w)
    rw [mvfderiv_congr_BCG6K heq]
    have hηd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (P.height b) x :=
      ((P.contMDiff_height b) x).mdifferentiableAt (by simp)
    have hud : MDifferentiableAt W.model 𝓘(ℝ, ℝ) u x := (hu x).mdifferentiableAt (by simp)
    have hhd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (fun y => u y - P.height b y) x := hud.sub hηd
    have hκd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (fun y => coreCutoff_BCG6K (P.height b y)) x :=
      ((contDiff_coreCutoff_BCG6K.contMDiff.comp (P.contMDiff_height b)) x).mdifferentiableAt
        (by simp)
    have hτd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (fun _ : W.Carrier => τ) x :=
      mdifferentiableAt_const
    have hκdiff : DifferentiableAt ℝ coreCutoff_BCG6K (P.height b x) :=
      (contDiff_coreCutoff_BCG6K.differentiable (by simp)) _
    change mvfderiv W.model (P.height b + (fun _ => τ) * ((fun y => coreCutoff_BCG6K (P.height b y)) *
      (fun y => u y - P.height b y))) x w ≠ 0
    rw [mvfderiv_add hηd (hτd.mul (hκd.mul hhd)), add_apply, mvfderiv_mul hτd (hκd.mul hhd),
      mvfderiv_const, add_apply, smul_apply, smul_apply, zero_apply, smul_zero, add_zero,
      smul_eq_mul, mvfderiv_mul hκd hhd, add_apply, smul_apply, smul_apply, smul_eq_mul,
      smul_eq_mul, DifferentialGeometry.Topology.Ehresmann.mvfderiv_comp_real hηd hκdiff w, hw1]
    have hd := abs_le.mp (abs_deriv_coreCutoff_le_BCG6K (P.height b x))
    have hκ0 := coreCutoff_nonneg_BCG6K (P.height b x)
    have hκ1 := coreCutoff_le_one_BCG6K (P.height b x)
    have hA : |mvfderiv W.model (fun y => u y - P.height b y) x w| ≤ c₃ * (101 / 100) :=
      (hBD x hband (by linarith) (by linarith) w).trans (mul_le_mul_of_nonneg_left hw2 hc₃)
    have hA' := abs_le.mp hA
    have hu2 := abs_lt.mp hux'
    have hεd0 : 0 < εd := (abs_nonneg _).trans_lt hux'
    have e1 : -(101 / 100 * c₃) ≤ coreCutoff_BCG6K (P.height b x) *
        mvfderiv W.model (fun y => u y - P.height b y) x w := by nlinarith
    have e2 : -(80 * εd) ≤ (u x - P.height b x) * (deriv coreCutoff_BCG6K (P.height b x) * 1) := by
      nlinarith
    have e3 : -(101 / 100 * c₃ + 80 * εd) ≤ τ * (coreCutoff_BCG6K (P.height b x) *
        mvfderiv W.model (fun y => u y - P.height b y) x w +
          (u x - P.height b x) * (deriv coreCutoff_BCG6K (P.height b x) * 1)) := by
      have h3 : -(101 / 100 * c₃ + 80 * εd) ≤ coreCutoff_BCG6K (P.height b x) *
          mvfderiv W.model (fun y => u y - P.height b y) x w +
            (u x - P.height b x) * (deriv coreCutoff_BCG6K (P.height b x) * 1) := by linarith
      have h4 : 0 ≤ 101 / 100 * c₃ + 80 * εd := by positivity
      nlinarith
    apply ne_of_gt
    linarith
  · have hQ : P.coreCorrection_BCG6K b u =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxT
    have heq : P.coreLevelT_BCG6K b u τ =ᶠ[𝓝 x] P.level b := by
      filter_upwards [hQ] with y hy
      rw [coreLevelT_BCG6K, hy, Pi.zero_apply, mul_zero, add_zero]
    have hQx : P.coreCorrection_BCG6K b u x = 0 := hQ.eq_of_nhds
    have hlev : P.level b x ≤ 90 := by
      have h : P.coreLevelT_BCG6K b u τ x = P.level b x := by
        rw [coreLevelT_BCG6K, hQx, mul_zero, add_zero]
      linarith
    rw [← mvfderiv_ne_zero_iff_BCG6K, mvfderiv_congr_BCG6K heq, mvfderiv_ne_zero_iff_BCG6K]
    exact P.mfderiv_level_ne_zero_BCG6K b hlev

end BoundaryCollarPacket

section Interior

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable (W) in
/-- The inclusion `W° → W` is smooth from the interior atlas. -/
theorem contMDiff_val_interior_BCG6K :
    ContMDiff (𝓡 3) W.model ∞ (Subtype.val : W.pieceInterior ⊤ → W.Carrier) :=
  (contMDiff_subtype_val (I := W.model) (U := W.pieceInterior ⊤)).comp
    (DifferentialGeometry.Manifold.contMDiff_interiorAtlas_id W.model ∞
      (M := W.pieceInterior ⊤))

/-- The points of `W°` are interior points of `W`. -/
theorem isInteriorPoint_of_mem_interior_BCG6K (x : W.pieceInterior ⊤) :
    W.model.IsInteriorPoint (x : W.Carrier) := by
  have h : (x : W.Carrier) ∈ ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) :
      Set W.Carrier) := x.2
  rw [coe_pieceInterior_top_BDRY1] at h
  exact h

/-- An interior point of `W` is a point of `W°`. -/
theorem mem_pieceInterior_of_isInteriorPoint_BCG6K {y : W.Carrier}
    (hy : W.model.IsInteriorPoint y) :
    y ∈ ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier) := by
  rw [coe_pieceInterior_top_BDRY1]
  exact hy

/-- A nonzero differential on `W` stays nonzero in the interior atlas of `W°`. -/
theorem mfderiv_comp_val_ne_zero_BCG6K {f : W.Carrier → ℝ}
    (hf : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ f) (x : W.pieceInterior ⊤)
    (h : mfderiv W.model 𝓘(ℝ, ℝ) f (x : W.Carrier) ≠ 0) :
    mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun y : W.pieceInterior ⊤ => f y) x ≠ 0 := by
  intro h0
  apply h
  have hg : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun y : W.pieceInterior ⊤ => f y) :=
    hf.comp contMDiff_subtype_val
  have e1 := DifferentialGeometry.Manifold.mfderiv_interiorAtlas W.model hg x
  have e2 := DifferentialGeometry.Manifold.mfderiv_openRestriction W.model hf x
    (isInteriorPoint_of_mem_interior_BCG6K x)
  have e3 : (show E3 →L[ℝ] ℝ from mfderiv W.model 𝓘(ℝ, ℝ) f (x : W.Carrier)) = 0 := by
    rw [← e2, ← e1]
    exact h0
  exact e3

/-- A nonzero real linear functional is surjective. -/
theorem surjective_of_ne_zero_BCG6K {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {L : V →L[ℝ] ℝ} (hL : L ≠ 0) : Surjective L := by
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hL (ContinuousLinearMap.ext h)
  intro c
  refine ⟨(c / L v) • v, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hv]

namespace BoundaryCollarPacket

variable {P : BoundaryCollarPacket W g K A w₀ ε} {b : Fin P.cusp.count}

/-- **The isotopy of the moving level** (tree kernel `exists_isotopy_regularSublevel_smooth` on
`W°`): compactly supported in `band ∩ {38 < η_b < 42}`, carrying the `40`-level of `G_{s(s)}` onto
that of `G_{s(t)}`. -/
theorem exists_level_isotopy_BCG6K (hε : ε ≤ 1 / 1000) {u : W.Carrier → ℝ}
    (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u) {εd c₃ : ℝ} (hc₃ : 0 ≤ c₃)
    (hR : 80 * εd + 102 / 100 * c₃ < 1)
    (hBIu : ∀ x ∈ P.safeBand_BAUGA b, |u x - (P.block b x).1| < εd)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w)) :
    ∃ (K' : Set (W.pieceInterior ⊤))
      (Φ : ℝ → ℝ → Diffeomorph (𝓡 3) (𝓡 3) (W.pieceInterior ⊤) (W.pieceInterior ⊤) ∞),
      IsCompact K' ∧
      (∀ x ∈ K', (x : W.Carrier) ∈ P.collarBand_BAUGA b ∧ 38 < P.height b x ∧
        P.height b x < 42) ∧
      (∀ s t x, x ∉ K' → Φ s t x = x) ∧
      ∀ s t, Φ s t '' {x : W.pieceInterior ⊤ |
          P.coreLevelT_BCG6K b u (Real.smoothTransition s) (x : W.Carrier) = 40} =
        {x : W.pieceInterior ⊤ |
          P.coreLevelT_BCG6K b u (Real.smoothTransition t) (x : W.Carrier) = 40} := by
  have hεd1 : εd < 1 / 10 := by linarith
  set Ψ : ℝ × W.pieceInterior ⊤ → ℝ :=
    fun q => P.coreLevelT_BCG6K b u (Real.smoothTransition q.1) q.2 - 40 with hΨdef
  set B : ℝ × W.pieceInterior ⊤ → ℝ := fun _ => 1 with hBdef
  have hval := contMDiff_val_interior_BCG6K W
  have hQ := P.contMDiff_coreCorrection_BCG6K b hu
  have hΨ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞ Ψ := by
    have h1 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × W.pieceInterior ⊤ => P.level b q.2) :=
      ((P.contMDiff_level b).comp hval).comp contMDiff_snd
    have h2 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × W.pieceInterior ⊤ => Real.smoothTransition q.1) :=
      Real.smoothTransition.contDiff.contMDiff.comp contMDiff_fst
    have h3 : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun q : ℝ × W.pieceInterior ⊤ => P.coreCorrection_BCG6K b u q.2) :=
      (hQ.comp hval).comp contMDiff_snd
    exact ((h1.add (h2.mul h3)).sub contMDiff_const)
  have hB : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞ B := contMDiff_const
  have htrans : ∀ q : ℝ × W.pieceInterior ⊤, Ψ q = 0 → 0 ≤ B q →
      Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ) (fun y => Ψ (q.1, y)) q.2) := by
    intro q hq _
    have hτ0 := Real.smoothTransition.nonneg q.1
    have hτ1 := Real.smoothTransition.le_one q.1
    have h40 : P.coreLevelT_BCG6K b u (Real.smoothTransition q.1) q.2 = 40 := by
      simp only [hΨdef] at hq
      linarith
    have hGs : ContMDiff W.model 𝓘(ℝ, ℝ) ∞
        (fun x => P.coreLevelT_BCG6K b u (Real.smoothTransition q.1) x + (-40)) :=
      ((P.contMDiff_level b).add (contMDiff_const.mul hQ)).add contMDiff_const
    have hreg := P.mfderiv_coreLevelT_ne_zero_BCG6K hε hu hc₃ hR hBIu hBD hτ0 hτ1 h40.le
    have hreg' : mfderiv W.model 𝓘(ℝ, ℝ)
        (fun x => P.coreLevelT_BCG6K b u (Real.smoothTransition q.1) x + (-40))
          (q.2 : W.Carrier) ≠ 0 := by
      have hGd : MDifferentiableAt W.model 𝓘(ℝ, ℝ)
          (P.coreLevelT_BCG6K b u (Real.smoothTransition q.1)) (q.2 : W.Carrier) :=
        ((((P.contMDiff_level b).add (contMDiff_const.mul hQ))) _).mdifferentiableAt (by simp)
      rw [← mvfderiv_ne_zero_iff_BCG6K, mvfderiv_fun_add hGd mdifferentiableAt_const,
        mvfderiv_const, add_zero, mvfderiv_ne_zero_iff_BCG6K]
      exact hreg
    have hne := mfderiv_comp_val_ne_zero_BCG6K hGs q.2 hreg'
    have hfun : (fun y => Ψ (q.1, y)) = fun y : W.pieceInterior ⊤ =>
        P.coreLevelT_BCG6K b u (Real.smoothTransition q.1) y + (-40) := by
      funext y
      simp only [hΨdef]
      ring
    rw [hfun]
    exact surjective_of_ne_zero_BCG6K hne
  have htransb : ∀ q : ℝ × W.pieceInterior ⊤, Ψ q = 0 → B q = 0 →
      Surjective (mfderiv (𝓡 3) 𝓘(ℝ, ℝ × ℝ) (fun y => (Ψ (q.1, y), B (q.1, y))) q.2) := by
    intro q _ hB0
    simp only [hBdef] at hB0
    norm_num at hB0
  set S0 : Set W.Carrier :=
    (P.cusp.collar b).toFun '' {p : CuspHalfSpace | 37 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 43} ∩
      {y | 399 / 10 ≤ P.height b y ∧ P.height b y ≤ 401 / 10} with hS0
  have hS0c : IsCompact S0 :=
    ((P.cusp.collar b).isCompact_image_band (by norm_num [cuspDepth])).inter_right
      ((isClosed_le continuous_const (P.contMDiff_height b).continuous).inter
        (isClosed_le (P.contMDiff_height b).continuous continuous_const))
  have hS0r : S0 ⊆ range (Subtype.val : W.pieceInterior ⊤ → W.Carrier) := by
    rintro _ ⟨⟨p, hp, rfl⟩, -⟩
    have hpd : p ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 43) (by norm_num [cuspDepth]) hp.2
    exact ⟨⟨_, mem_pieceInterior_of_isInteriorPoint_BCG6K
      (isInteriorPoint_of_height_pos_BCG6K (P.cusp.collar b) hpd (by linarith [hp.1]))⟩, rfl⟩
  have hS : IsCompact ((Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' S0) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hS0c hS0r
  have hWS : ∀ q : ℝ × W.pieceInterior ⊤, Ψ q = 0 → 0 ≤ B q →
      q.2 ∈ (Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' S0 := by
    intro q hq _
    have h40 : P.coreLevelT_BCG6K b u (Real.smoothTransition q.1) q.2 = 40 := by
      simp only [hΨdef] at hq
      linarith
    exact P.coreLevelT_eq_forty_mem_BCG6K hεd1 hBIu (Real.smoothTransition.nonneg q.1)
      (Real.smoothTransition.le_one q.1) h40
  set N0 : Set W.Carrier :=
    P.collarBand_BAUGA b ∩ {y | 38 < P.height b y ∧ P.height b y < 42} with hN0
  have hN : IsOpen ((Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' N0) :=
    continuous_subtype_val.isOpen_preimage _ ((P.isOpen_collarBand_BAUGA b).inter
      ((isOpen_lt continuous_const (P.contMDiff_height b).continuous).inter
        (isOpen_lt (P.contMDiff_height b).continuous continuous_const)))
  have hSN : (Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' S0 ⊆
      (Subtype.val : W.pieceInterior ⊤ → W.Carrier) ⁻¹' N0 := by
    rintro x ⟨⟨p, hp, hpx⟩, h1, h2⟩
    exact ⟨⟨p, ⟨by linarith [hp.1], by linarith [hp.2]⟩, hpx⟩, by linarith, by linarith⟩
  obtain ⟨K', Φ, hK'c, hK'N, -, -, hid, himg, -⟩ :=
    DifferentialGeometry.Analysis.ODE.exists_isotopy_regularSublevel_smooth hΨ hB htrans htransb
      hS hWS hN hSN
  refine ⟨K', Φ, hK'c, fun x hx => ?_, hid, fun s t => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hK'N hx
    exact ⟨h1, h2, h3⟩
  · have hset : ∀ r : ℝ, {x : W.pieceInterior ⊤ | Ψ (r, x) = 0 ∧ 0 ≤ B (r, x)} =
        {x : W.pieceInterior ⊤ |
          P.coreLevelT_BCG6K b u (Real.smoothTransition r) (x : W.Carrier) = 40} := by
      intro r
      ext x
      simp only [hΨdef, hBdef, mem_ofPred_eq, zero_le_one, and_true, sub_eq_zero]
    rw [← hset s, ← hset t]
    exact himg s t

variable (P b) in
/-- The points of `∂_b W` are not interior points of `W`. -/
theorem not_isInteriorPoint_of_mem_component_BCG6K {y : W.Carrier}
    (hy : y ∈ P.cusp.component b) : ¬ W.model.IsInteriorPoint y := by
  obtain ⟨t, rfl⟩ := (Set.ext_iff.mp (P.cusp.collar b).boundary_image y).mpr hy
  intro hint
  have hb : (P.cusp.collar b).toFun (t, halfZero) ∈ W.model.boundary W.Carrier :=
    ((P.cusp.collar b).boundary_preimage (mem_cuspDomain_halfZero t)).mpr halfZero_val_zero
  exact (W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp hint hb

variable (P b) in
/-- A non-interior point of the retained sublevel lies in `∂_b W`. -/
theorem mem_component_of_level_le_of_not_interior_BCG6K {y : W.Carrier}
    (hy : P.level b y ≤ 90) (hint : ¬ W.model.IsInteriorPoint y) : y ∈ P.cusp.component b := by
  have hyl : y ∈ {y | P.level b y ≤ 90} := hy
  rw [P.level_sublevel_eq b] at hyl
  obtain ⟨q, ⟨hqd, -⟩, rfl⟩ := hyl
  have hb : W.model.IsBoundaryPoint ((P.cusp.collar b).toFun q) :=
    (W.model.isInteriorPoint_or_isBoundaryPoint _).resolve_left hint
  have hz := ((P.cusp.collar b).boundary_preimage hqd).mp hb
  rw [cusp_eq_halfZero_of_height_eq_zero hz]
  exact (Set.ext_iff.mp (P.cusp.collar b).boundary_image _).mp ⟨q.1, rfl⟩

/-- **Connectedness of an open sublevel in `W°`** from a product certificate
`D : T² × [a, r] → {f ≤ r}` (`f ∘ D = pr₂`, `D p ∈ X ↔ p.2 = a`, `X` outside `W°`, the
non-interior points of `{f ≤ r}` in `X`): `{f < c} ∩ W°` is preconnected for `a < c ≤ r`. -/
theorem isPreconnected_lt_interior_BCG6K {f : W.Carrier → ℝ} {X : Set W.Carrier} {a r c : ℝ}
    (D : Torus × Icc a r → {x : W.Carrier // f x ≤ r}) (hDc : Continuous D)
    (hDs : Surjective D) (hDF : ∀ p, f (D p : W.Carrier) = p.2)
    (hDX : ∀ p, (D p : W.Carrier) ∈ X ↔ (p.2 : ℝ) = a) (hac : a < c) (hcr : c ≤ r)
    (hXW : ∀ y ∈ X, ¬ W.model.IsInteriorPoint y)
    (hbd : ∀ y, f y ≤ r → ¬ W.model.IsInteriorPoint y → y ∈ X) :
    IsPreconnected {x : W.pieceInterior ⊤ | f x < c} := by
  have har : a ≤ r := by linarith
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
  have himage : (Subtype.val : W.pieceInterior ⊤ → W.Carrier) ''
      {x : W.pieceInterior ⊤ | f x < c} =
      (fun q : Torus × ℝ => (D (q.1, Set.projIcc a r har q.2) : W.Carrier)) ''
        (univ ×ˢ Ioo a c) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : f (x : W.Carrier) < c := hx
      obtain ⟨p, hp⟩ := hDs ⟨x, by linarith⟩
      have hfp : f (x : W.Carrier) = p.2 := by rw [← hDF p, hp]
      have hnX : (D p : W.Carrier) ∉ X := by
        rw [hp]
        exact fun h => hXW _ h (isInteriorPoint_of_mem_interior_BCG6K x)
      have hpa : (p.2 : ℝ) ≠ a := fun h => hnX ((hDX p).mpr h)
      refine ⟨(p.1, (p.2 : ℝ)), ⟨mem_univ _, lt_of_le_of_ne p.2.2.1 (Ne.symm hpa),
        by rw [← hfp]; exact hx'⟩, ?_⟩
      change (D (p.1, Set.projIcc a r har (p.2 : ℝ)) : W.Carrier) = x
      rw [Set.projIcc_val, Prod.mk.eta, hp]
    · rintro ⟨q, ⟨-, hq1, hq2⟩, rfl⟩
      have hp2 : ((Set.projIcc a r har q.2 : Icc a r) : ℝ) = q.2 := by
        rw [Set.projIcc_of_mem har ⟨hq1.le, by linarith⟩]
      have hint : W.model.IsInteriorPoint (D (q.1, Set.projIcc a r har q.2) : W.Carrier) := by
        by_contra h
        have hX := (hDX _).mp (hbd _ (D (q.1, Set.projIcc a r har q.2)).2 h)
        change ((Set.projIcc a r har q.2 : Icc a r) : ℝ) = a at hX
        rw [hp2] at hX
        linarith
      refine ⟨⟨_, mem_pieceInterior_of_isInteriorPoint_BCG6K hint⟩, ?_, rfl⟩
      change f (D (q.1, Set.projIcc a r har q.2) : W.Carrier) < c
      rw [hDF]
      change ((Set.projIcc a r har q.2 : Icc a r) : ℝ) < c
      rw [hp2]
      exact hq2
  have hcont : Continuous fun q : Torus × ℝ => (D (q.1, Set.projIcc a r har q.2) : W.Carrier) :=
    continuous_subtype_val.comp (hDc.comp (continuous_fst.prodMk
      (continuous_projIcc.comp continuous_snd)))
  have h := (isPreconnected_univ.prod (isPreconnected_Ioo (a := a) (b := c))).image _
    hcont.continuousOn
  rw [← himage] at h
  exact h

/-- **The relative supported move (G4b, review 65 M3)**: an ambient diffeomorphism `Φ` of `W°`,
the identity off a compact set lying in the strip `band ∩ {38 < η_b < 42}` (hence near `∂W`),
carries the original level-`40` inner collar `{level_b ≤ 40}` onto the core and its level torus
onto the front. -/
theorem cuspCore_relative_move_BCG6K (hε : ε ≤ 1 / 1000)
    {u v : Fin P.cusp.count → W.Carrier → ℝ} (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u b))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃ : 0 ≤ c₃) (hR : 80 * εd + 102 / 100 * c₃ < 1)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u b y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w)) :
    ∃ (K' : Set (W.pieceInterior ⊤))
      (Φ : Diffeomorph (𝓡 3) (𝓡 3) (W.pieceInterior ⊤) (W.pieceInterior ⊤) ∞),
      IsCompact K' ∧
      (∀ x ∈ K', (x : W.Carrier) ∈ P.collarBand_BAUGA b ∧ 38 < P.height b x ∧
        P.height b x < 42) ∧
      (∀ x, x ∉ K' → Φ x = x) ∧
      (fun x => (Φ x : W.Carrier)) '' {x : W.pieceInterior ⊤ | P.level b x ≤ 40} =
        P.cuspCore_BCG6K b u v ∩
          ((W.pieceInterior ⊤ : TopologicalSpace.Opens W.Carrier) : Set W.Carrier) ∧
      (fun x => (Φ x : W.Carrier)) '' {x : W.pieceInterior ⊤ | P.level b x = 40} =
        P.cuspFront_BCG6K b u v := by
  obtain ⟨K', Φt, hK'c, hK'N, hid, himg⟩ :=
    exists_level_isotopy_BCG6K hε hu hc₃ hR (fun x _ => (hBI x).1) hBD
  set Φ := Φt 0 1 with hΦ
  set G := P.coreLevel_BCG6K b (u b) with hG
  have hL : Φ '' {x : W.pieceInterior ⊤ | P.level b x = 40} =
      {x : W.pieceInterior ⊤ | G x = 40} := by
    have h := himg 0 1
    simp only [Real.smoothTransition.zero, Real.smoothTransition.one, coreLevelT_zero_BCG6K,
      coreLevelT_one_BCG6K] at h
    exact h
  -- the fixed point near `∂_b W`
  obtain ⟨θ₀⟩ := (inferInstance : Nonempty Torus)
  set q₀ : CuspHalfSpace := (θ₀, halfSpaceOneLift 1) with hq₀
  have hz₀ : q₀.2.val 0 = 1 := by
    rw [hq₀]
    change (halfSpaceOneLift 1).1 0 = 1
    rw [halfSpaceOneLift_val_zero]
    norm_num
  have hq₀d : q₀ ∈ cuspDomain :=
    cusp_mem_cuspDomain_of_le (b := 1) (by norm_num [cuspDepth]) hz₀.le
  set x₀ : W.pieceInterior ⊤ := ⟨(P.cusp.collar b).toFun q₀,
    mem_pieceInterior_of_isInteriorPoint_BCG6K
      (isInteriorPoint_of_height_pos_BCG6K (P.cusp.collar b) hq₀d (by rw [hz₀]; norm_num))⟩
    with hx₀
  have hx₀band : (x₀ : W.Carrier) ∉ P.collarBand_BAUGA b := by
    rintro ⟨q, hq, hqx⟩
    have hqd : q ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hq.2.le
    have h := P.collar_bands_disjoint_BCG6K b hqd hq₀d hqx
    have h2 : 2 < q₀.2.val 0 := by rw [← h]; exact hq.1
    linarith
  have hx₀K : x₀ ∉ K' := fun h => hx₀band (hK'N x₀ h).1
  have hΦx₀ : Φ x₀ = x₀ := hid 0 1 x₀ hx₀K
  have hlev₀ : P.level b (x₀ : W.Carrier) < 39 :=
    P.level_lt_of_height_le_two_BCG6K b hq₀d (by rw [hz₀]; norm_num)
  have hG₀ : G (x₀ : W.Carrier) = P.level b (x₀ : W.Carrier) := by
    rw [hG, coreLevel_BCG6K, coreCorrection_BCG6K, indicator_of_notMem hx₀band, add_zero]
  -- connectedness of the two open sides
  have ha39 := P.levelBase_lt_thirtyNine_BCG6K b
  have hA₀ : IsPreconnected {x : W.pieceInterior ⊤ | P.level b x < 40} := by
    have : Fact (P.levelBase b < 90) := ⟨P.levelBase_lt b⟩
    obtain ⟨cs, -, -, -, D, hDF, hDX⟩ := P.retained b
    let := cs
    exact isPreconnected_lt_interior_BCG6K D D.continuous D.surjective hDF hDX
      (by linarith) (by norm_num) (fun y hy => not_isInteriorPoint_of_mem_component_BCG6K P b hy)
      (fun y hy hint => mem_component_of_level_le_of_not_interior_BCG6K P b hy hint)
  have hA₁ : IsPreconnected {x : W.pieceInterior ⊤ | G x < 40} := by
    have har : P.levelBase b < 40 := by linarith
    have : Fact (P.levelBase b < 40) := ⟨har⟩
    have hF := P.contMDiff_coreLevel_BCG6K b hu
    have hreg : ∀ x, P.coreLevel_BCG6K b (u b) x ≤ 40 →
        mfderiv W.model 𝓘(ℝ, ℝ) (P.coreLevel_BCG6K b (u b)) x ≠ 0 := fun x hx =>
      P.mfderiv_coreLevel_ne_zero_BCG6K b hε hu hc₃ hR (fun y _ => (hBI y).1) hBD hx
    have hr := P.exists_coreLevel_eq_forty_BCG6K b hu
    have hXa : ∀ x ∈ P.cusp.component b, P.coreLevel_BCG6K b (u b) x = P.levelBase b :=
      fun x hx => P.coreLevel_eq_levelBase_BCG6K b (u b) hx
    have hbdG : ∀ x, W.model.IsBoundaryPoint x → P.coreLevel_BCG6K b (u b) x ≤ 40 →
        x ∈ P.cusp.component b := fun x hx hle =>
      P.mem_component_of_isBoundaryPoint_BCG6K hεd hBI hBFM hx hle
    obtain ⟨cs, -, -, -, D, hDF, hDX⟩ :=
      (P.cusp.collar b).exists_sublevel_diffeomorph_torus_Icc har hF hreg hr hXa hbdG
    let := cs
    exact isPreconnected_lt_interior_BCG6K D D.continuous D.surjective hDF hDX
      (by linarith) le_rfl (fun y hy => not_isInteriorPoint_of_mem_component_BCG6K P b hy)
      (fun y hy hint => hbdG y ((W.model.isInteriorPoint_or_isBoundaryPoint y).resolve_left hint)
        hy)
  have hGc : Continuous G := (P.contMDiff_coreLevel_BCG6K b hu).continuous
  have hFc : Continuous (P.level b) := (P.contMDiff_level b).continuous
  have hopen : ∀ (f : W.Carrier → ℝ), Continuous f →
      IsOpen {x : W.pieceInterior ⊤ | f x < 40} ∧ IsOpen {x : W.pieceInterior ⊤ | 40 < f x} :=
    fun f hf => ⟨isOpen_lt (hf.comp continuous_subtype_val) continuous_const,
      isOpen_lt continuous_const (hf.comp continuous_subtype_val)⟩
  have hdisj : ∀ f : W.Carrier → ℝ, Disjoint {x : W.pieceInterior ⊤ | f x < 40}
      {x : W.pieceInterior ⊤ | 40 < f x} := fun f => by
    rw [Set.disjoint_left]
    intro x h1 h2
    change f _ < 40 at h1
    change 40 < f _ at h2
    linarith
  -- `Φ` maps the lower side onto the lower side
  have hfwd : Φ '' {x : W.pieceInterior ⊤ | P.level b x < 40} ⊆
      {x : W.pieceInterior ⊤ | G x < 40} := by
    refine (hA₀.image _ Φ.continuous.continuousOn).subset_left_of_subset_union
      (hopen G hGc).1 (hopen G hGc).2 (hdisj G) ?_ ⟨x₀, ⟨x₀, ?_, hΦx₀⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      rcases lt_trichotomy (G (Φ x)) 40 with h | h | h
      · exact Or.inl h
      · exfalso
        have hmem : Φ x ∈ Φ '' {x : W.pieceInterior ⊤ | P.level b x = 40} := by
          rw [hL]
          exact h
        obtain ⟨y, hy, hyx⟩ := hmem
        rw [Φ.injective hyx] at hy
        change P.level b _ = 40 at hy
        change P.level b _ < 40 at hx
        linarith
      · exact Or.inr h
    · change P.level b _ < 40
      linarith
    · change G _ < 40
      rw [hG₀]
      linarith
  have hbwd : Φ.symm '' {x : W.pieceInterior ⊤ | G x < 40} ⊆
      {x : W.pieceInterior ⊤ | P.level b x < 40} := by
    have hΦsx₀ : Φ.symm x₀ = x₀ := by
      calc Φ.symm x₀ = Φ.symm (Φ x₀) := by rw [hΦx₀]
        _ = x₀ := Φ.symm_apply_apply x₀
    refine (hA₁.image _ Φ.symm.continuous.continuousOn).subset_left_of_subset_union
      (hopen _ hFc).1 (hopen _ hFc).2 (hdisj _) ?_ ⟨x₀, ⟨x₀, ?_, hΦsx₀⟩, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      rcases lt_trichotomy (P.level b (Φ.symm y)) 40 with h | h | h
      · exact Or.inl h
      · exfalso
        have hmem : Φ (Φ.symm y) ∈ Φ '' {x : W.pieceInterior ⊤ | P.level b x = 40} :=
          ⟨_, h, rfl⟩
        rw [hL, Φ.apply_symm_apply] at hmem
        change G _ = 40 at hmem
        change G _ < 40 at hy
        linarith
      · exact Or.inr h
    · change G _ < 40
      rw [hG₀]
      linarith
    · change P.level b _ < 40
      linarith
  have hsides : Φ '' {x : W.pieceInterior ⊤ | P.level b x < 40} =
      {x : W.pieceInterior ⊤ | G x < 40} := by
    refine Subset.antisymm hfwd fun y hy => ⟨Φ.symm y, hbwd ⟨y, hy, rfl⟩, Φ.apply_symm_apply y⟩
  have hsub : Φ '' {x : W.pieceInterior ⊤ | P.level b x ≤ 40} =
      {x : W.pieceInterior ⊤ | G x ≤ 40} := by
    have h1 : {x : W.pieceInterior ⊤ | P.level b x ≤ 40} =
        {x : W.pieceInterior ⊤ | P.level b x < 40} ∪
          {x : W.pieceInterior ⊤ | P.level b x = 40} := by
      ext x
      simp only [mem_union, mem_ofPred_eq]
      exact le_iff_lt_or_eq
    have h2 : {x : W.pieceInterior ⊤ | G x ≤ 40} =
        {x : W.pieceInterior ⊤ | G x < 40} ∪ {x : W.pieceInterior ⊤ | G x = 40} := by
      ext x
      simp only [mem_union, mem_ofPred_eq]
      exact le_iff_lt_or_eq
    rw [h1, h2, image_union, hsides, hL]
  have hcomp : ∀ S : Set (W.pieceInterior ⊤), (fun x => (Φ x : W.Carrier)) '' S =
      Subtype.val '' (Φ '' S) := fun S => by
    rw [← image_comp]
    rfl
  refine ⟨K', Φ, hK'c, hK'N, fun x hx => hid 0 1 x hx, ?_, ?_⟩
  · rw [hcomp, hsub, P.cuspCore_eq_BCG6K hεd hBI hBFM]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
    · rintro ⟨hy, hyW⟩
      exact ⟨⟨y, hyW⟩, hy, rfl⟩
  · rw [hcomp, hL]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [P.cuspFront_eq_BCG6K hεd hBI hBFM]
      exact hx
    · intro hy
      obtain ⟨-, hint⟩ := P.mem_strip_of_mem_front_BCG6K hεd hBI hy
      rw [P.cuspFront_eq_BCG6K hεd hBI hBFM] at hy
      exact ⟨⟨y, mem_pieceInterior_of_isInteriorPoint_BCG6K hint⟩, hy, rfl⟩

end BoundaryCollarPacket

end Interior

end DifferentialGeometry.Geometry.Collapse
