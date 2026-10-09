import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreLevel
import DifferentialGeometry.Topology.Morse.Attachment.ModelCell
import DifferentialGeometry.Topology.Manifold.ChartDisk.Construction
import DifferentialGeometry.Topology.Ehresmann.SideBoundaryInterval

/-!
# BCG06, G3: the whole inner subgraph and the global frontier (lane BCG6-K)

Draft 61 §4.2–§4.3, disposition D61-9. KERNEL form (premises (BI), (BD), (BFM) of the design
note `docs/geometrization/chapter14/design-bcg06-whole-core-20261005.md` §0).

Route (recorded deviation from the draft's flow-line wording): no flow lines and no implicit
function graph. The height-graph move is a modification of the KEPT level function of the
retained inner collar inside the strip `38.5 < η_b < 41.5` of the original band,
`G := level_b + band.indicator (κ(η_b) (u - η_b))` (`coreLevel_BCG6K`), `κ = 1` on
`[39.5, 40.5]`, `κ = 0` off `(38.5, 41.5)`, `|κ'| ≤ 80`; `G = level_b` near `∂_b W`.

* `coreLevel_cases_BCG6K`: at EVERY point of `W` either `G < 40` and the point is in the core and
  not in the front, or `G > 40` and it is in neither, or it is a strip point with
  `39.9 < η_b < 40.1`, `v = 1`, `G = u` (the GLOBAL marker division (Loc) excludes remote sheets,
  `N₃₅` covers height `≤ 33`, the plateau `32 ≤ η_b ≤ 39.9` is filled by the marked branch);
* `cuspCore_eq_BCG6K`: `C_b = {G ≤ 40}` — the whole inner subgraph; `cuspFront_eq_BCG6K`:
  `H_b = {G = 40}`;
* `contMDiff_coreLevel_BCG6K`, `mfderiv_coreLevel_ne_zero_BCG6K` (no critical point on
  `{G ≤ 40}`: the kept certificate off the strip, the height-unit vector on it),
  `coreLevel_eq_levelBase_BCG6K` (`G = a` on `∂_b W`), `mem_component_of_isBoundaryPoint_BCG6K`,
  `exists_coreLevel_eq_forty_BCG6K`;
* `frontier_cuspCore_BCG6K`: the RELATIVE frontier of `C_b` in `W` is `H_b` (Fermat at the
  interior front points).
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

section Helpers

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

theorem mvfderiv_congr_BCG6K {f f₁ : M → ℝ} {x : M} (h : f₁ =ᶠ[𝓝 x] f) :
    mvfderiv I f₁ x = mvfderiv I f x := by
  unfold mvfderiv
  rw [h.mfderiv_eq]
  rfl

theorem mfderiv_ne_zero_of_mvfderiv_BCG6K {f : M → ℝ} {x : M} {w : TangentSpace I x}
    (hw : mvfderiv I f x w ≠ 0) : mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 := by
  intro h
  apply hw
  unfold mvfderiv
  rw [h]
  rfl

theorem mvfderiv_ne_zero_iff_BCG6K {f : M → ℝ} {x : M} :
    mvfderiv I f x ≠ 0 ↔ mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 := by
  constructor
  · intro h h0
    apply h
    unfold mvfderiv
    rw [h0]
    ext v
    rfl
  · intro h h0
    apply h
    ext v
    exact congrArg (fun L => L v) h0

/-- Zero extension of a real function vanishing on `O \ T` (`T ⊆ O` closed, `O` open). -/
theorem contMDiff_indicator_of_eq_zero_BCG6K {O T : Set M} {f : M → ℝ} (hO : IsOpen O)
    (hT : IsClosed T) (hTO : T ⊆ O) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hzero : ∀ x ∈ O, x ∉ T → f x = 0) : ContMDiff I 𝓘(ℝ, ℝ) ∞ (O.indicator f) := by
  have hsupp : tsupport (O.indicator f) ⊆ T := by
    apply closure_minimal _ hT
    intro x hx
    by_contra hxT
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO]; exact hzero x hxO hxT)
    · exact hx (indicator_of_notMem hxO _)
  apply contMDiff_of_tsupport
  intro x hx
  have hxO : x ∈ O := hTO (hsupp hx)
  apply (hf x).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy _

end Helpers

section Cutoff

/-- The strip cutoff `κ(t) = s(t - 38.5) s(41.5 - t)`, `s = Real.smoothTransition`. -/
def coreCutoff_BCG6K (t : ℝ) : ℝ :=
  Real.smoothTransition (t - 77 / 2) * Real.smoothTransition (83 / 2 - t)

theorem contDiff_coreCutoff_BCG6K : ContDiff ℝ ∞ coreCutoff_BCG6K :=
  (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

theorem coreCutoff_nonneg_BCG6K (t : ℝ) : 0 ≤ coreCutoff_BCG6K t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

theorem coreCutoff_le_one_BCG6K (t : ℝ) : coreCutoff_BCG6K t ≤ 1 := by
  have h1 := Real.smoothTransition.le_one (t - 77 / 2)
  have h2 := Real.smoothTransition.le_one (83 / 2 - t)
  have h3 := Real.smoothTransition.nonneg (t - 77 / 2)
  have h4 := Real.smoothTransition.nonneg (83 / 2 - t)
  rw [coreCutoff_BCG6K]
  nlinarith

theorem coreCutoff_eq_zero_of_le_BCG6K {t : ℝ} (ht : t ≤ 77 / 2) : coreCutoff_BCG6K t = 0 := by
  rw [coreCutoff_BCG6K, Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

theorem coreCutoff_eq_zero_of_ge_BCG6K {t : ℝ} (ht : 83 / 2 ≤ t) : coreCutoff_BCG6K t = 0 := by
  rw [coreCutoff_BCG6K, Real.smoothTransition.zero_of_nonpos (x := 83 / 2 - t) (by linarith),
    mul_zero]

theorem coreCutoff_eq_one_BCG6K {t : ℝ} (h1 : 79 / 2 ≤ t) (h2 : t ≤ 81 / 2) :
    coreCutoff_BCG6K t = 1 := by
  rw [coreCutoff_BCG6K, Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

theorem coreCutoff_mem_strip_BCG6K {t : ℝ} (h : coreCutoff_BCG6K t ≠ 0) :
    77 / 2 < t ∧ t < 83 / 2 := by
  constructor
  · by_contra h'
    exact h (coreCutoff_eq_zero_of_le_BCG6K (not_lt.mp h'))
  · by_contra h'
    exact h (coreCutoff_eq_zero_of_ge_BCG6K (not_lt.mp h'))

theorem deriv_smoothTransition_nonneg_BCG6K (x : ℝ) : 0 ≤ deriv Real.smoothTransition x := by
  rcases le_or_gt x 0 with h0 | h0
  · rw [DifferentialGeometry.Topology.Morse.CellAttachment.Real.smoothTransition_deriv_zero_of_nonpos
      x h0]
  rcases le_or_gt 1 x with h1 | h1
  · rw [DifferentialGeometry.Topology.Morse.CellAttachment.Real.smoothTransition_deriv_zero_of_one_le
      x h1]
  exact (DifferentialGeometry.Topology.smoothTransition_deriv_pos h0 h1).le

theorem hasDerivAt_smoothTransition_BCG6K (x : ℝ) :
    HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero).differentiableAt.hasDerivAt

/-- `|κ'| ≤ 80`. -/
theorem abs_deriv_coreCutoff_le_BCG6K (t : ℝ) : |deriv coreCutoff_BCG6K t| ≤ 80 := by
  have h1 : HasDerivAt (fun t => Real.smoothTransition (t - 77 / 2))
      (deriv Real.smoothTransition (t - 77 / 2)) t :=
    HasDerivAt.comp_sub_const t (77 / 2) (hasDerivAt_smoothTransition_BCG6K (t - 77 / 2))
  have h2 : HasDerivAt (fun t => Real.smoothTransition (83 / 2 - t))
      (-deriv Real.smoothTransition (83 / 2 - t)) t :=
    HasDerivAt.comp_const_sub (83 / 2) t (hasDerivAt_smoothTransition_BCG6K (83 / 2 - t))
  have hd : deriv coreCutoff_BCG6K t = deriv Real.smoothTransition (t - 77 / 2) *
      Real.smoothTransition (83 / 2 - t) + Real.smoothTransition (t - 77 / 2) *
        (-deriv Real.smoothTransition (83 / 2 - t)) := (h1.mul h2).deriv
  rw [hd]
  have a1 := deriv_smoothTransition_nonneg_BCG6K (t - 77 / 2)
  have a2 := deriv_smoothTransition_nonneg_BCG6K (83 / 2 - t)
  have b1 := DifferentialGeometry.Topology.Morse.CellAttachment.Real.smoothTransition_deriv_le_forty
    (t - 77 / 2)
  have b2 := DifferentialGeometry.Topology.Morse.CellAttachment.Real.smoothTransition_deriv_le_forty
    (83 / 2 - t)
  have c1 := Real.smoothTransition.nonneg (t - 77 / 2)
  have c2 := Real.smoothTransition.nonneg (83 / 2 - t)
  have d1 := Real.smoothTransition.le_one (t - 77 / 2)
  have d2 := Real.smoothTransition.le_one (83 / 2 - t)
  rw [abs_le]
  constructor <;> nlinarith

end Cutoff

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ}

namespace BoundaryCollarPacket

variable (P : BoundaryCollarPacket W g K A w₀ ε) (b : Fin P.cusp.count)

/-- The strip correction `band.indicator (κ(η_b) (u - η_b))` of the height-graph move. -/
def coreCorrection_BCG6K (u : W.Carrier → ℝ) : W.Carrier → ℝ :=
  (P.collarBand_BAUGA b).indicator
    (fun x => coreCutoff_BCG6K (P.height b x) * (u x - P.height b x))

/-- **The modified level** `G = level_b + band.indicator (κ(η_b) (u - η_b))`. -/
def coreLevel_BCG6K (u : W.Carrier → ℝ) (x : W.Carrier) : ℝ :=
  P.level b x + P.coreCorrection_BCG6K b u x

/-- The open strip `e(2 < z < 95)` of the band, where `level_b = η_b`. -/
def coreStrip_BCG6K : Set W.Carrier :=
  (P.cusp.collar b).toFun '' {p : CuspHalfSpace | 2 < p.2.val 0 ∧ p.2.val 0 < 95}

theorem isOpen_coreStrip_BCG6K : IsOpen (P.coreStrip_BCG6K b) :=
  (P.cusp.collar b).isOpen_image ((isOpen_lt continuous_const continuous_cusp_height).inter
    (isOpen_lt continuous_cusp_height continuous_const))
    fun p hp => cusp_mem_cuspDomain_of_le (b := 95) (by norm_num [cuspDepth]) hp.2.le

theorem coreStrip_subset_band_BCG6K : P.coreStrip_BCG6K b ⊆ P.collarBand_BAUGA b := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p, ⟨hp.1, by linarith [hp.2]⟩, rfl⟩

/-- On the strip, `G = η_b + κ(η_b) (u - η_b)`. -/
theorem coreLevel_eq_on_strip_BCG6K (u : W.Carrier → ℝ) {x : W.Carrier}
    (hx : x ∈ P.coreStrip_BCG6K b) :
    P.coreLevel_BCG6K b u x =
      P.height b x + coreCutoff_BCG6K (P.height b x) * (u x - P.height b x) := by
  have hband := P.coreStrip_subset_band_BCG6K b hx
  obtain ⟨p, hp, rfl⟩ := hx
  rw [coreLevel_BCG6K, coreCorrection_BCG6K, indicator_of_mem hband,
    P.level_eq_height b p hp.1.le hp.2.le]

/-- The support of the correction lies in `K = e(37.5 ≤ z ≤ 42.5) ∩ {38.5 ≤ η_b ≤ 41.5}`. -/
theorem tsupport_coreCorrection_subset_BCG6K (u : W.Carrier → ℝ) :
    tsupport (P.coreCorrection_BCG6K b u) ⊆
      (P.cusp.collar b).toFun '' {p : CuspHalfSpace | 75 / 2 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 85 / 2} ∩
        {x | 77 / 2 ≤ P.height b x ∧ P.height b x ≤ 83 / 2} := by
  refine closure_minimal ?_ (((P.cusp.collar b).isCompact_image_band
    (by norm_num [cuspDepth])).isClosed.inter ((isClosed_le continuous_const
      (P.contMDiff_height b).continuous).inter (isClosed_le (P.contMDiff_height b).continuous
        continuous_const)))
  intro x hx
  rw [mem_support] at hx
  by_cases hxb : x ∈ P.collarBand_BAUGA b
  · rw [coreCorrection_BCG6K, indicator_of_mem hxb] at hx
    have hκ := coreCutoff_mem_strip_BCG6K (left_ne_zero_of_mul hx)
    obtain ⟨p, hp, rfl⟩ := hxb
    have hpd : p ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
    have hc := abs_lt.mp (P.height_contract b p hpd hp.1.le hp.2.le).1
    have hε1 := P.tolerance_le_one
    exact ⟨⟨p, ⟨by linarith, by linarith⟩, rfl⟩, hκ.1.le, hκ.2.le⟩
  · rw [coreCorrection_BCG6K, indicator_of_notMem hxb] at hx
    exact (hx rfl).elim

theorem closedStrip_subset_coreStrip_BCG6K :
    (P.cusp.collar b).toFun '' {p : CuspHalfSpace | 75 / 2 ≤ p.2.val 0 ∧ p.2.val 0 ≤ 85 / 2} ⊆
      P.coreStrip_BCG6K b := by
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p, ⟨by linarith [hp.1], by linarith [hp.2]⟩, rfl⟩

/-- `G` is smooth on `W`. -/
theorem contMDiff_coreLevel_BCG6K {u : W.Carrier → ℝ} (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u) :
    ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (P.coreLevel_BCG6K b u) := by
  have hf : ContMDiff W.model 𝓘(ℝ, ℝ) ∞
      (fun x => coreCutoff_BCG6K (P.height b x) * (u x - P.height b x)) :=
    (contDiff_coreCutoff_BCG6K.contMDiff.comp (P.contMDiff_height b)).mul
      (hu.sub (P.contMDiff_height b))
  have hcorr : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (P.coreCorrection_BCG6K b u) := by
    refine contMDiff_indicator_of_eq_zero_BCG6K (P.isOpen_collarBand_BAUGA b)
      ((P.cusp.collar b).isCompact_image_band (a := 75 / 2) (b := 85 / 2)
        (by norm_num [cuspDepth])).isClosed
      ((P.closedStrip_subset_coreStrip_BCG6K b).trans (P.coreStrip_subset_band_BCG6K b)) hf ?_
    intro x hxO hxT
    obtain ⟨p, hp, rfl⟩ := hxO
    have hpd : p ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
    have hc := abs_lt.mp (P.height_contract b p hpd hp.1.le hp.2.le).1
    have hε1 := P.tolerance_le_one
    have hz : p.2.val 0 < 75 / 2 ∨ 85 / 2 < p.2.val 0 := by
      by_contra h
      simp only [not_or, not_lt] at h
      exact hxT ⟨p, ⟨h.1, h.2⟩, rfl⟩
    rcases hz with hz | hz
    · change coreCutoff_BCG6K _ * _ = 0
      rw [coreCutoff_eq_zero_of_le_BCG6K (by linarith), zero_mul]
    · change coreCutoff_BCG6K _ * _ = 0
      rw [coreCutoff_eq_zero_of_ge_BCG6K (by linarith), zero_mul]
  exact (P.contMDiff_level b).add hcorr


/-- A collar point of height `≥ 35.01` is not in `N₃₅(∂_b W)`. -/
theorem notMem_cuspNbhd35_BCG6K {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (hz : 3501 / 100 ≤ p.2.val 0) : (P.cusp.collar b).toFun p ∉ P.cuspNbhd35_BCG6K b := by
  intro hN
  obtain ⟨q, hq, hqx, hqz⟩ := P.exists_height_lt_of_mem_cuspNbhd35_BCG6K b hN
  have h := P.collar_bands_disjoint_BCG6K b hq hp hqx
  rw [h] at hqz
  linarith

/-- Off the band and off `e(z ≤ 2)` the level function is `> 90`. -/
theorem level_gt_ninety_of_notMem_BCG6K {x : W.Carrier} (hband : x ∉ P.collarBand_BAUGA b)
    (hlow : ¬ ∃ p ∈ cuspDomain, p.2.val 0 ≤ 2 ∧ (P.cusp.collar b).toFun p = x) :
    90 < P.level b x := by
  by_contra h
  have hx : x ∈ {y | P.level b y ≤ 90} := not_lt.mp h
  rw [P.level_sublevel_eq b] at hx
  obtain ⟨q, ⟨hqd, hq⟩, hqx⟩ := hx
  rcases hq with hz | ⟨h98, hη⟩
  · exact hlow ⟨q, hqd, hz, hqx⟩
  rcases le_or_gt (q.2.val 0) 2 with hz2 | hz2
  · exact hlow ⟨q, hqd, hz2, hqx⟩
  rcases h98.lt_or_eq with h98' | h98'
  · exact hband ⟨q, ⟨hz2, h98'⟩, hqx⟩
  · have hc := abs_lt.mp (P.height_contract b q hqd hz2.le h98).1
    have hε1 := P.tolerance_le_one
    rw [h98'] at hc
    linarith

/-- A band point of height `z > 95` has level `> 90`. -/
theorem level_gt_ninety_of_height_gt_BCG6K {p : CuspHalfSpace} (hp : p ∈ cuspDomain)
    (h95 : 95 < p.2.val 0) (h98 : p.2.val 0 < 98) :
    90 < P.level b ((P.cusp.collar b).toFun p) := by
  by_contra h
  have hx : (P.cusp.collar b).toFun p ∈ {y | P.level b y ≤ 90} := not_lt.mp h
  rw [P.level_sublevel_eq b] at hx
  obtain ⟨q, ⟨hqd, hq⟩, hqx⟩ := hx
  have hqp := P.collar_bands_disjoint_BCG6K b hqd hp hqx
  subst hqp
  have hc := abs_lt.mp (P.height_contract b q hp (by linarith) h98.le).1
  have hε1 := P.tolerance_le_one
  rcases hq with hz | ⟨-, hη⟩
  · linarith
  · linarith

variable {b}

/-- **The five-region partition** (draft 61 §4.3, review 65 M2). At EVERY point of `W`, with the
BCG04 errors (BI) and the BCG05 marker (BFM): either `G < 40` and the point is in the core, not in
the front, and lies in the band or in `e(z ≤ 2)`; or `G > 40` and it is in neither; or it is a
strip point with `39.9 < η_b < 40.1`, `v = 1`, `G = u`. -/
theorem coreLevel_cases_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ} {εd : ℝ}
    (hεd : εd < 1 / 1000000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1) (x : W.Carrier) :
    (P.coreLevel_BCG6K b (u b) x < 40 ∧ x ∈ P.cuspCore_BCG6K b u v ∧
        x ∉ P.cuspFront_BCG6K b u v ∧
        (x ∈ P.collarBand_BAUGA b ∨
          ∃ p ∈ cuspDomain, p.2.val 0 ≤ 2 ∧ (P.cusp.collar b).toFun p = x)) ∨
      (40 < P.coreLevel_BCG6K b (u b) x ∧ x ∉ P.cuspCore_BCG6K b u v ∧
        x ∉ P.cuspFront_BCG6K b u v) ∨
      (x ∈ P.collarBand_BAUGA b ∧ 399 / 10 < P.height b x ∧ P.height b x < 401 / 10 ∧
        v b x = 1 ∧ P.coreLevel_BCG6K b (u b) x = u b x ∧
        (x ∈ P.cuspCore_BCG6K b u v ↔ u b x ≤ 40) ∧
        (x ∈ P.cuspFront_BCG6K b u v ↔ u b x = 40)) := by
  have hε1 := P.tolerance_le_one
  have hεd0 : 0 ≤ εd := (abs_nonneg _).trans (hBI x).1.le
  have hloc := loc_constant_lt_BCG6K hεd
  have hmarked : ∀ y, (9 / 10 : ℝ) ≤ v b y → u b y ≤ 40 * v b y →
      y ∈ P.collarBand_BAUGA b ∧ P.height b y < 40 + 1 / 1000 := fun y h9 hle =>
    ⟨(P.mem_collarBand_of_marker_BCG6K b (by linarith) (hBI y).2 h9).2.1,
      by linarith [P.height_lt_of_marked_BCG6K b (by linarith) (hBI y).1 (hBI y).2 h9 hle]⟩
  have hfront : x ∈ P.cuspFront_BCG6K b u v →
      x ∈ P.collarBand_BAUGA b ∧ |P.height b x - 40| < 1 / 1000 :=
    P.front_height_BCG6K b hεd (hBI x).1 (hBI x).2
  by_cases hband : x ∈ P.collarBand_BAUGA b
  · have hband' := hband
    obtain ⟨p, hp, rfl⟩ := hband'
    have hpd : p ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
    have hc := abs_lt.mp (P.height_contract b p hpd hp.1.le hp.2.le).1
    have hNfar := P.notMem_cuspNbhd35_BCG6K b hpd
    have hQ : P.coreCorrection_BCG6K b (u b) ((P.cusp.collar b).toFun p) =
        coreCutoff_BCG6K (P.height b ((P.cusp.collar b).toFun p)) *
          (u b ((P.cusp.collar b).toFun p) - P.height b ((P.cusp.collar b).toFun p)) :=
      indicator_of_mem hband _
    set η := P.height b ((P.cusp.collar b).toFun p) with hη
    by_cases hz95 : p.2.val 0 ≤ 95
    · have hG : P.coreLevel_BCG6K b (u b) ((P.cusp.collar b).toFun p) =
          η + coreCutoff_BCG6K η * (u b ((P.cusp.collar b).toFun p) - η) := by
        rw [coreLevel_BCG6K, hQ, P.level_eq_height b p hp.1.le hz95]
      rcases lt_or_ge η 32 with h32 | h32
      · have hκ : coreCutoff_BCG6K η = 0 := coreCutoff_eq_zero_of_le_BCG6K (by linarith)
        left
        refine ⟨by rw [hG, hκ]; linarith,
          Or.inl (P.mem_cuspNbhd35_of_mem_band_BCG6K b hband h32), fun hH => ?_, Or.inl hband⟩
        have := (hfront hH).2
        linarith [(abs_lt.mp this).1]
      rcases le_or_gt η 78 with h78 | h78
      · have hsafe : (P.cusp.collar b).toFun p ∈ P.safeBand_BAUGA b := ⟨hband, h32, h78⟩
        have hv1 := hBFM _ hsafe
        have hblk := P.block_eq_of_mem_safeBand_BAUGA b hsafe
        have hu := (hBI ((P.cusp.collar b).toFun p)).1
        rw [hblk] at hu
        have hu' := abs_lt.mp hu
        have hκ0 := coreCutoff_nonneg_BCG6K η
        have hκ1 := coreCutoff_le_one_BCG6K η
        rcases le_or_gt η (399 / 10) with h399 | h399
        · left
          refine ⟨?_, Or.inr ⟨by rw [hv1]; norm_num, by rw [hv1]; linarith⟩, fun hH => ?_,
            Or.inl hband⟩
          · rw [hG]
            nlinarith
          · have := (hfront hH).2
            linarith [(abs_lt.mp this).1]
        rcases lt_or_ge η (401 / 10) with h401 | h401
        · right; right
          have hκ : coreCutoff_BCG6K η = 1 := coreCutoff_eq_one_BCG6K (by linarith) (by linarith)
          have hz : 3501 / 100 ≤ p.2.val 0 := by linarith
          refine ⟨hband, h399, h401, hv1, by rw [hG, hκ]; ring, ?_, ?_⟩
          · constructor
            · rintro (hN | ⟨-, hle⟩)
              · exact absurd hN (hNfar hz)
              · rw [hv1] at hle
                linarith
            · intro hle
              exact Or.inr ⟨by rw [hv1]; norm_num, by rw [hv1]; linarith⟩
          · constructor
            · rintro ⟨-, heq⟩
              rw [hv1] at heq
              linarith
            · intro heq
              exact ⟨by rw [hv1]; norm_num, by rw [hv1]; linarith⟩
        · right; left
          refine ⟨by rw [hG]; nlinarith, ?_, fun hH => ?_⟩
          · rintro (hN | ⟨h9, hle⟩)
            · exact hNfar (by linarith) hN
            · have := (hmarked _ h9 hle).2
              linarith
          · have := (hfront hH).2
            linarith [(abs_lt.mp this).2]
      · have hκ : coreCutoff_BCG6K η = 0 := coreCutoff_eq_zero_of_ge_BCG6K (by linarith)
        right; left
        refine ⟨by rw [hG, hκ]; linarith, ?_, fun hH => ?_⟩
        · rintro (hN | ⟨h9, hle⟩)
          · exact hNfar (by linarith) hN
          · have := (hmarked _ h9 hle).2
            linarith
        · have := (hfront hH).2
          linarith [(abs_lt.mp this).2]
    · have h95 : 95 < p.2.val 0 := not_le.mp hz95
      have hκ : coreCutoff_BCG6K η = 0 := coreCutoff_eq_zero_of_ge_BCG6K (by linarith)
      have hlev := P.level_gt_ninety_of_height_gt_BCG6K b hpd h95 hp.2
      right; left
      refine ⟨by rw [coreLevel_BCG6K, hQ, hκ, zero_mul, add_zero]; linarith, ?_, fun hH => ?_⟩
      · rintro (hN | ⟨h9, hle⟩)
        · exact hNfar (by linarith) hN
        · have := (hmarked _ h9 hle).2
          linarith
      · have := (hfront hH).2
        linarith [(abs_lt.mp this).2]
  · have hQ0 : P.coreCorrection_BCG6K b (u b) x = 0 := indicator_of_notMem hband _
    by_cases hlow : ∃ p ∈ cuspDomain, p.2.val 0 ≤ 2 ∧ (P.cusp.collar b).toFun p = x
    · have hlow' := hlow
      obtain ⟨p, hpd, hz2, rfl⟩ := hlow'
      have hl39 := P.level_lt_of_height_le_two_BCG6K b hpd hz2
      have hG : P.coreLevel_BCG6K b (u b) ((P.cusp.collar b).toFun p) < 40 := by
        rw [coreLevel_BCG6K, hQ0, add_zero]
        linarith
      left
      refine ⟨hG,
        Or.inl (P.mem_cuspNbhd35_of_height_le_BCG6K b hpd (by linarith)),
        fun hH => hband (hfront hH).1, Or.inr hlow⟩
    · right; left
      have hlev := P.level_gt_ninety_of_notMem_BCG6K b hband hlow
      have hG : 40 < P.coreLevel_BCG6K b (u b) x := by
        rw [coreLevel_BCG6K, hQ0, add_zero]
        linarith
      refine ⟨hG, ?_, fun hH => hband (hfront hH).1⟩
      rintro (hN | ⟨h9, hle⟩)
      · obtain ⟨q, hq, hqx, hqz⟩ := P.exists_height_lt_of_mem_cuspNbhd35_BCG6K b hN
        rcases le_or_gt (q.2.val 0) 2 with h2 | h2
        · exact hlow ⟨q, hq, h2, hqx⟩
        · exact hband ⟨q, ⟨h2, by linarith⟩, hqx⟩
      · exact hband (hmarked _ h9 hle).1

/-- **The whole inner subgraph (BCG06.a)**: `C_b = {G ≤ 40}` globally on `W`. -/
theorem cuspCore_eq_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ} {εd : ℝ}
    (hεd : εd < 1 / 1000000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1) :
    P.cuspCore_BCG6K b u v = {x | P.coreLevel_BCG6K b (u b) x ≤ 40} := by
  ext x
  rcases P.coreLevel_cases_BCG6K hεd hBI hBFM x with
    ⟨hG, hC, -, -⟩ | ⟨hG, hC, -⟩ | ⟨-, -, -, -, hG, hC, -⟩
  · exact ⟨fun _ => hG.le, fun _ => hC⟩
  · exact ⟨fun h => absurd h hC, fun h => absurd h (not_le.mpr hG)⟩
  · rw [hC]
    change _ ↔ P.coreLevel_BCG6K b (u b) x ≤ 40
    rw [hG]

/-- **The global front (BCG06.b)**: `H_b = {G = 40}` globally on `W`. -/
theorem cuspFront_eq_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ} {εd : ℝ}
    (hεd : εd < 1 / 1000000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1) :
    P.cuspFront_BCG6K b u v = {x | P.coreLevel_BCG6K b (u b) x = 40} := by
  ext x
  rcases P.coreLevel_cases_BCG6K hεd hBI hBFM x with
    ⟨hG, -, hH, -⟩ | ⟨hG, -, hH⟩ | ⟨-, -, -, -, hG, -, hH⟩
  · exact ⟨fun h => absurd h hH, fun h => absurd h hG.ne⟩
  · exact ⟨fun h => absurd h hH, fun h => absurd h hG.ne'⟩
  · rw [hH]
    change _ ↔ P.coreLevel_BCG6K b (u b) x = 40
    rw [hG]

/-- The front lies in the open strip of the band, at interior points of `W`. -/
theorem mem_strip_of_mem_front_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ} {εd : ℝ}
    (hεd : εd < 1 / 1000000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    {x : W.Carrier} (hx : x ∈ P.cuspFront_BCG6K b u v) :
    x ∈ P.coreStrip_BCG6K b ∧ W.model.IsInteriorPoint x := by
  obtain ⟨hband, hloc⟩ := P.front_height_BCG6K b hεd (hBI x).1 (hBI x).2 hx
  obtain ⟨p, hp, rfl⟩ := hband
  have hpd : p ∈ cuspDomain :=
    cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
  have hc := abs_lt.mp (P.height_contract b p hpd hp.1.le hp.2.le).1
  have hε1 := P.tolerance_le_one
  have hl := abs_lt.mp hloc
  exact ⟨⟨p, ⟨hp.1, by linarith⟩, rfl⟩,
    isInteriorPoint_of_height_pos_BCG6K (P.cusp.collar b) hpd (by linarith [hp.1])⟩

variable (b) in
/-- `G = a` on `∂_b W` (the correction vanishes off the band). -/
theorem coreLevel_eq_levelBase_BCG6K (u : W.Carrier → ℝ) {x : W.Carrier}
    (hx : x ∈ P.cusp.component b) : P.coreLevel_BCG6K b u x = P.levelBase b := by
  have hnot : x ∉ P.collarBand_BAUGA b := by
    obtain ⟨t, rfl⟩ := (Set.ext_iff.mp (P.cusp.collar b).boundary_image x).mpr hx
    rintro ⟨q, hq, hqx⟩
    have hqd : q ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hq.2.le
    have h := P.collar_bands_disjoint_BCG6K b hqd (mem_cuspDomain_halfZero t) hqx
    have h0 : q.2.val 0 = 0 := by rw [h]; exact halfZero_val_zero
    linarith [hq.1]
  rw [coreLevel_BCG6K, coreCorrection_BCG6K, indicator_of_notMem hnot, add_zero,
    P.level_eq_levelBase_of_mem_component_BCG6K b hx]

/-- The boundary points of `W` in `{G ≤ 40}` lie in `∂_b W`. -/
theorem mem_component_of_isBoundaryPoint_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ}
    {εd : ℝ} (hεd : εd < 1 / 1000000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1) {x : W.Carrier}
    (hb : W.model.IsBoundaryPoint x) (hx : P.coreLevel_BCG6K b (u b) x ≤ 40) :
    x ∈ P.cusp.component b := by
  have hband_int : x ∈ P.collarBand_BAUGA b → False := by
    rintro ⟨p, hp, rfl⟩
    have hpd : p ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
    exact (W.model.isInteriorPoint_iff_not_isBoundaryPoint _).mp
      (isInteriorPoint_of_height_pos_BCG6K (P.cusp.collar b) hpd (by linarith [hp.1])) hb
  rcases P.coreLevel_cases_BCG6K hεd hBI hBFM x with
    ⟨-, -, -, hreg⟩ | ⟨hG, -⟩ | ⟨hband, -⟩
  · rcases hreg with hband | ⟨p, hpd, -, rfl⟩
    · exact (hband_int hband).elim
    · have hz := ((P.cusp.collar b).boundary_preimage hpd).mp hb
      rw [cusp_eq_halfZero_of_height_eq_zero hz]
      exact (Set.ext_iff.mp (P.cusp.collar b).boundary_image _).mp ⟨p.1, rfl⟩
  · linarith
  · exact (hband_int hband).elim

variable (b) in
/-- `G` attains the value `40` (intermediate values along `e(t₀, z)`, `30 ≤ z ≤ 50`). -/
theorem exists_coreLevel_eq_forty_BCG6K {u : W.Carrier → ℝ}
    (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u) : ∃ x, P.coreLevel_BCG6K b u x = 40 := by
  obtain ⟨θ₀⟩ := (inferInstance : Nonempty Torus)
  have hε1 := P.tolerance_le_one
  have hz : ∀ s : ℝ, 0 ≤ s → ((θ₀, halfSpaceOneLift s) : CuspHalfSpace).2.val 0 = s := by
    intro s hs
    change (halfSpaceOneLift s).1 0 = s
    rw [halfSpaceOneLift_val_zero, max_eq_left hs]
  -- the value of `G` at a strip point of height `s` away from the cutoff strip
  have hval : ∀ s : ℝ, 3 ≤ s → s ≤ 90 →
      |P.height b ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift s)) - s| < 1 ∧
      ((P.height b ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift s)) ≤ 77 / 2 ∨
          83 / 2 ≤ P.height b ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift s))) →
        P.coreLevel_BCG6K b u ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift s)) =
          P.height b ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift s))) := by
    intro s h3 h90
    have hzs := hz s (by linarith)
    have hd : ((θ₀, halfSpaceOneLift s) : CuspHalfSpace) ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 90) (by norm_num [cuspDepth]) (by rw [hzs]; exact h90)
    have hc := (P.height_contract b _ hd (by rw [hzs]; linarith) (by rw [hzs]; linarith)).1
    rw [hzs] at hc
    have hstrip : (P.cusp.collar b).toFun (θ₀, halfSpaceOneLift s) ∈ P.coreStrip_BCG6K b :=
      ⟨_, ⟨by rw [hzs]; linarith, by rw [hzs]; linarith⟩, rfl⟩
    refine ⟨hc.trans_le hε1, fun hout => ?_⟩
    rw [P.coreLevel_eq_on_strip_BCG6K b u hstrip]
    rcases hout with h | h
    · rw [coreCutoff_eq_zero_of_le_BCG6K h, zero_mul, add_zero]
    · rw [coreCutoff_eq_zero_of_ge_BCG6K h, zero_mul, add_zero]
  obtain ⟨h30a, h30b⟩ := hval 30 (by norm_num) (by norm_num)
  obtain ⟨h50a, h50b⟩ := hval 50 (by norm_num) (by norm_num)
  have h30 := abs_lt.mp h30a
  have h50 := abs_lt.mp h50a
  have hG30 := h30b (Or.inl (by linarith))
  have hG50 := h50b (Or.inr (by linarith))
  have hc1 : ContinuousOn (fun s : ℝ => ((θ₀, halfSpaceOneLift s) : CuspHalfSpace))
      (Icc 30 50) :=
    contMDiffOn_cuspVertical.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      fun s hs => ⟨mem_univ _, show (0 : ℝ) ≤ s by linarith [hs.1]⟩
  have hc2 : ContinuousOn (fun s : ℝ => (P.cusp.collar b).toFun (θ₀, halfSpaceOneLift s))
      (Icc 30 50) :=
    (P.cusp.collar b).contMDiffOn.continuousOn.comp hc1 fun s hs => by
      change ((θ₀, halfSpaceOneLift s) : CuspHalfSpace).2.val 0 < cuspDepth
      rw [hz s (by linarith [hs.1]), cuspDepth]
      linarith [hs.2]
  have hc3 : ContinuousOn
      (fun s : ℝ => P.coreLevel_BCG6K b u ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift s)))
      (Icc 30 50) := (P.contMDiff_coreLevel_BCG6K b hu).continuous.comp_continuousOn hc2
  have h40 : (40 : ℝ) ∈ Icc
      (P.coreLevel_BCG6K b u ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift 30)))
      (P.coreLevel_BCG6K b u ((P.cusp.collar b).toFun (θ₀, halfSpaceOneLift 50))) :=
    ⟨by rw [hG30]; linarith, by rw [hG50]; linarith⟩
  obtain ⟨s, -, hs⟩ := intermediate_value_Icc (by norm_num : (30 : ℝ) ≤ 50) hc3 h40
  exact ⟨_, hs⟩

variable (b) in
/-- **No critical point on `{G ≤ 40}`** (E6's `hreg`, review 65 M1): on the support of the
correction (the strip `K`) the height-unit vector gives `dG(w) ≥ 1 - 80 ε∂ - 1.01 c₃ > 0` under the
registered condition (R) `80 ε∂ + 1.02 c₃ < 1`; elsewhere `G = level_b` near the point and the kept
certificate (R3) applies. -/
theorem mfderiv_coreLevel_ne_zero_BCG6K (hε : ε ≤ 1 / 1000) {u : W.Carrier → ℝ}
    (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u) {εd c₃ : ℝ} (hc₃ : 0 ≤ c₃)
    (hR : 80 * εd + 102 / 100 * c₃ < 1)
    (hBIu : ∀ x ∈ P.safeBand_BAUGA b, |u x - (P.block b x).1| < εd)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w))
    {x : W.Carrier} (hx : P.coreLevel_BCG6K b u x ≤ 40) :
    mfderiv W.model 𝓘(ℝ, ℝ) (P.coreLevel_BCG6K b u) x ≠ 0 := by
  by_cases hxT : x ∈ tsupport (P.coreCorrection_BCG6K b u)
  · obtain ⟨hxK, h1, h2⟩ := P.tsupport_coreCorrection_subset_BCG6K b u hxT
    have hxS : x ∈ P.coreStrip_BCG6K b := P.closedStrip_subset_coreStrip_BCG6K b hxK
    have hband := P.coreStrip_subset_band_BCG6K b hxS
    have hsafe : x ∈ P.safeBand_BAUGA b := ⟨hband, by linarith, by linarith⟩
    have hux := hBIu x hsafe
    rw [P.block_eq_of_mem_safeBand_BAUGA b hsafe] at hux
    have hux' : |u x - P.height b x| < εd := hux
    have heq : P.coreLevel_BCG6K b u =ᶠ[𝓝 x]
        fun y => P.height b y + coreCutoff_BCG6K (P.height b y) * (u y - P.height b y) := by
      filter_upwards [(P.isOpen_coreStrip_BCG6K b).mem_nhds hxS] with y hy
      exact P.coreLevel_eq_on_strip_BCG6K b u hy
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
    have hκdiff : DifferentiableAt ℝ coreCutoff_BCG6K (P.height b x) :=
      (contDiff_coreCutoff_BCG6K.differentiable (by simp)) _
    change mvfderiv W.model (P.height b + (fun y => coreCutoff_BCG6K (P.height b y)) *
      (fun y => u y - P.height b y)) x w ≠ 0
    rw [mvfderiv_add hηd (hκd.mul hhd), add_apply,
      mvfderiv_mul hκd hhd, add_apply, smul_apply,
      smul_apply, smul_eq_mul, smul_eq_mul,
      DifferentialGeometry.Topology.Ehresmann.mvfderiv_comp_real hηd hκdiff w, hw1]
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
    apply ne_of_gt
    linarith
  · have hQ : P.coreCorrection_BCG6K b u =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hxT
    have heq : P.coreLevel_BCG6K b u =ᶠ[𝓝 x] P.level b := by
      filter_upwards [hQ] with y hy
      rw [coreLevel_BCG6K, hy, Pi.zero_apply, add_zero]
    have hQx : P.coreCorrection_BCG6K b u x = 0 := hQ.eq_of_nhds
    have hlev : P.level b x ≤ 90 := by
      have h : P.coreLevel_BCG6K b u x = P.level b x := by rw [coreLevel_BCG6K, hQx, add_zero]
      linarith
    rw [← mvfderiv_ne_zero_iff_BCG6K, mvfderiv_congr_BCG6K heq, mvfderiv_ne_zero_iff_BCG6K]
    exact P.mfderiv_level_ne_zero_BCG6K b hlev

/-- **The relative frontier (BCG06.b, review 65 M4)**: `frontier_W C_b = H_b`. -/
theorem frontier_cuspCore_BCG6K (hε : ε ≤ 1 / 1000) {u v : Fin P.cusp.count → W.Carrier → ℝ}
    (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u b)) {εd c₃ : ℝ} (hεd : εd < 1 / 1000000)
    (hc₃ : 0 ≤ c₃) (hR : 80 * εd + 102 / 100 * c₃ < 1)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u b y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w)) :
    frontier (P.cuspCore_BCG6K b u v) = P.cuspFront_BCG6K b u v := by
  have hGc : Continuous (P.coreLevel_BCG6K b (u b)) :=
    (P.contMDiff_coreLevel_BCG6K b hu).continuous
  have hfront := P.cuspFront_eq_BCG6K hεd hBI hBFM
  rw [P.cuspCore_eq_BCG6K hεd hBI hBFM]
  ext x
  constructor
  · intro hx
    have hxs : P.coreLevel_BCG6K b (u b) x ≤ 40 :=
      (isClosed_le hGc continuous_const).frontier_subset hx
    rw [hfront]
    by_contra hne
    have hlt : P.coreLevel_BCG6K b (u b) x < 40 := lt_of_le_of_ne hxs hne
    apply hx.2
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset ((isOpen_lt hGc continuous_const).mem_nhds hlt)
      fun y (hy : P.coreLevel_BCG6K b (u b) y < 40) =>
        (le_of_lt hy : P.coreLevel_BCG6K b (u b) y ≤ 40)
  · intro hx
    have hx40 : P.coreLevel_BCG6K b (u b) x = 40 := by
      rw [hfront] at hx
      exact hx
    obtain ⟨-, hint⟩ := P.mem_strip_of_mem_front_BCG6K hεd hBI hx
    have hreg := P.mfderiv_coreLevel_ne_zero_BCG6K b hε hu hc₃ hR (fun y _ => (hBI y).1) hBD
      (le_of_eq hx40)
    refine ⟨subset_closure (le_of_eq hx40), fun hI => ?_⟩
    obtain ⟨y, hy, hgt⟩ := exists_gt_of_mfderiv_ne_zero_BCG6K hint hreg
      (mem_interior_iff_mem_nhds.mp hI)
    change P.coreLevel_BCG6K b (u b) y ≤ 40 at hy
    linarith

end BoundaryCollarPacket

end DifferentialGeometry.Geometry.Collapse
