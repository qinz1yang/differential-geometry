import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryComplete

/-!
# The gradient bound and properness for the two-cone fold

Lane A5 (design `docs/geometrization/handoffs/20261004-design-a5-filled-pants-assembly.md`, §4,
with review 21 §4.4–§4.5). Every point of the fold domain is `FoldRel`-related to a point over the
doubled triangle with fibre coordinate in `[0, 1)` (`exists_foldRel_unit`), and `FoldRel` preserves
the pulled-back exhaustion near the first point (`exhaustFn_comp_eventuallyEq`). Over the doubled
triangle the exhaustion is the coordinate `p 1` high in the outer cusp, and the remaining points lie
in the compact set `midSet σ Y` (the doubled triangle is closed and bounded below in height,
`isClosed_domain`), so the derivative is bounded by the `.hyperbolicProduct` norm on the whole fold
domain (`exists_bound_fderiv_exhaustFn`); the bound is transported to every point by the isometries
of the relation, as review 21 asks. On the interior of the block the exhaustion `twoConeExhaust` is
smooth because the fold is a surjective local diffeomorphism (`contMDiff_twoConeExhaust`) and proper
because each sublevel set is a closed subset of the image of a set `midSet σ Y`
(`isProperMap_twoConeExhaust`).
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Geometry
open scoped Topology ComplexConjugate ContDiff Manifold

universe u

namespace GC.Seifert

namespace TwoConeFold

namespace Fold

open ConeShape

private abbrev coord (i : Fin 3) : ModelCoordinates →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

private theorem norm_modelCoordinates_le (p : ModelCoordinates) :
    ‖p‖ ≤ |p 0| + |p 1| + |p 2| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ |p 0| + |p 1| + |p 2|)]
  apply Real.sqrt_le_sqrt
  have h0 := abs_nonneg (p 0)
  have h1 := abs_nonneg (p 1)
  have h2 := abs_nonneg (p 2)
  nlinarith [sq_abs (p 0), sq_abs (p 1), sq_abs (p 2)]

section Closed

variable {σ : ConeShape}

theorem isClosed_triangle (hθ : 0 < σ.θ₂) : IsClosed σ.triangle := by
  have h : σ.triangle = {z : ℂ | min (Real.sin σ.θ₁) (Real.sin σ.θ₂) / 4 ≤ z.im} ∩
      ⋂ i, {z | 0 ≤ σ.wallSide i z} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter]
    constructor
    · intro hz
      exact ⟨im_ge_of_mem_triangle hz, hz.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨lt_of_lt_of_le (low_pos hθ) h1, h2⟩
  rw [h]
  exact (isClosed_le continuous_const continuous_im).inter
    (isClosed_iInter fun i => isClosed_le continuous_const (σ.wallSide_continuous i))

theorem continuous_refl_zero : Continuous (σ.refl 0) := by
  change Continuous fun z : ℂ => -conj z
  exact Complex.continuous_conj.neg

theorem isClosed_domain (hθ : 0 < σ.θ₂) : IsClosed σ.domain := by
  have h : σ.domain = σ.triangle ∪ σ.refl 0 ⁻¹' σ.triangle := by
    ext z
    exact σ.mem_domain_iff
  rw [h]
  exact (isClosed_triangle hθ).union ((isClosed_triangle hθ).preimage continuous_refl_zero)

theorem abs_re_le_of_mem_domain {z : ℂ} (hz : z ∈ σ.domain) : |z.re| ≤ σ.width := by
  rcases σ.mem_domain_iff.1 hz with h | h
  · have h0 : 0 ≤ z.re := h.2 0
    have h1 : 0 ≤ σ.width - z.re := h.2 1
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · have h0 : 0 ≤ (σ.refl 0 z).re := h.2 0
    have h1 : 0 ≤ σ.width - (σ.refl 0 z).re := h.2 1
    rw [refl_zero_re] at h0 h1
    exact abs_le.2 ⟨by linarith, by linarith⟩

def midSet (σ : ConeShape) (Y : ℝ) : Set ModelCoordinates :=
  zOf ⁻¹' σ.domain ∩ {p | p 1 ≤ Y} ∩ {p | 0 ≤ p 2} ∩ {p | p 2 ≤ 1}

theorem isCompact_midSet (hθ : 0 < σ.θ₂) (Y : ℝ) : IsCompact (midSet σ Y) := by
  have hc (i : Fin 3) : Continuous fun p : ModelCoordinates => p i := (coord i).continuous
  have hclosed : IsClosed (midSet σ Y) :=
    ((((isClosed_domain hθ).preimage contDiff_zOf.continuous).inter
      (isClosed_le (hc 1) continuous_const)).inter (isClosed_le continuous_const (hc 2))).inter
      (isClosed_le (hc 2) continuous_const)
  set L := min (Real.sin σ.θ₁) (Real.sin σ.θ₂) / 4
  have hL : 0 < L := low_pos hθ
  have hbdd : Bornology.IsBounded (midSet σ Y) := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨σ.width + |Real.log L| + |Y| + 1, fun p hp => ?_⟩
    obtain ⟨⟨⟨hD, hY⟩, h0⟩, h1⟩ := hp
    replace hD : zOf p ∈ σ.domain := hD
    replace hY : p 1 ≤ Y := hY
    replace h0 : 0 ≤ p 2 := h0
    replace h1 : p 2 ≤ 1 := h1
    have e0 : |p 0| ≤ σ.width := by
      have := abs_re_le_of_mem_domain hD
      rwa [re_zOf] at this
    have hlow : Real.log L ≤ p 1 := by
      have him := im_ge_of_mem_domain hD
      rw [im_zOf] at him
      rw [← Real.log_exp (p 1)]
      exact Real.log_le_log hL him
    have e1 : |p 1| ≤ |Real.log L| + |Y| :=
      abs_le.2 ⟨by linarith [neg_abs_le (Real.log L), abs_nonneg Y],
        by linarith [le_abs_self Y, abs_nonneg (Real.log L)]⟩
    have e2 : |p 2| ≤ 1 := abs_le.2 ⟨by linarith, h1⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [norm_modelCoordinates_le p]
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbdd

end Closed

section Bound

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (m₁ m₂ : Fin d.fillingCount) (hk : d.k = 3)
  (hj : ∀ m : Fin d.fillingCount, (C.port (.inr m)).val ≠ 0)
  (hp : ∀ m : Fin d.fillingCount, 0 < (d.fillingSlope m).1)
  {σ : ConeShape} (D : σ.FoldData)
  (hθ₁ : σ.θ₁ * (chartNumbers C m₁ m₂).p₁ = Real.pi)
  (hθ₂ : σ.θ₂ * (chartNumbers C m₁ m₂).p₂ = Real.pi)
  (hc₁ : C.tubeCentre m₁ = ((3 / 2 : ℝ) : ℂ)) (hc₂ : C.tubeCentre m₂ = ((-(3 / 2) : ℝ) : ℂ))

theorem midSet_subset_foldDomain (Y : ℝ) : midSet σ Y ⊆ foldDomain C m₁ m₂ D hθ₁ hθ₂ :=
  fun _ hq => domain_subset_baseDomain C m₁ m₂ D hθ₁ hθ₂ hq.1.1.1

include hj hp hc₁ hc₂ in
theorem exists_foldRel_unit {y : ModelCoordinates} (hy : y ∈ foldDomain C m₁ m₂ D hθ₁ hθ₂) :
    ∃ y₀, zOf y₀ ∈ σ.domain ∧ 0 ≤ y₀ 2 ∧ y₀ 2 < 1 ∧
      FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
        (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y y₀ := by
  obtain ⟨y₁, hy₁, hrel⟩ := exists_foldRel_domain C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hy
  have hrel' := foldRel_moveTrans C m₁ m₂ hk D hθ₁ hθ₂ hrel.mem (-⌊y₁ 2⌋)
  refine ⟨moveTrans ((-⌊y₁ 2⌋ : ℤ) : ℝ) y₁, by rw [zOf_moveTrans]; exact hy₁, ?_, ?_,
    hrel.trans hrel'⟩
  · rw [moveTrans_two]
    push_cast
    linarith [Int.floor_le (y₁ 2)]
  · rw [moveTrans_two]
    push_cast
    linarith [Int.lt_floor_add_one (y₁ 2)]

theorem exhaustFn_comp_eventuallyEq {y y' : ModelCoordinates}
    (h : FoldRel (coordinateModelMetric .hyperbolicProduct) (foldDomain C m₁ m₂ D hθ₁ hθ₂)
      (foldMap C m₁ m₂ hk D hθ₁ hθ₂) y y') :
    ∃ γ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates,
      Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) γ =
        coordinateModelMetric .hyperbolicProduct ∧ γ y = y' ∧
      (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂ ∘ γ) =ᶠ[𝓝 y] exhaustFn C m₁ m₂ hk D hθ₁ hθ₂ := by
  obtain ⟨γ, hγ, hy, U, hyU, -, -, hid⟩ := h
  refine ⟨γ, hγ, hy, eventually_of_mem (U.isOpen.mem_nhds hyU) fun z hz => ?_⟩
  simp only [Function.comp_apply, exhaustFn]
  rw [hid z hz]

include hj hp hc₁ hc₂ in
theorem exists_bound_fderiv_exhaustFn :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ p ∈ foldDomain C m₁ m₂ D hθ₁ hθ₂, ∀ v : ModelCoordinates,
      |fderiv ℝ (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂) p v| ≤
        K * Real.sqrt (coordinateInner .hyperbolicProduct p v v) := by
  set N := foldDomain C m₁ m₂ D hθ₁ hθ₂
  set Yt := D.topHeight
  have hYt : 0 < Yt := lt_trans one_pos (one_lt_topHeight D)
  have hθ : 0 < σ.θ₂ := θ₂_pos hθ₂
  have hKc := isCompact_midSet hθ (Real.log Yt)
  have hKsub := midSet_subset_foldDomain C m₁ m₂ D hθ₁ hθ₂ (Real.log Yt)
  have hsmooth := contDiffOn_exhaustFn C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
  have hcont := hsmooth.continuousOn_fderiv_of_isOpen N.isOpen (by simp)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hcont.mono hKsub)
  set K := max 1 (|B| * (Yt + 1))
  refine ⟨K, le_max_left _ _, fun p hpN v => ?_⟩
  have hdiff : ∀ q ∈ N, DifferentiableAt ℝ (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂) q := fun q hq =>
    (hsmooth.contDiffAt (N.isOpen.mem_nhds hq)).differentiableAt (by simp)
  have hQ : ∀ q w : ModelCoordinates, 0 ≤ Real.sqrt (coordinateInner .hyperbolicProduct q w w) :=
    fun _ _ => Real.sqrt_nonneg _
  have key : ∀ p₀ : ModelCoordinates, zOf p₀ ∈ σ.domain → 0 ≤ p₀ 2 → p₀ 2 ≤ 1 →
      ∀ w : ModelCoordinates, |fderiv ℝ (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂) p₀ w| ≤
        K * Real.sqrt (coordinateInner .hyperbolicProduct p₀ w w) := by
    intro p₀ hD h0 h1 w
    by_cases ha : Yt < Real.exp (p₀ 1)
    · have hev := exhaustFn_eq_cuspInf C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hD ha
      rw [hev.fderiv_eq]
      change |fderiv ℝ (coord 1) p₀ w| ≤ _
      rw [(coord 1).fderiv]
      exact (abs_one_le_sqrt_coordinateInner p₀ w).trans (le_mul_of_one_le_left (hQ _ _)
        (le_max_left _ _))
    · push Not at ha
      have hmem : p₀ ∈ midSet σ (Real.log Yt) := by
        refine ⟨⟨⟨hD, ?_⟩, h0⟩, h1⟩
        change p₀ 1 ≤ Real.log Yt
        rw [← Real.log_exp (p₀ 1)]
        exact Real.log_le_log (Real.exp_pos _) ha
      have h1' : ‖fderiv ℝ (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂) p₀‖ ≤ |B| :=
        (hB p₀ hmem).trans (le_abs_self _)
      have h2 : |fderiv ℝ (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂) p₀ w| ≤ |B| * ‖w‖ := by
        rw [← Real.norm_eq_abs]
        exact ((fderiv ℝ (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂) p₀).le_opNorm w).trans
          (mul_le_mul_of_nonneg_right h1' (norm_nonneg _))
      have h3 := norm_le_mul_sqrt_coordinateInner_of_exp_le hYt.le ha w
      calc |fderiv ℝ (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂) p₀ w| ≤ |B| * ‖w‖ := h2
        _ ≤ |B| * ((Yt + 1) * Real.sqrt (coordinateInner .hyperbolicProduct p₀ w w)) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
        _ = (|B| * (Yt + 1)) * Real.sqrt (coordinateInner .hyperbolicProduct p₀ w w) := by ring
        _ ≤ K * Real.sqrt (coordinateInner .hyperbolicProduct p₀ w w) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (hQ _ _)
  obtain ⟨p₀, hD, h0, h1, hrel⟩ := exists_foldRel_unit C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hpN
  have hp₀ : p₀ ∈ N := hrel.mem
  obtain ⟨γ, hγ, hγp, hev⟩ := exhaustFn_comp_eventuallyEq C m₁ m₂ hk D hθ₁ hθ₂ hrel
  have hdγ : DifferentiableAt ℝ γ p :=
    (contMDiff_iff_contDiff.1 γ.contMDiff).differentiable (by simp) p
  have hchain : fderiv ℝ (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂) p v =
      fderiv ℝ (exhaustFn C m₁ m₂ hk D hθ₁ hθ₂) p₀ (fderiv ℝ γ p v) := by
    rw [← hev.fderiv_eq, fderiv_comp p (by rw [hγp]; exact hdiff p₀ hp₀) hdγ, hγp]
    rfl
  have hiso := coordinateInner_fderiv_of_pullbackMetric_eq hγ p v
  rw [hγp] at hiso
  rw [hchain, ← hiso]
  exact key p₀ hD h0 h1.le _

end Bound

section Interior

variable {W : CompactCarrier.{u}} {d : SeifertData} (C : SeifertBlockCharts W d)
  (m₁ m₂ : Fin d.fillingCount) (hk : d.k = 3)
  (hj : ∀ m : Fin d.fillingCount, (C.port (.inr m)).val ≠ 0)
  (hp : ∀ m : Fin d.fillingCount, 0 < (d.fillingSlope m).1)
  {σ : ConeShape} (D : σ.FoldData)
  (hθ₁ : σ.θ₁ * (chartNumbers C m₁ m₂).p₁ = Real.pi)
  (hθ₂ : σ.θ₂ * (chartNumbers C m₁ m₂).p₂ = Real.pi)
  (hc₁ : C.tubeCentre m₁ = ((3 / 2 : ℝ) : ℂ)) (hc₂ : C.tubeCentre m₂ = ((-(3 / 2) : ℝ) : ℂ))
  (hall : ∀ m, m = m₁ ∨ m = m₂)

include hj hp hθ₁ hθ₂ hc₁ hc₂ hall in
theorem contMDiff_twoConeExhaust :
    letI := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
    ContMDiff (𝓡 3) 𝓘(ℝ) ∞ (twoConeExhaust C hk D) := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  intro x
  obtain ⟨y, hy, rfl⟩ := surjective_foldMap C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hall x
  apply (isLocalDiffeomorphAt_foldMap C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hy).contMDiffAt_of_comp
  exact ((contDiffOn_exhaustFn C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂).contDiffAt
    ((foldDomain C m₁ m₂ D hθ₁ hθ₂).isOpen.mem_nhds hy)).contMDiffAt

include hj hp hθ₁ hθ₂ hc₁ hc₂ hall in
theorem continuous_twoConeExhaust : Continuous (twoConeExhaust C hk D) := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  exact (contMDiff_twoConeExhaust C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hall).continuous

include hj hp hc₁ hc₂ in
theorem continuousOn_foldMap :
    ContinuousOn (foldMap C m₁ m₂ hk D hθ₁ hθ₂) (foldDomain C m₁ m₂ D hθ₁ hθ₂) := by
  let _ := Manifold.interiorChartedSpace W.model ∞ (M := W.pieceInterior ⊤)
  intro y hy
  exact (isLocalDiffeomorphAt_foldMap C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂
    hy).contMDiffAt.continuousAt.continuousWithinAt

include hj hp hθ₁ hθ₂ hc₁ hc₂ hall in
theorem isProperMap_twoConeExhaust : IsProperMap (twoConeExhaust C hk D) := by
  have hcont := continuous_twoConeExhaust C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hall
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hcont, fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := hK.bddAbove
  set Y := max R (Real.log D.topHeight)
  have hθ : 0 < σ.θ₂ := θ₂_pos hθ₂
  have himg : IsCompact (foldMap C m₁ m₂ hk D hθ₁ hθ₂ '' midSet σ Y) :=
    (isCompact_midSet hθ Y).image_of_continuousOn
      ((continuousOn_foldMap C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂).mono
        (midSet_subset_foldDomain C m₁ m₂ D hθ₁ hθ₂ Y))
  refine himg.of_isClosed_subset (hK.isClosed.preimage hcont) fun x hx => ?_
  have hxR : twoConeExhaust C hk D x ≤ R := hR hx
  obtain ⟨y, hy, rfl⟩ := surjective_foldMap C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hall x
  obtain ⟨y₀, hD, h0, h1, hrel⟩ := exists_foldRel_unit C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hy
  refine ⟨y₀, ⟨⟨⟨hD, ?_⟩, h0⟩, h1.le⟩, hrel.map_eq⟩
  change y₀ 1 ≤ Y
  have hval : exhaustFn C m₁ m₂ hk D hθ₁ hθ₂ y₀ ≤ R := by
    unfold exhaustFn
    rw [hrel.map_eq]
    exact hxR
  by_cases ha : D.topHeight < Real.exp (y₀ 1)
  · have hev := (exhaustFn_eq_cuspInf C m₁ m₂ hk hj hp D hθ₁ hθ₂ hc₁ hc₂ hD ha).eq_of_nhds
    rw [hev] at hval
    exact le_max_of_le_left hval
  · push Not at ha
    refine le_max_of_le_right ?_
    rw [← Real.log_exp (y₀ 1)]
    exact Real.log_le_log (Real.exp_pos _) ha

end Interior

end Fold

end TwoConeFold

end GC.Seifert
