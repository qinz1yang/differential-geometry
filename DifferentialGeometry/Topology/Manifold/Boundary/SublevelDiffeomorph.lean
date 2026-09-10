import DifferentialGeometry.Topology.Manifold.BoundaryCollar.Height
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.FlowEmbedding
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.UniformInwardFlow
import DifferentialGeometry.Topology.Manifold.Boundary.RegularBand
import DifferentialGeometry.Topology.Manifold.RegularLevel.InteriorSublevel
import DifferentialGeometry.Topology.Manifold.MFDeriv.Affine
import DifferentialGeometry.Topology.Manifold.Collar.InverseRescaling
import DifferentialGeometry.Topology.Manifold.Interval.CompressionInverse

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Topology.Morse
namespace Poincare.Manifold.Boundary

theorem exists_regular_top_sublevel_diffeomorph
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [CompactSpace M]
    {V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y}
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hpos : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M,
      0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p))
    (N : Opens M) (hKN : (𝓡∂ (n + 1)).boundary M ⊆ N)
    {f : M → ℝ} (hf : ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    {b : ℝ} (hboundary : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M, f p = b)
    (hinterior : ∀ x, (𝓡∂ (n + 1)).IsInteriorPoint x → f x < b)
    (hunit : ∀ y ∈ N, (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f y) (V y) = (-1 : ℝ))
    {t : ℝ} (ht : t < b) :
    ∃ c : ℝ, t < c ∧ c < b ∧
      (∀ x, mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f x = 0 → f x < c) ∧
      ∃ (hreg : ∀ x, f x = c → mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
        (hi : {x | f x ≤ c} ⊆ (𝓡∂ (n + 1)).interior M),
        let _ := RegularLevel.interiorSublevelChartedSpace (𝓡∂ (n + 1))
          (EuclideanSpace.equiv (Fin (n + 1)) ℝ) hf hreg hi
        ∃ d : M ≃ₘ⟮𝓡∂ (n + 1), morseModelWithCornersHalfSpace n⟯ {x : M // f x ≤ c},
          (∀ x, f x ≤ t → (d x : M) = x) ∧
          ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M, f (d p : M) = c := by
  let I := 𝓡∂ (n + 1)
  let r : M → ℝ := fun x => b - f x
  have hr : ContMDiff I 𝓘(ℝ, ℝ) ∞ r := contMDiff_const.sub hf
  have hrzero (p : BoundaryManifold I M) : r p = 0 := by dsimp [r]; rw [hboundary]; exact sub_self b
  have hrpos (x : M) (hx : I.IsInteriorPoint x) : 0 < r x := sub_pos.mpr (hinterior x hx)
  have hdr (x : M) : (show EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) r x) =
      -(show EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) :=
    mfderiv_const_sub_real (hf.mdifferentiableAt (by simp)) b
  have hrate : ∀ y ∈ N, (mfderiv I 𝓘(ℝ, ℝ) r y) (V y) = (1 : ℝ) := by
    intro y hy
    have hd := congrArg (fun L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ => L (V y)) (hdr y)
    exact hd.trans ((congrArg (fun z : ℝ => -z) (hunit y hy)).trans (neg_neg (1 : ℝ)))
  have hK : IsCompact (I.boundary M) := (I.isClosed_boundary (n := ∞) (by simp)).isCompact
  obtain ⟨U, hKU, ε, hε, F, hF, hzero, hcurve, hflowInterior, _⟩ :=
    BoundaryCollar.exists_uniform_boundary_flow_of_inward hV hpos hK
  let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  let B := BoundaryManifold I M
  let J := (HasSmoothBoundary.boundaryModel I).prod (𝓡∂ 1)
  let collar : B × Icc (0 : ℝ) ε → M := fun q => F ((q.1 : M), (q.2 : ℝ))
  have hcs : ContMDiff J I ∞ collar := hF.comp_contMDiff
    ((boundaryInclusion_contMDiff (I := I) (M := M)).prodMap
      (contMDiff_subtypeVal_Icc (x := (0 : ℝ)) (y := ε)))
    (fun q => ⟨hKU q.1.2, q.2.2⟩)
  let : CompactSpace B := isCompact_iff_compactSpace.mp hK
  have hc : IsClosedEmbedding collar := hcs.continuous.isClosedEmbedding
    (BoundaryCollar.boundary_flow_injective hV hKU hzero hcurve hflowInterior)
  obtain ⟨δ, hδ, hδε, Y, hBY, hYN, chart, hchart, hheight⟩ :=
    BoundaryCollar.exists_boundary_flow_collar_diffeomorph_height hK hV hpos hKU hF
      hzero hcurve hflowInterior N hKN (hr.mdifferentiable (by simp)) hrzero hrate
  let Ω : Opens (B × Icc (0 : ℝ) ε) :=
    ⟨{q | q.2.val < δ}, isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
  have he (q : Ω) : (chart q : M) = collar q.val := hchart q
  have hY : (Y : Set M) = collar '' {q | q.2.val < δ} := by
    ext y
    constructor
    · intro hy
      let q := chart.symm ⟨y, hy⟩
      exact ⟨q.val, q.property, (he q).symm.trans (congrArg Subtype.val (chart.apply_symm_apply ⟨y, hy⟩))⟩
    · rintro ⟨q, hq, rfl⟩
      rw [← he ⟨q, hq⟩]
      exact (chart ⟨q, hq⟩).property
  have hopen : IsOpen (collar '' {q | q.2.val < δ}) := hY ▸ Y.isOpen
  have hheight' (q : B × Icc (0 : ℝ) ε) (hq : q.2.val < δ) : r (collar q) = q.2.val :=
    (congrArg r (he ⟨q, hq⟩)).symm.trans (hheight ⟨q, hq⟩)
  obtain ⟨ζ, hζ, hsmall, hcritical, _⟩ := exists_regular_boundary_band hr.continuous hrpos
    Y.isOpen hBY (fun x hx => hrate x (hYN hx))
  let ρ : ℝ := min (ζ / 4) (min (δ / 4) ((b - t) / 4))
  have hρ : 0 < ρ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hρζ : ρ ≤ ζ / 4 := min_le_left _ _
  have hρδ : ρ ≤ δ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hρt : ρ ≤ (b - t) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have h2ρδ : 2 * ρ < δ := by linarith
  obtain ⟨a, ha, haρ, σ, scalar, hscalar, hσs, hσmono, hσrange, _, hσfix⟩ :=
    Poincare.Manifold.Interval.exists_smooth_compression_with_diffeomorph hρ (h2ρδ.trans hδε).le
  have haζ : a < ζ := by linarith
  have haδ : a < δ := by linarith
  let c : ℝ := b - a
  have htc : t < c := by dsimp [c]; linarith
  have hcb : c < b := sub_lt_self b ha
  have hcrit (x : M) (hx : mfderiv I 𝓘(ℝ, ℝ) f x = 0) : f x < c := by
    have hzr : mfderiv I 𝓘(ℝ, ℝ) r x = 0 := (hdr x).trans
      ((congrArg (fun L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ => -L)
        (show (show EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ from mfderiv I 𝓘(ℝ, ℝ) f x) = 0 from hx)).trans (neg_zero))
    have hh := hcritical x hzr
    dsimp [r, c] at *
    linarith
  have hreg : ∀ x, f x = c → mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0 :=
    fun x hx hz => (ne_of_lt (hcrit x hz)) hx
  have hinter : {x | f x ≤ c} ⊆ I.interior M := by
    intro x hx
    apply (I.isInteriorPoint_iff_not_isBoundaryPoint x).mpr
    intro hxb
    have hb := hboundary ⟨x, hxb⟩
    change f x ≤ c at hx
    linarith
  let R := Poincare.Topology.Collar.rescale collar hc.isEmbedding σ
  have hR : IsClosedEmbedding R := Poincare.Topology.Collar.isClosedEmbedding_rescale
    collar hc.isEmbedding σ hσmono.injective h2ρδ hopen hσfix
  have hheightCut (q : B × Icc (0 : ℝ) ε) : a ≤ r (collar q) ↔ a ≤ q.2.val := by
    by_cases hq : q.2.val < δ
    · rw [hheight' q hq]
    · have hnotY : collar q ∉ Y := by
        change collar q ∉ (Y : Set M)
        rw [hY]
        rintro ⟨p, hp, hpq⟩
        exact hq ((hc.injective hpq) ▸ hp)
      have hqδ := le_of_not_gt hq
      have hrζ : ζ < r (collar q) := lt_of_not_ge (fun hz => hnotY (hsmall hz))
      exact iff_of_true (haζ.le.trans hrζ.le) (haδ.le.trans hqδ)
  have hrange : range R = {x | f x ≤ c} := by
    rw [Poincare.Topology.Collar.range_rescale collar hc.isEmbedding σ hσrange]
    ext x
    constructor
    · rintro (hx | ⟨q, hq, rfl⟩)
      · have hnotY : x ∉ Y := by
          intro hy
          have hy' : x ∈ collar '' {q | q.2.val < δ} := hY ▸ (show x ∈ (Y : Set M) from hy)
          exact hx (image_subset_range _ _ hy')
        have hh : ζ < r x := lt_of_not_ge (fun hz => hnotY (hsmall hz))
        change f x ≤ b - a
        dsimp [r] at hh
        linarith
      · have hh := (hheightCut q).mpr hq
        change f (collar q) ≤ b - a
        exact (le_sub_iff_add_le).mpr (by dsimp [r] at hh; linarith)
    · intro hx
      by_cases hxc : x ∈ range collar
      · obtain ⟨q, rfl⟩ := hxc
        exact Or.inr ⟨q, (hheightCut q).mp (by change f (collar q) ≤ b - a at hx; dsimp [r]; linarith), rfl⟩
      · exact Or.inl hxc
  let A : Set M := {x | f x ≤ c}
  let homeo : M ≃ₜ A := hR.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have hmap (x : M) : (homeo x : M) = R x := rfl
  let _ : ChartedSpace (MorseHalfSpace n) A :=
    RegularLevel.interiorSublevelChartedSpace I (EuclideanSpace.equiv (Fin (n + 1)) ℝ) hf hreg hinter
  have hRs : ContMDiff I I ∞ R := Poincare.Manifold.Collar.contMDiff_rescale collar hc.isEmbedding hcs σ hσs
    chart he (fun q hq => hq.trans_lt h2ρδ) hσfix
  have hforward : ContMDiff I (morseModelWithCornersHalfSpace n) ∞ homeo :=
    (RegularLevel.contMDiff_interiorSublevel_iff I (EuclideanSpace.equiv (Fin (n + 1)) ℝ)
      I hf hreg hinter).mpr hRs
  have hinverse : ContMDiff (morseModelWithCornersHalfSpace n) I ∞ homeo.symm :=
    Poincare.Manifold.Collar.contMDiff_rescale_homeomorph_symm
      (A := A) (K := morseModelWithCornersHalfSpace n) collar hc.isEmbedding hcs σ scalar hscalar
      chart he (fun q hq => hq.trans_lt h2ρδ) hσfix homeo hmap
      (RegularLevel.contMDiff_interiorSublevel_inclusion I (EuclideanSpace.equiv (Fin (n + 1)) ℝ) hf hreg hinter)
  let d : M ≃ₘ⟮I, morseModelWithCornersHalfSpace n⟯ A :=
    { homeo.toEquiv with contMDiff_toFun := hforward, contMDiff_invFun := hinverse }
  refine ⟨c, htc, hcb, hcrit, hreg, hinter, d, ?_, ?_⟩
  · intro x hx
    change R x = x
    by_cases hxc : x ∈ range collar
    · obtain ⟨q, rfl⟩ := hxc
      have htime : 2 * ρ ≤ q.2.val := by
        by_contra hn
        have hqt : q.2.val < 2 * ρ := lt_of_not_ge hn
        have hh := hheight' q (hqt.trans h2ρδ)
        dsimp [r] at hh
        linarith
      change Poincare.Topology.Collar.rescale collar hc.isEmbedding σ (collar q) = collar q
      rw [Poincare.Topology.Collar.rescale_apply, hσfix q.2 htime]
    · exact Poincare.Topology.Collar.rescale_of_not_mem collar hc.isEmbedding σ hxc
  · intro p
    let _ := RegularLevel.interiorSublevelIsManifold I (EuclideanSpace.equiv (Fin (n + 1)) ℝ) hf hreg hinter
    apply (RegularLevel.interiorSublevelBoundary_iff I (EuclideanSpace.equiv (Fin (n + 1)) ℝ) hf hreg hinter (d p)).mp
    exact ((d.isLocalDiffeomorph (p : M)).isBoundaryPoint_iff (by simp)).mp p.property

end Poincare.Manifold.Boundary
