import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProductChartRecord
import DifferentialGeometry.Topology.Manifold.OneManifold.CircleConsequences

/-!
# G17 kernel (d): the circle stage — a connected compact regular fibre is a smooth circle
(S-BAUG-D2)

* `exists_circle_embedding_of_connected_fibre_BAUGD` (generic): `g : N → ℝᵏ` smooth, `R ⊆ N` open,
  the level `S = R ∩ g⁻¹{b₀}` compact, connected, `dg` onto at its points, `dim N = k + 1`:
  there is a smooth embedding `ψ : S¹ → N` onto `S` (`nonempty_circle_diffeomorph_regularFiber` on
  `g|R`, composed with the inclusion of the regular fibre).
* `smoothProductChartAt_circle_of_record_BAUGD`: the circle-stage whole-fibre chart
  `SmoothProductChartAt_BIFc IM (𝓡 1) (F := Circle) k f X B y` from the record of one chart, the
  connectedness of the whole fibre and the submersion of the coordinate (`ψ` is produced, not
  assumed: compactness of the fibre is the properness of `f|X` over `{y}`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Topology Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold

section Circle

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {HN : Type} [TopologicalSpace HN] {I : ModelWithCorners ℝ E HN} [I.Boundaryless]
  {N : Type} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold I ∞ N] [T2Space N]
  [LocallyCompactSpace N] [SecondCountableTopology N]

omit [SecondCountableTopology N] in
/-- **A compact connected regular level of a smooth map `N → ℝᵏ` with `dim N = k + 1` is a smooth
circle**: a smooth embedding `S¹ → N` onto the level. -/
theorem exists_circle_embedding_of_connected_fibre_BAUGD {k : ℕ}
    (hdimE : Module.finrank ℝ E = k + 1)
    (g : N → EuclideanSpace ℝ (Fin k)) (hg : ContMDiff I (𝓡 k) ∞ g)
    (R : Set N) (hR : IsOpen R) (b₀ : EuclideanSpace ℝ (Fin k))
    (hreg : ∀ x ∈ R, g x = b₀ → Surjective (mfderiv I (𝓡 k) g x))
    (hcpt : IsCompact (R ∩ g ⁻¹' {b₀})) (hconn : IsConnected (R ∩ g ⁻¹' {b₀})) :
    ∃ ψ : Circle → N, IsSmoothEmbedding (𝓡 1) I ∞ ψ ∧ range ψ = R ∩ g ⁻¹' {b₀} := by
  classical
  let V : TopologicalSpace.Opens N := ⟨R, hR⟩
  have : LocallyCompactSpace V := hR.locallyCompactSpace
  let gV : V → EuclideanSpace ℝ (Fin k) := fun x => g x
  have hgV : ContMDiff I (𝓡 k) ∞ gV :=
    hg.comp (contMDiff_subtype_val (I := I) (U := V))
  have hregV : ∀ x, gV x = b₀ → Surjective (mfderiv I (𝓡 k) gV x) := by
    intro x hx
    have h := DifferentialGeometry.mfderiv_restrict_open (I := I) (J := 𝓡 k) g V x
    change Surjective (mfderiv I (𝓡 k) (fun z : V => g z) x)
    rw [h]
    exact hreg x.1 x.2 hx
  have himg : Subtype.val '' {x : V | gV x = b₀} = R ∩ g ⁻¹' {b₀} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  have hcptV : IsCompact {x : V | gV x = b₀} := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, himg]
    exact hcpt
  have hconnV : IsConnected {x : V | gV x = b₀} := by
    have h2 : IsPreconnected (Subtype.val '' {x : V | gV x = b₀}) := by
      rw [himg]
      exact hconn.isPreconnected
    have h1 : IsPreconnected {x : V | gV x = b₀} :=
      Topology.IsEmbedding.subtypeVal.toIsInducing.isPreconnected_image.mp h2
    obtain ⟨p, hp⟩ := hconn.nonempty
    exact ⟨⟨⟨p, hp.1⟩, hp.2⟩, h1⟩
  obtain ⟨e⟩ := OneManifold.nonempty_circle_diffeomorph_regularFiber gV b₀ hgV hregV
    (by rw [finrank_euclideanSpace_fin]; exact hdimE) hcptV hconnV
  let _ := regularFiberChartedSpace gV b₀ hgV hregV
  have := regularFiberIsManifold gV b₀ hgV hregV
  have : Nonempty (Fin (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k)))) :=
    ⟨⟨0, by rw [finrank_euclideanSpace_fin]; omega⟩⟩
  have hincl : IsSmoothEmbedding
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) → ℝ) I ∞
      (Subtype.val ∘ Subtype.val : {x : V // gV x = b₀} → N) := by
    have h1 : IsSmoothEmbedding
        𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) → ℝ) I ∞
        (Subtype.val : {x : V // gV x = b₀} → V) :=
      isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF (by simp)
        (contMDiff_regularFiberInclusion gV b₀ hgV hregV) IsEmbedding.subtypeVal
        (mfderiv_regularFiberInclusion_injective gV b₀ hgV hregV)
        (fun _ => BoundarylessManifold.isInteriorPoint)
    exact (IsSmoothEmbedding.of_opens V).comp h1 (by simp)
  have he : IsSmoothEmbedding (𝓡 1)
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) → ℝ) ∞ e :=
    isSmoothEmbedding_of_isLocalDiffeomorph_of_injective e.isLocalDiffeomorph e.injective
  refine ⟨(Subtype.val ∘ Subtype.val : {x : V // gV x = b₀} → N) ∘ e, hincl.comp he (by simp), ?_⟩
  have hsurj : range (e : Circle → {x : V // gV x = b₀}) = univ := e.surjective.range_eq
  rw [range_comp, hsurj, image_univ]
  ext x
  constructor
  · rintro ⟨⟨z, hz⟩, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨hxR, hxg⟩
    exact ⟨⟨⟨x, hxR⟩, hxg⟩, rfl⟩

end Circle

section CircleChart

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {HN : Type} [TopologicalSpace HN] {I : ModelWithCorners ℝ E HN} [I.Boundaryless]
  {N : Type} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold I ∞ N] [T2Space N]
  [LocallyCompactSpace N] [SecondCountableTopology N]
  {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **The circle-stage whole-fibre chart from the record of one chart** (see the module
docstring): `SmoothProductChartAt_BIFc IM (𝓡 1) (F := Circle) k f X B y`. The hypotheses are those
of `smoothProductChartAt_of_record_BAUGD`, with the standard fibre embedding `ψ` replaced by the
connectedness of the whole fibre `{x | ι x ∈ X ∧ f (ι x) = y}` and `dim N = k + 1`. -/
theorem smoothProductChartAt_circle_of_record_BAUGD {k : ℕ} (hk : 0 < k)
    (hdimE : Module.finrank ℝ E = k + 1)
    (ι : N → M) (hι : IsSmoothEmbedding I IM ∞ ι) (hιint : ∀ x, IM.IsInteriorPoint (ι x))
    (f : M → H) (X : Set M) (B : Set H)
    (κ : H →L[ℝ] EuclideanSpace ℝ (Fin k)) (σ₀ : EuclideanSpace ℝ (Fin k) → H)
    (Wb Mk O' Pi : Set H) {r : ℝ}
    (hB : B = Wb ∩ O') (hO' : IsOpen O') (hMk : IsOpen Mk) (hPi : IsOpen Pi)
    (ha : ContDiffOn ℝ ∞ σ₀ (ball (0 : EuclideanSpace ℝ (Fin k)) r))
    (hb : ∀ b ∈ ball (0 : EuclideanSpace ℝ (Fin k)) r, σ₀ b ∈ Wb ∩ Mk ∧ κ (σ₀ b) = b)
    (hc : ∀ y ∈ Wb ∩ Mk, κ y ∈ ball (0 : EuclideanSpace ℝ (Fin k)) r ∧ σ₀ (κ y) = y)
    (hXι : X ⊆ range ι) (himg : f '' X = B) (hXopen : IsOpen (ι ⁻¹' X))
    (hfι : Continuous (f ∘ ι))
    (hg : ContMDiff I (𝓡 k) ∞ (fun x => κ (f (ι x))))
    (hreg : ∀ x, ι x ∈ X → f (ι x) ∈ Mk → f (ι x) ∈ Pi →
      Surjective (mfderiv I (𝓡 k) (fun x => κ (f (ι x))) x))
    (hprop : ∀ Kc ⊆ B, IsCompact Kc → IsCompact (X ∩ f ⁻¹' Kc))
    {y : H} (hy : y ∈ B) (hyM : y ∈ Mk) (hyP : y ∈ Pi)
    (hconn : IsConnected {x | ι x ∈ X ∧ f (ι x) = y}) :
    SmoothProductChartAt_BIFc IM (𝓡 1) (F := Circle) k f X B y := by
  classical
  have hyWO : y ∈ Wb ∩ O' := hB ▸ hy
  obtain ⟨hκy, hσy⟩ := hc y ⟨hyWO.1, hyM⟩
  let g : N → EuclideanSpace ℝ (Fin k) := fun x => κ (f (ι x))
  let R₀ : Set N := {x | ι x ∈ X ∧ f (ι x) ∈ Mk ∩ Pi}
  have hR₀ : IsOpen R₀ := hXopen.inter ((hMk.inter hPi).preimage hfι)
  have hS : R₀ ∩ g ⁻¹' {κ y} = {x | ι x ∈ X ∧ f (ι x) = y} := by
    ext x
    constructor
    · rintro ⟨⟨hxX, hxM⟩, hxg⟩
      have hfB : f (ι x) ∈ B := himg ▸ mem_image_of_mem f hxX
      rw [hB] at hfB
      refine ⟨hxX, ?_⟩
      rw [← (hc _ ⟨hfB.1, hxM.1⟩).2, show κ (f (ι x)) = κ y from hxg, hσy]
    · rintro ⟨hxX, hxy⟩
      exact ⟨⟨hxX, hxy ▸ ⟨hyM, hyP⟩⟩, by rw [mem_preimage, mem_singleton_iff]; exact congrArg κ hxy⟩
  have hcpt : IsCompact {x | ι x ∈ X ∧ f (ι x) = y} := by
    have h := hprop {y} (singleton_subset_iff.mpr hy) isCompact_singleton
    rw [hι.isEmbedding.isCompact_iff]
    convert h using 1
    ext p
    constructor
    · rintro ⟨x, ⟨hxX, hxy⟩, rfl⟩
      exact ⟨hxX, hxy⟩
    · rintro ⟨hpX, hpy⟩
      obtain ⟨x, rfl⟩ := hXι hpX
      exact ⟨x, ⟨hpX, hpy⟩, rfl⟩
  obtain ⟨ψ, hψ, hψr⟩ := exists_circle_embedding_of_connected_fibre_BAUGD hdimE g hg R₀ hR₀
    (κ y) (fun x hx hxg => hreg x hx.1 hx.2.1 hx.2.2) (hS ▸ hcpt) (hS ▸ hconn)
  exact smoothProductChartAt_of_record_BAUGD hk (by omega) (𝓡 1) ι hι hιint f X B κ σ₀ Wb Mk O' Pi
    hB hO' hMk hPi ha hb hc hXι himg hXopen hfι hg hreg hprop hy hyM hyP ψ hψ (hψr.trans hS)

end CircleChart

end DifferentialGeometry.Geometry.Collapse
