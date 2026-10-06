import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceFibresV2
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProductChartKernel

/-!
# G17 kernel (c): `SmoothProductChartAt_BIFc` from the record of one marked chart (S-BAUG-D2)

`smoothProductChartAt_of_record_BAUGD` (generic, chain-free): given the interior manifold `N` with a
smooth embedding `ι : N → M` into the carrier (landing in the manifold interior), a stage map
`f : M → H` with source `X = f⁻¹(B) ⊆ ι(N)`, the record `(κ, σ₀, Wb, Mk)` of one marked chart on the
big base `Wb` (`B = Wb ∩ O'`), a smooth coordinate `g = κ ∘ f ∘ ι` that is a submersion where the
chart is active, properness of `f|X` over compact subsets of `B`, and the whole fibre over
`y ∈ B ∩ Mk` as a smooth embedded standard fibre `ψ : F → N`, the whole-fibre product chart
`SmoothProductChartAt_BIFc IM IF k f X B y` exists. Pieces: `baseChart_of_record_BAUGD` (the base
parametrization `σ₀ ∘ univBall`), `exists_productChart_of_proper_submersion_BAUGD` (Ehresmann over a
ball), and the composition with `ι` (a smooth embedding of a boundaryless manifold into the interior
of a manifold with corners).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Topology Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Manifold

section Record

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {HN : Type} [TopologicalSpace HN] {I : ModelWithCorners ℝ E HN} [I.Boundaryless]
  {N : Type} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold I ∞ N] [T2Space N]
  [LocallyCompactSpace N] [SecondCountableTopology N]
  {EM : Type} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ∞ M]
  {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- **A smooth product chart over a marked base piece from the record of one chart** (see the
module docstring). `Pi` is the open piece of the stage in which the active region lives (the ratio
piece of the chart): the submersion hypothesis `hreg` is asked only over `Mk ∩ Pi`. -/
theorem smoothProductChartAt_of_record_BAUGD {k : ℕ} (hk : 0 < k)
    (hdim : k < Module.finrank ℝ E)
    {EF : Type} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [FiniteDimensional ℝ EF]
    {HF : Type} [TopologicalSpace HF] (IF : ModelWithCorners ℝ EF HF) [IF.Boundaryless]
    {F : Type} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
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
    (ψ : F → N) (hψ : IsSmoothEmbedding IF I ∞ ψ)
    (hψr : range ψ = {x | ι x ∈ X ∧ f (ι x) = y}) :
    SmoothProductChartAt_BIFc IM IF (F := F) k f X B y := by
  classical
  have hyWO : y ∈ Wb ∩ O' := hB ▸ hy
  have hy' : y ∈ Wb ∩ (O' ∩ Pi) ∩ Mk := ⟨⟨hyWO.1, hyWO.2, hyP⟩, hyM⟩
  obtain ⟨hκy, hσy⟩ := hc y ⟨hyWO.1, hyM⟩
  obtain ⟨ε, hε, hsub, hO⟩ := exists_radius_baseChart_BAUGD σ₀ (O' ∩ Pi) (hO'.inter hPi) ha hκy
    (by rw [hσy]; exact ⟨hyWO.2, hyP⟩)
  let g : N → EuclideanSpace ℝ (Fin k) := fun x => κ (f (ι x))
  let R : Set N := {x | ι x ∈ X ∧ f (ι x) ∈ Mk ∩ Pi ∧ g x ∈ ball (κ y) ε}
  have hR : IsOpen R :=
    hXopen.inter (((hMk.inter hPi).preimage hfι).inter (isOpen_ball.preimage hg.continuous))
  -- on `R` the stage map is recovered from the coordinate
  have hpoint : ∀ x ∈ R, f (ι x) = σ₀ (g x) := by
    intro x hx
    have hfB : f (ι x) ∈ B := himg ▸ mem_image_of_mem f hx.1
    rw [hB] at hfB
    exact (hc _ ⟨hfB.1, hx.2.1.1⟩).2.symm
  -- the points over the ball `ball (κ y) ε` in the base
  have hσB : ∀ b ∈ ball (κ y) ε, σ₀ b ∈ B ∧ σ₀ b ∈ Mk ∩ Pi := by
    intro b hb'
    have h := hb b (hsub hb')
    exact ⟨hB ▸ ⟨h.1.1, (hO b hb').1⟩, h.1.2, (hO b hb').2⟩
  have hhprop : ∀ K ⊆ ball (κ y) ε, IsCompact K → IsCompact {x | x ∈ R ∧ g x ∈ K} := by
    intro K hK hKc
    have hS : IsCompact (σ₀ '' K) :=
      hKc.image_of_continuousOn (ha.continuousOn.mono (hK.trans hsub))
    have hSB : σ₀ '' K ⊆ B := by
      rintro _ ⟨b, hbK, rfl⟩
      exact (hσB b (hK hbK)).1
    have hcpt := hprop _ hSB hS
    have himage : ι '' {x | x ∈ R ∧ g x ∈ K} = X ∩ f ⁻¹' (σ₀ '' K) := by
      ext p
      constructor
      · rintro ⟨x, ⟨hxR, hxK⟩, rfl⟩
        exact ⟨hxR.1, ⟨g x, hxK, (hpoint x hxR).symm⟩⟩
      · rintro ⟨hpX, b, hbK, hbp⟩
        obtain ⟨x, rfl⟩ := hXι hpX
        have hκb : g x = b := by
          change κ (f (ι x)) = b
          rw [← hbp]
          exact (hb b (hsub (hK hbK))).2
        refine ⟨x, ⟨⟨hpX, ?_, ?_⟩, ?_⟩, rfl⟩
        · rw [← hbp]; exact (hσB b (hK hbK)).2
        · rw [hκb]; exact hK hbK
        · rw [hκb]; exact hbK
    exact hι.isEmbedding.isCompact_iff.mpr (himage ▸ hcpt)
  have hhsurj : ∀ b ∈ ball (κ y) ε, ∃ x ∈ R, g x = b := by
    intro b hb'
    obtain ⟨p, hpX, hpb⟩ : σ₀ b ∈ f '' X := himg ▸ (hσB b hb').1
    obtain ⟨x, rfl⟩ := hXι hpX
    have hκb : g x = b := by
      change κ (f (ι x)) = b
      rw [hpb]
      exact (hb b (hsub hb')).2
    exact ⟨x, ⟨hpX, by rw [hpb]; exact (hσB b hb').2, by rw [hκb]; exact hb'⟩, hκb⟩
  have hψr' : range ψ = R ∩ g ⁻¹' {κ y} := by
    rw [hψr]
    ext x
    constructor
    · rintro ⟨hxX, hxy⟩
      refine ⟨⟨hxX, by rw [hxy]; exact ⟨hyM, hyP⟩, ?_⟩, ?_⟩
      · change κ (f (ι x)) ∈ ball (κ y) ε
        rw [hxy]
        exact mem_ball_self hε
      · change κ (f (ι x)) = κ y
        rw [hxy]
    · rintro ⟨hxR, hxg⟩
      refine ⟨hxR.1, ?_⟩
      rw [hpoint x hxR, show g x = κ y from hxg, hσy]
  obtain ⟨ε', hε', hball, Φ, hΦemb, hΦrange, hΦg⟩ :=
    exists_productChart_of_proper_submersion_BAUGD hk hdim IF g hg R hR hε
      (fun x hx => hx.2.2) (fun x hx => hreg x hx.1 hx.2.1.1 hx.2.1.2) hhprop hhsurj ψ hψ hψr'
  obtain ⟨h0, hσsm, hσemb, hσinj, hκσ, hσrange⟩ := baseChart_of_record_BAUGD κ σ₀ Wb Mk
    (O' ∩ Pi) ha hb hc hy' hε' (hball.trans hsub) (fun b hb' => hO b (hball hb'))
  set c := OpenPartialHomeomorph.univBall (κ y) ε' with hcdef
  -- the composite `ι ∘ Φ` is a smooth embedding into `M`
  have hnt : Nontrivial (EuclideanSpace ℝ (Fin k) × EF) := by
    have : Nontrivial (EuclideanSpace ℝ (Fin k)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hk)
    exact nontrivial_prod_left
  have hιΦ : IsSmoothEmbedding ((𝓡 k).prod IF) IM ∞ (ι ∘ Φ) := by
    refine isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF
      (by simp) (hι.contMDiff.comp hΦemb.contMDiff) (hι.isEmbedding.comp hΦemb.isEmbedding)
      (fun q => ?_) (fun q => hιint _)
    have h1 : MDifferentiableAt ((𝓡 k).prod IF) I Φ q :=
      (hΦemb.contMDiff q).mdifferentiableAt (by simp)
    have h2 : MDifferentiableAt I IM ι (Φ q) := (hι.contMDiff (Φ q)).mdifferentiableAt (by simp)
    have hcomp := mfderiv_comp q h2 h1
    rw [hcomp]
    exact (hι.isImmersion.mfderiv_injective (by simp) (Φ q)).comp
      (hΦemb.isImmersion.mfderiv_injective (by simp) q)
  have hΦR : ∀ q, Φ q ∈ R := fun q => by
    have h : Φ q ∈ range Φ := mem_range_self q
    rw [hΦrange] at h
    exact h.1
  refine ⟨σ₀ ∘ c, ι ∘ Φ, (Mk ∩ Pi) ∩ κ ⁻¹' ball (κ y) ε', h0, hσsm, hσemb, hσinj,
    (hMk.inter hPi).inter (isOpen_ball.preimage κ.continuous), ?_, hιΦ, ?_, ?_⟩
  · rw [hσrange, hB]
    ext w
    simp only [mem_inter_iff, mem_preimage]
    tauto
  · -- the whole preimage of the base piece is the image of the chart
    have hrange : range (ι ∘ Φ) = ι '' (R ∩ g ⁻¹' ball (κ y) ε') := by
      rw [← hΦrange, range_comp]
    rw [hrange, hσrange]
    ext p
    constructor
    · rintro ⟨x, ⟨hxR, hxg⟩, rfl⟩
      have hfB : f (ι x) ∈ B := himg ▸ mem_image_of_mem f hxR.1
      rw [hB] at hfB
      exact ⟨hxR.1, ⟨hfB.1, hfB.2, hxR.2.1.2⟩, hxR.2.1.1, hxg⟩
    · rintro ⟨hpX, ⟨hpW, hpO, hpP⟩, hpM, hpκ⟩
      obtain ⟨x, rfl⟩ := hXι hpX
      exact ⟨x, ⟨⟨hpX, ⟨hpM, hpP⟩, hball hpκ⟩, hpκ⟩, rfl⟩
  · intro x z
    change f (ι (Φ (x, z))) = σ₀ (c x)
    rw [hpoint _ (hΦR _), hΦg x z]

end Record

end DifferentialGeometry.Geometry.Collapse
