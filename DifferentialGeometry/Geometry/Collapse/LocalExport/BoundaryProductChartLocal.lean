import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryProductChartCircle

/-!
# O-WF G2d: whole-fibre product charts from a LOCAL record (centred twins of S-BAUG-D2's G17)

S-BAUG-D2's record kernels (`baseChart_of_record_BAUGD`, `smoothProductChartAt_of_record_BAUGD`,
`smoothProductChartAt_circle_of_record_BAUGD`) ask the chart inverse `σ₀` of the base on a ball
CENTRED AT `0`, i.e. a global one-sheet record of the marked chart (CGP07). The local route of
lane O-WF only has, at each base point `y`, a smooth local inverse of the chart coordinate `κ` on
a small open set `Dset ∋ κ y`. These twins replace `ball 0 r` by an arbitrary OPEN set
`Dset ⊆ ℝᵏ` (proofs verbatim otherwise):

* `exists_radius_baseChart_OWF`, `baseChart_of_localRecord_OWF`;
* **`smoothProductChartAt_of_localRecord_OWF`** (standard fibre embedding `ψ` supplied);
* **`smoothProductChartAt_circle_of_localRecord_OWF`** (circle stage: `ψ` from the connected
  compact whole fibre).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Topology Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold

section Base

/-- **A radius for the chart at `y`**: a ball around `b₀` inside the open set `Dset` on which
`σ₀` stays in `O'`. -/
theorem exists_radius_baseChart_OWF {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {k : ℕ} (σ₀ : EuclideanSpace ℝ (Fin k) → H) (O' : Set H) (hO' : IsOpen O')
    {Dset : Set (EuclideanSpace ℝ (Fin k))} (hD : IsOpen Dset)
    (ha : ContDiffOn ℝ ∞ σ₀ Dset)
    {b₀ : EuclideanSpace ℝ (Fin k)} (hb₀ : b₀ ∈ Dset)
    (hO : σ₀ b₀ ∈ O') :
    ∃ ε : ℝ, 0 < ε ∧ ball b₀ ε ⊆ Dset ∧
      ∀ b ∈ ball b₀ ε, σ₀ b ∈ O' := by
  have hcont : ContinuousAt σ₀ b₀ := ha.continuousOn.continuousAt (hD.mem_nhds hb₀)
  have hpre : σ₀ ⁻¹' O' ∈ nhds b₀ := hcont.preimage_mem_nhds (hO'.mem_nhds hO)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hpre
    (hD.mem_nhds hb₀))
  exact ⟨ε, hε, fun b hb' => (hball hb').2, fun b hb' => (hball hb').1⟩

/-- **A base chart from the record of one marked chart** (see the module docstring), at any radius
`ε` for which `ball (κ y) ε ⊆ ball 0 r` and `σ₀` stays in `O'` on the ball. -/
theorem baseChart_of_localRecord_OWF {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {k : ℕ} (κ : H →L[ℝ] EuclideanSpace ℝ (Fin k)) (σ₀ : EuclideanSpace ℝ (Fin k) → H)
    (Wb Mk O' : Set H) {Dset : Set (EuclideanSpace ℝ (Fin k))}
    (ha : ContDiffOn ℝ ∞ σ₀ Dset)
    (hb : ∀ b ∈ Dset, σ₀ b ∈ Wb ∩ Mk ∧ κ (σ₀ b) = b)
    (hc : ∀ y ∈ Wb ∩ Mk,
      κ y ∈ Dset ∧ σ₀ (κ y) = y)
    {y : H} (hy : y ∈ Wb ∩ O' ∩ Mk) {ε : ℝ} (hε : 0 < ε)
    (hsub : ball (κ y) ε ⊆ Dset)
    (hO : ∀ b ∈ ball (κ y) ε, σ₀ b ∈ O') :
    σ₀ (OpenPartialHomeomorph.univBall (κ y) ε 0) = y ∧
      ContDiff ℝ ∞ (σ₀ ∘ OpenPartialHomeomorph.univBall (κ y) ε) ∧
      IsEmbedding (σ₀ ∘ OpenPartialHomeomorph.univBall (κ y) ε) ∧
      (∀ x, Injective (fderiv ℝ (σ₀ ∘ OpenPartialHomeomorph.univBall (κ y) ε) x)) ∧
      (∀ x, κ (σ₀ (OpenPartialHomeomorph.univBall (κ y) ε x)) =
        OpenPartialHomeomorph.univBall (κ y) ε x) ∧
      range (σ₀ ∘ OpenPartialHomeomorph.univBall (κ y) ε) =
        (Wb ∩ O') ∩ (Mk ∩ κ ⁻¹' ball (κ y) ε) := by
  obtain ⟨⟨hyW, hyO⟩, hyM⟩ := hy
  obtain ⟨hκy, hσy⟩ := hc y ⟨hyW, hyM⟩
  obtain ⟨hesm, hemb, hrange, he0, hde⟩ := univBall_data_BAUGD (κ y) hε
  set e := OpenPartialHomeomorph.univBall (κ y) ε with he
  have heb : ∀ x, e x ∈ ball (κ y) ε := fun x => hrange ▸ mem_range_self x
  have hκσ : ∀ x, κ (σ₀ (e x)) = e x := fun x => (hb _ (hsub (heb x))).2
  have hσsm : ContDiff ℝ ∞ (σ₀ ∘ e) :=
    contDiffOn_univ.mp (ha.comp (hesm.contDiffOn (s := univ)) (fun x _ => hsub (heb x)))
  refine ⟨by rw [he0, hσy], hσsm, ?_, ?_, fun x => hκσ x, ?_⟩
  · -- embedding: `κ ∘ (σ₀ ∘ e) = e` is an embedding
    refine IsEmbedding.of_comp hσsm.continuous κ.continuous ?_
    have : (⇑κ ∘ σ₀ ∘ ⇑e) = ⇑e := funext hκσ
    rw [this]
    exact hemb
  · -- injective differential: `κ ∘ D(σ₀ ∘ e) = De` and `De` is injective
    intro x u v huv
    have hdσ : DifferentiableAt ℝ (σ₀ ∘ e) x := (hσsm.differentiable (by simp)) x
    have hcomp : HasFDerivAt (κ ∘ (σ₀ ∘ e)) (κ.comp (fderiv ℝ (σ₀ ∘ e) x)) x :=
      κ.hasFDerivAt.comp x hdσ.hasFDerivAt
    have hκe : (κ ∘ (σ₀ ∘ e)) = e := funext hκσ
    rw [hκe] at hcomp
    have h1 : fderiv ℝ e x = κ.comp (fderiv ℝ (σ₀ ∘ e) x) := hcomp.fderiv
    apply hde x
    rw [h1]
    exact congrArg κ huv
  · -- range
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      have hx := heb x
      have hmem := hb _ (hsub hx)
      refine ⟨⟨hmem.1.1, hO _ hx⟩, hmem.1.2, ?_⟩
      change κ (σ₀ (e x)) ∈ ball (κ y) ε
      rw [hκσ]
      exact hx
    · rintro ⟨⟨hwW, hwO⟩, hwM, hwκ⟩
      obtain ⟨-, hw⟩ := hc w ⟨hwW, hwM⟩
      have hκw : κ w ∈ range e := by rw [hrange]; exact hwκ
      obtain ⟨x, hx⟩ := hκw
      refine ⟨x, ?_⟩
      change σ₀ (e x) = w
      rw [hx, hw]

end Base

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
theorem smoothProductChartAt_of_localRecord_OWF {k : ℕ} (hk : 0 < k)
    (hdim : k < Module.finrank ℝ E)
    {EF : Type} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [FiniteDimensional ℝ EF]
    {HF : Type} [TopologicalSpace HF] (IF : ModelWithCorners ℝ EF HF) [IF.Boundaryless]
    {F : Type} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
    (ι : N → M) (hι : IsSmoothEmbedding I IM ∞ ι) (hιint : ∀ x, IM.IsInteriorPoint (ι x))
    (f : M → H) (X : Set M) (B : Set H)
    (κ : H →L[ℝ] EuclideanSpace ℝ (Fin k)) (σ₀ : EuclideanSpace ℝ (Fin k) → H)
    (Wb Mk O' Pi : Set H) {Dset : Set (EuclideanSpace ℝ (Fin k))} (hD : IsOpen Dset)
    (hB : B = Wb ∩ O') (hO' : IsOpen O') (hMk : IsOpen Mk) (hPi : IsOpen Pi)
    (ha : ContDiffOn ℝ ∞ σ₀ Dset)
    (hb : ∀ b ∈ Dset, σ₀ b ∈ Wb ∩ Mk ∧ κ (σ₀ b) = b)
    (hc : ∀ y ∈ Wb ∩ Mk, κ y ∈ Dset ∧ σ₀ (κ y) = y)
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
  obtain ⟨ε, hε, hsub, hO⟩ := exists_radius_baseChart_OWF σ₀ (O' ∩ Pi) (hO'.inter hPi) hD ha hκy
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
  obtain ⟨h0, hσsm, hσemb, hσinj, hκσ, hσrange⟩ := baseChart_of_localRecord_OWF κ σ₀ Wb Mk
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

/-- **The circle-stage whole-fibre chart from the record of one chart** (see the module
docstring): `SmoothProductChartAt_BIFc IM (𝓡 1) (F := Circle) k f X B y`. The hypotheses are those
of `smoothProductChartAt_of_record_BAUGD`, with the standard fibre embedding `ψ` replaced by the
connectedness of the whole fibre `{x | ι x ∈ X ∧ f (ι x) = y}` and `dim N = k + 1`. -/
theorem smoothProductChartAt_circle_of_localRecord_OWF {k : ℕ} (hk : 0 < k)
    (hdimE : Module.finrank ℝ E = k + 1)
    (ι : N → M) (hι : IsSmoothEmbedding I IM ∞ ι) (hιint : ∀ x, IM.IsInteriorPoint (ι x))
    (f : M → H) (X : Set M) (B : Set H)
    (κ : H →L[ℝ] EuclideanSpace ℝ (Fin k)) (σ₀ : EuclideanSpace ℝ (Fin k) → H)
    (Wb Mk O' Pi : Set H) {Dset : Set (EuclideanSpace ℝ (Fin k))} (hD : IsOpen Dset)
    (hB : B = Wb ∩ O') (hO' : IsOpen O') (hMk : IsOpen Mk) (hPi : IsOpen Pi)
    (ha : ContDiffOn ℝ ∞ σ₀ Dset)
    (hb : ∀ b ∈ Dset, σ₀ b ∈ Wb ∩ Mk ∧ κ (σ₀ b) = b)
    (hc : ∀ y ∈ Wb ∩ Mk, κ y ∈ Dset ∧ σ₀ (κ y) = y)
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
  exact smoothProductChartAt_of_localRecord_OWF hk (by omega) (𝓡 1) ι hι hιint f X B κ σ₀ Wb Mk
    O' Pi hD hB hO' hMk hPi ha hb hc hXι himg hXopen hfι hg hreg hprop hy hyM hyP ψ hψ
    (hψr.trans hS)

end Record

end DifferentialGeometry.Geometry.Collapse
