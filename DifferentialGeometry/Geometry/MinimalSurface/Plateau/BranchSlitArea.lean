/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.BranchSlitFilling
import DifferentialGeometry.Geometry.Measure.Area.PiecewiseReparametrization
import DifferentialGeometry.Analysis.Integration.Measure.LipschitzSetTransport

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Planar.SlitRegluing
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

private theorem slit_mul_lipschitz (c : ℂ) :
    LipschitzWith ‖c‖₊ (fun z : ℂ => c * z) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm, ← mul_sub, norm_mul, coe_nnnorm]
  exact le_rfl

private theorem slit_div_lipschitz (c : ℂ) :
    LipschitzWith ‖c⁻¹‖₊ (fun z : ℂ => z / c) := by
  simpa only [div_eq_mul_inv, mul_comm] using slit_mul_lipschitz c⁻¹

private theorem slit_scale_image (c : ℂ) (hc : c ≠ 0) (s : Set ℂ) :
    (fun z : ℂ => c * z) '' s = (fun z : ℂ => z / c) ⁻¹' s := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [mem_preimage, mul_div_cancel_left₀ _ hc] using hw
  · intro hz
    exact ⟨z / c, hz, by
      change c * (z / c) = z
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hc]⟩

private theorem slit_square_bound {z : ℂ} (hz : z ∈ square) : ‖z‖ ≤ 2 := by
  exact (Complex.norm_le_abs_re_add_abs_im z).trans
    (by change |z.re| + |z.im| ≤ 2; linarith [hz.1, hz.2])

private theorem slit_square_closed : IsClosed square :=
  (isClosed_le Complex.continuous_re.abs continuous_const).inter
    (isClosed_le Complex.continuous_im.abs continuous_const)

private theorem slit_image_disjoint {f : ℂ → ℂ} {P a b : Set ℂ}
    (hf : InjOn f P) (ha : a ⊆ P) (hb : b ⊆ P) (h : Disjoint a b) :
    Disjoint (f '' a) (f '' b) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  have he : y = x := hf (hb hy) (ha hx) heq
  exact Set.disjoint_left.mp h hx (he ▸ hy)

private theorem slit_conjugated_piecewise_area
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {ι : Type*} [Finite ι] (F : OpenPartialHomeomorph ℂ ℂ)
    [IsFiniteMeasure (volume.restrict F.target)]
    {U V : ℂ → M} {C A B : ℝ≥0}
    (hU : ∀ x y, riemannianEDistOf g (U x) (U y) ≤ (C : ℝ≥0∞) * edist x y)
    (hF : LipschitzOnWith A (F : ℂ → ℂ) F.source)
    (hFi : LipschitzOnWith B (F.symm : ℂ → ℂ) F.target)
    (s t : ι → Set ℂ) (φ : ι → ℂ → ℂ) (K L : ι → ℝ≥0)
    (hs : ∀ i, IsOpen (s i)) (ht : ∀ i, IsOpen (t i))
    (hsP : ∀ i, s i ⊆ F.source) (htP : ∀ i, t i ⊆ F.source)
    (himage : ∀ i, φ i '' s i = t i)
    (hsdisj : Pairwise (fun i j => Disjoint (s i) (s j)))
    (htdisj : Pairwise (fun i j => Disjoint (t i) (t j)))
    (hscover : (⋃ i, s i) =ᵐ[volume] F.source)
    (htcover : (⋃ i, t i) =ᵐ[volume] F.source)
    (hφLip : ∀ i, LipschitzOnWith (K i) (φ i) (s i))
    (hφlower : ∀ i, ∀ x ∈ s i, ∀ y ∈ s i,
      edist x y ≤ (L i : ℝ≥0∞) * edist (φ i x) (φ i y))
    (hV : ∀ i, ∀ x ∈ s i, V (F x) = U (F (φ i x))) :
    riemannianArea g V F.target = riemannianArea g U F.target := by
  classical
  let ψ : ι → ℂ → ℂ := fun i z => F (φ i (F.symm z))
  have hφmem (i : ι) {x : ℂ} (hx : x ∈ s i) : φ i x ∈ t i := by
    rw [← himage i]
    exact mem_image_of_mem (φ i) hx
  have hψimage (i : ι) : ψ i '' (F '' s i) = F '' t i := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨φ i x, hφmem i hx, by simp only [ψ, F.left_inv (hsP i hx)]⟩
    · rintro ⟨y, hy, rfl⟩
      rw [← himage i] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨F x, mem_image_of_mem F hx, by simp only [ψ, F.left_inv (hsP i hx)]⟩
  have hmaps (i : ι) : MapsTo (F.symm : ℂ → ℂ) (F '' s i) (s i) := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [F.left_inv (hsP i hx)] using hx
  have hψLip (i : ι) : LipschitzOnWith (A * (K i * B)) (ψ i) (F '' s i) :=
    hF.comp ((hφLip i).comp (hFi.mono (image_subset_iff.mpr (fun _ hx =>
      F.map_source (hsP i hx)))) (hmaps i))
      (fun _ hx => htP i (hφmem i (hmaps i hx)))
  have hψlower (i : ι) : ∀ x ∈ F '' s i, ∀ y ∈ F '' s i,
      edist x y ≤ ((A * (L i * B) : ℝ≥0) : ℝ≥0∞) * edist (ψ i x) (ψ i y) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [ψ, F.left_inv (hsP i hx), F.left_inv (hsP i hy)]
    have hi := hFi (F.map_source (htP i (hφmem i hx)))
      (F.map_source (htP i (hφmem i hy)))
    rw [F.left_inv (htP i (hφmem i hx)), F.left_inv (htP i (hφmem i hy))] at hi
    calc
      edist (F x) (F y) ≤ (A : ℝ≥0∞) * edist x y := hF (hsP i hx) (hsP i hy)
      _ ≤ (A : ℝ≥0∞) * ((L i : ℝ≥0∞) * edist (φ i x) (φ i y)) := by
        gcongr
        exact hφlower i x hx y hy
      _ ≤ (A : ℝ≥0∞) * ((L i : ℝ≥0∞) *
          ((B : ℝ≥0∞) * edist (F (φ i x)) (F (φ i y)))) := by
        gcongr
      _ = _ := by simp only [ENNReal.coe_mul, mul_assoc]
  have hscover' : (⋃ i, F '' s i) =ᵐ[volume] F.target := by
    simpa only [F.bijOn.image_eq] using
      DifferentialGeometry.Analysis.image_iUnion_ae_eq_of_lipschitzOn
        hF (Subset.rfl : F.source ⊆ F.source) hsP hscover
  have htcover' : (⋃ i, F '' t i) =ᵐ[volume] F.target := by
    simpa only [F.bijOn.image_eq] using
      DifferentialGeometry.Analysis.image_iUnion_ae_eq_of_lipschitzOn
        hF (Subset.rfl : F.source ⊆ F.source) htP htcover
  refine (riemannianArea_piecewise_reparametrization g hU
    (fun i => F '' s i) ψ (fun i => A * (K i * B)) (fun i => A * (L i * B))
    (fun i => F.isOpen_image_of_subset_source (hs i) (hsP i))
    (fun i => image_subset_iff.mpr (fun _ hx => F.map_source (hsP i hx)))
    ?_ ?_ ?_ ?_ hscover' ?_ hψLip hψlower ?_).2
  · intro i
    rw [hψimage]
    exact image_subset_iff.mpr (fun _ hx => F.map_source (htP i hx))
  · intro i
    rw [hψimage]
    exact (F.isOpen_image_of_subset_source (ht i) (htP i)).measurableSet
  · intro i j hij
    exact (slit_image_disjoint F.injOn (hsP i) (hsP j) (hsdisj hij)).aedisjoint
  · intro i j hij
    rw [hψimage, hψimage]
    exact (slit_image_disjoint F.injOn (htP i) (htP j) (htdisj hij)).aedisjoint
  · simpa only [hψimage] using htcover'
  · rintro i _ ⟨x, hx, rfl⟩
    simpa only [Function.comp_apply, ψ, F.left_inv (hsP i hx)] using hV i x hx

private abbrev SlitIndex := Option ((Bool × Bool) × Fin 3)

private def slitBallCell (R : ℝ) : SlitIndex → Set ℂ
  | none => Metric.ball 0 R \ scaledSquare (R / 4)
  | some p => (fun z : ℂ => ((R / 4 : ℝ) : ℂ) * z) '' sourceCell p.1 p.2

private def slitBallTarget (R : ℝ) : SlitIndex → Set ℂ
  | none => Metric.ball 0 R \ scaledSquare (R / 4)
  | some p => (fun z : ℂ => ((R / 4 : ℝ) : ℂ) * z) '' targetCell p.1 p.2

private def slitBallBranch (R : ℝ) : SlitIndex → ℂ → ℂ
  | none => id
  | some p => scaledBranch (R / 4) p.1 p.2

private theorem slit_ball_cells (R : ℝ) (hR : 0 < R) :
    (∀ i, IsOpen (slitBallCell R i)) ∧
    (∀ i, IsOpen (slitBallTarget R i)) ∧
    (∀ i, slitBallCell R i ⊆ Metric.ball 0 R) ∧
    (∀ i, slitBallTarget R i ⊆ Metric.ball 0 R) ∧
    (∀ i, slitBallBranch R i '' slitBallCell R i = slitBallTarget R i) ∧
    Pairwise (fun i j => Disjoint (slitBallCell R i) (slitBallCell R j)) ∧
    Pairwise (fun i j => Disjoint (slitBallTarget R i) (slitBallTarget R j)) ∧
    (⋃ i, slitBallCell R i) =ᵐ[volume] Metric.ball 0 R ∧
    (⋃ i, slitBallTarget R i) =ᵐ[volume] Metric.ball 0 R ∧
    (∃ K L : SlitIndex → ℝ≥0,
      (∀ i, LipschitzOnWith (K i) (slitBallBranch R i) (slitBallCell R i)) ∧
      (∀ i, ∀ x ∈ slitBallCell R i, ∀ y ∈ slitBallCell R i,
        edist x y ≤ (L i : ℝ≥0∞) * edist (slitBallBranch R i x) (slitBallBranch R i y))) ∧
    (∀ i, EqOn (scaledSlitMap (R / 4)) (slitBallBranch R i) (slitBallCell R i)) := by
  classical
  let r := R / 4
  have hr : 0 < r := by dsimp [r]; linarith
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  let m : ℂ → ℂ := fun z => (r : ℂ) * z
  have hminj : Function.Injective m := by
    intro z w h
    exact mul_left_cancel₀ hc h
  have hsq : m '' square = scaledSquare r := slit_scale_image _ hc square
  have hsqBall : scaledSquare r ⊆ Metric.ball (0 : ℂ) R := by
    rw [← hsq]
    rintro _ ⟨z, hz, rfl⟩
    have hz' := slit_square_bound hz
    simp only [Metric.mem_ball, dist_zero_right, m, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    dsimp [r] at *
    nlinarith
  have hsqClosed : IsClosed (scaledSquare r) :=
    slit_square_closed.preimage (continuous_id.div_const (r : ℂ))
  have hsSq (p : (Bool × Bool) × Fin 3) : sourceCell p.1 p.2 ⊆ square :=
    (sourceCell_subset_closedCell p.1 p.2).trans (sourceClosedCell_subset_square p.1 p.2)
  have htSq (p : (Bool × Bool) × Fin 3) : targetCell p.1 p.2 ⊆ square := by
    rw [← branch_image_cell]
    rintro _ ⟨z, hz, rfl⟩
    exact branch_mem_square p.1 p.2 (sourceCell_subset_closedCell p.1 p.2 hz)
  have hscaledSq (s : Set ℂ) (hs : s ⊆ square) : m '' s ⊆ scaledSquare r := by
    rw [← hsq]
    exact image_mono hs
  have hsourceOpen : ∀ i, IsOpen (slitBallCell R i) := by
    intro i
    cases i with
    | none => exact Metric.isOpen_ball.sdiff hsqClosed
    | some p =>
      change IsOpen (m '' sourceCell p.1 p.2)
      rw [slit_scale_image _ hc]
      exact (sourceCell_isOpen p.1 p.2).preimage (continuous_id.div_const (r : ℂ))
  have htargetOpen : ∀ i, IsOpen (slitBallTarget R i) := by
    intro i
    cases i with
    | none => exact Metric.isOpen_ball.sdiff hsqClosed
    | some p =>
      change IsOpen (m '' targetCell p.1 p.2)
      rw [slit_scale_image _ hc]
      exact (targetCell_isOpen p.1 p.2).preimage (continuous_id.div_const (r : ℂ))
  have hsBall : ∀ i, slitBallCell R i ⊆ Metric.ball 0 R := by
    intro i
    cases i with
    | none => exact sdiff_subset
    | some p => exact (hscaledSq _ (hsSq p)).trans hsqBall
  have htBall : ∀ i, slitBallTarget R i ⊆ Metric.ball 0 R := by
    intro i
    cases i with
    | none => exact sdiff_subset
    | some p => exact (hscaledSq _ (htSq p)).trans hsqBall
  have hbranchImage : ∀ i, slitBallBranch R i '' slitBallCell R i = slitBallTarget R i := by
    intro i
    cases i with
    | none => exact image_id _
    | some p =>
      change scaledBranch r p.1 p.2 '' (m '' sourceCell p.1 p.2) = m '' targetCell p.1 p.2
      rw [← branch_image_cell p.1 p.2, image_image, image_image]
      apply congrArg (fun f : ℂ → ℂ => f '' sourceCell p.1 p.2)
      funext z
      simp only [scaledBranch, m, mul_div_cancel_left₀ _ hc]
  have hdisj (cells : ((Bool × Bool) × Fin 3) → Set ℂ)
      (hsub : ∀ p, cells p ⊆ square)
      (hd : Pairwise (fun p q => Disjoint (cells p) (cells q))) :
      Pairwise (fun i j : SlitIndex => Disjoint
        (i.elim (Metric.ball 0 R \ scaledSquare r) (fun p => m '' cells p))
        (j.elim (Metric.ball 0 R \ scaledSquare r) (fun p => m '' cells p))) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some q =>
        apply Set.disjoint_left.mpr
        intro z hz hzq
        exact hz.2 (hscaledSq _ (hsub q) hzq)
    | some p =>
      cases j with
      | none =>
        apply Set.disjoint_left.mpr
        intro z hzp hz
        exact hz.2 (hscaledSq _ (hsub p) hzp)
      | some q =>
        exact slit_image_disjoint (fun _ _ _ _ h => hminj h)
          (subset_univ _) (subset_univ _) (hd (fun hpq => hij (congrArg some hpq)))
  have hcover (cells : ((Bool × Bool) × Fin 3) → Set ℂ)
      (hsub : ∀ p, cells p ⊆ square)
      (hae : (⋃ p, cells p) =ᵐ[volume] square) :
      (⋃ i : SlitIndex, i.elim (Metric.ball 0 R \ scaledSquare r)
        (fun p => m '' cells p)) =ᵐ[volume] Metric.ball 0 R := by
    have hscaled := DifferentialGeometry.Analysis.image_iUnion_ae_eq_of_lipschitzOn
      (slit_mul_lipschitz (r : ℂ)).lipschitzOnWith (subset_univ square) hsub hae
    rw [hsq] at hscaled
    filter_upwards [hscaled] with z hz
    apply propext
    constructor
    · intro h
      rcases mem_iUnion.mp h with ⟨i, hi⟩
      cases i with
      | none => exact hi.1
      | some p => exact hsqBall (hscaledSq _ (hsub p) hi)
    · intro hzB
      by_cases hzSq : z ∈ scaledSquare r
      · obtain ⟨p, hp⟩ := mem_iUnion.mp (hz.mpr hzSq)
        exact mem_iUnion.mpr ⟨some p, hp⟩
      · exact mem_iUnion.mpr ⟨none, hzB, hzSq⟩
  have hsCover : (⋃ p : (Bool × Bool) × Fin 3, sourceCell p.1 p.2) =ᵐ[volume] square := by
    filter_upwards [sourceCell_ae_cover] with z hz
    apply propext
    simpa only [mem_iUnion, Prod.exists] using hz.symm
  have htCover : (⋃ p : (Bool × Bool) × Fin 3, targetCell p.1 p.2) =ᵐ[volume] square := by
    filter_upwards [targetCell_ae_cover] with z hz
    apply propext
    simpa only [mem_iUnion, Prod.exists] using hz.symm
  choose K hK using (fun p : (Bool × Bool) × Fin 3 => branch_lipschitz p.1 p.2)
  choose L hL using (fun p : (Bool × Bool) × Fin 3 => branchInv_lipschitz p.1 p.2)
  let k : SlitIndex → ℝ≥0 := fun i => i.elim 1 (fun p => ‖(r : ℂ)‖₊ * (K p * ‖(r : ℂ)⁻¹‖₊))
  let l : SlitIndex → ℝ≥0 := fun i => i.elim 1 (fun p => ‖(r : ℂ)‖₊ * (L p * ‖(r : ℂ)⁻¹‖₊))
  have hLip : ∀ i, LipschitzWith (k i) (slitBallBranch R i) := by
    intro i
    cases i with
    | none => exact LipschitzWith.id
    | some p => exact (slit_mul_lipschitz (r : ℂ)).comp ((hK p).comp (slit_div_lipschitz (r : ℂ)))
  have hLow : ∀ i, ∀ x ∈ slitBallCell R i, ∀ y ∈ slitBallCell R i,
      edist x y ≤ (l i : ℝ≥0∞) * edist (slitBallBranch R i x) (slitBallBranch R i y) := by
    intro i x _ y _
    cases i with
    | none =>
      simpa only [slitBallBranch, id_eq, l, Option.elim_none, ENNReal.coe_one, one_mul]
        using (le_refl (edist x y))
    | some p =>
      change edist x y ≤
        (((‖(r : ℂ)‖₊ * (L p * ‖(r : ℂ)⁻¹‖₊)) : ℝ≥0) : ℝ≥0∞) *
          edist (scaledBranch r p.1 p.2 x) (scaledBranch r p.1 p.2 y)
      have hinv := (slit_mul_lipschitz (r : ℂ)).comp ((hL p).comp (slit_div_lipschitz (r : ℂ)))
      have h := hinv (scaledBranch r p.1 p.2 x) (scaledBranch r p.1 p.2 y)
      simpa only [Function.comp_apply, scaledBranch, mul_div_cancel_left₀ _ hc,
        branchInv_branch, ← mul_div_assoc] using h
  have hcell (i : SlitIndex) : slitBallCell R i =
      i.elim (Metric.ball 0 R \ scaledSquare r) (fun p => m '' sourceCell p.1 p.2) := by
    cases i <;> rfl
  have htarget (i : SlitIndex) : slitBallTarget R i =
      i.elim (Metric.ball 0 R \ scaledSquare r) (fun p => m '' targetCell p.1 p.2) := by
    cases i <;> rfl
  refine ⟨hsourceOpen, htargetOpen, hsBall, htBall, hbranchImage,
    (by simpa only [hcell] using hdisj _ hsSq sourceCell_pairwiseDisjoint),
    (by simpa only [htarget] using hdisj _ htSq targetCell_pairwiseDisjoint),
    (by simpa only [hcell] using hcover _ hsSq hsCover),
    (by simpa only [htarget] using hcover _ htSq htCover),
    ⟨k, l, fun i => (hLip i).lipschitzOnWith, hLow⟩, ?_⟩
  intro i z hz
  cases i with
  | none => exact scaledSlitMap_eq_self_of_notMem hr.ne' hz.2
  | some p =>
    apply scaledSlitMap_eq_scaledBranch
    change z ∈ m '' sourceCell p.1 p.2 at hz
    rwa [slit_scale_image _ hc] at hz

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- The literal slit filling returned by `exists_actual_branch_slit_filling`
has exactly the original source-patch area. The same disk, source chart,
straightening and metric are retained. No differentiability at the center of
the straightening or membership in its declared partial domains is needed. -/
theorem riemannianDiskArea_actual_branch_slit_filling
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u d : C(closedDisk, M))
    {L : ℝ≥0} (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤
      (L : ℝ≥0∞) * edist z w)
    (e S : OpenPartialHomeomorph ℂ ℂ) {R : ℝ} (hR : 0 < R)
    (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1)
    (hχ : ∀ z, χ z = e.symm ((R : ℂ) * z))
    (hχsrc : Metric.closedBall (0 : ℂ) 1 ⊆ χ.source)
    (hSnorm : ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖S z‖ = ‖z‖ ∧ ‖S.symm z‖ = ‖z‖ ∧
      S.symm (S z) = z ∧ S (S.symm z) = z)
    {K J : ℝ≥0}
    (hSLip : LipschitzOnWith K (S : ℂ → ℂ) (Metric.closedBall (0 : ℂ) R))
    (hSiLip : LipschitzOnWith J (S.symm : ℂ → ℂ) (Metric.closedBall (0 : ℂ) R))
    (hd : ∀ z : closedDisk, d z = diskExtension u
      (e.symm (S (scaledSlitMap (R / 4) (S.symm ((R : ℂ) * z)))))) :
    riemannianDiskArea g d =
      riemannianArea g (diskExtension u) (χ '' Metric.closedBall (0 : ℂ) 1) := by
  classical
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have : IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let : PseudoEMetricSpace M := .ofRiemannianMetric 𝓘(ℝ, E) M
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hnormR : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hscale : MapsTo (fun z : ℂ => (R : ℂ) * z) (Metric.ball (0 : ℂ) 1)
      (Metric.ball (0 : ℂ) R) := by
    intro z hz
    simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
    rw [norm_mul, hnormR]
    nlinarith
  have hdivide (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) R) :
      S z / (R : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
    rw [norm_div, hnormR, (hSnorm z (Metric.mem_closedBall.mpr (by
      simpa only [dist_zero_right] using hz.le))).1]
    exact (div_lt_one hR).mpr hz
  have hinverse (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      S.symm ((R : ℂ) * z) ∈ Metric.ball (0 : ℂ) R := by
    have hrz := hscale hz
    simpa only [Metric.mem_ball, dist_zero_right,
      (hSnorm _ (Metric.ball_subset_closedBall hrz)).2.1] using hrz
  let F : OpenPartialHomeomorph ℂ ℂ :=
    { toFun := fun z => S z / (R : ℂ)
      invFun := fun z => S.symm ((R : ℂ) * z)
      source := Metric.ball 0 R
      target := Metric.ball 0 1
      map_source' := hdivide
      map_target' := hinverse
      left_inv' := by
        intro z hz
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hRc]
        exact (hSnorm z (Metric.ball_subset_closedBall hz)).2.2.1
      right_inv' := by
        intro z hz
        rw [(hSnorm _ (Metric.ball_subset_closedBall (hscale hz))).2.2.2,
          mul_div_cancel_left₀ _ hRc]
      open_source := Metric.isOpen_ball
      open_target := Metric.isOpen_ball
      continuousOn_toFun := (hSLip.continuousOn.mono Metric.ball_subset_closedBall).div_const _
      continuousOn_invFun := (hSiLip.continuousOn.mono Metric.ball_subset_closedBall).comp
        (continuous_const.mul continuous_id).continuousOn hscale }
  have hF : LipschitzOnWith (‖(R : ℂ)⁻¹‖₊ * K) (F : ℂ → ℂ) F.source :=
    (slit_div_lipschitz (R : ℂ)).comp_lipschitzOnWith (hSLip.mono Metric.ball_subset_closedBall)
  have hFi : LipschitzOnWith (J * ‖(R : ℂ)‖₊) (F.symm : ℂ → ℂ) F.target :=
    hSiLip.comp (slit_mul_lipschitz (R : ℂ)).lipschitzOnWith
      (fun _ hz => Metric.ball_subset_closedBall (hscale hz))
  let old := diskThroughSourceChart u χ hχsrc
  obtain ⟨C, hC⟩ := diskThroughSourceChart_lipschitz g u huLip χ le_rfl hχsrc
  have hOldLip : LipschitzWith C (diskExtension old) :=
    diskExtension_riemannian_lipschitz g hC
  have hOld (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) :
      diskExtension old z = diskExtension u (e.symm ((R : ℂ) * z)) := by
    rw [diskExtension_coe old ⟨z, Metric.ball_subset_closedBall hz⟩]
    exact congrArg (diskExtension u) (hχ z)
  let : IsFiniteMeasure (volume.restrict F.target) := isFiniteMeasure_restrict.mpr
    ((measure_mono (Metric.ball_subset_closedBall : Metric.ball (0 : ℂ) 1 ⊆
      Metric.closedBall (0 : ℂ) 1)).trans_lt
      (isCompact_closedBall (0 : ℂ) 1).measure_lt_top).ne
  obtain ⟨hs, ht, hsP, htP, himage, hsdisj, htdisj, hscover, htcover,
    ⟨kb, lb, hkb, hlb⟩, heq⟩ := slit_ball_cells R hR
  have hV : ∀ i, ∀ z ∈ slitBallCell R i,
      diskExtension d (F z) = diskExtension old (F (slitBallBranch R i z)) := by
    intro i z hz
    have hzP := hsP i hz
    have hbranch : slitBallBranch R i z ∈ Metric.ball (0 : ℂ) R := by
      apply htP i
      rw [← himage i]
      exact mem_image_of_mem _ hz
    rw [diskExtension_coe d ⟨F z, Metric.ball_subset_closedBall (F.map_source hzP)⟩,
      hd, hOld _ (F.map_source hbranch)]
    change diskExtension u (e.symm (S (scaledSlitMap (R / 4)
      (S.symm ((R : ℂ) * (S z / (R : ℂ))))))) =
      diskExtension u (e.symm ((R : ℂ) * (S (slitBallBranch R i z) / (R : ℂ))))
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hRc,
      (hSnorm z (Metric.ball_subset_closedBall hzP)).2.2.1,
      heq i hz, ← mul_div_assoc, mul_div_cancel_left₀ _ hRc]
  have harea : riemannianArea g (diskExtension d) (Metric.ball (0 : ℂ) 1) =
      riemannianArea g (diskExtension old) (Metric.ball (0 : ℂ) 1) :=
    slit_conjugated_piecewise_area g F hOldLip hF hFi
      (slitBallCell R) (slitBallTarget R) (slitBallBranch R) kb lb
      hs ht hsP htP himage hsdisj htdisj hscover htcover hkb hlb hV
  calc
    riemannianDiskArea g d = riemannianArea g (diskExtension d) (Metric.ball (0 : ℂ) 1) :=
      riemannianArea_closedBall_eq_ball g (diskExtension d) 0 1
    _ = riemannianArea g (diskExtension old) (Metric.ball (0 : ℂ) 1) := harea
    _ = riemannianDiskArea g old :=
      (riemannianArea_closedBall_eq_ball g (diskExtension old) 0 1).symm
    _ = _ := riemannianDiskArea_diskThroughSourceChart g u huLip χ le_rfl hχsrc

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- One call to the actual slit-filling producer, retaining every returned
map, trace, range and Lipschitz property, now with both exact area equalities. -/
theorem exists_actual_branch_slit_filling_same_area
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (u : C(closedDisk, M))
    {L : ℝ≥0} (huLip : ∀ z w, riemannianEDistOf g (u z) (u w) ≤
      (L : ℝ≥0∞) * edist z w)
    (e S : OpenPartialHomeomorph ℂ ℂ) {R : ℝ} (hR : 0 < R)
    (he : ContDiffOn ℝ 1 (e : ℂ → ℂ) e.source)
    (hei : ContDiffOn ℝ 1 (e.symm : ℂ → ℂ) e.target)
    (heSource : e.source ⊆ Metric.ball (0 : ℂ) 1)
    (heBall : Metric.closedBall (0 : ℂ) R ⊆ e.target)
    (hSnorm : ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖S z‖ = ‖z‖ ∧ ‖S.symm z‖ = ‖z‖ ∧
      S.symm (S z) = z ∧ S (S.symm z) = z)
    {K J : ℝ≥0}
    (hSLip : LipschitzOnWith K (S : ℂ → ℂ) (Metric.closedBall (0 : ℂ) R))
    (hSiLip : LipschitzOnWith J (S.symm : ℂ → ℂ) (Metric.closedBall (0 : ℂ) R))
    (hpair : ∀ t ∈ Icc (0 : ℝ) R,
      diskExtension u (e.symm (S (t : ℂ))) =
        diskExtension u (e.symm (S (-(t : ℂ))))) :
    ∃ (χ : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ℂ ℂ 1)
      (d v : C(closedDisk, M)) (C A : ℝ≥0),
      (∀ z, χ z = e.symm ((R : ℂ) * z)) ∧
      (∀ z, χ.symm z = e z / (R : ℂ)) ∧
      Metric.closedBall (0 : ℂ) 1 ⊆ χ.source ∧
      χ '' Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball (0 : ℂ) 1 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        S (scaledSlitMap (R / 4) (S.symm ((R : ℂ) * z))) ∈ Metric.closedBall (0 : ℂ) R) ∧
      (∀ z : closedDisk, d z = diskExtension u
        (e.symm (S (scaledSlitMap (R / 4) (S.symm ((R : ℂ) * z)))))) ∧
      (∀ z w, riemannianEDistOf g (d z) (d w) ≤ (C : ℝ≥0∞) * edist z w) ∧
      (∀ z ∈ Metric.sphere (0 : ℂ) 1,
        diskExtension d z = diskExtension u (χ z)) ∧
      Set.range d ⊆ Set.range u ∧
      (∀ z w, riemannianEDistOf g (v z) (v w) ≤ (A : ℝ≥0∞) * edist z w) ∧
      diskTrace v = diskTrace u ∧ Set.range v ⊆ Set.range u ∧
      (∀ z : closedDisk, (z : ℂ) ∈ χ '' Metric.closedBall (0 : ℂ) 1 →
        v z = diskExtension d (χ.symm z)) ∧
      (∀ z : closedDisk, (z : ℂ) ∉ interior (χ '' Metric.closedBall (0 : ℂ) 1) →
        v z = u z) ∧
      riemannianDiskArea g v = riemannianDiskArea g u -
        riemannianArea g (diskExtension u) (χ '' Metric.closedBall (0 : ℂ) 1) +
        riemannianDiskArea g d ∧
      riemannianDiskArea g d = riemannianArea g (diskExtension u)
        (χ '' Metric.closedBall (0 : ℂ) 1) ∧
      riemannianDiskArea g v = riemannianDiskArea g u := by
  obtain ⟨χ, d, v, C, A, hχ, hχi, hχsrc, hχinside, hmap, hd, hdLip,
    hboundary, hdRange, hvLip, hvTrace, hvRange, hvIn, hvOut, hvArea⟩ :=
    exists_actual_branch_slit_filling g u huLip e S hR he hei heSource heBall
      hSnorm hSLip hSiLip hpair
  have hdArea := riemannianDiskArea_actual_branch_slit_filling g u d huLip e S hR
    χ hχ hχsrc hSnorm hSLip hSiLip hd
  refine ⟨χ, d, v, C, A, hχ, hχi, hχsrc, hχinside, hmap, hd, hdLip,
    hboundary, hdRange, hvLip, hvTrace, hvRange, hvIn, hvOut, hvArea, hdArea, ?_⟩
  rw [hvArea, hdArea]
  ring

end DifferentialGeometry.Geometry
