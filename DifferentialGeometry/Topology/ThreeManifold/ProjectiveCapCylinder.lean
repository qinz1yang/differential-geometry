import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardCylinderCover
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.SphereChartReparametrization
import DifferentialGeometry.Topology.Manifold.BallChartOrientation
import DifferentialGeometry.Topology.ThreeManifold.AntipodalPresentation
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorphTrans

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev E4 := EuclideanSpace ℝ (Fin 4)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev S3 := Metric.sphere (0 : E4) 1
private abbrev CI := (𝓡 2).prod 𝓘(ℝ, ℝ)

universe u

open ConnectedSumQuotient

section ScaledCaps

open Metric

variable {M : ConnectedClosedOrientedManifold.{u} 3}
  (c : OrientedBallChart M.toClosedOrientedManifold) (b : E3 → M.Carrier)
  (hchart : ∀ x, c.chart x = b ((4 / 5 : ℝ) • x))

private theorem scaled_ball_image (b : E3 → M.Carrier) :
    (fun x => b ((4 / 5 : ℝ) • x)) '' ball (0 : E3) (5 / 4) = b '' ball (0 : E3) 1 := by
  change (b ∘ fun x : E3 => (4 / 5 : ℝ) • x) '' ball 0 (5 / 4) = _
  rw [image_comp, Metric.smul_image_ball (by norm_num : (4 / 5 : ℝ) ≠ 0)]
  norm_num

include hchart

private theorem chart_image_ball_five_fourths_eq_of_scaled :
    c.chart '' ball (0 : E3) (5 / 4) = b '' ball (0 : E3) 1 := by
  have hfun : (c.chart : E3 → M.Carrier) = (fun x => b ((4 / 5 : ℝ) • x)) := funext hchart
  rw [hfun]
  exact scaled_ball_image b

private theorem mem_outerPunctured_iff_of_scaled (x : c.toBallChart.Punctured) :
    x ∈ outerPunctured c ↔ x.val ∈ (b '' ball (0 : E3) 1)ᶜ := by
  change x.val ∉ c.chart '' ball (0 : E3) (5 / 4) ↔ _
  rw [chart_image_ball_five_fourths_eq_of_scaled c b hchart]
  rfl

private theorem exists_outerPunctured_iff_of_scaled (x : M.Carrier) :
    (∃ y : outerPunctured c, y.val.val = x) ↔ x ∈ (b '' ball (0 : E3) 1)ᶜ := by
  constructor
  · rintro ⟨y,rfl⟩
    exact (mem_outerPunctured_iff_of_scaled c b hchart y.val).mp y.property
  · intro hx
    have hx' : x ∉ c.chart '' ball (0 : E3) (5 / 4) := by
      rwa [chart_image_ball_five_fourths_eq_of_scaled c b hchart]
    have hp : x ∉ c.chart '' ball (0 : E3) 1 := by
      exact fun h => hx' ((image_mono (ball_subset_ball (by norm_num))) h)
    exact ⟨⟨⟨x,hp⟩,hx'⟩,rfl⟩

private theorem range_outerPunctured_val_of_scaled :
    range (fun x : outerPunctured c => x.val.val) = (b '' ball (0 : E3) 1)ᶜ := by
  ext x
  exact exists_outerPunctured_iff_of_scaled c b hchart x

private theorem range_outerPunctured_map_of_scaled {P : Type*} (F : M.Carrier → P) :
    range (fun x : outerPunctured c => F x.val.val) = F '' (b '' ball (0 : E3) 1)ᶜ := by
  rw [← range_outerPunctured_val_of_scaled c b hchart]
  exact range_comp F (fun x : outerPunctured c => x.val.val)

private theorem outerLeftBoundary_val_of_scaled (z : S2) :
    (outerLeftBoundary c z).val.val = b z.val := by
  change c.chart ((5 / 4 : ℝ) • z.val) = _
  rw [hchart,smul_smul]
  norm_num

private theorem outerRightBoundary_val_of_scaled (a : BoundaryAttachment) (z : S2) :
    (outerRightBoundary c a z).val.val = b (a.val z).val :=
  outerLeftBoundary_val_of_scaled c b hchart (a.val z)


end ScaledCaps

private theorem standard_of_marked_ball_complements
    {M N : ConnectedClosedOrientedManifold.{u} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold)
    (d : OrientedBallChart N.toClosedOrientedManifold)
    (b₀ : E3 → M.Carrier) (b₁ : E3 → N.Carrier)
    (hc : ∀ x, c.chart x = b₀ ((4 / 5 : ℝ) • x))
    (hd : ∀ x, d.chart x = b₁ ((4 / 5 : ℝ) • x))
    {P : Type u} [TopologicalSpace P] [ChartedSpace E3 P] [T2Space P]
    (F₀ : PartialDiffeomorph (𝓡 3) (𝓡 3) M.Carrier P ∞)
    (F₁ : PartialDiffeomorph (𝓡 3) (𝓡 3) N.Carrier P ∞)
    (T : PartialDiffeomorph CI (𝓡 3) (S2 × ℝ) P ∞)
    (hF₀ : (b₀ '' Metric.ball 0 1)ᶜ ⊆ F₀.source)
    (hF₁ : (b₁ '' Metric.ball 0 1)ᶜ ⊆ F₁.source)
    (hTs : univ ×ˢ Icc (0 : ℝ) 1 ⊆ T.source)
    (hdisj : Disjoint (F₀ '' (b₀ '' Metric.ball 0 1)ᶜ)
      (F₁ '' (b₁ '' Metric.ball 0 1)ᶜ))
    (hcross₀ : ∀ q : S2 × unitInterval,
      T (q.1, q.2.val) ∈ F₀ '' (b₀ '' Metric.ball 0 1)ᶜ → q.2 = 0)
    (hcross₁ : ∀ q : S2 × unitInterval,
      T (q.1, q.2.val) ∈ F₁ '' (b₁ '' Metric.ball 0 1)ᶜ → q.2 = 1)
    (hcover : range (fun q : S2 × unitInterval => T (q.1, q.2.val)) ∪
      (F₀ '' (b₀ '' Metric.ball 0 1)ᶜ ∪ F₁ '' (b₁ '' Metric.ball 0 1)ᶜ) = univ)
    (hzero : ∀ z : S2, F₀ (b₀ z) = T (z, 0))
    (hone : ∀ z : S2, F₁ (b₁ (boundaryAttachment.val z)) = T (z, 1))
    (hM : isPoincareStandard M.Carrier) (hN : isPoincareStandard N.Carrier) :
    isPoincareStandard P := by
  have hcmem (x : outerPunctured c) : x.val.val ∈ (b₀ '' Metric.ball 0 1)ᶜ :=
    (mem_outerPunctured_iff_of_scaled c b₀ hc x.val).mp x.property
  have hdmem (x : outerPunctured d) : x.val.val ∈ (b₁ '' Metric.ball 0 1)ᶜ :=
    (mem_outerPunctured_iff_of_scaled d b₁ hd x.val).mp x.property
  have hz (z : S2) : T (z, 0) = F₀ (outerLeftBoundary c z).val.val := by
    rw [outerLeftBoundary_val_of_scaled c b₀ hc]
    exact (hzero z).symm
  have ho (z : S2) : T (z, 1) = F₁ (outerRightBoundary d boundaryAttachment z).val.val := by
    rw [outerRightBoundary_val_of_scaled d b₁ hd]
    exact (hone z).symm
  apply isPoincareStandard_of_outer_caps_cylinder_cover c d F₀ F₁ T
    (fun x => hF₀ (hcmem x)) (fun x => hF₁ (hdmem x)) hTs
    ?_ ?_ ?_ ?_ hz ho hM hN
  · simpa only [range_outerPunctured_map_of_scaled c b₀ hc,
      range_outerPunctured_map_of_scaled d b₁ hd] using hdisj
  · intro q x h
    have ht := hcross₀ q ⟨x.val.val, hcmem x, h.symm⟩
    refine ⟨ht, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply F₀.toPartialEquiv.injOn (hF₀ (hcmem _)) (hF₀ (hcmem x))
    rw [← hz]
    simpa [ht] using h
  · intro q x h
    have ht := hcross₁ q ⟨x.val.val, hdmem x, h.symm⟩
    refine ⟨ht, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply F₁.toPartialEquiv.injOn (hF₁ (hdmem _)) (hF₁ (hdmem x))
    rw [← ho]
    simpa [ht] using h
  · simpa only [range_outerPunctured_map_of_scaled c b₀ hc,
      range_outerPunctured_map_of_scaled d b₁ hd] using hcover

private theorem sphere_image_subset_ball_complement
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace E3 Z]
    (b : BallChart 3 (𝓡 3) Z) :
    b.chart '' Metric.sphere (0 : E3) 1 ⊆ (b.chart '' Metric.ball (0 : E3) 1)ᶜ := by
  rintro x ⟨q, hq, rfl⟩
  exact (b.boundaryMap ⟨q, hq⟩).property

theorem isPoincareStandard_of_projective_ball_complements_cylinder_cover
    {Z₀ Z₁ P : Type u}
    [TopologicalSpace Z₀] [ChartedSpace E3 Z₀] [IsManifold (𝓡 3) ∞ Z₀]
    [TopologicalSpace Z₁] [ChartedSpace E3 Z₁] [IsManifold (𝓡 3) ∞ Z₁]
    [TopologicalSpace P] [ChartedSpace E3 P] [T2Space P]
    (p₀ : S3 → Z₀) (p₁ : S3 → Z₁)
    (hp₀ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p₀)
    (hp₁ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p₁)
    (hsurj₀ : Surjective p₀) (hsurj₁ : Surjective p₁)
    (hfibers₀ : ∀ x y : S3, p₀ x = p₀ y ↔ x = y ∨ (x : E4) = -(y : E4))
    (hfibers₁ : ∀ x y : S3, p₁ x = p₁ y ↔ x = y ∨ (x : E4) = -(y : E4))
    (b₀ : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z₀ ∞)
    (b₁ : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z₁ ∞)
    (hb₀ : Metric.closedBall 0 2 ⊆ b₀.source)
    (hb₁ : Metric.closedBall 0 2 ⊆ b₁.source)
    (F₀ : PartialDiffeomorph (𝓡 3) (𝓡 3) Z₀ P ∞)
    (F₁ : PartialDiffeomorph (𝓡 3) (𝓡 3) Z₁ P ∞)
    (T : PartialDiffeomorph CI (𝓡 3) (S2 × ℝ) P ∞)
    (hF₀ : (b₀ '' Metric.ball 0 1)ᶜ ⊆ F₀.source)
    (hF₁ : (b₁ '' Metric.ball 0 1)ᶜ ⊆ F₁.source)
    (hTs : univ ×ˢ Icc (0 : ℝ) 1 ⊆ T.source)
    (hdisj : Disjoint (F₀ '' (b₀ '' Metric.ball 0 1)ᶜ)
      (F₁ '' (b₁ '' Metric.ball 0 1)ᶜ))
    (hcross₀ : ∀ q : S2 × unitInterval,
      T (q.1, q.2.val) ∈ F₀ '' (b₀ '' Metric.ball 0 1)ᶜ → q.2 = 0)
    (hcross₁ : ∀ q : S2 × unitInterval,
      T (q.1, q.2.val) ∈ F₁ '' (b₁ '' Metric.ball 0 1)ᶜ → q.2 = 1)
    (hcover : range (fun q : S2 × unitInterval => T (q.1, q.2.val)) ∪
      (F₀ '' (b₀ '' Metric.ball 0 1)ᶜ ∪ F₁ '' (b₁ '' Metric.ball 0 1)ᶜ) = univ)
    (hboundary₀ : F₀ '' (b₀ '' Metric.sphere (0 : E3) 1) =
      range (fun q : S2 => T (q, 0)))
    (hboundary₁ : F₁ '' (b₁ '' Metric.sphere (0 : E3) 1) =
      range (fun q : S2 => T (q, 1))) :
    isPoincareStandard P := by
  obtain ⟨o₀, e₀, _, _, _⟩ :=
    SphericalSpaceFormGroup.exists_oriented_antipodal_diffeomorph_of_presentation
      p₀ hp₀ hsurj₀ hfibers₀
  obtain ⟨o₁, e₁, _, _, _⟩ :=
    SphericalSpaceFormGroup.exists_oriented_antipodal_diffeomorph_of_presentation
      p₁ hp₁ hsurj₁ hfibers₁
  let : T2Space Z₀ := e₀.toHomeomorph.t2Space
  let : T2Space Z₁ := e₁.toHomeomorph.t2Space
  let : CompactSpace Z₀ := e₀.toHomeomorph.compactSpace
  let : CompactSpace Z₁ := e₁.toHomeomorph.compactSpace
  let : ConnectedSpace Z₀ := e₀.surjective.connectedSpace e₀.continuous
  let : ConnectedSpace Z₁ := e₁.surjective.connectedSpace e₁.continuous
  let M : ConnectedClosedOrientedManifold 3 := { Carrier := Z₀, orientation := o₀ }
  let N : ConnectedClosedOrientedManifold 3 := { Carrier := Z₁, orientation := o₁ }
  let B₀ : BallChart 3 (𝓡 3) Z₀ := ⟨b₀, hb₀⟩
  let B₁ : BallChart 3 (𝓡 3) Z₁ := ⟨b₁, hb₁⟩
  obtain ⟨_, b₀', _, _, _, himage₀, hsource₀, hzero⟩ :=
    Manifold.exists_sphere_chart_reparametrization_of_cylinder_boundary b₀ F₀ T
      B₀.sphere_subset_source
      ((sphere_image_subset_ball_complement B₀).trans hF₀)
      (fun q => hTs ⟨mem_univ q, by norm_num⟩) hboundary₀
  obtain ⟨_, b₁', _, _, _, himage₁, hsource₁, _, hone⟩ :=
    Manifold.exists_sphere_chart_reparametrization_of_cylinder_slice b₁ F₁ T
      boundaryAttachment.val 1 B₁.sphere_subset_source
      ((sphere_image_subset_ball_complement B₁).trans hF₁)
      (fun q => hTs ⟨mem_univ q, by norm_num⟩) hboundary₁
  let B₀' : BallChart 3 (𝓡 3) M.Carrier := ⟨b₀', hsource₀ 2 hb₀⟩
  let B₁' : BallChart 3 (𝓡 3) N.Carrier := ⟨b₁', hsource₁ 2 hb₁⟩
  have hM : isPoincareStandard Z₀ :=
    isPoincareStandard_of_antipodal_presentation p₀ hp₀ hsurj₀ hfibers₀
  have hN : isPoincareStandard Z₁ :=
    isPoincareStandard_of_antipodal_presentation p₁ hp₁ hsurj₁ hfibers₁
  have hF₀' : (b₀' '' Metric.ball 0 1)ᶜ ⊆ F₀.source := by
    rwa [himage₀]
  have hF₁' : (b₁' '' Metric.ball 0 1)ᶜ ⊆ F₁.source := by
    rwa [himage₁]
  have hdisj' : Disjoint (F₀ '' (b₀' '' Metric.ball 0 1)ᶜ)
      (F₁ '' (b₁' '' Metric.ball 0 1)ᶜ) := by
    rwa [himage₀, himage₁]
  have hcross₀' : ∀ q : S2 × unitInterval,
      T (q.1, q.2.val) ∈ F₀ '' (b₀' '' Metric.ball 0 1)ᶜ → q.2 = 0 := by
    simpa only [himage₀] using hcross₀
  have hcross₁' : ∀ q : S2 × unitInterval,
      T (q.1, q.2.val) ∈ F₁ '' (b₁' '' Metric.ball 0 1)ᶜ → q.2 = 1 := by
    simpa only [himage₁] using hcross₁
  have hcover' : range (fun q : S2 × unitInterval => T (q.1, q.2.val)) ∪
      (F₀ '' (b₀' '' Metric.ball 0 1)ᶜ ∪ F₁ '' (b₁' '' Metric.ball 0 1)ᶜ) = univ := by
    rwa [himage₀, himage₁]
  rcases B₀'.exists_oriented_scaled (4 / 5) (by norm_num) (by norm_num) with
    ⟨c, hc⟩ | ⟨c, hc⟩ <;>
    rcases B₁'.exists_oriented_scaled (4 / 5) (by norm_num) (by norm_num) with
      ⟨d, hd⟩ | ⟨d, hd⟩
  · exact standard_of_marked_ball_complements (M := M) (N := N) c d b₀' b₁' hc hd F₀ F₁ T
      hF₀' hF₁' hTs hdisj' hcross₀' hcross₁' hcover' hzero hone hM hN
  · exact standard_of_marked_ball_complements (M := M) (N := N.opposite) c d b₀' b₁' hc hd F₀ F₁ T
      hF₀' hF₁' hTs hdisj' hcross₀' hcross₁' hcover' hzero hone hM hN
  · exact standard_of_marked_ball_complements (M := M.opposite) (N := N) c d b₀' b₁' hc hd F₀ F₁ T
      hF₀' hF₁' hTs hdisj' hcross₀' hcross₁' hcover' hzero hone hM hN
  · exact standard_of_marked_ball_complements (M := M.opposite) (N := N.opposite) c d b₀' b₁' hc hd F₀ F₁ T
      hF₀' hF₁' hTs hdisj' hcross₀' hcross₁' hcover' hzero hone hM hN

end DifferentialGeometry.Topology

open Metric Manifold

namespace PartialDiffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

private theorem exists_scaled_ball_chart (b : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    (hb : closedBall (0 : E) 2 ⊆ b.source) :
    ∃ R > 1, ∃ b' : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      closedBall (0 : E) (2 * R) ⊆ b.source ∧
      closedBall (0 : E) 2 ⊆ b'.source ∧
      (∀ x, b' x = b (R • x)) ∧
      b' '' ball (0 : E) 1 = b '' ball (0 : E) R ∧
      b' '' sphere (0 : E) 1 = b '' sphere (0 : E) R := by
  obtain ⟨δ, hδ, hδsub⟩ :=
    (isCompact_closedBall (0 : E) 2).exists_cthickening_subset_open b.open_source hb
  let r := δ + 2
  have hr : 2 < r := by dsimp [r]; linarith
  have hsub : closedBall (0 : E) r ⊆ b.source := by
    simpa only [cthickening_closedBall hδ.le (by norm_num : (0 : ℝ) ≤ 2)] using hδsub
  let R := r / 2
  have hR : 0 < R := by dsimp [R]; linarith
  have hR1 : 1 < R := by dsimp [R]; linarith
  have hrad : 2 * R = r := by dsimp [R]; ring
  have hsource : closedBall (0 : E) (2 * R) ⊆ b.source := by rwa [hrad]
  let D := (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E)
    (Units.mk0 R hR.ne')).toDiffeomorph
  let b' := D.toPartialDiffeomorph.trans b
  refine ⟨R, hR1, b', hsource, ?_, fun _ => rfl, ?_, ?_⟩
  · intro x hx
    refine ⟨mem_univ _, hsource ?_⟩
    change R • x ∈ closedBall (0 : E) (2 * R)
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have hn := mem_closedBall_zero_iff.mp hx
    nlinarith
  · change (fun x : E => b (R • x)) '' ball (0 : E) 1 = _
    rw [← Set.image_image]
    congr 1
    simpa only [smul_zero, Real.norm_of_nonneg hR.le, mul_one] using
      Metric.smul_image_ball hR.ne' (0 : E) 1
  · change (fun x : E => b (R • x)) '' sphere (0 : E) 1 = _
    rw [← Set.image_image]
    congr 1
    simpa only [smul_zero, Real.norm_of_nonneg hR.le, mul_one] using
      Metric.smul_image_sphere hR.ne' (0 : E) 1

end PartialDiffeomorph

namespace DifferentialGeometry.Topology.Manifold

private theorem compl_image_ball_subset {E Z : Type*} [PseudoMetricSpace E]
    (b : E → Z) (c : E) {r R : ℝ} (h : r ≤ R) :
    (b '' ball c R)ᶜ ⊆ (b '' ball c r)ᶜ :=
  compl_subset_compl.mpr (image_mono (ball_subset_ball h))

private theorem compl_image_ball_eq_union_annulus {E Z : Type*} [PseudoMetricSpace E]
    (b : E → Z) (c : E) {r R : ℝ} (h : r ≤ R)
    (hb : InjOn b (closedBall c R)) :
    (b '' ball c r)ᶜ = (b '' ball c R)ᶜ ∪ b '' (closedBall c R \ ball c r) := by
  have hsub : ball c r ⊆ closedBall c R :=
    (ball_subset_ball h).trans ball_subset_closedBall
  rw [hb.image_sdiff_subset hsub]
  ext z
  constructor
  · intro hz
    by_cases hzR : z ∈ b '' ball c R
    · exact Or.inr ⟨image_mono ball_subset_closedBall hzR, hz⟩
    · exact Or.inl hzR
  · rintro (hz | hz)
    · exact compl_image_ball_subset b c h hz
    · exact hz.2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  {E' E'' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E' H} {J : ModelWithCorners ℝ E'' H'}
  {Z P : Type*} [TopologicalSpace Z] [ChartedSpace H Z]
  [TopologicalSpace P] [ChartedSpace H' P]

private theorem ballComplementRadialCollar_image_unit_slab
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (v : sphere (0 : E) 1) {R : ℝ} (hR : 1 < R) :
    ballComplementRadialCollar (n := n) b F v R hR.ne' '' (univ ×ˢ Icc (0 : ℝ) 1) =
      F '' (b '' (closedBall (0 : E) R \ ball (0 : E) 1)) := by
  ext y
  constructor
  · rintro ⟨⟨z, t⟩, ht, rfl⟩
    have hr : R + (1 - R) * t ∈ Icc (1 : ℝ) R := by
      constructor <;> nlinarith [ht.2.1, ht.2.2]
    have hn : ‖(R + (1 - R) * t) • (z : E)‖ = R + (1 - R) * t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hr.1]),
        norm_eq_of_mem_sphere, mul_one]
    rw [ballComplementRadialCollar_apply]
    refine ⟨b ((R + (1 - R) * t) • (z : E)),
      ⟨(R + (1 - R) * t) • (z : E), ?_, rfl⟩, rfl⟩
    simp only [mem_sdiff, mem_closedBall_zero_iff, mem_ball_zero_iff, hn]
    exact ⟨hr.2, not_lt_of_ge hr.1⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hnx : 1 ≤ ‖x‖ := by
      simpa only [mem_ball_zero_iff, not_lt] using hx.2
    have hxR : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx.1
    have hx0 : x ≠ 0 := by
      intro hzero
      simp only [hzero, norm_zero] at hnx
      linarith
    let t : ℝ := (R - ‖x‖) / (R - 1)
    have ht : t ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hxR) (sub_nonneg.mpr hR.le)
      · exact (div_le_one (sub_pos.mpr hR)).mpr (by linarith)
    have heq : R + (1 - R) * t = ‖x‖ := by
      dsimp [t]
      field_simp [sub_ne_zero.mpr hR.ne']
      ring
    refine ⟨(sphereDirection v x, t), ⟨mem_univ _, ht⟩, ?_⟩
    rw [ballComplementRadialCollar_apply, heq, norm_smul_sphereDirection v hx0]

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]
  {E' E'' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E' H} {J : ModelWithCorners ℝ E'' H'}
  {Z P : Type*} [TopologicalSpace Z] [ChartedSpace H Z]
  [TopologicalSpace P] [ChartedSpace H' P]

private theorem sphere_image_mem_ball_complement
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞) {R : ℝ} (hR : 1 ≤ R)
    (hb : closedBall (0 : E) R ⊆ b.source) {w : E} (hw : w ∈ sphere (0 : E) 1) :
    b w ∈ (b '' ball (0 : E) 1)ᶜ := by
  rintro ⟨u, hu, heq⟩
  have hus : u ∈ b.source :=
    hb ((closedBall_subset_closedBall hR) (ball_subset_closedBall hu))
  have hws : w ∈ b.source :=
    hb ((closedBall_subset_closedBall hR) (sphere_subset_closedBall hw))
  have huw := b.injOn hus hws heq
  have hlt := mem_ball_zero_iff.mp hu
  rw [huw, mem_sphere_zero_iff_norm.mp hw] at hlt
  exact lt_irrefl 1 hlt

private theorem ballComplementRadialCollar_time_eq_zero_of_mem_outer_complement
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (v : sphere (0 : E) 1) {R : ℝ} (hR : 1 < R)
    (hb : closedBall (0 : E) R ⊆ b.source)
    (hF : (b '' ball (0 : E) 1)ᶜ ⊆ F.source)
    (q : sphere (0 : E) 1 × ℝ) (hq : q.2 ∈ Icc (0 : ℝ) 1)
    (hmem : ballComplementRadialCollar (n := n) b F v R hR.ne' q ∈
      F '' (b '' ball (0 : E) R)ᶜ) : q.2 = 0 := by
  have hr : 1 ≤ R + (1 - R) * q.2 := by nlinarith [hq.2]
  have hn : ‖(R + (1 - R) * q.2) • (q.1 : E)‖ = R + (1 - R) * q.2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith),
      norm_eq_of_mem_sphere, mul_one]
  have hqs : b ((R + (1 - R) * q.2) • (q.1 : E)) ∈ F.source :=
    (unit_slab_subset_ballComplementRadialCollar_source (n := n) b F v hR hb hF
      ⟨mem_univ _, hq⟩).2
  rcases hmem with ⟨y, hy, heq⟩
  have hys : y ∈ F.source := hF (fun hy1 =>
    hy ((image_mono (ball_subset_ball hR.le)) hy1))
  have hyq := F.injOn hys hqs heq
  by_contra hne
  have ht : 0 < q.2 := lt_of_le_of_ne hq.1 (Ne.symm hne)
  apply hy
  rw [hyq]
  refine ⟨_, ?_, rfl⟩
  rw [mem_ball_zero_iff, hn]
  nlinarith

private theorem ballComplementRadialCollar_time_eq_one_of_mem_inner_sphere
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞)
    (v : sphere (0 : E) 1) {R : ℝ} (hR : 1 < R)
    (hb : closedBall (0 : E) R ⊆ b.source)
    (hF : (b '' ball (0 : E) 1)ᶜ ⊆ F.source)
    (q : sphere (0 : E) 1 × ℝ) (hq : q.2 ∈ Icc (0 : ℝ) 1)
    (hmem : ballComplementRadialCollar (n := n) b F v R hR.ne' q ∈
      F '' (b '' sphere (0 : E) 1)) : q.2 = 1 := by
  have hr : R + (1 - R) * q.2 ∈ Icc (1 : ℝ) R := by
    constructor <;> nlinarith [hq.1, hq.2]
  have hn : ‖(R + (1 - R) * q.2) • (q.1 : E)‖ = R + (1 - R) * q.2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith [hr.1]),
      norm_eq_of_mem_sphere, mul_one]
  have hqs : b ((R + (1 - R) * q.2) • (q.1 : E)) ∈ F.source :=
    (unit_slab_subset_ballComplementRadialCollar_source (n := n) b F v hR hb hF
      ⟨mem_univ _, hq⟩).2
  rcases hmem with ⟨_, ⟨w, hw, rfl⟩, heq⟩
  have hws : w ∈ b.source :=
    hb ((closedBall_subset_closedBall hR.le) (sphere_subset_closedBall hw))
  have hbqs : (R + (1 - R) * q.2) • (q.1 : E) ∈ b.source := by
    apply hb
    rw [mem_closedBall_zero_iff, hn]
    exact hr.2
  have hwq := b.injOn hws hbqs
    (F.injOn (hF (sphere_image_mem_ball_complement b hR.le hb hw)) hqs heq)
  have hnw := mem_sphere_zero_iff_norm.mp hw
  rw [hwq, hn] at hnw
  nlinarith

private theorem disjoint_image_outer_ball_complement_image_inner_sphere
    (b : PartialDiffeomorph 𝓘(ℝ, E) I E Z ∞)
    (F : PartialDiffeomorph I J Z P ∞) {R : ℝ} (hR : 1 < R)
    (hb : closedBall (0 : E) 1 ⊆ b.source)
    (hF : (b '' ball (0 : E) 1)ᶜ ⊆ F.source) :
    Disjoint (F '' (b '' ball (0 : E) R)ᶜ) (F '' (b '' sphere (0 : E) 1)) := by
  rw [disjoint_left]
  rintro _ ⟨y, hy, rfl⟩ ⟨_, ⟨w, hw, rfl⟩, heq⟩
  have hys : y ∈ F.source := hF (fun hy1 =>
    hy ((image_mono (ball_subset_ball hR.le)) hy1))
  have hwy := F.injOn (hF (sphere_image_mem_ball_complement b le_rfl hb hw)) hys heq
  apply hy
  rw [← hwy]
  exact ⟨w, (sphere_subset_ball hR) hw, rfl⟩

end DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Topology

universe u

private abbrev SharedE3 := EuclideanSpace ℝ (Fin 3)

private theorem compact_ball_complement
    {Z : Type*} [TopologicalSpace Z] [ChartedSpace SharedE3 Z] [CompactSpace Z]
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) SharedE3 Z ∞)
    (hb : closedBall (0 : SharedE3) 1 ⊆ b.source) :
    IsCompact (b '' ball (0 : SharedE3) 1)ᶜ :=
  (b.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
    (ball_subset_closedBall.trans hb)).isClosed_compl.isCompact

private theorem frontier_ball_complement_image
    {Z P : Type*} [TopologicalSpace Z] [ChartedSpace SharedE3 Z] [CompactSpace Z] [T2Space Z]
    [TopologicalSpace P] [ChartedSpace SharedE3 P] [T2Space P]
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) SharedE3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z P ∞)
    (hb : closedBall (0 : SharedE3) 1 ⊆ b.source)
    (hF : (b '' ball (0 : SharedE3) 1)ᶜ ⊆ F.source) :
    F '' (b '' sphere (0 : SharedE3) 1) = frontier (F '' (b '' ball (0 : SharedE3) 1)ᶜ) :=
  Manifold.image_sphere_eq_frontier_of_ball_complement b F hb
    (compact_ball_complement b hb) hF


theorem isPoincareStandard_of_projective_ball_complement_cover
    {Z₀ Z₁ P : Type u}
    [TopologicalSpace Z₀] [ChartedSpace E3 Z₀] [IsManifold (𝓡 3) ∞ Z₀]
    [TopologicalSpace Z₁] [ChartedSpace E3 Z₁] [IsManifold (𝓡 3) ∞ Z₁]
    [TopologicalSpace P] [ChartedSpace E3 P] [T2Space P]
    (p₀ : S3 → Z₀) (p₁ : S3 → Z₁)
    (hp₀ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p₀)
    (hp₁ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p₁)
    (hsurj₀ : Surjective p₀) (hsurj₁ : Surjective p₁)
    (hfibers₀ : ∀ x y : S3, p₀ x = p₀ y ↔ x = y ∨ (x : E4) = -(y : E4))
    (hfibers₁ : ∀ x y : S3, p₁ x = p₁ y ↔ x = y ∨ (x : E4) = -(y : E4))
    (b₀ : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z₀ ∞)
    (b₁ : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z₁ ∞)
    (hb₀ : Metric.closedBall 0 2 ⊆ b₀.source)
    (hb₁ : Metric.closedBall 0 2 ⊆ b₁.source)
    (F₀ : PartialDiffeomorph (𝓡 3) (𝓡 3) Z₀ P ∞)
    (F₁ : PartialDiffeomorph (𝓡 3) (𝓡 3) Z₁ P ∞)
    (hF₀ : (b₀ '' Metric.ball 0 1)ᶜ ⊆ F₀.source)
    (hF₁ : (b₁ '' Metric.ball 0 1)ᶜ ⊆ F₁.source)
    (hinter : (F₁ '' (b₁ '' Metric.ball 0 1)ᶜ) ∩ (F₀ '' (b₀ '' Metric.ball 0 1)ᶜ) =
      frontier (F₀ '' (b₀ '' Metric.ball 0 1)ᶜ))
    (hfrontier : frontier (F₁ '' (b₁ '' Metric.ball 0 1)ᶜ) =
      frontier (F₀ '' (b₀ '' Metric.ball 0 1)ᶜ))
    (hcover : (F₀ '' (b₀ '' Metric.ball 0 1)ᶜ) ∪
      (F₁ '' (b₁ '' Metric.ball 0 1)ᶜ) = univ) :
    isPoincareStandard P := by
  obtain ⟨e₀, _, _⟩ := SphericalSpaceFormGroup.exists_antipodal_diffeomorph_of_presentation
    p₀ hp₀ hsurj₀ hfibers₀
  obtain ⟨e₁, _, _⟩ := SphericalSpaceFormGroup.exists_antipodal_diffeomorph_of_presentation
    p₁ hp₁ hsurj₁ hfibers₁
  let : T2Space Z₀ := e₀.toHomeomorph.t2Space
  let : T2Space Z₁ := e₁.toHomeomorph.t2Space
  let : CompactSpace Z₀ := e₀.toHomeomorph.compactSpace
  let : CompactSpace Z₁ := e₁.toHomeomorph.compactSpace
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  have hb₀1 : closedBall (0 : E3) 1 ⊆ b₀.source :=
    (closedBall_subset_closedBall (by norm_num)).trans hb₀
  have hb₁1 : closedBall (0 : E3) 1 ⊆ b₁.source :=
    (closedBall_subset_closedBall (by norm_num)).trans hb₁
  have hfr₀ := frontier_ball_complement_image b₀ F₀ hb₀1 hF₀
  have hfr₁ := frontier_ball_complement_image b₁ F₁ hb₁1 hF₁
  obtain ⟨R,hR,bR,hbRsrc,hbR,hbRapply,hbRball,hbRsphere⟩ :=
    PartialDiffeomorph.exists_scaled_ball_chart b₀ hb₀
  have hb₀R : closedBall (0 : E3) R ⊆ b₀.source :=
    (closedBall_subset_closedBall (by linarith)).trans hbRsrc
  have hsub : (b₀ '' ball (0 : E3) R)ᶜ ⊆ (b₀ '' ball (0 : E3) 1)ᶜ :=
    Manifold.compl_image_ball_subset b₀ 0 hR.le
  have hFR : (bR '' ball (0 : E3) 1)ᶜ ⊆ F₀.source := by
    rw [hbRball]
    exact hsub.trans hF₀
  let v : S2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let T := Manifold.ballComplementRadialCollar (n := 2) b₀ F₀ v R hR.ne'
  have hTs : univ ×ˢ Icc (0 : ℝ) 1 ⊆ T.source :=
    Manifold.unit_slab_subset_ballComplementRadialCollar_source b₀ F₀ v hR hb₀R hF₀
  have hTi : T '' (univ ×ˢ Icc (0 : ℝ) 1) ⊆ F₀ '' (b₀ '' ball (0 : E3) 1)ᶜ :=
    Manifold.ballComplementRadialCollar_image_unit_slab_subset b₀ F₀ v hR hb₀R
  have hTr : range (fun q : S2 × unitInterval => T (q.1,q.2.val)) =
      T '' (univ ×ˢ Icc (0 : ℝ) 1) := by
    ext y
    constructor
    · rintro ⟨q,rfl⟩
      exact ⟨(q.1,q.2.val),⟨mem_univ _,q.2.property⟩,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨(q.1,⟨q.2,hq.2⟩),rfl⟩
  have hdis : Disjoint (F₀ '' (bR '' ball (0 : E3) 1)ᶜ)
      (F₁ '' (b₁ '' ball (0 : E3) 1)ᶜ) := by
    rw [hbRball,disjoint_left]
    intro y hy₀ hy₁
    have hyK : y ∈ F₀ '' (b₀ '' ball (0 : E3) 1)ᶜ := image_mono hsub hy₀
    have hys : y ∈ F₀ '' (b₀ '' sphere (0 : E3) 1) := by
      rw [hfr₀,← hinter]
      exact ⟨hy₁,hyK⟩
    exact (disjoint_left.mp
      (Manifold.disjoint_image_outer_ball_complement_image_inner_sphere b₀ F₀ hR hb₀1 hF₀)) hy₀ hys
  have hc₀ (q : S2 × unitInterval)
      (hq : T (q.1,q.2.val) ∈ F₀ '' (bR '' ball (0 : E3) 1)ᶜ) : q.2 = 0 := by
    apply Subtype.ext
    exact Manifold.ballComplementRadialCollar_time_eq_zero_of_mem_outer_complement
      b₀ F₀ v hR hb₀R hF₀ (q.1,q.2.val) q.2.property (by simpa only [hbRball] using hq)
  have hc₁ (q : S2 × unitInterval)
      (hq : T (q.1,q.2.val) ∈ F₁ '' (b₁ '' ball (0 : E3) 1)ᶜ) : q.2 = 1 := by
    apply Subtype.ext
    apply Manifold.ballComplementRadialCollar_time_eq_one_of_mem_inner_sphere (n := 2)
      b₀ F₀ v hR hb₀R hF₀ (q.1,q.2.val) q.2.property
    rw [hfr₀,← hinter]
    exact ⟨hq,hTi ⟨(q.1,q.2.val),⟨mem_univ _,q.2.property⟩,rfl⟩⟩
  have hdecomp : F₀ '' (b₀ '' ball (0 : E3) 1)ᶜ =
      (F₀ '' (bR '' ball (0 : E3) 1)ᶜ) ∪ range (fun q : S2 × unitInterval => T (q.1,q.2.val)) := by
    rw [hbRball,hTr,Manifold.ballComplementRadialCollar_image_unit_slab b₀ F₀ v hR]
    rw [Manifold.compl_image_ball_eq_union_annulus b₀ 0 hR.le (b₀.injOn.mono hb₀R),image_union]
  have hcov : range (fun q : S2 × unitInterval => T (q.1,q.2.val)) ∪
      (F₀ '' (bR '' ball (0 : E3) 1)ᶜ ∪ F₁ '' (b₁ '' ball (0 : E3) 1)ᶜ) = univ := by
    rw [hdecomp] at hcover
    calc
      _ = (F₀ '' (bR '' ball (0 : E3) 1)ᶜ ∪ range (fun q : S2 × unitInterval => T (q.1,q.2.val))) ∪
          F₁ '' (b₁ '' ball (0 : E3) 1)ᶜ := by rw [union_left_comm, ← union_assoc]
      _ = univ := hcover
  have hbd₀ : F₀ '' (bR '' sphere (0 : E3) 1) = range (fun q : S2 => T (q,0)) := by
    ext y
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      refine ⟨⟨z,hz⟩,?_⟩
      change F₀ (b₀ ((R+(1-R)*0) • z)) = F₀ (bR z)
      rw [hbRapply,mul_zero,add_zero]
    · rintro ⟨z,rfl⟩
      refine ⟨bR z,⟨z,z.property,rfl⟩,?_⟩
      change F₀ (bR z) = F₀ (b₀ ((R+(1-R)*0) • z.val))
      rw [hbRapply,mul_zero,add_zero]
  have hbd₁ : F₁ '' (b₁ '' sphere (0 : E3) 1) = range (fun q : S2 => T (q,1)) := by
    rw [hfr₁,hfrontier,← hfr₀]
    ext y
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨⟨z,hz⟩,Manifold.ballComplementRadialCollar_apply_one b₀ F₀ v ⟨z,hz⟩ R hR.ne'⟩
    · rintro ⟨z,rfl⟩
      exact ⟨b₀ z,⟨z,z.property,rfl⟩,
        (Manifold.ballComplementRadialCollar_apply_one b₀ F₀ v z R hR.ne').symm⟩
  exact isPoincareStandard_of_projective_ball_complements_cylinder_cover
    p₀ p₁ hp₀ hp₁ hsurj₀ hsurj₁ hfibers₀ hfibers₁ bR b₁ hbR hb₁ F₀ F₁ T
    hFR hF₁ hTs hdis hc₀ hc₁ hcov hbd₀ hbd₁


end DifferentialGeometry.Topology
