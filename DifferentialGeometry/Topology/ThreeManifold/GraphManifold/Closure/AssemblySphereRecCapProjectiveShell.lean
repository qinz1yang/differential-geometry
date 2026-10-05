import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereRecShellChart
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyCycleHalfSpace
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingInterior
import DifferentialGeometry.Topology.Manifold.InjectiveLocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.InverseFunction.ContDiffOn
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import DifferentialGeometry.Topology.ThreeManifold.Geometrization.NoCuts

/-!
# FC42 sphere recursion, packet S3b (tools): the complement of a ball chart as a piece

Lane ASM-SPH3. Let `Y` be a closed three-manifold, `c` a chart of `Y` defined on the closed ball of
radius `2`, and `f : M → Y` a smooth embedding of a compact three-manifold with boundary whose image
is the complement of the open unit ball `c (B¹)` (the data of a punctured-`ℝP³` zero vertex):

* `isBoundaryPoint_iff_mem_image_sphere`: the model boundary of `M` is exactly `f⁻¹ (c (S²))`
  (interior criterion `immersion_image_mem_nhds`; boundary criterion
  `not_mem_interior_range_of_isBoundaryPoint` read on the carrier `NoCuts.carrier Y`);
* `exists_partialDiffeomorph_comp_inv`: for a smooth injective full-rank `g : M → T` into a
  three-manifold without boundary, `g ∘ f⁻¹` is a partial diffeomorphism of `Y` with source the
  open complement of `c (closed unit ball)`;
* `shellRadial`: the radial shell `(z, t) ↦ (1 + t / 2) z` of `S² × [0, 1]`, smooth with bijective
  differential, and the shell map `g ∘ f⁻¹ ∘ c ∘ shellRadial` (`shellLift`), smooth, injective and of
  bijective differential (`IsSmoothEmbedding.contMDiff_lift`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
open GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-! ## The radial shell -/

/-- The radial shell `(z, t) ↦ (1 + t / 2) z` between the spheres of radius `1` and `3 / 2`. -/
def shellRadial (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) :
    EuclideanSpace ℝ (Fin 3) :=
  (1 + (p.2 : ℝ) / 2) • (p.1 : EuclideanSpace ℝ (Fin 3))

theorem norm_shellRadial (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) :
    ‖shellRadial p‖ = 1 + (p.2 : ℝ) / 2 := by
  have h0 : (0 : ℝ) ≤ p.2 := p.2.2.1
  rw [shellRadial, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith), norm_eq_of_mem_sphere,
    mul_one]

theorem one_le_norm_shellRadial (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) :
    1 ≤ ‖shellRadial p‖ := by
  rw [norm_shellRadial]
  linarith [p.2.2.1]

theorem norm_shellRadial_le (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) :
    ‖shellRadial p‖ ≤ 3 / 2 := by
  rw [norm_shellRadial]
  linarith [p.2.2.2]

theorem shellRadial_injective : Injective shellRadial := by
  intro p q h
  have hn := congrArg norm h
  rw [norm_shellRadial, norm_shellRadial] at hn
  have ht : (p.2 : ℝ) = q.2 := by linarith
  have hpos : (1 + (p.2 : ℝ) / 2) ≠ 0 := by linarith [p.2.2.1]
  have hz : (p.1 : EuclideanSpace ℝ (Fin 3)) = q.1 := by
    have h' : (1 + (p.2 : ℝ) / 2) • (p.1 : EuclideanSpace ℝ (Fin 3)) =
        (1 + (p.2 : ℝ) / 2) • (q.1 : EuclideanSpace ℝ (Fin 3)) := by
      have h1 : shellRadial p = shellRadial q := h
      unfold shellRadial at h1
      rw [h1, ht]
    exact smul_right_injective _ hpos h'
  exact Prod.ext (Subtype.ext hz) (Subtype.ext ht)

theorem contMDiff_shellRadial : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ shellRadial := by
  have ht : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) 𝓘(ℝ, ℝ) ∞
      (fun p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 =>
        1 + (p.2 : ℝ) / 2) := by
    have hs : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) :=
      contMDiff_subtypeVal_Icc
    have ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun t : ℝ => 1 + t / 2) :=
      (contDiff_const.add (contDiff_id.div_const 2)).contMDiff
    exact ha.comp (hs.comp contMDiff_snd)
  exact ht.smul (contMDiff_coe_sphere.comp contMDiff_fst)

/-- The affine diffeomorphism `t ↦ 1 + t / 2` of the line. -/
def shellAffineHalf : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ where
  toFun t := 1 + t / 2
  invFun t := 2 * (t - 1)
  left_inv t := by dsimp; ring
  right_inv t := by dsimp; ring
  contMDiff_toFun := (contDiff_const.add (contDiff_id.div_const 2)).contMDiff
  contMDiff_invFun := (contDiff_const.mul (contDiff_id.sub contDiff_const)).contMDiff

theorem mfderiv_shellRadial_bijective
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) shellRadial p) := by
  let e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ := Prod.map id Subtype.val
  have hs : IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) :=
    isSmoothEmbedding_subtypeVal_Icc
  have he : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e :=
    contMDiff_id.prodMap hs.contMDiff
  have hBe : Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) e p) := by
    have hBs : Bijective (mfderiv (𝓡∂ 1) 𝓘(ℝ, ℝ) (fun z : Icc (0 : ℝ) 1 => (z : ℝ)) p.2) :=
      bijective_mfderiv_of_isImmersionAt (𝓡∂ 1) 𝓘(ℝ, ℝ) _ p.2
        (hs.isImmersion.isImmersionAt p.2) (by simp)
    rw [mfderiv_prodMap mdifferentiableAt_id (hs.contMDiff.mdifferentiable (by simp) _), mfderiv_id]
    exact Function.bijective_id.prodMap hBs
  let R : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ))
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ∞ :=
    (Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
      shellAffineHalf
  let g : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun q => (R q).2 • ((R q).1 : EuclideanSpace ℝ (Fin 3))
  have hpos : 0 < (R (e p)).2 := by
    change 0 < 1 + (p.2 : ℝ) / 2
    linarith [p.2.2.1]
  have hg : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ g (e p) :=
    (R.isLocalDiffeomorph (e p)).comp (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      (isLocalDiffeomorphAt_sphere_smul (R (e p)) hpos)
  have hBg : Bijective (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) g (e p)) :=
    (hg.mfderivToContinuousLinearEquiv (by simp)).bijective
  have hcomp : shellRadial = g ∘ e := rfl
  rw [hcomp, mfderiv_comp p (hg.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))]
  exact hBg.comp hBe

/-! ## The complement of a ball chart as the image of a piece -/

section Punctured

variable {Y : ConnectedClosedOrientedManifold.{u} 3}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
  [IsManifold (𝓡∂ 3) ∞ M] [CompactSpace M]
  (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
    Y.Carrier ∞)
  {f : M → Y.Carrier}

omit [IsManifold (𝓡∂ 3) ∞ M] [CompactSpace M] in
/-- The differential of a full-dimensional smooth embedding is bijective. -/
theorem mfderiv_bijective_of_isSmoothEmbedding (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f) (q : M) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3) f q) :=
  bijective_mfderiv_of_isImmersionAt (𝓡∂ 3) (𝓡 3) f q (hf.isImmersion.isImmersionAt q) (by simp)

omit [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
  [CompactSpace M] in
/-- The interior of the complement of an open unit ball chart image. -/
theorem interior_range_eq_compl_image_closedBall
    (hc : Metric.closedBall 0 1 ⊆ c.source)
    (hrange : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}) :
    interior (range f) = (c '' Metric.closedBall 0 1)ᶜ := by
  rw [hrange]
  change interior (c '' Metric.ball 0 1)ᶜ = _
  rw [interior_compl, closure_image_ball_of_partialDiffeomorph c hc]

omit [IsManifold (𝓡∂ 3) ∞ M] in
/-- **Boundary of the punctured piece.** A model-boundary point goes to the sphere `c (S²)`. -/
theorem mem_image_sphere_of_isBoundaryPoint (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 1 ⊆ c.source)
    (hrange : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    {q : M} (hq : (𝓡∂ 3).IsBoundaryPoint q) :
    f q ∈ c '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have hnot : f q ∉ interior (range f) :=
    not_mem_interior_range_of_isBoundaryPoint (W := NoCuts.carrier Y) (F := f) hf.contMDiff
      (mfderiv_bijective_of_isSmoothEmbedding hf) hf.isEmbedding.injective hq
      BoundarylessManifold.isInteriorPoint
  rw [interior_range_eq_compl_image_closedBall c hc hrange, notMem_compl_iff] at hnot
  obtain ⟨x, hx, hxq⟩ := hnot
  have hfq : f q ∈ range f := ⟨q, rfl⟩
  rw [hrange] at hfq
  refine ⟨x, ?_, hxq⟩
  rw [mem_sphere_zero_iff_norm]
  refine le_antisymm (mem_closedBall_zero_iff.mp hx) (le_of_not_gt fun hlt => hfq ?_)
  exact ⟨x, mem_ball_zero_iff.mpr hlt, hxq⟩

omit [CompactSpace M] in
/-- **Interior of the punctured piece.** A model-interior point goes off the closed ball
`c (B̄¹)`. -/
theorem notMem_image_closedBall_of_isInteriorPoint (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 1 ⊆ c.source)
    (hrange : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    {q : M} (hq : (𝓡∂ 3).IsInteriorPoint q) :
    f q ∉ c '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have hnhds : range f ∈ 𝓝 (f q) := by
    simpa only [image_univ] using
      DifferentialGeometry.Topology.immersion_image_mem_nhds (hf.isImmersion.isImmersionAt q)
        (by simp) hq (s := univ) Filter.univ_mem
  have hint : f q ∈ interior (range f) := mem_interior_iff_mem_nhds.mpr hnhds
  rw [interior_range_eq_compl_image_closedBall c hc hrange] at hint
  exact hint

/-- **The model boundary of the punctured piece is `f⁻¹ (c (S²))`.** -/
theorem isBoundaryPoint_iff_mem_image_sphere (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 1 ⊆ c.source)
    (hrange : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1}) {q : M} :
    (𝓡∂ 3).IsBoundaryPoint q ↔ f q ∈ c '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  refine ⟨mem_image_sphere_of_isBoundaryPoint c hf hc hrange, fun h => ?_⟩
  rcases (𝓡∂ 3).isInteriorPoint_or_isBoundaryPoint q with hq | hq
  · exact absurd (image_mono sphere_subset_closedBall h)
      (notMem_image_closedBall_of_isInteriorPoint c hf hc hrange hq)
  · exact hq

variable {T : Type*} [TopologicalSpace T] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) T]
  [IsManifold (𝓡 3) ∞ T]

/-- **`g ∘ f⁻¹` is a partial diffeomorphism** on the open complement of `c (B̄¹)`, for a smooth
injective full-rank `g` into a manifold without boundary. -/
theorem exists_partialDiffeomorph_comp_inv [Nonempty M] (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 1 ⊆ c.source)
    (hrange : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    (g : M → T) (hg : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ g) (hginj : Injective g)
    (hgb : ∀ q, Bijective (mfderiv (𝓡∂ 3) (𝓡 3) g q)) :
    ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) Y.Carrier T ∞,
      Φ.source = (c '' Metric.closedBall 0 1)ᶜ ∧ ∀ q, f q ∈ Φ.source → Φ (f q) = g q := by
  have hYne : Nonempty Y.Carrier := ⟨f (Classical.arbitrary M)⟩
  set S : Set Y.Carrier := (c '' Metric.closedBall 0 1)ᶜ with hS_def
  have hS : IsOpen S :=
    ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1).image_of_continuousOn
      (c.contMDiffOn_toFun.continuousOn.mono hc)).isClosed.isOpen_compl
  let G : Y.Carrier → T := g ∘ Function.invFun f
  have hGf : G ∘ f = g := by
    funext q
    change g (Function.invFun f (f q)) = g q
    rw [Function.leftInverse_invFun hf.isEmbedding.injective q]
  have hSf : ∀ y ∈ S, ∃ q, (𝓡∂ 3).IsInteriorPoint q ∧ f q = y := by
    intro y hy
    have hyr : y ∈ range f := by
      rw [hrange]
      exact fun h => hy (image_mono ball_subset_closedBall h)
    obtain ⟨q, rfl⟩ := hyr
    refine ⟨q, ?_, rfl⟩
    rcases (𝓡∂ 3).isInteriorPoint_or_isBoundaryPoint q with h | h
    · exact h
    · exact absurd (image_mono sphere_subset_closedBall
        (mem_image_sphere_of_isBoundaryPoint c hf hc hrange h)) hy
  have hGat : ∀ q, (𝓡∂ 3).IsInteriorPoint q → ContMDiffAt (𝓡 3) (𝓡 3) ∞ G (f q) := by
    intro q hq
    have hcomp : ContMDiffAt (𝓡∂ 3) (𝓡 3) ∞ (G ∘ f) q := by
      rw [hGf]
      exact hg.contMDiffAt
    exact hf.contMDiffAt_of_comp_of_isInteriorPoint le_rfl (by simp) hq hcomp
  have hGon : ContMDiffOn (𝓡 3) (𝓡 3) ∞ G S := by
    intro y hy
    obtain ⟨q, hq, rfl⟩ := hSf y hy
    exact (hGat q hq).contMDiffWithinAt
  have hloc : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ G S := by
    intro y
    obtain ⟨q, hq, hqy⟩ := hSf y.1 y.2
    have hyS : f q ∈ S := hqy ▸ y.2
    change IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ G y.1
    rw [← hqy]
    have hGd : MDifferentiableAt (𝓡 3) (𝓡 3) G (f q) := (hGat q hq).mdifferentiableAt (by simp)
    have hchain : mfderiv (𝓡∂ 3) (𝓡 3) g q =
        (mfderiv (𝓡 3) (𝓡 3) G (f q)).comp (mfderiv (𝓡∂ 3) (𝓡 3) f q) := by
      rw [← hGf]
      exact mfderiv_comp q hGd (hf.contMDiff.mdifferentiableAt (by simp))
    have hfb := mfderiv_bijective_of_isSmoothEmbedding hf q
    let D : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      mfderiv (𝓡 3) (𝓡 3) G (f q)
    have hD : Injective D := by
      intro v w hvw
      obtain ⟨v', rfl⟩ := hfb.2 v
      obtain ⟨w', rfl⟩ := hfb.2 w
      have h' : mfderiv (𝓡∂ 3) (𝓡 3) g q v' = mfderiv (𝓡∂ 3) (𝓡 3) g q w' := by
        rw [hchain]
        exact hvw
      rw [(hgb q).1 h']
    let A : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      (D.toLinearMap.linearEquivOfInjective hD rfl).toContinuousLinearEquiv
    exact isLocalDiffeomorphAt_of_contMDiffOn_of_hasMFDerivAt_equiv G hGon hS (f q) hyS A
      hGd.hasMFDerivAt
  have hinjOn : InjOn G S := by
    intro y hy y' hy' h
    obtain ⟨q, -, rfl⟩ := hSf y hy
    obtain ⟨q', -, rfl⟩ := hSf y' hy'
    have h' : (G ∘ f) q = (G ∘ f) q' := h
    rw [hGf] at h'
    rw [hginj h']
  obtain ⟨Φ, hsrc, -, hΦ⟩ := exists_partialDiffeomorph_of_injOn hS hloc hinjOn
  refine ⟨Φ, hsrc, fun q _ => ?_⟩
  rw [hΦ]
  exact congrFun hGf q

omit [IsManifold (𝓡∂ 3) ∞ M] [CompactSpace M] [IsManifold (𝓡 3) ∞ T] in
/-- **The shell map** `g ∘ f⁻¹ ∘ c ∘ shellRadial` on `S² × [0, 1]`: smooth, injective, of bijective
differential; its value at `p` is `g q` for the point `q` with `f q = c (shellRadial p)`. -/
theorem exists_shellLift (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    (hrange : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    (g : M → T) (hg : ContMDiff (𝓡∂ 3) (𝓡 3) ∞ g) (hginj : Injective g)
    (hgb : ∀ q, Bijective (mfderiv (𝓡∂ 3) (𝓡 3) g q)) :
    ∃ F₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 → T,
      ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ F₀ ∧ Injective F₀ ∧
      (∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) F₀ p)) ∧
      ∀ p, ∃ q, f q = c (shellRadial p) ∧ F₀ p = g q := by
  have hsrc : ∀ p, shellRadial p ∈ c.source := fun p =>
    hc (mem_closedBall_zero_iff.mpr ((norm_shellRadial_le p).trans (by norm_num)))
  let k : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1 → Y.Carrier :=
    fun p => c (shellRadial p)
  have hk : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ k :=
    c.contMDiffOn_toFun.comp_contMDiff contMDiff_shellRadial hsrc
  have hkinj : Injective k := fun p p' h =>
    shellRadial_injective (c.toOpenPartialHomeomorph.injOn (hsrc p) (hsrc p') h)
  have hkb : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) k p) := by
    intro p
    have hcl := c.isLocalDiffeomorphAt _ _ ∞ (hsrc p)
    have hcomp : k = c ∘ shellRadial := rfl
    rw [hcomp, mfderiv_comp p (hcl.mdifferentiableAt (by simp))
      (contMDiff_shellRadial.mdifferentiableAt (by simp))]
    exact (hcl.mfderivToContinuousLinearEquiv (by simp)).bijective.comp
      (mfderiv_shellRadial_bijective p)
  have hkf : range k ⊆ range f := by
    rintro _ ⟨p, rfl⟩
    rw [hrange]
    rintro ⟨x, hx, hxp⟩
    have hxs : x ∈ c.source := hc (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by norm_num)) hx)
    have hxe : x = shellRadial p := c.toOpenPartialHomeomorph.injOn hxs (hsrc p) hxp
    have h1 := one_le_norm_shellRadial p
    rw [← hxe] at h1
    exact absurd (mem_ball_zero_iff.mp hx) (not_lt.mpr h1)
  let r := hf.lift k hkf
  have hr : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ r := hf.contMDiff_lift hk hkf
  have hfr : ∀ p, f (r p) = k p := hf.comp_lift hkf
  have hrb : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) r p) := by
    intro p
    have hchain : mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) k p =
        (mfderiv (𝓡∂ 3) (𝓡 3) f (r p)).comp (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) r p) := by
      have hfun : k = f ∘ r := funext fun p => (hfr p).symm
      rw [hfun]
      exact mfderiv_comp p (hf.contMDiff.mdifferentiableAt (by simp))
        (hr.mdifferentiableAt (by simp))
    have hfb := mfderiv_bijective_of_isSmoothEmbedding hf (r p)
    constructor
    · intro v w hvw
      apply (hkb p).1
      rw [hchain]
      exact congrArg (mfderiv (𝓡∂ 3) (𝓡 3) f (r p)) hvw
    · intro w
      obtain ⟨v, hv⟩ := (hkb p).2 (mfderiv (𝓡∂ 3) (𝓡 3) f (r p) w)
      refine ⟨v, hfb.1 ?_⟩
      rw [← hv, hchain]
      rfl
  refine ⟨g ∘ r, hg.comp hr, ?_, fun p => ?_, fun p => ⟨r p, hfr p, rfl⟩⟩
  · intro p p' h
    apply hkinj
    rw [← hfr p, ← hfr p', hginj h]
  · rw [mfderiv_comp p (hg.mdifferentiableAt (by simp)) (hr.mdifferentiableAt (by simp))]
    exact (hgb (r p)).comp (hrb p)

end Punctured

end GC.GraphManifold.Assembly
