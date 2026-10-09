import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormPushShell
import DifferentialGeometry.Topology.Manifold.SmoothModelTransportSource

/-!
# FC42 normalization, packet N2a (pieces): shell, pushed piece, seam and height of a punctured `ℝP³`

Lane ASM-NRM4 (design of lane ASM-NRM3, approved by main). For an injective piece `P` with a smooth
embedding `f : P → Y` onto the complement of the open unit ball `c (B¹)` of a chart `c` of a closed
three-manifold `Y` (the data of a punctured-`ℝP³` zero vertex) and a small `η > 0`:

* the transfer `Ψ = P.map ∘ f⁻¹ : Y → W` (`PieceEmbedding.transfer`), a local diffeomorphism off
  `c (B̄¹)` with values in `W.interior`;
* the generic `S² × [0, 1]` piece `sphereIntervalPiece F` of a smooth injective full-rank map `F`
  (the product atlas transported to the half-space model) with its model diffeomorphism;
* the thin shell `shellMap` (`(z, t) ↦ Ψ (c ((1 + η t) z))`), the pushed piece `pushedPiece`
  (`P.map` replaced by `Ψ ∘ chartPush c η ∘ f`, same piece type), the seam `pushSeam` (collar
  `(z, s) ↦ Ψ (c ((1 + η + η s / 4) z))`);
* the height `pushHeight = chartRadius c ∘ f ∘ P⁻¹`, continuous on the image of `P`; the images of
  the shell and of the pushed piece are the parts of height `≤ 1 + η` and `≥ 1 + η`; the model
  boundary of `P` is the bottom sphere of the shell, the model boundary of the pushed piece and the
  seam sphere are its top sphere.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-! ## Chart points -/

section ChartPoints

variable {Y : Type*} [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  {c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) (EuclideanSpace ℝ (Fin 3)) Y ∞}

/-- A chart point of norm `≤ 2` lies in the chart image of a subset of the closed ball of radius `2`
exactly when its parameter does. -/
theorem chart_mem_image_iff (hc : Metric.closedBall 0 2 ⊆ c.source)
    {v : EuclideanSpace ℝ (Fin 3)} (hv : ‖v‖ ≤ 2) {s : Set (EuclideanSpace ℝ (Fin 3))}
    (hs : s ⊆ Metric.closedBall 0 2) : c v ∈ c '' s ↔ v ∈ s := by
  constructor
  · rintro ⟨w, hw, hwv⟩
    rwa [← c.toOpenPartialHomeomorph.injOn (hc (hs hw)) (hc (mem_closedBall_zero_iff.mpr hv)) hwv]
  · intro h
    exact ⟨v, h, rfl⟩

theorem chart_injOn (hc : Metric.closedBall 0 2 ⊆ c.source) {v w : EuclideanSpace ℝ (Fin 3)}
    (hv : ‖v‖ ≤ 2) (hw : ‖w‖ ≤ 2) (h : c v = c w) : v = w :=
  c.toOpenPartialHomeomorph.injOn (hc (mem_closedBall_zero_iff.mpr hv))
    (hc (mem_closedBall_zero_iff.mpr hw)) h

theorem chart_not_mem_ball (hc : Metric.closedBall 0 2 ⊆ c.source)
    {v : EuclideanSpace ℝ (Fin 3)} (hv1 : 1 ≤ ‖v‖) (hv2 : ‖v‖ ≤ 2) :
    c v ∉ c '' Metric.ball 0 1 := by
  rw [chart_mem_image_iff hc hv2 (Metric.ball_subset_closedBall.trans
    (Metric.closedBall_subset_closedBall (by norm_num)))]
  exact fun h => absurd (mem_ball_zero_iff.mp h) (not_lt.mpr hv1)

theorem chart_not_mem_closedBall (hc : Metric.closedBall 0 2 ⊆ c.source)
    {v : EuclideanSpace ℝ (Fin 3)} (hv1 : 1 < ‖v‖) (hv2 : ‖v‖ ≤ 2) :
    c v ∉ c '' Metric.closedBall 0 1 := by
  rw [chart_mem_image_iff hc hv2 (Metric.closedBall_subset_closedBall (by norm_num))]
  exact fun h => absurd (mem_closedBall_zero_iff.mp h) (not_le.mpr hv1)

/-- Off the unit chart ball, the chart radius is at least `1`. -/
theorem one_le_chartRadius (hc : Metric.closedBall 0 2 ⊆ c.source) {y : Y}
    (hy : y ∉ c '' Metric.ball 0 1) : 1 ≤ chartRadius c y := by
  by_contra hlt
  have hlt' : chartRadius c y < 1 := not_le.mp hlt
  obtain ⟨v, hv, rfl, hr⟩ := exists_chart_of_chartRadius_lt hc
    (show chartRadius c y < 3 / 2 by linarith)
  exact hy ⟨v, mem_ball_zero_iff.mpr (by linarith), rfl⟩

/-- Chart radius above `1` keeps a point off the closed unit chart ball. -/
theorem not_mem_closedBall_of_one_lt_chartRadius (hc : Metric.closedBall 0 2 ⊆ c.source) {y : Y}
    (hy : 1 < chartRadius c y) : y ∉ c '' Metric.closedBall 0 1 := by
  rintro ⟨v, hv, rfl⟩
  have hv1 := mem_closedBall_zero_iff.mp hv
  rw [chartRadius_chart hc (by linarith)] at hy
  exact absurd (lt_of_lt_of_le hy (min_le_left _ _)) (not_lt.mpr hv1)

/-- A point of chart radius `< r ≤ 3/2` lies in the chart ball of radius `r`, and conversely. -/
theorem chartRadius_lt_iff (hc : Metric.closedBall 0 2 ⊆ c.source) {y : Y} {r : ℝ}
    (hr : r ≤ 3 / 2) : chartRadius c y < r ↔ y ∈ c '' Metric.ball 0 r := by
  constructor
  · intro h
    obtain ⟨v, hv, rfl, hrv⟩ := exists_chart_of_chartRadius_lt hc
      (show chartRadius c y < 3 / 2 by linarith)
    exact ⟨v, mem_ball_zero_iff.mpr (by linarith), rfl⟩
  · rintro ⟨v, hv, rfl⟩
    have hv' := mem_ball_zero_iff.mp hv
    rw [chartRadius_chart hc (by linarith)]
    exact lt_of_le_of_lt (min_le_left _ _) hv'

end ChartPoints

/-! ## The generic `S² × [0, 1]` piece -/

section SphereIntervalPiece

local instance closureSphereConnected_ASMNRM4 : ConnectedSpace ClosureSphere.{u} :=
  have hS : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by
      rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)
  Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous

local instance sphereIccCharts_ASMNRM4 :
    ChartedSpace (EuclideanHalfSpace 3) (ClosureSphere.{u} × Icc (0 : ℝ) 1) :=
  DifferentialGeometry.Manifold.euclideanHalfSpaceProdChartedSpace _

local instance sphereIccSmooth_ASMNRM4 :
    IsManifold (𝓡∂ 3) ∞ (ClosureSphere.{u} × Icc (0 : ℝ) 1) :=
  DifferentialGeometry.Manifold.euclideanHalfSpaceProd_isManifold _

variable {W : CompactCarrier.{u}} (F : ClosureSphere.{u} × Icc (0 : ℝ) 1 → W.Carrier)
  (hF : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) W.model ∞ F)
  (hFb : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) W.model F p)) (hFi : Injective F)

/-- **The `S² × [0, 1]` piece of a smooth injective full-rank map `F`**: the piece type
`ClosureSphere × [0, 1]` with the product atlas transported to the half-space model. -/
def sphereIntervalPiece : PieceEmbedding W where
  Piece := ClosureSphere.{u} × Icc (0 : ℝ) 1
  map := F
  smooth := hF.comp
    (DifferentialGeometry.Manifold.euclideanHalfSpaceProdDiffeomorph
      (ClosureSphere.{u} × Icc (0 : ℝ) 1)).contMDiff
  mfderiv_bijective q := by
    let d := DifferentialGeometry.Manifold.euclideanHalfSpaceProdDiffeomorph
      (ClosureSphere.{u} × Icc (0 : ℝ) 1)
    change Bijective (mfderiv (𝓡∂ 3) W.model (F ∘ d) q)
    rw [mfderiv_comp q (hF.mdifferentiableAt (by simp)) (d.contMDiff.mdifferentiableAt (by simp))]
    exact (hFb (d q)).comp (d.mfderivToContinuousLinearEquiv (by simp) q).bijective
  injective := hFi

/-- The model diffeomorphism of `sphereIntervalPiece`. -/
def sphereIntervalPieceDiffeo :
    (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯
      (sphereIntervalPiece F hF hFb hFi).Piece :=
  (DifferentialGeometry.Manifold.euclideanHalfSpaceProdDiffeomorph
    (ClosureSphere.{u} × Icc (0 : ℝ) 1)).symm

theorem sphereIntervalPiece_map_diffeo (p : ClosureSphere.{u} × Icc (0 : ℝ) 1) :
    (sphereIntervalPiece F hF hFb hFi).map (sphereIntervalPieceDiffeo F hF hFb hFi p) = F p :=
  rfl

theorem range_sphereIntervalPiece : range (sphereIntervalPiece F hF hFb hFi).map = range F :=
  rfl

theorem sphereLevel_sphereIntervalPiece (t : Icc (0 : ℝ) 1) :
    (sphereIntervalPiece F hF hFb hFi).sphereLevel (sphereIntervalPieceDiffeo F hF hFb hFi) t =
      range fun z => F (z, t) :=
  rfl

end SphereIntervalPiece

/-! ## The transfer `Ψ = P.map ∘ f⁻¹` -/

namespace PieceEmbedding

variable {W : CompactCarrier.{u}} (P : PieceEmbedding W) {Y : ConnectedClosedOrientedManifold.{u} 3}

/-- The transfer `Ψ = P.map ∘ f⁻¹` of a parametrization `f : P.Piece → Y`. -/
def transfer (f : P.Piece → Y.Carrier) (y : Y.Carrier) : W.Carrier :=
  P.map (invFun f y)

variable {P}
variable {c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
    Y.Carrier ∞}
  {f : P.Piece → Y.Carrier}

theorem transfer_apply (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f) (q : P.Piece) :
    P.transfer f (f q) = P.map q := by
  unfold transfer
  rw [leftInverse_invFun hf.isEmbedding.injective q]

theorem transfer_mem_range (y : Y.Carrier) : P.transfer f y ∈ range P.map :=
  ⟨_, rfl⟩

theorem injOn_transfer (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f) :
    InjOn (P.transfer f) (range f) := by
  rintro _ ⟨q, rfl⟩ _ ⟨q', rfl⟩ h
  rw [transfer_apply hf, transfer_apply hf] at h
  rw [P.injective h]

theorem mem_range_of_not_mem
    (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    {y : Y.Carrier} (hy : y ∉ c '' Metric.ball 0 1) : y ∈ range f := by
  rw [hr]
  exact hy

theorem isInteriorPoint_of_not_mem (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    {q : P.Piece} (hq : f q ∉ c '' Metric.closedBall 0 1) : (𝓡∂ 3).IsInteriorPoint q := by
  rcases (𝓡∂ 3).isInteriorPoint_or_isBoundaryPoint q with h | h
  · exact h
  · exact absurd (image_mono Metric.sphere_subset_closedBall
      ((isBoundaryPoint_iff_mem_image_sphere c hf
        ((Metric.closedBall_subset_closedBall (by norm_num)).trans hc) hr).mp h)) hq

/-- Off the closed unit chart ball, the transfer goes to ambient interior points of the image of `P`
inside `W.interior`. -/
theorem transfer_mem_interior (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    {y : Y.Carrier} (hy : y ∉ c '' Metric.closedBall 0 1) :
    P.transfer f y ∈ interior (range P.map) ∩ W.interior := by
  obtain ⟨q, rfl⟩ := mem_range_of_not_mem hr fun h =>
    hy (image_mono Metric.ball_subset_closedBall h)
  have hq := isInteriorPoint_of_not_mem hf hc hr hy
  rw [transfer_apply hf]
  exact ⟨P.toPieceFold.map_mem_interior_range hq, P.isInteriorPoint_map hq⟩

/-- **The transfer is a local diffeomorphism off the closed unit chart ball.** -/
theorem isLocalDiffeomorphAt_transfer (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    {y : Y.Carrier} (hy : y ∉ c '' Metric.closedBall 0 1) :
    IsLocalDiffeomorphAt (𝓡 3) W.model ∞ (P.transfer f) y := by
  have hU : IsOpen (c '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)ᶜ :=
    (isClosed_chart_image_closedBall hc (by norm_num)).isOpen_compl
  have hcomp : P.transfer f ∘ f = P.map := funext (transfer_apply hf)
  have hat : ∀ y ∈ (c '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)ᶜ,
      ∃ q, f q = y ∧ (𝓡∂ 3).IsInteriorPoint q := by
    intro y hy
    obtain ⟨q, rfl⟩ := mem_range_of_not_mem hr fun h =>
      hy (image_mono Metric.ball_subset_closedBall h)
    exact ⟨q, rfl, isInteriorPoint_of_not_mem hf hc hr hy⟩
  have hsm : ContMDiffOn (𝓡 3) W.model ∞ (P.transfer f)
      (c '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)ᶜ := by
    intro y hy
    obtain ⟨q, rfl, hq⟩ := hat y hy
    have h1 : ContMDiffAt (𝓡∂ 3) W.model ∞ (P.transfer f ∘ f) q := by
      rw [hcomp]
      exact P.smooth.contMDiffAt
    exact (hf.contMDiffAt_of_comp_of_isInteriorPoint le_rfl (by simp) hq h1).contMDiffWithinAt
  obtain ⟨q, rfl, hq⟩ := hat y hy
  refine isLocalDiffeomorphAt_of_interior_bijective_on hU hsm hy
    BoundarylessManifold.isInteriorPoint (by rw [transfer_apply hf]; exact P.isInteriorPoint_map hq)
    ?_
  have hd : MDifferentiableAt (𝓡 3) W.model (P.transfer f) (f q) :=
    (hsm.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp)
  have hchain : mfderiv (𝓡∂ 3) W.model P.map q =
      (mfderiv (𝓡 3) W.model (P.transfer f) (f q)).comp (mfderiv (𝓡∂ 3) (𝓡 3) f q) := by
    rw [← hcomp]
    exact mfderiv_comp q hd (hf.contMDiff.mdifferentiableAt (by simp))
  have hfb := mfderiv_bijective_of_isSmoothEmbedding hf q
  have hPb := P.mfderiv_bijective q
  constructor
  · intro v w hvw
    obtain ⟨v', rfl⟩ := hfb.2 v
    obtain ⟨w', rfl⟩ := hfb.2 w
    have h' : mfderiv (𝓡∂ 3) W.model P.map q v' = mfderiv (𝓡∂ 3) W.model P.map q w' := by
      rw [hchain]
      exact hvw
    rw [hPb.1 h']
  · intro w
    obtain ⟨v', hv'⟩ := hPb.2 w
    refine ⟨mfderiv (𝓡∂ 3) (𝓡 3) f q v', ?_⟩
    rw [← hv', hchain]
    rfl

/-! ## The thin shell -/

/-- The shell map `(z, t) ↦ Ψ (c ((1 + η t) z))`. -/
def shellMap (f : P.Piece → Y.Carrier)
    (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      Y.Carrier ∞)
    (η : ℝ) (p : ClosureSphere.{u} × Icc (0 : ℝ) 1) : W.Carrier :=
  P.transfer f (c (pushShellRadial η (p.1.down, p.2)))

/-- The product diffeomorphism `ClosureSphere × [0, 1] ≅ S² × [0, 1]`. -/
def sphereIccDown : (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), (𝓡 2).prod (𝓡∂ 1)⟯
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) :=
  (uliftDiffeomorph (𝓡 2) SphereTwo).symm.prodCongr
    (Diffeomorph.refl (𝓡∂ 1) (Icc (0 : ℝ) 1) ∞)

theorem sphereIccDown_apply (p : ClosureSphere.{u} × Icc (0 : ℝ) 1) :
    sphereIccDown p = (p.1.down, p.2) :=
  rfl

variable (η : ℝ)

theorem norm_shell {η : ℝ} (hη : 0 ≤ η) (p : ClosureSphere.{u} × Icc (0 : ℝ) 1) :
    ‖pushShellRadial η (p.1.down, p.2)‖ = 1 + η * (p.2 : ℝ) :=
  norm_pushShellRadial hη _

theorem one_le_norm_shell {η : ℝ} (hη : 0 ≤ η) (p : ClosureSphere.{u} × Icc (0 : ℝ) 1) :
    1 ≤ ‖pushShellRadial η (p.1.down, p.2)‖ := by
  rw [norm_shell hη]
  nlinarith [p.2.2.1]

theorem norm_shell_le {η : ℝ} (hη : 0 ≤ η) (p : ClosureSphere.{u} × Icc (0 : ℝ) 1) :
    ‖pushShellRadial η (p.1.down, p.2)‖ ≤ 1 + η := by
  rw [norm_shell hη]
  nlinarith [p.2.2.2]

variable {η}

/-- The shell map as a smooth lift through `f`. -/
theorem exists_shellMap_lift (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    (hη : 0 < η) (hη4 : η ≤ 1 / 4) :
    ∃ r : ClosureSphere.{u} × Icc (0 : ℝ) 1 → P.Piece,
      ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ r ∧
      (∀ p, f (r p) = c (pushShellRadial η (p.1.down, p.2))) ∧
      (∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) r p)) ∧
      P.shellMap f c η = P.map ∘ r := by
  have hn2 : ∀ p : ClosureSphere.{u} × Icc (0 : ℝ) 1, ‖pushShellRadial η (p.1.down, p.2)‖ ≤ 2 :=
    fun p => (norm_shell_le hη.le p).trans (by linarith)
  have hsrc : ∀ p : ClosureSphere.{u} × Icc (0 : ℝ) 1,
      pushShellRadial η (p.1.down, p.2) ∈ c.source :=
    fun p => hc (mem_closedBall_zero_iff.mpr (hn2 p))
  let R : ClosureSphere.{u} × Icc (0 : ℝ) 1 → EuclideanSpace ℝ (Fin 3) :=
    pushShellRadial η ∘ sphereIccDown
  have hR : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ R :=
    (contMDiff_pushShellRadial η).comp sphereIccDown.contMDiff
  have hRb : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) R p) := by
    intro p
    rw [mfderiv_comp p ((contMDiff_pushShellRadial η).mdifferentiableAt (by simp))
      (sphereIccDown.contMDiff.mdifferentiableAt (by simp))]
    exact (mfderiv_pushShellRadial_bijective hη _).comp
      (sphereIccDown.mfderivToContinuousLinearEquiv (by simp) p).bijective
  let k : ClosureSphere.{u} × Icc (0 : ℝ) 1 → Y.Carrier := fun p => c (R p)
  have hk : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ k :=
    c.contMDiffOn_toFun.comp_contMDiff hR hsrc
  have hkb : ∀ p, Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) k p) := by
    intro p
    have hcl := c.isLocalDiffeomorphAt _ _ ∞ (hsrc p)
    have hcomp : k = c ∘ R := rfl
    rw [hcomp, mfderiv_comp p (hcl.mdifferentiableAt (by simp)) (hR.mdifferentiableAt (by simp))]
    exact (hcl.mfderivToContinuousLinearEquiv (by simp)).bijective.comp (hRb p)
  have hkf : range k ⊆ range f := by
    rintro _ ⟨p, rfl⟩
    exact mem_range_of_not_mem hr (chart_not_mem_ball hc (one_le_norm_shell hη.le p) (hn2 p))
  let r := hf.lift k hkf
  have hr' : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) ∞ r := hf.contMDiff_lift hk hkf
  have hfr : ∀ p, f (r p) = k p := hf.comp_lift hkf
  refine ⟨r, hr', hfr, fun p => ?_, ?_⟩
  · have hchain : mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) k p =
        (mfderiv (𝓡∂ 3) (𝓡 3) f (r p)).comp (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡∂ 3) r p) := by
      have hfun : k = f ∘ r := funext fun p => (hfr p).symm
      rw [hfun]
      exact mfderiv_comp p (hf.contMDiff.mdifferentiableAt (by simp))
        (hr'.mdifferentiableAt (by simp))
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
  · funext p
    change P.transfer f (k p) = P.map (r p)
    rw [← hfr p, transfer_apply hf]

theorem contMDiff_shellMap (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    (hη : 0 < η) (hη4 : η ≤ 1 / 4) :
    ContMDiff ((𝓡 2).prod (𝓡∂ 1)) W.model ∞ (P.shellMap f c η) := by
  obtain ⟨r, hr', -, -, heq⟩ := P.exists_shellMap_lift hf hc hr hη hη4
  rw [heq]
  exact P.smooth.comp hr'

theorem mfderiv_shellMap_bijective (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    (hη : 0 < η) (hη4 : η ≤ 1 / 4) (p : ClosureSphere.{u} × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) W.model (P.shellMap f c η) p) := by
  obtain ⟨r, hr', -, hrb, heq⟩ := P.exists_shellMap_lift hf hc hr hη hη4
  rw [heq, mfderiv_comp p (P.smooth.mdifferentiableAt (by simp)) (hr'.mdifferentiableAt (by simp))]
  exact (P.mfderiv_bijective _).comp (hrb p)

theorem injective_shellMap (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    (hη : 0 < η) (hη4 : η ≤ 1 / 4) : Injective (P.shellMap f c η) := by
  obtain ⟨r, -, hfr, -, heq⟩ := P.exists_shellMap_lift hf hc hr hη hη4
  intro p p' h
  rw [heq] at h
  have h1 := congrArg f (P.injective h)
  simp only [hfr] at h1
  have hv := chart_injOn hc ((norm_shell_le hη.le p).trans (by linarith))
    ((norm_shell_le hη.le p').trans (by linarith)) h1
  obtain ⟨h3, h4⟩ := Prod.mk.inj (pushShellRadial_injective hη hv)
  exact Prod.ext (ULift.ext h3) h4

/-- **The shell piece** `S² × [0, 1] → W`, `(z, t) ↦ Ψ (c ((1 + η t) z))`. -/
def shellPiece (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    (hη : 0 < η) (hη4 : η ≤ 1 / 4) : PieceEmbedding W :=
  sphereIntervalPiece (P.shellMap f c η) (P.contMDiff_shellMap hf hc hr hη hη4)
    (P.mfderiv_shellMap_bijective hf hc hr hη hη4) (P.injective_shellMap hf hc hr hη hη4)

/-- The model diffeomorphism of the shell piece. -/
def shellPieceDiffeo (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    (hη : 0 < η) (hη4 : η ≤ 1 / 4) :
    (ClosureSphere.{u} × Icc (0 : ℝ) 1) ≃ₘ⟮(𝓡 2).prod (𝓡∂ 1), 𝓡∂ 3⟯
      (P.shellPiece hf hc hr hη hη4).Piece :=
  sphereIntervalPieceDiffeo _ _ _ _

/-! ## The pushed piece -/

/-- The pushed map `q ↦ Ψ (chartPush c η (f q))`. -/
def pushedMap (f : P.Piece → Y.Carrier)
    (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      Y.Carrier ∞)
    (η : ℝ) (q : P.Piece) : W.Carrier :=
  P.transfer f (chartPush c η (f q))

section Pushed

variable {B : ℝ} (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
  (hc : Metric.closedBall 0 2 ⊆ c.source)
  (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
  (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B) (hη : 0 < η) (hηB : η * B ≤ 1 / 4)
  (hη4 : η ≤ 1 / 4)

include hr in
theorem not_mem_closedBall_half (q : P.Piece) : f q ∉ c '' Metric.closedBall 0 (1 / 2) := by
  have hq : f q ∈ range f := ⟨q, rfl⟩
  rw [hr] at hq
  exact fun h => hq (image_mono (Metric.closedBall_subset_ball (by norm_num)) h)

include hc hr hB hη hηB hη4 in
theorem chartPush_not_mem_ball (q : P.Piece) :
    chartPush c η (f q) ∉ c '' Metric.ball 0 (1 + η) := by
  have hq : f q ∈ range f := ⟨q, rfl⟩
  rw [hr] at hq
  exact chartPush_not_mem hc hB hη.le hηB (by linarith) hq

include hc hr hB hη hηB hη4 in
theorem chartPush_not_mem_closedBall (q : P.Piece) :
    chartPush c η (f q) ∉ c '' Metric.closedBall 0 1 := fun h =>
  chartPush_not_mem_ball hc hr hB hη hηB hη4 q
    (image_mono (Metric.closedBall_subset_ball (by linarith)) h)

include hf hc hr hB hη hηB hη4 in
theorem contMDiff_pushedMap : ContMDiff (𝓡∂ 3) W.model ∞ (P.pushedMap f c η) := by
  intro q
  have h1 : ContMDiffAt (𝓡∂ 3) (𝓡 3) ∞ (chartPush c η ∘ f) q :=
    (isLocalDiffeomorphAt_chartPush hc hB hη.le hηB (not_mem_closedBall_half hr q)).contMDiffAt.comp
      q hf.contMDiff.contMDiffAt
  exact (isLocalDiffeomorphAt_transfer hf hc hr
    (chartPush_not_mem_closedBall hc hr hB hη hηB hη4 q)).contMDiffAt.comp q h1

include hf hc hr hB hη hηB hη4 in
theorem mfderiv_pushedMap_bijective (q : P.Piece) :
    Bijective (mfderiv (𝓡∂ 3) W.model (P.pushedMap f c η) q) := by
  have hP := isLocalDiffeomorphAt_chartPush hc hB hη.le hηB (not_mem_closedBall_half hr q)
  have hT := isLocalDiffeomorphAt_transfer hf hc hr
    (chartPush_not_mem_closedBall hc hr hB hη hηB hη4 q)
  have hfd : MDifferentiableAt (𝓡∂ 3) (𝓡 3) f q := hf.contMDiff.mdifferentiableAt (by simp)
  have hPd : MDifferentiableAt (𝓡 3) (𝓡 3) (chartPush c η) (f q) := hP.mdifferentiableAt (by simp)
  have hTd : MDifferentiableAt (𝓡 3) W.model (P.transfer f) (chartPush c η (f q)) :=
    hT.mdifferentiableAt (by simp)
  change Bijective (mfderiv (𝓡∂ 3) W.model (P.transfer f ∘ (chartPush c η ∘ f)) q)
  rw [mfderiv_comp q hTd (hPd.comp q hfd), mfderiv_comp q hPd hfd]
  exact (hT.mfderivToContinuousLinearEquiv (by simp)).bijective.comp
    ((hP.mfderivToContinuousLinearEquiv (by simp)).bijective.comp
      (mfderiv_bijective_of_isSmoothEmbedding hf q))

include hf hc hr hB hη hηB hη4 in
theorem injective_pushedMap : Injective (P.pushedMap f c η) := by
  intro q q' h
  have hm : ∀ q : P.Piece, chartPush c η (f q) ∈ range f := fun q =>
    mem_range_of_not_mem hr fun h' => chartPush_not_mem_ball hc hr hB hη hηB hη4 q
      (image_mono (Metric.ball_subset_ball (by linarith)) h')
  have h1 := injOn_transfer hf (hm q) (hm q') h
  have h2 := injOn_chartPush hc hB hη.le hηB (not_mem_closedBall_half hr q)
    (not_mem_closedBall_half hr q') h1
  exact hf.isEmbedding.injective h2

/-- **The pushed piece**: the same piece type, the map `Ψ ∘ chartPush c η ∘ f`. -/
def pushedPiece : PieceEmbedding W :=
  { P with
    map := P.pushedMap f c η
    smooth := contMDiff_pushedMap hf hc hr hB hη hηB hη4
    mfderiv_bijective := mfderiv_pushedMap_bijective hf hc hr hB hη hηB hη4
    injective := injective_pushedMap hf hc hr hB hη hηB hη4 }

theorem pushedPiece_map : (pushedPiece hf hc hr hB hη hηB hη4).map = P.pushedMap f c η :=
  rfl

end Pushed

/-! ## The seam collar -/

/-- The collar map `(z, s) ↦ Ψ (c ((1 + η + η s / 4) z))`. -/
def collarMap (f : P.Piece → Y.Carrier)
    (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      Y.Carrier ∞)
    (η : ℝ) (p : ClosureSphere.{u} × ℝ) : W.Carrier :=
  P.transfer f (c (pushCollarRadial η (p.1.down, p.2)))

/-- The product diffeomorphism `ClosureSphere × ℝ ≅ S² × ℝ`. -/
def sphereRealDown : (ClosureSphere.{u} × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), (𝓡 2).prod 𝓘(ℝ, ℝ)⟯
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :=
  (uliftDiffeomorph (𝓡 2) SphereTwo).symm.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)

section Collar

variable (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
  (hc : Metric.closedBall 0 2 ⊆ c.source)
  (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
  (hη : 0 < η) (hη4 : η ≤ 1 / 4)

theorem norm_collar {p : ClosureSphere.{u} × ℝ} (hp : p.2 ∈ Ioo (-1 : ℝ) 1) (hη : 0 < η) :
    ‖pushCollarRadial η (p.1.down, p.2)‖ = 1 + η + η / 4 * p.2 :=
  norm_pushCollarRadial _ (by nlinarith [hp.1])

include hη hη4 in
theorem norm_collar_bounds {p : ClosureSphere.{u} × ℝ} (hp : p.2 ∈ Ioo (-1 : ℝ) 1) :
    1 < ‖pushCollarRadial η (p.1.down, p.2)‖ ∧ ‖pushCollarRadial η (p.1.down, p.2)‖ < 2 := by
  rw [norm_collar hp hη]
  constructor <;> nlinarith [hp.1, hp.2]

include hf hc hr hη hη4 in
theorem isLocalDiffeomorphOn_collarMap :
    IsLocalDiffeomorphOn sphereSignedCollarModel W.model ∞ (P.collarMap f c η)
      sphereSignedCollarSource := by
  rintro ⟨p, hp⟩
  have hs : p.2 ∈ Ioo (-1 : ℝ) 1 := hp.2
  obtain ⟨h1, h2⟩ := norm_collar_bounds hη hη4 hs
  have hsrc : pushCollarRadial η (p.1.down, p.2) ∈ c.source :=
    hc (mem_closedBall_zero_iff.mpr h2.le)
  have hD : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ sphereRealDown p :=
    sphereRealDown.isLocalDiffeomorph p
  have hR : IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (pushCollarRadial η)
      (sphereRealDown p) :=
    isLocalDiffeomorphAt_pushCollarRadial hη _ (by
      change 0 < 1 + η + η / 4 * p.2
      nlinarith [hs.1])
  have hC : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ c (pushCollarRadial η (sphereRealDown p)) :=
    c.isLocalDiffeomorphAt _ _ _ hsrc
  have hT : IsLocalDiffeomorphAt (𝓡 3) W.model ∞ (P.transfer f)
      (c (pushCollarRadial η (sphereRealDown p))) :=
    isLocalDiffeomorphAt_transfer hf hc hr (chart_not_mem_closedBall hc h1 h2.le)
  exact ((hD.comp _ _ hR).comp _ _ hC).comp _ _ hT

include hf hc hr hη hη4 in
theorem injOn_collarMap : InjOn (P.collarMap f c η) sphereSignedCollarSource := by
  rintro p hp p' hp' h
  have hs : p.2 ∈ Ioo (-1 : ℝ) 1 := hp.2
  have hs' : p'.2 ∈ Ioo (-1 : ℝ) 1 := hp'.2
  obtain ⟨h1, h2⟩ := norm_collar_bounds hη hη4 hs
  obtain ⟨h1', h2'⟩ := norm_collar_bounds hη hη4 hs'
  have hm : ∀ {v : EuclideanSpace ℝ (Fin 3)}, 1 < ‖v‖ → ‖v‖ < 2 → c v ∈ range f := fun h1 h2 =>
    mem_range_of_not_mem hr (chart_not_mem_ball hc h1.le h2.le)
  have hv := chart_injOn hc h2.le h2'.le (injOn_transfer hf (hm h1 h2) (hm h1' h2') h)
  have hn := congrArg norm hv
  rw [norm_collar hs hη, norm_collar hs' hη] at hn
  have h22 : p.2 = p'.2 := by
    have : η / 4 * p.2 = η / 4 * p'.2 := by linarith
    exact mul_left_cancel₀ (by positivity) this
  have hpos : (1 + η + η / 4 * p.2) ≠ 0 := by nlinarith [hs.1]
  have hz : (p.1.down : EuclideanSpace ℝ (Fin 3)) = p'.1.down := by
    have h' : (1 + η + η / 4 * p.2) • (p.1.down : EuclideanSpace ℝ (Fin 3)) =
        (1 + η + η / 4 * p.2) • (p'.1.down : EuclideanSpace ℝ (Fin 3)) := by
      have h3 : pushCollarRadial η (p.1.down, p.2) = pushCollarRadial η (p'.1.down, p'.2) := hv
      unfold pushCollarRadial at h3
      rw [h3, h22]
    exact smul_right_injective _ hpos h'
  exact Prod.ext (ULift.ext (Subtype.ext hz)) h22

include hf hc hr hη hη4 in
theorem exists_pushCollar :
    ∃ d : PartialDiffeomorph sphereSignedCollarModel W.model (ClosureSphere.{u} × ℝ) W.Carrier ∞,
      d.source = sphereSignedCollarSource ∧
        d.target = P.collarMap f c η '' sphereSignedCollarSource ∧
        (d : ClosureSphere.{u} × ℝ → W.Carrier) = P.collarMap f c η := by
  have : Nonempty (ClosureSphere.{u} × ℝ) :=
    ⟨(ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩, 0)⟩
  exact DifferentialGeometry.Topology.Manifold.exists_partialDiffeomorph_of_injOn
    (isOpen_univ.prod isOpen_Ioo) (isLocalDiffeomorphOn_collarMap hf hc hr hη hη4)
    (injOn_collarMap hf hc hr hη hη4)

include hf hc hr hη hη4 in
theorem collarMap_mem_interior {p : ClosureSphere.{u} × ℝ} (hp : p ∈ sphereSignedCollarSource) :
    P.collarMap f c η p ∈ interior (range P.map) ∩ W.interior := by
  obtain ⟨h1, h2⟩ := norm_collar_bounds hη hη4 (show p.2 ∈ Ioo (-1 : ℝ) 1 from hp.2)
  exact transfer_mem_interior hf hc hr (chart_not_mem_closedBall hc h1 h2.le)

/-- **The seam** of the split: the collar `(z, s) ↦ Ψ (c ((1 + η + η s / 4) z))`. -/
def pushSeam : SphereSeam W where
  collar := (exists_pushCollar hf hc hr hη hη4).choose
  source_eq := (exists_pushCollar hf hc hr hη hη4).choose_spec.1
  target_interior := by
    rw [(exists_pushCollar hf hc hr hη hη4).choose_spec.2.1]
    rintro _ ⟨p, hp, rfl⟩
    exact (collarMap_mem_interior hf hc hr hη hη4 hp).2

theorem pushSeam_collar_apply (p : ClosureSphere.{u} × ℝ) :
    (pushSeam hf hc hr hη hη4).collar p = P.collarMap f c η p :=
  congrFun (exists_pushCollar hf hc hr hη hη4).choose_spec.2.2 p

theorem pushSeam_target :
    (pushSeam hf hc hr hη hη4).collar.target = P.collarMap f c η '' sphereSignedCollarSource :=
  (exists_pushCollar hf hc hr hη hη4).choose_spec.2.1

end Collar

/-! ## The height -/

/-- The height `chartRadius c ∘ f ∘ P⁻¹` on `W`. -/
def pushHeight (f : P.Piece → Y.Carrier)
    (c : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (𝓡 3) (EuclideanSpace ℝ (Fin 3))
      Y.Carrier ∞)
    (x : W.Carrier) : ℝ :=
  chartRadius c (f (invFun P.map x))

theorem pushHeight_map (q : P.Piece) : P.pushHeight f c (P.map q) = chartRadius c (f q) := by
  unfold pushHeight
  rw [leftInverse_invFun P.injective q]

theorem pushHeight_transfer (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f) {y : Y.Carrier}
    (hy : y ∈ range f) : P.pushHeight f c (P.transfer f y) = chartRadius c y := by
  obtain ⟨q, rfl⟩ := hy
  rw [transfer_apply hf, pushHeight_map]

theorem continuousOn_pushHeight (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 2 ⊆ c.source) : ContinuousOn (P.pushHeight f c) (range P.map) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have h : (range P.map).domRestrict (P.pushHeight f c) =
      fun x => chartRadius c (f (P.homeomorphRange.symm x)) := by
    funext x
    have hq : invFun P.map (x : W.Carrier) = P.homeomorphRange.symm x := by
      apply P.injective
      rw [invFun_eq x.2, ← P.homeomorphRange_apply, Homeomorph.apply_symm_apply]
    simp only [domRestrict_apply, pushHeight, hq]
  rw [h]
  exact (continuous_chartRadius hc).comp (hf.contMDiff.continuous.comp
    P.homeomorphRange.symm.continuous)

theorem one_le_pushHeight (hc : Metric.closedBall 0 2 ⊆ c.source)
    (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    {x : W.Carrier} (hx : x ∈ range P.map) : 1 ≤ P.pushHeight f c x := by
  obtain ⟨q, rfl⟩ := hx
  rw [pushHeight_map]
  have hq : f q ∈ range f := ⟨q, rfl⟩
  rw [hr] at hq
  exact one_le_chartRadius hc hq

/-- Points of the image of height above `1` are ambient interior points inside `W.interior`. -/
theorem mem_interior_of_one_lt_pushHeight (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
    (hc : Metric.closedBall 0 2 ⊆ c.source)
    (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
    {x : W.Carrier} (hx : x ∈ range P.map) (h1 : 1 < P.pushHeight f c x) :
    x ∈ interior (range P.map) ∩ W.interior := by
  obtain ⟨q, rfl⟩ := hx
  rw [pushHeight_map] at h1
  rw [← transfer_apply hf]
  exact transfer_mem_interior hf hc hr (not_mem_closedBall_of_one_lt_chartRadius hc h1)

section Heights

variable (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
  (hc : Metric.closedBall 0 2 ⊆ c.source)
  (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
  (hη : 0 < η) (hη4 : η ≤ 1 / 4)

include hf hc hr hη hη4 in
theorem pushHeight_shellMap (p : ClosureSphere.{u} × Icc (0 : ℝ) 1) :
    P.pushHeight f c (P.shellMap f c η p) = 1 + η * (p.2 : ℝ) := by
  have h2 : ‖pushShellRadial η (p.1.down, p.2)‖ < 2 :=
    lt_of_le_of_lt (norm_shell_le hη.le p) (by linarith)
  unfold shellMap
  rw [pushHeight_transfer hf (mem_range_of_not_mem hr
    (chart_not_mem_ball hc (one_le_norm_shell hη.le p) h2.le)), chartRadius_chart hc h2,
    min_eq_left (by linarith [norm_shell_le hη.le p]), norm_shell hη.le]

include hf hc hr hη hη4 in
/-- **The shell is the part of height `≤ 1 + η`.** -/
theorem mem_range_shellMap_iff {x : W.Carrier} :
    x ∈ range (P.shellMap f c η) ↔ x ∈ range P.map ∧ P.pushHeight f c x ≤ 1 + η := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨transfer_mem_range _, ?_⟩
    rw [pushHeight_shellMap hf hc hr hη hη4]
    nlinarith [p.2.2.2]
  · rintro ⟨⟨q, rfl⟩, hle⟩
    rw [pushHeight_map] at hle
    obtain ⟨v, hv, hfv, hrv⟩ := exists_chart_of_chartRadius_lt hc
      (show chartRadius c (f q) < 3 / 2 by linarith)
    have hq : f q ∈ range f := ⟨q, rfl⟩
    rw [hr, ← hfv] at hq
    have hv1 : 1 ≤ ‖v‖ := not_lt.mp fun h => hq ⟨v, mem_ball_zero_iff.mpr h, rfl⟩
    have hvpos : 0 < ‖v‖ := by linarith
    have hvle : ‖v‖ ≤ 1 + η := by rw [← hrv]; exact hle
    let z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      ⟨‖v‖⁻¹ • v, by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']⟩
    let t : Icc (0 : ℝ) 1 := ⟨(‖v‖ - 1) / η, div_nonneg (by linarith) hη.le,
      (div_le_one hη).mpr (by linarith)⟩
    refine ⟨(ULift.up z, t), ?_⟩
    have hpush : pushShellRadial η (z, t) = v := by
      unfold pushShellRadial
      change (1 + η * ((‖v‖ - 1) / η)) • (‖v‖⁻¹ • v) = v
      rw [mul_div_cancel₀ _ hη.ne', smul_smul, show 1 + (‖v‖ - 1) = ‖v‖ by ring,
        mul_inv_cancel₀ hvpos.ne', one_smul]
    change P.transfer f (c (pushShellRadial η (z, t))) = P.map q
    rw [hpush, hfv, transfer_apply hf]

include hf hc hr hη hη4 in
/-- The bottom sphere of the shell is the model boundary image of `P`. -/
theorem image_boundary_eq_shellMap_zero :
    P.map '' (𝓡∂ 3).boundary P.Piece = range fun z => P.shellMap f c η (z, iccZero) := by
  have hc1 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ c.source :=
    (Metric.closedBall_subset_closedBall (by norm_num)).trans hc
  have hbd : ∀ q, (𝓡∂ 3).IsBoundaryPoint q ↔ f q ∈ c '' Metric.sphere 0 1 := fun _ =>
    isBoundaryPoint_iff_mem_image_sphere c hf hc1 hr
  have hz : ∀ z : ClosureSphere.{u}, pushShellRadial η (z.down, iccZero) = z.down := by
    intro z
    unfold pushShellRadial
    change (1 + η * 0) • (z.down : EuclideanSpace ℝ (Fin 3)) = z.down
    rw [mul_zero, add_zero, one_smul]
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨w, hw, hwq⟩ := (hbd q).mp hq
    refine ⟨ULift.up ⟨w, hw⟩, ?_⟩
    change P.transfer f (c (pushShellRadial η (ULift.down (ULift.up ⟨w, hw⟩), iccZero))) = _
    rw [hz, ← transfer_apply hf q, ← hwq]
  · rintro ⟨z, rfl⟩
    have hzn : ‖(z.down : EuclideanSpace ℝ (Fin 3))‖ = 1 := norm_eq_of_mem_sphere z.down
    obtain ⟨q, hq⟩ := mem_range_of_not_mem hr (chart_not_mem_ball hc hzn.ge (by linarith))
    refine ⟨q, (hbd q).mpr ⟨z.down, z.down.2, hq.symm⟩, ?_⟩
    change P.map q = P.transfer f (c (pushShellRadial η (z.down, iccZero)))
    rw [hz, ← hq, transfer_apply hf]

theorem collarMap_eq_shellMap {z : ClosureSphere.{u}} {s : ℝ} (hs1 : -1 < s) (hs0 : s ≤ 0) :
    P.collarMap f c η (z, s) =
      P.shellMap f c η (z, ⟨1 + s / 4, by linarith only [hs1], by linarith only [hs0]⟩) := by
  unfold collarMap shellMap pushCollarRadial pushShellRadial
  congr 3
  change 1 + η + η / 4 * s = 1 + η * (1 + s / 4)
  ring

theorem collarMap_zero (z : ClosureSphere.{u}) :
    P.collarMap f c η (z, 0) = P.shellMap f c η (z, iccOne) := by
  unfold collarMap shellMap pushCollarRadial pushShellRadial
  congr 3
  change 1 + η + η / 4 * 0 = 1 + η * 1
  ring

include hf hc hr hη hη4 in
theorem pushHeight_collarMap {p : ClosureSphere.{u} × ℝ} (hp : p.2 ∈ Ioo (-1 : ℝ) 1) :
    P.pushHeight f c (P.collarMap f c η p) = 1 + η + η / 4 * p.2 := by
  obtain ⟨h1, h2⟩ := norm_collar_bounds hη hη4 hp
  unfold collarMap
  rw [pushHeight_transfer hf (mem_range_of_not_mem hr (chart_not_mem_ball hc h1.le h2.le)),
    chartRadius_chart hc h2, norm_collar hp hη, min_eq_left (by nlinarith [hp.2])]

end Heights

section PushedHeights

variable {B : ℝ} (hf : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞ f)
  (hc : Metric.closedBall 0 2 ⊆ c.source)
  (hr : range f = {x | x ∉ c '' Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1})
  (hB : ∀ x, |deriv Real.smoothTransition x| ≤ B) (hη : 0 < η) (hηB : η * B ≤ 1 / 4)
  (hη4 : η ≤ 1 / 4)

include hf hc hr hB hη hηB hη4 in
/-- **The pushed piece is the part of height `≥ 1 + η`.** -/
theorem mem_range_pushedMap_iff {x : W.Carrier} :
    x ∈ range (P.pushedMap f c η) ↔ x ∈ range P.map ∧ 1 + η ≤ P.pushHeight f c x := by
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨transfer_mem_range _, ?_⟩
    have hn := chartPush_not_mem_ball hc hr hB hη hηB hη4 q
    have hm : chartPush c η (f q) ∈ range f := mem_range_of_not_mem hr fun h' =>
      hn (image_mono (Metric.ball_subset_ball (by linarith)) h')
    unfold pushedMap
    rw [pushHeight_transfer hf hm]
    exact not_lt.mp fun h => hn ((chartRadius_lt_iff hc (by linarith)).mp h)
  · rintro ⟨⟨q, rfl⟩, hle⟩
    rw [pushHeight_map] at hle
    have hn : f q ∉ c '' Metric.ball 0 (1 + η) := fun h =>
      absurd ((chartRadius_lt_iff hc (by linarith)).mpr h) (not_lt.mpr hle)
    obtain ⟨y', hy', hpy⟩ := exists_chartPush_eq hc hη.le hn
    obtain ⟨q', rfl⟩ := mem_range_of_not_mem hr hy'
    refine ⟨q', ?_⟩
    unfold pushedMap
    rw [hpy, transfer_apply hf]

include hf hc hr in
/-- The model boundary image of the pushed piece is the top sphere of the shell. -/
theorem image_boundary_pushedMap :
    P.pushedMap f c η '' (𝓡∂ 3).boundary P.Piece =
      range fun z => P.shellMap f c η (z, iccOne) := by
  have hc1 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ⊆ c.source :=
    (Metric.closedBall_subset_closedBall (by norm_num)).trans hc
  have hbd : ∀ q, (𝓡∂ 3).IsBoundaryPoint q ↔ f q ∈ c '' Metric.sphere 0 1 := fun _ =>
    isBoundaryPoint_iff_mem_image_sphere c hf hc1 hr
  have hz : ∀ w : EuclideanSpace ℝ (Fin 3), ‖w‖ = 1 →
      chartPush c η (c w) = c ((1 + η) • w) := by
    intro w hw
    rw [chartPush_chart hc η (by linarith), radialPush_of_norm_eq_one η hw]
  have hs1 : ∀ z : ClosureSphere.{u}, pushShellRadial η (z.down, iccOne) =
      (1 + η) • (z.down : EuclideanSpace ℝ (Fin 3)) := by
    intro z
    unfold pushShellRadial
    change (1 + η * 1) • (z.down : EuclideanSpace ℝ (Fin 3)) = _
    rw [mul_one]
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨w, hw, hwq⟩ := (hbd q).mp hq
    refine ⟨ULift.up ⟨w, hw⟩, ?_⟩
    change P.transfer f (c (pushShellRadial η (ULift.down (ULift.up ⟨w, hw⟩), iccOne))) =
      P.transfer f (chartPush c η (f q))
    rw [hs1, ← hwq, hz w (norm_eq_of_mem_sphere ⟨w, hw⟩)]
  · rintro ⟨z, rfl⟩
    have hzn : ‖(z.down : EuclideanSpace ℝ (Fin 3))‖ = 1 := norm_eq_of_mem_sphere z.down
    obtain ⟨q, hq⟩ := mem_range_of_not_mem hr (chart_not_mem_ball hc hzn.ge (by linarith))
    refine ⟨q, (hbd q).mpr ⟨z.down, z.down.2, hq.symm⟩, ?_⟩
    change P.transfer f (chartPush c η (f q)) =
      P.transfer f (c (pushShellRadial η (z.down, iccOne)))
    rw [hs1, ← hz _ hzn, hq]

end PushedHeights

end PieceEmbedding

end GC.GraphManifold.Assembly
