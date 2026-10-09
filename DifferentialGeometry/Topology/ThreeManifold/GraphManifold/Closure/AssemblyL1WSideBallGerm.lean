import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1WSideBallSign
import DifferentialGeometry.Topology.Embedding.Extension
import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.Manifold.ClosedCellOrientation
import DifferentialGeometry.Topology.Manifold.InverseFunction
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph

/-!
# Chapter-14 assembly, item L1, group G3b: the neck read in a ball, as a germ of `ℝ³`

For a ball `B : PieceEmbedding W` with model `e : B.Piece ≃ ClosedCell 3` and a neck `N` whose ball
side is `{τ ≤ 0}` (`hside`), the composite `N⁻¹ ∘ Bc` (`Bc = B ∘ e⁻¹ = ballCell B e`, defined on the
cell points sent into the neck) extends across the unit sphere to a partial diffeomorphism `φ` of
`ℝ³` onto an open subset of the neck space (`exists_ballGerm`). Over a neighbourhood `Ω` of any
compact `C` of the ball side of the neck: the inverse `φ⁻¹` sends the ball side to the closed cell
point `y` with `Bc y = N q`, the end disk `{τ = 0}` to the unit sphere, and its derivative is
`dι_y ∘ de ∘ (dB)⁻¹ ∘ dN_q` — the map whose determinant (with `neckSpaceEquiv`) is `ballNeckDetAmb`.

Route: a smooth cutoff times `N⁻¹ ∘ Bc` is smooth on `ClosedCell 3` and extends to `ℝ³` (the tree's
half-space extension through the closed-cell inclusion,
`IsSmoothEmbedding.exists_contDiff_extension_halfspace_of_isClosed_image`); the extension has
bijective differential on the compact set `val '' K` (chain rule through the inclusion) and is
injective there, hence restricts to a partial diffeomorphism
(`IsLocalDiffeomorphOn.exists_partialDiffeomorph_of_isCompact`). No interior hypothesis on the ball
is needed.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1bG : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance ballSmooth_ASML1bG : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 2

/-- The inclusion of the closed 3-cell is a smooth embedding (with the local chart instance). -/
theorem isSmoothEmbedding_cellVal : IsSmoothEmbedding (𝓡∂ 3) (𝓡 3) ∞
    (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) := by
  let _ : ChartedSpace (EuclideanHalfSpace (2 + 1)) (ClosedCell (2 + 1)) :=
    DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2
  exact DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 2

theorem bijective_mfderiv_cellVal (y : ClosedCell 3) :
    Bijective (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) y) :=
  DifferentialGeometry.Topology.Manifold.bijective_mfderiv_of_isImmersionAt (𝓡∂ 3) (𝓡 3) _ y
    (isSmoothEmbedding_cellVal.isImmersion.isImmersionAt y) rfl

/-- If `A ∘ V = P` with `V` and `P` bijective, then `A` is bijective. -/
theorem bijective_of_comp_eq {E F G' : Type*} [AddCommGroup E] [AddCommGroup F] [AddCommGroup G']
    [Module ℝ E] [Module ℝ F] [Module ℝ G'] (A : F →ₗ[ℝ] G') (V : E →ₗ[ℝ] F) (P : E →ₗ[ℝ] G')
    (h : A ∘ₗ V = P) (hV : Bijective V) (hP : Bijective P) : Bijective A := by
  refine ⟨fun x x' hxx' => ?_, fun z => ?_⟩
  · obtain ⟨u, rfl⟩ := hV.2 x
    obtain ⟨u', rfl⟩ := hV.2 x'
    have h1 : P u = P u' := by
      rw [← h]
      exact hxx'
    rw [hP.1 h1]
  · obtain ⟨u, rfl⟩ := hP.2 z
    exact ⟨V u, by rw [← h]; rfl⟩

variable {W : CompactCarrier.{u}} (B : PieceEmbedding W) (e : B.Piece ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ClosedCell 3)

/-- The ball read in the closed cell, `B ∘ e⁻¹`. -/
def ballCell (x : ClosedCell 3) : W.Carrier :=
  B.map (e.symm x)

theorem contMDiff_ballCell : ContMDiff (𝓡∂ 3) W.model ∞ (ballCell B e) :=
  B.smooth.comp e.symm.contMDiff

theorem injective_ballCell : Injective (ballCell B e) :=
  B.injective.comp e.symm.injective

theorem range_ballCell : range (ballCell B e) = range B.map := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨p, rfl⟩
    exact ⟨e p, by simp [ballCell]⟩

theorem mfderiv_ballCell (x : ClosedCell 3) :
    mfderiv (𝓡∂ 3) W.model (ballCell B e) x =
      (mfderiv (𝓡∂ 3) W.model B.map (e.symm x)).comp (mfderiv (𝓡∂ 3) (𝓡∂ 3) e.symm x) :=
  mfderiv_comp x (B.mdifferentiable_map (e.symm x))
    (e.symm.contMDiff.mdifferentiable (by simp) x)

theorem bijective_mfderiv_ballCell (x : ClosedCell 3) :
    Bijective (mfderiv (𝓡∂ 3) W.model (ballCell B e) x) := by
  rw [mfderiv_ballCell]
  exact (B.mfderiv_bijective (e.symm x)).comp
    (e.symm.isInvertible_mfderiv (by simp) (x := x)).bijective

theorem isClosedEmbedding_ballCell : Topology.IsClosedEmbedding (ballCell B e) :=
  (contMDiff_ballCell B e).continuous.isClosedEmbedding (injective_ballCell B e)

/-- The derivative of `e⁻¹` followed by that of `e` is the identity. -/
theorem mfderiv_e_comp_mfderiv_symm (x : ClosedCell 3) :
    (mfderiv (𝓡∂ 3) (𝓡∂ 3) e (e.symm x)).comp (mfderiv (𝓡∂ 3) (𝓡∂ 3) e.symm x) =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡∂ 3) x) := by
  have h : e ∘ e.symm = id := funext fun y => e.apply_symm_apply y
  have hc := mfderiv_comp x (e.contMDiff.mdifferentiable (by simp) (e.symm x))
    (e.symm.contMDiff.mdifferentiable (by simp) x)
  rw [h, mfderiv_id] at hc
  rw [hc.symm]

section Germ

variable (N : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
  (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞)

/-- A cell point sent into the neck target comes from the ball side of the neck. -/
theorem neckSymm_ballCell_snd_nonpos
    (hside : ∀ {q}, q ∈ N.source → (N q ∈ range B.map ↔ q.2 ≤ 0)) {y : ClosedCell 3}
    (hy : ballCell B e y ∈ N.target) : (N.symm (ballCell B e y)).2 ≤ 0 := by
  apply (hside (N.map_target hy)).mp
  rw [N.right_inv hy, ← range_ballCell B e]
  exact ⟨y, rfl⟩

theorem contMDiffOn_neckSymm_ballCell :
    ContMDiffOn (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
      (fun y => N.symm (ballCell B e y)) (ballCell B e ⁻¹' N.target) :=
  N.symm.contMDiffOn_toFun.comp (contMDiff_ballCell B e).contMDiffOn (fun _ hy => hy)

/-- Smoothness of `ψ ∘ ι • (N⁻¹ ∘ Bc)` on the whole cell, when `tsupport`-type control holds. -/
theorem contMDiff_cutoff_neckSymm_ballCell {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) {U₂ : Set (EuclideanSpace ℝ (Fin 3))}
    (hU₂ : ∀ y : ClosedCell 3, (y : EuclideanSpace ℝ (Fin 3)) ∈ U₂ → ballCell B e y ∈ N.target)
    (hzero : ∀ w ∉ U₂, ∀ᶠ w' in 𝓝 w, ψ w' = 0) (hU₂o : IsOpen U₂) :
    ContMDiff (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
      (fun y : ClosedCell 3 => ψ y.val • N.symm (ballCell B e y)) := by
  have hval : ContMDiff (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) :=
    isSmoothEmbedding_cellVal.contMDiff
  intro y
  by_cases hy : (y : EuclideanSpace ℝ (Fin 3)) ∈ U₂
  · have hopen : IsOpen (Subtype.val ⁻¹' U₂ : Set (ClosedCell 3)) :=
      hU₂o.preimage continuous_subtype_val
    have h1 : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ (fun y : ClosedCell 3 => ψ y.val) y :=
      (hψ.contMDiff.comp hval) y
    have h2 : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
        (fun y => N.symm (ballCell B e y)) y :=
      ((contMDiffOn_neckSymm_ballCell B e N).mono (fun y' hy' => hU₂ y' hy')).contMDiffAt
        (hopen.mem_nhds hy)
    exact h1.smul h2
  · have hev : ∀ᶠ y' : ClosedCell 3 in 𝓝 y, ψ y'.val = 0 :=
      continuous_subtype_val.continuousAt.eventually (hzero _ hy)
    apply (contMDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin 2) × ℝ))).congr_of_eventuallyEq
    filter_upwards [hev] with y' hy'
    rw [hy', zero_smul]

/-- **The neck read in the ball is a germ of `ℝ³`.** -/
theorem exists_ballGerm
    (hside : ∀ {q}, q ∈ N.source → (N q ∈ range B.map ↔ q.2 ≤ 0))
    {C : Set (EuclideanSpace ℝ (Fin 2) × ℝ)} (hC : IsCompact C) (hCne : C.Nonempty)
    (hCs : C ⊆ N.source) (hC0 : ∀ q ∈ C, q.2 ≤ 0) :
    ∃ φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
        (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 2) × ℝ) ∞,
    ∃ Ω : Set (EuclideanSpace ℝ (Fin 2) × ℝ), IsOpen Ω ∧ C ⊆ Ω ∧ Ω ⊆ φ.target ∧ Ω ⊆ N.source ∧
      (∀ q ∈ Ω, q.2 ≤ 0 → ∃ y : ClosedCell 3, φ.symm q = y.val ∧ ballCell B e y = N q) ∧
      (∀ q ∈ Ω, q.2 = 0 → ‖φ.symm q‖ = 1) ∧
      (∀ q ∈ Ω, ∀ y : ClosedCell 3, φ.symm q = y.val → ballCell B e y = N q →
        (fderiv ℝ φ y.val).comp (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) y) =
        (mfderiv W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) N.symm (N q)).comp
          (mfderiv (𝓡∂ 3) W.model (ballCell B e) y)) := by
  classical
  set Bc := ballCell B e with hBc
  -- the compact set of cell points over `C`
  have hNC : IsCompact (N '' C) := hC.image_of_continuousOn (N.contMDiffOn_toFun.continuousOn.mono hCs)
  let K : Set (ClosedCell 3) := Bc ⁻¹' (N '' C)
  have hK : IsCompact K :=
    (hNC.isClosed.preimage (contMDiff_ballCell B e).continuous).isCompact
  have hKA : ∀ y ∈ K, Bc y ∈ N.target := by
    rintro y ⟨q, hq, hqy⟩
    rw [← hqy]
    exact N.map_source (hCs hq)
  -- the open set `A = Bc⁻¹ N.target` is cut out by an open `U₂ ⊆ ℝ³`
  obtain ⟨U₂, hU₂o, hU₂⟩ := isOpen_induced_iff.mp
    (N.open_target.preimage (contMDiff_ballCell B e).continuous)
  have hU₂A : ∀ y : ClosedCell 3, (y : EuclideanSpace ℝ (Fin 3)) ∈ U₂ → Bc y ∈ N.target := by
    intro y hy
    have : y ∈ Subtype.val ⁻¹' U₂ := hy
    rw [hU₂] at this
    exact this
  let S : Set (EuclideanSpace ℝ (Fin 3)) := Subtype.val '' K
  have hS : IsCompact S := hK.image continuous_subtype_val
  have hSU₂ : S ⊆ U₂ := by
    rintro _ ⟨y, hy, rfl⟩
    have : y ∈ Bc ⁻¹' N.target := hKA y hy
    rw [← hU₂] at this
    exact this
  obtain ⟨δ, hδ, hδU⟩ := hS.exists_cthickening_subset_open hU₂o hSU₂
  -- the cutoff `ψ`: `1` on `cthickening (δ/2) S`, support `thickening δ S`
  obtain ⟨ψ, hψ, -, hψsupp, hψone⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
    (isOpen_thickening (δ := δ) (E := S)) (isClosed_cthickening (δ := δ / 2) (E := S))
    (cthickening_subset_thickening' hδ (by linarith) S)
  have hzero : ∀ w ∉ U₂, ∀ᶠ w' in 𝓝 w, ψ w' = 0 := by
    intro w hw
    have hw' : w ∉ cthickening δ S := fun h => hw (hδU h)
    filter_upwards [isClosed_cthickening.isOpen_compl.mem_nhds hw'] with w' hw'
    rw [← notMem_support, hψsupp]
    exact fun h => hw' (thickening_subset_cthickening δ S h)
  have hg := contMDiff_cutoff_neckSymm_ballCell B e N hψ hU₂A hzero hU₂o
  -- extension across the sphere
  have hclosed : IsClosed ((Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) '' univ) := by
    rw [image_univ, Subtype.range_coe_subtype]
    exact isClosed_le continuous_norm continuous_const
  let _ : ChartedSpace (EuclideanHalfSpace (2 + 1)) (ClosedCell 3) :=
    DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2
  obtain ⟨G, hG, hGg⟩ :=
    isSmoothEmbedding_cellVal.exists_contDiff_extension_halfspace_of_isClosed_image (d := 2) hg
      hclosed
  let U : Set (EuclideanSpace ℝ (Fin 3)) := thickening (δ / 2) S
  have hUo : IsOpen U := isOpen_thickening
  have hSU : S ⊆ U := self_subset_thickening (by linarith) S
  have hGP : ∀ y : ClosedCell 3, (y : EuclideanSpace ℝ (Fin 3)) ∈ U →
      Bc y ∈ N.target ∧ G y = N.symm (Bc y) := by
    intro y hy
    have hy2 : (y : EuclideanSpace ℝ (Fin 3)) ∈ U₂ :=
      hδU (thickening_subset_cthickening _ _ (thickening_mono (by linarith) S hy))
    refine ⟨hU₂A y hy2, ?_⟩
    have h1 : ψ y = 1 := (hψone y).mp (thickening_subset_cthickening _ _ hy)
    have h2 := hGg (mem_univ y)
    simp only [Function.comp_apply, h1, one_smul] at h2
    exact h2
  have hval : ContMDiff (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞
      (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) := isSmoothEmbedding_cellVal.contMDiff
  -- the derivative relation at cell points of `U`
  have hderiv : ∀ y : ClosedCell 3, (y : EuclideanSpace ℝ (Fin 3)) ∈ U →
      (fderiv ℝ G y.val).comp (mfderiv (𝓡∂ 3) (𝓡 3)
        (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) y) =
      (mfderiv W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) N.symm (Bc y)).comp
        (mfderiv (𝓡∂ 3) W.model Bc y) := by
    intro y hy
    have hopen : IsOpen (Subtype.val ⁻¹' U : Set (ClosedCell 3)) :=
      hUo.preimage continuous_subtype_val
    have heq : (G ∘ Subtype.val) =ᶠ[𝓝 y] (fun y' => N.symm (Bc y')) := by
      filter_upwards [hopen.mem_nhds hy] with y' hy'
      exact (hGP y' hy').2
    have hPd : HasMFDerivAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ)
        (fun y' => N.symm (Bc y')) y
        ((mfderiv W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) N.symm (Bc y)).comp
          (mfderiv (𝓡∂ 3) W.model Bc y)) :=
      (N.symm.mdifferentiableAt (by simp) (hGP y hy).1).hasMFDerivAt.comp y
        ((contMDiff_ballCell B e).mdifferentiable (by simp) y).hasMFDerivAt
    have hGd : HasMFDerivAt (𝓡∂ 3) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) (G ∘ Subtype.val) y
        ((fderiv ℝ G y.val).comp (mfderiv (𝓡∂ 3) (𝓡 3)
          (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) y)) :=
      ((hG.differentiable (by simp) y.val).hasFDerivAt.hasMFDerivAt).comp y
        (hval.mdifferentiable (by simp) y).hasMFDerivAt
    exact (hGd.congr_of_eventuallyEq heq.symm).mfderiv.symm.trans hPd.mfderiv
  have hbij : ∀ y : ClosedCell 3, (y : EuclideanSpace ℝ (Fin 3)) ∈ U →
      Bijective (fderiv ℝ G y.val) := by
    intro y hy
    have hP : Bijective ((mfderiv W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) N.symm (Bc y)).comp
        (mfderiv (𝓡∂ 3) W.model Bc y)) :=
      ((N.symm.isLocalDiffeomorphAt W.model 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞
        (hGP y hy).1).isInvertible_mfderiv (by simp)).bijective.comp
        (bijective_mfderiv_ballCell B e y)
    exact bijective_of_comp_eq (fderiv ℝ G y.val).toLinearMap
      (mfderiv (𝓡∂ 3) (𝓡 3) (Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) y).toLinearMap
      _ (congrArg ContinuousLinearMap.toLinearMap (hderiv y hy)) (bijective_mfderiv_cellVal y) hP
  -- the extension is a local diffeomorphism on `S` and injective there
  have hloc : IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) ∞ G S := by
    rintro ⟨w, y, hyK, rfl⟩
    have hy : (y : EuclideanSpace ℝ (Fin 3)) ∈ U := hSU ⟨y, hyK, rfl⟩
    let A := ContinuousLinearEquiv.ofBijective (fderiv ℝ G y.val)
      (LinearMap.ker_eq_bot.mpr (hbij y hy).1) (LinearMap.range_eq_top.mpr (hbij y hy).2)
    exact DifferentialGeometry.Topology.Manifold.isLocalDiffeomorphAt_of_hasMFDerivAt_equiv G
      hG.contMDiff y.val A ((hG.differentiable (by simp) y.val).hasFDerivAt.hasMFDerivAt)
  have hinj : InjOn G S := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ h
    rw [(hGP y (hSU ⟨y, hy, rfl⟩)).2, (hGP y' (hSU ⟨y', hy', rfl⟩)).2] at h
    have hb : Bc y = Bc y' := N.toPartialEquiv.symm.injOn (hKA y hy) (hKA y' hy') h
    exact congrArg Subtype.val (injective_ballCell B e hb)
  have hpre : ∀ q ∈ N.source, q.2 ≤ 0 → ∃ y : ClosedCell 3, Bc y = N q := by
    intro q hq hq0
    have h := (hside hq).mpr hq0
    rw [← range_ballCell B e] at h
    exact h
  have hSne : S.Nonempty := by
    obtain ⟨q, hq⟩ := hCne
    obtain ⟨y, hy⟩ := hpre q (hCs hq) (hC0 q hq)
    exact ⟨y.val, y, ⟨q, hq, hy.symm⟩, rfl⟩
  obtain ⟨φ, hφs, hφG⟩ := hloc.exists_partialDiffeomorph_of_isCompact hS hSne hinj
  have hφ : ∀ w, φ w = G w := fun w => congrFun hφG w
  -- the good set of cell points and its complement
  let Bad : Set (ClosedCell 3) := {y | (y : EuclideanSpace ℝ (Fin 3)) ∉ φ.source ∩ U}
  have hBad : IsClosed Bad :=
    ((φ.open_source.inter hUo).preimage continuous_subtype_val).isClosed_compl
  have hF : IsClosed (Bc '' Bad) :=
    (hBad.isCompact.image (contMDiff_ballCell B e).continuous).isClosed
  let Ω : Set (EuclideanSpace ℝ (Fin 2) × ℝ) := φ.target ∩ (N.source ∩ N ⁻¹' (Bc '' Bad)ᶜ)
  have hΩ : IsOpen Ω :=
    φ.open_target.inter (N.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage N.open_source
      hF.isOpen_compl)
  -- the key property: on the ball side of `Ω`, `φ⁻¹` is the cell point over `N q`
  have hkey : ∀ q ∈ N.source, N q ∉ Bc '' Bad → ∀ y : ClosedCell 3, Bc y = N q →
      (y : EuclideanSpace ℝ (Fin 3)) ∈ φ.source ∩ U ∧ φ y.val = q := by
    intro q hq hqF y hy
    have hyB : y ∉ Bad := fun h => hqF ⟨y, h, hy⟩
    have hyg : (y : EuclideanSpace ℝ (Fin 3)) ∈ φ.source ∩ U := not_not.mp hyB
    refine ⟨hyg, ?_⟩
    rw [hφ, (hGP y hyg.2).2, hy]
    exact N.left_inv hq
  refine ⟨φ, Ω, hΩ, ?_, inter_subset_left, fun q hq => hq.2.1, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨y, hy⟩ := hpre q (hCs hq) (hC0 q hq)
    have hyS : (y : EuclideanSpace ℝ (Fin 3)) ∈ S := ⟨y, ⟨q, hq, hy.symm⟩, rfl⟩
    have hqF : N q ∉ Bc '' Bad := by
      rintro ⟨y', hy', hy'q⟩
      have hyy : y' = y := injective_ballCell B e (hy'q.trans hy.symm)
      rw [hyy] at hy'
      exact hy' ⟨hφs hyS, hSU hyS⟩
    refine ⟨?_, hCs hq, hqF⟩
    have h := (hkey q (hCs hq) hqF y hy).2
    rw [← h]
    exact φ.map_source (hφs hyS)
  · intro q hq hq0
    obtain ⟨y, hy⟩ := hpre q hq.2.1 hq0
    obtain ⟨hyg, hφy⟩ := hkey q hq.2.1 hq.2.2 y hy
    refine ⟨y, ?_, hy⟩
    rw [← hφy]
    exact φ.left_inv hyg.1
  · intro q hq hq0
    obtain ⟨y, hy⟩ := hpre q hq.2.1 hq0.le
    obtain ⟨hyg, hφy⟩ := hkey q hq.2.1 hq.2.2 y hy
    have hsy : φ.symm q = y.val := by
      rw [← hφy]
      exact φ.left_inv hyg.1
    rw [hsy]
    by_contra hne
    have hlt : ‖(y : EuclideanSpace ℝ (Fin 3))‖ < 1 := lt_of_le_of_ne y.2 hne
    let O : Set (EuclideanSpace ℝ (Fin 3)) := φ.source ∩ (U ∩ ball 0 1)
    have hO : IsOpen O := φ.open_source.inter (hUo.inter isOpen_ball)
    have hyO : (y : EuclideanSpace ℝ (Fin 3)) ∈ O := ⟨hyg.1, hyg.2, mem_ball_zero_iff.mpr hlt⟩
    have himO : IsOpen (φ '' O) :=
      φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hO inter_subset_left
    have hqO : q ∈ φ '' O := ⟨y.val, hyO, hφy⟩
    obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp himO q hqO
    have hq' : (q.1, r / 2) ∈ ball q r := by
      rw [mem_ball, Prod.dist_eq]
      simp only [dist_self, Real.dist_eq, hq0, sub_zero]
      rw [abs_of_pos (by linarith : (0 : ℝ) < r / 2)]
      exact max_lt hr (by linarith)
    obtain ⟨w, ⟨hws, hwU, hwb⟩, hwq⟩ := hrO hq'
    let y'' : ClosedCell 3 := ⟨w, (mem_ball_zero_iff.mp hwb).le⟩
    have h1 := hGP y'' hwU
    have h2 := neckSymm_ballCell_snd_nonpos B e N hside h1.1
    rw [← h1.2, ← hφ] at h2
    change (φ w).2 ≤ 0 at h2
    rw [hwq] at h2
    change r / 2 ≤ 0 at h2
    linarith
  · intro q hq y hy hBy
    obtain ⟨hyg, -⟩ := hkey q hq.2.1 hq.2.2 y hBy
    have hfd : fderiv ℝ φ y.val = fderiv ℝ G y.val := by
      congr 1
    rw [hfd, hderiv y hyg.2, hBy]

end Germ

end GC.GraphManifold.Assembly
