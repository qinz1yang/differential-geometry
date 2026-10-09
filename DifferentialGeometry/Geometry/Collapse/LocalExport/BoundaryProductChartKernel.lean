import DifferentialGeometry.Geometry.Fibration.ActualStageChainGaf07Trivial
import DifferentialGeometry.Topology.Embedding.Lift
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorphImmersion
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingComposition
import DifferentialGeometry.Topology.Manifold.ImmersionCriterionInteriorTarget
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryBaseChartKernel

/-!
# G17 kernel (b): a smooth product chart from a proper submersion and ONE standard fibre
(S-BAUG-D2)

`exists_productChart_of_proper_submersion_BAUGD` (generic, chain-free): `N` a smooth
boundaryless manifold (the interior `W°`), `g : N → ℝᵏ` smooth, `R ⊆ N` open with
`g : R → ball b₀ ε` a proper surjective submersion, and a smooth embedding `ψ : F → N` of the
standard fibre model onto the whole fibre `R ∩ g⁻¹{b₀}`. Then for some `0 < ε'` there is a smooth
embedding `Φ : ℝᵏ × F → N` onto `R ∩ g⁻¹(ball b₀ ε')` with `g (Φ (x, z)) = univBall b₀ ε' x`:
Ehresmann's local triviality (`ehresmann_local_triviality`, the regular fibre over `b₀`), the
identification of `F` with that fibre through the smooth embedding `ψ`, a smooth parametrization
of a small ball by `ℝᵏ` (`univBall`), and the swap `F × Q ≃ Q × F`. Closed twin:
`local_trivial_of_proper_submersion_GAFD` (GAF07 Trivial), which stops at the fibre
diffeomorphism `fibre × Q ≃ f⁻¹Q` and never produces the product chart over `ℝᵏ`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Topology Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold

section ProductChart

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {HN : Type} [TopologicalSpace HN] {I : ModelWithCorners ℝ E HN} [I.Boundaryless]
  {N : Type} [TopologicalSpace N] [ChartedSpace HN N] [IsManifold I ∞ N] [T2Space N]
  [LocallyCompactSpace N] [SecondCountableTopology N]

/-- **A smooth product chart from a proper submersion onto a ball and one standard fibre**
(see the module docstring). -/
theorem exists_productChart_of_proper_submersion_BAUGD {k : ℕ} (hk : 0 < k)
    (hdim : k < Module.finrank ℝ E)
    {EF : Type} [NormedAddCommGroup EF] [NormedSpace ℝ EF] [FiniteDimensional ℝ EF]
    {HF : Type} [TopologicalSpace HF] (IF : ModelWithCorners ℝ EF HF) [IF.Boundaryless]
    {F : Type} [TopologicalSpace F] [ChartedSpace HF F] [IsManifold IF ∞ F]
    (g : N → EuclideanSpace ℝ (Fin k)) (hg : ContMDiff I (𝓡 k) ∞ g)
    (R : Set N) (hR : IsOpen R) {b₀ : EuclideanSpace ℝ (Fin k)} {ε : ℝ} (hε : 0 < ε)
    (hmaps : ∀ x ∈ R, g x ∈ ball b₀ ε)
    (hreg : ∀ x ∈ R, Surjective (mfderiv I (𝓡 k) g x))
    (hprop : ∀ K ⊆ ball b₀ ε, IsCompact K → IsCompact {x | x ∈ R ∧ g x ∈ K})
    (hsurj : ∀ b ∈ ball b₀ ε, ∃ x ∈ R, g x = b)
    (ψ : F → N) (hψ : IsSmoothEmbedding IF I ∞ ψ) (hψr : range ψ = R ∩ g ⁻¹' {b₀}) :
    ∃ ε' : ℝ, 0 < ε' ∧ ball b₀ ε' ⊆ ball b₀ ε ∧
      ∃ Φ : EuclideanSpace ℝ (Fin k) × F → N,
        IsSmoothEmbedding ((𝓡 k).prod IF) I ∞ Φ ∧
        range Φ = R ∩ g ⁻¹' ball b₀ ε' ∧
        ∀ x z, g (Φ (x, z)) = OpenPartialHomeomorph.univBall b₀ ε' x := by
  classical
  have : Nonempty (Fin (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k)))) :=
    ⟨⟨0, by rw [finrank_euclideanSpace_fin]; omega⟩⟩
  have : Nontrivial (EuclideanSpace ℝ (Fin k)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; exact hk)
  let V : TopologicalSpace.Opens N := ⟨R, hR⟩
  let O : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k)) := ⟨ball b₀ ε, isOpen_ball⟩
  have : LocallyCompactSpace V := hR.locallyCompactSpace
  obtain ⟨hsm, hproper, hsurjW, hregW⟩ :=
    chart_bundle_of_open_GAFD (I := I) hR isOpen_ball hg.contMDiffOn hmaps hreg hprop hsurj
  let fW : V → O := fun x => ⟨g x, hmaps x x.2⟩
  let y₀ : O := ⟨b₀, mem_ball_self hε⟩
  obtain ⟨Q, hy, Θ, hΘf, -⟩ := ehresmann_local_triviality (J := 𝓡 k) fW hsm hproper hregW y₀
  have hregF : ∀ x, fW x = y₀ → Surjective (mfderiv I (𝓡 k) fW x) := fun x _ => hregW x
  let _ := regularFiberChartedSpace fW y₀ hsm hregF
  have := regularFiberIsManifold fW y₀ hsm hregF
  -- the whole fibre over `y₀` as a submanifold of `N`
  have hincl : IsSmoothEmbedding
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) → ℝ) I ∞
      (Subtype.val ∘ Subtype.val : {x : V // fW x = y₀} → N) := by
    have h1 : IsSmoothEmbedding
        𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) → ℝ) I ∞
        (Subtype.val : {x : V // fW x = y₀} → V) :=
      isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF (by simp)
        (contMDiff_regularFiberInclusion fW y₀ hsm hregF) IsEmbedding.subtypeVal
        (mfderiv_regularFiberInclusion_injective fW y₀ hsm hregF)
        (fun _ => BoundarylessManifold.isInteriorPoint)
    exact (IsSmoothEmbedding.of_opens V).comp h1 (by simp)
  have hrange_sub : range ψ ⊆ range (Subtype.val ∘ Subtype.val : {x : V // fW x = y₀} → N) := by
    rw [hψr]
    rintro x ⟨hxR, hxb⟩
    exact ⟨⟨⟨x, hxR⟩, Subtype.ext hxb⟩, rfl⟩
  -- `ψ` lifted to the fibre: a smooth embedding onto the whole fibre
  let ψ' := hincl.lift ψ hrange_sub
  have hψ'emb : IsSmoothEmbedding IF
      𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) → ℝ) ∞ ψ' :=
    hincl.isSmoothEmbedding_lift hψ (by simp) hrange_sub
  have hψ'surj : ∀ z : {x : V // fW x = y₀}, ∃ w, ψ' w = z := by
    intro z
    have hz : (z.1.1 : N) ∈ range ψ := by
      rw [hψr]
      exact ⟨z.1.2, congrArg Subtype.val z.2⟩
    obtain ⟨w, hw⟩ := hz
    refine ⟨w, hincl.isEmbedding.injective ?_⟩
    exact (hincl.comp_lift hrange_sub w).trans hw
  -- a ball around `b₀` inside the trivialized neighbourhood `Q`
  obtain ⟨ε', hε', hballQ⟩ : ∃ ε' > 0,
      ball b₀ ε' ⊆ (Subtype.val : O → EuclideanSpace ℝ (Fin k)) '' (Q : Set O) := by
    have hopen : IsOpen ((Subtype.val : O → EuclideanSpace ℝ (Fin k)) '' (Q : Set O)) :=
      O.2.isOpenMap_subtype_val _ Q.isOpen
    have hmem : b₀ ∈ (Subtype.val : O → EuclideanSpace ℝ (Fin k)) '' (Q : Set O) :=
      ⟨y₀, hy, rfl⟩
    exact Metric.isOpen_iff.mp hopen b₀ hmem
  have hQε : (Subtype.val : O → EuclideanSpace ℝ (Fin k)) '' (Q : Set O) ⊆ ball b₀ ε := by
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  obtain ⟨hcsm, hcemb, hcrange, hc0, hcinj⟩ := univBall_data_BAUGD b₀ hε'
  have hcEmb : IsSmoothEmbedding (𝓡 k) (𝓡 k) ∞ (OpenPartialHomeomorph.univBall b₀ ε') :=
    isSmoothEmbedding_of_injective_mfderiv_of_interior_GSF (by simp) hcsm.contMDiff hcemb
      (fun x => by rw [mfderiv_eq_fderiv]; exact hcinj x)
      (fun _ => BoundarylessManifold.isInteriorPoint)
  let j : Q → EuclideanSpace ℝ (Fin k) := Subtype.val ∘ Subtype.val
  have hj : IsSmoothEmbedding (𝓡 k) (𝓡 k) ∞ j :=
    (IsSmoothEmbedding.of_opens (I := 𝓡 k) O).comp (IsSmoothEmbedding.of_opens (I := 𝓡 k) Q)
      (by simp)
  have hcj : range (OpenPartialHomeomorph.univBall b₀ ε') ⊆ range j := by
    rw [hcrange]
    intro x hx
    obtain ⟨q, hq, rfl⟩ := hballQ hx
    exact ⟨⟨q, hq⟩, rfl⟩
  let ιQ := hj.lift (OpenPartialHomeomorph.univBall b₀ ε') hcj
  have hιQ : IsSmoothEmbedding (𝓡 k) (𝓡 k) ∞ ιQ := hj.isSmoothEmbedding_lift hcEmb (by simp) hcj
  have hjιQ : ∀ x, ((ιQ x : Q) : O).1 = OpenPartialHomeomorph.univBall b₀ ε' x :=
    fun x => hj.comp_lift hcj x
  -- the trivialization restricted to `fibre × (small ball)`
  let U : TopologicalSpace.Opens V := ⟨fW ⁻¹' (Q : Set O), Q.isOpen.preimage hsm.continuous⟩
  have hΘemb : IsSmoothEmbedding
      ((𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ (EuclideanSpace ℝ (Fin k))) → ℝ)).prod
        (𝓡 k)) I ∞ Θ :=
    isSmoothEmbedding_of_isLocalDiffeomorph_of_injective Θ.isLocalDiffeomorph Θ.injective
  have hΦ₂ : IsSmoothEmbedding (IF.prod (𝓡 k)) I ∞
      ((Subtype.val : V → N) ∘ (Subtype.val : U → V) ∘ Θ ∘ Prod.map ψ' ιQ) :=
    (IsSmoothEmbedding.of_opens V).comp ((IsSmoothEmbedding.of_opens (I := I) U).comp
      (hΘemb.comp (hψ'emb.prodMap hιQ) (by simp)) (by simp)) (by simp)
  have hswap : IsSmoothEmbedding ((𝓡 k).prod IF) (IF.prod (𝓡 k)) ∞
      (Prod.swap : EuclideanSpace ℝ (Fin k) × F → F × EuclideanSpace ℝ (Fin k)) :=
    isSmoothEmbedding_of_isLocalDiffeomorph_of_injective
      (Diffeomorph.prodComm (𝓡 k) IF (EuclideanSpace ℝ (Fin k)) F ∞).isLocalDiffeomorph
      (Diffeomorph.prodComm (𝓡 k) IF (EuclideanSpace ℝ (Fin k)) F ∞).injective
  have hgΘ : ∀ (z : F) (x : EuclideanSpace ℝ (Fin k)),
      g (((Θ (ψ' z, ιQ x) : U) : V) : N) = OpenPartialHomeomorph.univBall b₀ ε' x := by
    intro z x
    exact (congrArg Subtype.val (hΘf (ψ' z, ιQ x))).trans (hjιQ x)
  refine ⟨ε', hε', fun x hx => hQε (hballQ hx),
    ((Subtype.val : V → N) ∘ (Subtype.val : U → V) ∘ Θ ∘ Prod.map ψ' ιQ) ∘ Prod.swap,
    hΦ₂.comp hswap (by simp), ?_, fun x z => hgΘ z x⟩
  ext p
  constructor
  · rintro ⟨⟨x, z⟩, rfl⟩
    refine ⟨(Θ (ψ' z, ιQ x)).1.2, ?_⟩
    change g (((Θ (ψ' z, ιQ x) : U) : V) : N) ∈ ball b₀ ε'
    rw [hgΘ z x, ← hcrange]
    exact mem_range_self x
  · rintro ⟨hpR, hpg⟩
    have hpg' : g p ∈ range (OpenPartialHomeomorph.univBall b₀ ε') := by
      rw [hcrange]
      exact hpg
    obtain ⟨x, hx⟩ := hpg'
    have hfv : fW ⟨p, hpR⟩ = ((ιQ x : Q) : O) := Subtype.ext (by rw [hjιQ x]; exact hx.symm)
    have hvU : (⟨p, hpR⟩ : V) ∈ U := by
      change fW ⟨p, hpR⟩ ∈ (Q : Set O)
      rw [hfv]
      exact (ιQ x).2
    let u : U := ⟨⟨p, hpR⟩, hvU⟩
    obtain ⟨z, hz⟩ := hψ'surj (Θ.symm u).1
    have hq : (Θ.symm u).2 = ιQ x := by
      have h := hΘf (Θ.symm u)
      rw [Diffeomorph.apply_symm_apply] at h
      exact Subtype.ext (h.symm.trans hfv)
    refine ⟨(x, z), ?_⟩
    have hpair : (ψ' z, ιQ x) = Θ.symm u := Prod.ext hz hq.symm
    change (((Θ (ψ' z, ιQ x) : U) : V) : N) = p
    rw [hpair, Diffeomorph.apply_symm_apply]

end ProductChart

end DifferentialGeometry.Geometry.Collapse
