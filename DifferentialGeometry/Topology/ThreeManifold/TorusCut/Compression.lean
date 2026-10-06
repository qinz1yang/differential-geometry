import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Sides
import DifferentialGeometry.Topology.PiecewiseLinear.ExtendedLoopTheoremOrientableCh5Port
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.CenteredDiskSimplexMap
import DifferentialGeometry.Topology.PiecewiseLinear.CylinderEndExtension
set_option autoImplicit false

/-!
# Compressing discs and π₁-injectivity of embedded tori

A compressing disc for a map `τ : S → X` is a topological embedding of the closed unit disc
whose boundary circle runs through the image of `τ` along a loop that is not nullhomotopic in
`S`, while its interior misses that image. Such a disc makes `π₁(τ)` non-injective. Conversely,
let `τ` be an injective two-sided torus in a Hausdorff space `X` that becomes a polyhedron under
a homeomorphism from an oriented closed combinatorial 3-manifold `|K|`. If `π₁(τ)` is not
injective, the PL loop theorem gives a PL compressing disc in `|K|`, which is carried back to
`X`. Such a presentation exists as soon as `X` has a PL atlas in which `τ` is a PL piece and
every combinatorial triangulation of `X` is orientable. The tori of a reconstruction of a
smooth torus assembly are two-sided through their seams, so incompressibility is equivalent to
the absence of compressing discs once these two triangulation inputs are available.
-/

noncomputable section
open Set Topology
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Topology.PiecewiseLinear

namespace GC.Topology
universe u v w
variable {S : Type u} {X : Type v} [TopologicalSpace S] [TopologicalSpace X]

def IsCompressingDisk (τ : C(S, X)) (d : C(closedDisk, X)) : Prop :=
  IsEmbedding d ∧ (∀ z : closedDisk, d z ∈ range τ ↔ ‖(z : ℂ)‖ = 1) ∧
    ∃ γ : freeLoop S, τ.comp γ = diskTrace d ∧ ¬ γ.Nullhomotopic

theorem not_injective_fundamentalGroup_map_of_freeLoop (τ : C(S, X)) (γ : freeLoop S)
    (hγ : ¬ γ.Nullhomotopic) (hτγ : (τ.comp γ).Nullhomotopic) :
    ¬ Function.Injective (FundamentalGroup.map τ (γ 0)) := by
  intro hinj
  let p : Path (γ 0) (γ 0) := circleToPath ⟨γ, rfl⟩
  have hp : pathToCircle p = γ :=
    congrArg Subtype.val ((basedPathCircleHomeomorph (γ 0)).apply_symm_apply ⟨γ, rfl⟩)
  have h1 : FundamentalGroup.map τ (γ 0) (Path.Homotopic.Quotient.mk p) = 1 := by
    apply Path.Homotopic.Quotient.eq.mpr
    apply (pathToCircle_nullhomotopic_iff (p.map τ.continuous)).mp
    rw [pathToCircle_natural, hp]
    exact hτγ
  have h2 : (show FundamentalGroup S (γ 0) from Path.Homotopic.Quotient.mk p) = 1 :=
    hinj (h1.trans (map_one _).symm)
  apply hγ
  rw [← hp]
  exact (pathToCircle_nullhomotopic_iff p).mpr (Path.Homotopic.Quotient.eq.mp h2)

theorem IsCompressingDisk.not_injective {τ : C(S, X)} {d : C(closedDisk, X)}
    (h : IsCompressingDisk τ d) : ∃ x, ¬ Function.Injective (FundamentalGroup.map τ x) := by
  obtain ⟨-, -, γ, hγd, hγ⟩ := h
  refine ⟨γ 0, not_injective_fundamentalGroup_map_of_freeLoop τ γ hγ ?_⟩
  rw [hγd]
  exact diskTrace_nullhomotopic d

theorem isTwoSided_range_of_openPartialHomeomorph {T : Type w} [TopologicalSpace T]
    [ConnectedSpace T] (c : OpenPartialHomeomorph (T × ℝ) X)
    (hc : c.source = {p | -1 < p.2 ∧ p.2 < 1}) : IsTwoSided (range fun t => c (t, 0)) := by
  have hsrc : ∀ t : T, ∀ s : ℝ, -1 < s → s < 1 → (t, s) ∈ c.source :=
    fun t s h1 h2 => by
    rw [hc]
    exact ⟨h1, h2⟩
  have hf : Continuous fun t : T => c (t, 0) :=
    c.continuousOn.comp_continuous (continuous_id.prodMk continuous_const)
      fun t => hsrc t 0 (by norm_num) (by norm_num)
  have hconn : IsConnected (range fun t => c (t, 0)) := isConnected_range hf
  intro x hx
  have hC : connectedComponentIn (range fun t => c (t, 0)) x = range fun t => c (t, 0) :=
    Subset.antisymm (connectedComponentIn_subset _ _)
      (hconn.isPreconnected.subset_connectedComponentIn hx Subset.rfl)
  rw [hC]
  have hST : (range fun t => c (t, 0)) ⊆ c.target := by
    rintro _ ⟨t, rfl⟩
    exact c.map_source (hsrc t 0 (by norm_num) (by norm_num))
  refine ⟨c.target, c.open_target.mem_nhdsSet.mpr hST, ?_⟩
  intro W hW hWV _ hpre
  obtain ⟨t₀, rfl⟩ := hx
  have hcont : ContinuousAt (fun s : ℝ => c (t₀, s)) 0 :=
    (c.continuousAt (hsrc t₀ 0 (by norm_num) (by norm_num))).comp
      (continuous_const.prodMk continuous_id).continuousAt
  have hW0 : ∀ᶠ s in 𝓝 (0 : ℝ), c (t₀, s) ∈ W :=
    hcont.preimage_mem_nhds (mem_nhdsSet_iff_forall.mp hW _ ⟨t₀, rfl⟩)
  have hnot : ∀ s : ℝ, -1 < s → s < 1 → s ≠ 0 →
      c (t₀, s) ∉ range fun t => c (t, 0) := by
    rintro s h1 h2 hs ⟨t, ht⟩
    have := congrArg Prod.snd (c.injOn (hsrc t 0 (by norm_num) (by norm_num))
      (hsrc t₀ s h1 h2) ht)
    exact hs this.symm
  let Up := c '' {p : T × ℝ | 0 < p.2 ∧ p.2 < 1}
  let Um := c '' {p : T × ℝ | -1 < p.2 ∧ p.2 < 0}
  have hUp : IsOpen Up := c.isOpen_image_of_subset_source
    ((isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const))
    fun p hp => hsrc p.1 p.2 (by linarith [hp.1]) hp.2
  have hUm : IsOpen Um := c.isOpen_image_of_subset_source
    ((isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const))
    fun p hp => hsrc p.1 p.2 hp.1 (by linarith [hp.2])
  have hcover : W \ (range fun t => c (t, 0)) ⊆ Up ∪ Um := by
    rintro y ⟨hyW, hyS⟩
    obtain ⟨p, hp, rfl⟩ : y ∈ c '' c.source :=
      ⟨c.symm y, c.map_target (hWV hyW), c.right_inv (hWV hyW)⟩
    rw [hc] at hp
    rcases lt_trichotomy p.2 0 with hlt | heq | hgt
    · exact Or.inr ⟨p, ⟨hp.1, hlt⟩, rfl⟩
    · exact (hyS ⟨p.1, by rw [← heq]⟩).elim
    · exact Or.inl ⟨p, ⟨hgt, hp.2⟩, rfl⟩
  obtain ⟨sp, hspW, hsp0, hsp1⟩ := (hW0.filter_mono nhdsWithin_le_nhds).and
    (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)) |>.exists
  obtain ⟨sm, hsmW, hsm0, hsm1⟩ := (hW0.filter_mono nhdsWithin_le_nhds).and
    (Ioo_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num)) |>.exists
  obtain ⟨y, ⟨-, hyS⟩, ⟨p, hp, rfl⟩, ⟨q, hq, hpq⟩⟩ := hpre Up Um hUp hUm hcover
    ⟨c (t₀, sp), ⟨hspW, hnot sp (by linarith) hsp1 hsp0.ne'⟩,
      ⟨(t₀, sp), ⟨hsp0, hsp1⟩, rfl⟩⟩
    ⟨c (t₀, sm), ⟨hsmW, hnot sm hsm0 (by linarith) hsm1.ne⟩,
      ⟨(t₀, sm), ⟨hsm0, hsm1⟩, rfl⟩⟩
  have := congrArg Prod.snd (c.injOn (hsrc q.1 q.2 hq.1 (by linarith [hq.2]))
    (hsrc p.1 p.2 (by linarith [hp.1]) hp.2) hpq)
  linarith [hp.1, hq.2]

theorem exists_ne_one_map_eq_one_of_not_injective {L : Type w} {K : Type*} [TopologicalSpace L]
    [TopologicalSpace K] (τ : C(S, X)) (Ψ : S ≃ₜ L) (ι : C(L, K)) (h : K ≃ₜ X)
    (hfac : ∀ t, τ t = h (ι (Ψ t))) {x : S}
    (hx : ¬ Function.Injective (FundamentalGroup.map τ x)) :
    ∃ g : FundamentalGroup L (Ψ x), g ≠ 1 ∧ FundamentalGroup.map ι (Ψ x) g = 1 := by
  have hfac' : τ = (h : C(K, X)).comp (ι.comp (Ψ : C(S, L))) := ContinuousMap.ext hfac
  subst hfac'
  rw [injective_iff_map_eq_one] at hx
  push Not at hx
  obtain ⟨g, hg1, hgne⟩ := hx
  have hhinj : Function.Injective (FundamentalGroup.map (h : C(K, X)) (ι (Ψ x))) :=
    injective_fundamentalGroup_map_of_leftInverse (h : C(K, X)) (h.symm : C(X, K))
      (fun y => h.symm_apply_apply y) _
  have hΨinj : Function.Injective (FundamentalGroup.map (Ψ : C(S, L)) x) :=
    injective_fundamentalGroup_map_of_leftInverse (Ψ : C(S, L)) (Ψ.symm : C(L, S))
      (fun y => Ψ.symm_apply_apply y) _
  refine ⟨FundamentalGroup.map (Ψ : C(S, L)) x g,
    fun h0 => hgne (hΨinj (h0.trans (map_one _).symm)), hhinj ?_⟩
  rw [map_one]
  rw [fundamentalGroup_map_comp, fundamentalGroup_map_comp] at hg1
  exact hg1

def HasPLPresentation (τ : C(Torus, X)) : Prop :=
  ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
    (_ : Finite K.faces)
    (h : K.space ≃ₜ X), IsCombinatorialManifold 3 K ∧ IsOrientable 3 K ∧
      IsPolyhedron (((↑) : K.space → EuclideanSpace ℝ (Fin N)) '' (h ⁻¹' range τ))

def IsTameCompressingDisk (τ : C(S, X)) (d : C(closedDisk, X)) : Prop :=
  IsCompressingDisk τ d ∧
    ∃ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N)))
      (h : K.space ≃ₜ X),
      IsPolyhedron (((↑) : K.space → EuclideanSpace ℝ (Fin N)) '' (h ⁻¹' range τ)) ∧
        IsPLBall 2 (((↑) : K.space → EuclideanSpace ℝ (Fin N)) '' (h ⁻¹' range d))

theorem IsTameCompressingDisk.isCompressingDisk {τ : C(S, X)} {d : C(closedDisk, X)}
    (h : IsTameCompressingDisk τ d) : IsCompressingDisk τ d :=
  h.1

private def circleHomeomorphUnitSphere :
    Circle ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype fun z => by
    change z ∈ Metric.sphere (0 : ℂ) 1 ↔
      Complex.orthonormalBasisOneI.repr z ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, mem_sphere_zero_iff_norm,
      Complex.orthonormalBasisOneI.repr.norm_map]

open Classical in
theorem exists_isCompressingDisk_of_triangulation [T2Space X] {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {τ : C(Torus, X)} (hτ : Function.Injective τ)
    (K : Geometry.SimplicialComplex ℝ E) [hKfin : Finite K.faces] (h : K.space ≃ₜ X)
    (hK : IsCombinatorialManifold 3 K) (hKo : IsOrientable 3 K)
    (hpoly : IsPolyhedron (((↑) : K.space → E) '' (h ⁻¹' range τ)))
    (htwo : IsTwoSided (range τ)) {x : Torus}
    (hx : ¬ Function.Injective (FundamentalGroup.map τ x)) :
    ∃ d, IsCompressingDisk τ d ∧
      IsPLBall 2 (((↑) : K.space → E) '' (h ⁻¹' range d)) := by
  obtain ⟨L, hLfin, hLspace⟩ := hpoly.exists_simplicialComplex
  have hLfin' : Finite L.faces := hLfin.to_subtype
  have hmemL : ∀ k : K.space, (k : E) ∈ L.space ↔ h k ∈ range τ := by
    intro k
    rw [hLspace]
    constructor
    · rintro ⟨k', hk', hkk'⟩
      rwa [← Subtype.ext hkk']
    · intro hk
      exact ⟨k, hk, rfl⟩
  have hLK : L.space ⊆ K.space := by
    rw [hLspace]
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hbd : (boundaryComplex 3 K).space = ∅ := by
    have hf : (boundaryComplex 3 K).faces = ∅ := hK.boundaryComplex_faces_eq_empty
    rw [Geometry.SimplicialComplex.space, hf]
    simp
  have hLK' : L.space ⊆ K.space \ (boundaryComplex 3 K).space := by
    rw [hbd, sdiff_empty]
    exact hLK
  have hψmem : ∀ t, ((h.symm (τ t) : K.space) : E) ∈ L.space := fun t =>
    (hmemL _).mpr (by rw [h.apply_symm_apply]; exact mem_range_self t)
  let ψ : C(Torus, L.space) := ⟨fun t => ⟨h.symm (τ t), hψmem t⟩,
    (continuous_subtype_val.comp (h.symm.continuous.comp τ.continuous)).subtype_mk _⟩
  have hψinj : Function.Injective ψ := by
    intro s t hst
    have h1 : ((ψ s : L.space) : E) = ψ t := congrArg Subtype.val hst
    exact hτ (h.symm.injective (Subtype.ext h1))
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨t, ht⟩ := (hmemL ⟨y, hLK hy⟩).mp hy
    refine ⟨t, Subtype.ext ?_⟩
    change ((h.symm (τ t) : K.space) : E) = y
    rw [ht, h.symm_apply_apply]
  let Ψ : Torus ≃ₜ L.space :=
    ψ.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩)
  have hτΨ : ∀ t, τ t = h ⟨Ψ t, hLK (Ψ t).2⟩ := by
    intro t
    have hk : (⟨Ψ t, hLK (Ψ t).2⟩ : K.space) = h.symm (τ t) := Subtype.ext rfl
    rw [hk, h.apply_symm_apply]
  have hL : IsCombinatorialManifold 2 L := isCombinatorialManifold_two_of_homeomorph_sphere_prod L
    (Ψ.symm.trans (circleHomeomorphUnitSphere.prodCongr circleHomeomorphUnitSphere))
  have htwo' : IsTwoSided (((↑) : K.space → E) ⁻¹' L.space) := by
    have h1 := htwo.preimage_of_isInducing h.isInducing (by rw [h.range_coe]; exact Filter.univ_mem)
    have h2 : ((↑) : K.space → E) ⁻¹' L.space = h ⁻¹' range τ := by
      ext k
      exact hmemL k
    rw [h2]
    exact h1
  let ι : C(L.space, K.space) :=
    ⟨Set.inclusion (hLK'.trans sdiff_subset), continuous_inclusion _⟩
  obtain ⟨g, hgne, hgmap⟩ := exists_ne_one_map_eq_one_of_not_injective τ Ψ ι h hτΨ hx
  obtain ⟨Δ, r, hr, hΔ, hmeet, hb, hess⟩ :=
    exists_compressing_disk_of_twoSided_surface K hKfin
      hK.isCombinatorialManifoldWithBoundary hKo L hLfin' hL hLK' htwo' (Ψ x) g hgne hgmap
  obtain ⟨σ, hσc, hσi, hσball, hσsphere, -⟩ :=
    exists_continuous_injective_image_closedBall_eq_stdSimplex
  let R := Complex.orthonormalBasisOneI.repr
  have hstd : ∀ z : closedDisk, σ (R z) ∈ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := by
    intro z
    rw [← hσball]
    refine ⟨R z, ?_, rfl⟩
    have hz := z.2
    rw [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    rwa [LinearIsometryEquiv.norm_map]
  have hbs : stdSimplexBoundary 2 ⊆ Convexity.StdSimplex.coordinateSet ℝ (Fin 3) :=
    fun y hy => hy.1
  have hrc : ContinuousOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) :=
    hr.2.1.continuousOn
  let F : closedDisk → E := fun z => r (σ (R z))
  have hFΔ : ∀ z, F z ∈ Δ := fun z => hr.1.mapsTo (hstd z)
  have hFK : ∀ z, F z ∈ K.space := fun z => (hΔ (hFΔ z)).1
  have hFc : Continuous F :=
    hrc.comp_continuous (hσc.comp (R.continuous.comp continuous_subtype_val)) hstd
  have hFmem : ∀ z, F z ∈ L.space ↔ ‖(z : ℂ)‖ = 1 := by
    intro z
    have h1 : F z ∈ L.space ↔ F z ∈ r '' stdSimplexBoundary 2 := by
      rw [← hmeet]
      exact ⟨fun hz => ⟨hFΔ z, hz⟩, fun hz => hz.2⟩
    rw [h1, hr.1.injOn.mem_image_iff hbs (hstd z), ← hσsphere, hσi.mem_set_image,
      mem_sphere_zero_iff_norm, LinearIsometryEquiv.norm_map]
  let d : C(closedDisk, X) :=
    ⟨fun z => h ⟨F z, hFK z⟩, h.continuous.comp (hFc.subtype_mk _)⟩
  have hFinj : Function.Injective F := by
    intro z w hzw
    exact Subtype.ext (R.injective (hσi (hr.1.injOn (hstd z) (hstd w) hzw)))
  have hdinj : Function.Injective d := by
    intro z w hzw
    exact hFinj (congrArg Subtype.val (h.injective hzw))
  have hdmem : ∀ z, d z ∈ range τ ↔ ‖(z : ℂ)‖ = 1 := fun z =>
    (hmemL ⟨F z, hFK z⟩).symm.trans (hFmem z)
  have hdb : ∀ θ : loopCircle, ‖((diskBoundary θ : closedDisk) : ℂ)‖ = 1 := fun θ =>
    Circle.norm_coe (AddCircle.toCircle θ)
  let γ : freeLoop Torus := ⟨fun θ => Ψ.symm ⟨F (diskBoundary θ), (hFmem _).mpr (hdb θ)⟩,
    Ψ.symm.continuous.comp ((hFc.comp diskBoundary.continuous).subtype_mk _)⟩
  have hγd : τ.comp γ = diskTrace d := by
    ext θ
    change τ (Ψ.symm _) = h ⟨F (diskBoundary θ), hFK _⟩
    rw [hτΨ, Homeomorph.apply_symm_apply]
  have hβmem : ∀ θ : loopCircle,
      r (σ (planarCircleParam θ)) ∈ r '' stdSimplexBoundary 2 := fun θ =>
    ⟨σ (planarCircleParam θ),
      by rw [← hσsphere]; exact ⟨_, (planarCircleParam θ).2, rfl⟩, rfl⟩
  have hs : ∀ φ : loopCircle, σ (planarCircleParam φ) ∈
      Convexity.StdSimplex.coordinateSet ℝ (Fin 3) := fun φ => by
    rw [← hσball]
    exact ⟨_, Metric.sphere_subset_closedBall (planarCircleParam φ).2, rfl⟩
  let β₀ : loopCircle → r '' stdSimplexBoundary 2 := fun θ =>
    ⟨r (σ (planarCircleParam θ)), hβmem θ⟩
  have hβc : Continuous β₀ := (hrc.comp_continuous
    (hσc.comp (continuous_subtype_val.comp planarCircleParam.continuous)) hs).subtype_mk _
  have hβinj : Function.Injective β₀ := by
    intro θ θ' hθ
    have h1 : r (σ (planarCircleParam θ)) = r (σ (planarCircleParam θ')) :=
      congrArg Subtype.val hθ
    exact planarCircleParam.injective (Subtype.ext (hσi (hr.1.injOn (hs θ) (hs θ') h1)))
  have hβsurj : Function.Surjective β₀ := by
    rintro ⟨y, w, hw, rfl⟩
    rw [← hσsphere] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    refine ⟨planarCircleParam.symm ⟨v, hv⟩, Subtype.ext ?_⟩
    change r (σ (planarCircleParam (planarCircleParam.symm ⟨v, hv⟩))) = r (σ v)
    rw [Homeomorph.apply_symm_apply]
  let β : loopCircle ≃ₜ r '' stdSimplexBoundary 2 :=
    hβc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective β₀ ⟨hβinj, hβsurj⟩)
  have hkey : ∀ θ, F (diskBoundary θ) = (β θ : E) := fun θ => by
    change r (σ (R (AddCircle.toCircle θ : ℂ))) = r (σ (planarCircleParam θ))
    rw [planarCircleParam_apply]
  have hball : IsPLBall 2 (((↑) : K.space → E) '' (h ⁻¹' range d)) := by
    have hΔeq : ((↑) : K.space → E) '' (h ⁻¹' range d) = Δ := by
      apply Subset.antisymm
      · rintro _ ⟨k, ⟨z, hz⟩, rfl⟩
        have hk : k = ⟨F z, hFK z⟩ := h.injective hz.symm
        rw [hk]
        exact hFΔ z
      · intro y hy
        obtain ⟨w, hw, rfl⟩ := hr.1.surjOn hy
        rw [← hσball] at hw
        obtain ⟨v, hv, rfl⟩ := hw
        have hz : R.symm v ∈ closedDisk := by
          rw [Metric.mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map]
          rwa [Metric.mem_closedBall, dist_zero_right] at hv
        refine ⟨⟨F ⟨R.symm v, hz⟩, hFK _⟩, ⟨⟨R.symm v, hz⟩, rfl⟩, ?_⟩
        change r (σ (R (R.symm v))) = r (σ v)
        rw [LinearIsometryEquiv.apply_symm_apply]
    rw [hΔeq]
    exact ⟨r, hr⟩
  refine ⟨d, ⟨(d.continuous.isClosedEmbedding hdinj).isEmbedding, hdmem, γ, hγd,
    fun hγ => hess ?_⟩, hball⟩
  have hn := (hγ.comp_right (Ψ : C(Torus, L.space))).comp_left
    (β.symm : C(r '' stdSimplexBoundary 2, loopCircle))
  have heq : (⟨Set.inclusion hb, continuous_inclusion hb⟩ :
      C(r '' stdSimplexBoundary 2, L.space)) =
      ((Ψ : C(Torus, L.space)).comp γ).comp
        (β.symm : C(r '' stdSimplexBoundary 2, loopCircle)) := by
    refine ContinuousMap.ext fun y => Subtype.ext ?_
    change (y : E) = ((Ψ (Ψ.symm ⟨F (diskBoundary (β.symm y)), _⟩) : L.space) : E)
    rw [Homeomorph.apply_symm_apply]
    change (y : E) = F (diskBoundary (β.symm y))
    rw [hkey, Homeomorph.apply_symm_apply]
  rw [heq]
  exact hn

theorem exists_isTameCompressingDisk_of_hasPLPresentation [T2Space X] {τ : C(Torus, X)}
    (hτ : Function.Injective τ) (hP : HasPLPresentation τ) (htwo : IsTwoSided (range τ))
    {x : Torus} (hx : ¬ Function.Injective (FundamentalGroup.map τ x)) :
    ∃ d, IsTameCompressingDisk τ d := by
  obtain ⟨N, K, hKfin, h, hK, hKo, hpoly⟩ := hP
  obtain ⟨d, hd, hball⟩ :=
    exists_isCompressingDisk_of_triangulation hτ K h hK hKo hpoly htwo hx
  exact ⟨d, hd, N, K, h, hpoly, hball⟩

def HasPLPieceAtlas (τ : C(Torus, X)) : Prop :=
  ∃ A : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X,
    letI := A
    HasGroupoid X (plGroupoid 3) ∧
      ∃ N : ℕ, Nonempty (PLPieceIn (EuclideanSpace ℝ (Fin N)) 3 X (range τ))

def IsTriangulationOrientable (X : Type v) [TopologicalSpace X] : Prop :=
  ∀ (N : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))) [Finite K.faces],
    IsCombinatorialManifold 3 K → Nonempty (K.space ≃ₜ X) → IsOrientable 3 K

theorem hasPLPresentation_of_hasPLPieceAtlas [T2Space X] [CompactSpace X] {τ : C(Torus, X)}
    (hA : HasPLPieceAtlas τ) (hO : IsTriangulationOrientable X) : HasPLPresentation τ := by
  obtain ⟨A, hG, N₁, ⟨S⟩⟩ := hA
  let := A
  have : Nonempty X := ⟨τ (1, 1)⟩
  obtain ⟨T⟩ := exists_pLPiece_univ (n := 3) (X := X)
  obtain ⟨K', hK', hfin', hcomb⟩ :=
    T.piece.exists_isSubdivision_isCombinatorialManifold_succ (m := 2)
  let T' := T.piece.subdivide K' hK' hfin'
  have hKfin : Finite K'.faces := hfin'.to_subtype
  have hSfin : Finite S.complex.faces := S.finite_faces.to_subtype
  have hKc : CompactSpace K'.space :=
    isCompact_iff_compactSpace.mp (isPolyhedron_space K').isCompact
  let f : K'.space → X := fun k => T'.map k
  have hfc : Continuous f := T'.continuousOn.domRestrict
  have hfinj : Function.Injective f := fun a b hab => Subtype.ext (T'.bijOn.injOn a.2 b.2 hab)
  have hfsurj : Function.Surjective f := fun y => by
    obtain ⟨k, hk, hky⟩ := T'.bijOn.surjOn (mem_univ y)
    exact ⟨⟨k, hk⟩, hky⟩
  let h : K'.space ≃ₜ X :=
    hfc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  refine ⟨T.ambientDim, K', hKfin, h, hcomb, hO _ K' hcomb ⟨h⟩, ?_⟩
  have htr := S.isPLHomeomorphOn_transition_of_subset T' (subset_univ _)
  have heq : ((↑) : K'.space → EuclideanSpace ℝ (Fin T.ambientDim)) '' (h ⁻¹' range τ) =
      T'.complex.space ∩ T'.map ⁻¹' range τ := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨hy, hyS⟩
      exact ⟨⟨y, hy⟩, hyS, rfl⟩
  rw [heq, ← htr.1.image_eq]
  exact (isPolyhedron_space S.complex).image_of_isPiecewiseAffineOn htr.2.1 htr.1.injOn

end GC.Topology

namespace GC.Endpoint
namespace SmoothAssembly
open GC.Topology
universe u
variable {C : CompactCarrier.{u}} {G : TorusGluing C}

theorem isTwoSided_range_torusInPrime (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P) (i : Fin G.count) :
    IsTwoSided (range (A.torusInPrime r i)) := by
  have h := isTwoSided_range_of_openPartialHomeomorph
    (A.primeSeam r i).toOpenPartialHomeomorph (A.primeSeam_source r i)
  have he : (range fun t => (A.primeSeam r i).toOpenPartialHomeomorph (t, 0)) =
      range (A.torusInPrime r i) := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, (A.primeSeam_zero r i t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, A.primeSeam_zero r i t⟩
  rw [he] at h
  exact h

theorem not_incompressible_of_isCompressingDisk (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P) (i : Fin G.count)
    {d : C(closedDisk, P.Carrier)} (hd : IsCompressingDisk (A.torusInPrime r i) d) :
    ¬ A.Incompressible r := by
  obtain ⟨x, hx⟩ := hd.not_injective
  exact fun h => hx (h i x)

theorem exists_isTameCompressingDisk_of_not_incompressible (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P)
    (hP : ∀ i, HasPLPresentation (A.torusInPrime r i)) (h : ¬ A.Incompressible r) :
    ∃ i d, IsTameCompressingDisk (A.torusInPrime r i) d := by
  simp only [Incompressible, not_forall] at h
  obtain ⟨i, x, hx⟩ := h
  exact ⟨i, exists_isTameCompressingDisk_of_hasPLPresentation
    (A.torusInPrime_isEmbedding r i).injective (hP i) (A.isTwoSided_range_torusInPrime r i) hx⟩

theorem incompressible_iff_of_hasPLPresentation (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P)
    (hP : ∀ i, HasPLPresentation (A.torusInPrime r i)) :
    A.Incompressible r ↔ ∀ i d, ¬ IsCompressingDisk (A.torusInPrime r i) d := by
  constructor
  · intro h i d hd
    exact A.not_incompressible_of_isCompressingDisk r i hd h
  · intro h
    by_contra hn
    obtain ⟨i, d, hd⟩ := A.exists_isTameCompressingDisk_of_not_incompressible r hP hn
    exact h i d hd.isCompressingDisk

theorem incompressible_iff_of_hasPLPieceAtlas (A : SmoothAssembly G)
    {P : ConnectedClosedOrientedManifold.{u} 3} (r : A.Reconstruction P)
    (hA : ∀ i, HasPLPieceAtlas (A.torusInPrime r i))
    (hO : IsTriangulationOrientable P.Carrier) :
    A.Incompressible r ↔ ∀ i d, ¬ IsCompressingDisk (A.torusInPrime r i) d :=
  A.incompressible_iff_of_hasPLPresentation r fun i =>
    hasPLPresentation_of_hasPLPieceAtlas (hA i) hO

end SmoothAssembly
end GC.Endpoint
