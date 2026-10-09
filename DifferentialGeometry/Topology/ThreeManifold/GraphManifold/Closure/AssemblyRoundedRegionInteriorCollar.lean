import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeamCollar

/-!
# FC42 packet T3, part 4: signed collars of a level embedded in the recharted interior

`exists_signedCollar_of_isolated_level` (`Closure/AssemblySeamCollar.lean`, B2) takes a smooth
embedding into the carrier `W` with its own model. When `W` has boundary, the level tori of the
rounded circle region (packet T3) come as smooth embeddings into an open subset of the INTERIOR with
the boundaryless recharted interior model (`interiorSeamModel`); the composition with the inclusion
into `W` is not covered by the tree's immersion-composition lemmas (they ask the final model to be
boundaryless). This file proves the B2 signed collar directly for an embedding into the recharted
interior (`exists_signedCollar_of_isolated_interior_level`): the proof of B2 with the embedding read
in the interior model, where the immersion is used (smoothness of the inverse). Its torus form,
`exists_torusSeam_of_interior_level`, gives a `TorusSeam W` inside the open set, with
`f (seam (t, s)) = c + δ s`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Filter
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section Core

variable {ES HS : Type*} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [TopologicalSpace HS]
  {IS : ModelWithCorners ℝ ES HS} {S : Type*} [TopologicalSpace S] [ChartedSpace HS S]
  [CompactSpace S] [Nonempty S]

/-- **Signed collar of an isolated regular level, embedded in the recharted interior.** -/
theorem exists_signedCollar_of_isolated_interior_level (W : CompactCarrier.{u})
    (O : TopologicalSpace.Opens W.Carrier) (f : W.Carrier → ℝ) (c : ℝ)
    (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f (W.pieceInterior O))
    (pO : S → W.pieceInterior O)
    (hpO : letI := interiorSeamCharts W O
      IsSmoothEmbedding IS interiorSeamModel ∞ pO)
    (hc : ∀ z, f (pO z) = c)
    (hlev : ∀ x : W.pieceInterior O, f x = c → x ∈ range pO)
    (hreg : ∀ z, mfderiv W.model 𝓘(ℝ, ℝ) f (pO z) ≠ 0) :
    ∃ (δ : ℝ) (_ : 0 < δ)
      (Φ : PartialDiffeomorph (IS.prod 𝓘(ℝ, ℝ)) W.model (S × ℝ) W.Carrier ∞),
      Φ.source = univ ×ˢ Ioo (-1) 1 ∧ Φ.target ⊆ W.pieceInterior O ∧
      (∀ z, Φ (z, 0) = pO z) ∧ ∀ p ∈ Φ.source, f (Φ p) = c + δ * p.2 := by
  classical
  let O' := W.pieceInterior O
  let _ := interiorSeamCharts W O
  have hM3 : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ O' := interiorSeamCharts_isManifold W O
  let f' : O' → ℝ := fun x => f x
  have hfat : ∀ x : O', ContMDiffAt W.model 𝓘(ℝ, ℝ) ∞ f x :=
    fun x => hf.contMDiffAt (O'.isOpen.mem_nhds x.2)
  have hf' : ContMDiff interiorSeamModel 𝓘(ℝ, ℝ) ∞ f' :=
    fun x => (hfat x).comp x (contMDiff_val_interiorSeamModel W O x)
  have hpOc : ContMDiff IS interiorSeamModel ∞ pO := hpO.contMDiff
  have hK : IsCompact {x : O' | f' x = c} := by
    have hset : {x : O' | f' x = c} = range pO := by
      ext x
      constructor
      · intro hx
        exact hlev x hx
      · rintro ⟨z, rfl⟩
        exact hc z
    rw [hset]
    exact isCompact_range hpOc.continuous
  have hr : ∀ x : O', f' x = c → mfderiv interiorSeamModel 𝓘(ℝ, ℝ) f' x ≠ 0 := by
    intro x hx
    obtain ⟨z, rfl⟩ := hlev x hx
    exact mfderiv_interiorSeamModel_ne_zero W O (pO z) (hfat (pO z)) (hreg z)
  obtain ⟨r, hr0, U', F, hF, e, hfwd, hback, htime, hval, hzero⟩ :=
    DifferentialGeometry.Manifold.RegularLevel.exists_flowCollar_of_compact_regularLevel_manifold
      interiorSeamModel hf' c hK hr
  have hτ : ∀ s ∈ Ioo (-1 : ℝ) 1, -(r * s) ∈ Ioo (-r) r := by
    intro s hs
    constructor <;> nlinarith [hs.1, hs.2]
  let lvl : S → {x : O' // f' x = c} := fun z => ⟨pO z, hc z⟩
  let toFun : S × ℝ → W.Carrier := fun p => (F (pO p.1, -(r * p.2)) : O').val
  have hFe : ∀ (z : S) (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1),
      F (pO z, -(r * s)) = (e (lvl z, ⟨-(r * s), hτ s hs⟩) : O') := by
    intro z s hs
    rw [hfwd]
  let x₀ : O' := pO (Classical.arbitrary S)
  let toO : W.Carrier → O' := fun y => if h : y ∈ O' then ⟨y, h⟩ else x₀
  have htoO : ∀ x : O', toO x.val = x := fun x => by
    simp [toO, x.2]
  let back : O' → O' := fun x => F (x, f' x - c)
  have hbackU : ∀ w : U', back (w : O') = ((e.symm w).1 : O') := by
    intro w
    simp only [back]
    rw [hback w]
  have hbackR : ∀ w : U', back (w : O') ∈ range pO := by
    intro w
    obtain ⟨z, hz⟩ := hlev _ (e.symm w).1.2
    exact ⟨z, by rw [hbackU w, ← hz]⟩
  let invFun : W.Carrier → S × ℝ := fun y => (Function.invFun pO (back (toO y)), (f y - c) / r)
  have hinj : Injective pO := hpO.isEmbedding.injective
  have hmapS : ∀ p ∈ (univ ×ˢ Ioo (-1 : ℝ) 1 : Set (S × ℝ)),
      toFun p ∈ Subtype.val '' (U' : Set O') := by
    rintro ⟨z, s⟩ ⟨-, hs⟩
    refine ⟨(e (lvl z, ⟨-(r * s), hτ s hs⟩) : O'), (e _).2, ?_⟩
    simp only [toFun]
    rw [hFe z s hs]
  have hmapT : ∀ y ∈ Subtype.val '' (U' : Set O'),
      invFun y ∈ (univ ×ˢ Ioo (-1 : ℝ) 1 : Set (S × ℝ)) := by
    rintro y ⟨x, hxU, rfl⟩
    refine ⟨mem_univ _, ?_⟩
    have ht := htime ⟨x, hxU⟩
    have hb := (e.symm ⟨x, hxU⟩).2.2
    rw [ht] at hb
    change -r < c - f x ∧ c - f x < r at hb
    change -1 < (f x - c) / r ∧ (f x - c) / r < 1
    constructor
    · rw [lt_div_iff₀ hr0]
      linarith [hb.2]
    · rw [div_lt_iff₀ hr0]
      linarith [hb.1]
  have hleft : ∀ p ∈ (univ ×ˢ Ioo (-1 : ℝ) 1 : Set (S × ℝ)), invFun (toFun p) = p := by
    rintro ⟨z, s⟩ ⟨-, hs⟩
    let q : {x : O' // f' x = c} × Ioo (-r) r := (lvl z, ⟨-(r * s), hτ s hs⟩)
    have hy : toFun (z, s) = ((e q : O') : W.Carrier) := by
      simp only [toFun]
      rw [hFe z s hs]
    have hb : back (toO (toFun (z, s))) = pO z := by
      rw [hy, htoO, hbackU, e.symm_apply_apply]
    have hv : f (toFun (z, s)) = c + r * s := by
      rw [hy]
      have := hval q
      change f ((e q : O') : W.Carrier) = c - -(r * s) at this
      rw [this]
      ring
    simp only [invFun]
    rw [hb, hv, Function.leftInverse_invFun hinj z]
    congr 1
    field_simp
    ring
  have hright : ∀ y ∈ Subtype.val '' (U' : Set O'), toFun (invFun y) = y := by
    rintro y ⟨x, hxU, rfl⟩
    let w : U' := ⟨x, hxU⟩
    let q := e.symm w
    have hz₀ : pO (Function.invFun pO (back (toO x.val))) = back (toO x.val) := by
      rw [htoO]
      exact Function.invFun_eq (hbackR w)
    have hpq : pO (Function.invFun pO (back (toO x.val))) = (q.1 : O') := by
      rw [hz₀, htoO]
      exact hbackU w
    have hsq : -(r * ((f x - c) / r)) = (q.2 : ℝ) := by
      rw [htime w]
      field_simp
      ring
    simp only [toFun, invFun]
    rw [hpq, hsq, ← hfwd q]
    change ((e (e.symm w) : O') : W.Carrier) = x
    rw [e.apply_symm_apply]
  have hbackS : ContMDiff interiorSeamModel interiorSeamModel ∞ back :=
    hF.comp (contMDiff_id.prodMk (hf'.sub contMDiff_const))
  have htoFun : ContMDiff (IS.prod 𝓘(ℝ, ℝ)) W.model ∞ toFun := by
    have hs : ContMDiff (IS.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ (fun p : S × ℝ => -(r * p.2)) :=
      ((contDiff_const.mul contDiff_id).neg : ContDiff ℝ ∞ (fun s : ℝ => -(r * s))).contMDiff.comp
        contMDiff_snd
    exact (contMDiff_val_interiorSeamModel W O).comp (hF.comp ((hpOc.comp contMDiff_fst).prodMk hs))
  have hinvOn : ContMDiffOn W.model (IS.prod 𝓘(ℝ, ℝ)) ∞ invFun (Subtype.val '' (U' : Set O')) := by
    rintro y ⟨x, hxU, rfl⟩
    apply ContMDiffAt.contMDiffWithinAt
    refine contMDiffAt_of_interiorSeamModel (K := IS.prod 𝓘(ℝ, ℝ)) (g := invFun) W O x ?_
    have hcomp : invFun ∘ Subtype.val =
        fun x' : O' => (Function.invFun pO (back x'), (f' x' - c) / r) := by
      funext x'
      simp only [Function.comp_apply, invFun, htoO]
      rfl
    rw [hcomp]
    have heq : (pO ∘ fun x' : O' => Function.invFun pO (back x')) =ᶠ[𝓝 x] back := by
      filter_upwards [U'.isOpen.mem_nhds hxU] with x' hx'
      exact Function.invFun_eq (hbackR ⟨x', hx'⟩)
    have hG : ContMDiffAt interiorSeamModel IS ∞
        (fun x' : O' => Function.invFun pO (back x')) x := by
      refine (ContMDiffAt.iff_comp_isImmersionAt
        (f := fun x' : O' => Function.invFun pO (back x')) (φ := pO) (x := x)
        (hpO.isImmersion.isImmersionAt (Function.invFun pO (back x)))).mpr ⟨?_, ?_⟩
      · apply hpO.isEmbedding.isInducing.continuousAt_iff.mpr
        exact hbackS.continuous.continuousAt.congr heq.symm
      · exact (hbackS x).congr_of_eventuallyEq heq
    have hD : ContMDiffAt interiorSeamModel 𝓘(ℝ, ℝ) ∞ (fun x' : O' => (f' x' - c) / r) x :=
      (((contDiff_id.sub contDiff_const).div_const r :
        ContDiff ℝ ∞ (fun t : ℝ => (t - c) / r)).contMDiff.comp
        hf') x
    exact hG.prodMk hD
  let Φ0 : PartialEquiv (S × ℝ) W.Carrier :=
    { toFun := toFun
      invFun := invFun
      source := univ ×ˢ Ioo (-1) 1
      target := Subtype.val '' (U' : Set O')
      map_source' := hmapS
      map_target' := hmapT
      left_inv' := hleft
      right_inv' := hright }
  let Φ : PartialDiffeomorph (IS.prod 𝓘(ℝ, ℝ)) W.model (S × ℝ) W.Carrier ∞ :=
    { toPartialEquiv := Φ0
      open_source := isOpen_univ.prod isOpen_Ioo
      open_target := O'.isOpen.isOpenMap_subtype_val _ U'.isOpen
      contMDiffOn_toFun := htoFun.contMDiffOn
      contMDiffOn_invFun := hinvOn }
  refine ⟨r, hr0, Φ, rfl, ?_, ?_, ?_⟩
  · rintro y ⟨x, -, rfl⟩
    exact x.2
  · intro z
    change toFun (z, 0) = pO z
    have h0 := hzero (lvl z)
    rw [hfwd] at h0
    have h0' : F (pO z, 0) = pO z := h0
    simp only [toFun, mul_zero, neg_zero]
    rw [h0']
  · rintro ⟨z, s⟩ ⟨-, hs⟩
    change f (toFun (z, s)) = c + r * s
    simp only [toFun]
    rw [hFe z s hs]
    have := hval (lvl z, ⟨-(r * s), hτ s hs⟩)
    change f ((e (lvl z, ⟨-(r * s), hτ s hs⟩) : O') : W.Carrier) = c - -(r * s) at this
    rw [this]
    ring

end Core

/-- **Torus seam of a level torus embedded in the recharted interior.** -/
theorem exists_torusSeam_of_interior_level (W : CompactCarrier.{u})
    (O : TopologicalSpace.Opens W.Carrier) (f : W.Carrier → ℝ) (c : ℝ)
    (hf : ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ f (W.pieceInterior O))
    (pO : Torus → W.pieceInterior O)
    (hpO : letI := interiorSeamCharts W O
      IsSmoothEmbedding torusModel interiorSeamModel ∞ pO)
    (hc : ∀ t, f (pO t) = c)
    (hlev : ∀ x : W.pieceInterior O, f x = c → x ∈ range pO)
    (hreg : ∀ t, mfderiv W.model 𝓘(ℝ, ℝ) f (pO t) ≠ 0) :
    ∃ (δ : ℝ) (_ : 0 < δ) (T : TorusSeam W),
      T.collar.target ⊆ W.pieceInterior O ∧ (∀ t, T.collar (t, 0) = pO t) ∧
      ∀ p ∈ signedCollarSource, f (T.collar p) = c + δ * p.2 := by
  have : Nonempty Torus := ⟨(1, 1)⟩
  obtain ⟨δ, hδ, Φ, hsrc, htgt, hzero, hval⟩ :=
    exists_signedCollar_of_isolated_interior_level W O f c hf pO hpO hc hlev hreg
  have hsrc' : Φ.source = signedCollarSource := hsrc.trans univ_prod_Ioo_eq_signedCollarSource
  exact ⟨δ, hδ, ⟨Φ, hsrc', fun y hy => (htgt hy).2⟩, htgt, hzero,
    fun p hp => hval p (hsrc'.symm ▸ hp)⟩

end GC.GraphManifold.Assembly
