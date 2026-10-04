import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyInverseSmooth
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySeams

/-!
# Chapter-14 assembly, bridge B2-side: half collars of a torus seam inside a piece

`exists_halfCollar_of_torusSeam` is the B2-side statement in the corrected form F2 (design
erratum E1; review item 5, D7), verbatim from `build-logs/scratch/ASM-FIX/AssemblyInterfacesV2.lean`.
The frozen V1 form (`AssemblyInterfaces.lean:415`) was vacuous: for `q := z t`, `hz0` gives
`P.map (z t) = S.collar (t, 0)`, a point of `S.collar.target`; `hloc` then makes `P.map` a local
diffeomorphism at `z t`, so by `IsLocalDiffeomorphAt.isInteriorPoint_iff` and `S.target_interior`
the point `z t` is interior, contradicting `hzb`.

Route: the lift is `L := P.map⁻¹ ∘ S.collar ∘ (id × ∓)` on `halfCollarSource`; its inverse
`q ↦ (S.collar⁻¹ (P.map q))` read in the half line is smooth with bijective differential, and
`contMDiffOn_of_leftInverse_of_bijective_mfderiv` (`AssemblyInverseSmooth.lean`) gives smoothness of
`L` at the boundary points. The strong form `exists_halfCollar_of_torusSeam_of_range` also records
the target (the whole preimage of the seam target) and that the zero section consists of boundary
points (inputs of B3's `boundary_exhausted`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

section HalfCollar

/-- The zero section of the half collar model consists of boundary points. -/
theorem halfCollar_isBoundaryPoint_halfZero (t : Torus) :
    halfCollarModel.IsBoundaryPoint (t, halfZero) := by
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint]
  intro h
  change (t, halfZero) ∈ halfCollarModel.interior (Torus × EuclideanHalfSpace 1) at h
  rw [ModelWithCorners.interior_prod] at h
  have hh := h.2
  change (modelWithCornersEuclideanHalfSpace 1).IsInteriorPoint halfZero at hh
  rw [ModelWithCorners.IsInteriorPoint, interior_range_modelWithCornersEuclideanHalfSpace] at hh
  change (0 : ℝ) < 0 at hh
  exact lt_irrefl _ hh

/-- A nonnegative smooth function, read as a point of the half line. -/
theorem contMDiffOn_halfPoint_max {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {u : M → ℝ} {s : Set M} (hu : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ u s) (hpos : ∀ x ∈ s, 0 ≤ u x) :
    ContMDiffOn I (𝓡∂ 1) ∞ (fun x => halfPoint (max (u x) 0) (le_max_right _ _)) s := by
  have hcu : ContinuousOn u s := hu.continuousOn
  intro x hx
  rw [contMDiffWithinAt_iff_target]
  refine ⟨?_, ?_⟩
  · have hind : Topology.IsInducing
        (Subtype.val : EuclideanHalfSpace 1 → EuclideanSpace ℝ (Fin 1)) :=
      Topology.IsInducing.subtypeVal
    exact hind.continuousWithinAt_iff.mpr (((PiLp.continuous_toLp 2 _).comp_continuousOn
      (continuousOn_pi.mpr fun _ => (continuous_id.max continuous_const).comp_continuousOn hcu)) x hx)
  · have hlin : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞
        (fun r : ℝ => (WithLp.toLp 2 (fun _ : Fin 1 => r) : EuclideanSpace ℝ (Fin 1))) :=
      ((EuclideanSpace.equiv (Fin 1) ℝ).symm.toContinuousLinearMap.contDiff.comp
        (contDiff_pi.mpr fun _ => contDiff_id)).contMDiff
    refine ((hlin.comp_contMDiffOn hu) x hx).congr (fun y hy => ?_) ?_
    · change (WithLp.toLp 2 (fun _ : Fin 1 => max (u y) 0) : EuclideanSpace ℝ (Fin 1)) = _
      simp only [Function.comp_apply, max_eq_left (hpos y hy)]
    · change (WithLp.toLp 2 (fun _ : Fin 1 => max (u x) 0) : EuclideanSpace ℝ (Fin 1)) = _
      simp only [Function.comp_apply, max_eq_left (hpos x hx)]

/-- **B2-side, strong form.** For an injective piece whose image meets the target of a torus seam
exactly in the closed side-`b` half collar, the inverse of the piece map gives an actual half
collar in the piece, with `P.map (L (t, s)) = seam (t, ∓s)` on all of `0 ≤ s < 1`; its target is
the whole preimage of the seam target and its zero section consists of boundary points. -/
theorem exists_halfCollar_of_torusSeam_of_range {W : CompactCarrier.{u}} (S : TorusSeam W)
    (P : PieceEmbedding W) (b : Bool)
    (hrange : range P.map ∩ S.collar.target =
      S.collar '' {p | p ∈ signedCollarSource ∧ if b then p.2 ≤ 0 else 0 ≤ p.2}) :
    ∃ L : PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) P.Piece ∞,
      L.source = halfCollarSource ∧ L.target = P.map ⁻¹' S.collar.target ∧
      (∀ t, (𝓡∂ 3).IsBoundaryPoint (L (t, halfZero))) ∧
      ∀ t s (hs : 0 ≤ s), s < 1 →
        P.map (L (t, halfPoint s hs)) = S.collar (t, if b then -s else s) := by
  classical
  let C := S.collar
  have hCs : C.source = signedCollarSource := S.source_eq
  let σ : ℝ → ℝ := fun s => if b then -s else s
  have hσσ : ∀ s, σ (σ s) = s := fun s => by cases b <;> simp [σ]
  have hside : ∀ s : ℝ, (if b then s ≤ 0 else 0 ≤ s) ↔ 0 ≤ σ s := fun s => by
    cases b <;> simp [σ]
  have hσlt : ∀ s : ℝ, -1 < s → s < 1 → σ s < 1 := fun s h1 h2 => by
    cases b <;> simp [σ] <;> linarith
  have hσsrc : ∀ s : ℝ, 0 ≤ s → s < 1 → -1 < σ s ∧ σ s < 1 := fun s h0 h1 => by
    cases b <;> simp [σ] <;> constructor <;> linarith
  have hσsm : ContDiff ℝ ∞ σ := by
    cases b
    · exact contDiff_id
    · exact contDiff_neg
  let κ : Torus × EuclideanHalfSpace 1 → W.Carrier := fun p => C (p.1, σ (p.2.val 0))
  have hκsrc : ∀ p ∈ halfCollarSource, (p.1, σ (p.2.val 0)) ∈ C.source := fun p hp => by
    rw [hCs]
    exact hσsrc _ p.2.2 hp
  have hκrange : ∀ p ∈ halfCollarSource, κ p ∈ range P.map := by
    intro p hp
    have hmem : κ p ∈ C '' {q | q ∈ signedCollarSource ∧ if b then q.2 ≤ 0 else 0 ≤ q.2} :=
      ⟨(p.1, σ (p.2.val 0)), ⟨hCs ▸ hκsrc p hp, (hside _).mpr (by rw [hσσ]; exact p.2.2)⟩, rfl⟩
    rw [← hrange] at hmem
    exact hmem.1
  let L0 : Torus × EuclideanHalfSpace 1 → P.Piece := fun p => Function.invFun P.map (κ p)
  have hL0 : ∀ p ∈ halfCollarSource, P.map (L0 p) = κ p :=
    fun p hp => Function.invFun_eq (hκrange p hp)
  let A : Set P.Piece := P.map ⁻¹' C.target
  have hAopen : IsOpen A := C.open_target.preimage P.continuous_map
  let Ψ : P.Piece → Torus × ℝ := fun q => C.invFun (P.map q)
  have hΨA : ∀ q ∈ A, Ψ q ∈ signedCollarSource ∧ 0 ≤ σ (Ψ q).2 ∧ C (Ψ q) = P.map q := by
    intro q hq
    have hmem : P.map q ∈ range P.map ∩ C.target := ⟨mem_range_self q, hq⟩
    rw [hrange] at hmem
    obtain ⟨p, ⟨hp, hps⟩, hpq⟩ := hmem
    have hΨp : Ψ q = p := by
      change C.invFun (P.map q) = p
      rw [← hpq]
      exact C.left_inv' (hCs ▸ hp)
    rw [hΨp]
    exact ⟨hp, (hside _).mp hps, hpq⟩
  let Ψ' : P.Piece → Torus × EuclideanHalfSpace 1 :=
    fun q => ((Ψ q).1, halfPoint (max (σ (Ψ q).2) 0) (le_max_right _ _))
  have hΨsm : ContMDiffOn (𝓡∂ 3) signedCollarModel ∞ Ψ A :=
    C.contMDiffOn_invFun.comp P.smooth.contMDiffOn (fun q hq => hq)
  have hΨ'sm : ContMDiffOn (𝓡∂ 3) halfCollarModel ∞ Ψ' A :=
    (contMDiff_fst.comp_contMDiffOn hΨsm).prodMk
      (contMDiffOn_halfPoint_max (hσsm.contMDiff.comp_contMDiffOn
        (contMDiff_snd.comp_contMDiffOn hΨsm)) (fun q hq => (hΨA q hq).2.1))
  let τ : Torus × EuclideanHalfSpace 1 → Torus × ℝ := fun p => (p.1, σ (p.2.val 0))
  have hτsm : ContMDiff halfCollarModel signedCollarModel ∞ τ := by
    refine contMDiff_fst.prodMk ?_
    have h1 : ContMDiff (𝓡∂ 1) 𝓘(ℝ, ℝ) ∞ (fun h : EuclideanHalfSpace 1 => h.val 0) :=
      (EuclideanSpace.proj (0 : Fin 1)).contDiff.contMDiff.comp
        (modelWithCornersEuclideanHalfSpace 1).contMDiff
    exact (hσsm.contMDiff.comp h1).comp contMDiff_snd
  have hτΨ' : ∀ q ∈ A, τ (Ψ' q) = Ψ q := by
    intro q hq
    change ((Ψ q).1, σ (max (σ (Ψ q).2) 0)) = Ψ q
    rw [max_eq_left (hΨA q hq).2.1, hσσ]
  have hbijΨ' : ∀ q ∈ A, Bijective (mfderiv (𝓡∂ 3) halfCollarModel Ψ' q) := by
    intro q hq
    have hev : (τ ∘ Ψ') =ᶠ[𝓝 q] Ψ := Filter.eventually_of_mem (hAopen.mem_nhds hq) hτΨ'
    have hΨ'd : MDifferentiableAt (𝓡∂ 3) halfCollarModel Ψ' q :=
      (hΨ'sm.contMDiffAt (hAopen.mem_nhds hq)).mdifferentiableAt (by simp)
    have hτd : MDifferentiableAt halfCollarModel signedCollarModel τ (Ψ' q) :=
      (hτsm _).mdifferentiableAt (by simp)
    have hH : HasMFDerivAt (𝓡∂ 3) signedCollarModel Ψ q
        ((mfderiv halfCollarModel signedCollarModel τ (Ψ' q)).comp
          (mfderiv (𝓡∂ 3) halfCollarModel Ψ' q)) :=
      (hτd.hasMFDerivAt.comp q hΨ'd.hasMFDerivAt).congr_of_eventuallyEq hev.symm
    have hcomp := hH.mfderiv
    have hCd : IsLocalDiffeomorphAt W.model signedCollarModel ∞ C.invFun (P.map q) :=
      C.symm.isLocalDiffeomorphAt W.model signedCollarModel ∞ hq
    have hmΨ : mfderiv (𝓡∂ 3) signedCollarModel Ψ q =
        (mfderiv W.model signedCollarModel C.invFun (P.map q)).comp
          (mfderiv (𝓡∂ 3) W.model P.map q) :=
      mfderiv_comp q (hCd.mdifferentiableAt (by simp)) (P.mdifferentiable_map q)
    have hb1 : Bijective (mfderiv W.model signedCollarModel C.invFun (P.map q)) :=
      (hCd.mfderivToContinuousLinearEquiv (by simp)).bijective
    have hbijΨ : Bijective (mfderiv (𝓡∂ 3) signedCollarModel Ψ q) := by
      rw [hmΨ, ContinuousLinearMap.coe_comp]
      exact hb1.comp (P.mfderiv_bijective q)
    rw [hcomp] at hbijΨ
    have hinj : Injective (mfderiv (𝓡∂ 3) halfCollarModel Ψ' q) := by
      intro v w hvw
      apply hbijΨ.1
      exact congrArg (mfderiv halfCollarModel signedCollarModel τ (Ψ' q)) hvw
    have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = Module.finrank ℝ
        ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) := by
      simp [Module.finrank_prod]
    exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ)
      (f := (mfderiv (𝓡∂ 3) halfCollarModel Ψ' q).toLinearMap) hdim).mp hinj⟩
  have hLA : ∀ p ∈ halfCollarSource, L0 p ∈ A := fun p hp => by
    change P.map (L0 p) ∈ C.target
    rw [hL0 p hp]
    exact C.map_source' (hκsrc p hp)
  have hΨ'src : ∀ q ∈ A, Ψ' q ∈ halfCollarSource := fun q hq => by
    change max (σ (Ψ q).2) 0 < 1
    rw [max_eq_left (hΨA q hq).2.1]
    exact hσlt _ (hΨA q hq).1.1 (hΨA q hq).1.2
  have hLΨ : ∀ q ∈ A, L0 (Ψ' q) = q := fun q hq => by
    apply P.injective
    rw [hL0 _ (hΨ'src q hq)]
    change C ((Ψ q).1, σ (max (σ (Ψ q).2) 0)) = P.map q
    rw [max_eq_left (hΨA q hq).2.1, hσσ]
    exact (hΨA q hq).2.2
  have hΨL : ∀ p ∈ halfCollarSource, Ψ' (L0 p) = p := fun p hp => by
    have h1 : Ψ (L0 p) = (p.1, σ (p.2.val 0)) := by
      change C.invFun (P.map (L0 p)) = _
      rw [hL0 p hp]
      exact C.left_inv' (hκsrc p hp)
    apply Prod.ext
    · change (Ψ (L0 p)).1 = p.1
      rw [h1]
    · apply Subtype.ext
      ext i
      fin_cases i
      change max (σ (Ψ (L0 p)).2) 0 = p.2.val 0
      rw [h1]
      change max (σ (σ (p.2.val 0))) 0 = p.2.val 0
      rw [hσσ]
      exact max_eq_left p.2.2
  have hL0c : ContinuousOn L0 halfCollarSource := by
    rw [P.isClosedEmbedding_map.isEmbedding.continuousOn_iff]
    have hκc : ContinuousOn κ halfCollarSource :=
      C.contMDiffOn_toFun.continuousOn.comp (continuous_fst.prodMk
        ((hσsm.continuous.comp ((EuclideanSpace.proj (0 : Fin 1)).continuous.comp
          continuous_subtype_val)).comp continuous_snd)).continuousOn hκsrc
    exact hκc.congr fun p hp => hL0 p hp
  have hL0sm : ContMDiffOn halfCollarModel (𝓡∂ 3) ∞ L0 halfCollarSource :=
    contMDiffOn_of_leftInverse_of_bijective_mfderiv hAopen GC.Seifert.isOpen_halfCollarSource' hΨ'sm hΨ'src
      hLA hΨL hLΨ hL0c hbijΨ'
  let L : PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) P.Piece ∞ :=
    { toFun := L0
      invFun := Ψ'
      source := halfCollarSource
      target := A
      map_source' := hLA
      map_target' := hΨ'src
      left_inv' := hΨL
      right_inv' := hLΨ
      open_source := GC.Seifert.isOpen_halfCollarSource'
      open_target := hAopen
      contMDiffOn_toFun := hL0sm
      contMDiffOn_invFun := hΨ'sm }
  refine ⟨L, rfl, rfl, fun t => ?_, fun t s hs hs1 => ?_⟩
  · have hmem : (t, halfZero) ∈ L.source := by
      change (0 : ℝ) < 1
      norm_num
    exact ((L.isLocalDiffeomorphAt halfCollarModel (𝓡∂ 3) ∞ hmem).isBoundaryPoint_iff (by simp)).mp
      (halfCollar_isBoundaryPoint_halfZero t)
  · change P.map (L0 (t, halfPoint s hs)) = _
    rw [hL0 _ hs1]
    rfl

/-- **B2-side. V2 (review item 5, D7; design erratum E1/F2, lane ASM-B2).** The V1 statement
(any `PieceFold`, `hloc` at points over the collar) was vacuous: with `q := z t`, `hz0` and `hloc`
make `z t` a local-diffeomorphism point over an interior seam point, hence an interior point
(`IsLocalDiffeomorphAt.isInteriorPoint_iff`), contradicting `hzb`. V2 takes a `PieceEmbedding`
whose image meets the seam collar exactly in the closed side-`b` half collar; the lift is
`P.map⁻¹ ∘ collar` (a special case of the reviewer's "proper local diffeomorphism of degree one
onto the closed half collar"). Self-seams take their two half collars from L3's explicit interval
product. Statement text adopted verbatim from `AssemblyInterfacesV2.lean`. -/
theorem exists_halfCollar_of_torusSeam {W : CompactCarrier.{u}} (S : TorusSeam W)
    (P : PieceEmbedding W) (b : Bool)
    (hrange : range P.map ∩ S.collar.target =
      S.collar '' {p | p ∈ signedCollarSource ∧ (if b then p.2 ≤ 0 else 0 ≤ p.2)}) :
    ∃ L : PartialDiffeomorph halfCollarModel (𝓡∂ 3) (Torus × EuclideanHalfSpace 1) P.Piece ∞,
      L.source = halfCollarSource ∧
      ∀ t s (hs : 0 ≤ s), s < 1 →
        P.map (L (t, halfPoint s hs)) = S.collar (t, if b then -s else s) := by
  obtain ⟨L, hsrc, -, -, heq⟩ := exists_halfCollar_of_torusSeam_of_range S P b hrange
  exact ⟨L, hsrc, heq⟩

end HalfCollar

end GC.GraphManifold.Assembly
