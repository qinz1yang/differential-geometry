import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.InnerCollarSublevel

/-!
# Two torus collars glued along their common level: the torus product (F-e, row E7)

Row E7 (sheet item C5; the product alternative of BCP03, blueprint 207B:8411–8432): a compact
carrier whose boundary consists of two cusp-collar components, and which is swept by ONE regular
smooth function from the first component to the second, is smoothly `T² × [a, b]`, with the two
external boundary labels kept. The blueprint's "absorb the inner boundary diffeomorphism into the
base coordinate of one collar" is replaced by the one-function route (no collar matching).

* `exists_regular_blend` (any manifold, boundary allowed): two smooth functions `g₁`, `g₂`,
  regular on `{g₁ < c₁}` and `{g₁ > c₂}` respectively, and on the transition band
  `{c₁ ≤ g₁ ≤ c₂}` ordered (`g₁ ≤ g₂`) and increasing along a common vector, glue to the regular
  smooth function `g₂ + χ(g₁)(g₁ − g₂)` (`χ` the inner-collar cutoff, `1` below `c₁`, `0` above
  `c₂`), equal to `g₁` below `c₁` and to `g₂` above `c₂`.
* `exists_diffeomorph_Icc_of_boundary_param` (kernel): a compact manifold with boundary carrying
  a regular smooth `u` with `u = a` on the image of an injective immersion `j : T → M` of a compact
  boundaryless `T`, `u = b` on a set `Y`, and `∂M ⊆ range j ∪ Y`, is `T × [a, b]`, carrying the
  second coordinate to `u`, `T × {a}` onto `range j` and `T × {b}` onto `Y`.
* `CuspEmbedding.exists_diffeomorph_torus_Icc_of_regular` (carrier form, `T = T²`, `j = e(·, 0)`).
* `CuspEmbedding.exists_diffeomorph_torus_Icc_of_two_collars` (E7): from two smooth functions
  `F_i`, `F_j` on `W` (the inner-collar functions of the two components, row E6 shape: `F = a` on
  the component, regular on a sublevel) with the transition hypotheses on `{c₁ ≤ F_i ≤ c₂}`.
  These hypotheses are what the BCP03 overlap argument proves; they are explicit, not a new Prop.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

section Blend

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- **Gluing of two regular functions along a transition band.** -/
theorem exists_regular_blend {g₁ g₂ : M → ℝ} {c₁ c₂ : ℝ} (hc : c₁ < c₂)
    (hg₁ : ContMDiff I 𝓘(ℝ, ℝ) ∞ g₁) (hg₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ g₂)
    (hreg₁ : ∀ x, g₁ x < c₁ → mfderiv I 𝓘(ℝ, ℝ) g₁ x ≠ 0)
    (hreg₂ : ∀ x, c₂ < g₁ x → mfderiv I 𝓘(ℝ, ℝ) g₂ x ≠ 0)
    (hle : ∀ x, c₁ ≤ g₁ x → g₁ x ≤ c₂ → g₁ x ≤ g₂ x)
    (htr : ∀ x, c₁ ≤ g₁ x → g₁ x ≤ c₂ → ∃ v : TangentSpace I x,
      0 < (show ℝ from mfderiv I 𝓘(ℝ, ℝ) g₁ x v) ∧
        0 < (show ℝ from mfderiv I 𝓘(ℝ, ℝ) g₂ x v)) :
    ∃ v : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ v ∧ (∀ x, mfderiv I 𝓘(ℝ, ℝ) v x ≠ 0) ∧
      (∀ x, g₁ x ≤ c₁ → v x = g₁ x) ∧ ∀ x, c₂ ≤ g₁ x → v x = g₂ x := by
  set χ : ℝ → ℝ := innerCollarCutoff c₁ c₂ with hχ
  have hχs : ContDiff ℝ ∞ χ := contDiff_innerCollarCutoff c₁ c₂
  refine ⟨fun y => g₂ y + χ (g₁ y) * (g₁ y - 0 - g₂ y), ?_, ?_, ?_, ?_⟩
  · exact hg₂.add ((hχs.contMDiff.comp hg₁).mul ((hg₁.sub contMDiff_const).sub hg₂))
  · intro x h0
    rcases lt_or_ge (g₁ x) c₁ with hx | hx
    · have hloc : (fun y => g₂ y + χ (g₁ y) * (g₁ y - 0 - g₂ y)) =ᶠ[𝓝 x] g₁ := by
        filter_upwards [(isOpen_lt hg₁.continuous continuous_const).mem_nhds hx] with y hy
        rw [hχ, innerCollarCutoff_of_le hc (le_of_lt hy)]
        ring
      rw [hloc.mfderiv_eq] at h0
      exact hreg₁ x hx h0
    rcases lt_or_ge c₂ (g₁ x) with hx' | hx'
    · have hloc : (fun y => g₂ y + χ (g₁ y) * (g₁ y - 0 - g₂ y)) =ᶠ[𝓝 x] g₂ := by
        filter_upwards [(isOpen_lt continuous_const hg₁.continuous).mem_nhds hx'] with y hy
        rw [hχ, innerCollarCutoff_of_ge hc (le_of_lt hy)]
        ring
      rw [hloc.mfderiv_eq] at h0
      exact hreg₂ x hx' h0
    obtain ⟨w, hw₁, hw₂⟩ := htr x hx hx'
    have hpos := mfderiv_cutoffBlend_pos (I := I) (h := g₂) (ρ := g₁) (φ := χ) (c := 0)
      (y := x) (v := w) ((hg₂ x).mdifferentiableAt (by simp))
      ((hg₁ x).mdifferentiableAt (by simp)) ((hχs.differentiable (by simp)).differentiableAt)
      (innerCollarCutoff_mem _ _ _).1 (innerCollarCutoff_mem _ _ _).2
      ((antitone_innerCollarCutoff hc).deriv_nonpos) (by linarith [hle x hx hx']) hw₂ hw₁
    rw [h0] at hpos
    exact lt_irrefl _ hpos
  · intro x hx
    change g₂ x + χ (g₁ x) * (g₁ x - 0 - g₂ x) = g₁ x
    rw [hχ, innerCollarCutoff_of_le hc hx]
    ring
  · intro x hx
    change g₂ x + χ (g₁ x) * (g₁ x - 0 - g₂ x) = g₂ x
    rw [hχ, innerCollarCutoff_of_ge hc hx]
    ring

end Blend

section Kernel

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Boundary

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (m + 1)) M]

omit [ChartedSpace (EuclideanHalfSpace (m + 1)) M] in
private theorem twoCollar_contMDiff_opens_iff {E' H' X : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace X]
    [ChartedSpace H' X] {E'' H'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace H'' Y] {U : TopologicalSpace.Opens Y} {n : ℕ∞ω} {g : X → U} :
    ContMDiff I' I'' n (Subtype.val ∘ g) ↔ ContMDiff I' I'' n g :=
  forall_congr' fun x => ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff (U := U) g univ x

variable [IsManifold (𝓡∂ (m + 1)) ∞ M]
variable {F G T : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  [TopologicalSpace T] [ChartedSpace G T] [IsManifold J ∞ T]

/-- **E7 kernel.** A compact manifold with boundary swept by a regular smooth `u` from the image
of an injective immersion `j` (level `a`) to a set `Y` (level `b`), with `∂M ⊆ range j ∪ Y`, is
`T × [a, b]`: the second coordinate goes to `u`, `T × {a}` onto `range j`, `T × {b}` onto `Y`. -/
theorem exists_diffeomorph_Icc_of_boundary_param [T2Space M] [CompactSpace M]
    [Nonempty T] [CompactSpace T] [T2Space T] (hdim : Module.finrank ℝ F = m)
    {u : M → ℝ} {a b : ℝ} (hab : a < b) (hu : ContMDiff (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) ∞ u)
    (hreg : ∀ x, mfderiv (𝓡∂ (m + 1)) 𝓘(ℝ, ℝ) u x ≠ 0) {Y : Set M}
    (hYb : ∀ x ∈ Y, u x = b) (hY : Y.Nonempty)
    {k : ℕ} (hk : 1 ≤ k) {j : T → M} (hj : ContMDiff J (𝓡∂ (m + 1)) k j)
    (hjinj : Injective j) (hjd : ∀ t, Injective (mfderiv J (𝓡∂ (m + 1)) j t))
    (hjbd : ∀ t, (𝓡∂ (m + 1)).IsBoundaryPoint (j t)) (hja : ∀ t, u (j t) = a)
    (hbd : ∀ x, (𝓡∂ (m + 1)).IsBoundaryPoint x → x ∈ range j ∨ x ∈ Y) :
    haveI : Fact (a < b) := ⟨hab⟩
    ∃ D : Diffeomorph (J.prod (𝓡∂ 1)) (𝓡∂ (m + 1)) (T × Icc a b) M ∞,
      (∀ p, u (D p) = p.2.1) ∧ (∀ p, D p ∈ range j ↔ p.2.1 = a) ∧
        ∀ p, D p ∈ Y ↔ p.2.1 = b := by
  classical
  have : Fact (a < b) := ⟨hab⟩
  have hboundary : ∀ x, (𝓡∂ (m + 1)).IsBoundaryPoint x → u x = a ∨ u x = b := by
    intro x hx
    rcases hbd x hx with ⟨t, rfl⟩ | hy
    · exact Or.inl (hja t)
    · exact Or.inr (hYb x hy)
  obtain ⟨t₀⟩ := (inferInstance : Nonempty T)
  obtain ⟨y₀, hy₀⟩ := hY
  obtain ⟨Θ, hΘu, -⟩ := DifferentialGeometry.Topology.Ehresmann.exists_boundary_interval_trivialization hab hu hreg hboundary
    ⟨j t₀, hja t₀⟩ ⟨y₀, hYb y₀ hy₀⟩
  let L := boundaryLevel u a b hab.ne hu.continuous hboundary
  let φ : T → L := fun t => ⟨⟨j t, hjbd t⟩, hja t⟩
  let ιL : L → M := fun y => y.1.1
  have hιL : ContMDiff (HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))) (𝓡∂ (m + 1)) ∞ ιL :=
    contMDiff_boundaryLevelInclusion u a b hab.ne hu.continuous hboundary
  have hφ : ContMDiff J (HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))) k φ := by
    rw [← twoCollar_contMDiff_opens_iff (U := L)]
    rw [DifferentialGeometry.Manifold.Boundary.contMDiff_boundary_iff
      (by exact_mod_cast le_top)]
    exact hj
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hk)
  have hφd : ∀ t, Injective
      (mfderiv J (HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))) φ t) := by
    intro t v w hvw
    apply hjd t
    have hcomp : mfderiv J (𝓡∂ (m + 1)) (ιL ∘ φ) t =
        (mfderiv (HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))) (𝓡∂ (m + 1)) ιL (φ t)).comp
          (mfderiv J (HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))) φ t) :=
      mfderiv_comp t ((hιL (φ t)).mdifferentiableAt (by simp))
        ((hφ t).mdifferentiableAt hk0)
    have hιφ : ιL ∘ φ = j := rfl
    rw [hιφ] at hcomp
    rw [hcomp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hvw]
  have hdimL : Module.finrank ℝ F =
      Module.finrank ℝ (HasSmoothBoundary.boundaryModelE (𝓡∂ (m + 1))) := by
    change Module.finrank ℝ F = Module.finrank ℝ (EuclideanSpace ℝ (Fin (m + 1 - 1)))
    rw [finrank_euclideanSpace, Fintype.card_fin, Nat.add_sub_cancel, hdim]
  have hφloc : IsLocalDiffeomorph J (HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))) k φ := by
    intro t
    obtain ⟨Ψ, htΨ, -, hφΨ, -, -⟩ :=
      DifferentialGeometry.Topology.Manifold.exists_finiteInteriorPatch hk isOpen_univ
        hφ.contMDiffOn (mem_univ t) BoundarylessManifold.isInteriorPoint
        BoundarylessManifold.isInteriorPoint hdimL (hφd t)
    exact ⟨Ψ, htΨ, hφΨ⟩
  have hφbij : Bijective φ := by
    refine ⟨fun t₁ t₂ h => hjinj (congrArg (fun y : L => y.1.1) h), fun y => ?_⟩
    have hya : u y.1.1 = a := y.2
    rcases hbd y.1.1 y.1.2 with ⟨t, ht⟩ | hy
    · exact ⟨t, Subtype.ext (Subtype.ext ht)⟩
    · exact absurd (hya.symm.trans (hYb _ hy)) hab.ne
  let d : T ≃ₘ^k⟮J, HasSmoothBoundary.boundaryModel (𝓡∂ (m + 1))⟯ L :=
    hφloc.diffeomorphOfBijective hφbij
  obtain ⟨d'⟩ := SmoothApproximation.nonempty_diffeomorph_of_diffeomorph k hk d
  let D := (d'.prodCongr (Diffeomorph.refl (𝓡∂ 1) (Icc a b) ∞)).trans Θ
  have hDu : ∀ p, u (D p) = p.2.1 := fun p => hΘu (d' p.1, p.2)
  have hDbd : ∀ p, (𝓡∂ (m + 1)).IsBoundaryPoint (D p) ↔ (p.2.1 = a ∨ p.2.1 = b) := by
    intro p
    rw [← (D.isLocalDiffeomorph p).isBoundaryPoint_iff (by decide)]
    change p ∈ (J.prod (𝓡∂ 1)).boundary (T × Icc a b) ↔ _
    rw [J.boundary_of_boundaryless_left, boundary_Icc]
    constructor
    · rintro ⟨-, h | h⟩
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val (show p.2 = _ from h))
    · rintro (h | h)
      · exact ⟨mem_univ _, Or.inl (Subtype.ext h)⟩
      · exact ⟨mem_univ _, Or.inr (Subtype.ext h)⟩
  refine ⟨D, hDu, fun p => ?_, fun p => ?_⟩
  · constructor
    · rintro ⟨t, ht⟩
      rw [← hDu p, ← ht]
      exact hja t
    · intro hp
      rcases hbd (D p) ((hDbd p).mpr (Or.inl hp)) with h | h
      · exact h
      · exact absurd (hp.symm.trans ((hDu p).symm.trans (hYb _ h))) hab.ne
  · constructor
    · intro h
      rw [← hDu p]
      exact hYb _ h
    · intro hp
      rcases hbd (D p) ((hDbd p).mpr (Or.inr hp)) with ⟨t, ht⟩ | h
      · exact absurd ((hja t).symm.trans ((congrArg u ht).trans ((hDu p).trans hp))) hab.ne
      · exact h

end Kernel

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}

/-- **E7, carrier form.** A carrier swept by a regular smooth `u` from the cusp-collar boundary
component `X` (level `a`) to a set `Y` (level `b`), with `∂W ⊆ X ∪ Y`, is `T² × [a, b]`, the
labels kept: `T² × {a}` onto `X` and `T² × {b}` onto `Y`. -/
theorem CuspEmbedding.exists_diffeomorph_torus_Icc_of_regular {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {Y : Set W.Carrier} {u : W.Carrier → ℝ} {a b : ℝ}
    (hab : a < b) (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u)
    (hreg : ∀ x, mfderiv W.model 𝓘(ℝ, ℝ) u x ≠ 0) (hXa : ∀ x ∈ X, u x = a)
    (hYb : ∀ x ∈ Y, u x = b) (hbd : ∀ x, W.model.IsBoundaryPoint x → x ∈ X ∨ x ∈ Y)
    (hY : Y.Nonempty) :
    haveI : Fact (a < b) := ⟨hab⟩
    ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc a b) W.Carrier ∞,
      (∀ p, u (D p) = p.2.1) ∧ (∀ p, D p ∈ X ↔ p.2.1 = a) ∧ ∀ p, D p ∈ Y ↔ p.2.1 = b := by
  obtain ⟨hj, hjinj, hjd, hjbd⟩ := e.boundary_param
  have hmem : ∀ x, x ∈ range (fun t : Torus => e.toFun (t, halfZero)) ↔ x ∈ X :=
    fun x => Set.ext_iff.mp e.boundary_image x
  have hja : ∀ t : Torus, u (e.toFun (t, halfZero)) = a := fun t =>
    hXa _ ((hmem _).mp (mem_range_self t))
  have hbd' : ∀ x, W.model.IsBoundaryPoint x →
      x ∈ range (fun t : Torus => e.toFun (t, halfZero)) ∨ x ∈ Y := fun x hx =>
    (hbd x hx).imp_left (hmem x).mpr
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) = 2 := by
    rw [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
  cases W with
  | mk k M orientation =>
    cases k with
    | closed =>
      obtain ⟨t₀⟩ := (inferInstance : Nonempty Torus)
      have hh := ModelWithCorners.Boundaryless.boundary_eq_empty (I := 𝓡 3) (M := M)
      have hb : e.toFun (t₀, halfZero) ∈ (𝓡 3).boundary M := hjbd t₀
      rw [hh] at hb
      exact hb.elim
    | withBoundary =>
      obtain ⟨D, hDu, hDX, hDY⟩ :=
        exists_diffeomorph_Icc_of_boundary_param (m := 2) (J := torusModel) (T := Torus) hdim
          hab hu hreg hYb hY (k := K + 1) (by omega) hj hjinj hjd hjbd hja hbd'
      exact ⟨D, hDu, fun p => (hmem _).symm.trans (hDX p), hDY⟩

/-- **E7 (two collars glued).** Let `X_i`, `X_j` be two cusp-collar boundary components with
`∂W ⊆ X_i ∪ X_j`, and `F_i`, `F_j` smooth on `W` with `F_i = a_i < c₁` on `X_i`, `c₂ ≤ F_i` and
`F_j = a_j` on `X_j`. If `F_i` is regular on `{F_i < c₁}`, `F_j` on `{F_i > c₂}`, and on the
transition band `{c₁ ≤ F_i ≤ c₂}` some vector raises `F_i` and lowers `F_j`, then `W` is
`T² × [a, b]`: a regular smooth `u` (equal to `F_i` below `c₁` and to `C − F_j` above `c₂`) is the
second coordinate, `T² × {a}` goes onto `X_i` and `T² × {b}` onto `X_j`. -/
theorem CuspEmbedding.exists_diffeomorph_torus_Icc_of_two_collars {Xi Xj : Set W.Carrier}
    (ei : CuspEmbedding W g K δ Xi) (ej : CuspEmbedding W g K δ Xj)
    {Fi Fj : W.Carrier → ℝ} {ai aj c₁ c₂ : ℝ} (hc : c₁ < c₂)
    (hFi : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fi) (hFj : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fj)
    (hXi : ∀ x ∈ Xi, Fi x = ai) (hai : ai < c₁) (hXj : ∀ x ∈ Xj, Fj x = aj)
    (hXjc : ∀ x ∈ Xj, c₂ ≤ Fi x)
    (hbd : ∀ x, W.model.IsBoundaryPoint x → x ∈ Xi ∨ x ∈ Xj)
    (hregi : ∀ x, Fi x < c₁ → mfderiv W.model 𝓘(ℝ, ℝ) Fi x ≠ 0)
    (hregj : ∀ x, c₂ < Fi x → mfderiv W.model 𝓘(ℝ, ℝ) Fj x ≠ 0)
    (htr : ∀ x, c₁ ≤ Fi x → Fi x ≤ c₂ → ∃ v : TangentSpace W.model x,
      0 < (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) Fi x v) ∧
        (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) Fj x v) < 0) :
    ∃ (u : W.Carrier → ℝ) (C a b : ℝ) (hab : a < b), ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u ∧
      (∀ x, mfderiv W.model 𝓘(ℝ, ℝ) u x ≠ 0) ∧ (∀ x, Fi x ≤ c₁ → u x = Fi x) ∧
      (∀ x, c₂ ≤ Fi x → u x = C - Fj x) ∧
      haveI : Fact (a < b) := ⟨hab⟩
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc a b) W.Carrier ∞,
        (∀ p, u (D p) = p.2.1) ∧ (∀ p, D p ∈ Xi ↔ p.2.1 = a) ∧ ∀ p, D p ∈ Xj ↔ p.2.1 = b := by
  obtain ⟨t₀⟩ := (inferInstance : Nonempty Torus)
  have hx₀ : ej.toFun (t₀, halfZero) ∈ Xj := by
    have h : ej.toFun (t₀, halfZero) ∈ range (fun t : Torus => ej.toFun (t, halfZero)) :=
      mem_range_self t₀
    rwa [ej.boundary_image] at h
  have : Nonempty W.Carrier := ⟨ej.toFun (t₀, halfZero)⟩
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, ∀ x, Fj x ≤ M₀ := by
    obtain ⟨x₀, -, hx₀⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
      hFj.continuous.continuousOn
    exact ⟨Fj x₀, fun x => hx₀ (mem_univ x)⟩
  set C : ℝ := c₂ + M₀ with hC
  have hg₂ : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (fun x => C - Fj x) := contMDiff_const.sub hFj
  have hdg₂ : ∀ x (v : TangentSpace W.model x),
      (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) (fun x => C - Fj x) x v) =
        -(show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) Fj x v) := by
    intro x v
    set L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := mfderiv W.model 𝓘(ℝ, ℝ) Fj x with hL
    have h : HasMFDerivAt W.model 𝓘(ℝ, ℝ) (fun x => C - Fj x) x
        ((0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) - L) :=
      (hasMFDerivAt_const C x).sub ((hFj x).mdifferentiableAt (by simp)).hasMFDerivAt
    rw [h.mfderiv]
    change (0 - L) v = -L v
    exact zero_sub (L v)
  obtain ⟨u, hu, hureg, hu₁, hu₂⟩ := exists_regular_blend (I := W.model) (g₁ := Fi)
    (g₂ := fun x => C - Fj x) hc hFi hg₂ hregi
    (fun x hx h0 => hregj x hx (by
      refine ContinuousLinearMap.ext fun v => ?_
      have h1 := hdg₂ x v
      rw [h0] at h1
      change (0 : ℝ) = -(show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) Fj x v) at h1
      change (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) Fj x v) = 0
      linarith))
    (fun x _ hx => by linarith [hM₀ x])
    (fun x h1 h2 => by
      obtain ⟨v, hv₁, hv₂⟩ := htr x h1 h2
      refine ⟨v, hv₁, ?_⟩
      rw [hdg₂]
      linarith)
  have hab : ai < C - aj := by
    have h1 := hXj _ hx₀
    have h2 := hM₀ (ej.toFun (t₀, halfZero))
    linarith
  have huXi : ∀ x ∈ Xi, u x = ai := fun x hx => by
    rw [hu₁ x (by rw [hXi x hx]; exact hai.le), hXi x hx]
  have huXj : ∀ x ∈ Xj, u x = C - aj := fun x hx => by
    rw [hu₂ x (hXjc x hx), hXj x hx]
  exact ⟨u, C, ai, C - aj, hab, hu, hureg, hu₁, hu₂,
    ei.exists_diffeomorph_torus_Icc_of_regular hab hu hureg huXi huXj hbd ⟨_, hx₀⟩⟩

end DifferentialGeometry.Geometry.Collapse
