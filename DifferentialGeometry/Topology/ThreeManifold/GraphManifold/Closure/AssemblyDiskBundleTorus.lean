import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyDiskSmale
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Topology.Manifold.AddCircle.Descent

/-!
# Chapter-14 assembly, D2S1 mapping-torus lemma (lane ASM-D2S1, group G2)

Frozen statement: `build-logs/scratch/ASM-D2S1/D2S1Inputs.lean` (`nonempty_solidTorus_diffeomorph_of_liftFlow`).
A compact-free form of "isotopic monodromies give diffeomorphic mapping tori" for disk bundles over
the circle. Inputs: a manifold `M` with boundary (model `𝓡∂ 3`), a smooth map `p : M → Circle`, a
jointly smooth flow `Φ` of diffeomorphisms lifting the rotation (`p (Φ t q) = exp(i t) · p q`; the
output shape of the frozen `exists_circleLiftFlow_of_boundary_submersion`), a smooth embedding
`fibre` of the closed disk onto `p⁻¹{1}`, and a flattened isotopy `K` (with jointly smooth inverses)
from the identity (`t < ε`) to a diffeomorphism `K t` with `Φ (2π) ∘ fibre ∘ K t = fibre` (`t > 1 − ε`),
i.e. to the inverse monodromy. Output: `M` is diffeomorphic to the standard solid torus.

The map is `(x, z) ↦ Φ (2π r) (fibre (K r x))` with `r = circleTurnAngle z ∈ [0, 1)` the angle of `z` in
turns; near the seam `r = 0 ≡ 1` it is `Φ (2π s) (fibre x)` for the continuous angle `s` (the
flattening identities). The inverse is `q ↦ ((K r)⁻¹ (fibre⁻¹ (Φ (−2π r) q)), p q)`, smooth through a
local smooth lift of the angle (`AddCircle.isLocalDiffeomorph_coe`) and the immersion criterion for
`fibre`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance diskChartsTorus_ASMD2S1 : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothTorus_ASMD2S1 : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

attribute [local instance] DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc
  DifferentialGeometry.Topology.Handle.closedCellIsManifold

local instance closedCellNonempty_ASMD2S1 : Nonempty (ClosedCell 2) := ⟨closedCellCenter 2⟩

/-! ## The angle of a point of the circle, in turns -/

theorem addCircle_diffeomorphCircle_coe (t : ℝ) :
    AddCircle.diffeomorphCircle (t : AddCircle (1 : ℝ)) = Circle.exp (2 * Real.pi * t) := by
  change AddCircle.homeomorphCircle one_ne_zero (t : AddCircle (1 : ℝ)) = _
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  congr 1
  ring

/-- The angle of `z` in turns, in `[0, 1)`. -/
def circleTurnAngle (z : Circle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 (AddCircle.diffeomorphCircle.symm z) : ℝ)

theorem circleTurnAngle_mem (z : Circle) : circleTurnAngle z ∈ Ico (0 : ℝ) 1 := by
  have h := (AddCircle.equivIco (1 : ℝ) 0 (AddCircle.diffeomorphCircle.symm z)).2
  simp only [zero_add] at h
  exact h

theorem exp_circleTurnAngle (z : Circle) : Circle.exp (2 * Real.pi * circleTurnAngle z) = z := by
  rw [← addCircle_diffeomorphCircle_coe]
  unfold circleTurnAngle
  rw [AddCircle.coe_equivIco]
  exact AddCircle.diffeomorphCircle.apply_symm_apply z

theorem circleTurnAngle_exp (t : ℝ) : circleTurnAngle (Circle.exp (2 * Real.pi * t)) = Int.fract t := by
  rw [← addCircle_diffeomorphCircle_coe]
  unfold circleTurnAngle
  rw [Diffeomorph.symm_apply_apply]
  have h := AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) t
  rw [div_one, mul_one] at h
  exact h

/-! ## Flow identities -/

theorem liftFlow_zero {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q)) (q : M) : Φ 0 q = q :=
  (Φ 0).injective (by
    change Φ 0 (Φ 0 q) = Φ 0 q
    rw [← hΦadd, add_zero])

theorem liftFlow_neg_apply {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q)) (t : ℝ) (q : M) : Φ (-t) (Φ t q) = q := by
  rw [← hΦadd, neg_add_cancel, liftFlow_zero hΦadd]

theorem liftFlow_apply_neg {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q)) (t : ℝ) (q : M) : Φ t (Φ (-t) q) = q := by
  rw [← hΦadd, add_neg_cancel, liftFlow_zero hΦadd]

/-- The seam identity of the turn map: past `1 − ε` one full turn of the flow undoes `K`. -/
theorem liftFlow_turn_seam {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q)) {fibre : ClosedCell 2 → M}
    {K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)} {t : ℝ} {x : ClosedCell 2}
    (hseam : Φ (2 * Real.pi) (fibre (K t x)) = fibre x) :
    Φ (2 * Real.pi * t) (fibre (K t x)) = Φ (2 * Real.pi * (t - 1)) (fibre x) := by
  rw [show 2 * Real.pi * t = 2 * Real.pi * (t - 1) + 2 * Real.pi by ring, hΦadd, hseam]

/-- The turn map in the continuous parameter: near every `s₀` it is the unperiodized map shifted
by `⌊s₀⌋`. -/
theorem liftFlow_turn_local {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M] {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q)) {fibre : ClosedCell 2 → M}
    {K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)} {ε : ℝ} (hε : 0 < ε)
    (hlo : ∀ t x, t < ε → K t x = x)
    (hhi : ∀ t x, 1 - ε < t → Φ (2 * Real.pi) (fibre (K t x)) = fibre x) (s₀ : ℝ) :
    ∀ᶠ s in 𝓝 s₀, ∀ x, Φ (2 * Real.pi * Int.fract s) (fibre (K (Int.fract s) x)) =
      Φ (2 * Real.pi * (s - ⌊s₀⌋)) (fibre (K (s - ⌊s₀⌋) x)) := by
  set n : ℤ := ⌊s₀⌋ with hn
  have hδ : 0 < min ε 1 := lt_min hε one_pos
  have hmem : s₀ ∈ Ioo ((n : ℝ) - min ε 1) (n + 1) :=
    ⟨by linarith [Int.floor_le s₀], Int.lt_floor_add_one s₀⟩
  filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs x
  by_cases hns : (n : ℝ) ≤ s
  · have hfl : ⌊s⌋ = n := Int.floor_eq_iff.mpr ⟨hns, hs.2⟩
    rw [← Int.self_sub_floor, hfl]
  · replace hns := not_le.mp hns
    have hfl : ⌊s⌋ = n - 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith [hs.1, min_le_right ε 1]
    have hfr : Int.fract s = s - n + 1 := by
      rw [← Int.self_sub_floor, hfl]
      push_cast
      ring
    have hlt : s - n < ε := by linarith
    rw [hfr, hlo _ x hlt, liftFlow_turn_seam hΦadd (hhi _ x (by linarith [min_le_left ε 1, hs.1]))]
    ring_nf

/-! ## The turn map and its inverse -/

/-- The turn map `(x, z) ↦ Φ (2π r) (fibre (K r x))` with `r = circleTurnAngle z`. -/
def liftFlowTurnMap {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)) (fibre : ClosedCell 2 → M)
    (K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)) (q : ClosedCell 2 × Circle) : M :=
  Φ (2 * Real.pi * circleTurnAngle q.2) (fibre (K (circleTurnAngle q.2) q.1))

/-- The inverse of the turn map: `q ↦ ((K r)⁻¹ (fibre⁻¹ (Φ (−2π r) q)), p q)`, `r = circleTurnAngle (p q)`. -/
def liftFlowTurnInv {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 3) M]
    (Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)) (fibre : ClosedCell 2 → M)
    (K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)) (p : M → Circle) (q : M) :
    ClosedCell 2 × Circle :=
  ((K (circleTurnAngle (p q))).symm (invFun fibre (Φ (-(2 * Real.pi * circleTurnAngle (p q))) q)), p q)

theorem liftFlowTurnInv_turnMap {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] {p : M → Circle} {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q)) (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q)
    {fibre : ClosedCell 2 → M} (hinj : Injective fibre) (hrange : range fibre = p ⁻¹' {1})
    (K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)) (x : ClosedCell 2 × Circle) :
    liftFlowTurnInv Φ fibre K p (liftFlowTurnMap Φ fibre K x) = x := by
  obtain ⟨x, z⟩ := x
  have hp1 : p (fibre (K (circleTurnAngle z) x)) = 1 := by
    have h : fibre (K (circleTurnAngle z) x) ∈ p ⁻¹' {1} := hrange ▸ mem_range_self _
    exact h
  have hpz : p (liftFlowTurnMap Φ fibre K (x, z)) = z := by
    change p (Φ (2 * Real.pi * circleTurnAngle z) (fibre (K (circleTurnAngle z) x))) = z
    rw [hΦp, hp1, mul_one, exp_circleTurnAngle]
  refine Prod.ext ?_ hpz
  change (K (circleTurnAngle (p (liftFlowTurnMap Φ fibre K (x, z))))).symm
    (invFun fibre (Φ (-(2 * Real.pi * circleTurnAngle (p (liftFlowTurnMap Φ fibre K (x, z)))))
      (liftFlowTurnMap Φ fibre K (x, z)))) = x
  rw [hpz]
  change (K (circleTurnAngle z)).symm (invFun fibre (Φ (-(2 * Real.pi * circleTurnAngle z))
    (Φ (2 * Real.pi * circleTurnAngle z) (fibre (K (circleTurnAngle z) x))))) = x
  rw [liftFlow_neg_apply hΦadd, Function.leftInverse_invFun hinj, Diffeomorph.symm_apply_apply]

theorem liftFlowTurnMap_turnInv {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] {p : M → Circle} {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q)) (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q)
    {fibre : ClosedCell 2 → M} (hrange : range fibre = p ⁻¹' {1})
    (K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)) (q : M) :
    liftFlowTurnMap Φ fibre K (liftFlowTurnInv Φ fibre K p q) = q := by
  have hmem : Φ (-(2 * Real.pi * circleTurnAngle (p q))) q ∈ range fibre := by
    rw [hrange]
    change p (Φ (-(2 * Real.pi * circleTurnAngle (p q))) q) = 1
    rw [hΦp]
    calc Circle.exp (-(2 * Real.pi * circleTurnAngle (p q))) * p q
        = Circle.exp (-(2 * Real.pi * circleTurnAngle (p q))) *
            Circle.exp (2 * Real.pi * circleTurnAngle (p q)) := by rw [exp_circleTurnAngle]
      _ = 1 := by rw [← Circle.exp_add, neg_add_cancel, Circle.exp_zero]
  change Φ (2 * Real.pi * circleTurnAngle (p q)) (fibre (K (circleTurnAngle (p q))
    ((K (circleTurnAngle (p q))).symm (invFun fibre (Φ (-(2 * Real.pi * circleTurnAngle (p q))) q))))) = q
  rw [Diffeomorph.apply_symm_apply, Function.invFun_eq hmem, liftFlow_apply_neg hΦadd]

theorem contMDiff_liftFlowTurnMap {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q)) {fibre : ClosedCell 2 → M}
    (hfibre : ContMDiff (𝓡∂ 2) (𝓡∂ 3) ∞ fibre) {K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)}
    (hK : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => K x.2 x.1))
    {ε : ℝ} (hε : 0 < ε) (hlo : ∀ t x, t < ε → K t x = x)
    (hhi : ∀ t x, 1 - ε < t → Φ (2 * Real.pi) (fibre (K t x)) = fibre x) :
    ContMDiff ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3) ∞ (liftFlowTurnMap Φ fibre K) := by
  have hF₀ : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞
      (fun x : ClosedCell 2 × ℝ => Φ (2 * Real.pi * x.2) (fibre (K x.2 x.1))) :=
    hΦ.comp ((contMDiff_const.mul contMDiff_snd).prodMk (hfibre.comp hK))
  have hF : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞
      (fun x : ClosedCell 2 × ℝ =>
        Φ (2 * Real.pi * Int.fract x.2) (fibre (K (Int.fract x.2) x.1))) := by
    intro y₀
    have hshift : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞
        (fun x : ClosedCell 2 × ℝ =>
          Φ (2 * Real.pi * (x.2 - ⌊y₀.2⌋)) (fibre (K (x.2 - ⌊y₀.2⌋) x.1))) :=
      hF₀.comp (contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const))
    apply (hshift y₀).congr_of_eventuallyEq
    have h := liftFlow_turn_local hΦadd hε hlo hhi y₀.2
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds h] with y hy
    exact hy y.1
  have hG' : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 3) ∞
      (fun x : ClosedCell 2 × AddCircle (1 : ℝ) =>
        liftFlowTurnMap Φ fibre K (x.1, AddCircle.diffeomorphCircle x.2)) := by
    have h := AddCircle.contMDiffOn_of_comp_coe (I := 𝓡∂ 2) (J := 𝓡∂ 3)
      (U := (univ : Set (ClosedCell 2)))
      (f := fun x : ClosedCell 2 × AddCircle (1 : ℝ) =>
        liftFlowTurnMap Φ fibre K (x.1, AddCircle.diffeomorphCircle x.2)) (by
        refine ContMDiff.contMDiffOn ?_
        convert hF using 2 with y
        simp only [liftFlowTurnMap, addCircle_diffeomorphCircle_coe, circleTurnAngle_exp])
    rw [univ_prod_univ] at h
    exact contMDiffOn_univ.mp h
  have hsymm : ContMDiff ((𝓡∂ 2).prod (𝓡 1)) ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun q : ClosedCell 2 × Circle => (q.1, AddCircle.diffeomorphCircle.symm q.2)) :=
    contMDiff_fst.prodMk (AddCircle.diffeomorphCircle.symm.contMDiff.comp contMDiff_snd)
  convert hG'.comp hsymm using 1
  funext q
  simp only [Function.comp_apply, Diffeomorph.apply_symm_apply]

theorem contMDiff_liftFlowTurnInv {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] {p : M → Circle}
    (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p) {Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M)}
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q)) (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q)
    {fibre : ClosedCell 2 → M} (hfibre : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ fibre)
    (hrange : range fibre = p ⁻¹' {1}) {K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2)}
    (hKi : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
      (fun x : ClosedCell 2 × ℝ => (K x.2).symm x.1))
    {ε : ℝ} (hε : 0 < ε) (hlo : ∀ t x, t < ε → K t x = x)
    (hhi : ∀ t x, 1 - ε < t → Φ (2 * Real.pi) (fibre (K t x)) = fibre x) :
    ContMDiff (𝓡∂ 3) ((𝓡∂ 2).prod (𝓡 1)) ∞ (liftFlowTurnInv Φ fibre K p) := by
  intro q₀
  refine ContMDiffAt.prodMk ?_ (hp q₀)
  set r₀ := circleTurnAngle (p q₀) with hr₀
  have hloc := AddCircle.isLocalDiffeomorph_coe r₀
  let C := AddCircle.diffeomorphCircle
  let σ : M → ℝ := fun q => hloc.localInverse (C.symm (p q))
  have hz₀ : C.symm (p q₀) = (r₀ : AddCircle (1 : ℝ)) := by
    rw [hr₀]
    unfold circleTurnAngle
    rw [AddCircle.coe_equivIco]
  have hσ₀ : σ q₀ = r₀ := by
    change hloc.localInverse (C.symm (p q₀)) = r₀
    rw [hz₀]
    exact hloc.localInverse_left_inv hloc.localInverse_mem_target
  have hCp : ContMDiff (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ (fun q => C.symm (p q)) := C.symm.contMDiff.comp hp
  have hσ : ContMDiffAt (𝓡∂ 3) 𝓘(ℝ, ℝ) ∞ σ q₀ := by
    have h1 : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ hloc.localInverse (C.symm (p q₀)) := by
      rw [hz₀]
      exact hloc.contMDiffAt_localInverse
    exact h1.comp q₀ (hCp q₀)
  have hsrc : ∀ᶠ q in 𝓝 q₀, C.symm (p q) ∈ hloc.localInverse.source :=
    hCp.continuous.continuousAt.preimage_mem_nhds
      (hloc.localInverse_open_source.mem_nhds (by rw [hz₀]; exact hloc.localInverse_mem_source))
  have hpσ : ∀ᶠ q in 𝓝 q₀, p q = Circle.exp (2 * Real.pi * σ q) := by
    filter_upwards [hsrc] with q hq
    rw [← addCircle_diffeomorphCircle_coe]
    change p q = C (hloc.localInverse (C.symm (p q)) : AddCircle (1 : ℝ))
    rw [hloc.localInverse_right_inv hq]
    exact (C.apply_symm_apply (p q)).symm
  have hint : ∀ᶠ q in 𝓝 q₀, σ q ∈ Ioo (-(min ε 1)) 1 := by
    have hmem : σ q₀ ∈ Ioo (-(min ε 1)) 1 := by
      rw [hσ₀]
      exact ⟨lt_of_lt_of_le (neg_neg_of_pos (lt_min hε one_pos)) (circleTurnAngle_mem _).1,
        (circleTurnAngle_mem _).2⟩
    exact hσ.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds hmem)
  have hone : ∀ᶠ q in 𝓝 q₀, Φ (-(2 * Real.pi * σ q)) q ∈ range fibre := by
    filter_upwards [hpσ] with q hq
    rw [hrange]
    change p (Φ (-(2 * Real.pi * σ q)) q) = 1
    rw [hΦp, hq, ← Circle.exp_add, neg_add_cancel, Circle.exp_zero]
  let g : M → ClosedCell 2 := fun q => invFun fibre (Φ (-(2 * Real.pi * σ q)) q)
  have hpair : ContMDiffAt (𝓡∂ 3) (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) ∞
      (fun q => (-(2 * Real.pi * σ q), q)) q₀ :=
    ((contMDiffAt_const.mul hσ).neg).prodMk contMDiffAt_id
  have hΦσ : ContMDiffAt (𝓡∂ 3) (𝓡∂ 3) ∞ (fun q => Φ (-(2 * Real.pi * σ q)) q) q₀ :=
    ContMDiffAt.comp (g := fun x : ℝ × M => Φ x.1 x.2) q₀ (hΦ _) hpair
  have hfg : (fibre ∘ g) =ᶠ[𝓝 q₀] (fun q => Φ (-(2 * Real.pi * σ q)) q) := by
    filter_upwards [hone] with q hq
    exact Function.invFun_eq hq
  have hgc : ContinuousAt g q₀ :=
    hfibre.isEmbedding.isInducing.continuousAt_iff.mpr
      (hΦσ.continuousAt.congr hfg.symm)
  have hg : ContMDiffAt (𝓡∂ 3) (𝓡∂ 2) ∞ g q₀ :=
    (ContMDiffAt.iff_comp_isImmersionAt (hfibre.isImmersion.isImmersionAt (g q₀))).mpr
      ⟨hgc, hΦσ.congr_of_eventuallyEq hfg⟩
  have hloc' : ContMDiffAt (𝓡∂ 3) (𝓡∂ 2) ∞ (fun q => (K (σ q)).symm (g q)) q₀ :=
    (hKi (g q₀, σ q₀)).comp q₀ (hg.prodMk hσ)
  apply hloc'.congr_of_eventuallyEq
  filter_upwards [hpσ, hint, hone] with q hq hqi hqo
  change (K (circleTurnAngle (p q))).symm (invFun fibre (Φ (-(2 * Real.pi * circleTurnAngle (p q))) q)) =
    (K (σ q)).symm (g q)
  rw [hq, circleTurnAngle_exp]
  by_cases h0 : 0 ≤ σ q
  · rw [Int.fract_eq_self.mpr ⟨h0, hqi.2⟩]
  · replace h0 := not_le.mp h0
    have hfr : Int.fract (σ q) = σ q + 1 := by
      rw [← Int.self_sub_floor]
      have hfl : ⌊σ q⌋ = -1 := by
        rw [Int.floor_eq_iff]
        push_cast
        constructor <;> linarith [hqi.1, min_le_right ε 1]
      rw [hfl]
      push_cast
      ring
    have hKσ : (K (σ q)).symm (g q) = g q := by
      apply (K (σ q)).injective
      change K (σ q) ((K (σ q)).symm (g q)) = K (σ q) (g q)
      rw [Diffeomorph.apply_symm_apply, hlo _ _ (by linarith)]
    rw [hKσ, hfr]
    have hgy : fibre (g q) = Φ (-(2 * Real.pi * σ q)) q := Function.invFun_eq hqo
    have hseam := hhi (σ q + 1) (g q) (by linarith [hqi.1, min_le_left ε 1])
    have hfK : fibre (K (σ q + 1) (g q)) = Φ (-(2 * Real.pi * (σ q + 1))) q := by
      rw [← liftFlow_neg_apply hΦadd (2 * Real.pi) (fibre (K (σ q + 1) (g q))), hseam, hgy,
        ← hΦadd]
      congr 2
      ring
    apply (K (σ q + 1)).injective
    change K (σ q + 1) ((K (σ q + 1)).symm
      (invFun fibre (Φ (-(2 * Real.pi * (σ q + 1))) q))) = K (σ q + 1) (g q)
    rw [Diffeomorph.apply_symm_apply, ← hfK, Function.leftInverse_invFun hfibre.isEmbedding.injective]

/-! ## The closed disk as the unit disc of the solid torus model -/

/-- `ClosedCell 2 ≃ UnitDisc` through the isometry `ℝ² ≃ ℂ`. -/
def closedCellUnitDiscDiffeomorph : ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ UnitDisc.{u} where
  toFun x := ULift.up ⟨Complex.orthonormalBasisOneI.repr.symm x.val, by
    change ‖Complex.orthonormalBasisOneI.repr.symm x.val‖ ^ 2 ≤ 1
    rw [LinearIsometryEquiv.norm_map]
    have h := x.2
    nlinarith [norm_nonneg x.val]⟩
  invFun w := ⟨Complex.orthonormalBasisOneI.repr w.down.val, by
    rw [LinearIsometryEquiv.norm_map]
    have h : ‖w.down.val‖ ^ 2 ≤ 1 := w.down.2
    nlinarith [norm_nonneg w.down.val]⟩
  left_inv x := Subtype.ext (LinearIsometryEquiv.apply_symm_apply _ _)
  right_inv w := by
    apply ULift.ext
    apply Subtype.ext
    exact LinearIsometryEquiv.symm_apply_apply _ _
  contMDiff_toFun := by
    have hval : ContMDiff (𝓡∂ 2) (𝓡 2) ∞
        (Subtype.val : ClosedCell 2 → EuclideanSpace ℝ (Fin 2)) :=
      (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 1).contMDiff
    have h : ContMDiff (𝓡∂ 2) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 =>
        (⟨Complex.orthonormalBasisOneI.repr.symm x.val, by
          change ‖Complex.orthonormalBasisOneI.repr.symm x.val‖ ^ 2 ≤ 1
          rw [LinearIsometryEquiv.norm_map]
          have h := x.2
          nlinarith [norm_nonneg x.val]⟩ : unitDiscSet)) :=
      (unitDiscAtlas.contMDiff_iff_subtype_val _).mpr
        (Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp hval)
    exact (uliftDiffeomorph (𝓡∂ 2) unitDiscSet).contMDiff.comp h
  contMDiff_invFun := by
    refine (ContMDiff.iff_comp_isImmersion
      (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 1).isImmersion).mpr
      ⟨?_, ?_⟩
    · exact (Complex.orthonormalBasisOneI.repr.continuous.comp
        (contMDiff_disc_val.{u}.continuous)).subtype_mk _
    · exact Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff.contMDiff.comp
        contMDiff_disc_val.{u}

/-! ## G2 -/

/-- **G2: the mapping-torus lemma.** A lift flow of the rotation, a fibre disk over `1` and a
flattened isotopy from the identity to the inverse monodromy identify the total space with the
standard solid torus. Strengthening of the frozen text (`D2S1Inputs.lean`): the instance
`[IsManifold (𝓡∂ 3) ∞ M]` is not needed and is dropped; the verbatim form is the `example` below. -/
theorem nonempty_solidTorus_diffeomorph_of_liftFlow {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M]
    (p : M → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
    (Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M))
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q)
    (fibre : ClosedCell 2 → M) (hfibre : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ fibre)
    (hrange : range fibre = p ⁻¹' {1})
    (K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2))
    (hK : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => K x.2 x.1))
    (hKi : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
      (fun x : ClosedCell 2 × ℝ => (K x.2).symm x.1))
    {ε : ℝ} (hε : 0 < ε) (hlo : ∀ t x, t < ε → K t x = x)
    (hhi : ∀ t x, 1 - ε < t → Φ (2 * Real.pi) (fibre (K t x)) = fibre x) :
    Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯ M) := by
  let T : (ClosedCell 2 × Circle) ≃ₘ⟮(𝓡∂ 2).prod (𝓡 1), 𝓡∂ 3⟯ M :=
    { toFun := liftFlowTurnMap Φ fibre K
      invFun := liftFlowTurnInv Φ fibre K p
      left_inv := liftFlowTurnInv_turnMap hΦadd hΦp hfibre.isEmbedding.injective hrange K
      right_inv := liftFlowTurnMap_turnInv hΦadd hΦp hrange K
      contMDiff_toFun := contMDiff_liftFlowTurnMap hΦ hΦadd hfibre.contMDiff hK hε hlo hhi
      contMDiff_invFun := contMDiff_liftFlowTurnInv hp hΦ hΦadd hΦp hfibre hrange hKi hε hlo hhi }
  exact ⟨(solidTorusDiscCircle.{u}.trans
    ((closedCellUnitDiscDiffeomorph.{u}.symm).prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))).trans T⟩

/-- The frozen G2 text verbatim (with the unused `[IsManifold (𝓡∂ 3) ∞ M]`). -/
example {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 3) M] [IsManifold (𝓡∂ 3) ∞ M]
    (p : M → Circle) (hp : ContMDiff (𝓡∂ 3) (𝓡 1) ∞ p)
    (Φ : ℝ → (M ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ M))
    (hΦ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡∂ 3)) (𝓡∂ 3) ∞ (fun x : ℝ × M => Φ x.1 x.2))
    (hΦadd : ∀ s t q, Φ (s + t) q = Φ s (Φ t q))
    (hΦp : ∀ t q, p (Φ t q) = Circle.exp t * p q)
    (fibre : ClosedCell 2 → M) (hfibre : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ 3) ∞ fibre)
    (hrange : range fibre = p ⁻¹' {1})
    (K : ℝ → (ClosedCell 2 ≃ₘ⟮𝓡∂ 2, 𝓡∂ 2⟯ ClosedCell 2))
    (hK : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞ (fun x : ClosedCell 2 × ℝ => K x.2 x.1))
    (hKi : ContMDiff ((𝓡∂ 2).prod 𝓘(ℝ, ℝ)) (𝓡∂ 2) ∞
      (fun x : ClosedCell 2 × ℝ => (K x.2).symm x.1))
    {ε : ℝ} (hε : 0 < ε) (hlo : ∀ t x, t < ε → K t x = x)
    (hhi : ∀ t x, 1 - ε < t → Φ (2 * Real.pi) (fibre (K t x)) = fibre x) :
    Nonempty (solidTorusCarrier.{u}.Carrier ≃ₘ⟮solidTorusCarrier.{u}.model, 𝓡∂ 3⟯ M) :=
  nonempty_solidTorus_diffeomorph_of_liftFlow p hp Φ hΦ hΦadd hΦp fibre hfibre hrange K hK hKi hε
    hlo hhi

end GC.GraphManifold.Assembly
