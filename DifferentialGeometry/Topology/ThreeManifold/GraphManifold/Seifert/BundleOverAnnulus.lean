import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.BundleOverDisc
import DifferentialGeometry.Topology.Manifold.AddCircle.Circle
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Product
import DifferentialGeometry.Analysis.Calculus.Inverse.InjectiveParameterizedInverse
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Ring.Periodic

/-!
# Circle bundles over an annulus

Chapter 6, lane RG01c: the annulus part of RG01 in the form fixed by external review 5
(`docs/geometrization/review/out/review-p1-elementarize-plan.md`, §2 and rows 2.2–2.4): one
monodromy, no `Diff⁺(S¹) ≃ SO(2)`, a cutoff in the straightening time, and the rotation winding
kept and absorbed by the second port. Everything here is unconditional.

(1) Straightening family (`AnnulusStraightening`). `cexp t = exp (2πit)` is a covering and a local
diffeomorphism `ℝ → S¹`; continuous maps from simply connected spaces lift, smooth maps lift
smoothly, and two lifts differ by one integer on a connected space. For a lift `F` of a circle map,
`straightenLift F t x = (1 - t) F x + t (x + F 0)` is the lift homotopy `H_t`; replacing `F` by
`F + n` shifts it by `n` (`straightenLift_add_const`), so `H_t` is independent of the lift mod `ℤ`.
The time is `cutoff s₁ s₂ r` (`0` for `r ≤ s₁`, `1` for `r ≥ s₂`, smooth) and the base point is
frozen by `freeze s₁ s₂ r` (`r` for `r ≤ s₁`, `s₂` for `r ≥ s₂`). For a fibre-preserving
diffeomorphism `Ψ₀` of `(S¹ × ℝ) × S¹` (the transition over the overlap annulus),
`exists_oriented_lift` lifts `Ψ₀` to `ℝ³`, shows the fibre derivative never vanishes and has one
sign, and separates a fixed reflection `z ↦ z ^ ε`, `ε = ±1`. `exists_straightening` returns a
fibre-preserving diffeomorphism `Ψ` with `Ψ = Ψ₀` for `r ≤ s₁`, `Ψ(θ, r, z) = σ(θ) z ^ ε` for
`r ≥ s₂`, `σ(θ)` the transition at `(θ, s₂)` evaluated at `1` (a rotation family whose winding is
not removed), and in between `Ψ` is `cexp ∘ H_{cutoff r}` of every lift of the frozen fibre map.
The parametrised inverse comes from `exists_contDiffOn_inverse_of_bijective` on the cover;
`fibreDiffeo` is each `H_t` as a circle diffeomorphism.

(2) Annulus with two charts. An `AnnulusChartPair F` is a cover of the base of `F` by an inner and
an outer open set with charts over the projection, coordinates `S¹ × ℝ ≃ inner ∩ outer`, an angle
on the outer set restricting to the first coordinate, and openness of the two ends
(`innerPart s`, `outerPart s`: the chart domain minus the far side of radius `s`). The transition
in coordinates is `transition`. With three charts (inner on `innerPart s₁`, the straightened chart
on the overlap, the rotated outer chart on `outerPart s₂`) all transitions are `1`
(`straightAtlas`), so `PrincipalAtlas.productOfCoboundary` gives `exists_product`: a product
`U ≃ base × S¹` over the projection equal to the inner chart on `innerPart s₁` and to
`σ(angle) · (outer chart) ^ ε` on `outerPart s₂`. No orientation input is needed: the overlap is
connected, so the transition has one fibre orientation and `ε` records it.

(3) Ports. `exists_product_ports` and `exists_product_portCollars`: for base collars `β₁` in
`innerPart s₁` and `β₂` in `outerPart s₂` with `angle ∘ β₂ = e ∘ fst`, the first port collar is
unchanged and the second becomes the product port after the torus reparametrisation
`ψ(s, f) = (s, (σ(e s)⁻¹ f) ^ ε)`, which fixes the base circle and carries the winding of
`σ ∘ e` (the shape `collar (ψ p.1, p.2) = Φ⁻¹ (β p, f)` asked by `Elementarize`).
-/

set_option autoImplicit false

noncomputable section
open Set
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace AnnulusStraightening

def cexp (t : ℝ) : Circle := AddCircle.diffeomorphCircle (t : AddCircle (1 : ℝ))

theorem cexp_eq (t : ℝ) : cexp t = Circle.exp (2 * Real.pi * t) := by
  change AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero (t : AddCircle (1 : ℝ)) = _
  rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  congr 1
  ring

theorem cexp_add (s t : ℝ) : cexp (s + t) = cexp s * cexp t := by
  rw [cexp_eq, cexp_eq, cexp_eq, mul_add, Circle.exp_add]

theorem cexp_zero : cexp 0 = 1 := by
  rw [cexp_eq, mul_zero, Circle.exp_zero]

theorem cexp_int (n : ℤ) : cexp n = 1 := by
  rw [cexp_eq, Circle.exp_two_pi_mul_int]

theorem cexp_neg (t : ℝ) : cexp (-t) = (cexp t)⁻¹ := by
  rw [cexp_eq, cexp_eq, mul_neg, Circle.exp_neg]

theorem cexp_add_int (t : ℝ) (n : ℤ) : cexp (t + n) = cexp t := by
  rw [cexp_add, cexp_int, mul_one]

theorem cexp_eq_cexp_iff {s t : ℝ} : cexp s = cexp t ↔ ∃ n : ℤ, s = t + n := by
  rw [cexp_eq, cexp_eq, Circle.exp_eq_exp]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have h2 : 2 * Real.pi * s = 2 * Real.pi * (t + m) := by rw [hm]; ring
    exact mul_left_cancel₀ hpi h2
  · rintro ⟨m, rfl⟩
    exact ⟨m, by ring⟩

theorem cexp_surjective : Function.Surjective cexp := by
  intro z
  obtain ⟨a, ha⟩ := AddCircle.diffeomorphCircle.surjective z
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective a
  exact ⟨t, ha⟩

theorem isLocalDiffeomorph_cexp : IsLocalDiffeomorph 𝓘(ℝ, ℝ) (𝓡 1) ∞ cexp :=
  DifferentialGeometry.isLocalDiffeomorph_comp AddCircle.diffeomorphCircle.isLocalDiffeomorph
    AddCircle.isLocalDiffeomorph_coe

theorem contMDiff_cexp : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ cexp :=
  isLocalDiffeomorph_cexp.contMDiff

theorem exists_continuous_cexp_lift {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A]
    [LocallyPathConnectedSpace A] {f : A → Circle} (hf : Continuous f) :
    ∃ F : A → ℝ, Continuous F ∧ ∀ a, cexp (F a) = f a := by
  obtain ⟨a₀⟩ := (inferInstance : Nonempty A)
  obtain ⟨e₀, he₀⟩ := QuotientAddGroup.mk_surjective (AddCircle.diffeomorphCircle.symm (f a₀))
  let g : C(A, AddCircle (1 : ℝ)) := ⟨fun a => AddCircle.diffeomorphCircle.symm (f a),
    AddCircle.diffeomorphCircle.symm.continuous.comp hf⟩
  obtain ⟨F, hF, -⟩ := (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts g
    a₀ e₀ he₀
  refine ⟨F, F.continuous, fun a => ?_⟩
  have h := congrFun hF.2 a
  change ((F a : ℝ) : AddCircle (1 : ℝ)) = AddCircle.diffeomorphCircle.symm (f a) at h
  change AddCircle.diffeomorphCircle ((F a : ℝ) : AddCircle (1 : ℝ)) = f a
  rw [h, Diffeomorph.apply_symm_apply]

theorem exists_contDiff_cexp_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → Circle} (hf : ContMDiff 𝓘(ℝ, E) (𝓡 1) ∞ f) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ ∀ a, cexp (F a) = f a := by
  obtain ⟨F, hFc, hF⟩ := exists_continuous_cexp_lift hf.continuous
  refine ⟨F, ?_, hF⟩
  have h : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ F :=
    isLocalDiffeomorph_cexp.contMDiff_of_continuous_of_comp hFc
      (hf.congr fun a => hF a) le_rfl
  exact contMDiff_iff_contDiff.mp h

theorem exists_int_of_cexp_eq {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {F F' : A → ℝ} (hF : Continuous F) (hF' : Continuous F')
    (h : ∀ a, cexp (F' a) = cexp (F a)) (a₀ : A) : ∃ n : ℤ, ∀ a, F' a = F a + n := by
  have hint (a : A) : ∃ n : ℤ, F' a - F a = n := by
    obtain ⟨n, hn⟩ := cexp_eq_cexp_iff.mp (h a)
    exact ⟨n, by rw [hn]; ring⟩
  obtain ⟨n, hn⟩ := hint a₀
  refine ⟨n, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hint a
  suffices hmn : m = n by
    rw [← hmn]
    linarith
  have hcont : ContinuousOn (fun a => F' a - F a) univ := (hF'.sub hF).continuousOn
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hle : (m : ℝ) + 1 ≤ n := by exact_mod_cast hlt
    have hmem : (m : ℝ) + 1 / 2 ∈ Icc (F' a - F a) (F' a₀ - F a₀) := by
      rw [hm, hn]
      constructor <;> linarith
    obtain ⟨c, -, hc⟩ := isPreconnected_univ.intermediate_value (mem_univ a) (mem_univ a₀)
      hcont hmem
    obtain ⟨k, hk⟩ := hint c
    change F' c - F c = _ at hc
    rw [hk] at hc
    have h1 : (k : ℝ) - m = 1 / 2 := by linarith
    have h2 : (k - m : ℤ) = (1 / 2 : ℝ) := by push_cast; linarith
    have h3 : (0 : ℝ) < ((k - m : ℤ) : ℝ) := by rw [h2]; norm_num
    have h4 : ((k - m : ℤ) : ℝ) < 1 := by rw [h2]; norm_num
    have h5 : (0 : ℤ) < k - m := by exact_mod_cast h3
    have h6 : k - m < (1 : ℤ) := by exact_mod_cast h4
    omega
  · have hle : (n : ℝ) + 1 ≤ m := by exact_mod_cast hlt
    have hmem : (n : ℝ) + 1 / 2 ∈ Icc (F' a₀ - F a₀) (F' a - F a) := by
      rw [hm, hn]
      constructor <;> linarith
    obtain ⟨c, -, hc⟩ := isPreconnected_univ.intermediate_value (mem_univ a₀) (mem_univ a)
      hcont hmem
    obtain ⟨k, hk⟩ := hint c
    change F' c - F c = _ at hc
    rw [hk] at hc
    have h2 : (k - n : ℤ) = (1 / 2 : ℝ) := by push_cast; linarith
    have h3 : (0 : ℝ) < ((k - n : ℤ) : ℝ) := by rw [h2]; norm_num
    have h4 : ((k - n : ℤ) : ℝ) < 1 := by rw [h2]; norm_num
    have h5 : (0 : ℤ) < k - n := by exact_mod_cast h3
    have h6 : k - n < (1 : ℤ) := by exact_mod_cast h4
    omega



def straightenLift (F : ℝ → ℝ) (t x : ℝ) : ℝ := (1 - t) * F x + t * (x + F 0)

theorem straightenLift_add_const (F : ℝ → ℝ) (c t x : ℝ) :
    straightenLift (fun y => F y + c) t x = straightenLift F t x + c := by
  unfold straightenLift
  ring

theorem straightenLift_zero (F : ℝ → ℝ) (x : ℝ) : straightenLift F 0 x = F x := by
  unfold straightenLift
  ring

theorem straightenLift_one (F : ℝ → ℝ) (x : ℝ) : straightenLift F 1 x = x + F 0 := by
  unfold straightenLift
  ring

theorem straightenLift_add_one {F : ℝ → ℝ} (hF : ∀ y, F (y + 1) = F y + 1) (t x : ℝ) :
    straightenLift F t (x + 1) = straightenLift F t x + 1 := by
  unfold straightenLift
  rw [hF]
  ring

def cutoff (s₁ s₂ r : ℝ) : ℝ := Real.smoothTransition ((r - s₁) / (s₂ - s₁))

def freeze (s₁ s₂ r : ℝ) : ℝ := (1 - cutoff s₁ s₂ r) * r + cutoff s₁ s₂ r * s₂

theorem cutoff_of_le {s₁ s₂ r : ℝ} (hs : s₁ < s₂) (hr : r ≤ s₁) : cutoff s₁ s₂ r = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by linarith))

theorem cutoff_of_ge {s₁ s₂ r : ℝ} (hs : s₁ < s₂) (hr : s₂ ≤ r) : cutoff s₁ s₂ r = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).mpr (by linarith))

theorem cutoff_nonneg (s₁ s₂ r : ℝ) : 0 ≤ cutoff s₁ s₂ r := Real.smoothTransition.nonneg _

theorem cutoff_le_one (s₁ s₂ r : ℝ) : cutoff s₁ s₂ r ≤ 1 := Real.smoothTransition.le_one _

theorem contDiff_cutoff (s₁ s₂ : ℝ) : ContDiff ℝ ∞ (cutoff s₁ s₂) :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp
    ((contDiff_id.sub contDiff_const).div_const _)

theorem contDiff_freeze (s₁ s₂ : ℝ) : ContDiff ℝ ∞ (freeze s₁ s₂) :=
  ((contDiff_const.sub (contDiff_cutoff s₁ s₂)).mul contDiff_id).add
    ((contDiff_cutoff s₁ s₂).mul contDiff_const)

theorem freeze_of_le {s₁ s₂ r : ℝ} (hs : s₁ < s₂) (hr : r ≤ s₁) : freeze s₁ s₂ r = r := by
  unfold freeze
  rw [cutoff_of_le hs hr]
  ring

theorem freeze_of_ge {s₁ s₂ r : ℝ} (hs : s₁ < s₂) (hr : s₂ ≤ r) : freeze s₁ s₂ r = s₂ := by
  unfold freeze
  rw [cutoff_of_ge hs hr]
  ring

def liftFamily (G : (ℝ × ℝ) × ℝ → ℝ) (s₁ s₂ : ℝ) (v : (ℝ × ℝ) × ℝ) : ℝ :=
  straightenLift (fun x => G ((v.1.1, freeze s₁ s₂ v.1.2), x)) (cutoff s₁ s₂ v.1.2) v.2

variable {G : (ℝ × ℝ) × ℝ → ℝ} {s₁ s₂ : ℝ}

theorem liftFamily_eq (v : (ℝ × ℝ) × ℝ) : liftFamily G s₁ s₂ v =
    (1 - cutoff s₁ s₂ v.1.2) * G ((v.1.1, freeze s₁ s₂ v.1.2), v.2) +
      cutoff s₁ s₂ v.1.2 * (v.2 + G ((v.1.1, freeze s₁ s₂ v.1.2), 0)) := rfl

theorem contDiff_liftFamily (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (liftFamily G s₁ s₂) := by
  have hr : ContDiff ℝ ∞ (fun v : (ℝ × ℝ) × ℝ => v.1.2) := contDiff_snd.comp contDiff_fst
  have hc : ContDiff ℝ ∞ (fun v : (ℝ × ℝ) × ℝ => cutoff s₁ s₂ v.1.2) :=
    (contDiff_cutoff s₁ s₂).comp hr
  have hq : ContDiff ℝ ∞ (fun v : (ℝ × ℝ) × ℝ => (v.1.1, freeze s₁ s₂ v.1.2)) :=
    (contDiff_fst.comp contDiff_fst).prodMk ((contDiff_freeze s₁ s₂).comp hr)
  have h1 : ContDiff ℝ ∞ (fun v : (ℝ × ℝ) × ℝ => G ((v.1.1, freeze s₁ s₂ v.1.2), v.2)) :=
    hG.comp (hq.prodMk contDiff_snd)
  have h0 : ContDiff ℝ ∞ (fun v : (ℝ × ℝ) × ℝ => G ((v.1.1, freeze s₁ s₂ v.1.2), 0)) :=
    hG.comp (hq.prodMk contDiff_const)
  exact ((contDiff_const.sub hc).mul h1).add (hc.mul (contDiff_snd.add h0))

theorem liftFamily_of_le (hs : s₁ < s₂) (v : (ℝ × ℝ) × ℝ) (hv : v.1.2 ≤ s₁) :
    liftFamily G s₁ s₂ v = G v := by
  rw [liftFamily_eq, cutoff_of_le hs hv, freeze_of_le hs hv]
  ring

theorem liftFamily_of_ge (hs : s₁ < s₂) (v : (ℝ × ℝ) × ℝ) (hv : s₂ ≤ v.1.2) :
    liftFamily G s₁ s₂ v = v.2 + G ((v.1.1, s₂), 0) := by
  rw [liftFamily_eq, cutoff_of_ge hs hv, freeze_of_ge hs hv]
  ring

theorem liftFamily_add_int (hper : ∀ p x, G (p, x + 1) = G (p, x) + 1) (p : ℝ × ℝ) (x : ℝ)
    (n : ℤ) : liftFamily G s₁ s₂ (p, x + n) = liftFamily G s₁ s₂ (p, x) + n := by
  have hP (q : ℝ × ℝ) : Function.Periodic (fun y => G (q, y) - y) 1 := by
    intro y
    simp only
    rw [hper]
    ring
  have hG (q : ℝ × ℝ) (y : ℝ) : G (q, y + n) = G (q, y) + n := by
    have h := (hP q).int_mul n y
    simp only [mul_one] at h
    linarith
  rw [liftFamily_eq, liftFamily_eq]
  simp only
  rw [hG]
  ring

theorem liftFamily_wind_int {w : ℤ} (hwind : ∀ θ r x, G ((θ + 1, r), x) = G ((θ, r), x) + w)
    (θ r x : ℝ) (n : ℤ) :
    liftFamily G s₁ s₂ ((θ + n, r), x) = liftFamily G s₁ s₂ ((θ, r), x) + n * w := by
  have hP (r' x' : ℝ) : Function.Periodic (fun y => G ((y, r'), x') - w * y) 1 := by
    intro y
    simp only
    rw [hwind]
    ring
  have hG (r' x' : ℝ) : G ((θ + n, r'), x') = G ((θ, r'), x') + n * w := by
    have h := (hP r' x').int_mul n θ
    simp only [mul_one] at h
    linarith
  rw [liftFamily_eq, liftFamily_eq]
  simp only
  rw [hG, hG]
  ring

theorem hasDerivAt_section {f : (ℝ × ℝ) × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) (x : ℝ) :
    HasDerivAt (fun y => f (p, y)) (fderiv ℝ f (p, x) (0, 1)) x := by
  have hd : DifferentiableAt ℝ f (p, x) := hf.differentiable (by simp) _
  have hs : HasDerivAt (fun y : ℝ => (p, y)) ((0 : ℝ × ℝ), (1 : ℝ)) x :=
    (hasDerivAt_const x p).prodMk (hasDerivAt_id x)
  exact hd.hasFDerivAt.comp_hasDerivAt x hs

theorem deriv_section {f : (ℝ × ℝ) × ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) (x : ℝ) :
    deriv (fun y => f (p, y)) x = fderiv ℝ f (p, x) (0, 1) :=
  (hasDerivAt_section hf p x).deriv

theorem deriv_liftFamily_pos (hG : ContDiff ℝ ∞ G)
    (hpos : ∀ p x, 0 < deriv (fun y => G (p, y)) x) (p : ℝ × ℝ) (x : ℝ) :
    0 < deriv (fun y => liftFamily G s₁ s₂ (p, y)) x := by
  set q : ℝ × ℝ := (p.1, freeze s₁ s₂ p.2)
  set t := cutoff s₁ s₂ p.2
  have hGd : HasDerivAt (fun y => G (q, y)) (deriv (fun y => G (q, y)) x) x :=
    ((hG.differentiable (by simp)).comp (differentiable_const q |>.prodMk
      differentiable_id)).differentiableAt.hasDerivAt
  have hd : HasDerivAt (fun y => liftFamily G s₁ s₂ (p, y))
      ((1 - t) * deriv (fun y => G (q, y)) x + t * (1 + 0)) x := by
    have h := (hGd.const_mul (1 - t)).add (((hasDerivAt_id x).add
      (hasDerivAt_const x (G (q, 0)))).const_mul t)
    exact h
  rw [hd.deriv]
  have ht0 : 0 ≤ t := cutoff_nonneg _ _ _
  have ht1 : t ≤ 1 := cutoff_le_one _ _ _
  have hq := hpos q x
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]
    linarith
  · nlinarith


theorem bijective_of_deriv_pos_of_add_int {f : ℝ → ℝ} (hpos : ∀ x, 0 < deriv f x)
    (hper : ∀ x (n : ℤ), f (x + n) = f x + n) : Function.Bijective f := by
  have hmono : StrictMono f := strictMono_of_deriv_pos hpos
  have hcont : Continuous f :=
    continuous_iff_continuousAt.mpr fun x =>
      (differentiableAt_of_deriv_ne_zero (hpos x).ne').continuousAt
  refine ⟨hmono.injective, fun y => ?_⟩
  obtain ⟨n, hn⟩ := exists_int_gt (|y - f 0|)
  have ha : f (0 + (-n : ℤ)) ≤ y := by
    rw [hper]
    push_cast
    have := neg_abs_le (y - f 0)
    linarith
  have hb : y ≤ f (0 + (n : ℤ)) := by
    rw [hper]
    have := le_abs_self (y - f 0)
    linarith
  have hle : (0 : ℝ) + (-n : ℤ) ≤ 0 + (n : ℤ) := by
    push_cast
    have : (0 : ℝ) ≤ n := le_trans (abs_nonneg _) hn.le
    linarith
  obtain ⟨c, -, hc⟩ := intermediate_value_Icc hle hcont.continuousOn ⟨ha, hb⟩
  exact ⟨c, hc⟩

theorem exists_liftFamily_inverse (hG : ContDiff ℝ ∞ G)
    (hper : ∀ p x, G (p, x + 1) = G (p, x) + 1)
    (hpos : ∀ p x, 0 < deriv (fun y => G (p, y)) x) :
    ∃ R : (ℝ × ℝ) × ℝ → ℝ, ContDiff ℝ ∞ R ∧
      (∀ p x, R (p, liftFamily G s₁ s₂ (p, x)) = x) ∧
      ∀ p y, liftFamily G s₁ s₂ (p, R (p, y)) = y := by
  have hH := contDiff_liftFamily (s₁ := s₁) (s₂ := s₂) hG
  obtain ⟨R, hR, h1, h2⟩ :=
    DifferentialGeometry.Analysis.exists_contDiffOn_inverse_of_bijective (E := ℝ × ℝ)
    (h := liftFamily G s₁ s₂) (V := univ) isOpen_univ hH.contDiffOn
    (by
      intro p hp
      exact bijective_of_deriv_pos_of_add_int (deriv_liftFamily_pos hG hpos p)
        (liftFamily_add_int hper p))
    (by
      intro p hp x
      rw [← deriv_section hH]
      exact (deriv_liftFamily_pos hG hpos p x).ne')
  refine ⟨R, ?_, fun p x => h1 p (mem_univ p) x, fun p y => h2 p (mem_univ p) y⟩
  rw [← contDiffOn_univ]
  simpa only [univ_prod_univ] using hR

abbrev coverModel := (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, ℝ)

abbrev fibreModel := ((𝓡 1).prod 𝓘(ℝ, ℝ)).prod (𝓡 1)

def coverMap (v : (ℝ × ℝ) × ℝ) : (Circle × ℝ) × Circle := ((cexp v.1.1, v.1.2), cexp v.2)

theorem isLocalDiffeomorph_coverMap : IsLocalDiffeomorph coverModel fibreModel ∞ coverMap :=
  (isLocalDiffeomorph_cexp.prodMap (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞).isLocalDiffeomorph).prodMap
    isLocalDiffeomorph_cexp

theorem coverMap_surjective : Function.Surjective coverMap := by
  rintro ⟨⟨θ, r⟩, z⟩
  obtain ⟨a, rfl⟩ := cexp_surjective θ
  obtain ⟨b, rfl⟩ := cexp_surjective z
  exact ⟨((a, r), b), rfl⟩

theorem contMDiff_of_comp_coverMap {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type*} [TopologicalSpace N]
    [ChartedSpace H' N] {f : (Circle × ℝ) × Circle → N}
    (h : ContMDiff coverModel J ∞ (f ∘ coverMap)) : ContMDiff fibreModel J ∞ f :=
  isLocalDiffeomorph_coverMap.contMDiff_of_comp_of_surjective coverMap_surjective h

theorem contMDiff_toCover :
    ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) coverModel ∞ (fun v : (ℝ × ℝ) × ℝ => v) :=
  ((contDiff_fst.comp contDiff_fst).contMDiff.prodMk
    (contDiff_snd.comp contDiff_fst).contMDiff).prodMk contDiff_snd.contMDiff

theorem contMDiff_ofCover :
    ContMDiff coverModel 𝓘(ℝ, (ℝ × ℝ) × ℝ) ∞ (fun v : (ℝ × ℝ) × ℝ => v) :=
  (contMDiff_fst.fst.prodMk_space contMDiff_fst.snd).prodMk_space contMDiff_snd

theorem contDiff_of_contMDiff_cover {F : (ℝ × ℝ) × ℝ → ℝ}
    (h : ContMDiff coverModel 𝓘(ℝ, ℝ) ∞ F) : ContDiff ℝ ∞ F :=
  contMDiff_iff_contDiff.mp (h.comp contMDiff_toCover)

theorem contMDiff_cover_of_contDiff {F : (ℝ × ℝ) × ℝ → ℝ} (h : ContDiff ℝ ∞ F) :
    ContMDiff coverModel 𝓘(ℝ, ℝ) ∞ F :=
  h.contMDiff.comp contMDiff_ofCover

theorem exists_cover_lift {f : (Circle × ℝ) × Circle → Circle}
    (hf : ContMDiff fibreModel (𝓡 1) ∞ f) :
    ∃ G : (ℝ × ℝ) × ℝ → ℝ, ContDiff ℝ ∞ G ∧ ∀ v, cexp (G v) = f (coverMap v) := by
  have h : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × ℝ) (𝓡 1) ∞ (fun v => f (coverMap v)) :=
    (hf.comp isLocalDiffeomorph_coverMap.contMDiff).comp contMDiff_toCover
  exact exists_contDiff_cexp_lift h

def rep (z : Circle) : ℝ := Function.surjInv cexp_surjective z

theorem cexp_rep (z : Circle) : cexp (rep z) = z := Function.surjInv_eq cexp_surjective z

theorem exists_rep_cexp (t : ℝ) : ∃ n : ℤ, rep (cexp t) = t + n :=
  cexp_eq_cexp_iff.mp (cexp_rep (cexp t))

section Straighten

variable {G : (ℝ × ℝ) × ℝ → ℝ} {s₁ s₂ : ℝ} {w : ℤ}

def straightenMap (G : (ℝ × ℝ) × ℝ → ℝ) (s₁ s₂ : ℝ) (u : (Circle × ℝ) × Circle) : Circle :=
  cexp (liftFamily G s₁ s₂ ((rep u.1.1, u.1.2), rep u.2))

def straightenInv (R : (ℝ × ℝ) × ℝ → ℝ) (u : (Circle × ℝ) × Circle) : Circle :=
  cexp (R ((rep u.1.1, u.1.2), rep u.2))

theorem straightenMap_coverMap (hper : ∀ p x, G (p, x + 1) = G (p, x) + 1)
    (hwind : ∀ θ r x, G ((θ + 1, r), x) = G ((θ, r), x) + w) (v : (ℝ × ℝ) × ℝ) :
    straightenMap G s₁ s₂ (coverMap v) = cexp (liftFamily G s₁ s₂ v) := by
  obtain ⟨n, hn⟩ := exists_rep_cexp v.1.1
  obtain ⟨n', hn'⟩ := exists_rep_cexp v.2
  unfold straightenMap coverMap
  simp only
  rw [hn, hn', liftFamily_add_int hper, liftFamily_wind_int hwind]
  have h : liftFamily G s₁ s₂ ((v.1.1, v.1.2), v.2) + n * w + n' =
      liftFamily G s₁ s₂ v + ((n * w + n' : ℤ) : ℝ) := by
    push_cast
    ring
  rw [h, cexp_add_int]

theorem liftFamily_injective (hG : ContDiff ℝ ∞ G)
    (hpos : ∀ p x, 0 < deriv (fun y => G (p, y)) x) (p : ℝ × ℝ) :
    Function.Injective (fun x => liftFamily G s₁ s₂ (p, x)) :=
  (strictMono_of_deriv_pos (deriv_liftFamily_pos hG hpos p)).injective

theorem straightenInv_coverMap (hG : ContDiff ℝ ∞ G) (hper : ∀ p x, G (p, x + 1) = G (p, x) + 1)
    (hpos : ∀ p x, 0 < deriv (fun y => G (p, y)) x)
    (hwind : ∀ θ r x, G ((θ + 1, r), x) = G ((θ, r), x) + w) {R : (ℝ × ℝ) × ℝ → ℝ}
    (hR₂ : ∀ p y, liftFamily G s₁ s₂ (p, R (p, y)) = y) (v : (ℝ × ℝ) × ℝ) :
    straightenInv R (coverMap v) = cexp (R v) := by
  obtain ⟨n, hn⟩ := exists_rep_cexp v.1.1
  obtain ⟨n', hn'⟩ := exists_rep_cexp v.2
  unfold straightenInv coverMap
  simp only
  rw [hn, hn']
  have heq : R ((v.1.1 + n, v.1.2), v.2 + n') = R v + ((n' - n * w : ℤ) : ℝ) := by
    apply liftFamily_injective (s₁ := s₁) (s₂ := s₂) hG hpos (v.1.1 + n, v.1.2)
    simp only
    rw [hR₂, liftFamily_wind_int hwind, liftFamily_add_int hper]
    have h := hR₂ v.1 v.2
    simp only [Prod.mk.eta] at h
    rw [h]
    push_cast
    ring
  rw [heq, cexp_add_int]

def straightenDiffeo (hG : ContDiff ℝ ∞ G) (hper : ∀ p x, G (p, x + 1) = G (p, x) + 1)
    (hpos : ∀ p x, 0 < deriv (fun y => G (p, y)) x)
    (hwind : ∀ θ r x, G ((θ + 1, r), x) = G ((θ, r), x) + w) (R : (ℝ × ℝ) × ℝ → ℝ)
    (hR : ContDiff ℝ ∞ R) (hR₁ : ∀ p x, R (p, liftFamily G s₁ s₂ (p, x)) = x)
    (hR₂ : ∀ p y, liftFamily G s₁ s₂ (p, R (p, y)) = y) :
    ((Circle × ℝ) × Circle) ≃ₘ⟮fibreModel, fibreModel⟯ ((Circle × ℝ) × Circle) where
  toFun u := (u.1, straightenMap G s₁ s₂ u)
  invFun u := (u.1, straightenInv R u)
  left_inv u := by
    obtain ⟨v, rfl⟩ := coverMap_surjective u
    have h : ((coverMap v).1, straightenMap G s₁ s₂ (coverMap v)) =
        coverMap (v.1, liftFamily G s₁ s₂ v) := by
      rw [straightenMap_coverMap hper hwind]
      rfl
    simp only
    rw [h, straightenInv_coverMap hG hper hpos hwind hR₂]
    simp only [hR₁]
    rfl
  right_inv u := by
    obtain ⟨v, rfl⟩ := coverMap_surjective u
    have h : ((coverMap v).1, straightenInv R (coverMap v)) = coverMap (v.1, R v) := by
      rw [straightenInv_coverMap hG hper hpos hwind hR₂]
      rfl
    simp only
    rw [h, straightenMap_coverMap hper hwind]
    simp only [hR₂]
    rfl
  contMDiff_toFun := by
    refine contMDiff_fst.prodMk (contMDiff_of_comp_coverMap ?_)
    have h : ContMDiff coverModel (𝓡 1) ∞ (fun v => cexp (liftFamily G s₁ s₂ v)) :=
      contMDiff_cexp.comp (contMDiff_cover_of_contDiff (contDiff_liftFamily hG))
    exact h.congr fun v => straightenMap_coverMap hper hwind v
  contMDiff_invFun := by
    refine contMDiff_fst.prodMk (contMDiff_of_comp_coverMap ?_)
    have h : ContMDiff coverModel (𝓡 1) ∞ (fun v => cexp (R v)) :=
      contMDiff_cexp.comp (contMDiff_cover_of_contDiff hR)
    exact h.congr fun v => straightenInv_coverMap hG hper hpos hwind hR₂ v

end Straighten


theorem contMDiff_zpow_sign {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ContMDiff (𝓡 1) (𝓡 1) ∞ (fun z : Circle => z ^ ε) := by
  rcases hε with rfl | rfl
  · exact contMDiff_id.congr fun z => zpow_one z
  · exact (contMDiff_inv (𝓡 1) (n := ∞) (G := Circle)).congr fun z => zpow_neg_one z

theorem zpow_sign_zpow_sign {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (z : Circle) : (z ^ ε) ^ ε = z := by
  rw [← zpow_mul]
  rcases hε with rfl | rfl <;> simp

section FibreRotate

variable {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]

def fibreRotate (σ : P → Circle) (hσ : ContMDiff I' (𝓡 1) ∞ σ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    (P × Circle) ≃ₘ⟮I'.prod (𝓡 1), I'.prod (𝓡 1)⟯ (P × Circle) where
  toFun u := (u.1, σ u.1 * u.2 ^ ε)
  invFun u := (u.1, ((σ u.1)⁻¹ * u.2) ^ ε)
  left_inv u := by
    simp only [inv_mul_cancel_left, zpow_sign_zpow_sign hε]
  right_inv u := by
    simp only [zpow_sign_zpow_sign hε, mul_inv_cancel_left]
  contMDiff_toFun := contMDiff_fst.prodMk ((hσ.comp contMDiff_fst).mul
    ((contMDiff_zpow_sign hε).comp contMDiff_snd))
  contMDiff_invFun := contMDiff_fst.prodMk ((contMDiff_zpow_sign hε).comp
    ((hσ.comp contMDiff_fst).inv.mul contMDiff_snd))

theorem fibreRotate_symm_apply (σ : P → Circle) (hσ : ContMDiff I' (𝓡 1) ∞ σ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (u : P × Circle) :
    (fibreRotate σ hσ ε hε).symm u = (u.1, ((σ u.1)⁻¹ * u.2) ^ ε) := rfl

theorem fibreRotate_apply (σ : P → Circle) (hσ : ContMDiff I' (𝓡 1) ∞ σ) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1) (u : P × Circle) :
    fibreRotate σ hσ ε hε u = (u.1, σ u.1 * u.2 ^ ε) := rfl

end FibreRotate

section LiftAnalysis

variable (Ψ₀ : ((Circle × ℝ) × Circle) ≃ₘ⟮fibreModel, fibreModel⟯ ((Circle × ℝ) × Circle))

theorem exists_int_shift_of_lift {F : (ℝ × ℝ) × ℝ → ℝ} (hF : Continuous F)
    {T : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ} (hT : Continuous T)
    (h : ∀ v, cexp (F (T v)) = cexp (F v)) :
    ∃ n : ℤ, ∀ v, F (T v) = F v + n :=
  exists_int_of_cexp_eq hF (hF.comp hT) h 0

theorem exists_oriented_lift (hΨ₀ : ∀ u, (Ψ₀ u).1 = u.1) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∃ G : (ℝ × ℝ) × ℝ → ℝ, ContDiff ℝ ∞ G ∧
      (∀ p x, G (p, x + 1) = G (p, x) + 1) ∧ (∀ p x, 0 < deriv (fun y => G (p, y)) x) ∧
      (∃ w : ℤ, ∀ θ r x, G ((θ + 1, r), x) = G ((θ, r), x) + w) ∧
      ∀ v, cexp (G v) = (Ψ₀ ((coverMap v).1, (coverMap v).2 ^ ε)).2 := by
  obtain ⟨G₀, hG₀, hl₀⟩ := exists_cover_lift (f := fun u => (Ψ₀ u).2)
    (contMDiff_snd.comp Ψ₀.contMDiff)
  obtain ⟨G₁, hG₁, hl₁⟩ := exists_cover_lift (f := fun u => (Ψ₀.symm u).2)
    (contMDiff_snd.comp Ψ₀.symm.contMDiff)
  have hΨ₀s (u : (Circle × ℝ) × Circle) : (Ψ₀.symm u).1 = u.1 := by
    have h := hΨ₀ (Ψ₀.symm u)
    rw [Diffeomorph.apply_symm_apply] at h
    exact h.symm
  have hinv (u : (Circle × ℝ) × Circle) : (Ψ₀.symm (u.1, (Ψ₀ u).2)).2 = u.2 := by
    have h : (u.1, (Ψ₀ u).2) = Ψ₀ u := Prod.ext (hΨ₀ u).symm rfl
    rw [h, Diffeomorph.symm_apply_apply]
  have hinv' (u : (Circle × ℝ) × Circle) : (Ψ₀ (u.1, (Ψ₀.symm u).2)).2 = u.2 := by
    have h : (u.1, (Ψ₀.symm u).2) = Ψ₀.symm u := Prod.ext (hΨ₀s u).symm rfl
    rw [h, Diffeomorph.apply_symm_apply]
  obtain ⟨w, hw⟩ := exists_int_shift_of_lift hG₀.continuous
    (T := fun v => ((v.1.1 + 1, v.1.2), v.2)) (by fun_prop) (fun v => by
      rw [hl₀, hl₀]
      unfold coverMap
      rw [cexp_add, cexp_eq 1, mul_one, Circle.exp_two_pi, mul_one])
  obtain ⟨d, hd⟩ := exists_int_shift_of_lift hG₀.continuous
    (T := fun v => (v.1, v.2 + 1)) (by fun_prop) (fun v => by
      rw [hl₀, hl₀]
      unfold coverMap
      rw [cexp_add, cexp_eq 1, mul_one, Circle.exp_two_pi, mul_one])
  obtain ⟨d', hd'⟩ := exists_int_shift_of_lift hG₁.continuous
    (T := fun v => (v.1, v.2 + 1)) (by fun_prop) (fun v => by
      rw [hl₁, hl₁]
      unfold coverMap
      rw [cexp_add, cexp_eq 1, mul_one, Circle.exp_two_pi, mul_one])
  obtain ⟨m, hm⟩ := exists_int_of_cexp_eq (F := fun v : (ℝ × ℝ) × ℝ => v.2)
    (F' := fun v => G₁ (v.1, G₀ v)) continuous_snd
    (hG₁.continuous.comp (continuous_fst.prodMk hG₀.continuous)) (fun v => by
      show cexp (G₁ (v.1, G₀ v)) = cexp v.2
      rw [hl₁]
      unfold coverMap
      rw [hl₀]
      exact hinv (coverMap v)) 0
  have hd'1 (p : ℝ × ℝ) : Function.Periodic (fun y => G₁ (p, y) - d' * y) 1 := by
    intro x
    simp only
    rw [show (p, x + 1) = ((fun v : (ℝ × ℝ) × ℝ => (v.1, v.2 + 1)) (p, x)) from rfl, hd']
    ring
  have hG₁n (p : ℝ × ℝ) (y : ℝ) (n : ℤ) : G₁ (p, y + n) = G₁ (p, y) + n * d' := by
    have h := (Function.Periodic.int_mul (hd'1 p) n) y
    simp only [mul_one] at h
    linarith
  have hdd : d * d' = 1 := by
    have h1 := hm ((0, 0), 1)
    have h0 := hm ((0, 0), 0)
    simp only at h1 h0
    have h2 : G₀ ((0, 0), 1) = G₀ ((0, 0), 0) + d := by
      have := hd ((0, 0), 0)
      simpa only [zero_add] using this
    rw [h2, hG₁n, h0] at h1
    have h3 : ((d * d' : ℤ) : ℝ) = 1 := by push_cast; linarith
    exact_mod_cast h3
  have hderiv (p : ℝ × ℝ) (x : ℝ) : deriv (fun y => G₀ (p, y)) x ≠ 0 := by
    have hc := HasDerivAt.comp x (hasDerivAt_section hG₁ p (G₀ (p, x)))
      (hasDerivAt_section hG₀ p x)
    have hid : HasDerivAt ((fun y => G₁ (p, y)) ∘ (fun y => G₀ (p, y))) 1 x := by
      have h := (hasDerivAt_id x).add_const (m : ℝ)
      exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => hm (p, y))
    have h := hc.unique hid
    rw [deriv_section hG₀]
    intro h0
    rw [h0, mul_zero] at h
    exact zero_ne_one h
  have hcont : Continuous (fun v : (ℝ × ℝ) × ℝ => fderiv ℝ G₀ v (0, 1)) :=
    (hG₀.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsign : (∀ v : (ℝ × ℝ) × ℝ, 0 < fderiv ℝ G₀ v (0, 1)) ∨
      ∀ v : (ℝ × ℝ) × ℝ, fderiv ℝ G₀ v (0, 1) < 0 := by
    by_contra hc
    simp only [not_or, not_forall, not_lt] at hc
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hc
    have hne (v : (ℝ × ℝ) × ℝ) : fderiv ℝ G₀ v (0, 1) ≠ 0 := by
      rw [← deriv_section hG₀]
      exact hderiv v.1 v.2
    have ha' : fderiv ℝ G₀ a (0, 1) < 0 := lt_of_le_of_ne ha (hne a)
    have hb' : 0 < fderiv ℝ G₀ b (0, 1) := lt_of_le_of_ne' hb (hne b)
    obtain ⟨c, -, hc⟩ := isPreconnected_univ.intermediate_value (mem_univ a) (mem_univ b)
      hcont.continuousOn ⟨ha'.le, hb'.le⟩
    exact hne c hc
  rcases hsign with hpos | hneg
  · have hpos' (p : ℝ × ℝ) (x : ℝ) : 0 < deriv (fun y => G₀ (p, y)) x := by
      rw [deriv_section hG₀]
      exact hpos (p, x)
    have hdpos : 0 < d := by
      have h := strictMono_of_deriv_pos (hpos' (0, 0)) (show (0 : ℝ) < 1 by norm_num)
      have h2 := hd ((0, 0), 0)
      simp only [zero_add] at h2
      have h3 : (0 : ℝ) < d := by linarith
      exact_mod_cast h3
    have hd1' : d = 1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hdd with h | h
      · exact h
      · omega
    refine ⟨1, Or.inl rfl, G₀, hG₀, fun p x => ?_, hpos', ⟨w, fun θ r x => ?_⟩, fun v => ?_⟩
    · have h := hd (p, x)
      rw [hd1'] at h
      simpa using h
    · exact hw ((θ, r), x)
    · rw [zpow_one, hl₀]
  · have hneg' (p : ℝ × ℝ) (x : ℝ) : deriv (fun y => G₀ (p, y)) x < 0 := by
      rw [deriv_section hG₀]
      exact hneg (p, x)
    have hdneg : d < 0 := by
      have hanti : StrictAnti (fun y => G₀ ((0, 0), y)) := strictAnti_of_deriv_neg (hneg' (0, 0))
      have h := hanti (show (0 : ℝ) < 1 by norm_num)
      have h2 := hd ((0, 0), 0)
      simp only [zero_add] at h2
      have h3 : (d : ℝ) < 0 := by linarith
      exact_mod_cast h3
    have hd1' : d = -1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hdd with h | h
      · omega
      · exact h
    refine ⟨-1, Or.inr rfl, fun v => G₀ (v.1, -v.2),
      hG₀.comp (contDiff_fst.prodMk contDiff_snd.neg), fun p x => ?_, fun p x => ?_,
      ⟨w, fun θ r x => ?_⟩, fun v => ?_⟩
    · have h := hd (p, -(x + 1))
      rw [hd1'] at h
      simp only at h ⊢
      rw [show -(x + 1) + 1 = -x by ring] at h
      push_cast at h
      linarith
    · have h := deriv_comp_neg (f := fun y => G₀ (p, y)) (x := x)
      simp only at h ⊢
      rw [h]
      linarith [hneg' p (-x)]
    · exact hw ((θ, r), -x)
    · simp only
      rw [hl₀]
      unfold coverMap
      simp only
      rw [cexp_neg, zpow_neg_one]

end LiftAnalysis


def fibreDiffeo (Ψ : ((Circle × ℝ) × Circle) ≃ₘ⟮fibreModel, fibreModel⟯ ((Circle × ℝ) × Circle))
    (hΨ : ∀ u, (Ψ u).1 = u.1) (q : Circle × ℝ) : Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle where
  toFun z := (Ψ (q, z)).2
  invFun w := (Ψ.symm (q, w)).2
  left_inv z := by
    have h : (q, (Ψ (q, z)).2) = Ψ (q, z) := Prod.ext (hΨ (q, z)).symm rfl
    simp only
    rw [h, Diffeomorph.symm_apply_apply]
  right_inv w := by
    have h1 : (Ψ.symm (q, w)).1 = q := by
      have h := hΨ (Ψ.symm (q, w))
      rw [Diffeomorph.apply_symm_apply] at h
      exact h.symm
    have h : (q, (Ψ.symm (q, w)).2) = Ψ.symm (q, w) := Prod.ext h1.symm rfl
    simp only
    rw [h, Diffeomorph.apply_symm_apply]
  contMDiff_toFun := contMDiff_snd.comp (Ψ.contMDiff.comp (contMDiff_const.prodMk contMDiff_id))
  contMDiff_invFun :=
    contMDiff_snd.comp (Ψ.symm.contMDiff.comp (contMDiff_const.prodMk contMDiff_id))

theorem fibreDiffeo_apply
    (Ψ : ((Circle × ℝ) × Circle) ≃ₘ⟮fibreModel, fibreModel⟯ ((Circle × ℝ) × Circle))
    (hΨ : ∀ u, (Ψ u).1 = u.1) (q : Circle × ℝ) (z : Circle) :
    fibreDiffeo Ψ hΨ q z = (Ψ (q, z)).2 := rfl

theorem exists_straightening
    (Ψ₀ : ((Circle × ℝ) × Circle) ≃ₘ⟮fibreModel, fibreModel⟯ ((Circle × ℝ) × Circle))
    (hΨ₀ : ∀ u, (Ψ₀ u).1 = u.1) {s₁ s₂ : ℝ} (hs : s₁ < s₂) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∃ Ψ : ((Circle × ℝ) × Circle) ≃ₘ⟮fibreModel, fibreModel⟯ ((Circle × ℝ) × Circle),
        (∀ u, (Ψ u).1 = u.1) ∧ (∀ u, u.1.2 ≤ s₁ → Ψ u = Ψ₀ u) ∧
        (∀ u, s₂ ≤ u.1.2 → (Ψ u).2 = (Ψ₀ ((u.1.1, s₂), 1)).2 * u.2 ^ ε) ∧
        ∀ (θ : Circle) (r : ℝ) (F : ℝ → ℝ), Continuous F →
          (∀ x, cexp (F x) = (Ψ₀ ((θ, freeze s₁ s₂ r), cexp x ^ ε)).2) →
          ∀ x, (Ψ ((θ, r), cexp x ^ ε)).2 = cexp (straightenLift F (cutoff s₁ s₂ r) x) := by
  obtain ⟨ε, hε, G, hG, hper, hpos, ⟨w, hwind⟩, hlift⟩ := exists_oriented_lift Ψ₀ hΨ₀
  obtain ⟨R, hR, hR₁, hR₂⟩ := exists_liftFamily_inverse (s₁ := s₁) (s₂ := s₂) hG hper hpos
  let Ψ' := straightenDiffeo hG hper hpos hwind R hR hR₁ hR₂
  let Rε := fibreRotate (I' := (𝓡 1).prod 𝓘(ℝ, ℝ)) (P := Circle × ℝ) 1 contMDiff_one ε hε
  have hΨ (u : (Circle × ℝ) × Circle) :
      (Rε.trans Ψ') u = (u.1, straightenMap G s₁ s₂ (u.1, u.2 ^ ε)) := by
    change (u.1, straightenMap G s₁ s₂ (u.1, 1 * u.2 ^ ε)) = _
    rw [one_mul]
  have hcov (u : (Circle × ℝ) × Circle) : ∃ v, coverMap v = (u.1, u.2 ^ ε) ∧ v.1.2 = u.1.2 := by
    obtain ⟨v, hv⟩ := coverMap_surjective (u.1, u.2 ^ ε)
    exact ⟨v, hv, congrArg (fun q => q.1.2) hv⟩
  refine ⟨ε, hε, Rε.trans Ψ', fun u => by rw [hΨ], fun u hu => ?_, fun u hu => ?_, ?_⟩
  · obtain ⟨v, hv, hvr⟩ := hcov u
    rw [hΨ, ← hv, straightenMap_coverMap hper hwind, liftFamily_of_le hs v (hvr ▸ hu), hlift,
      hv]
    refine Prod.ext (hΨ₀ u).symm ?_
    change (Ψ₀ (u.1, (u.2 ^ ε) ^ ε)).2 = _
    rw [zpow_sign_zpow_sign hε]
  · obtain ⟨v, hv, hvr⟩ := hcov u
    rw [hΨ, ← hv, straightenMap_coverMap hper hwind, liftFamily_of_ge hs v (hvr ▸ hu), cexp_add,
      hlift]
    have h1 : (coverMap ((v.1.1, s₂), 0)).1 = (u.1.1, s₂) := by
      have h := congrArg (fun q => q.1.1) hv
      exact Prod.ext h rfl
    have h2 : (coverMap ((v.1.1, s₂), 0)).2 ^ ε = 1 := by
      change cexp 0 ^ ε = 1
      rw [cexp_zero, one_zpow]
    have h3 : cexp v.2 = u.2 ^ ε := congrArg Prod.snd hv
    simp only
    rw [h1, h2, h3, mul_comm]
  · intro θ r F hF hFl x
    obtain ⟨θ', rfl⟩ := cexp_surjective θ
    have hv : ((cexp θ', r), (cexp x ^ ε) ^ ε) = coverMap ((θ', r), x) := by
      rw [zpow_sign_zpow_sign hε]
      rfl
    rw [hΨ]
    simp only
    rw [hv, straightenMap_coverMap hper hwind]
    obtain ⟨n, hn⟩ := exists_int_of_cexp_eq (F := fun y => G ((θ', freeze s₁ s₂ r), y)) (F' := F)
      (hG.continuous.comp (continuous_const.prodMk continuous_id)) hF
      (fun y => by rw [hFl, hlift]; rfl) 0
    have hFeq : F = fun y => G ((θ', freeze s₁ s₂ r), y) + n := funext hn
    rw [hFeq, straightenLift_add_const, cexp_add_int]
    rfl

end AnnulusStraightening

open AnnulusStraightening

variable {C : CompactCarrier.{u}} {U : TopologicalSpace.Opens C.Carrier}

def CircleFibration.restrictChart (F : CircleFibration C U)
    {V D : TopologicalSpace.Opens F.base.Carrier}
    (hD : D ≤ V) (τ : TopologicalSpace.Opens.comap F.projection V ≃ₘ⟮C.model,
      (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ (V × Circle))
    (hτ : ∀ x, (τ x).1.val = F.projection x.val) :
    TopologicalSpace.Opens.comap F.projection D ≃ₘ⟮C.model,
      (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ (D × Circle) where
  toFun x := (⟨(τ (TopologicalSpace.Opens.inclusion
      (TopologicalSpace.Opens.comap_mono F.projection hD) x)).1.val, by
        rw [hτ]
        exact x.2⟩,
    (τ (TopologicalSpace.Opens.inclusion
      (TopologicalSpace.Opens.comap_mono F.projection hD) x)).2)
  invFun q := ⟨(τ.symm (TopologicalSpace.Opens.inclusion hD q.1, q.2)).val, by
    change F.projection _ ∈ D
    rw [← hτ, Diffeomorph.apply_symm_apply]
    exact q.1.2⟩
  left_inv x := by
    apply Subtype.ext
    dsimp only
    have h : ((TopologicalSpace.Opens.inclusion hD ⟨(τ
        (TopologicalSpace.Opens.inclusion (TopologicalSpace.Opens.comap_mono F.projection hD)
          x)).1.val, by rw [hτ]; exact x.2⟩ : V),
        (τ (TopologicalSpace.Opens.inclusion
          (TopologicalSpace.Opens.comap_mono F.projection hD) x)).2) =
        τ (TopologicalSpace.Opens.inclusion
          (TopologicalSpace.Opens.comap_mono F.projection hD) x) := rfl
    rw [h, Diffeomorph.symm_apply_apply]
  right_inv q := by
    have h : TopologicalSpace.Opens.inclusion (TopologicalSpace.Opens.comap_mono F.projection hD)
        ⟨(τ.symm (TopologicalSpace.Opens.inclusion hD q.1, q.2)).val, by
          change F.projection _ ∈ D
          rw [← hτ, Diffeomorph.apply_symm_apply]
          exact q.1.2⟩ =
        τ.symm (TopologicalSpace.Opens.inclusion hD q.1, q.2) := rfl
    simp only [h, Diffeomorph.apply_symm_apply]
  contMDiff_toFun := by
    have hc := τ.contMDiff.comp
      (contMDiff_inclusion (I := C.model) (TopologicalSpace.Opens.comap_mono F.projection hD))
    refine ContMDiff.prodMk ?_ (contMDiff_snd.comp hc)
    apply (ContMDiff.subtypeVal_comp_iff D _).mp
    have h : ContMDiff C.model (SurfaceModel.model F.base.kind) ∞
        (fun x => (τ (TopologicalSpace.Opens.inclusion
          (TopologicalSpace.Opens.comap_mono F.projection hD) x)).1.val) :=
      contMDiff_subtype_val.comp (contMDiff_fst.comp hc)
    exact h
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff _ _).mp
    have h : ContMDiff ((SurfaceModel.model F.base.kind).prod (𝓡 1)) C.model ∞
        (fun q : D × Circle =>
          (τ.symm (TopologicalSpace.Opens.inclusion hD q.1, q.2)).val) :=
      contMDiff_subtype_val.comp (τ.symm.contMDiff.comp
        (((contMDiff_inclusion hD).comp contMDiff_fst).prodMk contMDiff_snd))
    exact h

variable (F : CircleFibration C U) {V D : TopologicalSpace.Opens F.base.Carrier} (hD : D ≤ V)
  (τ : TopologicalSpace.Opens.comap F.projection V ≃ₘ⟮C.model,
      (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ (V × Circle))
  (hτ : ∀ x, (τ x).1.val = F.projection x.val)

theorem CircleFibration.restrictChart_fst (x : TopologicalSpace.Opens.comap F.projection D) :
    (CircleFibration.restrictChart F hD τ hτ x).1.val = F.projection x.val :=
  hτ _

theorem CircleFibration.restrictChart_snd (x : U) (hx : F.projection x ∈ D) :
    (CircleFibration.restrictChart F hD τ hτ ⟨x, hx⟩).2 = (τ ⟨x, hD hx⟩).2 := rfl

theorem CircleFibration.restrictChart_apply (x : U) (hx : F.projection x ∈ D) :
    CircleFibration.restrictChart F hD τ hτ ⟨x, hx⟩ = (⟨F.projection x, hx⟩, (τ ⟨x, hD hx⟩).2) :=
  Prod.ext (Subtype.ext (hτ _)) rfl

include hτ in
theorem CircleFibration.chart_eq_mk (x : U) (hx : F.projection x ∈ V) :
    τ ⟨x, hx⟩ = (⟨F.projection x, hx⟩, (τ ⟨x, hx⟩).2) :=
  Prod.ext (Subtype.ext (hτ _)) rfl

structure AnnulusChartPair (F : CircleFibration C U) where
  inner : TopologicalSpace.Opens F.base.Carrier
  outer : TopologicalSpace.Opens F.base.Carrier
  covers : ∀ y, y ∈ inner ∨ y ∈ outer
  innerChart : TopologicalSpace.Opens.comap F.projection inner ≃ₘ⟮C.model,
    (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ (inner × Circle)
  innerChart_fst : ∀ x, (innerChart x).1.val = F.projection x.val
  outerChart : TopologicalSpace.Opens.comap F.projection outer ≃ₘ⟮C.model,
    (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ (outer × Circle)
  outerChart_fst : ∀ x, (outerChart x).1.val = F.projection x.val
  coord : (Circle × ℝ) ≃ₘ⟮(𝓡 1).prod 𝓘(ℝ, ℝ), SurfaceModel.model F.base.kind⟯ ↥(inner ⊓ outer)
  angle : F.base.Carrier → Circle
  angle_smooth : ContMDiffOn (SurfaceModel.model F.base.kind) (𝓡 1) ∞ angle outer
  angle_coord : ∀ q, angle (coord q) = q.1
  isOpen_innerPart : ∀ s, IsOpen ((inner : Set F.base.Carrier) \
    (fun q => ((coord q : ↥(inner ⊓ outer)) : F.base.Carrier)) '' {q | s ≤ q.2})
  isOpen_outerPart : ∀ s, IsOpen ((outer : Set F.base.Carrier) \
    (fun q => ((coord q : ↥(inner ⊓ outer)) : F.base.Carrier)) '' {q | q.2 ≤ s})

namespace AnnulusChartPair

variable {F} (P : AnnulusChartPair F)

def innerPart (s : ℝ) : TopologicalSpace.Opens F.base.Carrier :=
  ⟨(P.inner : Set F.base.Carrier) \
    (fun q => ((P.coord q : ↥(P.inner ⊓ P.outer)) : F.base.Carrier)) '' {q | s ≤ q.2},
    P.isOpen_innerPart s⟩

def outerPart (s : ℝ) : TopologicalSpace.Opens F.base.Carrier :=
  ⟨(P.outer : Set F.base.Carrier) \
    (fun q => ((P.coord q : ↥(P.inner ⊓ P.outer)) : F.base.Carrier)) '' {q | q.2 ≤ s},
    P.isOpen_outerPart s⟩

def overlapInner :=
  CircleFibration.restrictChart F (inf_le_left : P.inner ⊓ P.outer ≤ P.inner) P.innerChart
  P.innerChart_fst

def overlapOuter :=
  CircleFibration.restrictChart F (inf_le_right : P.inner ⊓ P.outer ≤ P.outer) P.outerChart
  P.outerChart_fst

def transition : ((Circle × ℝ) × Circle) ≃ₘ⟮fibreModel, fibreModel⟯ ((Circle × ℝ) × Circle) :=
  (P.coord.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).trans (P.overlapOuter.symm.trans
    (P.overlapInner.trans (P.coord.symm.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))))

theorem transition_fst (u : (Circle × ℝ) × Circle) : (P.transition u).1 = u.1 := by
  change P.coord.symm (P.overlapInner (P.overlapOuter.symm (P.coord u.1, u.2))).1 = u.1
  have h : (P.overlapInner (P.overlapOuter.symm (P.coord u.1, u.2))).1 = P.coord u.1 := by
    apply Subtype.ext
    rw [overlapInner, CircleFibration.restrictChart_fst]
    have h2 := CircleFibration.restrictChart_fst F (inf_le_right : P.inner ⊓ P.outer ≤ P.outer)
      P.outerChart P.outerChart_fst (P.overlapOuter.symm (P.coord u.1, u.2))
    change (P.overlapOuter (P.overlapOuter.symm (P.coord u.1, u.2))).1.val = _ at h2
    rw [Diffeomorph.apply_symm_apply] at h2
    exact h2.symm
  rw [h, Diffeomorph.symm_apply_apply]

theorem transition_snd (x : U) (hx : F.projection x ∈ P.inner ⊓ P.outer) :
    (P.transition (P.coord.symm ⟨F.projection x, hx⟩, (P.outerChart ⟨x, hx.2⟩).2)).2 =
      (P.innerChart ⟨x, hx.1⟩).2 := by
  change (P.overlapInner (P.overlapOuter.symm (P.coord (P.coord.symm ⟨F.projection x, hx⟩),
    (P.outerChart ⟨x, hx.2⟩).2))).2 = _
  rw [Diffeomorph.apply_symm_apply]
  have h : ((⟨F.projection x, hx⟩ : ↥(P.inner ⊓ P.outer)), (P.outerChart ⟨x, hx.2⟩).2) =
      P.overlapOuter ⟨x, hx⟩ :=
    (CircleFibration.restrictChart_apply F (inf_le_right : P.inner ⊓ P.outer ≤ P.outer) P.outerChart
      P.outerChart_fst x hx).symm
  rw [h, Diffeomorph.symm_apply_apply]
  rfl

theorem innerPart_le (s : ℝ) : P.innerPart s ≤ P.inner := sdiff_subset

theorem outerPart_le (s : ℝ) : P.outerPart s ≤ P.outer := sdiff_subset

def innerRestrict (s : ℝ) :=
  CircleFibration.restrictChart F (P.innerPart_le s) P.innerChart P.innerChart_fst

def middleChart (Ψ : ((Circle × ℝ) × Circle) ≃ₘ⟮fibreModel, fibreModel⟯ ((Circle × ℝ) × Circle)) :
    TopologicalSpace.Opens.comap F.projection (P.inner ⊓ P.outer) ≃ₘ⟮C.model,
      (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ (↥(P.inner ⊓ P.outer) × Circle) :=
  P.overlapOuter.trans ((P.coord.symm.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞)).trans
    (Ψ.trans (P.coord.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))))

theorem middleChart_apply (Ψ : ((Circle × ℝ) × Circle) ≃ₘ⟮fibreModel, fibreModel⟯
    ((Circle × ℝ) × Circle)) (hΨ : ∀ u, (Ψ u).1 = u.1) (x : U)
    (hx : F.projection x ∈ P.inner ⊓ P.outer) :
    P.middleChart Ψ ⟨x, hx⟩ = (⟨F.projection x, hx⟩,
      (Ψ (P.coord.symm ⟨F.projection x, hx⟩, (P.outerChart ⟨x, hx.2⟩).2)).2) := by
  change (P.coord (Ψ (P.coord.symm (P.overlapOuter ⟨x, hx⟩).1, (P.overlapOuter ⟨x, hx⟩).2)).1,
    (Ψ (P.coord.symm (P.overlapOuter ⟨x, hx⟩).1, (P.overlapOuter ⟨x, hx⟩).2)).2) = _
  rw [overlapOuter, CircleFibration.restrictChart_apply, hΨ, Diffeomorph.apply_symm_apply]

def rotation (s₂ : ℝ) (θ : Circle) : Circle := (P.transition ((θ, s₂), 1)).2

theorem contMDiff_rotation (s₂ : ℝ) : ContMDiff (𝓡 1) (𝓡 1) ∞ (P.rotation s₂) :=
  contMDiff_snd.comp (P.transition.contMDiff.comp
    ((contMDiff_id.prodMk contMDiff_const).prodMk contMDiff_const))

theorem contMDiff_angle_restrict (s : ℝ) :
    ContMDiff (SurfaceModel.model F.base.kind) (𝓡 1) ∞
      (fun y : P.outerPart s => P.angle y.val) :=
  fun v => contMDiffAt_subtype_iff.mpr
    ((P.angle_smooth v (P.outerPart_le s v.2)).contMDiffAt
      (P.outer.isOpen.mem_nhds (P.outerPart_le s v.2)))

def outerRotChart (s₂ : ℝ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) :
    TopologicalSpace.Opens.comap F.projection (P.outerPart s₂) ≃ₘ⟮C.model,
      (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ (↥(P.outerPart s₂) × Circle) :=
  (CircleFibration.restrictChart F (P.outerPart_le s₂) P.outerChart P.outerChart_fst).trans
    (fibreRotate (fun y : P.outerPart s₂ => P.rotation s₂ (P.angle y.val))
      ((P.contMDiff_rotation s₂).comp (P.contMDiff_angle_restrict s₂)) ε hε)

theorem outerRotChart_apply (s₂ : ℝ) (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (x : U)
    (hx : F.projection x ∈ P.outerPart s₂) :
    P.outerRotChart s₂ ε hε ⟨x, hx⟩ = (⟨F.projection x, hx⟩,
      P.rotation s₂ (P.angle (F.projection x)) * (P.outerChart ⟨x, hx.1⟩).2 ^ ε) := by
  simp only [outerRotChart, Diffeomorph.coe_trans, Function.comp_apply, fibreRotate_apply]
  rw [CircleFibration.restrictChart_apply]

theorem coord_symm_val (y : ↥(P.inner ⊓ P.outer)) : ((P.coord (P.coord.symm y)) : F.base.Carrier) =
    y.val := by
  rw [Diffeomorph.apply_symm_apply]

theorem coord_symm_le_of_mem_innerPart {s : ℝ} (x : F.base.Carrier) (hx : x ∈ P.inner ⊓ P.outer)
    (h : x ∈ P.innerPart s) : (P.coord.symm ⟨x, hx⟩).2 < s := by
  by_contra hc
  exact h.2 ⟨P.coord.symm ⟨x, hx⟩, not_lt.mp hc, P.coord_symm_val _⟩

theorem coord_symm_ge_of_mem_outerPart {s : ℝ} (x : F.base.Carrier) (hx : x ∈ P.inner ⊓ P.outer)
    (h : x ∈ P.outerPart s) : s < (P.coord.symm ⟨x, hx⟩).2 := by
  by_contra hc
  exact h.2 ⟨P.coord.symm ⟨x, hx⟩, not_lt.mp hc, P.coord_symm_val _⟩

section Atlas

variable (Ψ : ((Circle × ℝ) × Circle) ≃ₘ⟮fibreModel, fibreModel⟯ ((Circle × ℝ) × Circle))
  (hΨ : ∀ u, (Ψ u).1 = u.1) {s₁ s₂ : ℝ} {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
  (hle : ∀ u, u.1.2 ≤ s₁ → Ψ u = P.transition u)
  (hge : ∀ u, s₂ ≤ u.1.2 → (Ψ u).2 = P.rotation s₂ u.1.1 * u.2 ^ ε)

include hΨ hle in
theorem innerRestrict_eq_middleChart (x : U) (h₀ : F.projection x ∈ P.innerPart s₁)
    (h₁ : F.projection x ∈ P.inner ⊓ P.outer) :
    (P.innerRestrict s₁ ⟨x, h₀⟩).2 = (P.middleChart Ψ ⟨x, h₁⟩).2 := by
  rw [middleChart_apply P Ψ hΨ x h₁]
  dsimp only
  rw [hle _ (P.coord_symm_le_of_mem_innerPart _ h₁ h₀).le, transition_snd]
  rfl

include hΨ hge in
theorem middleChart_eq_outerRotChart (x : U) (h₁ : F.projection x ∈ P.inner ⊓ P.outer)
    (h₂ : F.projection x ∈ P.outerPart s₂) :
    (P.middleChart Ψ ⟨x, h₁⟩).2 = (P.outerRotChart s₂ ε hε ⟨x, h₂⟩).2 := by
  rw [middleChart_apply P Ψ hΨ x h₁, outerRotChart_apply]
  dsimp only
  rw [hge _ (P.coord_symm_ge_of_mem_outerPart _ h₁ h₂).le]
  have h : P.angle (F.projection x) = (P.coord.symm ⟨F.projection x, h₁⟩).1 := by
    rw [← P.angle_coord, P.coord_symm_val]
  rw [h]

theorem not_mem_innerPart_outerPart (hs : s₁ < s₂) (y : F.base.Carrier)
    (h₀ : y ∈ P.innerPart s₁) (h₂ : y ∈ P.outerPart s₂) : False := by
  have h₁ : y ∈ P.inner ⊓ P.outer := ⟨h₀.1, h₂.1⟩
  have a := P.coord_symm_le_of_mem_innerPart _ h₁ h₀
  have b := P.coord_symm_ge_of_mem_outerPart _ h₁ h₂
  linarith

def straightAtlas (hs : s₁ < s₂) : PrincipalAtlas F where
  count := 3
  domain := ![P.innerPart s₁, P.inner ⊓ P.outer, P.outerPart s₂]
  covers y := by
    by_cases hO : y ∈ P.inner ⊓ P.outer
    · exact ⟨1, hO⟩
    · have hn : ∀ s : Set (Circle × ℝ),
          y ∉ (fun q => ((P.coord q : ↥(P.inner ⊓ P.outer)) : F.base.Carrier)) '' s := by
        intro s hs
        obtain ⟨q, -, hq⟩ := hs
        exact hO (hq ▸ (P.coord q).2)
      rcases P.covers y with h | h
      · exact ⟨0, h, hn _⟩
      · exact ⟨2, h, hn _⟩
  chart i := match i with
    | 0 => P.innerRestrict s₁
    | 1 => P.middleChart Ψ
    | 2 => P.outerRotChart s₂ ε hε
  chart_fst i x := by
    obtain ⟨x, hx⟩ := x
    fin_cases i
    · exact CircleFibration.restrictChart_fst F _ P.innerChart P.innerChart_fst ⟨x, hx⟩
    · change (P.middleChart Ψ ⟨x, hx⟩).1.val = _
      rw [middleChart_apply P Ψ hΨ x hx]
    · have hx' : F.projection x ∈ P.outerPart s₂ := hx
      change (P.outerRotChart s₂ ε hε ⟨x, hx'⟩).1.val = F.projection x
      rw [outerRotChart_apply]
  transition := 1
  chart_snd i j x hi hj := by
    rw [Pi.one_apply, Pi.one_apply, Pi.one_apply, one_mul]
    fin_cases i <;> fin_cases j
    · rfl
    · exact P.innerRestrict_eq_middleChart Ψ hΨ hle x hi hj
    · exact (P.not_mem_innerPart_outerPart hs _ hi hj).elim
    · exact (P.innerRestrict_eq_middleChart Ψ hΨ hle x hj hi).symm
    · rfl
    · exact P.middleChart_eq_outerRotChart Ψ hΨ hε hge x hi hj
    · exact (P.not_mem_innerPart_outerPart hs _ hj hi).elim
    · exact (P.middleChart_eq_outerRotChart Ψ hΨ hε hge x hj hi).symm
    · rfl

theorem straightAtlas_chart_inner (hs : s₁ < s₂) (x : U) (h : F.projection x ∈ P.innerPart s₁) :
    ((P.straightAtlas Ψ hΨ hε hle hge hs).chart (0 : Fin 3) ⟨x, h⟩).2 =
      (P.innerChart ⟨x, h.1⟩).2 := rfl

theorem straightAtlas_chart_outer (hs : s₁ < s₂) (x : U) (h : F.projection x ∈ P.outerPart s₂) :
    ((P.straightAtlas Ψ hΨ hε hle hge hs).chart (2 : Fin 3) ⟨x, h⟩).2 =
      P.rotation s₂ (P.angle (F.projection x)) * (P.outerChart ⟨x, h.1⟩).2 ^ ε := by
  change (P.outerRotChart s₂ ε hε ⟨x, h⟩).2 = _
  rw [outerRotChart_apply]

theorem straightAtlas_coboundary (hs : s₁ < s₂) (i j : Fin 3) (y : F.base.Carrier) :
    (P.straightAtlas Ψ hΨ hε hle hge hs).transition i j y =
      (1 : Fin 3 → F.base.Carrier → Circle) i y *
        ((1 : Fin 3 → F.base.Carrier → Circle) j y)⁻¹ := by
  rw [Pi.one_apply, Pi.one_apply, Pi.one_apply, Pi.one_apply, inv_one, mul_one]
  rfl

def straightProduct (hs : s₁ < s₂) :
    U ≃ₘ⟮C.model, (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ F.base.Carrier × Circle :=
  (P.straightAtlas Ψ hΨ hε hle hge hs).productOfCoboundary (h := 1)
    (by
      intro i j y hi hj
      exact P.straightAtlas_coboundary Ψ hΨ hε hle hge hs i j y)
    (by
      intro i
      exact contMDiffOn_const)

theorem straightProduct_fst (hs : s₁ < s₂) (x : U) :
    (P.straightProduct Ψ hΨ hε hle hge hs x).1 = F.projection x := rfl

theorem straightProduct_inner (hs : s₁ < s₂) (x : U) (h : F.projection x ∈ P.innerPart s₁) :
    (P.straightProduct Ψ hΨ hε hle hge hs x).2 = (P.innerChart ⟨x, h.1⟩).2 := by
  change ((P.straightAtlas Ψ hΨ hε hle hge hs).productMap _ x).2 = _
  rw [PrincipalAtlas.productMap_eq _ (by
      intro i j y hi hj
      exact P.straightAtlas_coboundary Ψ hΨ hε hle hge hs i j y) x (0 : Fin 3) h]
  exact mul_inv_eq_iff_eq_mul.mpr
    ((P.straightAtlas_chart_inner Ψ hΨ hε hle hge hs x h).trans (mul_one _).symm)

theorem straightProduct_outer (hs : s₁ < s₂) (x : U) (h : F.projection x ∈ P.outerPart s₂) :
    (P.straightProduct Ψ hΨ hε hle hge hs x).2 =
      P.rotation s₂ (P.angle (F.projection x)) * (P.outerChart ⟨x, h.1⟩).2 ^ ε := by
  change ((P.straightAtlas Ψ hΨ hε hle hge hs).productMap _ x).2 = _
  rw [PrincipalAtlas.productMap_eq _ (by
      intro i j y hi hj
      exact P.straightAtlas_coboundary Ψ hΨ hε hle hge hs i j y) x (2 : Fin 3) h]
  exact mul_inv_eq_iff_eq_mul.mpr
    ((P.straightAtlas_chart_outer Ψ hΨ hε hle hge hs x h).trans (mul_one _).symm)

omit Ψ hΨ hε hle hge in
theorem exists_product (hs : s₁ < s₂) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∃ Φ : U ≃ₘ⟮C.model, (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ F.base.Carrier × Circle,
        (∀ x, (Φ x).1 = F.projection x) ∧
        (∀ x (h : F.projection x ∈ P.innerPart s₁), (Φ x).2 = (P.innerChart ⟨x, h.1⟩).2) ∧
        ∀ x (h : F.projection x ∈ P.outerPart s₂),
          (Φ x).2 = P.rotation s₂ (P.angle (F.projection x)) * (P.outerChart ⟨x, h.1⟩).2 ^ ε := by
  obtain ⟨ε, hε, Ψ, hΨ, hle, hge, -⟩ := exists_straightening P.transition
    P.transition_fst hs
  exact ⟨ε, hε, P.straightProduct Ψ hΨ hε hle hge hs, P.straightProduct_fst Ψ hΨ hε hle hge hs,
    P.straightProduct_inner Ψ hΨ hε hle hge hs, P.straightProduct_outer Ψ hΨ hε hle hge hs⟩

theorem symm_eq_innerChart_symm
    (Φ : U ≃ₘ⟮C.model, (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ F.base.Carrier × Circle)
    (hΦ : ∀ x, (Φ x).1 = F.projection x)
    (hin : ∀ x (h : F.projection x ∈ P.innerPart s₁), (Φ x).2 = (P.innerChart ⟨x, h.1⟩).2)
    (y : F.base.Carrier) (hy : y ∈ P.innerPart s₁) (f : Circle) :
    Φ.symm (y, f) = (P.innerChart.symm (⟨y, hy.1⟩, f)).val := by
  set x := Φ.symm (y, f)
  have hx : Φ x = (y, f) := Φ.apply_symm_apply _
  have hpx : F.projection x = y := by rw [← hΦ, hx]
  have hxi : F.projection x ∈ P.innerPart s₁ := hpx ▸ hy
  have h2 := hin x hxi
  rw [hx] at h2
  have hc : P.innerChart ⟨x, hxi.1⟩ = (⟨y, hy.1⟩, f) := by
    rw [CircleFibration.chart_eq_mk F P.innerChart P.innerChart_fst x hxi.1, ← h2]
    exact Prod.ext (Subtype.ext hpx) rfl
  have h3 : (⟨x, hxi.1⟩ : TopologicalSpace.Opens.comap F.projection P.inner) =
      P.innerChart.symm (⟨y, hy.1⟩, f) := by
    rw [← hc, Diffeomorph.symm_apply_apply]
  exact congrArg Subtype.val h3

include hε in
theorem symm_eq_outerChart_symm
    (Φ : U ≃ₘ⟮C.model, (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ F.base.Carrier × Circle)
    (hΦ : ∀ x, (Φ x).1 = F.projection x)
    (hout : ∀ x (h : F.projection x ∈ P.outerPart s₂),
      (Φ x).2 = P.rotation s₂ (P.angle (F.projection x)) * (P.outerChart ⟨x, h.1⟩).2 ^ ε)
    (y : F.base.Carrier) (hy : y ∈ P.outerPart s₂) (f : Circle) :
    Φ.symm (y, f) =
      (P.outerChart.symm (⟨y, hy.1⟩, ((P.rotation s₂ (P.angle y))⁻¹ * f) ^ ε)).val := by
  set x := Φ.symm (y, f)
  have hx : Φ x = (y, f) := Φ.apply_symm_apply _
  have hpx : F.projection x = y := by rw [← hΦ, hx]
  have hxo : F.projection x ∈ P.outerPart s₂ := hpx ▸ hy
  have h2 := hout x hxo
  rw [hx, show P.angle (F.projection x) = P.angle y by rw [hpx]] at h2
  have h2' : f = P.rotation s₂ (P.angle y) * (P.outerChart ⟨x, hxo.1⟩).2 ^ ε := h2
  have h4 : (P.outerChart ⟨x, hxo.1⟩).2 = ((P.rotation s₂ (P.angle y))⁻¹ * f) ^ ε := by
    rw [h2', inv_mul_cancel_left, zpow_sign_zpow_sign hε]
  have hc : P.outerChart ⟨x, hxo.1⟩ = (⟨y, hy.1⟩, ((P.rotation s₂ (P.angle y))⁻¹ * f) ^ ε) := by
    rw [CircleFibration.chart_eq_mk F P.outerChart P.outerChart_fst x hxo.1, h4]
    exact Prod.ext (Subtype.ext hpx) rfl
  have h3 : (⟨x, hxo.1⟩ : TopologicalSpace.Opens.comap F.projection P.outer) =
      P.outerChart.symm (⟨y, hy.1⟩, ((P.rotation s₂ (P.angle y))⁻¹ * f) ^ ε) := by
    rw [← hc, Diffeomorph.symm_apply_apply]
  exact congrArg Subtype.val h3

theorem exists_product_ports (hs : s₁ < s₂)
    (β₁ β₂ : Circle × EuclideanHalfSpace 1 → F.base.Carrier)
    (hβ₁ : ∀ a, β₁ a ∈ P.innerPart s₁) (hβ₂ : ∀ a, β₂ a ∈ P.outerPart s₂)
    (e : Circle → Circle) (he : ContMDiff (𝓡 1) (𝓡 1) ∞ e)
    (hangle : ∀ a, P.angle (β₂ a) = e a.1) :
    ∃ Φ : U ≃ₘ⟮C.model, (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ F.base.Carrier × Circle,
      (∀ x, (Φ x).1 = F.projection x) ∧
      ∃ ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus, (∀ t, (ψ t).1 = t.1) ∧
        (∀ p : Torus × EuclideanHalfSpace 1, Φ.symm (β₁ (p.1.1, p.2), p.1.2) =
          (P.innerChart.symm (⟨β₁ (p.1.1, p.2), (hβ₁ _).1⟩, p.1.2)).val) ∧
        ∀ p : Torus × EuclideanHalfSpace 1, Φ.symm (β₂ (p.1.1, p.2), p.1.2) =
          (P.outerChart.symm (⟨β₂ (p.1.1, p.2), (hβ₂ _).1⟩, (ψ p.1).2)).val := by
  obtain ⟨ε, hε, Φ, hΦ, hin, hout⟩ := P.exists_product hs
  refine ⟨Φ, hΦ, (fibreRotate (fun t => P.rotation s₂ (e t))
    ((P.contMDiff_rotation s₂).comp he) ε hε).symm, fun t => rfl,
    fun p => P.symm_eq_innerChart_symm Φ hΦ hin _ (hβ₁ _) _, fun p => ?_⟩
  rw [P.symm_eq_outerChart_symm hε Φ hΦ hout _ (hβ₂ _), fibreRotate_symm_apply, hangle]

theorem exists_product_portCollars (hs : s₁ < s₂)
    (β₁ β₂ : Circle × EuclideanHalfSpace 1 → F.base.Carrier)
    (hβ₁ : ∀ a, β₁ a ∈ P.innerPart s₁) (hβ₂ : ∀ a, β₂ a ∈ P.outerPart s₂)
    (e : Circle → Circle) (he : ContMDiff (𝓡 1) (𝓡 1) ∞ e)
    (hangle : ∀ a, P.angle (β₂ a) = e a.1) (col₁ col₂ : Torus × EuclideanHalfSpace 1 → C.Carrier)
    (hcol₁ : ∀ p, p ∈ halfCollarSource →
      col₁ p = ((P.innerChart.symm (⟨β₁ (p.1.1, p.2), (hβ₁ _).1⟩, p.1.2)).val : C.Carrier))
    (hcol₂ : ∀ p, p ∈ halfCollarSource →
      col₂ p = ((P.outerChart.symm (⟨β₂ (p.1.1, p.2), (hβ₂ _).1⟩, p.1.2)).val : C.Carrier)) :
    ∃ Φ : U ≃ₘ⟮C.model, (SurfaceModel.model F.base.kind).prod (𝓡 1)⟯ F.base.Carrier × Circle,
      (∀ x, (Φ x).1 = F.projection x) ∧
      ∃ ψ : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus, (∀ t, (ψ t).1 = t.1) ∧
        (∀ p, p ∈ halfCollarSource →
          col₁ p = ((Φ.symm (β₁ (p.1.1, p.2), p.1.2) : U) : C.Carrier)) ∧
        ∀ p, p ∈ halfCollarSource →
          col₂ (ψ p.1, p.2) = ((Φ.symm (β₂ (p.1.1, p.2), p.1.2) : U) : C.Carrier) := by
  obtain ⟨Φ, hΦ, ψ, hψ, h₁, h₂⟩ := P.exists_product_ports hs β₁ β₂ hβ₁ hβ₂ e he hangle
  refine ⟨Φ, hΦ, ψ, hψ, fun p hp => ?_, fun p hp => ?_⟩
  · rw [hcol₁ p hp, h₁]
  · rw [hcol₂ (ψ p.1, p.2) hp, h₂]
    exact congrArg (fun a => ((P.outerChart.symm (⟨β₂ (a, p.2), (hβ₂ (a, p.2)).1⟩,
      (ψ p.1).2)).val : C.Carrier)) (hψ p.1)

end Atlas

end AnnulusChartPair

end GC.Seifert
