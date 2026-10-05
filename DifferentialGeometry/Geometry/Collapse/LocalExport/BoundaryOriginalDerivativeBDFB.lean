import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryGlobalDerivativeBDFB
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Boundary.LipschitzDerivativeBDFB
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedInterior
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceAugmented
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAffineHeightTransport
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInteriorTransfer
import DifferentialGeometry.Geometry.Collapse.BoundaryCloud.SupportListsCollar
import DifferentialGeometry.Analysis.Calculus.Cutoff.BoundaryBlockProfile

/-!
# BCG01's derivative clause on the original carrier: `‖D F_∂‖ ≤ bder₀` (lane B-DFB, G3)

Blueprint `master207B.tex`, BCG01 (B:8727–8820, the clause `‖DF‖ ≤ bder₀`) and the input of A3c:
the ACTUAL augmented map `F_∂ = S.boundaryOriginalMap` of a stored boundary supply
`S : BoundarySupplyCore` (BAUG-A's `F_int^W ⊕ ⊕_b ℝ²_b`, interior part `S.interiorMapW_BAUGA`,
boundary slots the packet's actual collar blocks) has `‖dF_∂(v)‖ ≤ bder₀ |v|_g` at EVERY point of
the original carrier `W` (boundary included), for the original metric `g`, with the numerical
constant `bder₀ = 1000 (N_TCP + 2) P₀² + 2 P_B` (CGP02's interior constant plus BCG.0's profile
constant), in the separated (nonproduct) branch of T3B.

* `norm_mvfderiv_boundaryAugmentedMap_le_BDFB` (generic): the augmented map's derivative is at most
  `a + (3/2) c` when the interior part's is at most `a` and the boundary blocks' derivatives sum to
  at most `c` (`‖(planeAxis u, v)‖² ≤ 2 ‖(u, v)‖²`, square sums);
* `ofReal_le_distanceToBoundary_of_image_ball_BDFB`: a `ĝ`-ball of `W°` whose image is the `g`-ball
  of the same radius `R` forces `D(j) ≥ R` (that `g`-ball misses `∂W`);
  `four_lt_distanceToBoundary_of_transport_BDFB`: hence the points of the inner ball
  `B_ĝ(j, r)` (`4r ≤ R`, `D(j) > 10`) have `D > 4`;
* `four_lt_distanceToBoundary_of_mem_tsupport_slot_BDFB`: every NON-scale interior slot of
  `F_int` has its closed support in `{D > 4}` (circle, slim, `edgeB`: T3B's consumer balls; zero:
  the `400 r` zero balls; `E'`: `{D > 10}`); `intSlotW_eventuallyEq_zero_BDFB`: near a point with
  `D < 4` every non-scale slot of `F_int^W` vanishes;
* `norm_mvfderiv_interiorMapW_le_BDFB`: `‖dF_int^W(v)‖ ≤ 1000 (N_TCP + 2) P₀² |v|_g` on `W` —
  on `{D ≥ 4}` through `val` (`ĝ = g°` there, G2's `norm_mvfderiv_interiorMapOn_le_BDFB`), on
  `{D < 4}` only the scale slot `(0, ρ)` survives and `|dρ(v)| ≤ Λ |v|_g` (G3a, corners allowed);
* **`BoundarySupplyCore.norm_mvfderiv_boundaryOriginalMap_le_BDFB`** (the frozen target G0):
  `‖dF_∂(v)‖ ≤ boundaryDerivBound_BDFB · √(g(v, v))` (boundary blocks:
  `BoundaryCollarPacket.sum_norm_mvfderiv_block_le`, collar disjointness from the separated branch).
* Consumer: `BoundarySupply.norm_mvfderiv_boundaryOriginalMap_le_BDFB` (the full supply with
  BCG02's certificates, in the separated branch of its `geometric_cases`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry GC.Endpoint
open DifferentialGeometry.Analysis DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

/-! ### Numerical constants -/

/-- BCG.0's boundary profile constant `P_B ≥ 1` (`‖𝓑'‖∞, ‖𝓑''‖∞ ≤ P_B`), numerical. -/
def boundaryProfileBound_BDFB : ℝ :=
  Classical.choose exists_boundaryBlock_derivative_bounds

/-- **BCG01's early derivative constant** `bder₀ = 1000 (N_TCP + 2) P₀² + 2 P_B` (numerical: fixed
before `Δ`, the noncollapsing constant, the number of charts and the scale range). -/
def boundaryDerivBound_BDFB : ℝ :=
  1000 * ((tcp01SupportBound : ℝ) + 2) * cgpProfileBound ^ 2 + 2 * boundaryProfileBound_BDFB

theorem one_le_boundaryProfileBound_BDFB : 1 ≤ boundaryProfileBound_BDFB :=
  (Classical.choose_spec exists_boundaryBlock_derivative_bounds).1

theorem norm_fderiv_boundaryBlock_le_BDFB (t : ℝ) :
    ‖fderiv ℝ boundaryBlock t‖ ≤ boundaryProfileBound_BDFB :=
  (Classical.choose_spec exists_boundaryBlock_derivative_bounds).2.1 t

/-! ### Generic calculus of the augmented map -/

section Generic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- `mvfderiv` only depends on the germ. -/
theorem mvfderiv_congr_BDFB {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f f' : M → F}
    {x : M} (h : f =ᶠ[𝓝 x] f') (v : TangentSpace I x) :
    mvfderiv I f x v = mvfderiv I f' x v := by
  rw [mvfderiv_apply_LC, mvfderiv_apply_LC, h.mfderiv_eq]
  rfl

/-- A function that vanishes near `x` has zero `mvfderiv` at `x`. -/
theorem mvfderiv_eq_zero_of_eventuallyEq_zero_BDFB {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : M → F} {x : M} (h : f =ᶠ[𝓝 x] fun _ => 0) (v : TangentSpace I x) :
    mvfderiv I f x v = 0 := by
  rw [mvfderiv_congr_BDFB h, mvfderiv_apply_LC, mfderiv_const]
  rfl

/-- Chain rule with a continuous linear map on the target. -/
theorem mvfderiv_clm_comp_BDFB {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) {f : M → F} {x : M}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f x) (v : TangentSpace I x) :
    mvfderiv I (fun y => L (f y)) x v = L (mvfderiv I f x v) := by
  have h := L.hasFDerivAt.hasMFDerivAt.comp x hf.hasMFDerivAt
  rw [mvfderiv_apply_LC, mvfderiv_apply_LC]
  exact congrArg (fun T => T v) h.mfderiv

/-- The `i`-th component of the derivative of a differentiable map into a `BlockSpace` is the
derivative of the `i`-th component. -/
theorem mvfderiv_blockSpace_apply_BDFB {κ : Type*} [Fintype κ]
    {F : M → BlockSpace (fun _ : κ => ℝ²)} {x : M}
    (hF : MDifferentiableAt I 𝓘(ℝ, BlockSpace (fun _ : κ => ℝ²)) F x) (v : TangentSpace I x)
    (i : κ) : mvfderiv I F x v i = mvfderiv I (fun y => F y i) x v := by
  let pr : BlockSpace (fun _ : κ => ℝ²) →L[ℝ] WithLp 2 (ℝ² × ℝ) :=
    PiLp.proj 2 (fun _ : κ => WithLp 2 (ℝ² × ℝ)) i
  have h := pr.hasFDerivAt.hasMFDerivAt.comp x hF.hasMFDerivAt
  have hfun : (pr ∘ F) = fun y => F y i := rfl
  rw [hfun] at h
  rw [mvfderiv_apply_LC, mvfderiv_apply_LC, h.mfderiv]
  rfl

/-- The plane encoding at most doubles squared norms: `‖(planeAxis u, v)‖² ≤ 2 ‖(u, v)‖²`. -/
theorem norm_planeBlockEmbed_sq_le_BDFB (z : ℝ × ℝ) :
    ‖planeBlockEmbed_BAUGA z‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, planeBlockEmbed_fst_BAUGA, planeBlockEmbed_snd_BAUGA,
    norm_planeAxis, Real.norm_eq_abs, sq_abs, sq_abs]
  have h1 : |z.1| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le z
  have h2 : |z.2| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le z
  have h1' := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (abs_nonneg _) h2 2
  rw [sq_abs] at h1' h2'
  linarith

/-- The pair `(0, r)` of a slot has norm `|r|`. -/
theorem norm_toLp_zero_prod_BDFB (r : ℝ) :
    ‖(WithLp.toLp 2 ((0 : ℝ²), r) : WithLp 2 (ℝ² × ℝ))‖ = |r| := by
  rw [WithLp.prod_norm_eq_of_L2]
  have h1 : (WithLp.toLp 2 ((0 : ℝ²), r) : WithLp 2 (ℝ² × ℝ)).fst = 0 := rfl
  have h2 : (WithLp.toLp 2 ((0 : ℝ²), r) : WithLp 2 (ℝ² × ℝ)).snd = r := rfl
  rw [h1, h2, norm_zero, Real.norm_eq_abs, sq_abs]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add]
  exact Real.sqrt_sq_eq_abs r

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The derivative of the augmented map.** If the interior part `Fint` and every boundary block
`B b` are `C^n` (`n ≠ 0`) at `x`, `‖dFint(v)‖ ≤ a` and `Σ_b ‖dB_b(v)‖ ≤ c`, then
`‖dF_∂(v)‖ ≤ a + (3/2) c` (`F_∂ = boundaryAugmentedMap_BAUGA Fint B`). -/
theorem norm_mvfderiv_boundaryAugmentedMap_le_BDFB {n : WithTop ℕ∞} (hn : n ≠ 0)
    {Fint : M → BlockSpace (fun _ : ι => ℝ²)} {Bk : κ → M → ℝ × ℝ} {x : M}
    (hF : ContMDiffAt I 𝓘(ℝ, BlockSpace (fun _ : ι => ℝ²)) n Fint x)
    (hB : ∀ b, ContMDiffAt I 𝓘(ℝ, ℝ × ℝ) n (Bk b) x) (v : TangentSpace I x) {a c : ℝ}
    (ha : ‖mvfderiv I Fint x v‖ ≤ a) (hc : ∑ b, ‖mvfderiv I (Bk b) x v‖ ≤ c) :
    ‖mvfderiv I (boundaryAugmentedMap_BAUGA Fint Bk) x v‖ ≤ a + 3 / 2 * c := by
  have hFd : MDifferentiableAt I 𝓘(ℝ, BlockSpace (fun _ : ι => ℝ²)) Fint x :=
    hF.mdifferentiableAt hn
  have hBd : ∀ b, MDifferentiableAt I 𝓘(ℝ, ℝ × ℝ) (Bk b) x := fun b =>
    (hB b).mdifferentiableAt hn
  have hAug : ContMDiffAt I 𝓘(ℝ, BlockSpace (fun _ : ι ⊕ κ => ℝ²)) n
      (boundaryAugmentedMap_BAUGA Fint Bk) x := by
    have hFpi := ((PiLp.continuousLinearEquiv 2 ℝ fun _ : ι => WithLp 2 (ℝ² × ℝ) :
      BlockSpace (fun _ : ι => ℝ²) →L[ℝ] ∀ _ : ι, WithLp 2 (ℝ² × ℝ))).contMDiff.contMDiffAt.comp
        x hF
    have hpi : ContMDiffAt I 𝓘(ℝ, ∀ _ : ι ⊕ κ, WithLp 2 (ℝ² × ℝ)) n
        (fun p => Sum.elim (fun i => Fint p i) (fun b => planeBlockEmbed_BAUGA (Bk b p))) x := by
      refine contMDiffAt_pi_space.2 fun t => ?_
      rcases t with i | b
      · exact contMDiffAt_pi_space.1 hFpi i
      · exact planeBlockEmbed_BAUGA.contMDiff.contMDiffAt.comp x (hB b)
    exact ((PiLp.continuousLinearEquiv 2 ℝ fun _ : ι ⊕ κ => WithLp 2 (ℝ² × ℝ)).symm :
      (∀ _ : ι ⊕ κ, WithLp 2 (ℝ² × ℝ)) →L[ℝ] BlockSpace (fun _ : ι ⊕ κ => ℝ²)).contMDiff.contMDiffAt.comp
        x hpi
  have hAd := hAug.mdifferentiableAt hn
  have hinl : ∀ i, mvfderiv I (boundaryAugmentedMap_BAUGA Fint Bk) x v (Sum.inl i) =
      mvfderiv I Fint x v i := by
    intro i
    rw [mvfderiv_blockSpace_apply_BDFB hAd, mvfderiv_blockSpace_apply_BDFB hFd]
    rfl
  have hinr : ∀ b, mvfderiv I (boundaryAugmentedMap_BAUGA Fint Bk) x v (Sum.inr b) =
      planeBlockEmbed_BAUGA (mvfderiv I (Bk b) x v) := by
    intro b
    rw [mvfderiv_blockSpace_apply_BDFB hAd]
    exact mvfderiv_clm_comp_BDFB planeBlockEmbed_BAUGA (hBd b) v
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  have hs0 : 0 ≤ ∑ b, ‖mvfderiv I (Bk b) x v‖ := Finset.sum_nonneg fun b _ => norm_nonneg _
  have hc0 : 0 ≤ c := hs0.trans hc
  have hsq : ‖mvfderiv I (boundaryAugmentedMap_BAUGA Fint Bk) x v‖ ^ 2 ≤ (a + 3 / 2 * c) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
    simp only [hinl, hinr]
    have h1 : ∑ i, ‖mvfderiv I Fint x v i‖ ^ 2 = ‖mvfderiv I Fint x v‖ ^ 2 :=
      (PiLp.norm_sq_eq_of_L2 _ _).symm
    have h2 : ∑ b, ‖planeBlockEmbed_BAUGA (mvfderiv I (Bk b) x v)‖ ^ 2 ≤
        2 * (∑ b, ‖mvfderiv I (Bk b) x v‖) ^ 2 := by
      calc ∑ b, ‖planeBlockEmbed_BAUGA (mvfderiv I (Bk b) x v)‖ ^ 2
          ≤ ∑ b, 2 * ‖mvfderiv I (Bk b) x v‖ ^ 2 :=
            Finset.sum_le_sum fun b _ => norm_planeBlockEmbed_sq_le_BDFB _
        _ = 2 * ∑ b, ‖mvfderiv I (Bk b) x v‖ ^ 2 := by rw [Finset.mul_sum]
        _ ≤ 2 * (∑ b, ‖mvfderiv I (Bk b) x v‖) ^ 2 := by
            gcongr
            exact Finset.sum_sq_le_sq_sum_of_nonneg fun b _ => norm_nonneg _
    have h3 : (∑ b, ‖mvfderiv I (Bk b) x v‖) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hs0 hc 2
    have h4 : ‖mvfderiv I Fint x v‖ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (norm_nonneg _) ha 2
    rw [h1]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

end Generic

/-! ### Distance to the boundary through transported balls -/

section Transport

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier]

/-- **A transported ball misses the boundary**: if `ι B_ĝ(j, R) = B_g(j, R)`, then `D(j) ≥ R`
(a boundary point at `g`-distance `< R` from `j` would lie in `ι W°`). -/
theorem ofReal_le_distanceToBoundary_of_image_ball_BDFB
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)) {j : W.pieceInterior ⊤} {R : ℝ} :
    letI := inducedMetricSpace ĝ
    Subtype.val '' Metric.ball j R = riemannianBallOf g j.val R →
    ENNReal.ofReal R ≤ distanceToBoundary W g j.val := by
  let _ := inducedMetricSpace ĝ
  intro hball
  unfold distanceToBoundary
  refine le_iInf fun q => ?_
  by_contra hlt
  push Not at hlt
  have hq : (q : W.Carrier) ∈ riemannianBallOf g j.val R := hlt
  rw [← hball] at hq
  obtain ⟨y, -, hy⟩ := hq
  have hyI : (y : W.Carrier) ∈ W.model.interior W.Carrier := by
    rw [← coe_pieceInterior_top_BDRY1]
    exact y.2
  rw [hy, ← W.model.compl_boundary] at hyI
  exact hyI q.2

/-- **Inner transported balls stay in `{D > 4}`**: with `ι B_ĝ(j, R) = B_g(j, R)`,
`d_g = d_ĝ` on `B_ĝ(j, R')`, `D(j) > 10`, `4r ≤ R` and `r ≤ R'`, every point of `B_ĝ(j, r)` has
`D > 4`. -/
theorem four_lt_distanceToBoundary_of_transport_BDFB
    (g : SmoothRiemannianMetric W.model W.Carrier)
    (ĝ : SmoothRiemannianMetric 𝓘(ℝ, E3) (W.pieceInterior ⊤)) {j x : W.pieceInterior ⊤}
    {r R R' : ℝ} (h4 : 4 * r ≤ R) (hrR' : r ≤ R') :
    letI := inducedMetricSpace ĝ
    Subtype.val '' Metric.ball j R = riemannianBallOf g j.val R →
    (∀ y ∈ Metric.ball j R', ∀ z ∈ Metric.ball j R',
      riemannianEDistOf g y.val z.val = edist y z) →
    ENNReal.ofReal 10 < distanceToBoundary W g j.val → x ∈ Metric.ball j r →
    ENNReal.ofReal 4 < distanceToBoundary W g x.val := by
  let _ := inducedMetricSpace ĝ
  intro hball hdist hj hx
  have hxr : dist x j < r := hx
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hxr
  have hR := ofReal_le_distanceToBoundary_of_image_ball_BDFB g ĝ hball
  have hrc : ENNReal.ofReal (r + 4) ≤ distanceToBoundary W g j.val := by
    by_cases h2 : r ≤ 2
    · exact le_of_lt (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by linarith)) hj)
    · exact (ENNReal.ofReal_le_ofReal (by linarith)).trans hR
  have hjb : j ∈ Metric.ball j R' := mem_ball_self (lt_of_lt_of_le hr hrR')
  have hxb : x ∈ Metric.ball j R' := lt_of_lt_of_le hxr hrR'
  have hxg : x.val ∈ riemannianBallOf g j.val r := by
    change riemannianEDistOf g j.val x.val < ENNReal.ofReal r
    rw [hdist j hjb x hxb, edist_dist, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hxr
  exact riemannianBallOf_subset_lt_distanceToBoundary_BDRY1 W g hr.le (by norm_num) hrc hxg

end Transport

/-! ### The interior part on the original carrier -/

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

namespace BoundarySupplyCore

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz
    W g δn n B oM)

/-- **The non-scale interior slots live in `{D > 4}`**: the closed support of every slot of BAUG-A's
interior formula other than the scale slot lies in `{D > 4}` (circle, slim, `edgeB`: T3B's
transported consumer balls `4K₀ρ(j)`; zero: the transported `400 r` zero balls; `E'`: `{D > 10}`). -/
theorem four_lt_distanceToBoundary_of_mem_tsupport_slot_BDFB (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) {t : S.IntTag_BAUGA}
    (ht : t ≠ S.scaleTag_BAUGA) {x : W.pieceInterior ⊤}
    (hx : x ∈ tsupport (fun y => S.interiorMapOn_BAUGA y t)) :
    ENNReal.ofReal 4 < distanceToBoundary W g x.val := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hK0 := consumerConstant_ge_BAUGA hΔ hV hβ1 hb
  rcases t with j | j | j | i | bb
  · -- circle centre
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    have hj1 : ENNReal.ofReal 10 < distanceToBoundary W g j.1 :=
      (S.family.circle.centres_subset hj).1
    have htr := S.transport_spec.2.1 j.1 hj1
    have hrj := S.rho_pos j.1
    have hxs : x ∈ Metric.ball j.1 (200 * S.rho j.1) :=
      S.family.circle.tsupport_subset_ball j.1 hj
        (tsupport_blockSlot_subset_BAUGA (fun _ => S.rho j.1) (S.family.circle.cutoff j.1)
          (S.family.circle.coord_BAUGA j.1) hx)
    exact four_lt_distanceToBoundary_of_transport_BDFB g S.completion.metric
      (by nlinarith) (by nlinarith) htr.1 htr.2 hj1 hxs
  · -- slim centre
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    have hj1 : ENNReal.ofReal 10 < distanceToBoundary W g j.1 :=
      (S.family.slim.centres_subset hj).1
    have htr := S.transport_spec.2.1 j.1 hj1
    have hrj := S.rho_pos j.1
    have hpos := mul_pos hΔ hrj
    have hS : tsupport (S.family.slim.cutoff_BCNT j.1) ⊆
        Metric.ball j.1 (10 ^ 6 * Δ * S.rho j.1) :=
      (S.family.slim.tsupport_cutoff_subset_BCNT j.1).trans
        (closedBall_subset_ball (by nlinarith))
    have hxs : x ∈ Metric.ball j.1 (10 ^ 6 * Δ * S.rho j.1) :=
      hS (tsupport_blockSlot_subset_BAUGA (fun _ => S.rho j.1) (S.family.slim.cutoff_BCNT j.1)
        (fun y => planeAxis ((S.family.slim.centre j.1 hj).coord_BCG2 y)) hx)
    exact four_lt_distanceToBoundary_of_transport_BDFB g S.completion.metric
      (by nlinarith) (by nlinarith) htr.1 htr.2 hj1 hxs
  · -- revised edge centre
    have hj := (Set.Finite.mem_toFinset _).mp j.2
    have hj2 : ENNReal.ofReal 20 < distanceToBoundary W g j.1 :=
      S.family.edgeB.centres_subset hj
    have hj1 : ENNReal.ofReal 10 < distanceToBoundary W g j.1 :=
      lt_trans (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by norm_num, by norm_num⟩) hj2
    have htr := S.transport_spec.2.1 j.1 hj1
    have hrj := S.rho_pos j.1
    have hpos := mul_pos hΔ hrj
    have hS := (S.family.tsupport_edgeB_cutoff_subset_BAUGA hΛ hΔ hμ hτ hΔΛ hj).2.2
    have hxs : x ∈ Metric.ball j.1 (100 * Δ * S.rho j.1) :=
      hS (tsupport_blockSlot_subset_BAUGA (fun _ => S.rho j.1) (S.family.edgeB.cutoff_BAUGA j.1)
        (fun y => planeAxis (S.family.edgeB.coord_BAUGA j.1 y)) hx)
    exact four_lt_distanceToBoundary_of_transport_BDFB g S.completion.metric
      (by nlinarith) (by nlinarith) htr.1 htr.2 hj1 hxs
  · -- zero centre
    have hi := (Set.Finite.mem_toFinset _).mp i.2
    have hi1 : ENNReal.ofReal 10 < distanceToBoundary W g i.1 :=
      S.family.zero.centres_subset hi
    have hI := S.transport_spec.2.2.2.2.2.1 i.1 hi
    have hcen := S.family.zero.zero_center i.1 hi
    have hr := (S.family.zero.zero i.1 hi).radius_pos
    have hspec := (S.family.zero.zero i.1 hi).radial_spec.2.2.2.2.2.2.2.2.2.2.2
    have hts := hspec.choose_spec.2.2.2.2.2.1
    have hball : tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((S.family.zero.zero i.1 hi).radial y)) ⊆
        Metric.ball i.1 (S.family.zero.zero i.1 hi).radius := by
      intro y hy
      have h := (hts hy).2
      have h' : ((S.family.zero.zero i.1 hi).radius)⁻¹ *
          dist y (S.family.zero.zero i.1 hi).center < 9 / 10 + e := h
      rw [hcen, inv_mul_lt_iff₀ hr] at h'
      rw [Metric.mem_ball]
      nlinarith
    have hxs : x ∈ Metric.ball i.1 (S.family.zero.zero i.1 hi).radius :=
      hball (tsupport_blockSlot_subset_BAUGA (fun _ => (S.family.zero.zero i.1 hi).radius)
        (fun y => Calculus.annularCutoff Calculus.cutoffProfile
          ((S.family.zero.zero i.1 hi).radial y))
        (fun y => planeAxis ((S.family.zero.zero i.1 hi).radial y)) hx)
    exact four_lt_distanceToBoundary_of_transport_BDFB g S.completion.metric
      (by linarith) (by linarith) hI.1 hI.2 hi1 hxs
  · cases bb
    · exact absurd rfl ht
    · -- the weak-edge block E'
      have h : ENNReal.ofReal 10 < distanceToBoundary W g x :=
        S.family.tsupport_edgeBMarker_subset_region_BAUGA hΛ hΔ hμ hτ hΔΛ
          ((tsupport_blockSlot_subset_BAUGA (fun y : W.pieceInterior ⊤ => S.rho y)
            S.family.edgeBMarker_BAUGA
            (fun y => planeAxis (S.family.edgeBHeight_BAUGA y))) hx)
      exact lt_trans (ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by norm_num, by norm_num⟩) h

/-- **Near a point with `D < 4` every non-scale slot of `F_int^W` vanishes.** -/
theorem intSlotW_eventuallyEq_zero_BDFB (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (he : e ≤ 1 / 10) {t : S.IntTag_BAUGA} (ht : t ≠ S.scaleTag_BAUGA) {p : W.Carrier}
    (hp : distanceToBoundary W g p < ENNReal.ofReal 4) :
    S.intSlotW_BAUGA t =ᶠ[𝓝 p] fun _ => 0 := by
  have hO : ∀ᶠ y in 𝓝 p, distanceToBoundary W g y < ENNReal.ofReal 4 :=
    upperSemicontinuous_distanceToBoundary_BDRY1 W g p _ hp
  filter_upwards [hO] with y hy
  simp only [intSlotW_BAUGA, ht, ↓reduceIte]
  by_cases hyr : ∃ x : W.pieceInterior ⊤, x.val = y
  · obtain ⟨x, rfl⟩ := hyr
    rw [Subtype.val_injective.extend_apply]
    have hx : x ∉ tsupport (fun z => S.interiorMapOn_BAUGA z t) := fun hx =>
      (lt_irrefl _) (hy.trans
        (S.four_lt_distanceToBoundary_of_mem_tsupport_slot_BDFB hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he
          ht hx))
    exact image_eq_zero_of_notMem_tsupport (f := fun z => S.interiorMapOn_BAUGA z t) hx
  · rw [Function.extend_apply' _ _ _ hyr]
    rfl

/-- **`F_int^W` on `{D < 4}`**: only the scale slot `(0, ρ)` survives, so
`‖dF_int^W(v)‖ = |dρ(v)| ≤ Λ |v|_g` (the scale is `Λ`-Lipschitz for `g`; corners allowed). -/
theorem norm_mvfderiv_interiorMapW_le_of_lt_four_BDFB (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) {p : W.Carrier}
    (hp : distanceToBoundary W g p < ENNReal.ofReal 4) (v : TangentSpace W.model p) :
    ‖mvfderiv W.model S.interiorMapW_BAUGA p v‖ ≤ Λ * Real.sqrt (g.inner p v v) := by
  have hF : MDifferentiableAt W.model 𝓘(ℝ, BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
      S.interiorMapW_BAUGA p :=
    (S.contMDiff_interiorMapW_BAUGA hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he p).mdifferentiableAt (by simp)
  have hcomp : ∀ t, mvfderiv W.model S.interiorMapW_BAUGA p v t =
      mvfderiv W.model (S.intSlotW_BAUGA t) p v := fun t =>
    mvfderiv_blockSpace_apply_BDFB hF v t
  have hzero : ∀ t, t ≠ S.scaleTag_BAUGA → mvfderiv W.model S.interiorMapW_BAUGA p v t = 0 := by
    intro t ht
    rw [hcomp]
    exact mvfderiv_eq_zero_of_eventuallyEq_zero_BDFB
      (S.intSlotW_eventuallyEq_zero_BDFB hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he ht hp) v
  let L0 : ℝ →L[ℝ] WithLp 2 (ℝ² × ℝ) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ² ℝ).symm : (ℝ² × ℝ) →L[ℝ] WithLp 2 (ℝ² × ℝ)).comp
      (ContinuousLinearMap.inr ℝ ℝ² ℝ)
  have hρd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) S.rho p :=
    (S.scale_spec.1 p).mdifferentiableAt (by simp)
  have hscale : mvfderiv W.model S.interiorMapW_BAUGA p v S.scaleTag_BAUGA =
      WithLp.toLp 2 ((0 : ℝ²), mvfderiv W.model S.rho p v) := by
    rw [hcomp]
    have hfun : S.intSlotW_BAUGA S.scaleTag_BAUGA = fun y => L0 (S.rho y) := by
      funext y
      unfold intSlotW_BAUGA
      split_ifs with h
      · rfl
      · exact absurd rfl h
    rw [hfun]
    exact mvfderiv_clm_comp_BDFB L0 hρd v
  have hsq : ‖mvfderiv W.model S.interiorMapW_BAUGA p v‖ ^ 2 =
      |mvfderiv W.model S.rho p v| ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Finset.sum_eq_single S.scaleTag_BAUGA
      (fun t _ ht => by rw [hzero t ht, norm_zero]; ring) (by simp), hscale,
      norm_toLp_zero_prod_BDFB]
  have hnorm : ‖mvfderiv W.model S.interiorMapW_BAUGA p v‖ = |mvfderiv W.model S.rho p v| :=
    (pow_left_inj₀ (norm_nonneg _) (abs_nonneg _) two_ne_zero).mp hsq
  rw [hnorm]
  exact abs_mvfderiv_le_of_lipschitz_riemannianEDistOf_BDFB g
    ((S.scale_spec.1 p).of_le (by exact_mod_cast le_top)) hΛ Filter.univ_mem
    (fun x _ y _ => S.scale_spec.2.1 x y) v

/-- **`F_int^W` on `{D ≥ 4}`**: through `val`, `dF_int^W(dval u) = dF_int(u)` and
`g(dval u, dval u) = ĝ(u, u)` (`ĝ = g°` on `{D ≥ 4}`), so G2's bound on `(W°, ĝ)` transfers. -/
theorem norm_mvfderiv_interiorMapW_le_of_four_le_BDFB (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ)
    (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V)
    (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10) (hΔ1 : 1 ≤ Δ)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax)
    (he40 : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : σs ∈ Icc (0 : ℝ) 1)
    (hσc : σc ∈ Icc (0 : ℝ) 1) (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    {p : W.Carrier} (hp : ENNReal.ofReal 4 ≤ distanceToBoundary W g p)
    (v : TangentSpace W.model p) :
    ‖mvfderiv W.model S.interiorMapW_BAUGA p v‖ ≤
      1000 * ((tcp01SupportBound : ℝ) + 2) * cgpProfileBound ^ 2 * Real.sqrt (g.inner p v v) := by
  have hpos : 0 < distanceToBoundary W g p :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num)) hp
  have hint := mem_interior_of_distanceToBoundary_pos_BDRY1 W g hpos
  have hmem : p ∈ W.pieceInterior ⊤ := by
    rw [← SetLike.mem_coe, coe_pieceInterior_top_BDRY1]
    exact hint
  obtain ⟨x, rfl⟩ : ∃ x : W.pieceInterior ⊤, x.val = p := ⟨⟨p, hmem⟩, rfl⟩
  obtain ⟨u, rfl⟩ := ((isLocalDiffeomorph_pieceInterior_val W ⊤).mfderivToContinuousLinearEquiv
    (by simp) x).surjective v
  have hcoe : ((isLocalDiffeomorph_pieceInterior_val W ⊤).mfderivToContinuousLinearEquiv
      (by simp) x) u = mfderiv 𝓘(ℝ, E3) W.model Subtype.val x u := rfl
  rw [hcoe]
  have heq : ∀ y : W.pieceInterior ⊤, ENNReal.ofReal 4 ≤ distanceToBoundary W g y →
      S.completion.metric.inner y = (pieceInteriorMetric W g ⊤).inner y := fun y hy =>
    S.completion.inner_eq_on_agree y (S.completion.far_subset_agree hy)
  have hF0 := S.contMDiff_interiorMapW_BAUGA hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he
  have hF := (hF0 x.val).mdifferentiableAt (by simp)
  have hD := mvfderiv_comp_val_BCG7 W S.interiorMapW_BAUGA x hF u
  have hfun : (fun y : W.pieceInterior ⊤ => S.interiorMapW_BAUGA y) = S.interiorMapOn_BAUGA :=
    funext S.interiorMapW_val_BAUGA
  have hD2 := (congrArg (fun f => mvfderiv 𝓘(ℝ, E3) f x u) hfun).symm.trans hD
  rw [← hD2, inner_mfderiv_val_BCG7 W g S.completion.metric heq x hp u u]
  exact S.norm_mvfderiv_interiorMapOn_le_BDFB hΛ hΔ1 hμ hτ hLΛ hLmax he40 hT hσs hσc hγc hεr x u

/-- **CGP02 for `F_int^W` on the original carrier `(W, g)`**:
`‖dF_int^W(v)‖ ≤ 1000 (N_TCP + 2) P₀² |v|_g` at every point of `W`, boundary included. -/
theorem norm_mvfderiv_interiorMapW_le_BDFB (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (he : e ≤ 1 / 10) (hΔ1 : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he40 : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : σs ∈ Icc (0 : ℝ) 1) (hσc : σc ∈ Icc (0 : ℝ) 1)
    (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1) (p : W.Carrier)
    (v : TangentSpace W.model p) :
    ‖mvfderiv W.model S.interiorMapW_BAUGA p v‖ ≤
      1000 * ((tcp01SupportBound : ℝ) + 2) * cgpProfileBound ^ 2 * Real.sqrt (g.inner p v v) := by
  by_cases hp : ENNReal.ofReal 4 ≤ distanceToBoundary W g p
  · exact S.norm_mvfderiv_interiorMapW_le_of_four_le_BDFB hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ
      hLmax he40 hT hσs hσc hγc hεr hp v
  · push Not at hp
    refine (S.norm_mvfderiv_interiorMapW_le_of_lt_four_BDFB hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hp
      v).trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    have hP1 := cgpProfileBound_spec.1
    have hP2 : 1 ≤ cgpProfileBound ^ 2 := one_le_pow₀ hP1
    have hΛ1 : Λ ≤ 1 := by nlinarith
    have hN0 : (0 : ℝ) ≤ tcp01SupportBound := Nat.cast_nonneg _
    have h2 : 2000 ≤ 1000 * ((tcp01SupportBound : ℝ) + 2) := by linarith
    nlinarith

/-- **BCG01 (`‖DF‖` clause) / input of A3c — the frozen target of lane B-DFB.** In the separated
branch of T3B, the actual augmented map `F_∂ = S.boundaryOriginalMap` on the original carrier
`(W, g)` has `‖dF_∂(v)‖ ≤ bder₀ |v|_g` at every point (boundary included) and every tangent vector,
with the numerical `bder₀ = boundaryDerivBound_BDFB = 1000 (N_TCP + 2) P₀² + 2 P_B`. -/
theorem norm_mvfderiv_boundaryOriginalMap_le_BDFB
    -- BEGIN uniform register block (A3c's, verbatim)
    (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10)
    (hΔ1 : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    -- END uniform register block; ADDITIONS (LPA06 / zero counts, CGP02 profile budgets)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he40 : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : σs ∈ Icc (0 : ℝ) 1) (hσc : σc ∈ Icc (0 : ℝ) 1)
    (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    -- the separated branch (BCG01: nonproduct case; `DP.separated` in A1)
    (hsep : S.SeparatedCollarZero_BIF) (p : W.Carrier) (v : TangentSpace W.model p) :
    ‖mvfderiv W.model S.boundaryOriginalMap p v‖ ≤
      boundaryDerivBound_BDFB * Real.sqrt (g.inner p v v) := by
  have hν := Real.sqrt_nonneg (g.inner p v v)
  have hP0 : 0 ≤ boundaryProfileBound_BDFB := by linarith [one_le_boundaryProfileBound_BDFB]
  have hint := S.norm_mvfderiv_interiorMapW_le_BDFB hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he hΔ1 hLΛ hLmax
    he40 hT hσs hσc hγc hεr p v
  have hdisj : ∀ i j : Fin S.packet.cusp.count, i ≠ j →
      Disjoint ((S.packet.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((S.packet.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) := fun i j hij =>
    (hsep.1 i j hij).1
  have hbd := S.packet.toBoundaryCollarPacket.sum_norm_mvfderiv_block_le
    (cuspTolerance_le_thousandth_BCUSP1 _ _ _) hdisj norm_fderiv_boundaryBlock_le_BDFB p v
  have hF := S.contMDiff_interiorMapW_BAUGA hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he p
  have hB : ∀ bb, ContMDiffAt W.model 𝓘(ℝ, ℝ × ℝ) ∞ (S.packet.toBoundaryCollarPacket.block bb) p :=
    fun bb => S.packet.toBoundaryCollarPacket.contMDiff_block bb p
  have h := norm_mvfderiv_boundaryAugmentedMap_le_BDFB (by simp) hF hB v hint hbd
  change ‖mvfderiv W.model (boundaryAugmentedMap_BAUGA S.interiorMapW_BAUGA
    S.packet.toBoundaryCollarPacket.block) p v‖ ≤ _
  refine h.trans ?_
  unfold boundaryDerivBound_BDFB
  nlinarith [mul_nonneg hP0 hν]

end BoundarySupplyCore

namespace BoundarySupply

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

/-- **Consumer**: for the FULL stored supply (with BCG02's certificates), in the separated branch
of its own `geometric_cases`, the augmented map obeys BCG01's derivative bound with the numerical
`bder₀` at every point of `W` (boundary included). -/
theorem norm_mvfderiv_boundaryOriginalMap_le_BDFB
    (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM)
    (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e ≤ 1 / 10)
    (hΔ1 : 1 ≤ Δ) (hLΛ : 1000000 * Δ * Λ < 1 / 100000)
    (hLmax : 4 * (10 + 2 * (2000000 * Δ) + Δ / 3) ≤ Lmax) (he40 : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hσs : σs ∈ Icc (0 : ℝ) 1) (hσc : σc ∈ Icc (0 : ℝ) 1)
    (hγc : γc ∈ Icc (0 : ℝ) 1) (hεr : εr ∈ Icc (0 : ℝ) 1)
    (hsep : ¬ S.toBoundarySupplyCore.LabelledWholeProduct_BIF) (p : W.Carrier)
    (v : TangentSpace W.model p) :
    ‖mvfderiv W.model S.toBoundarySupplyCore.boundaryOriginalMap p v‖ ≤
      boundaryDerivBound_BDFB * Real.sqrt (g.inner p v v) :=
  S.toBoundarySupplyCore.norm_mvfderiv_boundaryOriginalMap_le_BDFB hΛ hΔ hμ hτ hΔΛ hV hβ1 hb he
    hΔ1 hLΛ hLmax he40 hT hσs hσc hγc hεr
    (S.toBoundarySupplyCore.geometric_cases_BIF.resolve_left hsep) p v

end BoundarySupply

end DifferentialGeometry.Geometry.Collapse
