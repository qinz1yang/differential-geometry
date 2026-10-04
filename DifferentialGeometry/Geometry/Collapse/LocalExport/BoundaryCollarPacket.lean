import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPremises
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.InnerCollarSublevel
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFirstExit
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspBoundaryBandUpperDistance
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspFiniteCurvature
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspTorusDiameter
import DifferentialGeometry.Analysis.Calculus.Cutoff.BoundaryBlockProfile

/-!
# LC88: the collar layer of the boundary-collapse packet

Blueprint row LC88 (`def:collapse-boundary-packet`, master207A): besides the four KL 16.1
premises (`LocalExport/BoundaryPremises.lean`), the packet records, for every labelled boundary
component with its depth-100 pair collar `e = cusp.collar i` (height `z p = p.2.val 0`),

* the smoothed depth coordinate `η_i` on the buffered collar, with the Z contract of BCP01.a on
  `2 ≤ z ≤ 98` at a tolerance `ε ≤ 1` (B-5b's E8, `CuspEmbedding.exists_smooth_height_C2`);
* the retained piece `I × T²`: a smooth level function `F_i` (`= η_i` on `2 ≤ z ≤ 95`) whose
  sublevel `{F_i ≤ 90}` is the inner collar cut by the level `90`, a smooth manifold with boundary
  diffeomorphic as a pair to `(T² × [a_i, 90], T² × {a_i})` with the boundary label kept
  (B-5b's E6 = BCP01.c, `CuspEmbedding.exists_innerCollar_diffeomorph_torus_Icc`);
* the buffer field: the intrinsic one-neighbourhood of the depth-91 collar (which contains the
  retained piece), away from boundary distance nine, lies in the collar band `6 < z < 93` and in
  the smoothed depth band `5 < η_i < 95` (first exit E.3 and the boundary-band upper distance of
  B-5a);
* the reference pinching `-1/2 ≤ sec ≤ -1/8` on the whole collar (FT-C's
  `CuspEmbedding.sectional_pinching`, curvature `-1/4` of the reference cusp).

From `η_i` the module builds FC43's collar block `(η_i ζ_i, ζ_i)` with BCG.0's profile
(`boundaryBlock`): it is smooth on the carrier, its cutoff `ζ_i` is supported in the collar
between depths `20 - ε` and `90 + ε`, nonzero only where `20 < η_i < 90`, and equals one between
depths `30 + ε` and `80 - ε` (`BoundaryCollarPacket.block`, `BoundaryCollarPacket.cutoff`).

* `BoundaryCollarPacket`: the record (DATA with proofs of its fields), extending
  `BoundaryCollapsePremises`.
* `BoundaryCollarPacket.nonempty_of_premises`, `BoundaryCollarPacket.ofPremises`: the producer, for
  `2 ≤ K`, `w₀ ≤ 1/6408` and `0 < ε ≤ 1`; `nonempty_of_hypotheses` from the tree's
  `boundaryCollapseHypotheses`.
* `CuspEmbedding.exists_height_mem_of_edist_lt_one`: the buffer kernel for one collar.

Not recorded here (still open for LC88): the interior family with centres at boundary distance
greater than ten (LPA06 and KL 16.5–16.6), the product-or-disjoint alternative of KL 16.5 (BCP03
overlap with the two-collar gluing E7), the slim adapted coordinate on the depth band (BCP02).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Connection
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

universe u

section Kernels

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}
  {X : Set W.Carrier}

/-- Buffer kernel: a point within intrinsic distance one of the depth-91 collar and at boundary
distance greater than nine is a collar point of height in `(6, 93)`. -/
theorem CuspEmbedding.exists_height_mem_of_edist_lt_one (e : CuspEmbedding W g K δ X)
    (hδ : δ ≤ 3 / 4) {p : CuspHalfSpace} (hp : p.2.val 0 ≤ 91) {x : W.Carrier}
    (hx : riemannianEDistOf g (e.toFun p) x < 1)
    (h9 : ENNReal.ofReal 9 < distanceToBoundary W g x) :
    ∃ q ∈ cuspDomain, e.toFun q = x ∧ 6 < q.2.val 0 ∧ q.2.val 0 < 93 := by
  have hmem : x ∈ e.toFun '' {q : CuspHalfSpace | q.2.val 0 < 93} := by
    by_contra hnot
    have h1 := e.ofReal_le_riemannianEDistOf_of_not_mem_image_height_lt
      (h := 93) (by norm_num [cuspDepth]) (p := p) (by linarith) hnot
    have hs : (1 / 2 : ℝ) ≤ Real.sqrt (1 - δ) := by
      rw [show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by linarith)
    have hge : (1 : ℝ) ≤ Real.sqrt (1 - δ) * (93 - p.2.val 0) := by
      nlinarith [Real.sqrt_nonneg (1 - δ)]
    have : (1 : ℝ≥0∞) ≤ riemannianEDistOf g (e.toFun p) x := by
      calc (1 : ℝ≥0∞) = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal hge
        _ ≤ _ := h1
    exact absurd hx (not_lt.mpr this)
  obtain ⟨q, hq93, rfl⟩ := hmem
  have hq : q ∈ cuspDomain := cusp_mem_cuspDomain_of_le (b := 93) (by norm_num [cuspDepth])
    (le_of_lt hq93)
  refine ⟨q, hq, rfl, ?_, hq93⟩
  have hbd : e.toFun (q.1, halfZero) ∈ W.model.boundary W.Carrier :=
    (e.boundary_preimage (mem_cuspDomain_halfZero q.1)).mpr halfZero_val_zero
  have hle : distanceToBoundary W g (e.toFun q) ≤
      riemannianEDistOf g (e.toFun q) (e.toFun (q.1, halfZero)) :=
    iInf_le (fun b : W.model.boundary W.Carrier => riemannianEDistOf g (e.toFun q) b) ⟨_, hbd⟩
  have hup := e.riemannianEDistOf_le_flat hq (mem_cuspDomain_halfZero q.1)
  rw [riemannianEDistOf_self, ENNReal.toReal_zero] at hup
  have hz0 : 0 ≤ q.2.val 0 := q.2.2
  have hsq : Real.sqrt ((q.2.val 0 - (halfZero : EuclideanHalfSpace 1).val 0) ^ 2 + 0 ^ 2) =
      q.2.val 0 := by
    rw [halfZero_val_zero, sub_zero, zero_pow two_ne_zero, add_zero, Real.sqrt_sq hz0]
  change riemannianEDistOf g (e.toFun q) (e.toFun (q.1, halfZero)) ≤ ENNReal.ofReal
    (Real.sqrt (1 + δ) * Real.sqrt ((q.2.val 0 - (halfZero : EuclideanHalfSpace 1).val 0) ^ 2
      + 0 ^ 2)) at hup
  rw [hsq] at hup
  have h9' : ENNReal.ofReal 9 < ENNReal.ofReal (Real.sqrt (1 + δ) * q.2.val 0) :=
    h9.trans_le (hle.trans hup)
  have h9r : 9 < Real.sqrt (1 + δ) * q.2.val 0 :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num)).mp h9'
  have hs : Real.sqrt (1 + δ) < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by linarith)
  nlinarith [Real.sqrt_nonneg (1 + δ)]

/-- The collar block of a height `η` that is `ε`-close to the collar height on `2 ≤ z ≤ 98`
(`ε ≤ 1`), extended by zero off `e(2 < z < 98)`: smooth on the carrier. -/
theorem CuspEmbedding.contMDiff_indicator_boundaryBlock_height (e : CuspEmbedding W g K δ X)
    {η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η) {ε : ℝ} (hε1 : ε ≤ 1)
    (hZ : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 → |η (e.toFun p) - p.2.val 0| < ε) :
    ContMDiff W.model 𝓘(ℝ, ℝ × ℝ) ∞
      ((e.toFun '' {p : CuspHalfSpace | 2 < p.2.val 0 ∧ p.2.val 0 < 98}).indicator
        (fun x => boundaryBlock (η x))) := by
  have hO : IsOpen (e.toFun '' {p : CuspHalfSpace | 2 < p.2.val 0 ∧ p.2.val 0 < 98}) :=
    e.isOpen_image ((isOpen_lt continuous_const continuous_cusp_height).inter
      (isOpen_lt continuous_cusp_height continuous_const))
      fun p hp => cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
  have hT : IsClosed (e.toFun '' {p : CuspHalfSpace | 20 - ε ≤ p.2.val 0 ∧ p.2.val 0 ≤ 90 + ε}) :=
    (e.isCompact_image_band (by norm_num [cuspDepth]; linarith)).isClosed
  refine contMDiff_indicator_boundaryBlock hO hT ?_ hη.contMDiffOn ?_
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨p, ⟨by linarith [hp.1], by linarith [hp.2]⟩, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩ hnot
    have hpd : p ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
    have h := abs_lt.mp (hZ p hpd hp.1.le hp.2.le)
    by_cases hlow : p.2.val 0 < 20 - ε
    · exact boundaryBlock_eq_zero_of_le (by linarith)
    · by_cases hhigh : 90 + ε < p.2.val 0
      · exact boundaryBlock_eq_zero_of_ge (by linarith)
      · exact (hnot ⟨p, ⟨not_lt.mp hlow, not_lt.mp hhigh⟩, rfl⟩).elim

/-- The collar block is supported in the collar between depths `20 - ε` and `90 + ε`. -/
theorem CuspEmbedding.tsupport_indicator_boundaryBlock_height (e : CuspEmbedding W g K δ X)
    {η : W.Carrier → ℝ} {ε : ℝ} (hε1 : ε ≤ 1)
    (hZ : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 → |η (e.toFun p) - p.2.val 0| < ε) :
    tsupport ((e.toFun '' {p : CuspHalfSpace | 2 < p.2.val 0 ∧ p.2.val 0 < 98}).indicator
        (fun x => boundaryBlock (η x))) ⊆
      e.toFun '' {p : CuspHalfSpace | 20 - ε ≤ p.2.val 0 ∧ p.2.val 0 ≤ 90 + ε} := by
  refine closure_minimal ?_ (e.isCompact_image_band (by norm_num [cuspDepth]; linarith)).isClosed
  intro x hx
  by_cases hxO : x ∈ e.toFun '' {p : CuspHalfSpace | 2 < p.2.val 0 ∧ p.2.val 0 < 98}
  · obtain ⟨p, hp, rfl⟩ := hxO
    rw [mem_support, indicator_of_mem (mem_image_of_mem e.toFun hp)] at hx
    have hpd : p ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
    have h := abs_lt.mp (hZ p hpd hp.1.le hp.2.le)
    refine ⟨p, ⟨?_, ?_⟩, rfl⟩
    · by_contra hlow
      exact hx (boundaryBlock_eq_zero_of_le (by linarith))
    · by_contra hhigh
      exact hx (boundaryBlock_eq_zero_of_ge (by linarith))
  · rw [mem_support, indicator_of_notMem hxO] at hx
    exact (hx rfl).elim

/-- Where the collar block is nonzero, the point lies in `e(2 < z < 98)` and `20 < η < 90`. -/
theorem mem_of_indicator_boundaryBlock_ne_zero {S : Set W.Carrier} {η : W.Carrier → ℝ}
    {x : W.Carrier} (hx : S.indicator (fun x => boundaryBlock (η x)) x ≠ 0) :
    x ∈ S ∧ 20 < η x ∧ η x < 90 := by
  by_cases hxS : x ∈ S
  · rw [indicator_of_mem hxS] at hx
    exact ⟨hxS, mem_Ioo_of_boundaryBlock_ne_zero hx⟩
  · rw [indicator_of_notMem hxS] at hx
    exact (hx rfl).elim

/-- The cutoff of the collar block equals one between depths `30 + ε` and `80 - ε`. -/
theorem CuspEmbedding.indicator_boundaryBlock_height_snd_eq_one (e : CuspEmbedding W g K δ X)
    {η : W.Carrier → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hZ : ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 → |η (e.toFun p) - p.2.val 0| < ε)
    {p : CuspHalfSpace} (h30 : 30 + ε ≤ p.2.val 0) (h80 : p.2.val 0 ≤ 80 - ε) :
    ((e.toFun '' {p : CuspHalfSpace | 2 < p.2.val 0 ∧ p.2.val 0 < 98}).indicator
        (fun x => boundaryBlock (η x)) (e.toFun p)).2 = 1 := by
  have hpd : p ∈ cuspDomain :=
    cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) (by linarith)
  have h := abs_lt.mp (hZ p hpd (by linarith) (by linarith))
  have hmem : e.toFun p ∈ e.toFun '' {p : CuspHalfSpace | 2 < p.2.val 0 ∧ p.2.val 0 < 98} :=
    mem_image_of_mem e.toFun ⟨by linarith, by linarith⟩
  rw [indicator_of_mem hmem, boundaryBlock_snd]
  exact boundaryProfile_eq_one ⟨by linarith, by linarith⟩

end Kernels

/-- **LC88, collar layer.** The boundary-collapse packet at tolerance `ε`: the four KL 16.1
premises (with `K, A` fixed before `w₀`) and, for every labelled boundary component `i` with pair
collar `e = cusp.collar i`, the smoothed depth coordinate with its Z contract, the retained piece
`I × T²` as a pair with its label, the buffer field and the reference pinching. DATA with proofs of
these fields; it asserts no compatibility with any other chart. -/
structure BoundaryCollarPacket (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (A : ℝ → ℝ) (w₀ ε : ℝ)
    extends BoundaryCollapsePremises W g K A w₀ where
  /-- The collar error threshold (the cusp `δ = w₀`). -/
  threshold : w₀ ≤ 1 / 6408
  tolerance_pos : 0 < ε
  tolerance_le_one : ε ≤ 1
  /-- The smoothed depth coordinate `η_i`, smooth on the whole carrier. -/
  height : Fin cusp.count → W.Carrier → ℝ
  contMDiff_height : ∀ i, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (height i)
  /-- The Z contract (BCP01.a) on `2 ≤ z ≤ 98`: value, differential and Hessian `ε`-close to the
  collar height, in the reference norms. -/
  height_contract : ∀ i, ∀ p ∈ cuspDomain, 2 ≤ p.2.val 0 → p.2.val 0 ≤ 98 →
    |height i ((cusp.collar i).toFun p) - p.2.val 0| < ε ∧
    (∀ v : TangentSpace halfCollarModel p,
      |(show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (height i ∘ (cusp.collar i).toFun) p v) -
          (show ℝ from v.2 0)| ≤
        ε * Real.sqrt ((cusp.collar i).cusp.metric.inner p v v)) ∧
    ∀ v w : TangentSpace halfCollarModel p,
      |(CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g)
          (fun y => height i y - (invFunOn (cusp.collar i).toFun cuspDomain y).2.val 0)
          ((cusp.collar i).toFun p)
          (mfderiv halfCollarModel W.model (cusp.collar i).toFun p v)
          (mfderiv halfCollarModel W.model (cusp.collar i).toFun p w)| ≤
        ε * Real.sqrt ((cusp.collar i).cusp.metric.inner p v v) *
          Real.sqrt ((cusp.collar i).cusp.metric.inner p w w)
  /-- The level function `F_i` cutting the inner collar, with bottom value `a_i < 90`. -/
  level : Fin cusp.count → W.Carrier → ℝ
  levelBase : Fin cusp.count → ℝ
  levelBase_lt : ∀ i, levelBase i < 90
  contMDiff_level : ∀ i, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (level i)
  level_eq_height : ∀ i (p : CuspHalfSpace), 2 ≤ p.2.val 0 → p.2.val 0 ≤ 95 →
    level i ((cusp.collar i).toFun p) = height i ((cusp.collar i).toFun p)
  /-- The retained sublevel `{F_i ≤ 90}` in collar terms. -/
  level_sublevel_eq : ∀ i, {y | level i y ≤ 90} = (cusp.collar i).toFun '' {p | p ∈ cuspDomain ∧
    (p.2.val 0 ≤ 2 ∨ (p.2.val 0 ≤ 98 ∧ height i ((cusp.collar i).toFun p) ≤ 90))}
  /-- The retained piece `{F_i ≤ 90}` is `I × T²` as a pair, with the boundary label kept. -/
  retained : ∀ i, ∃ cs : ChartedSpace (EuclideanHalfSpace 3) {x : W.Carrier // level i x ≤ 90},
    letI := cs
    IsManifold (𝓡∂ 3) ∞ {x : W.Carrier // level i x ≤ 90} ∧
    ContMDiff (𝓡∂ 3) W.model ∞ (fun x : {x : W.Carrier // level i x ≤ 90} => x.1) ∧
    (∀ y : {x : W.Carrier // level i x ≤ 90}, (𝓡∂ 3).IsBoundaryPoint y ↔
      (y.1 ∈ cusp.component i ∨ level i y.1 = 90)) ∧
    haveI : Fact (levelBase i < 90) := ⟨levelBase_lt i⟩
    ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc (levelBase i) 90)
        {x : W.Carrier // level i x ≤ 90} ∞,
      (∀ p, level i (D p).1 = p.2.1) ∧ ∀ p, (D p).1 ∈ cusp.component i ↔ p.2.1 = levelBase i
  /-- The buffer field: the intrinsic one-neighbourhood of the depth-91 collar, away from boundary
  distance nine, lies in the collar band `6 < z < 93` and in the smoothed band `5 < η_i < 95`. -/
  buffer : ∀ i (p : CuspHalfSpace) (x : W.Carrier), p.2.val 0 ≤ 91 →
    riemannianEDistOf g ((cusp.collar i).toFun p) x < 1 →
    ENNReal.ofReal 9 < distanceToBoundary W g x →
    ∃ q ∈ cuspDomain, (cusp.collar i).toFun q = x ∧ 6 < q.2.val 0 ∧ q.2.val 0 < 93 ∧
      5 < height i x ∧ height i x < 95
  /-- The reference pinching `-1/2 ≤ sec ≤ -1/8` on the whole collar. -/
  pinching : ∀ i, ∀ q ∈ cuspDomain, ∀ u w : TangentSpace W.model ((cusp.collar i).toFun q),
    -(1 / 2) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2) ≤
        metricRm04StandardAt g ((cusp.collar i).toFun q) u w w u ∧
      metricRm04StandardAt g ((cusp.collar i).toFun q) u w w u ≤
        -(1 / 8) * (g.inner _ u u * g.inner _ w w - g.inner _ u w ^ 2)

namespace BoundaryCollarPacket

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier}
  {K : ℕ} {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- **Producer.** The premises with `2 ≤ K` and `w₀ ≤ 1/6408` give a collar packet at every
tolerance `0 < ε ≤ 1`. -/
theorem nonempty_of_premises (P : BoundaryCollapsePremises W g K A w₀) (hK : 2 ≤ K)
    (hw : w₀ ≤ 1 / 6408) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Nonempty (BoundaryCollarPacket W g K A w₀ ε) := by
  have h := fun i => (P.cusp.collar i).exists_innerCollar_diffeomorph_torus_Icc
    (by omega) hε
  choose η F a har hη hF hZ hmid hchar hret using h
  refine ⟨{
    toBoundaryCollapsePremises := P
    threshold := hw
    tolerance_pos := hε
    tolerance_le_one := hε1
    height := η
    contMDiff_height := hη
    height_contract := hZ
    level := F
    levelBase := a
    levelBase_lt := har
    contMDiff_level := hF
    level_eq_height := hmid
    level_sublevel_eq := fun i => by
      ext y
      constructor
      · intro hy
        obtain ⟨p, hp, rfl, h⟩ := (hchar i y).mp hy
        exact ⟨p, ⟨hp, h⟩, rfl⟩
      · rintro ⟨p, ⟨hp, h⟩, rfl⟩
        exact (hchar i _).mpr ⟨p, hp, rfl, h⟩
    retained := hret
    buffer := ?_
    pinching := ?_ }⟩
  · intro i p x hp hx h9
    obtain ⟨q, hq, rfl, h6, h93⟩ := (P.cusp.collar i).exists_height_mem_of_edist_lt_one
      (by linarith) hp hx h9
    have h := abs_lt.mp (hZ i q hq (by linarith) (by linarith)).1
    exact ⟨q, hq, rfl, h6, h93, by linarith, by linarith⟩
  · intro i q hq u w
    exact (P.cusp.collar i).sectional_pinching hK (P.cusp.collar i).delta_nonneg hw hq u w

/-- A choice of collar packet from the premises (`2 ≤ K`, `w₀ ≤ 1/6408`, `0 < ε ≤ 1`). -/
def ofPremises (P : BoundaryCollapsePremises W g K A w₀) (hK : 2 ≤ K) (hw : w₀ ≤ 1 / 6408)
    (hε : 0 < ε) (hε1 : ε ≤ 1) : BoundaryCollarPacket W g K A w₀ ε :=
  Classical.choice (nonempty_of_premises P hK hw hε hε1)

/-- The tree's boundary collapse hypotheses give a collar packet (`2 ≤ K`, `w₀ ≤ 1/6408`,
`0 < ε ≤ 1`). -/
theorem nonempty_of_hypotheses (h : boundaryCollapseHypotheses W g K A w₀) (hK : 2 ≤ K)
    (hw : w₀ ≤ 1 / 6408) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Nonempty (BoundaryCollarPacket W g K A w₀ ε) :=
  nonempty_of_premises (BoundaryCollapsePremises.ofHypotheses h) hK hw hε hε1

/-- FC43's collar block `(η_i ζ_i, ζ_i)` of component `i`, extended by zero off `e(2 < z < 98)`. -/
def block (P : BoundaryCollarPacket W g K A w₀ ε) (i : Fin P.cusp.count) : W.Carrier → ℝ × ℝ :=
  ((P.cusp.collar i).toFun '' {p : CuspHalfSpace | 2 < p.2.val 0 ∧ p.2.val 0 < 98}).indicator
    (fun x => boundaryBlock (P.height i x))

/-- The collar cutoff `ζ_i` of component `i`. -/
def cutoff (P : BoundaryCollarPacket W g K A w₀ ε) (i : Fin P.cusp.count) : W.Carrier → ℝ :=
  fun x => (P.block i x).2

variable (P : BoundaryCollarPacket W g K A w₀ ε) (i : Fin P.cusp.count)

/-- The collar block is smooth on the carrier. -/
theorem contMDiff_block : ContMDiff W.model 𝓘(ℝ, ℝ × ℝ) ∞ (P.block i) :=
  (P.cusp.collar i).contMDiff_indicator_boundaryBlock_height (P.contMDiff_height i)
    P.tolerance_le_one fun p hp h2 h98 => (P.height_contract i p hp h2 h98).1

/-- The collar cutoff is smooth on the carrier. -/
theorem contMDiff_cutoff : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (P.cutoff i) :=
  contDiff_snd.contMDiff.comp (P.contMDiff_block i)

/-- The collar block (hence the cutoff) is supported between depths `20 - ε` and `90 + ε`. -/
theorem tsupport_block_subset : tsupport (P.block i) ⊆
    (P.cusp.collar i).toFun '' {p : CuspHalfSpace | 20 - ε ≤ p.2.val 0 ∧ p.2.val 0 ≤ 90 + ε} :=
  (P.cusp.collar i).tsupport_indicator_boundaryBlock_height P.tolerance_le_one
    fun p hp h2 h98 => (P.height_contract i p hp h2 h98).1

/-- The collar cutoff is supported between depths `20 - ε` and `90 + ε`. -/
theorem tsupport_cutoff_subset : tsupport (P.cutoff i) ⊆
    (P.cusp.collar i).toFun '' {p : CuspHalfSpace | 20 - ε ≤ p.2.val 0 ∧ p.2.val 0 ≤ 90 + ε} := by
  refine (closure_mono ?_).trans (P.tsupport_block_subset i)
  intro x hx
  rw [mem_support] at hx ⊢
  intro h
  exact hx (by change (P.block i x).2 = 0; rw [h]; rfl)

/-- Where the collar block is nonzero, `20 < η_i < 90` (support strictly inside the band). -/
theorem height_mem_of_block_ne_zero {x : W.Carrier} (hx : P.block i x ≠ 0) :
    20 < P.height i x ∧ P.height i x < 90 :=
  (mem_of_indicator_boundaryBlock_ne_zero hx).2

/-- The collar cutoff takes values in `[0, 1]`. -/
theorem cutoff_mem_Icc (x : W.Carrier) : P.cutoff i x ∈ Icc (0 : ℝ) 1 := by
  change (P.block i x).2 ∈ Icc (0 : ℝ) 1
  by_cases hx : x ∈ (P.cusp.collar i).toFun '' {p : CuspHalfSpace | 2 < p.2.val 0 ∧ p.2.val 0 < 98}
  · rw [block, indicator_of_mem hx, boundaryBlock_snd]
    exact boundaryProfile_mem_Icc _
  · rw [block, indicator_of_notMem hx]
    exact ⟨le_rfl, zero_le_one⟩

/-- The collar cutoff equals one between depths `30 + ε` and `80 - ε` (plateau). -/
theorem cutoff_eq_one {p : CuspHalfSpace} (h30 : 30 + ε ≤ p.2.val 0) (h80 : p.2.val 0 ≤ 80 - ε) :
    P.cutoff i ((P.cusp.collar i).toFun p) = 1 :=
  (P.cusp.collar i).indicator_boundaryBlock_height_snd_eq_one P.tolerance_pos.le
    (fun q hq h2 h98 => (P.height_contract i q hq h2 h98).1) h30 h80

/-- The retained piece lies in the collar below depth `91`. -/
theorem exists_of_level_le {y : W.Carrier} (hy : P.level i y ≤ 90) :
    ∃ p ∈ cuspDomain, (P.cusp.collar i).toFun p = y ∧ p.2.val 0 < 91 := by
  have hy' : y ∈ {y | P.level i y ≤ 90} := hy
  rw [P.level_sublevel_eq i] at hy'
  obtain ⟨p, ⟨hp, h⟩, rfl⟩ := hy'
  refine ⟨p, hp, rfl, ?_⟩
  rcases h with h2 | ⟨h98, hη⟩
  · linarith
  · by_contra h91
    have h := abs_lt.mp (P.height_contract i p hp (by linarith) h98).1
    linarith [P.tolerance_le_one]

/-- The buffer field for the retained piece: a point within intrinsic distance one of
`{F_i ≤ 90}` and at boundary distance greater than nine lies in the smoothed band `5 < η_i < 95`. -/
theorem buffer_of_level_le {y x : W.Carrier} (hy : P.level i y ≤ 90)
    (hx : riemannianEDistOf g y x < 1) (h9 : ENNReal.ofReal 9 < distanceToBoundary W g x) :
    ∃ q ∈ cuspDomain, (P.cusp.collar i).toFun q = x ∧ 6 < q.2.val 0 ∧ q.2.val 0 < 93 ∧
      5 < P.height i x ∧ P.height i x < 95 := by
  obtain ⟨p, -, rfl, hp⟩ := P.exists_of_level_le i hy
  exact P.buffer i p x hp.le hx h9

end BoundaryCollarPacket

end DifferentialGeometry.Geometry.Collapse
