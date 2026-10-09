import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksMaster

/-!
# Chapter-14 assembly, item L1, G3b / T1′: the master bicollar as a partial diffeomorphism

Lane ASM-L1m. Consumer of E2b (`BallHandleCycle.exists_masterDomain`): the master map of a rim is,
on the master domain of a small height `η'`, an actual partial diffeomorphism `Φ` from
`ℝ² × ℝ` into `W`, whose ball side is exactly the heights `s ≤ 0`
(`BallHandleCycle.exists_masterPartialDiffeomorph`). This is the form in which the rim neck (E2)
restricts it.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
  Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

local instance ballCharts_ASML1mA : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 2

local instance diskCharts_ASML1mA : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

theorem isOpen_masterDomain (η Y : ℝ) : IsOpen (masterDomain η Y) :=
  (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
    ((isOpen_lt continuous_const continuous_snd).inter (isOpen_lt continuous_snd continuous_const))

theorem zero_mem_masterDomain {η Y : ℝ} (hη : 0 < η) (hY : 0 < Y) :
    (0 : EuclideanSpace ℝ (Fin 2) × ℝ) ∈ masterDomain η Y := by
  refine ⟨?_, ?_, hY⟩
  · change ‖(0 : EuclideanSpace ℝ (Fin 2))‖ < 1 + 9 / 32
    rw [norm_zero]
    norm_num
  · change -η < (0 : ℝ)
    linarith

/-- **The master bicollar as a partial diffeomorphism.** Under the hypotheses of E2b, for a
small height `η'` the master map is a partial diffeomorphism on `masterDomain η' Y` whose ball side
is exactly `s ≤ 0`. -/
theorem BallHandleCycle.exists_masterPartialDiffeomorph {W : CompactCarrier.{u}}
    (C : BallHandleCycle W)
    (k : Fin C.len) (b : Bool) {a : ℝ} (ha : 3 / 4 < a) (ha' : a ≤ 2)
    (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {ρ σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσ0 : σ 0 = 0) (hσd : ∀ y ∈ Ico 0 a, 0 < deriv σ y)
    (hσ1 : ∀ y ∈ Ico 0 a, σ y < 1)
    (heq : ∀ (θ : Circle) (x y : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      -a < x → x ≤ 0 → 0 ≤ y → y < a →
      (w : EuclideanSpace ℝ (Fin 2)) = ρ x • A (planeOfCircle θ) →
      (t : ℝ) = endCoord b (σ y) → C.rimChart k b (θ, (x, y)) = (C.handle k).map (w, t))
    {P : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) (hP1 : P 1 = 1) (hPpos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P s)
    (hPmono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P (r ^ 2)) r)
    (hPρ : ∀ r, 1 - 11 / 128 ≤ r → r ≤ 1 → r * P (r ^ 2) = ρ (8 * (r - 1)))
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hfd : ∀ x, 0 < deriv f x)
    (hfid : ∀ x ∈ Icc (-3 / 4 : ℝ) (3 / 4), f x = x) (hfb : ∀ x, -1 < f x ∧ f x < 1)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    (hBhsrc : Metric.closedBall 0 1 ⊆ Bh.source)
    (hBhball : ∀ x : ClosedCell 3, Bh x.val =
      (C.ball (rimBall C.len k b)).map ((C.ballModel _).symm x))
    {η : ℝ} (hη : 0 < η) (G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3))
    (hG : ContDiffOn ℝ ∞ G (collarDomain η))
    (hGsrc : ∀ q ∈ collarDomain η, G q ∈ Bh.source)
    (hGd : ∀ q ∈ collarDomain η, Bijective (fderiv ℝ G q))
    (hGH : ∀ q ∈ collarDomain η, 0 ≤ q.2 → ∀ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      (w : EuclideanSpace ℝ (Fin 2)) = handleDiskMap A P q.1 →
      (t : ℝ) = endCoord b (σ q.2) → Bh (G q) = (C.handle k).map (w, t))
    (hGχ : ∀ q ∈ collarDomain η, 59 / 64 ≤ ‖q.1‖ →
      Bh (G q) = C.rimChart k b (planeUnit q.1, (8 * (‖q.1‖ - 1), q.2)))
    (hGball : ∀ q ∈ collarDomain η, q.2 < 0 → ‖G q‖ < 1)
    {O : Set W.Carrier} (hO : IsOpen O) (hslice : C.rimSlice k b ⊆ O) {Y : ℝ} (hY : 3 / 4 < Y)
    (hYa : Y < a) :
    ∃ η' : ℝ, 0 < η' ∧ η' ≤ η ∧
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model
          (EuclideanSpace ℝ (Fin 2) × ℝ) W.Carrier ∞,
        Φ.source = masterDomain η' Y ∧
        (∀ q, Φ q = masterMap (C.rimChart k b) (C.handle k) b Bh G A P σ f q) ∧
        ∀ q ∈ Φ.source, (Φ q ∈ range (C.ball (rimBall C.len k b)).map ↔ q.2 ≤ 0) := by
  obtain ⟨η', hη', hη'η, hLD, hinj, hball, -⟩ := C.exists_masterDomain k b ha ha' A hσ hσ0 hσd
    hσ1 heq hP hP1 hPpos hPmono hPρ hf hfd hfid hfb Bh hBhsrc hBhball hη G hG hGsrc hGd hGH hGχ
    hGball hO hslice hY hYa
  obtain ⟨Φ, hsrc, -, hfun⟩ := hLD.exists_partialDiffeomorph_of_injOn
    (isOpen_masterDomain η' Y) ⟨0, zero_mem_masterDomain hη' (by linarith)⟩ hinj
  have hΦ : ∀ q, Φ q = masterMap (C.rimChart k b) (C.handle k) b Bh G A P σ f q := fun q =>
    congrFun hfun q
  refine ⟨η', hη', hη'η, Φ, hsrc, hΦ, fun q hq => ?_⟩
  rw [hΦ q]
  exact hball q (hsrc ▸ hq)

end GC.GraphManifold.Assembly
