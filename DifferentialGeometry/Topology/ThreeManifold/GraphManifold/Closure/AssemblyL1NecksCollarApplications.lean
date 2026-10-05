import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyL1NecksCollar

/-!
# Chapter-14 assembly, item L1, G3b / T1′: consumers of the ball-side collar

Lane ASM-L1e3, group C1 (consumer of `AssemblyL1NecksCharts` and `AssemblyL1NecksCollar`).

* `ballSideCollar_isLocalDiffeomorphOn`: a collar with bijective differential, read through the
  ball chart, is a local diffeomorphism into the carrier (the Euclidean inverse function theorem
  `isLocalDiffeomorphAt_of_contDiffOn_of_bijective` of `AssemblyL1NecksCharts`).
* `exists_ballSideCollar_isLocalDiffeomorphOn`: E2a, read in the carrier: a local diffeomorphism
  of the slab `collarDomain η` into `W`, sending the ball side `s < 0` into the open ball and equal
  to the rim chart near the rim.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- A collar with bijective differential, read through the ball chart, is a local
diffeomorphism into the carrier. -/
theorem ballSideCollar_isLocalDiffeomorphOn {W : CompactCarrier.{u}}
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    {η : ℝ} {G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3)}
    (hG : ContDiffOn ℝ ∞ G (collarDomain η)) (hGsrc : ∀ q ∈ collarDomain η, G q ∈ Bh.source)
    (hGd : ∀ q ∈ collarDomain η, Bijective (fderiv ℝ G q)) :
    IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model ∞ (Bh ∘ G)
      (collarDomain η) := by
  intro q
  exact (isLocalDiffeomorphAt_of_contDiffOn_of_bijective (isOpen_collarDomain η) q.2 hG
    (hGd q q.2)).comp W.model W.Carrier (Bh.isLocalDiffeomorphAt (𝓡 3) W.model ∞ (hGsrc q q.2))

/-- **E2a read in the carrier.** -/
theorem exists_ballSideCollar_isLocalDiffeomorphOn {W : CompactCarrier.{u}} (H : EdgeHandle W)
    (b : Bool)
    (χ : PartialDiffeomorph ((𝓡 1).prod 𝓘(ℝ, ℝ × ℝ)) W.model (Circle × (ℝ × ℝ)) W.Carrier ∞)
    (hχsrc : ∀ {p : Circle × (ℝ × ℝ)}, p ∈ χ.source ↔ p.2 ∈ rimBox 2)
    (Bh : PartialDiffeomorph (𝓡 3) W.model (EuclideanSpace ℝ (Fin 3)) W.Carrier ∞)
    (hBhsrc : Metric.closedBall 0 1 ⊆ Bh.source)
    (hsphere : ∀ {y}, y ∈ Bh.source → Bh y ∈ H.endDisk b → ‖y‖ = 1)
    (hdisk : H.endDisk b ⊆ Bh '' Metric.closedBall 0 1)
    (hHB : ∀ (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      H.map (w, t) ∈ Bh '' Metric.closedBall 0 1 → (t : ℝ) = 0 ∨ (t : ℝ) = 1)
    {a : ℝ} (ha : 3 / 4 < a) (A : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    {ρ σ : ℝ → ℝ} (hσ : ContDiff ℝ ∞ σ) (hσ0 : σ 0 = 0) (hσd : ∀ y ∈ Ico 0 a, 0 < deriv σ y)
    (heq : ∀ (θ : Circle) (x y : ℝ) (w : ClosedCell 2) (t : Icc (0 : ℝ) 1),
      -a < x → x ≤ 0 → 0 ≤ y → y < a →
      (w : EuclideanSpace ℝ (Fin 2)) = ρ x • A (planeOfCircle θ) →
      (t : ℝ) = endCoord b (σ y) → χ (θ, (x, y)) = H.map (w, t))
    {P : ℝ → ℝ} (hP : ContDiff ℝ ∞ P) (hP1 : P 1 = 1) (hPpos : ∀ s, 0 ≤ s → s ≤ 1 → 0 < P s)
    (hPmono : ∀ r, 0 ≤ r → r ≤ 1 → 0 < deriv (fun r : ℝ => r * P (r ^ 2)) r)
    (hPρ : ∀ r, 1 - 11 / 128 ≤ r → r ≤ 1 → r * P (r ^ 2) = ρ (8 * (r - 1))) :
    ∃ η : ℝ, 0 < η ∧ ∃ G : EuclideanSpace ℝ (Fin 2) × ℝ → EuclideanSpace ℝ (Fin 3),
      IsLocalDiffeomorphOn 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) × ℝ) W.model ∞ (Bh ∘ G)
        (collarDomain η) ∧
      (∀ q ∈ collarDomain η, q.2 < 0 → (Bh ∘ G) q ∈ Bh '' Metric.ball 0 1) ∧
      ∀ q ∈ collarDomain η, 59 / 64 ≤ ‖q.1‖ →
        (Bh ∘ G) q = χ (planeUnit q.1, (8 * (‖q.1‖ - 1), q.2)) := by
  obtain ⟨η, hη, G, hG, hGsrc, hGd, -, hGχ, hGball⟩ :=
    exists_ballSideCollar H b χ hχsrc Bh hBhsrc hsphere hdisk hHB ha A hσ hσ0 hσd heq hP hP1
      hPpos hPmono hPρ
  exact ⟨η, hη, G, ballSideCollar_isLocalDiffeomorphOn Bh hG hGsrc hGd,
    fun q hq hs => ⟨G q, mem_ball_zero_iff.mpr (hGball q hq hs), rfl⟩, hGχ⟩

end GC.GraphManifold.Assembly
