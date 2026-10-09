import DifferentialGeometry.Geometry.Metric.Approximation.FactorTransferApproximation
import DifferentialGeometry.Geometry.Metric.Approximation.DirectedSplittingCompatibility

set_option autoImplicit false

namespace GC.MetricGeometry

open Set Filter Metric
open scoped Topology

private theorem transverse_coordinates_dist_le
    {D : Type*} [MetricSpace D] {j k : ℕ}
    (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))))
    (z : WithLp 2 (EuclideanSpace ℝ (Fin k) × D)) (d : D) :
    dist (WithLp.toLp 2 ((Q z.fst).snd, z.snd)) (WithLp.toLp 2 (0, d)) ≤
      dist z (WithLp.toLp 2 (0, d)) := by
  let e := (IsometryEquiv.withLpProdCongr 2 Q.toIsometryEquiv (IsometryEquiv.refl D)).trans
    (IsometryEquiv.withLpProdAssoc 2 (EuclideanSpace ℝ (Fin j))
      (EuclideanSpace ℝ (Fin (k - j))) D)
  have hb : e (WithLp.toLp 2 (0, d)) = WithLp.toLp 2 (0, WithLp.toLp 2 (0, d)) := by
    change WithLp.toLp 2 ((Q 0).fst, WithLp.toLp 2 ((Q 0).snd, d)) = _
    rw [map_zero]
    rfl
  have hh := WithLp.dist_snd_le (e z) (e (WithLp.toLp 2 (0, d)))
  rw [e.dist_eq, hb] at hh
  exact hh

private theorem exists_compatibility_map_of_full_product_errors
    {X Y Aᵢ A Bᵢ B : Type*}
    [MetricSpace X] [MetricSpace Y] [MetricSpace Aᵢ] [MetricSpace A]
    [MetricSpace Bᵢ] [MetricSpace B]
    {p : X} {aᵢ : Aᵢ} {a : A} {bᵢ : Bᵢ} {b : B}
    {j k : ℕ} {δ ν τ ε ρ : ℝ}
    (φ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), aᵢ)) δ)
    (ψ : KleinerLottApprox p (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), bᵢ)) ν)
    (g : PointedBallApprox aᵢ a (8 * (τ⁻¹ + 2)) ε)
    (h : PointedBallApprox bᵢ b (8 * (τ⁻¹ + 2)) ε)
    (eA : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin j) × A))
    (eB : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × B))
    (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))))
    (H : WithLp 2 (EuclideanSpace ℝ (Fin (k - j)) × B) ≃ᵢ A)
    (hH : H (WithLp.toLp 2 (0, b)) = a)
    (hfactor : ∀ y, eA y = WithLp.toLp 2 ((Q (eB y).fst).fst,
      H (WithLp.toLp 2 ((Q (eB y).fst).snd, (eB y).snd))))
    (hτ : 0 < τ) (hτone : τ < 1) (hδ : δ < τ) (hν : ν < τ)
    (hε : ε < τ / 100) (hρ : 0 < ρ) (herror : 2 * ε + 4 * ρ < τ)
    (hcontrol : ∀ x ∈ ball p τ⁻¹, ∃ y : Y,
      ∀ (ha : dist (φ.toFun x).snd aᵢ ≤ 8 * (τ⁻¹ + 2))
        (hb : dist (ψ.toFun x).snd bᵢ ≤ 8 * (τ⁻¹ + 2)),
        dist (WithLp.toLp 2 ((φ.toFun x).fst, g.toFun ⟨(φ.toFun x).snd, ha⟩)) (eA y) < ρ ∧
        dist (WithLp.toLp 2 ((ψ.toFun x).fst, h.toFun ⟨(ψ.toFun x).snd, hb⟩)) (eB y) < ρ) :
    ∃ F : KleinerLottApprox
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k - j))), bᵢ)) aᵢ τ,
      ∀ x ∈ ball p τ⁻¹,
        dist (WithLp.toLp 2 ((Q (ψ.toFun x).fst).fst,
          F.toFun (WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, (ψ.toFun x).snd))))
          (φ.toFun x) < τ := by
  have hi : 0 < τ⁻¹ := inv_pos.mpr hτ
  obtain ⟨F, hF⟩ := exists_factor_transfer_kleinerLott_approximation g h H hH hτ hτone hε
  refine ⟨F, ?_⟩
  intro x hx
  have hxδ : x ∈ ball p δ⁻¹ := hx.trans ((inv_lt_inv₀ hτ φ.error_pos).mpr hδ)
  have hxν : x ∈ ball p ν⁻¹ := hx.trans ((inv_lt_inv₀ hτ ψ.error_pos).mpr hν)
  have hxlt : dist x p < τ⁻¹ := hx
  have hrφ := (abs_le.mp (φ.radial_error x hxδ)).2
  have hrψ := (abs_le.mp (ψ.radial_error x hxν)).2
  have ha : dist (φ.toFun x).snd aᵢ ≤ 8 * (τ⁻¹ + 2) := by
    have hh := WithLp.dist_snd_le (φ.toFun x) (WithLp.toLp 2 (0, aᵢ))
    change dist (φ.toFun x).snd aᵢ ≤ _ at hh
    linarith [φ.error_lt_one]
  have hb : dist (ψ.toFun x).snd bᵢ ≤ 8 * (τ⁻¹ + 2) := by
    have hh := WithLp.dist_snd_le (ψ.toFun x) (WithLp.toLp 2 (0, bᵢ))
    change dist (ψ.toFun x).snd bᵢ ≤ _ at hh
    linarith [ψ.error_lt_one]
  let z : BallCarrier (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k - j))), bᵢ))
      (2 * (τ⁻¹ + 2)) :=
    ⟨WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, (ψ.toFun x).snd), by
      have hh := transverse_coordinates_dist_le Q (ψ.toFun x) bᵢ
      linarith [ψ.error_lt_one]⟩
  have hFa := (hF z).1
  have hFinv := (hF z).2 hFa hb
  obtain ⟨y, hy⟩ := hcontrol x hx
  obtain ⟨hAy, hBy⟩ := hy ha hb
  let PA := WithLp.toLp 2 ((φ.toFun x).fst, g.toFun ⟨(φ.toFun x).snd, ha⟩)
  let PB := WithLp.toLp 2 ((ψ.toFun x).fst, h.toFun ⟨(ψ.toFun x).snd, hb⟩)
  let C : WithLp 2 (EuclideanSpace ℝ (Fin k) × B) ≃ᵢ
      WithLp 2 (EuclideanSpace ℝ (Fin j) × A) :=
    ((IsometryEquiv.withLpProdCongr 2 Q.toIsometryEquiv (IsometryEquiv.refl B)).trans
      (IsometryEquiv.withLpProdAssoc 2 (EuclideanSpace ℝ (Fin j))
        (EuclideanSpace ℝ (Fin (k - j))) B)).trans
      (IsometryEquiv.withLpProdCongr 2 (IsometryEquiv.refl _) H)
  have hC : C (eB y) = eA y := (hfactor y).symm
  have hclose : dist PA (C PB) < 2 * ρ := by
    have ht := dist_triangle PA (eA y) (C PB)
    have hBy' : dist (eA y) (C PB) < ρ := by
      rw [← hC, C.dist_eq, dist_comm]
      exact hBy
    change dist PA (eA y) < ρ at hAy
    linarith
  let PF := WithLp.toLp 2 ((Q (ψ.toFun x).fst).fst, g.toFun ⟨F.toFun z.val, hFa⟩)
  have hPF : dist PF (C PB) < ε := by
    change dist (WithLp.toLp 2 ((Q (ψ.toFun x).fst).fst, g.toFun ⟨F.toFun z.val, hFa⟩))
      (WithLp.toLp 2 ((Q (ψ.toFun x).fst).fst,
        H (WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, h.toFun ⟨(ψ.toFun x).snd, hb⟩)))) < ε
    have hh := (WithLp.isometry_prodMk_left (Q (ψ.toFun x).fst).fst).dist_eq
      (g.toFun ⟨F.toFun z.val, hFa⟩)
      (H (WithLp.toLp 2 ((Q (ψ.toFun x).fst).snd, h.toFun ⟨(ψ.toFun x).snd, hb⟩)))
    exact hh.trans_lt hFinv
  have htarget : dist PA PF < 2 * ρ + ε := by
    have ht := dist_triangle PA (C PB) PF
    rw [dist_comm (C PB) PF] at ht
    linarith
  have hd := g.distortion ⟨(φ.toFun x).snd, ha⟩ ⟨F.toFun z.val, hFa⟩
  have hprod := WithLp.prod_dist_dist_sub_le (φ.toFun x).fst (Q (ψ.toFun x).fst).fst
    (φ.toFun x).snd (F.toFun z.val)
    (g.toFun ⟨(φ.toFun x).snd, ha⟩) (g.toFun ⟨F.toFun z.val, hFa⟩)
  rw [abs_sub_comm] at hd
  have hdist := (abs_lt.mp (hprod.trans_lt hd)).2
  change dist (WithLp.toLp 2 ((φ.toFun x).fst, (φ.toFun x).snd))
    (WithLp.toLp 2 ((Q (ψ.toFun x).fst).fst, F.toFun z.val)) - dist PA PF < ε at hdist
  have hη : WithLp.toLp 2 ((φ.toFun x).fst, (φ.toFun x).snd) = φ.toFun x := rfl
  rw [hη, dist_comm (φ.toFun x)] at hdist
  change dist (WithLp.toLp 2 ((Q (ψ.toFun x).fst).fst, F.toFun z.val)) (φ.toFun x) < τ
  linarith

end GC.MetricGeometry

namespace GC.MetricGeometry

open Set Filter Metric
open scoped Topology

universe u v w z v' w'
variable {X : ℕ → Type u} {Aᵢ : ℕ → Type v} {Bᵢ : ℕ → Type w}
variable {Y : Type z} {A : Type v'} {B : Type w'}
variable [∀ i, MetricSpace (X i)] [∀ i, MetricSpace (Aᵢ i)] [∀ i, MetricSpace (Bᵢ i)]
variable [MetricSpace Y] [MetricSpace A] [MetricSpace B]
variable {p : ∀ i, X i} {aᵢ : ∀ i, Aᵢ i} {bᵢ : ∀ i, Bᵢ i} {q : Y} {a : A} {b : B}
variable {j k : ℕ} {δ ν R ε P α L β : ℕ → ℝ}


theorem eventually_exists_compatibility_map_of_full_product_convergence
    (φ : ∀ i, KleinerLottApprox (p i)
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), aᵢ i)) (δ i))
    (ψ : ∀ i, KleinerLottApprox (p i)
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), bᵢ i)) (ν i))
    (hδ : Tendsto δ atTop (𝓝 0)) (hν : Tendsto ν atTop (𝓝 0))
    (f : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (g : ∀ i, PointedBallApprox (aᵢ i) a (P i) (α i))
    (h : ∀ i, PointedBallApprox (bᵢ i) b (L i) (β i))
    (hP : Tendsto P atTop atTop) (hα : Tendsto α atTop (𝓝 0))
    (hL : Tendsto L atTop atTop) (hβ : Tendsto β atTop (𝓝 0))
    (eA : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin j) × A))
    (eB : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × B))
    (hcontrol : ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
      S ≤ R i ∧ ∀ x : BallCarrier (p i) (R i), dist x.val (p i) ≤ S →
        (dist ((φ i).toFun x.val).snd (aᵢ i) ≤ P i ∧
          ∀ hx : dist ((φ i).toFun x.val).snd (aᵢ i) ≤ P i,
            dist (WithLp.toLp 2 (((φ i).toFun x.val).fst,
              (g i).toFun ⟨((φ i).toFun x.val).snd, hx⟩))
              (eA ((f i).toFun x)) < ζ) ∧
        (dist ((ψ i).toFun x.val).snd (bᵢ i) ≤ L i ∧
          ∀ hx : dist ((ψ i).toFun x.val).snd (bᵢ i) ≤ L i,
            dist (WithLp.toLp 2 (((ψ i).toFun x.val).fst,
              (h i).toFun ⟨((ψ i).toFun x.val).snd, hx⟩))
              (eB ((f i).toFun x)) < ζ))
    (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))))
    (H : WithLp 2 (EuclideanSpace ℝ (Fin (k - j)) × B) ≃ᵢ A)
    (hH : H (WithLp.toLp 2 (0, b)) = a)
    (hfactor : ∀ y, eA y = WithLp.toLp 2 ((Q (eB y).fst).fst,
      H (WithLp.toLp 2 ((Q (eB y).fst).snd, (eB y).snd))))
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    ∀ᶠ i in atTop, ∃ F : KleinerLottApprox
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin (k - j))), bᵢ i)) (aᵢ i) τ,
      ∀ x ∈ ball (p i) τ⁻¹,
        dist (WithLp.toLp 2 ((Q ((ψ i).toFun x).fst).fst,
          F.toFun (WithLp.toLp 2 ((Q ((ψ i).toFun x).fst).snd, ((ψ i).toFun x).snd))))
          ((φ i).toFun x) < τ := by
  let e : ℝ := τ / 1000
  have he : 0 < e := by dsimp [e]; positivity
  have hsmall : e < τ / 100 := by dsimp [e]; linarith
  have herror : 2 * e + 4 * e < τ := by dsimp [e]; linarith
  have hr : e < 8 * (τ⁻¹ + 2) := by
    have hi : 0 < τ⁻¹ := inv_pos.mpr hτ
    dsimp [e]
    linarith
  filter_upwards [hδ.eventually (eventually_lt_nhds hτ),
    hν.eventually (eventually_lt_nhds hτ),
    hP.eventually (eventually_ge_atTop (8 * (τ⁻¹ + 2))),
    hL.eventually (eventually_ge_atTop (8 * (τ⁻¹ + 2))),
    hα.eventually (eventually_lt_nhds (by linarith : 0 < e / 2)),
    hβ.eventually (eventually_lt_nhds (by linarith : 0 < e / 2)),
    hcontrol τ⁻¹ e he] with i hiδ hiν hiP hiL hiα hiβ hi
  let G : PointedBallApprox (aᵢ i) a (8 * (τ⁻¹ + 2)) e :=
    ((g i).restrict (by linarith) hiP).enlargeError (by linarith) hr
  let K : PointedBallApprox (bᵢ i) b (8 * (τ⁻¹ + 2)) e :=
    ((h i).restrict (by linarith) hiL).enlargeError (by linarith) hr
  apply exists_compatibility_map_of_full_product_errors (φ i) (ψ i) G K eA eB Q H hH
    hfactor hτ hτone hiδ hiν hsmall he herror
  intro x hx
  let xx : BallCarrier (p i) (R i) := ⟨x, hx.le.trans hi.1⟩
  obtain ⟨hA, hB⟩ := hi.2 xx hx.le
  refine ⟨(f i).toFun xx, ?_⟩
  intro ha hb
  constructor
  · change dist (WithLp.toLp 2 (((φ i).toFun x).fst,
      (g i).toFun ⟨((φ i).toFun x).snd, ha.trans hiP⟩)) (eA ((f i).toFun xx)) < e
    exact hA.2 _
  · change dist (WithLp.toLp 2 (((ψ i).toFun x).fst,
      (h i).toFun ⟨((ψ i).toFun x).snd, hb.trans hiL⟩)) (eB ((f i).toFun xx)) < e
    exact hB.2 _


theorem eventually_splittingCompatible_of_full_product_convergence
    (φ : ∀ i, KleinerLottApprox (p i)
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin j)), aᵢ i)) (δ i))
    (ψ : ∀ i, KleinerLottApprox (p i)
      (WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin k)), bᵢ i)) (ν i))
    (hδ : Tendsto δ atTop (𝓝 0)) (hν : Tendsto ν atTop (𝓝 0))
    (f : ∀ i, PointedBallApprox (p i) q (R i) (ε i))
    (g : ∀ i, PointedBallApprox (aᵢ i) a (P i) (α i))
    (h : ∀ i, PointedBallApprox (bᵢ i) b (L i) (β i))
    (hP : Tendsto P atTop atTop) (hα : Tendsto α atTop (𝓝 0))
    (hL : Tendsto L atTop atTop) (hβ : Tendsto β atTop (𝓝 0))
    (eA : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin j) × A))
    (eB : Y ≃ᵢ WithLp 2 (EuclideanSpace ℝ (Fin k) × B))
    (hcontrol : ∀ S ζ : ℝ, 0 < ζ → ∀ᶠ i in atTop,
      S ≤ R i ∧ ∀ x : BallCarrier (p i) (R i), dist x.val (p i) ≤ S →
        (dist ((φ i).toFun x.val).snd (aᵢ i) ≤ P i ∧
          ∀ hx : dist ((φ i).toFun x.val).snd (aᵢ i) ≤ P i,
            dist (WithLp.toLp 2 (((φ i).toFun x.val).fst,
              (g i).toFun ⟨((φ i).toFun x.val).snd, hx⟩))
              (eA ((f i).toFun x)) < ζ) ∧
        (dist ((ψ i).toFun x.val).snd (bᵢ i) ≤ L i ∧
          ∀ hx : dist ((ψ i).toFun x.val).snd (bᵢ i) ≤ L i,
            dist (WithLp.toLp 2 (((ψ i).toFun x.val).fst,
              (h i).toFun ⟨((ψ i).toFun x.val).snd, hx⟩))
              (eB ((f i).toFun x)) < ζ))
    (Q : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin j) × EuclideanSpace ℝ (Fin (k - j))))
    (H : WithLp 2 (EuclideanSpace ℝ (Fin (k - j)) × B) ≃ᵢ A)
    (hH : H (WithLp.toLp 2 (0, b)) = a)
    (hfactor : ∀ y, eA y = WithLp.toLp 2 ((Q (eB y).fst).fst,
      H (WithLp.toLp 2 ((Q (eB y).fst).snd, (eB y).snd))))
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (hjk : j ≤ k) :
    ∀ᶠ i in atTop, SplittingCompatible (φ i) (ψ i) τ := by
  filter_upwards [eventually_exists_compatibility_map_of_full_product_convergence
    φ ψ hδ hν f g h hP hα hL hβ eA eB hcontrol Q H hH hfactor hτ hτone] with i hi
  obtain ⟨F, hF⟩ := hi
  refine ⟨hjk, Q, (IsometryEquiv.refl _).toKleinerLottApprox rfl hτ hτone, F, ?_⟩
  intro x hx
  exact (hF x hx).le

end GC.MetricGeometry
