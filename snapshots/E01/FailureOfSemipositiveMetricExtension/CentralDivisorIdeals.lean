import FailureOfSemipositiveMetricExtension.DivisorStalkIdeals

/-! The frame-independent powers of the actual ell divisor equation in genuine
holomorphic local rings, and the prescribed section's order-two divisibility. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold Manifold TopologicalSpace Opposite CategoryTheory
open scoped Manifold ContDiff

def divisorPowerStalkIdeal {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (s : SectionData t a b) (k : ℕ) (p : Fiber t) : Ideal (HolomorphicStalk t p) :=
  Ideal.span { (sectionGerm s ((core t a b).indexAt p) p ((core t a b).mem_baseSet_at p))^k }

theorem divisorPowerStalkIdeal_eq_frame {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (s : SectionData t a b) (k : ℕ) (i : Index) (p : Fiber t) (hp : p ∈ baseSet t i) :
    divisorPowerStalkIdeal s k p = Ideal.span {(sectionGerm s i p hp)^k} :=
  sectionGerm_power_ideal_frame_independent s k _ i p ⟨(core t a b).mem_baseSet_at p,hp⟩

theorem divisorPowerStalkIdeal_off_zero {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (s : SectionData t a b) (k : ℕ) (p : Fiber t) (hp : sectionValue s p ≠ 0) :
    divisorPowerStalkIdeal s k p = ⊤ := by
  rw [divisorPowerStalkIdeal,Ideal.span_singleton_eq_top]
  exact ((sectionGerm_isUnit_iff s _ p ((core t a b).mem_baseSet_at p)).mpr hp).pow k

def ellPowerStalkIdeal (k : ℕ) (p : Fiber 0) : Ideal (HolomorphicStalk 0 p) :=
  divisorPowerStalkIdeal ellSection k p

theorem sigmaSection_germ_factorization (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i) :
    sectionGerm sigmaSection i p hp = (sectionGerm ellSection i p hp)^2 * sectionGerm qSection i p hp := by
  have hc : coefficientSection sigmaSection i =
      (coefficientSection ellSection i)^2 * coefficientSection qSection i := by
    apply Subtype.ext
    funext q
    exact sigmaSection_coefficient i q
  unfold sectionGerm
  rw [hc,map_mul,map_pow]

/-- In every actual frame, the nonzero constructed section has germ divisible by ell². -/
theorem sigmaSection_germ_mem_ellSquare (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i) :
    sectionGerm sigmaSection i p hp ∈ ellPowerStalkIdeal 2 p := by
  rw [ellPowerStalkIdeal,divisorPowerStalkIdeal_eq_frame ellSection 2 i p hp,
    Ideal.mem_span_singleton,sigmaSection_germ_factorization]
  exact dvd_mul_right _ _

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
