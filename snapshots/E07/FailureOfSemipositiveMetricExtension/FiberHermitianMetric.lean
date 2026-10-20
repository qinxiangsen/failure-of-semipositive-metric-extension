import FailureOfSemipositiveMetricExtension.GlobalFiberSections
import FailureOfSemipositiveMetricExtension.RealAnalyticBridge

/-! Genuine smooth positive Hermitian metric data on the actual line bundles.
The Fubini--Study sum-of-squares construction is formalized through its positive
weights, real smoothness, frame transformations and invariant fibre norms.
Curvature semipositivity is a separate assertion, not assumed here. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

structure SmoothHermitianMetric (t : ℂ) (a : ℤ) (b : Fin 4 → ℤ) where
  coefficient : Index → Fiber t → ℝ
  positive : ∀ i p, p ∈ baseSet t i → 0 < coefficient i p
  smooth : ∀ i, ContMDiffOn 𝓘(ℝ,FixedFiber.Coord) 𝓘(ℝ) ω (coefficient i) (baseSet t i)
  compatible : ∀ i j p, p ∈ baseSet t i ∩ baseSet t j →
    coefficient j p * Complex.normSq (gain t a b i j p) = coefficient i p

def metricNormSq {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (h : SmoothHermitianMetric t a b)
    (p : Fiber t) (v : (core t a b).Fiber p) : ℝ :=
  h.coefficient ((core t a b).indexAt p) p * Complex.normSq (show ℂ from v)

theorem metricNormSq_nonneg {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (h : SmoothHermitianMetric t a b)
    (p : Fiber t) (v : (core t a b).Fiber p) : 0 ≤ metricNormSq h p v :=
  mul_nonneg (h.positive _ p ((core t a b).mem_baseSet_at p)).le (Complex.normSq_nonneg _)

theorem metricNormSq_pos_iff {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (h : SmoothHermitianMetric t a b)
    (p : Fiber t) (v : (core t a b).Fiber p) : 0 < metricNormSq h p v ↔ v ≠ 0 := by
  rw [metricNormSq,mul_pos_iff_of_pos_left (h.positive _ p ((core t a b).mem_baseSet_at p)),Complex.normSq_pos]

theorem metricNormSq_smul {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (h : SmoothHermitianMetric t a b)
    (p : Fiber t) (c : ℂ) (v : (core t a b).Fiber p) :
    metricNormSq h p (c • v) = Complex.normSq c * metricNormSq h p v := by
  change _ * Complex.normSq (c * (show ℂ from v)) = _
  rw [Complex.normSq_mul]
  unfold metricNormSq
  ring

/-- The actual norm is independent of the selected bundle frame. -/
theorem metricNormSq_localTriv {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} (h : SmoothHermitianMetric t a b)
    (i : Index) (p : Fiber t) (v : (core t a b).Fiber p) (hp : p ∈ baseSet t i) :
    metricNormSq h p v = h.coefficient i p * Complex.normSq (((core t a b).localTriv i ⟨p,v⟩).2) := by
  rw [VectorBundleCore.localTriv_apply]
  change _ = h.coefficient i p * Complex.normSq (gain t a b ((core t a b).indexAt p) i p * (show ℂ from v))
  rw [Complex.normSq_mul,← mul_assoc,h.compatible _ i p ⟨(core t a b).mem_baseSet_at p,hp⟩]
  rfl

def sectionNormSum {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} {m : ℕ}
    (s : Fin m → SectionData t a b) (i : Index) (p : Fiber t) : ℝ :=
  ∑ k, Complex.normSq ((s k).coefficient i p)

theorem sectionNormSum_positive {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} {m : ℕ}
    (s : Fin m → SectionData t a b) (hgen : ∀ p, ∃ k, sectionValue (s k) p ≠ 0)
    (i : Index) (p : Fiber t) (hp : p ∈ baseSet t i) : 0 < sectionNormSum s i p := by
  obtain ⟨k,hk⟩ := hgen p
  apply Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
  refine ⟨k,Finset.mem_univ k,Complex.normSq_pos.mpr ?_⟩
  exact fun hz => hk ((sectionValue_zero_iff (s k) i p hp).mpr hz)

theorem sectionNormSum_transition {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} {m : ℕ}
    (s : Fin m → SectionData t a b) (i j : Index) (p : Fiber t)
    (hp : p ∈ baseSet t i ∩ baseSet t j) :
    sectionNormSum s j p = Complex.normSq (gain t a b i j p) * sectionNormSum s i p := by
  unfold sectionNormSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← (s k).compatible i j p hp,Complex.normSq_mul]

theorem sectionNormSum_contMDiffOn {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} {m : ℕ}
    (s : Fin m → SectionData t a b) (i : Index) :
    ContMDiffOn 𝓘(ℝ,FixedFiber.Coord) 𝓘(ℝ) ω (sectionNormSum s i) (baseSet t i) := by
  apply contMDiffOn_finset_sum
  intro k _
  exact (FailureOfSemipositiveMetricExtension.normSq_contDiff_real ω).contMDiff.comp_contMDiffOn
    (FailureOfSemipositiveMetricExtension.complex_contMDiffOn_real ((s k).analytic i))

/-- The standard metric attached to an actually generating finite family of sections. -/
def generatedMetric {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} {m : ℕ}
    (s : Fin m → SectionData t a b) (hgen : ∀ p, ∃ k, sectionValue (s k) p ≠ 0) :
    SmoothHermitianMetric t a b where
  coefficient i p := (sectionNormSum s i p)⁻¹
  positive i p hp := inv_pos.mpr (sectionNormSum_positive s hgen i p hp)
  smooth i := by
    have hi : ContDiffOn ℝ ω (fun x : ℝ => x⁻¹) {x | x ≠ 0} :=
      contDiffOn_id.inv (fun _ h => h)
    exact hi.contMDiffOn.comp (sectionNormSum_contMDiffOn s i)
      (fun p hp => ne_of_gt (sectionNormSum_positive s hgen i p hp))
  compatible i j p hp := by
    have hSi := ne_of_gt (sectionNormSum_positive s hgen i p hp.1)
    have hSj := ne_of_gt (sectionNormSum_positive s hgen j p hp.2)
    have hG : Complex.normSq (gain t a b i j p) ≠ 0 := by
      intro hz
      rw [sectionNormSum_transition s i j p hp,hz,zero_mul] at hSj
      exact hSj rfl
    rw [sectionNormSum_transition s i j p hp]
    field_simp
end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
