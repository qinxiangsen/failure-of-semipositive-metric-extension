import FailureOfSemipositiveMetricExtension.CentralWeightSemicontinuity
import FailureOfSemipositiveMetricExtension.Literature.FubiniStudy

/-! Applications of the explicitly admitted generic log-sum-squares theorem.
All functions, actual chart domains, analyticity, coefficient identities and
nonvanishing hypotheses are proved from the constructed family and sections. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

def weightChartDomain (t : ℂ) (i : Index) (r : Fin 4) (e : Fin 2) : Set FixedFiber.Coord :=
  FixedFiber.domain t r e ∩ FixedFiber.param t r e ⁻¹' baseSet t i

theorem weightChartDomain_isOpen (t : ℂ) (i : Index) (r : Fin 4) (e : Fin 2) :
    IsOpen (weightChartDomain t i r e) :=
  (FixedFiber.chart t r e).isOpen_inter_preimage_symm (baseSet_isOpen t i)

theorem coefficient_contDiffOn_chart {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (s : SectionData t a b) (i : Index) (r : Fin 4) (e : Fin 2) :
    ContDiffOn ℂ ω (fun q => s.coefficient i (FixedFiber.param t r e q)) (weightChartDomain t i r e) :=
  ((s.analytic i).comp ((FixedFiber.param_contMDiffOn t r e ω).mono (fun _ h => h.1))
    (fun _ h => h.2)).contDiffOn

/-- Local psh weights on every one of the genuine covering charts and bundle frames. -/
def HasPlurisubharmonicWeights {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ}
    (h : SingularHermitianWeight t a b) : Prop :=
  ∀ i r e, FailureOfSemipositiveMetricExtension.PlurisubharmonicOn (fun q => h.weight i (FixedFiber.param t r e q))
    (weightChartDomain t i r e)

/-- General application: actual generating analytic sections yield psh metric weights. -/
theorem generatedMetric_plurisubharmonic {t : ℂ} {a : ℤ} {b : Fin 4 → ℤ} {m : ℕ}
    (s : Fin m → SectionData t a b) (hgen : ∀ p, ∃ k, sectionValue (s k) p ≠ 0) :
    HasPlurisubharmonicWeights (smoothMetricWeight (generatedMetric s hgen)) := by
  intro i r e
  apply (FailureOfSemipositiveMetricExtension.Literature.log_sum_squares_plurisubharmonic
    (fun k q => (s k).coefficient i (FixedFiber.param t r e q)) (weightChartDomain t i r e)
    (weightChartDomain_isOpen t i r e) (fun k => coefficient_contDiffOn_chart (s k) i r e)
    1 (by norm_num)).congrOn
  intro q hq
  have hS := sectionNormSum_positive s hgen i (FixedFiber.param t r e q) hq.2
  have hS' : (∑ k, Complex.normSq ((s k).coefficient i (FixedFiber.param t r e q))) ≠ 0 := ne_of_gt hS
  simp only [FailureOfSemipositiveMetricExtension.logSumSquaresWeight,hS',if_false,one_mul,smoothMetricWeight,
    generatedMetric,Real.log_inv,neg_neg]
  rfl

theorem centralAMetric_plurisubharmonic :
    HasPlurisubharmonicWeights (smoothMetricWeight centralAMetric) :=
  generatedMetric_plurisubharmonic liftedCentralCubics liftedCentralCubics_basepoint_free

theorem nearbyLMetric_plurisubharmonic (t : ℂ) (ht : t ≠ 0) :
    HasPlurisubharmonicWeights (smoothMetricWeight (nearbyLMetric t ht)) :=
  generatedMetric_plurisubharmonic (FailureOfSemipositiveMetricExtension.GlobalLineBundle.fibrePencil t)
    (FailureOfSemipositiveMetricExtension.GlobalLineBundle.fibrePencil_no_basepoint t ht)

theorem centralH0_logSumSquares (i : Index) (p : Fiber 0) (hp : p ∈ baseSet 0 i) :
    centralH0.weight i p = FailureOfSemipositiveMetricExtension.logSumSquaresWeight (1/2)
      (fun k x => ellSection.coefficient i x * (liftedCentralCubics k).coefficient i x) p := by
  have hs : (∑ k : Fin 4, Complex.normSq
      (ellSection.coefficient i p * (liftedCentralCubics k).coefficient i p)) = centralH0Amplitude i p := by
    simp only [Complex.normSq_mul,← Finset.mul_sum]
    unfold centralH0Amplitude sectionNormSum
    ring
  rw [centralH0_eq_extendedHalfLog i p hp]
  simp only [FailureOfSemipositiveMetricExtension.logSumSquaresWeight,hs,extendedHalfLog]
  split_ifs
  · rfl
  · congr 1
    ring

/-- Psh of the prescribed singular weights, including every point of ell.
Only the cited generic logarithmic psh theorem is external. -/
theorem centralH0_plurisubharmonic : HasPlurisubharmonicWeights centralH0 := by
  intro i r e
  apply (FailureOfSemipositiveMetricExtension.Literature.log_sum_squares_plurisubharmonic
    (fun k q => ellSection.coefficient i (FixedFiber.param 0 r e q) *
      (liftedCentralCubics k).coefficient i (FixedFiber.param 0 r e q))
    (weightChartDomain 0 i r e) (weightChartDomain_isOpen 0 i r e)
    (fun k => (coefficient_contDiffOn_chart ellSection i r e).mul
      (coefficient_contDiffOn_chart (liftedCentralCubics k) i r e))
    (1/2) (by norm_num)).congrOn
  intro q hq
  exact (centralH0_logSumSquares i (FixedFiber.param 0 r e q) hq.2).symm

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
