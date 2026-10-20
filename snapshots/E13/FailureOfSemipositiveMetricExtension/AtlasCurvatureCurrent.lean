import FailureOfSemipositiveMetricExtension.CurrentCoordinateCovariance
import FailureOfSemipositiveMetricExtension.MultiplierGerms

/-! A global (1,1)-current as a differential form with genuine distribution
coefficients satisfying the full coordinate-change law on an actual covering
atlas. This is a descent definition of currents, not a family of unrelated local
existence statements. Global de Rham/cohomology objects are not asserted here. -/
namespace FailureOfSemipositiveMetricExtension.AtlasCurvature
noncomputable section
open Set MeasureTheory IsManifold
open scoped Topology Manifold ContDiff
open WeakComplexHessian PshCurvatureCurrentInterface CurrentCoordinateCovariance

abbrev Coord := ℂ × ℂ
variable (M : Type) [TopologicalSpace M] [ChartedSpace Coord M]

/-- Actual coordinate/gauge data of a metric, restricted to simultaneous
coordinate and line frames. The gauge direction is weight(a)-weight(b). -/
structure MetricAtlas (A : Type) where
  coordinate : A → Multiplier.AnalyticCoordinate M
  cover : ∀ p : M, ∃ a, p ∈ (coordinate a).chart.source
  weight : A → M → WithBot ℝ
  gauge : A → A → M → ℂ
  gauge_analytic : ∀ a b, ContMDiffOn 𝓘(ℂ,Coord) 𝓘(ℂ) ω (gauge a b)
    ((coordinate a).chart.source ∩ (coordinate b).chart.source)
  gauge_nonzero : ∀ a b p, p ∈ (coordinate a).chart.source ∩ (coordinate b).chart.source → gauge a b p ≠ 0
  compatible : ∀ a b p, p ∈ (coordinate a).chart.source ∩ (coordinate b).chart.source →
    weight a p = weight b p + (Real.log (Complex.normSq (gauge a b p)) : ℝ)
  psh : ∀ a, PlurisubharmonicOn (fun z => weight a ((coordinate a).chart.symm z)) (coordinate a).chart.target
  finite_dense : ∀ a, FinitePointsDense (fun z => weight a ((coordinate a).chart.symm z)) (coordinate a).chart.target

variable {M} {A : Type} (D : MetricAtlas M A)
namespace MetricAtlas

def localWeight (a : A) : Coord → WithBot ℝ := fun z => D.weight a ((D.coordinate a).chart.symm z)

def change (a b : A) : PartialHomeomorph Coord Coord :=
  (D.coordinate a).chart.symm.trans (D.coordinate b).chart

def localGauge (a b : A) : Coord → ℂ := fun z => D.gauge a b ((D.coordinate a).chart.symm z)

/-- Atlas-compatible local distributional coefficients, each with an actual
positive locally finite trace measure and both complex closedness identities.
The overlap formula includes the inverse-volume Jacobian and complex test
extension; thus the data represent one global differential current. -/
structure GlobalPositiveClosedCurrent where
  localCurrent : ∀ a, CurvatureCurrent (D.localWeight a) (D.coordinate a).chart.target
  transported_test : ∀ a b φ, IsTest (D.change a b).source φ → ∀ j k r s,
    IsComplexTest (D.change a b).target (transportedTest (D.change a b) φ j k r s)
  compatible : ∀ a b φ, IsTest (D.change a b).source φ → ∀ j k,
    coefficient (realRepresentative (D.localWeight a)) j k φ =
      ∑ r : Fin 2, ∑ s : Fin 2, complexCoefficient (realRepresentative (D.localWeight b)) r s
        (transportedTest (D.change a b) φ j k r s)

variable [IsManifold 𝓘(ℂ,Coord) ω M]

theorem change_analytic (a b : A) : ContDiffOn ℂ ω (D.change a b) (D.change a b).source := by
  apply contMDiffOn_iff_contDiffOn.mp
  exact (D.coordinate b).forward.comp ((D.coordinate a).inverse.mono (fun _ h => h.1)) (fun _ h => h.2)

theorem change_symm_analytic (a b : A) : ContDiffOn ℂ ω (D.change a b).symm (D.change a b).target := by
  apply contMDiffOn_iff_contDiffOn.mp
  exact (D.coordinate a).forward.comp ((D.coordinate b).inverse.mono (fun _ h => h.1)) (fun _ h => h.2)

theorem localGauge_analytic (a b : A) : ContDiffOn ℂ ω (D.localGauge a b) (D.change a b).source := by
  apply contMDiffOn_iff_contDiffOn.mp
  exact (D.gauge_analytic a b).comp ((D.coordinate a).inverse.mono (fun _ h => h.1))
    (fun _ h => ⟨(D.coordinate a).chart.map_target h.1,h.2⟩)

theorem localGauge_nonzero (a b : A) (z : Coord) (hz : z ∈ (D.change a b).source) :
    D.localGauge a b z ≠ 0 :=
  D.gauge_nonzero a b _ ⟨(D.coordinate a).chart.map_target hz.1,hz.2⟩

theorem localWeight_change (a b : A) (z : Coord) (hz : z ∈ (D.change a b).source) :
    D.localWeight a z = D.localWeight b (D.change a b z) +
      (Real.log (Complex.normSq (D.localGauge a b z)) : ℝ) := by
  change D.weight a ((D.coordinate a).chart.symm z) =
    D.weight b ((D.coordinate b).chart.symm ((D.coordinate b).chart ((D.coordinate a).chart.symm z))) + _
  have hp : (D.coordinate a).chart.symm z ∈ (D.coordinate b).chart.source := hz.2
  have he : (D.coordinate b).chart.symm ((D.coordinate b).chart ((D.coordinate a).chart.symm z)) =
      (D.coordinate a).chart.symm z := (D.coordinate b).chart.left_inv hp
  rw [he]
  exact D.compatible a b _ ⟨(D.coordinate a).chart.map_target hz.1,hz.2⟩

/-- All overlap hypotheses are derived from genuine analytic coordinate maps
and gauge data. Only the two precisely universal current facts are inputs. -/
theorem globalCurrent_with_lelong_exists
    (hcurrent : PshCurrentStatement) (hcovariance : CovarianceStatement) :
    ∃ T : GlobalPositiveClosedCurrent D, ∀ a z, z ∈ (D.coordinate a).chart.target →
      HasLelongNumber (T.localCurrent a) z (FailureOfSemipositiveMetricExtension.logarithmicOrder (D.localWeight a) z) := by
  have hloc (a : A) := hcurrent (D.localWeight a) (D.coordinate a).chart.target
      (D.coordinate a).chart.open_target (D.psh a) (D.finite_dense a)
  let T := fun a => Classical.choose (hloc a)
  have hc (a b : A) (φ : Coord → ℝ) (hφ : IsTest (D.change a b).source φ) :=
    hcovariance (D.change a b) (D.change_analytic a b) (D.change_symm_analytic a b)
      (D.localWeight a) (D.localWeight b)
      ((T a).locallyIntegrable.mono_set (fun _ h => h.1))
      ((T b).locallyIntegrable.mono_set (fun _ h => h.1))
      (ae_restrict_of_ae_restrict_of_subset (fun _ h => h.1) (T a).finite_ae)
      (ae_restrict_of_ae_restrict_of_subset (fun _ h => h.1) (T b).finite_ae)
      (D.localGauge a b) (D.localGauge_analytic a b) (D.localGauge_nonzero a b)
      (D.localWeight_change a b) φ hφ
  exact ⟨{ localCurrent := T
           transported_test := fun a b φ hφ => (hc a b φ hφ).1
           compatible := fun a b φ hφ => (hc a b φ hφ).2 },
    fun a z hz => (Classical.choose_spec (hloc a)) z hz⟩

theorem globalCurrent_exists_of_local_current_and_covariance
    (hcurrent : PshCurrentStatement) (hcovariance : CovarianceStatement) :
    Nonempty (GlobalPositiveClosedCurrent D) := by
  obtain ⟨T,_⟩ := D.globalCurrent_with_lelong_exists hcurrent hcovariance
  exact ⟨T⟩

end MetricAtlas
end
end FailureOfSemipositiveMetricExtension.AtlasCurvature
