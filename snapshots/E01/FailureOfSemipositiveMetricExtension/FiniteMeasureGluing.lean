import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-! Gluing finitely many compatible local measures using a measurable disjoint
partition.  Local agreement and uniqueness, rather than a sum with overlap
multiplicity, characterize the resulting global measure. -/
namespace FailureOfSemipositiveMetricExtension.MeasureGluing
noncomputable section
open Set MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {n : ℕ}

def finiteGlue (U : Fin n → Set X) (μ : Fin n → Measure X) : Measure X :=
  Measure.sum (fun i => (μ i).restrict (disjointed U i))

theorem disjointed_measurable (U : Fin n → Set X) (hU : ∀ i, MeasurableSet (U i)) (i : Fin n) :
    MeasurableSet (disjointed U i) := by
  rw [disjointed_eq_inter_compl]
  exact (hU i).inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ => (hU j).compl)

theorem finiteGlue_restrict (U : Fin n → Set X) (μ : Fin n → Measure X)
    (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    (hagree : ∀ i j, (μ i).restrict (U i ∩ U j) = (μ j).restrict (U i ∩ U j))
    (j : Fin n) : (finiteGlue U μ).restrict (U j) = (μ j).restrict (U j) := by
  have hD := disjointed_measurable U hU
  have hpartition : ⋃ i, disjointed U i = univ := (iUnion_disjointed).trans hcover
  have hlocal (i : Fin n) : ((μ i).restrict (disjointed U i)).restrict (U j) =
      ((μ j).restrict (U j)).restrict (disjointed U i) := by
    rw [Measure.restrict_restrict (hU j),Measure.restrict_restrict (hD i),inter_comm (disjointed U i)]
    exact Measure.restrict_congr_mono
      (show U j ∩ disjointed U i ⊆ U i ∩ U j from
        fun p hp => ⟨disjointed_subset U i hp.2,hp.1⟩) (hagree i j)
  rw [finiteGlue,Measure.restrict_sum _ (hU j)]
  simp_rw [hlocal]
  rw [← Measure.restrict_iUnion (disjoint_disjointed U) hD,hpartition,Measure.restrict_univ]

/-- Agreement with any further compatible chart, not only the selected cover. -/
theorem finiteGlue_restrict_other (U : Fin n → Set X) (μ : Fin n → Measure X)
    (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    (V : Set X) (hV : MeasurableSet V) (ν : Measure X)
    (hagree : ∀ i, (μ i).restrict (U i ∩ V) = ν.restrict (U i ∩ V)) :
    (finiteGlue U μ).restrict V = ν.restrict V := by
  have hD := disjointed_measurable U hU
  have hpartition : ⋃ i, disjointed U i = univ := (iUnion_disjointed).trans hcover
  have hlocal (i : Fin n) : ((μ i).restrict (disjointed U i)).restrict V =
      (ν.restrict V).restrict (disjointed U i) := by
    rw [Measure.restrict_restrict hV,Measure.restrict_restrict (hD i),inter_comm (disjointed U i)]
    exact Measure.restrict_congr_mono
      (show V ∩ disjointed U i ⊆ U i ∩ V from
        fun p hp => ⟨disjointed_subset U i hp.2,hp.1⟩) (hagree i)
  rw [finiteGlue,Measure.restrict_sum _ hV]
  simp_rw [hlocal]
  rw [← Measure.restrict_iUnion (disjoint_disjointed U) hD,hpartition,Measure.restrict_univ]

theorem finiteGlue_unique (U : Fin n → Set X) (μ : Fin n → Measure X)
    (hU : ∀ i, MeasurableSet (U i)) (hcover : ⋃ i, U i = univ)
    (hagree : ∀ i j, (μ i).restrict (U i ∩ U j) = (μ j).restrict (U i ∩ U j))
    (ν : Measure X) (hν : ∀ i, ν.restrict (U i) = (μ i).restrict (U i)) :
    ν = finiteGlue U μ := by
  apply Measure.ext_of_iUnion_eq_univ hcover
  intro i
  rw [hν i,finiteGlue_restrict U μ hU hcover hagree i]

theorem finiteGlue_mass_bound (U : Fin n → Set X) (μ : Fin n → Measure X) :
    finiteGlue U μ univ ≤ ∑ i, μ i univ := by
  rw [finiteGlue,Measure.sum_apply _ MeasurableSet.univ,tsum_fintype]
  exact Finset.sum_le_sum (fun i _ => Measure.restrict_le_self _)

instance finiteGlue_finite (U : Fin n → Set X) (μ : Fin n → Measure X)
    [∀ i, IsFiniteMeasure (μ i)] : IsFiniteMeasure (finiteGlue U μ) := by
  constructor
  exact (finiteGlue_mass_bound U μ).trans_lt (ENNReal.sum_lt_top.mpr (fun i _ => measure_lt_top _ _))

end
end FailureOfSemipositiveMetricExtension.MeasureGluing
