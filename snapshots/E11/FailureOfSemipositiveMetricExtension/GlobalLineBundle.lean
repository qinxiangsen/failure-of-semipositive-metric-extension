import FailureOfSemipositiveMetricExtension.GlobalChartTopology
import FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle
import FailureOfSemipositiveMetricExtension.ProjectiveLineBundle

/-! Actual global complex line bundles on the closed four-centre incidence space,
glued from the integer-degree cocycles of its projective ambient factors. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set Bundle
open FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped BigOperators

abbrev Index := Fin 3 × (Fin 4 → Fin 2)

def baseSet (i : Index) : Set Total := {p |
  blowdown p ∈ FailureOfSemipositiveMetricExtension.ProjectivePlane.chartSet i.1 ∧
  ∀ r, directions p r ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet (i.2 r)}

theorem baseSet_isOpen (i : Index) : IsOpen (baseSet i) := by
  have h1 : IsOpen {p : Total | blowdown p ∈ FailureOfSemipositiveMetricExtension.ProjectivePlane.chartSet i.1} :=
    (FailureOfSemipositiveMetricExtension.ProjectivePlane.chartSet_isOpen i.1).preimage blowdown_continuous
  have h2 : IsOpen {p : Total | ∀ r, directions p r ∈ FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet (i.2 r)} := by
    rw [setOf_forall]
    apply isOpen_iInter_of_finite
    intro r
    exact (FailureOfSemipositiveMetricExtension.ProjectiveLine.chartSet_isOpen (i.2 r)).preimage (direction_continuous r)
  exact h1.inter h2

def gain (a : ℤ) (b : Fin 4 → ℤ) (i j : Index) (p : Total) : ℂ :=
  FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.gain a i.1 j.1 (blowdown p) *
    ∏ r, FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain (b r) (i.2 r) (j.2 r) (directions p r)

theorem gain_self (a : ℤ) (b : Fin 4 → ℤ) (i : Index) (p : Total) : gain a b i i p = 1 := by
  simp [gain,FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.gain,FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.ratio_self,
    FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain,FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.ratio_self]

theorem gain_comp (a : ℤ) (b : Fin 4 → ℤ) (i j l : Index) (p : Total)
    (hp : p ∈ baseSet i ∩ baseSet j ∩ baseSet l) :
    gain a b j l p * gain a b i j p = gain a b i l p := by
  unfold gain
  rw [show ∀ A B C D : ℂ, (A*B)*(C*D) = (A*C)*(B*D) from by intros; ring]
  rw [FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.gain_comp a i.1 j.1 l.1 (blowdown p)
    ⟨⟨hp.1.1.1,hp.1.2.1⟩,hp.2.1⟩,← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro r _
  exact FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain_comp (b r) (i.2 r) (j.2 r) (l.2 r)
    (directions p r) ⟨⟨hp.1.1.2 r,hp.1.2.2 r⟩,hp.2.2 r⟩

theorem gain_continuousOn (a : ℤ) (b : Fin 4 → ℤ) (i j : Index) :
    ContinuousOn (gain a b i j) (baseSet i ∩ baseSet j) := by
  apply ContinuousOn.mul
  · exact (FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.gain_continuousOn a i.1 j.1).comp
      blowdown_continuous.continuousOn (fun _ hp => ⟨hp.1.1,hp.2.1⟩)
  · apply continuousOn_finset_prod
    intro r _
    exact (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.gain_continuousOn (b r) (i.2 r) (j.2 r)).comp
      (direction_continuous r).continuousOn (fun _ hp => ⟨hp.1.2 r,hp.2.2 r⟩)

/-- The genuine line bundle of ambient multidegree (a;b₁,b₂,b₃,b₄). -/
def core (a : ℤ) (b : Fin 4 → ℤ) : VectorBundleCore ℂ Total ℂ Index where
  baseSet := baseSet
  isOpen_baseSet := baseSet_isOpen
  indexAt p := ((FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.core a).indexAt (blowdown p),
    fun r => (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (b r)).indexAt (directions p r))
  mem_baseSet_at p := ⟨(FailureOfSemipositiveMetricExtension.ProjectivePlaneBundle.core a).mem_baseSet_at _,
    fun r => (FailureOfSemipositiveMetricExtension.ProjectiveLineBundle.core (b r)).mem_baseSet_at _⟩
  coordChange i j p := gain a b i j p • ContinuousLinearMap.id ℂ ℂ
  coordChange_self i p _ v := by simp [gain_self]
  continuousOn_coordChange i j := (gain_continuousOn a b i j).smul continuousOn_const
  coordChange_comp i j l p hp v := by
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_eq_mul]
    rw [← mul_assoc,gain_comp a b i j l p hp]

theorem fiber_finrank (a : ℤ) (b : Fin 4 → ℤ) (p : Total) :
    Module.finrank ℂ ((core a b).Fiber p) = 1 := Module.finrank_self ℂ

theorem actual_vectorBundle (a : ℤ) (b : Fin 4 → ℤ) : VectorBundle ℂ ℂ (core a b).Fiber := inferInstance

end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
